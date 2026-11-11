/-
The stage-2 walk's loop invariants, its measure, and the smallest back edge
proved against them.

`Stage2WalkObligation` (`JsonStage2IR`) is `Satisfies` for the pinned 165-block
body, and its first conjunct is completion at `stage2Budget`
(`stage2WalkObligation_iff_completion`).  `runFuel` is fuel-indexed, so the proof
that resists is the loop: an invariant preserved by every arm, and a measure that
decreases on every back edge.  This module scopes that proof and discharges one
arm of it.  It does not claim the obligation.

## What the loop carries

The walk is the outer entry loop `while.body.i`, with five inner loops.  Its state
is not a function of the report `Stage2Run` records, and the reason is recorded at
`Stage2Run`'s definition: the arena cursor is the *sum* of the extents the walk
decoded into it, and a sum of `Nat`s does not name its summands.  A record that
carried `alen` alone could not say what the walk had written, so the loop carries
the summands themselves:

* `spans : List (Nat × Nat)` — the decoded bodies' document extents, in document
  order.  The invariant states `alen ≤ ndst0 + spans.map (·.2) |>.sum` plus the
  two shape clauses, which is exactly the predicate `Stage2SpansInside` and
  exactly what `arenaLe_of_spans` consumes to give `alen ≤ ndst0 + n`.  The
  report keeps the bound, not the list;
* `records : Nat` — the event records emitted, with `evlen = nev0 + 13 * records`
  and `records ≤ k`.  Thirteen bytes per record is the body's own store
  (`out_reserve(&z->ev, 13)` and `len += 13`), and at most one record per entry is
  the count `Stage2OneRecordPerEntry` needs;
* `k : Nat` — the block index into the entry stream, at the phi the loop reads
  (`%k.0.i249`);
* `alen` and `evlen` — the two cursors;
* `pending : Option (Nat × Nat)` — the record in flight: the entry position and
  the arena offset reserved for its decoded body, `none` between records;
* `refusal : Bool` and `eoff : Nat` — the refusal bit and the offset it stores,
  the two clauses nothing in `Stage2Run`'s vocabulary names at the refusal arm;
* `block : String` — the block the run is at;
* `inner : Nat` — the remaining inner work at the block, the measure's second
  component.

`WalkGeom` is `stage2Pre`'s staging, named field for field.  A geometry is not
assumed: `WalkGeom.nonempty` unpacks any `Γ_stage2.pre` into one, so the invariant
is not vacuous at a caller the record admits.

The memory half is `Owns (inRegions [(dst, alen), (ev, evlen)]) s.mem m0`: the
walk owns the arena and event prefixes it has written, and the staging survives
outside them.  The report's `Owns` clause at `alen + 64` follows from this and the
staged capacity (`owns_reserve_of_owns_extent`, `JsonStage2Body`).

## The measure

The measure is a `Nat`, not a pair:

    walkMeasure G C = (G.nep - C.k) * (walkInnerCap G + 1) + C.inner
    walkInnerCap G  = G.n + 5

The pair is `(remaining entries, inner work)`, encoded lexicographically with the
inner component's bound as the radix.  `n + 5` is the bound on the inner work at
any back edge: the scans `land.rhs.i`, `land.rhs.i103`, `land.rhs71.i` and
`land.rhs457.i` walk the document, so at most `n`; the literal comparison
`for.body.i.i` is bounded by `min (ee - idx) ln` with `ln` four or five at
`if.end48.i`'s phi, so at most `n + 5`.  That every inner arm stays under the cap
is what the remaining five arms must show; the outer arm is strict on the factor
because `inner` resets to at most the cap, which is why the radix is `cap + 1`.

The arm proved below does not consume the cap's value: it decreases the inner
component at a fixed `k`, and the outer term is the same on both sides.

## The arm, and the shape

Six back edges, on the body's 165 blocks (`#guard` at
`JsonStage2IR:1399`):

| back edge                     | loop                 | shape                        |
| ----------------------------- | -------------------- | ---------------------------- |
| `for.inc.i.i → for.body.i.i`  | literal comparison   | two blocks, no memory write  |
| `while.body370.i → land.rhs.i`| whitespace skip      | scans the gap                |
| `while.body.i104 → land.rhs.i103` | string scan      | scans to the closing quote   |
| `while.body76.i → land.rhs71.i`   | escape scan      | scans for a backslash        |
| `while.body462.i → land.rhs457.i` | extra-token scan | scans to the next entry      |
| `cleanup478.i → while.body.i` | the entry loop       | the whole dispatch           |

The smallest is `for.inc.i.i → for.body.i.i`: one control step (two pure
instructions and a `condbr`), no memory write, and the only proof is the block's
`denoteCode`, the branch, and `c - (i + 1) < c - i`.  `forInc_step` proves it
against `WalkInv` — every field of the invariant is preserved, and the measure
strictly decreases — and `forInc_arm` states the same at the invariant alone,
with only the latch's own guard beside it.

The hard arm is the entry loop's, `cleanup478.i → while.body.i`: its iteration is
the whole dispatch, and inside it are the three obligations the source's own
guards mark — the **nesting** state (`sp`, `ctype`, `cst`, and the `sp >= MAXD`
refusal) and the **two reserves** (`z_arena_reserve` before a decoded body and
`out_reserve(&z->ev, 13)` before each record), each of which can take a refusal
arm and leave the cursors, the refusal bit and the refusal offset as the record
must report them.  The four scans are the middle: their measures are the
document-bounded ones, and they read staged memory but do not write it.

## What is not here

`Stage2WalkObligation` is not proved.  This module supplies the invariant
statement, the measure, and one arm; the other five arms, the seed from `entry`
to `while.body.i`, the exit states, and the composition with `Stage2Run`'s six
clauses remain.  In particular, `WalkLocal` pins the inner component only at the
two blocks this arm reaches; the other arms must pin it at their own back-edge
sources, and until they do the measure is a statement about this edge and not a
well-founded bound on the whole control flow.
-/
import LeanLLVM.Refinement.JsonStage2Body
import LeanLLVM.Refinement.JsonEscapeListBody

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The staging geometry -/

/-- `stage2Pre`'s witnesses, at the memory the caller staged.  A geometry is the
staging the loop reads, held fixed for the run; the invariant and the measure are
indexed by it.  Every field and every clause is `stage2Pre`'s, in the same order,
so the loop does not work at a weaker domain than the record admits. -/
structure WalkGeom (m0 : Mem) where
  /-- The document. -/
  b : Nat
  /-- The document's length. -/
  n : Nat
  /-- The entry stream. -/
  ep : Nat
  /-- The entry count. -/
  nep : Nat
  /-- The escape list. -/
  xp : Nat
  /-- The escape count. -/
  nxp : Nat
  /-- The arena. -/
  dst : Nat
  /-- The arena's capacity. -/
  dstcap : Nat
  /-- The arena's cursor slot. -/
  ndst : Nat
  /-- The event stream. -/
  ev : Nat
  /-- The event stream's capacity. -/
  evcap : Nat
  /-- The event stream's cursor slot. -/
  nev : Nat
  /-- The refusal slot. -/
  err : Nat
  /-- The document's bytes. -/
  bs : List UInt8
  /-- The entry stream's positions. -/
  ent : List Nat
  /-- The arena's cursor as staged. -/
  ndst0 : Nat
  /-- The event stream's cursor as staged. -/
  nev0 : Nat
  /-- The document is readable. -/
  doc : readBytes m0 b n = some bs
  /-- The decoder's read-past tail is staged. -/
  tail : HasBytes m0 (b + n) stage2ReadTail
  /-- The entry stream is readable. -/
  entries : readLanes32 m0 ep nep = some ent
  /-- The entry positions are in document order. -/
  order : ent.Pairwise (· < ·)
  /-- The entry positions are inside the document. -/
  inside : ∀ q ∈ ent, q < n
  /-- The escape list's bytes are staged. -/
  esc : HasBytes m0 xp (4 * nxp)
  /-- The arena is staged. -/
  arenaCap : HasBytes m0 dst dstcap
  /-- The arena has room for the document and the decoder's slack. -/
  arenaRoom : ndst0 + n + stage2ArenaReserve ≤ dstcap
  /-- The event stream is staged. -/
  evCap : HasBytes m0 ev evcap
  /-- The event stream has room for one record per input byte. -/
  evRoom : nev0 + stage2RecordBytes * n ≤ evcap
  /-- The arena's cursor slot reads as staged. -/
  ndstRead : readBytes m0 ndst 8 = some (wordBytes 8 ndst0)
  /-- The event cursor's slot reads as staged. -/
  nevRead : readBytes m0 nev 8 = some (wordBytes 8 nev0)
  /-- The refusal slot is staged. -/
  errBytes : HasBytes m0 err 8
  /-- The document's positions fit the entry stream's 32-bit words. -/
  maxDoc : n ≤ stage2MaxDocument
  /-- The staged objects are separate. -/
  separate : DisjointRegions
    (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)

/-- **The staging is inhabited at every caller the record admits.**  `WalkGeom`
is `stage2Pre` unpacked, so a walk inside `Γ_stage2.pre` has a geometry to carry;
without this the invariant would be satisfiable only by a caller the record
refuses, which is the vacuity the completion conjunct exists to exclude. -/
theorem WalkGeom.nonempty {args : List Value} {m0 : Mem} {next : Nat}
    (h : Γ_stage2.pre args m0 next) : Nonempty (WalkGeom m0) := by
  have h' : stage2Pre args m0 next := h
  obtain ⟨b, n, ep, nep, xp, nxp, dst, dstcap, ndst, ev, evcap, nev, err, bs, ent,
    ndst0, nev0, -, doc, tail, entries, order, inside, esc, arenaCap, arenaRoom,
    evCap, evRoom, ndstRead, nevRead, errBytes, maxDoc, separate⟩ := h'
  exact ⟨{
    b := b
    n := n
    ep := ep
    nep := nep
    xp := xp
    nxp := nxp
    dst := dst
    dstcap := dstcap
    ndst := ndst
    ev := ev
    evcap := evcap
    nev := nev
    err := err
    bs := bs
    ent := ent
    ndst0 := ndst0
    nev0 := nev0
    doc := doc
    tail := tail
    entries := entries
    order := order
    inside := inside
    esc := esc
    arenaCap := arenaCap
    arenaRoom := arenaRoom
    evCap := evCap
    evRoom := evRoom
    ndstRead := ndstRead
    nevRead := nevRead
    errBytes := errBytes
    maxDoc := maxDoc
    separate := separate
  }⟩

/-- The entry count is at most the document's: the stream's positions are
strictly increasing and inside the document.  `Stage2Run.nep_le` is the same fact
at the report; the loop needs it at the staging. -/
theorem WalkGeom.nep_le {m0 : Mem} (G : WalkGeom m0) : G.nep ≤ G.n := by
  rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  exact length_le_of_pairwise_lt G.order G.inside

/-! ### The carry and the invariant -/

/-- What the loop carries between iterations.  The extents are a list because a
cursor is their sum and a sum does not name its summands (`Stage2Run`'s
definition records the obstruction). -/
structure WalkCarry {m0 : Mem} (G : WalkGeom m0) where
  /-- The block index into the entry stream. -/
  k : Nat
  /-- The arena cursor. -/
  alen : Nat
  /-- The event cursor. -/
  evlen : Nat
  /-- The event records emitted, thirteen bytes each. -/
  records : Nat
  /-- The decoded bodies' document extents, in document order. -/
  spans : List (Nat × Nat)
  /-- The record in flight: its entry position and its reserved arena offset. -/
  pending : Option (Nat × Nat)
  /-- The refusal bit. -/
  refusal : Bool
  /-- The refusal offset. -/
  eoff : Nat
  /-- The block the run is at. -/
  block : String
  /-- The remaining inner work at that block. -/
  inner : Nat

/-- The block-local half of the invariant: the inner component and the registers
it is read from, at the two blocks the proved arm reaches.  At every other block
it is `True`; pinning it there is the remaining arms' work, and the module
docstring says so rather than claiming a bound it does not have. -/
def WalkLocal {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : Prop :=
  if C.block = "for.inc.i.i" then
    ∃ i c : Nat, C.inner = c - i ∧ i < c ∧ c < 2 ^ 64 ∧
      lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))
  else if C.block = "for.body.i.i" then
    ∃ i c : Nat, C.inner = c - i ∧ i < c ∧ c < 2 ^ 64 ∧
      s.pre = some "for.inc.i.i" ∧
      lookupName s.env "%inc.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))
  else True

/-- **The walk's invariant.**  Everything the loop carries, at the block it is at,
and the memory it has written.  This is the predicate every one of the six arms
must preserve; `forInc_step` proves the smallest one does. -/
structure WalkInv {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Prop where
  /-- The run is at the carried block. -/
  pc_eq : s.pc = C.block
  /-- The entry index is the phi the outer loop reads. -/
  blockIndex : lookupName s.env "%k.0.i249" = some (.int 64 (BitVec.ofNat 64 C.k))
  /-- The index has not passed the stream. -/
  k_le : C.k ≤ G.nep
  /-- At most one record per entry. -/
  records_le : C.records ≤ C.k
  /-- The event cursor is exactly thirteen bytes per record. -/
  evlen_eq : C.evlen = G.nev0 + stage2RecordBytes * C.records
  /-- The arena cursor is bounded by the extents it decoded. -/
  alen_le_sum : C.alen ≤ G.ndst0 + (C.spans.map (fun r => r.2)).sum
  /-- The extents are in document order. -/
  spans_order : C.spans.Pairwise (fun r s => r.1 + r.2 ≤ s.1)
  /-- Every extent ends inside the document. -/
  spans_inside : ∀ r ∈ C.spans, r.1 + r.2 ≤ G.n
  /-- The record in flight reserves the arena at the cursor, inside the document:
  at most one record is being assembled, and its reservation is the cursor's own
  offset. -/
  pending_at : ∀ p off, C.pending = some (p, off) → off = C.alen ∧ p < G.n
  /-- The refusal offset is inside the document. -/
  eoff_le : C.eoff ≤ G.n
  /-- The walk owns the two prefixes it has written, and the staging survives. -/
  owning : Owns (inRegions [(G.dst, C.alen), (G.ev, C.evlen)]) s.mem m0
  /-- The block-local facts the measure is read from. -/
  blockLocal : WalkLocal C s

namespace WalkInv

variable {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}

/-- The arena's bound, from the carried extents: this is
`Stage2SpansInside`'s content and `arenaLe_of_spans`'s conclusion, so the report's
`alen ≤ ndst0 + n` is downstream of the carry rather than assumed. -/
theorem alen_le (h : WalkInv G C s) : C.alen ≤ G.ndst0 + G.n :=
  arenaLe_of_spans h.spans_order h.spans_inside h.alen_le_sum

/-- The event cursor's bound, from one record per entry and the entry count. -/
theorem evlen_le (h : WalkInv G C s) : C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := by
  have h1 : stage2RecordBytes * C.records ≤ stage2RecordBytes * G.n :=
    Nat.mul_le_mul_left _ (le_trans h.records_le (le_trans h.k_le G.nep_le))
  rw [h.evlen_eq]
  omega

/-- The block-local facts at the latch: the invariant implies them, and the arm's
lemma takes them explicitly so its `WalkInv` hypothesis is not unpacked twice. -/
theorem forInc {h : WalkInv G C s} (hblock : C.block = "for.inc.i.i") :
    ∃ i c : Nat, C.inner = c - i ∧ i < c ∧ c < 2 ^ 64 ∧
      lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
  simpa [WalkLocal, hblock] using h.blockLocal

end WalkInv

/-! ### The measure -/

/-- A bound on the inner work at any back edge: the scans are bounded by the
document, and the literal comparison by its own five-byte cap. -/
def walkInnerCap {m0 : Mem} (G : WalkGeom m0) : Nat := G.n + 5

/-- **The measure**, as one `Nat`: the remaining entries radix the remaining inner
work.  The outer term decreases by at least one per entry; the inner term by
exactly one per inner iteration; the radix is `cap + 1` so an outer step is strict
even when the inner component resets to its cap. -/
def walkMeasure {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : Nat :=
  (G.nep - C.k) * (walkInnerCap G + 1) + C.inner

/-- The latch's own guard: the exit test is false, so the back edge — not
`for.end.i.i` — is the one the latch takes.  It is the only fact the arm needs
beside the invariant, because the invariant's block-local clause is what names the
registers the guard is about. -/
def ForIncGuard {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : Prop :=
  ∃ i c : Nat, C.inner = c - i ∧ i + 1 < c ∧ c < 2 ^ 64 ∧
    lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
    lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))

/-! ### The arm: `for.inc.i.i → for.body.i.i` -/

/-- The latch: `%inc.i.i = %i.029.i.i + 1`, the exit test `eq %inc.i.i,
%cond.i.i`, and the back edge to the header.  Two instructions, no memory. -/
def forIncBlock : Block :=
  { name := "for.inc.i.i",
    instrs := [
      Instr.binop "%inc.i.i" BinOp.add 64 (Operand.reg "%i.029.i.i")
        (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond.not.i.i" IPred.eq 64 (Operand.reg "%inc.i.i")
        (Operand.reg "%cond.i.i")],
    term := Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.i.i" "for.body.i.i" }

/-- The latch is the pinned body's block: the arm's proof is about `stage2Body`,
not about a transcription of it. -/
theorem forInc_find : stage2Body.findBlock "for.inc.i.i" = some forIncBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, forIncBlock]

/-- `%d = add i64 %a, 1` at the state's own environment.  `BlockEval`'s step is
stated at `stateAt env s`; this is the same step at `s`, which is the shape the
arm's state has. -/
theorem denoteCode_add_one (calls : Calls) (s : State) (d a : String) {x : BitVec 64}
    (ha : lookupName s.env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .add 64 (.reg a) (.imm (.int 64 (BitVec.ofNat 64 1))) :: is) s =
      denoteCode calls is (s.bind d (.int 64 (x + BitVec.ofNat 64 1))) := by
  simpa only [stateAt, State.bind] using
    (denoteCode_add_imm (calls := calls) (env := s.env) (s := s) (d := d) (a := a)
      (x := x) (c := BitVec.ofNat 64 1) ha is)

/-- `%d = icmp eq i64 %a, %b` at the state's own environment. -/
theorem denoteCode_icmp_eq (calls : Calls) (s : State) (d a b : String) {x y : BitVec 64}
    (ha : lookupName s.env a = some (.int 64 x))
    (hb : lookupName s.env b = some (.int 64 y)) (is : List Instr) :
    denoteCode calls (.icmp d .eq 64 (.reg a) (.reg b) :: is) s =
      denoteCode calls is (s.bind d (.int 1 (evalICmp .eq x y))) := by
  simpa only [stateAt, State.bind] using
    (denoteCode_icmp_eq_reg (calls := calls) (env := s.env) (s := s) (d := d) (a := a)
      (b := b) (x := x) (y := y) ha hb is)

/-- One step of the latch, at the state its back edge carries. -/
theorem forInc_denote {calls : Calls} (s : State) (i c : Nat)
    (hi : lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    denoteCode calls
      [Instr.binop "%inc.i.i" BinOp.add 64 (Operand.reg "%i.029.i.i")
         (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
       Instr.icmp "%exitcond.not.i.i" IPred.eq 64 (Operand.reg "%inc.i.i")
         (Operand.reg "%cond.i.i")] s =
      some (s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 (i + 1)))
            |>.bind "%exitcond.not.i.i" (.int 1 (0 : BitVec 1))) := by
  rw [denoteCode_add_one calls s "%inc.i.i" "%i.029.i.i" (x := BitVec.ofNat 64 i) hi]
  rw [denoteCode_icmp_eq calls
      (s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 i + BitVec.ofNat 64 1)))
      "%exitcond.not.i.i" "%inc.i.i" "%cond.i.i"
      (x := BitVec.ofNat 64 i + BitVec.ofNat 64 1) (y := BitVec.ofNat 64 c)
      (by simp only [State.bind, lookupName_cons_self])
      (by
        simp only [State.bind]
        rw [lookupName_cons_ne _ _ (by decide)]
        exact hc)]
  have hadd : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) := by
    rw [← BitVec.ofNat_add (n := 64) i 1]
  have hne : BitVec.ofNat 64 (i + 1) ≠ BitVec.ofNat 64 c := by
    intro heq
    have h1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
      rw [BitVec.toNat_ofNat]
      omega
    have h2 : (BitVec.ofNat 64 c).toNat = c := by
      rw [BitVec.toNat_ofNat]
      omega
    rw [heq, h2] at h1
    omega
  simp only [hadd]
  rw [show evalICmp IPred.eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 0 from
    (evalICmp_eq_zero_iff _ _).mpr hne]
  simp only [denoteCode, denoteRun, State.bindAll]

/-- The latch's terminator: at a clear exit test it jumps to the header and
records the latch as the predecessor. -/
theorem forInc_term {calls : Calls} (s : State) (i c : Nat)
    (hpc : s.pc = "for.inc.i.i")
    (hi : lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    step calls stage2Body s =
      .jump { (s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 (i + 1)))).bind
                "%exitcond.not.i.i" (.int 1 (0 : BitVec 1)) with
              pc := "for.body.i.i"
              pre := some "for.inc.i.i" } := by
  simp only [step, hpc, forInc_find, forIncBlock]
  rw [forInc_denote s i c hi hc hlt hcw]
  dsimp only
  rw [execTerm_condbr_zero _ _ _ _ _
      (by simp only [State.bind, evalOperand, lookupName_cons_self]) rfl]
  simp only [State.bind, hpc]

/-- **The smallest arm.**  From the invariant at the latch, one control step
reaches the header with the invariant preserved and the measure strictly smaller:
`k` is unchanged and the inner component goes from `c - i` to `c - (i + 1)`.

This is the feasibility test the scope asks for: the invariant is preserved field
for field (the block, the index, the cursors, the extents, the record in flight,
the refusal offset, the memory claim, and the local facts at the landing block),
and the measure's decrease is the arm's own arithmetic, not a hypothesis. -/
theorem forInc_step {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (i c : Nat)
    (hInv : WalkInv G C s) (hblock : C.block = "for.inc.i.i")
    (hi : lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hinner : C.inner = c - i) (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    ∃ (e : State) (C' : WalkCarry G),
      WalkInv G C' e ∧
      C'.block = "for.body.i.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  -- the landing state and the carried data one inner iteration later
  let e : State :=
    { s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 (i + 1)))
      |>.bind "%exitcond.not.i.i" (.int 1 (0 : BitVec 1)) with
      pc := "for.body.i.i"
      pre := some "for.inc.i.i" }
  let C' : WalkCarry G := { C with block := "for.body.i.i", inner := c - (i + 1) }
  have hpc : s.pc = "for.inc.i.i" := by rw [hInv.pc_eq, hblock]
  have hstep : step calls stage2Body s = .jump e := forInc_term s i c hpc hi hc hlt hcw
  have hk : lookupName e.env "%k.0.i249" = lookupName s.env "%k.0.i249" := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  refine ⟨e, C', ?_, rfl, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := by rw [hk]; exact hInv.blockIndex
        k_le := hInv.k_le
        records_le := hInv.records_le
        evlen_eq := hInv.evlen_eq
        alen_le_sum := hInv.alen_le_sum
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        eoff_le := hInv.eoff_le
        owning := hInv.owning
        blockLocal := ?_ }
    dsimp only [WalkLocal, C']
    rw [if_neg (by decide), if_pos rfl]
    refine ⟨i + 1, c, rfl, hlt, hcw, rfl, ?_⟩
    dsimp only [e, State.bind]
    refine ⟨?_, ?_⟩
    · rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    · rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hc
  · dsimp only [walkMeasure, C']
    rw [hinner]
    exact Nat.add_lt_add_left (by omega) _
  · intro k
    rw [show 1 + k = k + 1 from by omega]
    simp only [runFuel, hstep]

/-- **The arm at its front door.**  Beside `WalkInv` the only hypothesis is the
latch's guard: no register read and no counter value is assumed.  The guard's
`i + 1 < c` is what `forInc_step` turns into the branch and the decrease. -/
theorem forInc_arm {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "for.inc.i.i")
    (hguard : ForIncGuard C s) :
    ∃ (e : State) (C' : WalkCarry G),
      WalkInv G C' e ∧
      C'.block = "for.body.i.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  obtain ⟨i, c, hinner, hlt, hcw, hi, hc⟩ := hguard
  exact forInc_step G C s i c hInv hblock hi hc hinner hlt hcw

/-! ### The instrument -/

/-- info: 'LeanLLVM.Refinement.WalkGeom.nonempty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkGeom.nonempty

/-- info: 'LeanLLVM.Refinement.WalkInv.alen_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.alen_le

/-- info: 'LeanLLVM.Refinement.WalkInv.evlen_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.evlen_le

/-- info: 'LeanLLVM.Refinement.forInc_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_find

/-- info: 'LeanLLVM.Refinement.forInc_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_step

/-- info: 'LeanLLVM.Refinement.WalkGeom.nep_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkGeom.nep_le

/-- info: 'LeanLLVM.Refinement.WalkInv.forInc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.forInc

/-- info: 'LeanLLVM.Refinement.denoteCode_add_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.denoteCode_add_one

/-- info: 'LeanLLVM.Refinement.denoteCode_icmp_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.denoteCode_icmp_eq

/-- info: 'LeanLLVM.Refinement.forInc_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_denote

/-- info: 'LeanLLVM.Refinement.forInc_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_term

/-- info: 'LeanLLVM.Refinement.forInc_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_arm


end LeanLLVM.Refinement
