import LeanLLVM.Refinement.BlockEval
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
indexed by it.  Every field and every clause is `stage2Pre`'s (the three widths
and the two address facts sit beside `maxDoc` rather than after the watermark),
so the loop does not work at a weaker domain than the record admits. -/
structure WalkGeom (m0 : Mem) where
  /-- The document. -/
  b : Nat
  /-- The document's length. -/
  n : Nat
  /-- The entry stream. -/
  ep : Nat
  /-- **The document's base is non-null**, `stage2Pre`'s clause.  The entry block's
  `%invariant.gep` is a signed `getelementptr` at `-1`, so a base of zero is not a
  caller the body can be run for. -/
  bPos : 0 < b
  /-- **The document's base is a word**, `stage2Pre`'s clause: the value the
  staging writes at `%s->b` and the entry block reads back as `%3`. -/
  bLt : b < 2 ^ 64
  /-- **The entry stream's base is a word**, `stage2Pre`'s clause. -/
  epLt : ep < 2 ^ 64
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
  /-- **The escape count is its argument word's value**, `stage2Pre`'s clause at the
  geometry.  The ABI carries it as an eight-byte word, so it is below `2 ^ 64` and
  the word's `.toNat` is the number itself.  The adapter's staging names the same
  number as a word (`stage2StagedPre`), and this is half of what reconciles the
  two region lists (`stage2StagedRegions_reconcile`). -/
  nxpLt : nxp < 2 ^ 64
  /-- **The arena's capacity is its argument word's value**, `stage2Pre`'s clause. -/
  dstcapLt : dstcap < 2 ^ 64
  /-- **The event stream's capacity is its argument word's value**, `stage2Pre`'s
  clause. -/
  evcapLt : evcap < 2 ^ 64
  /-- **The arena's staged address is a word**, `stage2Pre`'s clause.  The walk
  hands its sub-calls `.ptr (G.dst + ...)` and reads the arena's base back through
  the log's `%ar` word (`wordBytes 8 G.dst`), an eight-byte residue, so an address
  at or above `2 ^ 64` would name a different object than the word holds. -/
  dstLt : dst < 2 ^ 64
  /-- **The event stream's staged address is a word**, `stage2Pre`'s clause: the
  twin of `dstLt` at `%ev`, whose word `if.then328.i` reads as `%33`. -/
  evLt : ev < 2 ^ 64
  /-- **The event cursor's signed bound**, `stage2Pre`'s clause.
  `if.then328.i` forms its record pointers from a signed index, so the cursor has
  to stay below `2 ^ 63`; the clause is `nev0 + 13 * n < 2 ^ 63`, and
  `WalkInv.evlen_le` carries it to `C.evlen < 2 ^ 63` at every state. -/
  ev63 : nev0 + stage2RecordBytes * n < 2 ^ 63
  /-- The staged objects are separate. -/
  separate : DisjointRegions
    (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)
  /-- **The cursor the call is made at**, which is where the body's four stack
  objects land (`stage2AllocaWrites`).  It is `Γ_stage2.pre`'s `next` and not a
  number chosen here. -/
  next0 : Nat
  /-- **The watermark**: every staged object ends at or below the cursor.  This is
  `stage2Pre`'s last clause, read at the geometry, and it is what makes the four
  stack objects disjoint from every staged byte — the fact the frame and the two
  read proofs below consume. -/
  watermark : ∀ r ∈ stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err,
    r.1 + r.2 ≤ next0

/-- **The staging is inhabited at every caller the record admits.**  `WalkGeom`
is `stage2Pre` unpacked, so a walk inside `Γ_stage2.pre` has a geometry to carry;
without this the invariant would be satisfiable only by a caller the record
refuses, which is the vacuity the completion conjunct exists to exclude. -/
theorem WalkGeom.nonempty {args : List Value} {m0 : Mem} {next : Nat}
    (h : Γ_stage2.pre args m0 next) : Nonempty (WalkGeom m0) := by
  have h' : stage2Pre args m0 next := h
  obtain ⟨b, n, ep, nep, xp, nxp, dst, dstcap, ndst, ev, evcap, nev, err, bs, ent,
    ndst0, nev0, -, doc, tail, entries, order, inside, esc, arenaCap, arenaRoom,
    evCap, evRoom, ndstRead, nevRead, errBytes, maxDoc, separate, hwm, hnxp, hdstcap,
    hevcap, hbpos, hbLt, hepLt, hdstLt, hevLt, hev63⟩ := h'
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
    nxpLt := hnxp
    dstcapLt := hdstcap
    evcapLt := hevcap
    bPos := hbpos
    bLt := hbLt
    epLt := hepLt
    dstLt := hdstLt
    evLt := hevLt
    ev63 := hev63
    separate := separate
    next0 := next
    watermark := hwm
  }⟩

/-- The entry count is at most the document's: the stream's positions are
strictly increasing and inside the document.  `Stage2Run.nep_le` is the same fact
at the report; the loop needs it at the staging. -/
theorem WalkGeom.nep_le {m0 : Mem} (G : WalkGeom m0) : G.nep ≤ G.n := by
  rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  exact length_le_of_pairwise_lt G.order G.inside

/-! ### The carry and the invariant -/

/-- **The staging the walk's own objects have at the adapter.**  `WalkGeom` is
`stage2Pre`'s thirteen-argument staging; the flattened body also receives the
eight objects the constraint flattening appends, plus the caller's two count
slots.  They are fixed for the run, so the carry holds them: `stage2StagedPre`
gives their presence and separation, and the log's fields are read at the log's
own address (`stage2.c`'s `ZOut` at `%z`).

The two count slots are here for the reason `stage2StagedPre` states them: the
adapter separates them from the seven scratch objects, and a caller reads them
back after the run, so the staging that the port speaks about is the seventeen-
object one. -/
structure WalkStage {m0 : Mem} (G : WalkGeom m0) where
  /-- The cursor record `%c.i`. -/
  c : Nat
  /-- The type stack `%ctype.i`. -/
  ctype : Nat
  /-- The state stack `%cst.i`. -/
  cst : Nat
  /-- The scalar token `%t352.i`. -/
  tok : Nat
  /-- The walk's own staging record `%s`. -/
  s : Nat
  /-- The log `%z`. -/
  z : Nat
  /-- The refusal record `%e`. -/
  e : Nat
  /-- The caller's entry-count slot. -/
  nkSlot : Nat
  /-- The caller's escape-count slot. -/
  nxpSlot : Nat
  /-- The staged objects are separate, as the adapter's staging states them.  The
  pre also stages `%d.i` beside this list (`stage2StagedPre`'s own entry); the
  carry names the seventeen because that is every object the walk writes. -/
  separate : DisjointRegions
    (stage2StagedRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev G.evcap
      G.ndst G.nev G.err c ctype cst tok s z e nkSlot nxpSlot)
  /-- The seven objects the walk writes are present in the staged memory. -/
  present : ∀ r ∈ stage2StagedWrites c ctype cst tok s z e, HasBytes m0 r.1 r.2
  /-- **The number path's output slot `%d.i`**, an appended parameter rather than
  one of the seven: `num_fast_el1`'s accepting arm stores the converted value
  through it (`s2NumFastFoot`'s `(out, 8)`). -/
  d : Nat
  /-- `%d.i`'s eight bytes are staged. -/
  dPresent : HasBytes m0 d 8
  /-- **`%d.i` is separate from the walk's staged objects** — the adapter's
  separation of its own slot (`stage2StagedPre_dSep`), in the orientation the
  frame's exclusions read. -/
  dSep : ∀ r ∈ stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err c ctype cst tok s z e,
    r.1 + r.2 ≤ d ∨ d + 8 ≤ r.1
  /-- **The seven appended objects end at or below the call's cursor.**  `%ei.i`,
  `%root_done.i`, `%xj.i` and `%outn.i` are the body's own four `alloca`s at
  `G.next0` (`stage2AllocaWrites`), and the seven the constraint flattening
  appends are the *caller's* objects, staged before the call — so every one of
  them, and `%d.i` too, ends at or below the cursor the callee allocates from.
  This is `Γ_stage2.pre`'s watermark statement (`stage2Pre`'s last clause, which
  `WalkGeom.watermark` carries at the thirteen ABI objects) at the objects the
  adapter appends.  It is the adapter's clause (`stage2StagedPre`'s last
  conjunct) read at the geometry: the adapter's predicate carries the call's
  `next`, so the relation between the seven and the cursor is stated where the
  caller can promise it, and `walkStage_at_pre` is what transports it here.  Its
  consumers are `WalkStage.rootSlot_log` and `WalkStage.rootSlot_ev`, and they are
  what makes the container-closing helper's root slot — and its container byte —
  fresh of the log and the event stream, so a link that calls `s2_after_value`
  needs no staging hypothesis beside it. -/
  sevenEnd : ∀ r ∈ stage2StagedWrites c ctype cst tok s z e, r.1 + r.2 ≤ G.next0

/-- **The root slot misses the log.**  `%root_done.i` is the second allocated slot
at `G.next0 + 8`, four bytes wide, and the log ends at or below `G.next0`, so the
two are separate: `walkAfterValue_facts`' depth-zero arm writes the root flag and
the log's four fields read across it. -/
theorem WalkStage.rootSlot_log {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) :
    G.next0 + 8 + 4 ≤ S.z ∨ S.z + stage2LogExtent ≤ G.next0 + 8 := by
  have h := S.sevenEnd (S.z, stage2LogExtent) (by simp [stage2StagedWrites])
  simp only [stage2LogExtent] at h ⊢
  omega

/-- **The root slot misses the event stream.**  Same slot, and the stream is one
of the thirteen ABI objects, so `WalkGeom.watermark` places its whole capacity at
or below the cursor. -/
theorem WalkStage.rootSlot_ev {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) :
    G.next0 + 8 + 4 ≤ G.ev + G.nev0 ∨ G.ev + G.evcap ≤ G.next0 + 8 := by
  have h := G.watermark (G.ev, G.evcap) (by simp [stage2Regions])
  omega


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
  /-- The event records emitted, in order, at the widths their emitters write. -/
  events : List EventRecord
  /-- The decoded bodies' document extents, in document order. -/
  spans : List (Nat × Nat)
  /-- The record in flight: its entry position, the arena offset reserved for
  its decoded body, and that body's document extent.  The extent is the third
  component rather than something the arms re-derive: `z_arena_reserve` tests
  `alen + len + 64` against the arena's capacity, and `len` — the token's
  document extent, `entry[k+1] - entry[k] - 1` — is the number the test is
  about.  Carrying it is what makes the arena trap's exclusion a statement of
  this invariant instead of a hypothesis beside it. -/
  pending : Option (Nat × Nat × Nat)
  /-- The refusal bit. -/
  refusal : Bool
  /-- The refusal offset. -/
  eoff : Nat
  /-- The block the run is at. -/
  block : String
  /-- The remaining inner work at that block. -/
  inner : Nat
  /-- The nesting depth, the index the two container stacks are written at.  It is
  `%sp.i.0248`'s value at the loop head's `phi`; the merge at `cleanup478.i` is
  the edge that moves it. -/
  sp : Nat
  /-- **The written mark of the two container stacks.**  `if.end24.i` stores at
  the register's depth `sp`, not at the mark the stack already reached, so a push
  after a pop writes below the previous mark and the mark is the largest index
  either stack has written: a push moves it to `max wlen (sp + 1)` and every
  other block leaves it alone.  The mark rather than the register's depth is what
  a byte read at `sp - 1` is found under after a pop. -/
  wlen : Nat
  /-- The type stack's contents, one byte per index below the written mark. -/
  tyMap : Nat → UInt8
  /-- The state stack's contents, one byte per index below the written mark. -/
  stMap : Nat → UInt8
  /-- The adapter's staging of the walk's own objects, fixed for the run. -/
  stage : WalkStage G

/-! ### The walk's three region lists

The record's memory claim is two claims, and the region they are stated over is a
list each:

* `walkStaged` — the objects the run *makes present*, at the extents the caller
  staged them: the arena's window (the decoded document plus the decoder's slack),
  the two cursor slots, the refusal slot, the seven appended objects and `%d.i`'s
  slot.  Every extent is a constant of the geometry, so no arm's step has to
  re-derive it as a cursor moves: presence is monotone and a store only adds
  cells.
* `walkWide` — the objects the run may *write*: the arena's decoded prefix and the
  event stream's prefix at the carried cursors (the extents the body stores into),
  the seven, `%d.i`, and the four stack objects the body allocates at the cursor
  `stage2AllocaWrites G.next0`.

The split is not a choice of presentation.  A single `Owns` at `walkWide` would
demand *presence* of the four stack bytes, which is false at the loop head: the
`alloca`s create no cells and nothing writes them until a helper stores through
them.  And a single `Owns` at the staged list only would be contradicted by every
helper call that writes a stack slot.  So the run carries presence over what the
caller staged and silence over what the run may write, and the two lists differ by
exactly the four slots.

The four are *fresh* — outside `walkStaged`'s every byte — because both lists' bases
were staged at or below `G.next0` (`G.watermark`) and every alloca entry starts
there (`stage2AllocaWrites_start`).  That is the fact the document's and the entry
stream's read proofs read: a byte inside a staged object is below `next0`, hence
outside `walkAlloca`, hence outside `walkWide`. -/

/-- The objects the run makes present, at the extents the caller staged them. -/
def walkStaged {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : List (Nat × Nat) :=
  [(G.dst, G.ndst0 + G.n + stage2ArenaReserve), (G.ndst, 8), (G.ev, G.evcap),
   (G.nev, 8), (G.err, 8)] ++
    stage2ReportScratch C.stage.c C.stage.ctype C.stage.cst C.stage.tok C.stage.s
      C.stage.z C.stage.e C.stage.d

/-- The run's write extents at the carried cursors: the arena's decoded prefix, the
seven appended objects, `%d.i`, and the event stream's prefix. -/
def walkPresent {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : List (Nat × Nat) :=
  [(G.dst, C.alen), (G.ev, C.evlen)] ++
    stage2ReportScratch C.stage.c C.stage.ctype C.stage.cst C.stage.tok C.stage.s
      C.stage.z C.stage.e C.stage.d

/-- The objects the run may write, at its cursors: the write extents above and the
body's four stack slots. -/
def walkWide {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : List (Nat × Nat) :=
  walkPresent G C ++ stage2AllocaWrites G.next0

/-- **The frame's list at the run's own cursor.**  `walkWide` names the five stack
slots the body writes *before its first allocating call*; the allocator is
monotone (`Semantics`, `.alloca`), so a run that has called a helper once writes
above them and the fixed list stops describing it.  The region a run at cursor
`next` has touched is `walkPresent` together with the interval from `G.next0` to
`next`, and `n` is that interval's extent, `next - G.next0`.

The interval is one entry rather than five: `WalkInv.next_ge` says a cursor is at
least at the end of the initialisation's four `alloca`s, and a single entry makes
the cursor's growth a one-line arithmetic step rather than a membership search.
The fixed list is the first call's bound; the record's region is this interval at
the run's own end (`stage2StackEnd`), so nothing here needs the cursor to stay
inside the five slots. -/
def walkWideAt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (n : Nat) :
    List (Nat × Nat) :=
  walkPresent G C ++ [(G.next0, n)]

/-- **The frame's list grows with the cursors.**  Every entry of the list at one
carry lies inside an entry of the list at another, when the arena's and the event
stream's cursors only advance and the staging is the same.  This is the coverage a
step that moves a cursor reads (`UnchangedOutside.write_grow`), and the two
cursor-moving stores of the arena and the event stream are its only consumers. -/
theorem walkWide_grow {m0 : Mem} {G : WalkGeom m0} {C C' : WalkCarry G}
    (hala : C.alen ≤ C'.alen) (hevl : C.evlen ≤ C'.evlen) (hstage : C'.stage = C.stage) :
    ∀ r ∈ walkWide G C, ∃ s ∈ walkWide G C', s.1 ≤ r.1 ∧ r.1 + r.2 ≤ s.1 + s.2 := by
  intro r hr
  simp only [walkWide, walkPresent, stage2ReportScratch] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_cons.mp hr with rfl | hr1
      · exact ⟨(G.dst, C'.alen), by simp [walkWide, walkPresent], le_rfl, by omega⟩
      · rcases List.mem_cons.mp hr1 with rfl | hnil
        · exact ⟨(G.ev, C'.evlen), by simp [walkWide, walkPresent], le_rfl, by omega⟩
        · exact absurd hnil (by simp)
    · exact ⟨r, by
        simp only [walkWide, walkPresent]
        refine List.mem_append_left _ (List.mem_append_right _ ?_)
        rw [hstage]
        exact hr, le_rfl, le_rfl⟩
  · exact ⟨r, by simp [walkWide, walkPresent, hr], le_rfl, le_rfl⟩

/-- A byte inside the staged objects is inside the frame's list. -/
theorem walkWide_of_staged {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {a : Nat}
    (h : inRegions (stage2ReportScratch C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d) a) :
    inRegions (walkWide G C) a := by
  obtain ⟨r, hr, hi⟩ := h
  exact ⟨r, List.mem_append_left _ (List.mem_append_right _ hr), hi⟩

/-- A byte inside the two staged prefixes is inside the frame's list. -/
theorem walkWide_of_prefix {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {a : Nat}
    (h : inRegions [(G.dst, C.alen), (G.ev, C.evlen)] a) :
    inRegions (walkWide G C) a := by
  obtain ⟨r, hr, hi⟩ := h
  exact ⟨r, List.mem_append_left _ (List.mem_append_left _ hr), hi⟩

/-- A byte inside the seven appended objects is inside the frame's list. -/
theorem walkWide_of_seven {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {a : Nat}
    (h : inRegions (stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e) a) :
    inRegions (walkWide G C) a :=
  walkWide_of_staged (inRegions_mono (fun r hr => List.mem_append_left _ hr) h)

/-- A byte inside the staged objects is inside the cursor frame's list. -/
theorem walkWideAt_of_staged {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {n a : Nat}
    (h : inRegions (stage2ReportScratch C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d) a) :
    inRegions (walkWideAt G C n) a := by
  obtain ⟨r, hr, hi⟩ := h
  exact ⟨r, List.mem_append_left _ (List.mem_append_right _ hr), hi⟩

/-- A byte inside the two staged prefixes is inside the cursor frame's list. -/
theorem walkWideAt_of_prefix {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {n a : Nat}
    (h : inRegions [(G.dst, C.alen), (G.ev, C.evlen)] a) :
    inRegions (walkWideAt G C n) a := by
  obtain ⟨r, hr, hi⟩ := h
  exact ⟨r, List.mem_append_left _ (List.mem_append_left _ hr), hi⟩

/-- A byte inside the seven appended objects is inside the cursor frame's list. -/
theorem walkWideAt_of_seven {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {n a : Nat}
    (h : inRegions (stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e) a) :
    inRegions (walkWideAt G C n) a :=
  walkWideAt_of_staged (inRegions_mono (fun r hr => List.mem_append_left _ hr) h)

/-- **A byte of the cursor's interval is inside the cursor frame's list.**  The
interval's entry starts at the staging's cursor, so its bytes are the ones above
`G.next0` and below `G.next0 + n`. -/
theorem walkWideAt_alloca {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {n a : Nat}
    (hlo : G.next0 ≤ a) (hhi : a < G.next0 + n) :
    inRegions (walkWideAt G C n) a :=
  ⟨(G.next0, n), List.mem_append_right _ (List.mem_cons_self), hlo, hhi⟩

/-- **The region grows with the carry and the cursor.**  Every entry of the list at
one carry and cursor lies inside an entry at a later carry and cursor, when the
arena and the event stream only advance, the staging is the same and the cursor
only moves forward.  This is the coverage a step that moves a cursor reads
(`UnchangedOutside.write_grow`). -/
theorem walkWideAt_grow {m0 : Mem} {G : WalkGeom m0} {C C' : WalkCarry G}
    {n n' : Nat} (hala : C.alen ≤ C'.alen) (hevl : C.evlen ≤ C'.evlen)
    (hstage : C'.stage = C.stage) (hn : n ≤ n') :
    ∀ r ∈ walkWideAt G C n, ∃ s ∈ walkWideAt G C' n',
      s.1 ≤ r.1 ∧ r.1 + r.2 ≤ s.1 + s.2 := by
  intro r hr
  simp only [walkWideAt, walkPresent, stage2ReportScratch] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_cons.mp hr with rfl | hr1
      · exact ⟨(G.dst, C'.alen), by simp [walkWideAt, walkPresent], le_rfl, by omega⟩
      · rcases List.mem_cons.mp hr1 with rfl | hnil
        · exact ⟨(G.ev, C'.evlen), by simp [walkWideAt, walkPresent], le_rfl, by omega⟩
        · exact absurd hnil (by simp)
    · exact ⟨r, by
        simp only [walkWideAt, walkPresent]
        refine List.mem_append_left _ (List.mem_append_right _ ?_)
        rw [hstage]
        exact hr, le_rfl, le_rfl⟩
  · rcases List.mem_cons.mp hr with rfl | hnil
    · exact ⟨(G.next0, n'), by
        change (G.next0, n') ∈ walkPresent G C' ++ [(G.next0, n')]
        exact List.mem_append_right _ (List.mem_cons_self ..), le_rfl, by omega⟩
    · exact absurd hnil (by simp)

/-- **A later cursor makes a weaker claim**, so the earlier cursor's frame implies
it: every entry at `n` lies inside the interval at `n'` when `n ≤ n'`. -/
theorem walkWideAt_le {m0 m : Mem} {G : WalkGeom m0} {C : WalkCarry G} {n n' : Nat}
    (hn : n ≤ n') (h : UnchangedOutside m0 m (walkWideAt G C n)) :
    UnchangedOutside m0 m (walkWideAt G C n') := by
  refine UnchangedOutside.of_covered h ?_
  intro r hr
  change r ∈ walkPresent G C ++ [(G.next0, n)] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, by
      change r ∈ walkPresent G C ++ [(G.next0, n')]
      exact List.mem_append_left _ hr, le_rfl, le_rfl⟩
  · rcases List.mem_cons.mp hr with rfl | hnil
    · exact ⟨(G.next0, n'), by
        change (G.next0, n') ∈ walkPresent G C ++ [(G.next0, n')]
        exact List.mem_append_right _ (List.mem_cons_self ..), le_rfl, by omega⟩
    · exact absurd hnil (by simp)

/-- The interval's own entry is in the cursor's list. -/
theorem mem_walkWideAt_interval {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {n : Nat} :
    (G.next0, n) ∈ walkWideAt G C n := by
  change (G.next0, n) ∈ walkPresent G C ++ [(G.next0, n)]
  exact List.mem_append_right _ (List.mem_cons_self ..)

/-- A present entry is in the cursor's list. -/
theorem mem_walkWideAt_present {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {n : Nat}
    {r : Nat × Nat} (h : r ∈ walkPresent G C) : r ∈ walkWideAt G C n := by
  change r ∈ walkPresent G C ++ [(G.next0, n)]
  exact List.mem_append_left _ h

/-- **The four allocated slots and the first call's `%ei`, as members.**  The
memberships are stated once here rather than proved by `simp` at each of the five
cases: the list is a literal and the constructors are the whole proof. -/
theorem mem_allocaWrites_0 (a : Nat) : (a, 8) ∈ stage2AllocaWrites a := by
  unfold stage2AllocaWrites
  exact List.mem_cons_self ..

theorem mem_allocaWrites_8 (a : Nat) : (a + 8, 4) ∈ stage2AllocaWrites a := by
  unfold stage2AllocaWrites
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem mem_allocaWrites_12 (a : Nat) : (a + 12, 8) ∈ stage2AllocaWrites a := by
  unfold stage2AllocaWrites
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem mem_allocaWrites_20 (a : Nat) : (a + 20, 8) ∈ stage2AllocaWrites a := by
  unfold stage2AllocaWrites
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..)))

theorem mem_allocaWrites_28 (a : Nat) : (a + 28, 8) ∈ stage2AllocaWrites a := by
  unfold stage2AllocaWrites
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- **The five slots cover their whole window.**  They are contiguous — `8 + 4 + 8 +
8 + 8 = 36 = stage2BootstrapExtent + 8` — so a byte at or above the cursor and
below the window's end is inside one of them.  This is what makes the five slots a
consequence of a stack region that covers their window, rather than a region
stated separately from it. -/
theorem allocaWrites_cover {a x : Nat} (hlo : a ≤ x)
    (hhi : x < a + (stage2BootstrapExtent + 8)) :
    inRegions (stage2AllocaWrites a) x := by
  have h36 : a + (stage2BootstrapExtent + 8) = a + 36 := by
    simp [stage2BootstrapExtent]
  rw [h36] at hhi
  rcases Nat.lt_or_ge x (a + 8) with h1 | h1
  · exact ⟨(a, 8), mem_allocaWrites_0 a, by omega, by omega⟩
  rcases Nat.lt_or_ge x (a + 12) with h2 | h2
  · exact ⟨(a + 8, 4), mem_allocaWrites_8 a, by omega, by omega⟩
  rcases Nat.lt_or_ge x (a + 20) with h3 | h3
  · exact ⟨(a + 12, 8), mem_allocaWrites_12 a, by omega, by omega⟩
  rcases Nat.lt_or_ge x (a + 28) with h4 | h4
  · exact ⟨(a + 20, 8), mem_allocaWrites_20 a, by omega, by omega⟩
  · exact ⟨(a + 28, 8), mem_allocaWrites_28 a, by omega, by omega⟩

/-- info: 'LeanLLVM.Refinement.allocaWrites_cover' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.allocaWrites_cover

/-- info: 'LeanLLVM.Refinement.walkWideAt_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkWideAt_le

/-- **A byte below the cursor is outside the cursor's interval**, which is the
half of the frame's list the `next_ge` interval contributes: the interval starts at
`G.next0`, so a byte the staging placed below it is not in it. -/
theorem not_interval_of_lt {m0 : Mem} {G : WalkGeom m0} {n a : Nat}
    (h : a < G.next0) :
    ¬ inRegions [(G.next0, n)] a := by
  rintro ⟨r, hr, hlo, hhi⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  omega

/-- A byte below the watermark is outside the four stack slots. -/
theorem not_walkAlloca_of_lt {m0 : Mem} {G : WalkGeom m0} {a : Nat}
    (h : a < G.next0) :
    ¬ inRegions (stage2AllocaWrites G.next0) a :=
  not_inRegions_allocaWrites h

/-- **A byte of a staged ABI object is below the watermark.**  The staging's
entries are the objects the read proofs exclude, and each ends at or below the
cursor, so every byte of one is below it — and therefore outside the four stack
slots. -/
theorem staged_lt_watermark {m0 : Mem} {G : WalkGeom m0} {r : Nat × Nat} {a : Nat}
    (hr : r ∈ stage2Regions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev G.evcap
      G.ndst G.nev G.err)
    (ha : a < r.1 + r.2) : a < G.next0 :=
  Nat.lt_of_lt_of_le ha (G.watermark r hr)

/-- A write at a byte the frame's list covers leaves the frame.  The list is the
cursor's (`walkWideAt`), so the cursor is implicit in the caller's frame. -/
theorem walkFrame_write_inside {m0 m : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {n a : Nat} {bs : List UInt8}
    (h : UnchangedOutside m0 m (walkWideAt G C n))
    (hw : ∀ k, k < bs.length → inRegions (walkWideAt G C n) (a + k)) :
    UnchangedOutside m0 (writeBytes m a bs) (walkWideAt G C n) :=
  h.write_inside hw

/-- A store at a byte inside one of the walk's staged extents preserves the frame
(the common shape: the cursor record's field, the two stacks, the log's fields). -/
theorem walkFrame_write_staged {m0 m : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {n a : Nat} {bs : List UInt8}
    (h : UnchangedOutside m0 m (walkWideAt G C n))
    (hw : ∀ k, k < bs.length →
      inRegions (stage2ReportScratch C.stage.c C.stage.ctype C.stage.cst
        C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d) (a + k)) :
    UnchangedOutside m0 (writeBytes m a bs) (walkWideAt G C n) :=
  h.write_inside (fun k hk => walkWideAt_of_staged (hw k hk))

/-- Presence is monotone under a write.  The target memory is named so that a
caller states the memory the run left rather than having the write inferred from
the goal: a step's memory is a stack of writes, and the caller's `rfl` fixes the
inner one. -/
theorem walkStaged_write {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {m m' : Mem}
    {a : Nat} {bs : List UInt8}
    (hm : m' = writeBytes m a bs)
    (h : ∀ r ∈ walkStaged G C, HasBytes m r.1 r.2) :
    ∀ r ∈ walkStaged G C, HasBytes m' r.1 r.2 := by
  subst hm
  exact fun r hr => hasBytes_writeBytes (h r hr)

/-- A scan's counter at a block that reads it: the counter register holds `i`,
the scan's own bound register holds `c`, and the remaining work `c - i` is inside
the iteration's remaining inner budget.  Every scan tests its counter for equality
with that bound, so the two registers are what both its guard and its measure are
read from, and `c - i ≤ inner` is what makes the step's decrement safe. -/
def ScanCount (s : State) (phi cond : String) (inner : Nat) : Prop :=
  ∃ i c : Nat, c - i ≤ inner ∧ i < c ∧ c < 2 ^ 64 ∧
    lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)) ∧
    lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c))

/-- The same at a scan's landing block.  The counter is the increment the latch
wrote — `BlockEval`'s `phi` selects it because the predecessor names the latch —
and the bound register is the one the latch read. -/
def ScanLanded (s : State) (src inc cond : String) (inner : Nat) : Prop :=
  ∃ i c : Nat, c - i ≤ inner ∧ i < c ∧ c < 2 ^ 64 ∧
    s.pre = some src ∧
    lookupName s.env inc = some (.int 64 (BitVec.ofNat 64 i)) ∧
    lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c))

/-- **The guard that is false**, kept as the record of the hypothesis the traversal
bundles carried.  It quantifies over *every* pair of naturals whose words are the
two registers' with `c - i ≤ inner` and concludes `i + 1 < c`; the pair `i = c`
satisfies the premise (`c - i = 0`) and fails the conclusion, so the predicate holds
at no state whose registers hold words.  Nothing takes it: a visit's `i + 1 < c` is a
premise of the round (`scanRound_at`, `JsonStage2WalkRevolutionScanRound`) and the
bundles' rows are the round's own `∀`, stated at the state's cells below the word's
width. -/
def ScanGuard (s : State) (phi cond : String) (inner : Nat) : Prop :=
  ∀ i c : Nat, c - i ≤ inner →
    lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)) →
    lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)) →
    i + 1 < c

/-- **The inner work one iteration is allowed**, the inner component's bound and
the radix's base in `walkMeasure`.  It is a budget shared by the whole iteration,
not one scan's remaining work: the scans reset the inner component as each one is
entered, so the measure rises across an entry unless the value it carries is a
resource the whole iteration draws on.  Four scans may each walk the document, and
the literal comparison adds at most five bytes, so `4 * n + 5` covers every path
the dispatch has.  It is a completion witness and not a tight bound. -/
def walkInnerCap {m0 : Mem} (G : WalkGeom m0) : Nat := 4 * G.n + 5

/-- **A scan's landing block entered from its first predecessor.**  A scan's
landing block (`land.rhs*`) has two predecessors: its latch, on the back edge, and
the block that enters the scan first.  Only the back edge has the latch's
increment to read, so on the entry edge the counter is the value the landing
block's own `phi` will select from that predecessor, and the fact is that value —
not `ScanLanded`'s, which is about the other edge.  A landing block's local fact
is therefore the disjunction of the two. -/
def ScanEntered (s : State) (src counter cond : String) (inner : Nat) : Prop :=
  ∃ i c : Nat, c - i ≤ inner ∧ i < c ∧ c < 2 ^ 64 ∧ s.pre = some src ∧
    lookupName s.env counter = some (.int 64 (BitVec.ofNat 64 i)) ∧
    lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c))

/-- **A scan's landing block where the scan has no bytes: the counter and the bound
are the same word.**  Both arms above require `i < c`, so a scan the walk's guard does
not enter has no local fact at its landing block — and the walk reaches
`land.rhs457.i` with `%ee.1.i = %cond350.i`: on the arm whose last entry byte is not
whitespace, the token's end *is* the entry's end, so the copy call's target tests
`ult %ee.1.i %cond350.i` false and jumps to `if.end473.i`, leaving `land.rhs457.i` as
the sibling it never visits.

**A vocabulary that has no fact for a state the model reaches is a defect in the
vocabulary**, so the local fact gains this third disjunct rather than a relaxation of
`ScanEntered`: relaxing `i < c` to `i ≤ c` would weaken every existing consumer's
conclusion, while a new disjunct is additive and each consumer discharges the new case
from its own `i < c`.  The budget condition is omitted for the same reason it is
vacuous here — no work remains, so `c - c = 0` covers it. -/
def ScanEmpty (s : State) (counter cond : String) : Prop :=
  ∃ c : Nat, c < 2 ^ 64 ∧
    lookupName s.env counter = some (.int 64 (BitVec.ofNat 64 c)) ∧
    lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c))

/-- The block-local half of the invariant: the remaining budget's coverage of the
work still to do, and the registers it is read from, at the ten blocks whose
carrier is not `True` — the literal comparison's two and each of the four scans'
latch and landing.  A landing block
has two predecessors, so its fact is disjunctive: `ScanLanded` on the latch's back
edge and `ScanEntered` on the edge that first enters the scan, and the literal
comparison's landing block is the same pair (the latch's `%inc.i.i` or
`if.end48.i`'s zero).  At every other block it is `True`; pinning it there is the
remaining arm's work (the entry loop's), and the module docstring says so rather
than claiming a bound it does not have.

**The extra-token scan's landing has a third disjunct.**  `land.rhs457.i` is reachable
with `%ee.1.i = %cond350.i` — the arm whose byte before the entry's end is not
whitespace reaches it with the token ending exactly at the entry's end — and there the
scan is not entered at all, so neither `ScanLanded` nor `ScanEntered` holds.  That state
is why `ScanEmpty` exists; the other landings have not been shown to need it, and adding
it only where a reachable state requires it keeps the change additive.

**The loop head carries its own guard.**  `NodeBlock21` is entered only with an entry
left — `%k.0.i249 < %nep` is the test that sends the walk into the body — so the head's
clause is `C.k < G.nep`.  It is the one clause stated on the carry's index and not on a
register, and it is what `WalkLoopEnd.facts`' producer reads to know the last entry's
index: `WalkInv.k_le` bounds the index by the count, and with the head's guard the
consumer's `¬ (C.k + 1 < G.nep)` makes `C.k + 1 = G.nep` follow.  The seed supplies it
(`walkSeed_invariant`, at `0 < G.nep`) and the header's pass preserves it
(`whileBody_step`, whose guard `k < G.nep` is the target's). -/
def WalkLocal {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : Prop :=
  if C.block = "for.inc.i.i" then
    ∃ i c : Nat, c - i ≤ C.inner ∧ i < c ∧ c < 2 ^ 64 ∧
      lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))
  else if C.block = "for.body.i.i" then
    ((∃ i c : Nat, c - i ≤ C.inner ∧ i < c ∧ c < 2 ^ 64 ∧
        s.pre = some "for.inc.i.i" ∧
        lookupName s.env "%inc.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
        lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))) ∨
      (∃ c : Nat, c ≤ C.inner ∧ 0 < c ∧ c < 2 ^ 64 ∧
        s.pre = some "if.end48.i" ∧
        lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))))
  else if C.block = "while.body370.i" then
    ScanCount s "%ee.0.i238" "%cond350.i" C.inner
  else if C.block = "land.rhs.i" then
    (ScanLanded s "while.body370.i" "%inc371.i" "%cond350.i" C.inner ∨
      ScanEntered s "land.rhs.i.preheader" "%idxprom.i" "%cond350.i" C.inner)
  else if C.block = "while.body.i104" then
    ScanCount s "%ee.011.i" "%cond.i" C.inner
  else if C.block = "land.rhs.i103" then
    (ScanLanded s "while.body.i104" "%inc.i105" "%cond.i" C.inner ∨
      ScanEntered s "cond.end.i96" "%idxprom.i" "%cond.i" C.inner)
  else if C.block = "while.body76.i" then
    ScanCount s "%s2.020.i" "%cond.i" C.inner
  else if C.block = "land.rhs71.i" then
    (ScanLanded s "while.body76.i" "%inc77.i" "%cond.i" C.inner ∨
      ScanEntered s "if.end67.i" "%ee.0.lcssa.i" "%cond.i" C.inner)
  else if C.block = "while.body462.i" then
    ScanCount s "%q.0.i246" "%cond350.i" C.inner
  else if C.block = "land.rhs457.i" then
    (ScanLanded s "while.body462.i" "%inc463.i" "%cond350.i" C.inner ∨
      ScanEntered s "if.then447.i" "%ee.1.i" "%cond350.i" C.inner ∨
      ScanEmpty s "%ee.1.i" "%cond350.i")
  else if C.block = "NodeBlock21" then C.k < G.nep
  else True

/-- **The pointer registers the dispatch's blocks read**, in one place.

`%3` and `%5` are `entry`'s two loads — the document's base and the entry
stream's base — and the four others are the addresses the header and the nesting
arm read: `%k11.i` is the cursor record's `k` field (`%c.i + 32`), `%ctype.i` and
`%cst.i` are the two container stacks' bases, and `%hash1.i.i` is the log's hash
word (`%z + 32`).  Each is bound before the loop and no block of the dispatch
rebinds one, which is why the invariant carries them as bindings: a block's
`denoteCode` reads them, and the carry is where the run's fixed addresses live.
`WalkPtrs.bind` is the step that says a bind at any other name preserves all six.

They are binding facts about the emitted body rather than clauses about the
walk's memory — `%3`'s *value* is the document's address, and only the
initialisation knows it is `G.b` — so they sit beside `blockIndex` and
`depth_reg` rather than with the log's fields, and their production is the seed's. -/
def WalkPtrs {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (env : Env) : Prop :=
  lookupName env "%3" = some (.ptr G.b) ∧
    lookupName env "%5" = some (.ptr G.ep) ∧
    lookupName env "%k11.i" = some (.ptr (C.stage.c + 32)) ∧
    lookupName env "%ctype.i" = some (.ptr C.stage.ctype) ∧
    lookupName env "%cst.i" = some (.ptr C.stage.cst) ∧
    lookupName env "%hash1.i.i" = some (.ptr (C.stage.z + 32))

/-- **A bind at another name preserves all six pointer registers.**  Each
disequality is a literal comparison, so an arm discharges it with `decide`; the
six conclusions are the six cells read back out of the extended environment. -/
theorem WalkPtrs.bind {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkPtrs G C env) {d : String} {v : Value}
    (h3 : ¬ d = "%3") (h5 : ¬ d = "%5") (hk : ¬ d = "%k11.i")
    (hc : ¬ d = "%ctype.i") (hs : ¬ d = "%cst.i") (hh : ¬ d = "%hash1.i.i") :
    WalkPtrs G C ((d, v) :: env) := by
  obtain ⟨hd3, hd5, hdk, hdc, hds, hdh⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [lookupName, ite_eq_right h3]; exact hd3
  · simp only [lookupName, ite_eq_right h5]; exact hd5
  · simp only [lookupName, ite_eq_right hk]; exact hdk
  · simp only [lookupName, ite_eq_right hc]; exact hdc
  · simp only [lookupName, ite_eq_right hs]; exact hds
  · simp only [lookupName, ite_eq_right hh]; exact hdh

/-- **A run of two binds at other names preserves the six pointer registers.** -/
theorem WalkPtrs.bind_pair {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkPtrs G C env) {a b : String} {va vb : Value}
    (ha : ¬ a = "%3" ∧ ¬ a = "%5" ∧ ¬ a = "%k11.i" ∧ ¬ a = "%ctype.i"
      ∧ ¬ a = "%cst.i" ∧ ¬ a = "%hash1.i.i")
    (hb : ¬ b = "%3" ∧ ¬ b = "%5" ∧ ¬ b = "%k11.i" ∧ ¬ b = "%ctype.i"
      ∧ ¬ b = "%cst.i" ∧ ¬ b = "%hash1.i.i") :
    WalkPtrs G C ((b, vb) :: (a, va) :: env) :=
  (h.bind ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2).bind
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2

/-! ### The two register carriers

The dispatch's blocks read registers the invariant did not bind, and a link's
successor hypotheses have to come from somewhere.  There are two kinds, and they
are different kinds:

* **static** registers, bound once by `entry` or `while.body.i.lr.ph` and never
  rebound.  Their values are fixed by the staging — the `%z`/`%s`/`%c.i`
  offsets, the document base's predecessor, and the four stack objects' slots at
  the call's cursor — so `WalkRegs` is a lookup per name, and a run that binds
  none of them keeps every one by `denoteCode_lookupName`.
* **per-iteration** registers, rebound by the header on every pass: `%7` is the
  entry stream's lane at the carried index, `%8` the document byte that lane
  selects, and `%arrayidx10.i` the token's position address (`%3 + %idxprom.i` at
  `%3 = G.b`).  Their values are functions of the carry's `k`, so `WalkIter` states
  them at `entryPos G C.k`, `entryByte G C.k` and `G.b + entryPos G C.k` rather
  than at constants, and the header's step (`whileBody_step`) is what produces them.

`WalkIter` is a clause at every loop state because the header binds all three before
the dispatch runs, and every block between it and the next header leaves them
alone.  The paths that never pass the header — the preheader and `entry` itself
— are not loop states, so the carrier is not a claim about them; the seed is the
first state it is asserted at.

The container stacks' *contents* are a third carrier, and their shape is set by
what a push and a pop do to them: a clause of the form "the byte at `sp - 1` is
`t`" cannot be carried by a link that pushes or pops, because the byte at the new
`sp - 1` was written at an earlier index and the carry does not remember it.  The
sound shape is a carried map `Nat → UInt8`, read off the stack's own bytes at the
carried written mark.  `WalkStackBytes`, in this module, states it, and
proves its laws: a push extends the map at the index it writes, whether that index
is the written mark or, after a pop, below it (`WalkStackBytes.pushAt`/`pushNatAt`),
a one-byte store rewrites it where it writes at any index
(`WalkStackBytes.storeAt`/`storeNatAt`), a pop or the merge at `cleanup478.i` is a
restriction (`WalkStackBytes.restrict`), and `s2_value_pos` reads the map at
`sp - 1` (`walkStack_valuePos`).  `walkStack_ifEnd24_at` composes the push link's
two writes at `ctype + sp` and `cst + sp` into one update of both maps, at the
written mark `max wlen (sp + 1)`.

Those maps are carried: `WalkCarry.wlen` is the written mark and `tyMap`/`stMap`
the two maps, and `WalkInv` states `sp ≤ wlen`, `wlen ≤ stage2StackExtent` and one
`WalkStackBytes` per stack.  Every link of the six modules builds the four
clauses — unchanged where the block writes elsewhere, `walkStack_ifEnd24_at` at
the nesting arm's push, `WalkStackBytes.storeAt` at the class-D stores, and
`WalkStackBytes.write_outside` against a staged object, the cursor record, `%d.i`
or the allocas at the rest.  Nothing beside them is owed: the class-D stores need
no `sp - 1` specification because `storeAt` is stated at an arbitrary index, and
the helper that advances the state stack's top is `walkAfterValue_stBytesAt` with
`walkAfterValueMapAt`'s map. -/

/-- The entry stream's position at index `k`, with `0` past the end.  The
carrier is read at an index the loop's own bound keeps inside the stream, so the
default is a totalisation, not a case the walk takes. -/
def entryPos {m0 : Mem} (G : WalkGeom m0) (k : Nat) : Nat :=
  G.ent.getD k 0

/-- The document byte the entry at index `k` selects, with `0` past the end.
`%8` is `entry[%idxprom.i]`, so this is the value the header binds. -/
def entryByte {m0 : Mem} (G : WalkGeom m0) (k : Nat) : UInt8 :=
  G.bs.getD (entryPos G k) 0

/-- The static names the carrier binds, as the list `walkStaticRegs`' keys.  It
is a literal, and `walkStaticRegs_names` is the `rfl` that says the two lists are
the same one, so a name cannot enter one without entering the other. -/
def walkStaticNames : List String :=
  ["%nsp", "%xp1", "%nxp2", "%n2.i", "%ep3.i", "%len", "%cap", "%0",
   "%h1.i.i.i51", "%ar", "%alen", "%acap", "%gap.i", "%end.i", "%kind404.i",
   "%n6.i", "%ix.i", "%nix.i", "%e7.i", "%invariant.gep", "%ei.i",
   "%root_done.i", "%xj.i", "%outn.i", "%nep", "%c.i", "%z", "%xp", "%nxp",
   "%4", "%t352.i", "%e", "%s", "%ndst", "%nev", "%err"]

/-- The static address registers the dispatch reads, beside `WalkPtrs`' six: the
`%s` record's fields, the log's six addresses the reserves and the merges read,
the token's three, the cursor record's five, the document base's predecessor, the
four stack objects at the call's cursor, and the four parameters the string
path's links read directly — the two staging records `%c.i` and `%z`, and the
escape list `%xp` with its count `%nxp`.  `%4` is the stream's end — the document
length word the caller staged — and `%t352.i` and `%e` are the token record's and
the refusal record's addresses, which the last entry's merge and its tails read.
`%s`, `%ndst`, `%nev` and `%err` are the record and the three ABI bases the
finalisation's two copies read: the four are staging parameters the caller binds
once, which is why `WalkFinalEnv` is a reading of this carrier at the merge rather
than a supply.  Every one is bound before the loop and no block of the dispatch
rebinds it. -/
def walkStaticRegs {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : List (String × Value) :=
  [("%nsp", .ptr (C.stage.s + 56)), ("%xp1", .ptr (C.stage.s + 72)),
   ("%nxp2", .ptr (C.stage.s + 80)), ("%n2.i", .ptr (C.stage.s + 8)),
   ("%ep3.i", .ptr (C.stage.s + 48)),
   ("%len", .ptr (C.stage.z + 8)), ("%cap", .ptr (C.stage.z + 16)),
   ("%0", .ptr (C.stage.z + 24)), ("%h1.i.i.i51", .ptr (C.stage.z + 24)),
   ("%ar", .ptr (C.stage.z + 40)), ("%alen", .ptr (C.stage.z + 48)),
   ("%acap", .ptr (C.stage.z + 56)),
   ("%gap.i", .ptr (C.stage.tok + 20)), ("%end.i", .ptr (C.stage.tok + 8)),
   ("%kind404.i", .ptr (C.stage.tok + 16)),
   ("%n6.i", .ptr (C.stage.c + 8)), ("%ix.i", .ptr (C.stage.c + 16)),
   ("%nix.i", .ptr (C.stage.c + 24)), ("%e7.i", .ptr (C.stage.c + 1112)),
   ("%invariant.gep", .ptr (G.b - 1)),
   ("%ei.i", .ptr G.next0), ("%root_done.i", .ptr (G.next0 + 8)),
   ("%xj.i", .ptr (G.next0 + 12)), ("%outn.i", .ptr (G.next0 + 20)),
   ("%nep", .int 64 (BitVec.ofNat 64 G.nep)),
   ("%c.i", .ptr C.stage.c), ("%z", .ptr C.stage.z),
   ("%xp", .ptr G.xp), ("%nxp", .int 64 (BitVec.ofNat 64 G.nxp)),
   ("%4", .int 64 (BitVec.ofNat 64 G.n)), ("%t352.i", .ptr C.stage.tok),
   ("%e", .ptr C.stage.e), ("%s", .ptr C.stage.s), ("%ndst", .ptr G.ndst),
   ("%nev", .ptr G.nev), ("%err", .ptr G.err)]

/-- The names a run must avoid to keep both carriers.  `%inc.i` is here as well as
the three per-iteration registers: its cell is `WalkInv.inc_reg`'s, keyed on `C.k`,
and a run that binds it must be the header's own pass.  `%idxprom.i` is here for
the same reason — its cell is `WalkInv.idx_reg`'s, also keyed on `C.k`. -/
def walkCarriedNames : List String :=
  "%inc.i" :: "%7" :: "%8" :: "%arrayidx10.i" :: "%idxprom.i" :: walkStaticNames

/-- **A bind destination fresh from the register carriers.**  A block whose run
binds none of these keeps `WalkRegs` (the static list), `WalkInv.inc_reg`
(`%inc.i`, whose cell is keyed on `C.k`), `WalkInv.idx_reg` (`%idxprom.i`, keyed
on it too) and `WalkIter.regarr` (`%arrayidx10.i`, whose cell is keyed on the
carried index as well). -/
abbrev walkFreshName (d : String) : Prop :=
  d ∉ walkStaticNames ∧ d ≠ "%inc.i" ∧ d ≠ "%arrayidx10.i" ∧ d ≠ "%idxprom.i"

/-- The per-iteration registers a bind must avoid to keep `WalkIter`'s three
clauses. -/
abbrev walkIterFresh (d : String) : Prop :=
  d ≠ "%7" ∧ d ≠ "%8" ∧ d ≠ "%arrayidx10.i"

/-- The key list and the register list name the same names. -/
theorem walkStaticRegs_names {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) :
    (walkStaticRegs G C).map Prod.fst = walkStaticNames := rfl

/-- **The static carrier**: every register `walkStaticRegs` names holds the value
the staging fixes for it.  A bind, or a run that binds none of the names, keeps
it — the lookup is per name and no memory is involved. -/
def WalkRegs {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (env : Env) : Prop :=
  ∀ p ∈ walkStaticRegs G C, lookupName env p.1 = some p.2

/-- **The per-iteration carrier**: `%7` is the entry stream's lane at the carried
index, `%8` is the document byte that lane selects, and `%arrayidx10.i` is the
token's position address — the header's `%3 + %idxprom.i` at `%3 = G.b`.  All
three are rebound by `while.body.i`, so the clause is a function of `C.k`, not a
constant; the header's step produces it and every other block's run leaves it
alone. -/
structure WalkIter {m0 : Mem} (G : WalkGeom m0) (k : Nat) (env : Env) : Prop where
  /-- `%7` holds the lane at the carried index. -/
  reg7 : lookupName env "%7" = some (.int 32 (BitVec.ofNat 32 (entryPos G k)))
  /-- `%8` holds the document byte the lane selects. -/
  reg8 : lookupName env "%8" = some (.int 8 (BitVec.ofNat 8 (entryByte G k).toNat))
  /-- `%arrayidx10.i` holds the token's position address, `G.b + entryPos G k`. -/
  regarr : lookupName env "%arrayidx10.i" = some (.ptr (G.b + entryPos G k))

/-- A name the builder does not bind reads through to the incoming environment. -/
theorem lookupName_cells_of_notin :
    ∀ (cs : List (String × Value)) (n : String) (env : Env),
      n ∉ cs.map (·.1) → lookupName (cells cs env) n = lookupName env n
  | [], _, _, _ => rfl
  | (k, v) :: cs, n, env, h => by
      have hk : k ≠ n := by intro hkn; exact h (by subst hkn; simp)
      simp only [cells, lookupName_cons_ne v (cells cs env) hk]
      exact lookupName_cells_of_notin cs n env (fun hc => h (List.mem_cons_of_mem _ hc))

/-- A name of a cell list's keys is one of a list that contains every key. -/
theorem mem_names_of_cells {cs : List (String × Value)} {ns : List String}
    (h : ∀ c ∈ cs, c.1 ∈ ns) : ∀ n, n ∈ cs.map (·.1) → n ∈ ns := by
  intro n hn
  obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hn
  rw [← hcn]
  exact h c hc

/-- A bind at a name outside the carrier leaves it alone. -/
theorem WalkRegs.bind {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkRegs G C env) {d : String} {v : Value}
    (hd : d ∉ walkStaticNames) : WalkRegs G C ((d, v) :: env) := by
  intro p hp
  have hpd : p.1 ≠ d := by
    intro h'
    apply hd
    rw [← walkStaticRegs_names G C, List.mem_map]
    exact ⟨p, hp, h'⟩
  rw [lookupName_cons_ne v env (Ne.symm hpd)]
  exact h p hp

/-- A cell list none of whose names is a carrier name leaves the carrier alone. -/
theorem WalkRegs.cells_of {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkRegs G C env) (cs : List (String × Value))
    (hne : ∀ n ∈ cs.map (·.1), n ∉ walkStaticNames) : WalkRegs G C (cells cs env) := by
  intro p hp
  have hpnot : p.1 ∉ cs.map (·.1) := by
    intro hin
    exact hne p.1 hin (by
      rw [← walkStaticRegs_names G C]
      exact List.mem_map_of_mem hp)
  rw [lookupName_cells_of_notin cs p.1 env hpnot]
  exact h p hp

/-- **A cell list whose keys are a literal list keeps the carrier**, decided on
the names alone: the bridge between `cells_of`'s membership hypothesis and a
`decide` over strings. -/
theorem WalkRegs.names_of_eq {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkRegs G C env) (ns : List String) {cs : List (String × Value)}
    (hnames : cs.map (·.1) = ns) (hne : ∀ n ∈ ns, n ∉ walkStaticNames) :
    WalkRegs G C (cells cs env) :=
  h.cells_of _ (fun n hn => hne n (hnames ▸ hn))

/-- Two binds at names outside the carrier leave it alone. -/
theorem WalkRegs.bind_pair {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkRegs G C env) {a b : String} {va vb : Value}
    (ha : a ∉ walkStaticNames) (hb : b ∉ walkStaticNames) :
    WalkRegs G C ((b, vb) :: (a, va) :: env) :=
  (h.bind ha).bind hb

/-- A bind at a name outside the carrier leaves the per-iteration carrier alone. -/
theorem WalkIter.bind {m0 : Mem} {G : WalkGeom m0} {k : Nat} {env : Env}
    (h : WalkIter G k env) {d : String} {v : Value}
    (hfr : walkIterFresh d) : WalkIter G k ((d, v) :: env) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lookupName_cons_ne v env hfr.1]; exact h.reg7
  · rw [lookupName_cons_ne v env hfr.2.1]; exact h.reg8
  · rw [lookupName_cons_ne v env hfr.2.2]; exact h.regarr

/-- Two binds at names outside the carrier leave the per-iteration carrier alone. -/
theorem WalkIter.bind_pair {m0 : Mem} {G : WalkGeom m0} {k : Nat} {env : Env}
    (h : WalkIter G k env) {a b : String} {va vb : Value}
    (ha : walkIterFresh a) (hb : walkIterFresh b) :
    WalkIter G k ((b, vb) :: (a, va) :: env) :=
  (h.bind ha).bind hb

/-- A cell list that names none of `walkCarriedNames` leaves the carrier alone. -/
theorem WalkIter.cells_of {m0 : Mem} {G : WalkGeom m0} {k : Nat} {env : Env}
    (h : WalkIter G k env) (cs : List (String × Value))
    (hne : ∀ n ∈ cs.map (·.1), n ∉ walkCarriedNames) :
    WalkIter G k (cells cs env) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lookupName_cells_of_notin cs "%7" env
      (fun hin => hne "%7" hin (by simp [walkCarriedNames]))]
    exact h.reg7
  · rw [lookupName_cells_of_notin cs "%8" env
      (fun hin => hne "%8" hin (by simp [walkCarriedNames]))]
    exact h.reg8
  · rw [lookupName_cells_of_notin cs "%arrayidx10.i" env
      (fun hin => hne "%arrayidx10.i" hin (by simp [walkCarriedNames]))]
    exact h.regarr

-- The bridge for the per-iteration carrier, after `cells_of`.
/-- The per-iteration carrier through a cell list whose keys are a literal list. -/
theorem WalkIter.names_of_eq {m0 : Mem} {G : WalkGeom m0} {k : Nat} {env : Env}
    (h : WalkIter G k env) (ns : List String) {cs : List (String × Value)}
    (hnames : cs.map (·.1) = ns) (hne : ∀ n ∈ ns, n ∉ walkCarriedNames) :
    WalkIter G k (cells cs env) :=
  h.cells_of _ (fun n hn => hne n (hnames ▸ hn))

/-- **The preheader's five binds are the staging's own values.**  `while.body.i.lr.ph`
binds `%k11.i`, `%h1.i.i.i51`, `%gap.i`, `%end.i` and `%kind404.i`, each to the
address `walkStaticRegs` names for it, so the static carrier survives the block.
The list is the run's own environment, newest first: the block writes the five in
source order, so `%kind404.i` is the outermost cell and `%k11.i` the oldest — the
order `cells` reads its argument in. -/
theorem preheaderRegs {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (env : Env)
    (h : WalkRegs G C env) :
    WalkRegs G C (cells
      [("%kind404.i", .ptr (C.stage.tok + 16)), ("%end.i", .ptr (C.stage.tok + 8)),
       ("%gap.i", .ptr (C.stage.tok + 20)), ("%h1.i.i.i51", .ptr (C.stage.z + 24)),
       ("%k11.i", .ptr (C.stage.c + 32))] env) := by
  intro p hp
  rw [walkStaticRegs] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals try (rw [lookupName_cells_of_notin _ _ _ (by decide)])
  all_goals first
    | exact h _ (by simp [walkStaticRegs])
    | simp [cells, lookupName]

/-! ### The map and its agreement with the stack's bytes -/

/-- **The container stack's carried contents**: the stack at `base` holds `M`'s
first `n` values, one byte each.  `n` is the carried depth, so the byte a block
reads at `sp - 1` is `M (sp - 1)` — a value the carry keeps after the depth that
produced it has moved. -/
def WalkStackBytes (mem : Mem) (base : Nat) (M : Nat → UInt8) (n : Nat) : Prop :=
  ∀ i, i < n → readByte mem (base + i) = some (M i)

/-- **The empty mark carries any map**: no index is below zero.  This is the
seed's stack clause and the clause a depth reduced to zero restates. -/
theorem WalkStackBytes.empty {mem : Mem} {base : Nat} {M : Nat → UInt8} :
    WalkStackBytes mem base M 0 :=
  fun i hi => absurd hi (Nat.not_lt_zero i)

/-- The byte at an index the depth admits. -/
theorem WalkStackBytes.at {mem : Mem} {base n : Nat} {M : Nat → UInt8}
    (h : WalkStackBytes mem base M n) {i : Nat} (hi : i < n) :
    readByte mem (base + i) = some (M i) :=
  h i hi

/-- **The top of the stack at a positive depth.**  This is the byte every
container-state check and every push at the top reads. -/
theorem WalkStackBytes.top {mem : Mem} {base n : Nat} {M : Nat → UInt8}
    (h : WalkStackBytes mem base M n) (hn : 0 < n) :
    readByte mem (base + (n - 1)) = some (M (n - 1)) :=
  h (n - 1) (by omega)

/-- **A restriction of the depth keeps the map.**  A pop lowers `n` and the merge
at `cleanup478.i` moves it without writing either stack, so both are this step. -/
theorem WalkStackBytes.restrict {mem : Mem} {base n n' : Nat} {M : Nat → UInt8}
    (h : WalkStackBytes mem base M n) (hn : n' ≤ n) : WalkStackBytes mem base M n' :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hn)

/-- **A write outside the stack's extent leaves it.** -/
theorem WalkStackBytes.write_outside {mem : Mem} {base n a : Nat} {M : Nat → UInt8}
    {bs : List UInt8} (h : WalkStackBytes mem base M n)
    (hout : a + bs.length ≤ base ∨ base + n ≤ a) :
    WalkStackBytes (writeBytes mem a bs) base M n := by
  intro i hi
  rw [readByte_writeBytes_outside mem bs (by omega)]
  exact h i hi

/-- **A push**: one byte written at the depth extends the map by it.  This is the
store `if.end24.i` makes at `ctype + sp` (and its state-stack twin at
`cst + sp`), with the pushed byte as the store's own list. -/
theorem WalkStackBytes.push {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : UInt8}
    (h : WalkStackBytes mem base M n) :
    WalkStackBytes (writeBytes mem (base + n) [v]) base
      (fun i => if i = n then v else M i) (n + 1) := by
  intro i hi
  by_cases hin : i = n
  · rw [hin]
    simpa using readByte_writeBytes_at mem [v] (base + n) 0 (by simp)
  · rw [readByte_writeBytes_outside mem [v] (by omega)]
    simp only [if_neg hin]
    exact h i (by omega)

/-- **A byte written at an index below the depth rewrites the map there.**  The
container-state stores of class D are this shape: one `i8` literal at the state
stack's byte the block indexed. -/
theorem WalkStackBytes.store {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : UInt8}
    (h : WalkStackBytes mem base M n) {k : Nat} (hk : k < n) :
    WalkStackBytes (writeBytes mem (base + k) [v]) base
      (fun i => if i = k then v else M i) n := by
  intro i hi
  by_cases hik : i = k
  · rw [hik]
    simpa using readByte_writeBytes_at mem [v] (base + k) 0 (by simp)
  · have hout : base + i < base + k ∨ base + k + [v].length ≤ base + i := by
      rcases Nat.lt_or_ge i k with hlt | hge
      · left; omega
      · right; simp only [List.length_cons, List.length_nil]; omega
    rw [readByte_writeBytes_outside mem [v] hout]
    simp only [if_neg hik]
    exact h i hi

/-- **A push of a `natToBytes` byte**, the store shape the body's blocks actually
emit: the pushed value is the one-byte list `natToBytes v 1`, and the map keeps
its own byte. -/
theorem WalkStackBytes.pushNat {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : Nat}
    (h : WalkStackBytes mem base M n) :
    WalkStackBytes (writeBytes mem (base + n) (natToBytes v 1)) base
      (fun i => if i = n then (natToBytes v 1).getD 0 0 else M i) (n + 1) := by
  intro i hi
  by_cases hin : i = n
  · rw [hin]
    simpa using readByte_writeBytes_at mem (natToBytes v 1) (base + n) 0
      (by simp [natToBytes_length])
  · rw [readByte_writeBytes_outside mem (natToBytes v 1) (by
      left; simp [natToBytes_length]; omega)]
    simp only [if_neg hin]
    exact h i (by omega)

/-- **A one-byte literal store at an index below the depth**, the class-D shape:
`store i8 <imm>, %arrayidx`. -/
theorem WalkStackBytes.storeNat {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : Nat}
    (h : WalkStackBytes mem base M n) {k : Nat} (hk : k < n) :
    WalkStackBytes (writeBytes mem (base + k) (natToBytes v 1)) base
      (fun i => if i = k then (natToBytes v 1).getD 0 0 else M i) n := by
  intro i hi
  by_cases hik : i = k
  · rw [hik]
    simpa using readByte_writeBytes_at mem (natToBytes v 1) (base + k) 0
      (by simp [natToBytes_length])
  · have hout : base + i < base + k ∨
        base + k + (natToBytes v 1).length ≤ base + i := by
      rcases Nat.lt_or_ge i k with hlt | hge
      · left; omega
      · right; simp [natToBytes_length]; omega
    rw [readByte_writeBytes_outside mem (natToBytes v 1) hout]
    simp only [if_neg hik]
    exact h i hi

/-- **A push at an index at or below the written depth.**  A push writes at the
register's depth, which may be below the mark after a pop; the map updates at the
pushed index and the mark becomes `max n (i + 1)`.  This is the shape
`if.end24.i` has, whose store is at `%sp`, not at the mark. -/
theorem WalkStackBytes.pushAt {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : UInt8}
    {i : Nat} (h : WalkStackBytes mem base M n) (hi : i ≤ n) :
    WalkStackBytes (writeBytes mem (base + i) [v]) base
      (fun j => if j = i then v else M j) (max n (i + 1)) := by
  intro j hj
  by_cases hji : j = i
  · rw [hji]
    simpa using readByte_writeBytes_at mem [v] (base + i) 0 (by simp)
  · have hjn : j < n := by
      by_contra hge
      have hge' : n ≤ j := Nat.le_of_not_lt hge
      have : i + 1 ≤ j := by omega
      have : max n (i + 1) ≤ j := max_le hge' this
      omega
    have hout : base + j < base + i ∨ base + i + [v].length ≤ base + j := by
      rcases Nat.lt_or_ge j i with hlt | hge
      · left; omega
      · right; simp only [List.length_cons, List.length_nil]; omega
    rw [readByte_writeBytes_outside mem [v] hout]
    simp only [if_neg hji]
    exact h j hjn

/-- **A `natToBytes` push at an index at or below the written depth**, the store
shape the body's blocks emit. -/
theorem WalkStackBytes.pushNatAt {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : Nat}
    {i : Nat} (h : WalkStackBytes mem base M n) (hi : i ≤ n) :
    WalkStackBytes (writeBytes mem (base + i) (natToBytes v 1)) base
      (fun j => if j = i then (natToBytes v 1).getD 0 0 else M j) (max n (i + 1)) := by
  intro j hj
  by_cases hji : j = i
  · rw [hji]
    simpa using readByte_writeBytes_at mem (natToBytes v 1) (base + i) 0
      (by simp [natToBytes_length])
  · have hjn : j < n := by
      by_contra hge
      have hge' : n ≤ j := Nat.le_of_not_lt hge
      have : i + 1 ≤ j := by omega
      have : max n (i + 1) ≤ j := max_le hge' this
      omega
    have hout : base + j < base + i ∨ base + i + (natToBytes v 1).length ≤ base + j := by
      rcases Nat.lt_or_ge j i with hlt | hge
      · left; omega
      · right; simp [natToBytes_length]; omega
    rw [readByte_writeBytes_outside mem (natToBytes v 1) hout]
    simp only [if_neg hji]
    exact h j hjn

/-- **A one-byte store at any index.**  A class-D store writes the state stack at
the index a previous block computed; that index may be inside the written depth
(the map updates there) or at or above it (the write misses the map's extent, and
the map is unchanged there because it only constrains indices below `n`). -/
theorem WalkStackBytes.storeAt {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : UInt8}
    {k : Nat} (h : WalkStackBytes mem base M n) :
    WalkStackBytes (writeBytes mem (base + k) [v]) base
      (fun i => if i = k then v else M i) n := by
  intro i hi
  by_cases hik : i = k
  · rw [hik]
    simpa using readByte_writeBytes_at mem [v] (base + k) 0 (by simp)
  · have hout : base + i < base + k ∨ base + k + [v].length ≤ base + i := by
      rcases Nat.lt_or_ge i k with hlt | hge
      · left; omega
      · right; simp only [List.length_cons, List.length_nil]; omega
    rw [readByte_writeBytes_outside mem [v] hout]
    simp only [if_neg hik]
    exact h i hi

/-- **A one-byte literal store at any index**, the class-D `natToBytes` shape. -/
theorem WalkStackBytes.storeNatAt {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : Nat}
    {k : Nat} (h : WalkStackBytes mem base M n) :
    WalkStackBytes (writeBytes mem (base + k) (natToBytes v 1)) base
      (fun i => if i = k then (natToBytes v 1).getD 0 0 else M i) n := by
  intro i hi
  by_cases hik : i = k
  · rw [hik]
    simpa using readByte_writeBytes_at mem (natToBytes v 1) (base + k) 0
      (by simp [natToBytes_length])
  · have hout : base + i < base + k ∨
        base + k + (natToBytes v 1).length ≤ base + i := by
      rcases Nat.lt_or_ge i k with hlt | hge
      · left; omega
      · right; simp [natToBytes_length]; omega
    rw [readByte_writeBytes_outside mem (natToBytes v 1) hout]
    simp only [if_neg hik]
    exact h i hi

end LeanLLVM.Refinement
