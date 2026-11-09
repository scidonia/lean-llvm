/-
The staged invariant and the exit word the assembled expander's arms consume.

`DecodeLatch` (`JsonEscapeDecodeRun.lean`) binds the state's `%p`, `%xp`, `%tab`,
`%pos0` and `%n` to existentials and pins only `%dst` and `%nxp.toNat = nps`; it
carries no staging.  The first block after the latch — `while.body6`, whose
`%arrayidx7` load reads four bytes at `%xp + 4 * c` — therefore cannot be
evaluated from `LatchInv` alone: a state can satisfy it while `%xp` points at
memory that holds no position stream.  `StagedLatchInv`
(`JsonEscapeCopyLoops.lean`) adds the staging the two copies and the seed already
consume; `AssemblyLatchInv` adds the five register cells the staging and the
record's `pre` are about.

The two arm statements and the exit word below are the consumer-side forms of
this milestone's arms.  They live here, below `JsonEscapeExpandRun`, because the
decode module's own arm definition is body-generic: it cannot be stated at
`AssemblyLatchInv` (the name is not in scope there), and `%err`/`%xj` are the
record's destinations, not the decode module's to know.

**The exit word, and what this module adds to it.**  The decoded exit stores
`%k.1.lcssa = %add28` at `%xj` in `us_run.exit112` (`JsonEscapeIR.lean:602`),
after the final copy, while the post's cursor clause names the walk's own `nps`;
`DecodeLatchExit` now records the equality (`c = nps`, derived at the arm from the
latch's `c ≤ nps` and the false exit test), so `AssemblyLatchExit` is its
projection.  The refusal's two stores happen in `if.then20`/`if.then22`
(`:384-385`, `:539-540`), before the exit state at `cleanup41`, and
`DecodeRefusalExit` records them with the destinations bound existentially;
`AssemblyRefusalExit` adds the two equalities tying those destinations to the
record's — the residue this module owes, because the record's `err` and `xj` are
its own.  The `cleanup41` *return* half needs none of the store facts
(`refusalReturn`).
-/
import LeanLLVM.Vellum.JsonEscapeCompose

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonScanSpec

/-! ### The staged invariant the arms consume -/

/-- The byte cursor the latch's own step will form, read off the state alone.

`cleanup32` forms `%add24 = %adv.2 + %sub`, where `%sub` is the residual the
previous iteration left and `%adv.2` is the `phi` selecting the escape's advance
(`%adv.1.i` on the emitter edge, the constant two on the simple-escape edge).  The
block therefore *determines* the value from cells it reads, but `DecodeLatch`'s
existentials do not expose it: the walk is stated at an index the invariant
mentions only inside `DecodeInv`, and `DecodeInv` is not injective in that index
(an empty remainder makes every cursor decode the same outcome).  The cursor is
therefore a function of the state, and the boundedness clause below can name it
without a second copy of the cell pins. -/
def latchCursor (s : State) : Option Nat :=
  match s.pre with
  | some "if.end32.i" =>
      match lookupName s.env "%sub", lookupName s.env "%adv.1.i" with
      | some (.int 64 sub), some (.int 64 adv) => some (adv + sub).toNat
      | _, _ => none
  | some "if.then6.i" =>
      match lookupName s.env "%sub" with
      | some (.int 64 sub) => some (BitVec.ofInt 64 2 + sub).toNat
      | _ => none
  | _ => none

/-- The latch with the caller's staging, the five register cells that staging and
the record's `pre` are about, the cursor's bound, and the **frame**.

A cell holds one value, so the pinnings are not a second claim beside
`DecodeLatch`'s: they force its existentials equal (`assemblyLatchInv_paddr_eq`).

The frame is the one fact the walk's state cannot supply about itself.  The
record's `post` compares the caller's *initial* memory with the memory the run
leaves (`UnchangedOutside mem m regions`), and no exit word is a relation between
two memories; a word written from the exit state alone can therefore satisfy every
clause while saying nothing about what the run changed.  The invariant is where the
arms establish it, block by block, so a block whose writes leave the destination
extent has to say so rather than pass the obligation to whoever reads the exit.

**The region list is the extent the walk has written, not the record's.**  At the
latch the run has produced the decoded prefix in the destination and nothing else:
the offset slot, the cursor slot and the position list are written only by the exit
blocks.  Naming them as regions anyway would say nothing about the offset slot,
which is what let `entryExit_admits_clobbered_err` satisfy the word at a state whose
slot the run never touches, and it would leave a body byte inside a named region
unconstrained at the exit.  The narrower list implies the record's wider one, so
the continuation weakens it; the record's own frame is not changed.

**The cursor's bound is a consequence the block does not carry.**  `while.end35`
forms `%sub38 = %n - %i.0.lcssa` in 64-bit arithmetic, so a cursor past the body
wraps the subtraction and the copy's residual is `2 ^ 64 - (i - n)`; the walk itself
does not exclude that (`latchExit_admits_cursor_past_body`).  The run's cursor stays
inside the body because each step advances by an escape's own width, so the bound is
true of the run and is carried here at the latch's own binder.

**The cursor stands behind the head position, and the clause is a relation rather
than a bound.**  `DecodeInv.prefix_le_cursor` bounds the decoded prefix by the
cursor; nothing bounds the cursor by the position it is about to decode, and the
walk does not exclude a cursor past it (`escapeDecodeGo` copies `take (q - i)`,
which is empty for `q < i`).  The blocks do exclude it, by wrapping: `if.end` forms
`%sub13 = %sub - %i.0295` with `%sub` the head position and `%i.0295` the cursor, so
at a cursor past the head the copy's residual is `2 ^ 64 - 1` and no bound inside
`decodeIterCost` can exhaust the copy's visits.  The state that exhibits the wrap
is `wrapState` (`JsonEscapeExpandAssembly`), and this clause is what puts it outside
the invariant: `Spaced`'s head premise is `i ≤ q`, so `assemblyLatchInv_cursor_le_head`
recovers the relation at the head, the copy's residual `q - i` is a subtraction of
naturals, and the successor's spacing is `Spaced.step` at the escape the emitter
consumed. -/
def AssemblyLatchInv (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (err xj : Nat) (mem : Mem) (r c : Nat) (s : State) : Prop :=
  StagedLatchInv body st dst nps goal xp pos0 n ps r c s ∧
  lookupName s.env "%p" = some (.ptr b) ∧
  lookupName s.env "%xp" = some (.ptr xp) ∧
  lookupName s.env "%tab" = some (.ptr tab) ∧
  lookupName s.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName s.env "%err" = some (.ptr err) ∧
  lookupName s.env "%xj" = some (.ptr xj) ∧
  (∀ i : Nat, latchCursor s = some i → i ≤ n) ∧
  (∀ i : Nat, latchCursor s = some i → Spaced body i ((escAt body st 0).drop c)) ∧
  UnchangedOutside mem s.mem [(dst, n + 64)]

/-- The staged latch under the pinnings. -/
theorem assemblyLatchInv_staged {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    {mem : Mem} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj
      mem r c s) :
    StagedLatchInv body st dst nps goal xp pos0 n ps r c s := h.1

/-- The latch's own invariant. -/
theorem assemblyLatchInv_latch {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    {mem : Mem} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj
      mem r c s) :
    LatchInv body st dst nps goal r s c :=
  stagedLatchInv_latch h.1

/-- The caller's staging, with the `%add` cell beside it. -/
theorem assemblyLatchInv_staging {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    {mem : Mem} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj
      mem r c s) :
    ∃ addv : BitVec 64,
      DecodeStaging s.mem nps xp pos0 n ps addv ∧
      lookupName s.env "%add" = some (.int 64 addv) :=
  stagedLatchInv_staging h.1

/-- The latch's budget pair. -/
theorem assemblyLatchInv_budget {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    {mem : Mem} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj
      mem r c s) :
    c ≤ nps ∧ nps ≤ c + r :=
  stagedLatchInv_budget h.1

/-- The five parameter cells. -/
theorem assemblyLatchInv_params {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    {mem : Mem} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj
      mem r c s) :
    lookupName s.env "%p" = some (.ptr b) ∧
      lookupName s.env "%xp" = some (.ptr xp) ∧
      lookupName s.env "%tab" = some (.ptr tab) ∧
      lookupName s.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
      lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- The two destination slots.  The exit words' store clauses are about the
caller's slots, so the invariant names them rather than leaving `DecodeLatch`'s
existentials free. -/
theorem assemblyLatchInv_dest {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    {mem : Mem} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj
      mem r c s) :
    lookupName s.env "%err" = some (.ptr err) ∧
      lookupName s.env "%xj" = some (.ptr xj) :=
  ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

/-- **The frame**: everything outside the destination extent reads as it did in the
caller's memory.  This is the fact the exit word cannot derive from the exit state,
and the reason it rides in the invariant: the arms establish it as they proceed. -/
theorem assemblyLatchInv_frame {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    {mem : Mem} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj
      mem r c s) :
    UnchangedOutside mem s.mem [(dst, n + 64)] :=
  h.2.2.2.2.2.2.2.2.2.2

/-- **The cursor's bound**, at the latch: the byte cursor the next step forms is
inside the body, so `while.end35`'s subtraction does not wrap. -/
theorem assemblyLatchInv_cursor {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    {mem : Mem} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj
      mem r c s) :
    ∀ i : Nat, latchCursor s = some i → i ≤ n :=
  h.2.2.2.2.2.2.2.2.1

/-- **The cursor stands behind the position it is about to decode.**  The walk's
remaining positions are spaced from that cursor: the same `Spaced` the decoded
length rests on, stated at the latch's own cursor.

It is a relation between two quantities the invariant already carries and not a
bound on either.  `DecodeInv.prefix_le_cursor` bounds the decoded prefix by the
cursor and says nothing about the cursor's relation to the *head* position, so a
cursor past the head satisfies every other clause; `if.end` then forms
`%sub13 = %sub - %i.0295` with `%sub` the head and `%i.0295` the cursor, a 64-bit
subtraction that wraps to `2 ^ 64 - 1` and gives the copy a residual no bound
inside `decodeIterCost` can exhaust.  The state exhibiting the wrap is `wrapState`
in `JsonEscapeExpandAssembly`, and it is outside this invariant by this clause. -/
theorem assemblyLatchInv_spaced {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    {mem : Mem} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj
      mem r c s) :
    ∀ i : Nat, latchCursor s = some i → Spaced body i ((escAt body st 0).drop c) :=
  h.2.2.2.2.2.2.2.2.2.1

/-- **A spaced list puts the cursor behind its head.**  The constructors' only
cursor-sensitive premise is `i ≤ q`, so from a non-empty spaced list the head
position is at or past the cursor.  This is the form the iteration arm reads: the
copy's residual `q - i` is a subtraction of naturals only because this holds. -/
theorem Spaced.head_le {bs : List UInt8} {i q : Nat} {qs : List Nat}
    (h : Spaced bs i (q :: qs)) : i ≤ q := by
  cases h with
  | control _ _ _ _ hiq _ _ => exact hiq
  | refuse _ _ _ hiq _ _ => exact hiq
  | step _ _ _ _ _ _ hiq _ _ _ _ _ => exact hiq

/-- **The arm's form of the spacing**: a latch state's cursor is at or behind the
head position its index names. -/
theorem assemblyLatchInv_cursor_le_head {body : List UInt8} {st : ClassState}
    {dst nps : Nat} {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat}
    {err xj : Nat} {mem : Mem} {r c : Nat} {s : State}
    (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem r c s)
    {i q : Nat} (hi : latchCursor s = some i)
    (hq : (escAt body st 0)[c]? = some q) : i ≤ q := by
  have hsp := assemblyLatchInv_spaced h i hi
  have hc : c < (escAt body st 0).length := by
    rw [List.getElem?_eq_some_iff] at hq
    exact hq.1
  have hq' : (escAt body st 0)[c]'hc = q := by
    have h1 : (escAt body st 0)[c]? = some ((escAt body st 0)[c]'hc) :=
      List.getElem?_eq_getElem hc
    rw [h1] at hq
    exact Option.some.inj hq
  rw [List.drop_eq_getElem_cons hc, hq'] at hsp
  exact Spaced.head_le hsp

/-- **The spacing the next latch inherits.**  At a position the emitter decodes,
the walk's list continues at `q + adv`, with one entry dropped after a surrogate
pair: `Spaced` says so in its `step` constructor, and the three refusals' premises
are contradicted by the emitter's own facts (the byte is not a control byte and
`escapeAt` names an escape).  This is what carries the latch's spacing clause to
the successor: the cursor moves to `q + adv` and the remaining list is exactly the
one the successor decodes. -/
theorem Spaced.step_tail {bs : List UInt8} {i q : Nat} {qs : List Nat} {adv : Nat}
    {bytes : List UInt8} {b : UInt8}
    (h : Spaced bs i (q :: qs)) (hb : bs[q]? = some b) (hctl : IsControlB b = false)
    (hesc : escapeAt bs q = some (bytes, adv)) :
    Spaced bs (q + adv) (if adv = 12 then qs.drop 1 else qs) := by
  cases h with
  | control _ _ _ b' _ hb' hctl' =>
      rw [hb'] at hb
      cases Option.some.inj hb
      rw [hctl'] at hctl
      exact absurd hctl (by simp)
  | refuse _ _ _ _ hlt hnone =>
      rw [hnone] at hesc
      exact absurd hesc (by simp)
  | step _ _ _ adv' bytes' b' _ hb' hctl' hesc' hlen hadv ih =>
      rw [hb'] at hb
      cases Option.some.inj hb
      rw [hesc'] at hesc
      cases Option.some.inj hesc
      exact ih

/-- **The successor latch's spacing, from this latch's.**  The emitter consumes the
head position with its own advance; the successor's index is `c + 1` for a
two-character or six-byte escape and `c + 2` for a surrogate pair, and its cursor is
`q + adv`.  The remaining list is the one `Spaced.step_tail` names, at that index. -/
theorem assemblyLatchInv_spaced_succ {body : List UInt8} {st : ClassState}
    {dst nps : Nat} {goal : EscapeOutcome} {b xp tab : Nat} {pos0 n : Nat}
    {ps : List Nat} {err xj : Nat} {mem : Mem} {r c : Nat} {s : State}
    (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem r c s)
    {i q adv : Nat} {bytes : List UInt8} {b' : UInt8}
    (hi : latchCursor s = some i) (hq : (escAt body st 0)[c]? = some q)
    (hb : body[q]? = some b') (hctl : IsControlB b' = false)
    (hesc : escapeAt body q = some (bytes, adv)) :
    Spaced body (q + adv)
      ((escAt body st 0).drop (c + 1 + (if adv = 12 then 1 else 0))) := by
  have hsp := assemblyLatchInv_spaced h i hi
  have hc : c < (escAt body st 0).length := by
    rw [List.getElem?_eq_some_iff] at hq
    exact hq.1
  have hq' : (escAt body st 0)[c]'hc = q := by
    have h1 : (escAt body st 0)[c]? = some ((escAt body st 0)[c]'hc) :=
      List.getElem?_eq_getElem hc
    rw [h1] at hq
    exact Option.some.inj hq
  rw [List.drop_eq_getElem_cons hc, hq'] at hsp
  have hnext := Spaced.step_tail hsp hb hctl hesc
  by_cases h12 : adv = 12
  · simp only [h12, ite_true] at hnext ⊢
    rw [List.drop_drop] at hnext
    exact hnext
  · simp only [h12, ite_false] at hnext ⊢
    exact hnext

/-- The pinning forces `DecodeLatch`'s `%p` existential: the two values are equal,
so the extension refines the decode invariant rather than competing with it. -/
theorem assemblyLatchInv_paddr_eq {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    {mem : Mem} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj
      mem r c s)
    {paddr : Nat} (hp : lookupName s.env "%p" = some (.ptr paddr)) : paddr = b := by
  have hb : lookupName s.env "%p" = some (.ptr b) := h.2.1
  rw [hp] at hb
  exact Value.ptr.inj (Option.some.inj hb)

/-! ### The exit word the consumer needs

The previous word described **a state**: it named the block, the walk's cells and,
for the refusal, the two stores, and nothing about *the run that produced the
state or the caller who asked for it*.  That is why it admitted states the body
never reaches, and why the record's `post` — which matches the **initial**
staging's walk and the caller's **initial** memory — could not hold at them.  The
words below are relational instead: each branch is stated at the caller's staging
(`args mem body ps pos0 n b xp tab err xj`), pinned to the target block's
predecessor, and tied to the walk the post matches.  `Γ_escape_expand_at` is that
staging: the record's `pre` **by name**, the equations that align its witnesses
with these binders, and the clauses whose `Nat`-level form the record's witnesses
cannot transport; `ExpandStaging` is its synonym at the same binders.

**The branches follow the pinned `phi` tables**, not a guess at the reachable set:
`cleanup41`'s incoming list names `us_run.exit112`, `if.then20` and `if.then22`
(`JsonEscapeIR.lean:608`), and `while.end35`'s names `while.end`, `while.body6`,
`cleanup32` and `while.body` (`:555-559`).  All seven are present.  The two that an
admissible staging cannot reach — `while.body6`, which the loop enters only on
`ps[c] ≥ pos0 + n`, and `while.body`, which the pre-scan enters only on
`ps[k] < pos0` — carry that witness in the branch, so the exclusion is the
staging's range clause (`DecodeStaging`'s third conjunct) contradicting it, stated
as a theorem, rather than an omission from the disjunction.

**`us_run.exit112` is not a refusal edge.**  It stores the cursor and computes
`%add40 = %sub38 + %j.0.lcssa`, which `cleanup41`'s `phi` returns: that is where a
successful call's length is concluded, so `AssemblySuccessExit` carries the post's
decoded branch and a refusal-only predecessor set would leave the success path with
no word at all.

**The frame is not derivable here.**  `UnchangedOutside mem e.mem regions` relates
the caller's initial memory to the exit state's; it is carried by `ExpandStaging`
through `AssemblyLatchInv` and restated at each branch, because no branch can
obtain it from the state alone. -/

/-- **The caller's staging at the expander's own binders** — the record's `pre`,
the equations that align its witnesses with these binders, and the clauses whose
`Nat`-level form does not transport out of it.

The conjunction has three groups, and the grouping is the statement's content
rather than a layout choice:

* **The record's `pre`, by name.**  `(Γ_escape_expand escapeExpandBudget).pre args
  mem next` is the caller's staging exactly as `JsonEscapeSteps.lean` states it;
  `JsonEscapeSteps.lean` remains its only wording, and this predicate adds no
  second spelling of it.
* **The alignment equations.**  `args = …` at these binders and `st =
  ⟨true, false⟩`.  These are new content: the `pre` binds its own witnesses, so
  nothing in it names `b`, `n`, `dst`, `err`, `xp`, `xj`, `nps`, `pos0`, `tab` or
  `st`.  The argument equation is what identifies the binders with the call's
  slots — without it a branch could speak about a different destination, cursor or
  offset slot than the caller's — and `st = ⟨true, false⟩` is what carries the
  `pre`'s rebased list from the record's rig to this word's classifier state.
* **The clauses whose `Nat`-level form does not transport out of the `pre`.**
  `BitVec.ofNat 64` is **not injective**.  The two argument equations make the
  pointer slots equal — `Value.ptr` is injective, so `b`, `dst`, `err`, `xp`, `xj`
  and `tab` cross as equalities — but they make the numeric slots equal only
  modulo `2 ^ 64`, so the `pre`'s `n`, `nps` and `pos0` witnesses say nothing about
  the values of these binders.  Every clause the exit proof reads at `n`, `nps`,
  `pos0` or the cursor `k0` is therefore stated here, at these binders: the body
  read `readBytes mem b n = some body`; the width bound `pos0 + n ≤ 2 ^ 32` that
  makes the body's 64-bit `%add = pos0 + n` unwrap and every position fit the
  `uint32` the body loads; `DecodeStaging`, the list read at `4 * nps` with its
  length, its range at `pos0`/`n` and its end offset; the rebased list
  `ps.map (fun q => q - pos0) = escapePositionsFrom body st`; `DecodeNoAlias` and
  the two spacing disjunctions, whose destination extent is `n + 64`; and the
  cursor slot's read `readBytes mem xj 8 = some (wordBytes 8 k0)` with its bound
  `k0 ≤ nps` and the walk tie — the `pre` does not name `goal` at all, so the
  identification of the caller's outcome with the staging's walk can only be
  stated here.

One `pre` clause is deliberately **absent**, and the absence is part of the
statement: the offset slot's read `readBytes mem err 8 = some (wordBytes 8 err0)`
transports, because `err` occupies a `Value.ptr` slot and the `pre`'s read is the
same read at these binders; its witness `err0` is not nameable here, so the exit
branches state the offset slot's preservation as the memory equation `readBytes
e.mem err 8 = readBytes mem err 8` rather than by identifying `err0` across the
coercion.  The `pre`'s remaining clauses are not restated either: no consumer reads
them at these binders, and copying them here at `Nat` slots is the duplication this
split removes.

The decision the split records: **a clause restated is duplication; an alignment
equation is new content; a clause whose `Nat`-level form does not transport is
neither, and must be said again.**  That is why the `Γ_entry_pos8at` precedent is
followed by naming rather than by re-definition.  That adapter existed because a
capture changed a unit's ABI, and its rule was to consume through an adapter rather
than edit the ABI; here the record is unchanged and the mismatch is a lossy
coercion at the slot, so re-indexing the record's clauses wholesale would copy them
at `Nat` slots.  The precedent's spirit applies (consume through an adapter); its
letter does not (rewrite the record). -/
def Γ_escape_expand_at (args : List Value) (mem : Mem) (next : Nat) (body : List UInt8)
    (st : ClassState) (dst nps : Nat) (goal : EscapeOutcome) (b xp tab : Nat)
    (pos0 n : Nat) (ps : List Nat) (err xj : Nat) : Prop :=
  -- 1. the record's `pre`, by name
  (Γ_escape_expand escapeExpandBudget).pre args mem next ∧
  -- 2. the alignment equations (new content)
  args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr dst, .ptr err, .ptr xp,
    .ptr xj, .int 64 (BitVec.ofNat 64 nps), .int 64 (BitVec.ofNat 64 pos0),
    .ptr tab] ∧
  st = ⟨true, false⟩ ∧
  -- 3. the clauses whose `Nat`-level form the `pre` cannot transport
  readBytes mem b n = some body ∧
  pos0 + n ≤ 2 ^ 32 ∧
  (∃ addv : BitVec 64, DecodeStaging mem nps xp pos0 n ps addv) ∧
  ps.map (fun q => q - pos0) = escapePositionsFrom body st ∧
  DecodeNoAlias n dst err xj tab ∧
  (b + n + 32 ≤ dst ∨ dst + n + 64 ≤ b) ∧
  (xp + 4 * nps ≤ dst ∨ dst + n + 64 ≤ xp) ∧
  (∃ k0 : Nat, readBytes mem xj 8 = some (wordBytes 8 k0) ∧ k0 ≤ nps ∧
    goal = escapeDecodeGo body 0 k0 ((ps.map (fun q => q - pos0)).drop k0) [])

/-- The caller's staging at the exit word's witnesses: a synonym for
`Γ_escape_expand_at`, not a second definition.  `abbrev` is the synonym form the
language offers — it is definitionally the adapter above, so there is one adapter
with one home, and a reader who unfolds either name reaches the same three groups.
Every exit branch and arm is stated at this name; see `Γ_escape_expand_at` for what
each group is and why. -/
abbrev ExpandStaging (args : List Value) (mem : Mem) (next : Nat) (body : List UInt8)
    (st : ClassState) (dst nps : Nat) (goal : EscapeOutcome) (b xp tab : Nat)
    (pos0 n : Nat) (ps : List Nat) (err xj : Nat) : Prop :=
  Γ_escape_expand_at args mem next body st dst nps goal b xp tab pos0 n ps err xj

/-- The decoded exit, on `cleanup32`'s edge: the walk at the bound, the exit
block's cells, the byte cursor's bound, and the frame.

`%add24` is the cell `while.end35`'s `phi` copies into `%i.0.lcssa`, and the block
forms `%sub38 = %n - %i.0.lcssa` from it in 64-bit arithmetic.  The bound is stated
at that cell because it is what keeps the subtraction the block's `Nat` reading;
without it the word admits a cursor past the body, whose residual wraps
(`latchExit_admits_cursor_past_body`).

The frame names only the destination extent, because at this edge the run has
written nothing else.  That is what makes the offset slot's preservation, and the
body's own bytes at this memory, consequences of the branch rather than facts
nothing states. -/
def AssemblyLatchExit (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (err xj : Nat) (mem : Mem) (e : State) : Prop :=
  e.pc = "while.end35" ∧ e.pre = some "cleanup32" ∧
  (∃ c : Nat, DecodeLatchExit body st dst nps goal c e) ∧
  (∃ add24 : BitVec 64, lookupName e.env "%add24" = some (.int 64 add24) ∧
    add24.toNat ≤ n) ∧
  lookupName e.env "%p" = some (.ptr b) ∧
  lookupName e.env "%xp" = some (.ptr xp) ∧
  lookupName e.env "%tab" = some (.ptr tab) ∧
  lookupName e.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%err" = some (.ptr err) ∧
  lookupName e.env "%xj" = some (.ptr xj) ∧
  UnchangedOutside mem e.mem [(dst, n + 64)]

/-- The entry's exit, on `while.end`'s edge: the walk has nothing left to decode,
so `while.end`'s cursor is the list's length and `while.end35`'s two copy bases
will be its zero constants.  The cells named here are the predecessor's, because
the state is the exit block's *entry*: `%j.0.lcssa` and `%i.0.lcssa` do not exist
until the block steps.

The walk is pinned at the seed's shape — cursor `0`, index `nps`, nothing written
— rather than left as a `DecodeInv` at an arbitrary cursor and prefix.  The block
ignores the invariant's `i` and `out`: `while.end35`'s two entry `phi`s supply
`0` for both `%i.0.lcssa` and `%j.0.lcssa`, so the final copy always starts at the
body's first byte and the destination's base, whatever the invariant records.  An
exit word that quantifies over `i` and `out` therefore admits states the run never
produces and that its own continuation cannot reach the post from: with
`body = [0x61, 0x5C, 0x6E]`, `st = ⟨true, false⟩`, `n = 3`, `ps = [1]`,
`pos0 = 0` and `k0 = 0` the staging's goal is `.decoded [0x61, 0x0A] 1`; the
generic word is satisfiable at `i = 3` and `out = [0x61, 0x0A]`, where the block
copies `sub = n - 0 = 3` bytes from the body's first byte and returns
`%add40 = 3`, while the goal's output length is `2`.  The seed's own shape is what
`emptySeedRun` constructs, and it is what the continuation reads.

`%dst` is pinned for the same reason and by the same evidence.  `while.end35`
forms the final copy's destination as `%add.ptr37 = %dst + %j.0.lcssa`, so the
block reads the cell and the register is part of the edge; the walk's `stored`
clause and the frame name the *number* `dst`, not the register, and nothing else
in the branch ties one to the other.  A state whose every other cell is right and
whose `%dst` is `dst + 32` therefore satisfies the branch, while the run copies
the body at `dst + 32` and the post reads the caller's bytes at `dst`: the write
is inside the destination extent, so the frame holds and the post is false.  The
sibling branch needs no such clause because `DecodeLatchExit` pins `%dst` itself. -/
def AssemblyEntryExit (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (err xj : Nat) (mem : Mem) (e : State) : Prop :=
  e.pc = "while.end35" ∧ e.pre = some "while.end" ∧
  DecodeInv body st e.mem dst nps 0 nps [] goal ∧
  lookupName e.env "%k.0.lcssa" = some (.int 64 (BitVec.ofNat 64 nps)) ∧
  lookupName e.env "%p" = some (.ptr b) ∧
  lookupName e.env "%dst" = some (.ptr dst) ∧
  lookupName e.env "%xp" = some (.ptr xp) ∧
  lookupName e.env "%tab" = some (.ptr tab) ∧
  lookupName e.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%err" = some (.ptr err) ∧
  lookupName e.env "%xj" = some (.ptr xj) ∧
  UnchangedOutside mem e.mem [(dst, n + 64)]

/-- **`while.body6`'s edge**, admitted with the witness that makes it live: the
position the loop loaded lies at or past the window's end.  Under an admissible
staging the range clause contracts that witness, which is the exclusion theorem's
content; the branch is here so that no edge is omitted by construction. -/
def AssemblyWhileBody6Exit (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (err xj : Nat) (mem : Mem) (e : State) : Prop :=
  e.pc = "while.end35" ∧ e.pre = some "while.body6" ∧
  (∃ (c q : Nat), ps[c]? = some q ∧ pos0 + n ≤ q ∧
    lookupName e.env "%k.1296" = some (.int 64 (BitVec.ofNat 64 c)) ∧
    lookupName e.env "%conv8" = some (.int 64 (BitVec.ofNat 64 q))) ∧
  lookupName e.env "%p" = some (.ptr b) ∧
  lookupName e.env "%xp" = some (.ptr xp) ∧
  lookupName e.env "%tab" = some (.ptr tab) ∧
  lookupName e.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%err" = some (.ptr err) ∧
  lookupName e.env "%xj" = some (.ptr xj) ∧
  UnchangedOutside mem e.mem [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)]

/-- **`while.body`'s edge**, admitted with the witness that makes it live: the
pre-scan loaded a position below the window's start.  The range clause's lower
bound contracts it under an admissible staging. -/
def AssemblyWhileBodyExit (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (err xj : Nat) (mem : Mem) (e : State) : Prop :=
  e.pc = "while.end35" ∧ e.pre = some "while.body" ∧
  (∃ (k q : Nat), ps[k]? = some q ∧ q < pos0 ∧
    lookupName e.env "%k.0287" = some (.int 64 (BitVec.ofNat 64 k)) ∧
    lookupName e.env "%conv" = some (.int 64 (BitVec.ofNat 64 q))) ∧
  lookupName e.env "%p" = some (.ptr b) ∧
  lookupName e.env "%xp" = some (.ptr xp) ∧
  lookupName e.env "%tab" = some (.ptr tab) ∧
  lookupName e.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%err" = some (.ptr err) ∧
  lookupName e.env "%xj" = some (.ptr xj) ∧
  UnchangedOutside mem e.mem [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)]

/-- **The success conclusion**, on `us_run.exit112`'s edge.  The returned value is
`%add40`, the decoded length the walk names; the cursor slot holds the walk's
count, and the offset slot is untouched.  This is the edge a predecessor set made
of refusals alone would have dropped, and with it the record's `v = out.length`
clause. -/
def AssemblySuccessExit (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (err xj : Nat) (mem : Mem) (e : State) : Prop :=
  e.pc = "cleanup41" ∧ e.pre = some "us_run.exit112" ∧
  lookupName e.env "%p" = some (.ptr b) ∧
  lookupName e.env "%xp" = some (.ptr xp) ∧
  lookupName e.env "%tab" = some (.ptr tab) ∧
  lookupName e.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%err" = some (.ptr err) ∧
  lookupName e.env "%xj" = some (.ptr xj) ∧
  (∃ (out : List UInt8) (k : Nat),
    goal = .decoded out k ∧
    lookupName e.env "%add40" = some (.int 64 (BitVec.ofNat 64 out.length)) ∧
    readBytes e.mem dst out.length = some out ∧
    readBytes e.mem xj 8 = some (wordBytes 8 k) ∧
    readBytes e.mem err 8 = readBytes mem err 8) ∧
  UnchangedOutside mem e.mem [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)]

/-- **The refusal's exit**, on `if.then20`'s or `if.then22`'s edge.

`DecodeRefusalExit` is the *state-shaped* conjunct, and it stays that: it records
the block, the two cells and the two stores, and it names no staging.  The tie that
makes it a statement about this run is here — the predecessor disjunction, the
destinations pinned to the caller's slots, and `goal = .refused off k` at the
state's own `%sub`/`%inc11`, which is what connects the branch to the walk the
record's `post` matches.  A reader must not take the generic name for the whole
fact. -/
def AssemblyRefusalExit (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (err xj : Nat) (mem : Mem) (e : State) : Prop :=
  DecodeRefusalExit e ∧
  (e.pre = some "if.then20" ∨ e.pre = some "if.then22") ∧
  lookupName e.env "%err" = some (.ptr err) ∧
  lookupName e.env "%xj" = some (.ptr xj) ∧
  (∃ (off k : BitVec 64),
    lookupName e.env "%sub" = some (.int 64 off) ∧
    lookupName e.env "%inc11" = some (.int 64 k) ∧
    goal = .refused off.toNat k.toNat) ∧
  UnchangedOutside mem e.mem [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)]

/-- **The exit word**: the caller's staging, and one branch per `phi` edge of the
two exit blocks.  The branch list is the pinned tables' incoming lists, not a
reachable-set claim; the reachable set is the exclusion theorems' subject. -/
def assemblyExitWord (args : List Value) (mem : Mem) (next : Nat)
    (body : List UInt8) (st : ClassState) (dst nps : Nat) (goal : EscapeOutcome)
    (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat) (err xj : Nat)
    (e : State) : Prop :=
  ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps err xj ∧
  (AssemblyLatchExit body st dst nps goal b xp tab pos0 n ps err xj mem e ∨
   AssemblyEntryExit body st dst nps goal b xp tab pos0 n ps err xj mem e ∨
   AssemblyWhileBody6Exit body st dst nps goal b xp tab pos0 n ps err xj mem e ∨
   AssemblyWhileBodyExit body st dst nps goal b xp tab pos0 n ps err xj mem e ∨
   AssemblySuccessExit body st dst nps goal b xp tab pos0 n ps err xj mem e ∨
   AssemblyRefusalExit body st dst nps goal b xp tab pos0 n ps err xj mem e)

/-! ### The two arm statements -/

/-- **The iteration arm**, at the staged invariant and the caller's staging: one
position's copy, its escape, and the return to the latch with the index advanced.

The staging is a parameter rather than something the invariant implies, because
the arm derives its two reads from it: `while.body6`'s position load needs the
list `ExpandStaging` names at `*xp`, and the emitter's table read needs the table
`ExpandStaging` names at `%tab`.  `ExpandStaging.latch_reads` transfers both across
the latch's frame, so the arm gets them where the staging is in scope.  A step
whose hypothesis is `AssemblyLatchInv` alone could not reach either read, and a
run stated that way would be a theorem about one producer's staging rather than
about the caller's.  `.refuse` and `.seed` take the same staging, so the three
runs are one shape. -/
def assemblyLatchStep (args : List Value) (mem : Mem) (next : Nat)
    (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab pos0 n : Nat) (ps : List Nat)
    (err xj : Nat)
    (hstaging : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps
      err xj) (cost : Nat) : Prop :=
  ∀ (r : Nat) (s : State) (c : Nat),
    AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem (r + 1) c s →
    (decide (nps ≤ c) || decodeRefuses body ps pos0 c) = false →
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "cleanup32" ∧
      c < c' ∧
      AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem r c' e ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
        runFuel escapeCalls k usDecFunction e

/-- **The refusal arm**, at the staged invariant: the refusal's stores and its
exit at `cleanup41`, with the exit word's strengthened refusal form. -/
def assemblyRefusalArm (args : List Value) (mem : Mem) (next : Nat)
    (body : List UInt8) (st : ClassState) (dst nps : Nat) (goal : EscapeOutcome)
    (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat) (err xj : Nat)
    (hstaging : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps
      err xj) (cost : Nat) : Prop :=
  ∀ (r : Nat) (s : State) (c : Nat),
    AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem r c s →
    (decide (nps ≤ c) || decodeRefuses body ps pos0 c) = true → ¬ nps ≤ c →
    ∃ (e : State) (j : Nat), j ≤ cost ∧ decodeTwoExit e ∧
      assemblyExitWord args mem next body st dst nps goal b xp tab pos0 n ps err xj e ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
        runFuel escapeCalls k usDecFunction e

/-! ### The decoded exit at the arm

`DecodeLatch` carries `c ≤ nps`; the exit test being false is `nps ≤ c`; the two
give the index the exit's store carries.  The step is re-derived here rather than
projected from `decodeLatch_step_exit`, because the word now names the exit state's
cells as the caller's: the state the step returns has to be in hand for those
pinnings to be proved, and the earlier lemma returns it existentially. -/
theorem assemblyLatchStepExit {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    {mem : Mem} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj
      mem r c s)
    (hb : decide (nps ≤ c) = true) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧
      AssemblyLatchExit body st dst nps goal b xp tab pos0 n ps err xj mem e ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
        runFuel escapeCalls k usDecFunction e := by
  obtain ⟨hp_b, hxp_b, htab_b, hpos0_b, hn_b⟩ := assemblyLatchInv_params h
  obtain ⟨herr_b, hxj_b⟩ := assemblyLatchInv_dest h
  have hframe := assemblyLatchInv_frame h
  obtain ⟨i, out, prev, sub, inc11, adv, jv, nxp, paddr, xpaddr, tabaddr, erraddr,
    xjaddr, pos0v, addv, nv, hpc, hwalk, hcle, hpre, hsub, hinc11, hnxp, hnps, hphi,
    hnext, hi, hjlen, hpcell, hdstcell, hxpcell, htabcell, herrcell, hxjcell,
    hpos0cell, haddcall, hncell⟩ := (assemblyLatchInv_latch h).1
  have hge : ¬ (decodeNextIdx inc11 adv).toNat < nxp.toNat := by
    rw [hnext, hnps]
    exact Nat.not_lt_of_ge (of_decide_eq_true hb)
  have hcond : evalICmp .ult (decodeNextIdx inc11 adv) nxp = (0 : BitVec 1) :=
    (evalICmp_ult_zero_iff _ _).2 hge
  have hceq : c = nps := by
    have hge' : nps ≤ c := of_decide_eq_true hb
    omega
  rcases hphi with ⟨hprev, hj, ha⟩ | ⟨hprev, hj, hadv⟩
  · subst hprev
    let e : State :=
      { (withEnv (udCleanup32Env s.env jv adv sub inc11 nxp) s) with
          pc := "while.end35", pre := some "cleanup32" }
    have hstep : step escapeCalls usDecFunction s = .jump e := by
      have h1 := udCleanup32_step_zero s.env s "if.end32.i" (.reg "%add.i125")
        (.reg "%adv.1.i") jv adv sub inc11 nxp hpc hpre
        latch_phi_operand_emitter latch_phi_operand_emitter_adv
        (evalOperand_reg_eq s.env s "%add.i125" (.int 64 jv) hj)
        (by
          rw [evalOperand_reg_eq (("%j.3", .int 64 jv) :: s.env) s "%adv.1.i"
            (.int 64 adv) (by rw [lookupName_cons_ne _ _ (by decide)]; exact ha)])
        hsub hinc11 hnxp hcond
      have hs : withEnv s.env s = s := rfl
      rw [hs] at h1
      exact h1
    refine ⟨e, 1, by omega, ?_, fun k => runFuel_jump_prefix hstep k⟩
    have hcur : latchCursor s = some i := by
      simp only [latchCursor, hpre, hsub, ha, hi]
    refine ⟨rfl, rfl, ⟨c, i, out, jv, adv + sub, decodeNextIdx inc11 adv, paddr,
      xpaddr, tabaddr, erraddr, xjaddr, pos0v, addv, nv, rfl, ?_, hceq, ?_, hjlen,
      ?_, hi, ?_, hnext, hpcell, hdstcell, hxpcell, htabcell, herrcell, hxjcell,
      hpos0cell, haddcall, hncell⟩, ?_, hp_b, hxp_b, htab_b, hpos0_b, hn_b, herr_b,
      hxj_b, hframe⟩
    · rw [show e.mem = s.mem from rfl]; exact hwalk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · simp only [e, withEnv, udCleanup32Env, decodeNextIdx, decodePairBit]; ud_lk
    · refine ⟨adv + sub, ?_, ?_⟩
      · simp only [e, withEnv, udCleanup32Env]; ud_lk
      · rw [hi]; exact assemblyLatchInv_cursor h i hcur
  · subst hprev
    let e : State :=
      { (withEnv (udCleanup32Env s.env jv adv sub inc11 nxp) s) with
          pc := "while.end35", pre := some "cleanup32" }
    have hstep : step escapeCalls usDecFunction s = .jump e := by
      have h1 := udCleanup32_step_zero s.env s "if.then6.i" (.reg "%add8.i")
        (.imm (.int 64 (BitVec.ofInt 64 2))) jv adv sub inc11 nxp hpc hpre
        latch_phi_operand_simple latch_phi_operand_simple_adv
        (evalOperand_reg_eq s.env s "%add8.i" (.int 64 jv) hj)
        (by rw [hadv]; rfl)
        hsub hinc11 hnxp hcond
      have hs : withEnv s.env s = s := rfl
      rw [hs] at h1
      exact h1
    refine ⟨e, 1, by omega, ?_, fun k => runFuel_jump_prefix hstep k⟩
    have hcur : latchCursor s = some i := by
      simp only [latchCursor, hpre, hsub]
      rw [← hadv, hi]
    refine ⟨rfl, rfl, ⟨c, i, out, jv, adv + sub, decodeNextIdx inc11 adv, paddr,
      xpaddr, tabaddr, erraddr, xjaddr, pos0v, addv, nv, rfl, ?_, hceq, ?_, hjlen,
      ?_, hi, ?_, hnext, hpcell, hdstcell, hxpcell, htabcell, herrcell, hxjcell,
      hpos0cell, haddcall, hncell⟩, ?_, hp_b, hxp_b, htab_b, hpos0_b, hn_b, herr_b,
      hxj_b, hframe⟩
    · rw [show e.mem = s.mem from rfl]; exact hwalk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · simp only [e, withEnv, udCleanup32Env, decodeNextIdx, decodePairBit]; ud_lk
    · refine ⟨adv + sub, ?_, ?_⟩
      · simp only [e, withEnv, udCleanup32Env]; ud_lk
      · rw [hi]; exact assemblyLatchInv_cursor h i hcur


/-! ### The two-exit instance at the staged invariant

One `BoundLoop` for both exits, at the invariant the arms consume: the bound is
the list's length, the head the latch, the exit test the disjunction "at the bound
or the head position refuses", and the exit word the strengthened three-edge one.
The exit arm's bound case is `assemblyLatchStepExit`; the refusal case is the
caller's arm. -/
def assemblyBoundLoop (args : List Value) (mem : Mem) (next : Nat)
    (body : List UInt8) (st : ClassState) (dst nps : Nat) (goal : EscapeOutcome)
    (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat) (err xj : Nat)
    (hstaging : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps
      err xj) (cost : Nat) (hcost : 1 ≤ cost)
    (hrefuse : assemblyRefusalArm args mem next body st dst nps goal b xp tab pos0 n
      ps err xj hstaging cost)
    (hloop : assemblyLatchStep args mem next body st dst nps goal b xp tab pos0 n ps
      err xj hstaging cost) :
    BoundLoop escapeCalls usDecFunction where
  head := "cleanup32"
  exitBlock := "while.end35"
  N := nps
  cost := cost
  Inv := fun r s c =>
    AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem r c s
  atBound := fun _ c => decide (nps ≤ c) || decodeRefuses body ps pos0 c
  Exit := decodeTwoExit
  ExitWord := assemblyExitWord args mem next body st dst nps goal b xp tab pos0 n ps
    err xj
  step_exit := by
    intro r s c h hat
    by_cases hb : nps ≤ c
    · obtain ⟨e, j, hj, hexit, hrun⟩ :=
        assemblyLatchStepExit h (decide_eq_true hb)
      exact ⟨e, j, by omega, Or.inl hexit.1, ⟨hstaging, Or.inl hexit⟩, hrun⟩
    · have hrf : decodeRefuses body ps pos0 c = true := by
        cases hr : decodeRefuses body ps pos0 c with
        | false =>
            rw [hr] at hat
            simp [hb] at hat
        | true => rfl
      exact hrefuse r s c h hat hb
  step_loop := hloop
  exit_at_zero := by
    intro s c h
    have hb := assemblyLatchInv_budget h
    simp [decide_eq_true (by omega : nps ≤ c)]
  budget := by
    intro r s c h
    exact assemblyLatchInv_budget h

/-- **The staged walk's fuel**: from the latch at the whole bound, the run reaches
an exit state the word admits within `(nps + 1) * cost`, and a continuation that
splits once at the exit lifts to the whole walk. -/
theorem assemblyBoundLoop_run_at (args : List Value) (mem : Mem) (next : Nat)
    (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab pos0 n : Nat) (ps : List Nat) (err xj : Nat)
    (hstaging : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps
      err xj) (cost : Nat) (hcost : 1 ≤ cost)
    (hrefuse : assemblyRefusalArm args mem next body st dst nps goal b xp tab pos0 n
      ps err xj hstaging cost)
    (hloop : assemblyLatchStep args mem next body st dst nps goal b xp tab pos0 n ps
      err xj hstaging cost)
    (s : State) (c : Nat) (k : Nat)
    (hinv : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem nps c s)
    {o : Outcome}
    (hcont : ∀ (e : State), decodeTwoExit e →
      assemblyExitWord args mem next body st dst nps goal b xp tab pos0 n ps err xj e →
      runFuel escapeCalls k usDecFunction e = some o) :
    runFuel escapeCalls ((nps + 1) * cost + k) usDecFunction s = some o :=
  (assemblyBoundLoop args mem next body st dst nps goal b xp tab pos0 n ps err xj
    hstaging cost hcost hrefuse hloop).run_at s c hinv k hcont

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.AssemblyLatchInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AssemblyLatchInv

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_latch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_latch

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_params' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_params

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_paddr_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_paddr_eq

/-- info: 'LeanLLVM.Vellum.AssemblyLatchExit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AssemblyLatchExit

/-- info: 'LeanLLVM.Vellum.assemblyLatchStepExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyLatchStepExit

/-- info: 'LeanLLVM.Vellum.assemblyBoundLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyBoundLoop

/-- info: 'LeanLLVM.Vellum.assemblyBoundLoop_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyBoundLoop_run_at

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_cursor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_cursor

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_spaced' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_spaced

/-- info: 'LeanLLVM.Vellum.Spaced.head_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spaced.head_le

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_cursor_le_head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_cursor_le_head

/-- info: 'LeanLLVM.Vellum.Spaced.step_tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spaced.step_tail

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_spaced_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_spaced_succ

end LeanLLVM.Vellum
