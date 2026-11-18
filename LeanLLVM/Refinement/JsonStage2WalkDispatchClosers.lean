/-
The closing delimiter with a container open: the last class before the letters.

## The route

With `C.sp > 0` a `]` (byte `93`) or a `}` (byte `125`) does not refuse for want of a
container.  Both enter `if.then53.i`, and the depth test's *non*-refusal arm takes them
to `if.end59.i`, the nesting check:

| block | class | what the link is |
|---|---|---|
| `NodeBlock21` → `NodeBlock19` | A | `%8 < 91` is false at both bytes |
| `NodeBlock19` → `NodeBlock11` / `NodeBlock17` | A | `%8 < 123` is true at `]`, false at `}` |
| `NodeBlock11` → `LeafBlock9` / `NodeBlock17` → `LeafBlock15` | A | `%8 < 93` / `%8 < 125` |
| `LeafBlock9` / `LeafBlock15` | A | `%8 = 93` / `%8 = 125`, both to `if.then53.i` |
| `if.then53.i` | A | `%sp.i.0248 = 0` is false, so the edge is `if.end59.i` |
| `if.end59.i` | G | both stacks' bytes at `sp - 1`, the marker compared with the byte |
| `if.end74.i` | G | the state stack's byte at the same index |
| `cond.end.i` / `NodeBlock27` | A | the state byte's own test |
| `if.then109.i` | F | calls `@s2_after_value`; the log's hash word is zero |
| `if.end.i.i55` | G | the two log words, the event reserve's guard |
| `out_reserve.exit.i.i60` | D | the tag byte and the cursor, at the merge |

The nesting check compares the *expected* marker — `1` for `}`, `2` for `]` — with the
type stack's byte one below the depth (`walkSelVal`).  A disagreement is the refusal
`if.then71.i`; agreement reads the state stack's byte at the same index and tests it:
`]` merges at `0` and `1` (`cond.end.i`'s `%15 ult 2`), `}` at `0` and `3`
(`NodeBlock27`'s `%15 slt 3` then `LeafBlock23`/`LeafBlock25`'s equality), and anything
else is the state stack's refusal at `cleanup104.i`.  Both refusals store the entry's
position at `%e + 8` and jump to the refusal copy; the merge's index is `%inc.i` and its
depth `%sub.i` — the closing delimiter consumes an entry and pops a container.

## The counts

| route | links | endpoint |
|---|---|---|
| merge, `]` | 11 | `cleanup478.i` at `%sub.i`, `%inc.i` |
| merge, `}` | 13 | the same merge, through `cond.true.i` and `NodeBlock27` |
| marker mismatch, `]` | 7 | `if.then` (`mismatchedRefuse_at`) |
| marker mismatch, `}` | 7 | `if.then` |
| state mismatch, `]` | 9 | `if.then` |
| state mismatch, `}` | 11 | `if.then` |

The prices are the endpoints' own: the merge's `p + 2 ≤ 32·Δk + 8·ΔA` at one entry, and
the refusal's `p + 2 ≤ 32·(nep - k) + 8·(n - entryPos k)` — `refusePrice_of_le`'s bound,
which every refusal of at most thirty steps fits.

## Where the states come from

Every link's target is the state the *next* link reads a cell from, so each is named
before it is a segment's index.  The head's states are the operands' literals
(`refuseS₁`…`refuseS₄` for `]`, `closeBcS₁`…`closeBcS₄` for `}`); the nesting check's is
`stackSelOut`, `if.end74.i`'s is `ifEnd74Out`; and the two tail blocks whose target is
inside their proofs — `if.end.i.i55` and `out_reserve.exit.i.i60` — are named by
`closeEndIIRun`/`closeEndIIS` and `closeEmitRun`/`closeEmitS` with their own `step`
equations, exactly as the opener's three are.

## The merge route at a staged document

`JsonStage2WalkDispatchOpenersDomain`'s depth-one producer states the reached *head*, not
the stacks, so the documents' merge routes were every reachable route's refusal.  This
module's `containerOpen_depth_one_stacks` extends that producer with the push's two bytes,
which is what lets `[]` and `{}` select the merge: the push writes `ifEnd24StByte` (`0`)
on the state stack, and `0` is a merge value for both bytes.
`JsonStage2WalkDispatchClosersDomain` is that exercise: `[]` and `{}` merge at
`closeBracketMerge_at` and `closeBraceMerge_at`, `[}` and `{]` are the marker's refusals,
and the one-byte `]`/`}` are the depth's negative controls.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalar
import LeanLLVM.Refinement.JsonStage2WalkDispatchCommaArms
import LeanLLVM.Refinement.JsonStage2WalkDispatchColonArms
import LeanLLVM.Refinement.JsonStage2WalkDispatchBase

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanLane
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The carriers

One abbreviation per named carry of the route, so the term a link's conclusion names and
the term the next link is stated at are the same term. -/

/-- The carry at `if.then53.i`: the head's, with the block advanced. -/
abbrev closeC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "if.then53.i" }

/-- The carry at `if.end59.i`: the nesting check's source. -/
abbrev closeC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "if.end59.i" }

/-- The carry at `if.end74.i`: the state stack's read. -/
abbrev closeC₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "if.end74.i" }

/-- The carry at `cond.end.i`: the state byte's test, on `]`'s route. -/
abbrev closeC₄b {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "cond.end.i" }

/-- The carry at `cond.true.i`: the state byte's test, on `}`'s route. -/
abbrev closeC₄c {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "cond.true.i" }

/-- The carry at `NodeBlock27`: `}`'s state byte against `3`. -/
abbrev closeC₅c {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock27" }

/-- The carry at `LeafBlock23`: `}`'s state byte against `0`. -/
abbrev closeC₆a {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "LeafBlock23" }

/-- The carry at `LeafBlock25`: `}`'s state byte against `3`, above the pivot. -/
abbrev closeC₆b {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "LeafBlock25" }

/-- The carry at `cleanup104.i`: the state stack's refusal store. -/
abbrev closeC_R {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "cleanup104.i" }

/-! ### The brace's head

`}`'s four pivots: `123 < 91` false, `123 < 123` false, `123 < 125` true, `123 = 125`
false.  The last is the leaf's equality test's clear arm, which is the same
`if.then53.i` the bracket reaches through `LeafBlock9`. -/

/-- `NodeBlock21` at `%8 = 125`: `%8 < 91` is false, so the edge is `NodeBlock19`. -/
def closeBcS₁ (s : State) : State :=
  { s.bind "%Pivot22" (.int 1 (0 : BitVec 1)) with pc := "NodeBlock19", pre := some s.pc }

/-- `NodeBlock19` at `%8 = 125`: `%8 < 123` is false, so the edge is `NodeBlock17`. -/
def closeBcS₂ (s : State) : State :=
  { s.bind "%Pivot20" (.int 1 (0 : BitVec 1)) with pc := "NodeBlock17", pre := some s.pc }

/-- `NodeBlock17` at `%8 = 125`: `%8 < 125` is false, so the edge is `LeafBlock15`. -/
def closeBcS₃ (s : State) : State :=
  { s.bind "%Pivot18" (.int 1 (0 : BitVec 1)) with pc := "LeafBlock15", pre := some s.pc }

/-- `LeafBlock15` at `%8 = 125`: `%8 = 125` is true, so the edge is `if.then53.i`. -/
def closeBcS₄ (s : State) : State :=
  { s.bind "%SwitchLeaf16" (.int 1 (1 : BitVec 1)) with
    pc := "if.then53.i", pre := some s.pc }

/-- **`NodeBlock21` at a closing brace.** -/
theorem closeBcStep₁ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125))) :
    WalkLink calls G C s { C with block := "NodeBlock19" } (closeBcS₁ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock21_at G C s hInv hhead h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 125) (BitVec.ofNat 8 91) = 0 := by decide
  have hstate : s' = closeBcS₁ s := hs'.trans (by simp [closeBcS₁, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`NodeBlock19` at a closing brace.** -/
theorem closeBcStep₂ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock19")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125))) :
    WalkLink calls G C s { C with block := "NodeBlock17" } (closeBcS₂ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock19_at G C s hInv hblock h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 125) (BitVec.ofNat 8 123) = 0 := by decide
  have hstate : s' = closeBcS₂ s := hs'.trans (by simp [closeBcS₂, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`NodeBlock17` at a closing brace.** -/
theorem closeBcStep₃ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock17")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125))) :
    WalkLink calls G C s { C with block := "LeafBlock15" } (closeBcS₃ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.NodeBlock17_at G C s hInv hblock h8
  have hbit : evalICmp .slt (BitVec.ofNat 8 125) (BitVec.ofNat 8 125) = 0 := by decide
  have hstate : s' = closeBcS₃ s := hs'.trans (by simp [closeBcS₃, hbit])
  rw [hstate] at hl
  simpa [hbit] using hl

/-- **`LeafBlock15` at a closing brace.** -/
theorem closeBcStep₄ {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "LeafBlock15")
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125))) :
    WalkLink calls G C s (closeC₁ C) (closeBcS₄ s) := by
  obtain ⟨s', hl, hs'⟩ := WalkLink.LeafBlock15_at G C s hInv hblock h8
  have hbit : evalICmp .eq (BitVec.ofNat 8 125) (BitVec.ofNat 8 125) = 1 := by decide
  have hstate : s' = closeBcS₄ s := hs'.trans (by simp [closeBcS₄, hbit])
  rw [hstate] at hl
  simpa [hbit, closeC₁] using hl

/-! ### The two heads, counted at four

The bracket's four pivots are `refuseStep₁`…`refuseStep₄` at the byte's literal; the
brace's are `closeBcStep₁`…`closeBcStep₄`.  Each link's `%8` is the invariant's own
per-iteration carrier (`WalkIter.reg8`), so the byte's literal is `hbe`, not a premise per
link. -/

/-- The brace's state at `if.then53.i`: the four pivots' chain. -/
abbrev closeBraceS₄ (s : State) : State :=
  closeBcS₄ (closeBcS₃ (closeBcS₂ (closeBcS₁ s)))

/-- **The bracket's route to `if.then53.i`.** -/
theorem closeBracketHeadSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 93) :
    Seg calls G C s (closeC₁ C) (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))) 4 := by
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) := by
    simp only [evalOperand]; rw [hInv.iter.reg8, hbe]
  have L₁ := refuseStep₁ (calls := calls) G C s hInv hblock h8
  have h8₁ : evalOperand (refuseS₁ s) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 93)) := by
    simp only [evalOperand]; rw [L₁.inv'.iter.reg8, hbe]
  have L₂ := refuseStep₂ (calls := calls) G { C with block := "NodeBlock19" } (refuseS₁ s)
    L₁.inv' rfl h8₁
  have h8₂ : evalOperand (refuseS₂ (refuseS₁ s)) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 93)) := by
    simp only [evalOperand]; rw [L₂.inv'.iter.reg8, hbe]
  have L₃ := refuseStep₃ (calls := calls) G { C with block := "NodeBlock11" }
    (refuseS₂ (refuseS₁ s)) L₂.inv' rfl h8₂
  have h8₃ : evalOperand (refuseS₃ (refuseS₂ (refuseS₁ s))) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 93)) := by
    simp only [evalOperand]; rw [L₃.inv'.iter.reg8, hbe]
  have L₄ := refuseStep₄ (calls := calls) G { C with block := "LeafBlock9" }
    (refuseS₃ (refuseS₂ (refuseS₁ s))) L₃.inv' rfl h8₃
  exact Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄ (Seg.nil L₄.inv'))))

/-- **The brace's route to `if.then53.i`.** -/
theorem closeBraceHeadSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 125) :
    Seg calls G C s (closeC₁ C) (closeBraceS₄ s) 4 := by
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) := by
    simp only [evalOperand]; rw [hInv.iter.reg8, hbe]
  have L₁ := closeBcStep₁ (calls := calls) G C s hInv hblock h8
  have h8₁ : evalOperand (closeBcS₁ s) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 125)) := by
    simp only [evalOperand]; rw [L₁.inv'.iter.reg8, hbe]
  have L₂ := closeBcStep₂ (calls := calls) G { C with block := "NodeBlock19" }
    (closeBcS₁ s) L₁.inv' rfl h8₁
  have h8₂ : evalOperand (closeBcS₂ (closeBcS₁ s)) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 125)) := by
    simp only [evalOperand]; rw [L₂.inv'.iter.reg8, hbe]
  have L₃ := closeBcStep₃ (calls := calls) G { C with block := "NodeBlock17" }
    (closeBcS₂ (closeBcS₁ s)) L₂.inv' rfl h8₂
  have h8₃ : evalOperand (closeBcS₃ (closeBcS₂ (closeBcS₁ s))) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 125)) := by
    simp only [evalOperand]; rw [L₃.inv'.iter.reg8, hbe]
  have L₄ := closeBcStep₄ (calls := calls) G { C with block := "LeafBlock15" }
    (closeBcS₃ (closeBcS₂ (closeBcS₁ s))) L₃.inv' rfl h8₃
  exact Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄ (Seg.nil L₄.inv'))))

/-! ### The nesting check's source

The head's five links end at `if.end59.i` — the four pivots and `if.then53.i`'s depth
test, whose cell is the non-refusal one at a positive depth. -/

/-- The bracket's state after the depth test. -/
abbrev closeBracketS₅ (s : State) : State :=
  mlS₅ (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))

/-- The brace's state after the depth test. -/
abbrev closeBraceS₅ (s : State) : State := mlS₅ (closeBraceS₄ s)

/-- **The prefix at a positive depth**: the head's four pivots and the depth test, five
links from the loop head to `if.end59.i`. -/
theorem closePrefixBracketSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 93)
    (hsp : C.sp ≠ 0) :
    WalkSegment calls G C s (closeC₂ C) (closeBracketS₅ s) 5 := by
  have hh := closeBracketHeadSeg (calls := calls) G C s hInv hblock hbe
  have h5 : WalkLink calls G (closeC₁ C) (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s))))
      (closeC₂ C) (closeBracketS₅ s) :=
    mlStep₅ (calls := calls) G (closeC₁ C)
      (refuseS₄ (refuseS₃ (refuseS₂ (refuseS₁ s)))) (Seg.measure hh).inv' rfl hsp
  exact (Seg.measure hh).trans (Seg.measure (Seg.tail h5 (Seg.nil h5.inv')))

/-- **The prefix at a positive depth, on the brace's route.** -/
theorem closePrefixBraceSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 125)
    (hsp : C.sp ≠ 0) :
    WalkSegment calls G C s (closeC₂ C) (closeBraceS₅ s) 5 := by
  have hh := closeBraceHeadSeg (calls := calls) G C s hInv hblock hbe
  have h5 : WalkLink calls G (closeC₁ C) (closeBraceS₄ s) (closeC₂ C) (closeBraceS₅ s) :=
    mlStep₅ (calls := calls) G (closeC₁ C) (closeBraceS₄ s) (Seg.measure hh).inv' rfl hsp
  exact (Seg.measure hh).trans (Seg.measure (Seg.tail h5 (Seg.nil h5.inv')))

/-! ### The cells the nesting check reads

`%sub.i` is the depth less one, `%cmp61.i` the closing byte's own test, and the marker
the type stack's byte at that index.  Nothing between the head and `if.end59.i` binds
them, so each is the invariant's at the prefix's endpoint. -/

/-- The depth's index at the nesting check. -/
theorem closeSub_eq {sp : Nat} (hpos : 0 < sp) (h32 : sp < 2 ^ 32) :
    BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295 = BitVec.ofNat 32 (sp - 1) := by
  refine BitVec.eq_of_toNat_eq ?_
  rw [pairOff_eq hpos h32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- `%8`'s test at the closing bracket: false, so `if.end74.i` takes `cond.end.i`. -/
theorem closeSelBit_93 : walkSelBit (BitVec.ofNat 8 93) = 0 := by decide

/-- `%8`'s test at the closing brace: true, so `if.end74.i` takes `cond.true.i`. -/
theorem closeSelBit_125 : walkSelBit (BitVec.ofNat 8 125) = 1 := by decide

/-- The closing bracket's expected marker is `2`. -/
theorem closeSelVal_93 : walkSelVal (BitVec.ofNat 8 93) = BitVec.ofNat 32 2 := by decide

/-- The closing brace's expected marker is `1`. -/
theorem closeSelVal_125 : walkSelVal (BitVec.ofNat 8 125) = BitVec.ofNat 32 1 := by decide

/-- An unsigned comparison at the `Nat` level, at one. -/
theorem closeUlt_one {x y : Nat} (hx : x < 256) (hy : y < 256) (h : x < y) :
    evalICmp .ult (BitVec.ofNat 8 x) (BitVec.ofNat 8 y) = 1 := by
  have hlt : (BitVec.ofNat 8 x).toNat < (BitVec.ofNat 8 y).toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
    exact h
  have hb : BitVec.ult (BitVec.ofNat 8 x) (BitVec.ofNat 8 y) = true :=
    (BitVec.ult_iff_toNat_lt).2 hlt
  simp only [evalICmp, hb, BitVec.ofBool_true]

/-- An unsigned comparison at the `Nat` level, at zero. -/
theorem closeUlt_zero {x y : Nat} (hx : x < 256) (hy : y < 256) (h : ¬ x < y) :
    evalICmp .ult (BitVec.ofNat 8 x) (BitVec.ofNat 8 y) = 0 := by
  have hlt : ¬ (BitVec.ofNat 8 x).toNat < (BitVec.ofNat 8 y).toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
    exact h
  have hb : BitVec.ult (BitVec.ofNat 8 x) (BitVec.ofNat 8 y) = false := by
    cases hu : BitVec.ult (BitVec.ofNat 8 x) (BitVec.ofNat 8 y) with
    | false => rfl
    | true => exact absurd ((BitVec.ult_iff_toNat_lt).1 hu) hlt
  simp only [evalICmp, hb, BitVec.ofBool_false]

/-- An equality at the `Nat` level, at one. -/
theorem closeEq_one {x y : Nat} (hx : x < 256) (hy : y < 256) (h : x = y) :
    evalICmp .eq (BitVec.ofNat 8 x) (BitVec.ofNat 8 y) = 1 := by
  have hbe : BitVec.ofNat 8 x = BitVec.ofNat 8 y := by
    refine BitVec.eq_of_toNat_eq ?_
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt hy, h]
  exact (evalICmp_eq_one_iff _ _).2 hbe

/-- An equality at the `Nat` level, at zero. -/
theorem closeEq_zero {x y : Nat} (hx : x < 256) (hy : y < 256) (h : ¬ x = y) :
    evalICmp .eq (BitVec.ofNat 8 x) (BitVec.ofNat 8 y) = 0 := by
  refine refuseICmp_eq_zero (fun hh => h ?_)
  have h' := congrArg BitVec.toNat hh
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h'
  exact h'

/-! ### The nesting check's cells

`if.end59.i` reads the depth register, the byte and the two stack bases, and compares the
byte's expected marker with the type stack's byte one below the depth.  The facts are the
invariant's, read at the `sp - 1` the nest forms (`pairOff_eq`). -/

/-- The cells `if.end59.i` reads: the depth, the two stack bases, and both stacks' bytes at
the depth less one. -/
structure CloseStackFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Prop where
  /-- The depth register. -/
  sp : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 C.sp))
  /-- The type stack's base. -/
  ct : lookupName s.env "%ctype.i" = some (.ptr C.stage.ctype)
  /-- The state stack's base. -/
  cs : lookupName s.env "%cst.i" = some (.ptr C.stage.cst)
  /-- The type stack's byte at the depth less one — the open container's marker. -/
  tyread : readBytes s.mem
      (C.stage.ctype + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
    some [C.tyMap (C.sp - 1)]
  /-- The state stack's byte at the same index — the marker's own state. -/
  stread : readBytes s.mem
      (C.stage.cst + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
    some [C.stMap (C.sp - 1)]
  /-- The offset is inside `2 ^ 63`, which is the gep's bound. -/
  q63 : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63

/-- **The nesting check's cells, at a positive depth.** -/
theorem closeStackFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hsp : C.sp ≠ 0) : CloseStackFacts G C s where
  sp := hInv.depth_reg
  ct := hInv.ptrs.2.2.2.1
  cs := hInv.ptrs.2.2.2.2.1
  tyread := by
    have hlt : C.sp - 1 < C.wlen := by
      have h := hInv.sp_le_wlen; omega
    rw [pairOff_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap),
      JsonEntrySteps.readBytes_one, hInv.tyBytes (C.sp - 1) hlt]
    rfl
  stread := by
    have hlt : C.sp - 1 < C.wlen := by
      have h := hInv.sp_le_wlen; omega
    rw [pairOff_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap),
      JsonEntrySteps.readBytes_one, hInv.stBytes (C.sp - 1) hlt]
    rfl
  q63 := by
    rw [pairOff_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap)]
    have h := hInv.depth_cap
    simp only [stage2StackExtent] at h
    omega

/-- **A name the nest does not bind reads through it.** -/
theorem closeSel_other (s : State) (sp ct : Nat) (db : BitVec 8) (b : UInt8)
    (bit : BitVec 1) (n : String)
    (h : "%cmp69.not.i" ≠ n ∧ "%conv67.i" ≠ n ∧ "%14" ≠ n ∧ "%arrayidx66.i" ≠ n ∧
      "%idxprom65.i" ≠ n ∧ "%conv64.i" ≠ n ∧ "%cmp61.i" ≠ n ∧ "%sub.i" ≠ n) :
    lookupName (stackSelOut s sp ct db b bit).env n = lookupName s.env n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [walkSelectEnv, cells, stateAt,
    lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2, lookupName_cons_ne _ _ h3,
    lookupName_cons_ne _ _ h4, lookupName_cons_ne _ _ h5, lookupName_cons_ne _ _ h6,
    lookupName_cons_ne _ _ h7, lookupName_cons_ne _ _ h8]

/-- The nest's offset cell, at `stackSelOut`. -/
theorem closeSel_idx (s : State) (sp ct : Nat) (db : BitVec 8) (b : UInt8) (bit : BitVec 1) :
    lookupName (stackSelOut s sp ct db b bit).env "%idxprom65.i" =
      some (.int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295).toNat)) := by
  simp only [stackSelOut, walkSelectEnv, cells, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The nest's byte test, at `stackSelOut`. -/
theorem closeSel_cmp (s : State) (sp ct : Nat) (db : BitVec 8) (b : UInt8) (bit : BitVec 1) :
    lookupName (stackSelOut s sp ct db b bit).env "%cmp61.i" =
      some (.int 1 (walkSelBit db)) := by
  simp only [stackSelOut, walkSelectEnv, cells, stateAt, walkSelBit]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The depth less one, at `stackSelOut`. -/
theorem closeSel_sub (s : State) (sp ct : Nat) (db : BitVec 8) (b : UInt8) (bit : BitVec 1) :
    lookupName (stackSelOut s sp ct db b bit).env "%sub.i" =
      some (.int 32 (BitVec.ofNat 32 sp + BitVec.ofNat 32 4294967295)) := by
  simp only [stackSelOut, walkSelectEnv, cells, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The nest's target has the source's memory. -/
theorem closeSel_mem (s : State) (sp ct : Nat) (db : BitVec 8) (b : UInt8) (bit : BitVec 1) :
    (stackSelOut s sp ct db b bit).mem = s.mem := rfl

/-- The nest's target has the source's cursor. -/
theorem closeSel_next (s : State) (sp ct : Nat) (db : BitVec 8) (b : UInt8) (bit : BitVec 1) :
    (stackSelOut s sp ct db b bit).next = s.next := rfl

/-- The state byte's value at `ifEnd74.i`'s target. -/
theorem closeByte_val (s : State) (cs q : Nat) (b : UInt8) (bit : BitVec 1) :
    evalOperand (ifEnd74Out s cs q b bit) (.reg "%15") =
      some (.int 8 (BitVec.ofNat 8 b.toNat)) := rfl

/-- `ifEnd74.i`'s target has the source's memory. -/
theorem closeByte_mem (s : State) (cs q : Nat) (b : UInt8) (bit : BitVec 1) :
    (ifEnd74Out s cs q b bit).mem = s.mem := rfl

/-- `ifEnd74.i`'s target has the source's cursor. -/
theorem closeByte_next (s : State) (cs q : Nat) (b : UInt8) (bit : BitVec 1) :
    (ifEnd74Out s cs q b bit).next = s.next := rfl

/-! ### The named states of the merge's tail

`if.end.i.i55` and `out_reserve.exit.i.i60` each conclude an existential state, so the cells
the next block reads are not terms.  Both are named here, with their own `step`
equations, exactly as the opener's `openS₈`/`openS₉` are. -/

/-- The run `if.end.i.i55` leaves: the two log words, the increment and its test. -/
abbrev closeEndIIRun {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (nl nc : BitVec 64) : State :=
  stateAt (cells
    [("%cmp.not.i.i.i59", .int 1 (evalICmp .ugt (nl + BitVec.ofNat 64 1) nc)),
     ("%add.i.i.i58", .int 64 (nl + BitVec.ofNat 64 1)),
     ("%o.val11.i.i57", .int 64 nc),
     ("%o.val.i.i56", .int 64 nl)] s.env) s

/-- `if.end.i.i55`'s target, at the reserve's clear guard. -/
abbrev closeEndIIS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (nl nc : BitVec 64) : State :=
  { env := (closeEndIIRun C s nl nc).env, mem := s.mem, next := s.next,
    pc := "out_reserve.exit.i.i60", pre := some s.pc }

/-- **`if.end.i.i55`'s step, at the state `closeEndIIS`.**  The two log words, the
increment and its clear test's edge. -/
theorem closeEndIITerm {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hpc : s.pc = "if.end.i.i55") {al ac : Nat} {nl nc : BitVec 64}
    (hlen : lookupName s.env "%len" = some (.ptr al))
    (hcap : lookupName s.env "%cap" = some (.ptr ac))
    (hreadL : readBytes s.mem al 8 = some (natToBytes nl.toNat 8))
    (hreadC : readBytes s.mem ac 8 = some (natToBytes nc.toNat 8))
    (hguard : evalICmp .ugt (nl + BitVec.ofNat 64 1) nc = 0) :
    step calls stage2Body s = .jump (closeEndIIS C s nl nc) := by
  have hden : denoteCode calls walkIf_end_i_i55.instrs s =
      some (stateAt (cells
        [("%cmp.not.i.i.i59", .int 1 (evalICmp .ugt (nl + BitVec.ofNat 64 1) nc)),
         ("%add.i.i.i58", .int 64 (nl + BitVec.ofNat 64 1)),
         ("%o.val11.i.i57", .int 64 nc),
         ("%o.val.i.i56", .int 64 nl)] s.env) s) := by
    simp only [walkIf_end_i_i55]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_load64 (calls := calls) (env := s.env) (s := s) (d := "%o.val.i.i56")
      (p := "%len") (a := al) (v := nl) hlen hreadL]
    rw [denoteCode_load64 (calls := calls)
      (env := ("%o.val.i.i56", .int 64 nl) :: s.env) (s := s)
      (d := "%o.val11.i.i57") (p := "%cap") (a := ac) (v := nc) hcap hreadC]
    rw [walkDenoteCode_add_imm_w (calls := calls)
      (env := ("%o.val11.i.i57", .int 64 nc) :: ("%o.val.i.i56", .int 64 nl) :: s.env)
      (s := s) (d := "%add.i.i.i58") (a := "%o.val.i.i56") (w := 64) (x := nl)
      (c := BitVec.ofNat 64 1) (by simp [lookupName])]
    rw [denoteCode_icmp_reg_w (calls := calls)
      (env := ("%add.i.i.i58", .int 64 (nl + BitVec.ofNat 64 1)) ::
        ("%o.val11.i.i57", .int 64 nc) :: ("%o.val.i.i56", .int 64 nl) :: s.env) (s := s)
      (d := "%cmp.not.i.i.i59") (a := "%add.i.i.i58") (b := "%o.val11.i.i57") IPred.ugt 64
      (x := nl + BitVec.ofNat 64 1) (y := nc)
      (by simp [lookupName]) (by simp [lookupName])]
    rfl
  have hd : lookupName (closeEndIIRun C s nl nc).env "%cmp.not.i.i.i59" =
      some (.int 1 (evalICmp .ugt (nl + BitVec.ofNat 64 1) nc)) := by
    dsimp only [closeEndIIRun, stateAt, cells]
    exact lookupName_cons_self _ _ _
  have hfind : stage2Body.findBlock s.pc = some walkIf_end_i_i55 := by
    rw [hpc]; exact walkIf_end_i_i55_find
  have hterm : walkIf_end_i_i55.term =
      Term.condbr (Operand.reg "%cmp.not.i.i.i59") "if.end.i.i.i64" "out_reserve.exit.i.i60" :=
    rfl
  simp only [step, hfind, hden, hterm]
  rw [walkExecTerm_condbr hd]
  simp only [closeEndIIS, closeEndIIRun]
  rw [hguard, ite_eq_right (by decide)]
  rfl

/-- The run `out_reserve.exit.i.i60` leaves: the tag's two cells. -/
abbrev closeEmitRun {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : State :=
  stateAt (cells
    [("%add.ptr.i.i61", .ptr (G.ev + C.evlen)), ("%20", .ptr G.ev)] s.env) s

/-- **`out_reserve.exit.i.i60`'s target**: the merge's own state, at the tag's store. -/
abbrev closeEmitS {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (k : BitVec 8) : State :=
  { env := (closeEmitRun C s).env,
    mem := writeBytes (writeBytes s.mem (G.ev + C.evlen) (natToBytes k.toNat 1))
      (C.stage.z + 8) (wordBytes 8 (C.evlen + 1)),
    next := s.next, pc := "cleanup478.i", pre := some s.pc }

/-- **`out_reserve.exit.i.i60`'s step, at the state `closeEmitS`.** -/
theorem closeEmitTerm {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) {k : BitVec 8} (hpc : s.pc = "out_reserve.exit.i.i60")
    (hz : lookupName s.env "%z" = some (.ptr C.stage.z))
    (hload : readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev))
    (hev64 : G.ev < 2 ^ 64)
    (hs : lookupName s.env "%conv115.i" = some (.int 8 k))
    (ho : lookupName s.env "%o.val.i.i56" = some (.int 64 (BitVec.ofNat 64 C.evlen)))
    (hst : lookupName s.env "%add.i.i.i58" = some (.int 64 (BitVec.ofNat 64 (C.evlen + 1))))
    (hlen : lookupName s.env "%len" = some (.ptr (C.stage.z + 8)))
    (hev63 : C.evlen < 2 ^ 63) (hev64len : C.evlen + 1 < 2 ^ 64) :
    step (stage2Calls stage2SubCalls) stage2Body s = .jump (closeEmitS C s k) := by
  have hden : denoteCode (stage2Calls stage2SubCalls) walkOut_reserve_exit_i_i60.instrs s =
      some (stateAt (cells
        [("%add.ptr.i.i61", .ptr (G.ev + C.evlen)), ("%20", .ptr G.ev)] s.env)
        { env := s.env,
          mem := writeBytes (writeBytes s.mem (G.ev + C.evlen) (natToBytes k.toNat 1))
            (C.stage.z + 8) (wordBytes 8 (C.evlen + 1)),
          next := s.next, pc := s.pc, pre := s.pre }) := by
    simp only [walkOut_reserve_exit_i_i60]
    conv_lhs => rw [← stateAt_self s]
    rw [walkDenoteCode_loadPtr (stage2Calls stage2SubCalls) s.env s "%20" "%z"
      (q := G.ev) hz hload hev64
      [Instr.gep "%add.ptr.i.i61" (.int 8) (.reg "%20") (.reg "%o.val.i.i56"),
       Instr.store (.int 8) (.reg "%conv115.i") (.reg "%add.ptr.i.i61"),
       Instr.store (.int 64) (.reg "%add.i.i.i58") (.reg "%len")]]
    rw [denoteCode_gep8_ofNat (stage2Calls stage2SubCalls) _ s "%add.ptr.i.i61" "%20"
      "%o.val.i.i56" (by rw [lookupName_cons_self])
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact ho) hev63
      [Instr.store (.int 8) (.reg "%conv115.i") (.reg "%add.ptr.i.i61"),
       Instr.store (.int 64) (.reg "%add.i.i.i58") (.reg "%len")]]
    rw [denoteCode_store8 (stage2Calls stage2SubCalls) _ s "%conv115.i" "%add.ptr.i.i61"
      (by rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact hs)
      (by rw [lookupName_cons_self])
      [Instr.store (.int 64) (.reg "%add.i.i.i58") (.reg "%len")]]
    rw [denoteCode_store64_ofNat (stage2Calls stage2SubCalls) _
      { env := s.env,
        mem := writeBytes s.mem (G.ev + C.evlen) (natToBytes k.toNat 1),
        next := s.next, pc := s.pc, pre := s.pre }
      "%add.i.i.i58" "%len"
      (by rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact hst)
      hev64len
      (by rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]; exact hlen) []]
    rfl
  have hfind : stage2Body.findBlock s.pc = some walkOut_reserve_exit_i_i60 := by
    rw [hpc]; exact walkOut_reserve_exit_i_i60_find
  have hterm : walkOut_reserve_exit_i_i60.term = Term.br "cleanup478.i" := rfl
  simp only [step, hfind, hden, hterm]
  simp only [execTerm]
  simp only [closeEmitS, closeEmitRun]
  rfl

/-! ### `cond.true.i`: the brace's empty block

`}`'s state-byte test enters `cond.true.i`, which has no instructions and jumps to
`NodeBlock27`.  Naming its target is what lets the byte's value be read there. -/

/-- A jump's target: the state with the successor's `pc` and the predecessor recorded. -/
abbrev closeJump (s : State) (t : String) : State :=
  { s with pc := t, pre := some s.pc }

/-- **`cond.true.i`'s link**, at the state it leaves: the block's only effect is its
`pc`. -/
theorem closeCondTrue_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "cond.true.i") :
    WalkLink calls G C s { C with block := "NodeBlock27" } (closeJump s "NodeBlock27") := by
  obtain ⟨s', hl⟩ := WalkLink.cond_true_i (calls := calls) G C s hInv hblock
  have hfind : stage2Body.findBlock s.pc = some walkCond_true_i := by
    rw [hInv.pc_eq, hblock]; exact walkCond_true_i_find
  have hden : denoteCode calls walkCond_true_i.instrs s = some s := by
    simp only [walkCond_true_i, denoteCode_nil]
  have hstep : step calls stage2Body s = .jump (closeJump s "NodeBlock27") := by
    simp only [step, hfind, hden]
    rw [show walkCond_true_i.term = Term.br "NodeBlock27" from rfl]
    simp only [execTerm, closeJump]
  have hs : s' = closeJump s "NodeBlock27" := Ctrl.jump.inj (hl.step.symm.trans hstep)
  rw [hs] at hl
  exact hl

/-! ### The nesting check's two refusal tails

The marker's disagreement and the offset store, and the state byte's disagreement and its
store.  Both end at `mlS₇`, whose memory is the store's read-back. -/

/-- The carry at `if.then71.i`: the marker's refusal block. -/
abbrev closeCM {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "if.then71.i" }

/-- The carry at `if.then`: the refusal copy. -/
abbrev closeCR {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (j : Nat) : WalkCarry G :=
  { C with block := "if.then", eoff := j, refusal := true }

/-- The bracket prefix's memory is the head's. -/
theorem closeBracketS₅_mem (s : State) : (closeBracketS₅ s).mem = s.mem := rfl

/-- The bracket prefix's cursor is the head's. -/
theorem closeBracketS₅_next (s : State) : (closeBracketS₅ s).next = s.next := rfl

/-- The brace prefix's memory is the head's. -/
theorem closeBraceS₅_mem (s : State) : (closeBraceS₅ s).mem = s.mem := rfl

/-- The brace prefix's cursor is the head's. -/
theorem closeBraceS₅_next (s : State) : (closeBraceS₅ s).next = s.next := rfl

/-- A name a `bind` does not write reads through it. -/
theorem closeBind_ne {s : State} {a n : String} {v : Value} (h : a ≠ n) :
    lookupName (s.bind a v).env n = lookupName s.env n := by
  simp only [State.bind, lookupName_cons_ne _ _ h]

/-- **A name the bracket prefix does not bind reads through it.** -/
theorem closeBracketS₅_other (s : State) (n : String)
    (h : "%Pivot22" ≠ n ∧ "%Pivot20" ≠ n ∧ "%Pivot12" ≠ n ∧ "%SwitchLeaf10" ≠ n ∧
      "%cmp54.i" ≠ n) :
    lookupName (closeBracketS₅ s).env n = lookupName s.env n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [closeBracketS₅, mlS₅, refuseS₄, refuseS₃, refuseS₂, refuseS₁, State.bind,
    lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2, lookupName_cons_ne _ _ h3,
    lookupName_cons_ne _ _ h4, lookupName_cons_ne _ _ h5]

/-- **A name the brace prefix does not bind reads through it.** -/
theorem closeBraceS₅_other (s : State) (n : String)
    (h : "%Pivot22" ≠ n ∧ "%Pivot20" ≠ n ∧ "%Pivot18" ≠ n ∧ "%SwitchLeaf16" ≠ n ∧
      "%cmp54.i" ≠ n) :
    lookupName (closeBraceS₅ s).env n = lookupName s.env n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [closeBraceS₅, closeBraceS₄, closeBcS₄, closeBcS₃, closeBcS₂, closeBcS₁, mlS₅,
    State.bind, lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2,
    lookupName_cons_ne _ _ h3, lookupName_cons_ne _ _ h4, lookupName_cons_ne _ _ h5]

/-- `bytesToNat` of a one-byte read is the byte's value. -/
theorem closeBytesToNat_one (b : UInt8) : bytesToNat [b] = b.toNat := by
  simp [bytesToNat]

/-- The comparison's `Nat` operand is the byte's value. -/
theorem closeOfNat8_toNat (b : UInt8) :
    (BitVec.ofNat 8 (bytesToNat [b])).toNat = b.toNat := by
  rw [closeBytesToNat_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt b)]

/-- **The marker agrees at the bracket's own marker.** -/
theorem closeAgree_93 {b1 : UInt8} (hm : b1.toNat = 2) :
    evalICmp .eq (walkSelVal (BitVec.ofNat 8 93))
      (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [b1])).toNat) = 1 := by
  rw [closeSelVal_93, closeOfNat8_toNat, hm]
  exact (evalICmp_eq_one_iff _ _).2 rfl

/-- **The marker agrees at the brace's own marker.** -/
theorem closeAgree_125 {b1 : UInt8} (hm : b1.toNat = 1) :
    evalICmp .eq (walkSelVal (BitVec.ofNat 8 125))
      (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [b1])).toNat) = 1 := by
  rw [closeSelVal_125, closeOfNat8_toNat, hm]
  exact (evalICmp_eq_one_iff _ _).2 rfl

/-- **The marker disagrees at the bracket's own marker.** -/
theorem closeDisagree_93 {b1 : UInt8} (hm : b1.toNat ≠ 2) :
    evalICmp .eq (walkSelVal (BitVec.ofNat 8 93))
      (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [b1])).toNat) = 0 := by
  rw [closeSelVal_93, closeOfNat8_toNat]
  refine refuseICmp_eq_zero (fun h => hm ?_)
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : (2 : Nat) < 2 ^ 32),
    Nat.mod_eq_of_lt (show b1.toNat < 2 ^ 32 by have := UInt8.toNat_lt b1; omega)] at h'
  exact h'.symm

/-- **The marker disagrees at the brace's own marker.** -/
theorem closeDisagree_125 {b1 : UInt8} (hm : b1.toNat ≠ 1) :
    evalICmp .eq (walkSelVal (BitVec.ofNat 8 125))
      (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [b1])).toNat) = 0 := by
  rw [closeSelVal_125, closeOfNat8_toNat]
  refine refuseICmp_eq_zero (fun h => hm ?_)
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : (1 : Nat) < 2 ^ 32),
    Nat.mod_eq_of_lt (show b1.toNat < 2 ^ 32 by have := UInt8.toNat_lt b1; omega)] at h'
  exact h'.symm

/-! ### The marker's refusals, at the head

The bracket's is `mismatchedRefuse_at`, whose byte is `93`; the brace's is the prefix and
`closeMarkerTailSeg`, seven links at either byte. -/

/-- **The bracket's marker refusal at the head**: `]` inside a container whose type-stack
byte is not the bracket's marker. -/
theorem closeMarkerBracket_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 93)
    (hsp : C.sp ≠ 0) (hq : (C.tyMap (C.sp - 1)).toNat ≠ 2)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    WalkRefuseAt calls G C s := by
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) := by
    simp only [evalOperand]; rw [hInv.iter.reg8, hbe]
  exact mismatchedRefuse_at G C s hInv hhead h8 hsp hq hv he hj hj64 hk

/-- **A refusal, packaged**: a counted run to the copy at `closeCR`, the word the copy
loads, and the price inside the remaining credit. -/
theorem closeRefusePkg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) {sd : State} {j p : Nat}
    (hseg : WalkSegment calls G C s (closeCR C j) sd p)
    (hword : readBytes sd.mem (C.stage.e + 8) 8 = some (wordBytes 8 j))
    (hj : j ≤ G.n) (hk : C.k < G.nep) (hp : p ≤ 30) :
    WalkRefuseAt calls G C s :=
  ⟨closeCR C j, sd, p, ⟨hseg, rfl, ⟨j, hj, hword⟩⟩, hseg.inv'.eoff_le,
    refusePrice_of_le G C hp hk⟩

/-- **The marker's disagreement and the offset store**: two links from `if.end59.i` to the
refusal copy, at a byte whose bracket is not the open container's marker. -/
theorem closeMarkerTailSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s₅ : State) (hInv : WalkInv G C s₅) (hblock : C.block = "if.end59.i")
    (f : CloseStackFacts G C s₅)
    {db : BitVec 8} {b1 : UInt8}
    (h8 : lookupName s₅.env "%8" = some (.int 8 db))
    (hmark : C.tyMap (C.sp - 1) = b1)
    (hbit : evalICmp .eq (walkSelVal db)
      (BitVec.ofNat 32 (BitVec.ofNat 8 (bytesToNat [b1])).toNat) = 0)
    {j : Nat} (hv : lookupName s₅.env "%idxprom.i" = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s₅.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkSegment calls G C s₅ (closeCR C j)
      (mlS₇ C j (stackSelOut s₅ C.sp C.stage.ctype db b1 (stackSelBit db b1))) 2 := by
  have hreadT : readBytes s₅.mem
      (C.stage.ctype + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b1] := by
    rw [← hmark]; exact f.tyread
  have L₁ : WalkLink calls G C s₅ (closeCM C)
      (stackSelOut s₅ C.sp C.stage.ctype db b1 (stackSelBit db b1)) :=
    mlStep₆ (calls := calls) G C s₅ hInv hblock f.sp h8 f.ct f.q63 hreadT hbit
  have hv' : evalOperand (stackSelOut s₅ C.sp C.stage.ctype db b1
      (stackSelBit db b1)) (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)) := by
    exact LeanLLVM.evalOperand_reg_of
      ((closeSel_other s₅ C.sp C.stage.ctype db b1 (stackSelBit db b1) "%idxprom.i"
        (by decide)).trans hv)
  have he' : lookupName (stackSelOut s₅ C.sp C.stage.ctype db b1
      (stackSelBit db b1)).env "%e" = some (.ptr C.stage.e) := by
    rw [closeSel_other s₅ C.sp C.stage.ctype db b1 (stackSelBit db b1) "%e" (by decide)]
    exact he
  have L₂ : WalkLink calls G (closeCM C)
      (stackSelOut s₅ C.sp C.stage.ctype db b1 (stackSelBit db b1)) (closeCR C j)
      (mlS₇ C j (stackSelOut s₅ C.sp C.stage.ctype db b1 (stackSelBit db b1))) :=
    mlStep₇ (calls := calls) G (closeCM C)
      (stackSelOut s₅ C.sp C.stage.ctype db b1 (stackSelBit db b1)) L₁.inv' rfl hv' he'
      hj hj64
  exact Seg.measure (Seg.tail L₁ (Seg.tail L₂ (Seg.nil L₂.inv')))

/-- **The brace's marker refusal at the head**: `}` inside a container whose type-stack
byte is not the brace's marker. -/
theorem closeMarkerBrace_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 125)
    (hsp : C.sp ≠ 0) (hq : (C.tyMap (C.sp - 1)).toNat ≠ 1)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    WalkRefuseAt calls G C s := by
  have hseg := closePrefixBraceSeg (calls := calls) G C s hInv hhead hbe hsp
  have hInv₅ := hseg.inv'
  have hk₂ : (closeC₂ C).k = C.k := rfl
  have h8₅ : lookupName (closeBraceS₅ s).env "%8" =
      some (.int 8 (BitVec.ofNat 8 125)) := by
    have h := hInv₅.iter.reg8
    rw [hk₂, hbe] at h
    exact h
  have f : CloseStackFacts G (closeC₂ C) (closeBraceS₅ s) :=
    closeStackFacts (G := G) (C := closeC₂ C) (s := closeBraceS₅ s) hInv₅
      (by show (closeC₂ C).sp ≠ 0; exact hsp)
  have hv₅ : evalOperand (closeBraceS₅ s) (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 j)) := by
    simp only [evalOperand]
    rw [closeBraceS₅_other s "%idxprom.i" (by decide)]
    walk_read using hv
  have he₅ : lookupName (closeBraceS₅ s).env "%e" = some (.ptr C.stage.e) := by
    rw [closeBraceS₅_other s "%e" (by decide)]
    exact he
  have htail := closeMarkerTailSeg (calls := calls) G (closeC₂ C) (closeBraceS₅ s) hInv₅ rfl f
    h8₅ (b1 := (closeC₂ C).tyMap ((closeC₂ C).sp - 1)) rfl
    (closeDisagree_125 (by simpa only [closeC₂] using hq))
    (by exact lookupName_of_evalOperand_reg hv₅) he₅ hj hj64
  have htot : WalkSegment calls G C s (closeCR C j)
      (mlS₇ C j (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125)
        (C.tyMap (C.sp - 1)) (stackSelBit (BitVec.ofNat 8 125) (C.tyMap (C.sp - 1))))) 7 :=
    hseg.trans htail
  exact closeRefusePkg G C s htot
    (refuseSegment_word_of_store (m := (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 125) (C.tyMap (C.sp - 1))
      (stackSelBit (BitVec.ofNat 8 125) (C.tyMap (C.sp - 1)))).mem)
      (e := C.stage.e) (v := j))
    hj hk (by omega)

/-- **The state stack's disagreement and the offset store**: two links from `cond.end.i` to
the refusal copy, at a state byte of at least `2`. -/
theorem closeStateTailSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s₆ : State) (hInv : WalkInv G C s₆) (hblock : C.block = "cond.end.i")
    {b2 : UInt8}
    (h15 : lookupName s₆.env "%15" = some (.int 8 (BitVec.ofNat 8 b2.toNat)))
    (hbit : evalICmp .ult (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 2) = 0)
    {j : Nat} (hv : lookupName s₆.env "%idxprom.i" = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s₆.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkSegment calls G C s₆ (closeCR C j) (clS₉ C j (clS₈ s₆)) 2 := by
  have hv' : evalOperand s₆ (.reg "%15") = some (.int 8 (BitVec.ofNat 8 b2.toNat)) :=
    BlockEval.evalOperand_reg_of s₆.env s₆ "%15" (.int 8 (BitVec.ofNat 8 b2.toNat)) h15
  have L₁ : WalkLink calls G C s₆ { C with block := "cleanup104.i" } (clS₈ s₆) :=
    clStep₈ (calls := calls) G C s₆ hInv hblock hv' hbit
  have hv₈ : evalOperand (clS₈ s₆) (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)) := by
    show evalOperand (s₆.bind "%16" (.int 1 (0 : BitVec 1))) (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 j))
    exact LeanLLVM.evalOperand_reg_of
      ((closeBind_ne (s := s₆) (a := "%16") (n := "%idxprom.i") (v := .int 1 0)
        (by decide)).trans hv)
  have he₈ : lookupName (clS₈ s₆).env "%e" = some (.ptr C.stage.e) := by
    show lookupName (s₆.bind "%16" (.int 1 (0 : BitVec 1))).env "%e" = _
    exact (closeBind_ne (s := s₆) (a := "%16") (n := "%e") (v := .int 1 0)
      (by decide)).trans he
  have L₂ : WalkLink calls G { C with block := "cleanup104.i" } (clS₈ s₆) (closeCR C j)
      (clS₉ C j (clS₈ s₆)) :=
    clStep₉ (calls := calls) G { C with block := "cleanup104.i" } (clS₈ s₆) L₁.inv' rfl
      hv₈ he₈ hj hj64
  exact Seg.measure (Seg.tail L₁ (Seg.tail L₂ (Seg.nil L₂.inv')))

/-- **A name `if.end74.i`'s cells do not bind reads through them.** -/
theorem closeByte_other (s : State) (cs q : Nat) (b : UInt8) (bit : BitVec 1) (n : String)
    (h : "%15" ≠ n ∧ "%arrayidx76.i" ≠ n) :
    lookupName (ifEnd74Out s cs q b bit).env n = lookupName s.env n := by
  obtain ⟨h1, h2⟩ := h
  simp only [ifEnd74Out, stateAt, cells,
    lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2]

/-- **A name a cell list does not bind reads through it.** -/
theorem closeCells_other : ∀ (cs : List (String × Value)) (env : Env) (n : String),
    (∀ c ∈ cs, c.1 ≠ n) → lookupName (cells cs env) n = lookupName env n
  | [], _, _, _ => rfl
  | c :: cs, env, n, h => by
      simp only [cells]
      rw [lookupName_cons_ne _ _ (h c (by simp))]
      exact closeCells_other cs env n (fun d hd => h d (by simp [hd]))

/-- **A name a run's cells do not bind reads through them.** -/
theorem closeStateAt_other (cs : List (String × Value)) (s : State) (n : String)
    (h : ∀ c ∈ cs, c.1 ≠ n) :
    lookupName (stateAt (cells cs s.env) s).env n = lookupName s.env n :=
  closeCells_other cs s.env n h

/-- The carry at `if.then109.i`. -/
abbrev closeC₁₀ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "if.then109.i" }

/-- The carry `cond.end.i`'s merge edge leaves: the same update, written at the
state-byte test's carry so the link's conclusion matches it by unfolding alone. -/
abbrev closeC₁₀b {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { closeC₄b C with block := "if.then109.i" }

/-- The carry `LeafBlock23`'s merge edge leaves. -/
abbrev closeC₁₀a {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { closeC₆a C with block := "if.then109.i" }

/-- The carry `LeafBlock25`'s merge edge leaves. -/
abbrev closeC₁₀c {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { closeC₆b C with block := "if.then109.i" }

/-- The `cond.end.i` state's `%16` cell. -/
def closeCondBit (b2 : UInt8) : BitVec 1 :=
  evalICmp .ult (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 2)

/-- The `if.then109.i` state at `]`: the `%16` cell bound over `cond.end.i`'s successor. -/
def closeBracket109S (s₆ : State) (b2 : UInt8) : State :=
  closeJump (s₆.bind "%16" (.int 1 (closeCondBit b2))) "if.then109.i"

/-- The kind byte the bracket's merge appends. -/
theorem closeBracket_kind : BitVec.ofNat 8 4 = (BitVec.ofNat 8 4) := rfl

/-! ### `if.then109.i` at a resolved answer

The block's target is the callee's memory and cursor, so it is a function of the
`CallOutcome` the call resolves to.  `closeIfThen109Term` names it — the same shape
`openOutReserveTerm` gives the opener's tail — and `close109S` is where the merge's
next block reads from. -/

/-- The run `if.then109.i` leaves at a resolved answer and the zero hash word. -/
abbrev close109Run (s : State) (r : CallOutcome) (c8 : BitVec 8) : State :=
  stateAt (cells
    [("%tobool.not.i.i49", .int 1 (evalICmp .eq
        (BitVec.ofNat 32 (bytesToNat (natToBytes 0 4))) (BitVec.ofNat 32 0))),
     ("%17", .int 32 (BitVec.ofNat 32 (bytesToNat (natToBytes 0 4)))),
     ("%conv115.i", .int 8 c8)] s.env)
    { s with mem := r.mem, next := r.next }

/-- `if.then109.i`'s target: the merge's tail begins at `if.end.i.i55`. -/
def close109S (s : State) (r : CallOutcome) (c8 : BitVec 8) : State :=
  { close109Run s r c8 with pc := "if.end.i.i55", pre := some s.pc }

/-- **`if.then109.i`'s step, at the state `close109S`.**  The value's flag, the
zero hash word's comparison, and the edge to `if.end.i.i55`. -/
theorem closeIfThen109Term {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (c8 : BitVec 8) (hpc : s.pc = "if.then109.i")
    {p : String} {op : Operand} {spz : BitVec 32}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p walkIfThen109Incoming = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 8 c8))
    (hsub : lookupName s.env "%sub.i" = some (.int 32 spz))
    (hct : lookupName s.env "%ctype.i" = some (.ptr C.stage.ctype))
    (hcs : lookupName s.env "%cst.i" = some (.ptr C.stage.cst))
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hz : lookupName s.env "%hash1.i.i" = some (.ptr (C.stage.z + 32)))
    (hcall : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 spz, .ptr (G.next0 + 8), .ptr C.stage.ctype, .ptr C.stage.cst]
      s.mem s.next = some r)
    (hread : readBytes r.mem (C.stage.z + 32) 4 = some (natToBytes 0 4)) :
    step (stage2Calls stage2SubCalls) stage2Body s = .jump (close109S s r c8) := by
  have hden : denoteCode (stage2Calls stage2SubCalls) walkIfThen109.instrs s =
      some (close109Run s r c8) := by
    dsimp only [close109Run]
    exact walkIfThen109_denote (sub := stage2SubCalls) (env := s.env) (s := s)
      (p := p) (op := op) (c8 := c8) (spz := spz) (rd := G.next0 + 8)
      (ct := C.stage.ctype) (cs := C.stage.cst) (r := r) (hzA := C.stage.z + 32)
      hpre hinc hop hsub hrd hct hcs hcall hz hread
  have hd : lookupName (close109Run s r c8).env "%tobool.not.i.i49" =
      some (.int 1 (evalICmp .eq
        (BitVec.ofNat 32 (bytesToNat (natToBytes 0 4))) (BitVec.ofNat 32 0))) := by
    dsimp only [close109Run, stateAt, cells]
    exact lookupName_cons_self _ _ _
  have hfind : stage2Body.findBlock s.pc = some walkIfThen109 := by
    rw [hpc]; exact walkIfThen109_find
  have hterm : walkIfThen109.term =
      Term.condbr (Operand.reg "%tobool.not.i.i49") "if.end.i.i55" "if.then.i.i50" := rfl
  simp only [step, hfind, hden, hterm]
  rw [walkExecTerm_condbr hd]
  simp only [close109S]
  rw [walkBytesToNat_zero4]
  rw [show evalICmp .eq (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) = (1 : BitVec 1) from
    by decide]
  rfl

/-- A name the `if.then109.i` run's cells do not bind reads through them. -/
theorem close109Run_other (s : State) (r : CallOutcome) (c8 : BitVec 8) (n : String)
    (h : "%tobool.not.i.i49" ≠ n ∧ "%17" ≠ n ∧ "%conv115.i" ≠ n) :
    lookupName (close109Run s r c8).env n = lookupName s.env n := by
  obtain ⟨h1, h2, h3⟩ := h
  dsimp only [close109Run, stateAt]
  exact closeCells_other _ _ _ (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3)

/-- A name the `if.then109.i` state does not bind reads through it. -/
theorem close109S_other (s : State) (r : CallOutcome) (c8 : BitVec 8) (n : String)
    (h : "%tobool.not.i.i49" ≠ n ∧ "%17" ≠ n ∧ "%conv115.i" ≠ n) :
    lookupName (close109S s r c8).env n = lookupName s.env n :=
  close109Run_other s r c8 n h

/-- The tag byte the merge appends, at the `if.then109.i` state. -/
theorem close109S_conv115 (s : State) (r : CallOutcome) (c8 : BitVec 8) :
    lookupName (close109S s r c8).env "%conv115.i" = some (.int 8 c8) := by
  dsimp only [close109S, close109Run, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- A name the `cond.end.i` merge state does not bind reads through it. -/
theorem closeBracket109S_other (s₆ : State) (b2 : UInt8) (n : String) (h : "%16" ≠ n) :
    lookupName (closeBracket109S s₆ b2).env n = lookupName s₆.env n := by
  dsimp only [closeBracket109S, closeJump, State.bind]
  exact lookupName_cons_ne _ _ h

/-- The `if.then109.i` cells of the bracket's merge state. -/
theorem closeBracket109S_mem (s₆ : State) (b2 : UInt8) :
    (closeBracket109S s₆ b2).mem = s₆.mem := rfl

/-- The `if.then109.i` cursor of the bracket's merge state. -/
theorem closeBracket109S_next (s₆ : State) (b2 : UInt8) :
    (closeBracket109S s₆ b2).next = s₆.next := rfl

/-- A name `if.end.i.i55`'s run does not bind reads through it. -/
theorem closeEndIIRun_other {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (nl nc : BitVec 64) (n : String)
    (h : "%cmp.not.i.i.i59" ≠ n ∧ "%add.i.i.i58" ≠ n ∧
      "%o.val11.i.i57" ≠ n ∧ "%o.val.i.i56" ≠ n) :
    lookupName (closeEndIIRun C s nl nc).env n = lookupName s.env n := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  dsimp only [closeEndIIRun, stateAt]
  exact closeCells_other _ _ _ (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4)

/-- A name `if.end.i.i55`'s state does not bind reads through it. -/
theorem closeEndIIS_other {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (nl nc : BitVec 64) (n : String)
    (h : "%cmp.not.i.i.i59" ≠ n ∧ "%add.i.i.i58" ≠ n ∧
      "%o.val11.i.i57" ≠ n ∧ "%o.val.i.i56" ≠ n) :
    lookupName (closeEndIIS C s nl nc).env n = lookupName s.env n :=
  closeEndIIRun_other C s nl nc n h

/-- The reserve's loaded length at `if.end.i.i55`'s target. -/
theorem closeEndIIS_oval {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (nl nc : BitVec 64) :
    lookupName (closeEndIIS C s nl nc).env "%o.val.i.i56" = some (.int 64 nl) := by
  dsimp only [closeEndIIS, closeEndIIRun, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The reserve's increment at `if.end.i.i55`'s target. -/
theorem closeEndIIS_add {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (nl nc : BitVec 64) :
    lookupName (closeEndIIS C s nl nc).env "%add.i.i.i58" =
      some (.int 64 (nl + BitVec.ofNat 64 1)) := by
  dsimp only [closeEndIIS, closeEndIIRun, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- A name the tag's run cells do not bind reads through them. -/
theorem closeEmitRun_other {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (n : String)
    (h : "%add.ptr.i.i61" ≠ n ∧ "%20" ≠ n) :
    lookupName (closeEmitRun C s).env n = lookupName s.env n := by
  obtain ⟨h1, h2⟩ := h
  dsimp only [closeEmitRun, stateAt]
  exact closeCells_other _ _ _ (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact h1
    · exact h2)

/-- A name the tag's store state does not bind reads through it. -/
theorem closeEmitS_other {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (k : BitVec 8) (n : String)
    (h : "%add.ptr.i.i61" ≠ n ∧ "%20" ≠ n) :
    lookupName (closeEmitS C s k).env n = lookupName s.env n := by
  obtain ⟨h1, h2⟩ := h
  dsimp only [closeEmitS, closeEmitRun, stateAt]
  exact closeCells_other _ _ _ (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact h1
    · exact h2)

/-! ### The merge's carries, past the after-value call

The call is the one block whose target carry is a function of its answer, so the
carry's `stMap` is named here rather than left in `WalkLink.if_then109_i`'s
conclusion. -/

/-- `if.then109.i`'s carry: the after-value map at the popped index. -/
abbrev closeAfter109 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (spz : BitVec 32) : WalkCarry G :=
  { C with block := "if.end.i.i55", stMap := walkAfterValueMapAt C spz.toNat }

/-- `if.end.i.i55`'s carry: the reserve's guard is clear. -/
abbrev closeC₁₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (spz : BitVec 32) : WalkCarry G :=
  { closeAfter109 C spz with block := "out_reserve.exit.i.i60" }

/-- **The merge's carry**: the tag byte advances the event cursor by one and appends
the record the closing byte selects (`2` for `}`, `4` for `]`). -/
abbrev closeCEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (spz : BitVec 32) (c8 : BitVec 8) : WalkCarry G :=
  { closeC₁₂ C spz with
    block := "cleanup478.i", evlen := (closeC₁₂ C spz).evlen + 1,
    events := (closeC₁₂ C spz).events ++ [EventRecord.tag c8.toNat] }

/-- The merge's price at one step. -/
theorem closePrice {m0 : Mem} (G : WalkGeom m0) {k p : Nat} (hp : p ≤ 13) :
    p + 2 ≤ stage2EntryAllowance * (k + 1 - k) +
      stage2ByteAllowance * (entryPos G (k + 1) - entryPos G k) := by
  have h1 : k + 1 - k = 1 := by omega
  simp only [stage2EntryAllowance, stage2ByteAllowance, h1]
  omega

/-- The merge's index bound at one step. -/
theorem closeCap {m0 : Mem} (G : WalkGeom m0) {k : Nat} (hk : k < G.nep) :
    k + 1 ≤ (BitVec.ofNat 64 G.nep).toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (openNep_lt G)]
  omega

/-! ### The merge, on the bracket's route

Eleven links: the head's four pivots, the depth test's non-refusal edge, the
nesting check's agreement, the state stack's read, `cond.end.i`'s agreement, the
after-value call, the second reserve and the tag.  The carry's depth is `%sub.i`
and its index `%inc.i`; the tag byte is `4`. -/

/-- **The merge's three-link tail from `if.then109.i`.**  The after-value call at the
resolved answer, the second reserve and the tag; the carry's tag byte is the `phi`'s,
so the endpoint's event record is the one the closing byte selects. -/
theorem closeAfterValueSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hpc : s.pc = "if.then109.i")
    {p : String} {op : Operand} {c8 : BitVec 8}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p walkIfThen109Incoming = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 8 c8))
    (hsub : lookupName s.env "%sub.i" = some (.int 32
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)))
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (hsp : C.sp ≠ 0) (hklt : C.k < G.nep) :
    ∃ (sd : State),
      WalkSegment (stage2Calls stage2SubCalls) G C s
        (closeCEnd C (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295) c8) sd 3 ∧
      sd.pre = some "out_reserve.exit.i.i60" ∧
      lookupName sd.env "%sub.i" = some (.int 32
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)) ∧
      evalOperand sd (.reg "%inc.i") = some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
      lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) := by
  have hspz : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat =
      C.sp - 1 := by
    rw [closeSub_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have h := hInv.depth_cap
      simp only [stage2StackExtent] at h
      omega)]
  have hspzcap : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat ≤
      stage2StackExtent := by
    have h := hInv.depth_cap
    simp only [stage2StackExtent] at h ⊢
    omega
  have hbyte : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat - 1 + 1 ≤
      stage2StackExtent := by
    have h520 : stage2StackExtent = 520 := rfl
    rw [h520] at hspzcap ⊢
    omega
  obtain ⟨r, hcall, hpost, hfr⟩ := s2AfterValueContract.resolves (next := s.next) hpreA
  obtain ⟨m, hm, -, hmem, hrn⟩ := hpost
  have hread : readBytes r.mem (C.stage.z + 32) 4 = some (natToBytes 0 4) := by
    obtain h1 | ⟨b, h1⟩ := stage2AfterValue_form hm
    · rw [hmem, h1]
      rw [walkReadBytes_log_of_write (m := s.mem) (z := C.stage.z)
        (a := G.next0 + 8) (w := 4) (off := 32) (w' := 4) (bs := wordBytes 4 1)
        (by simp [wordBytes, natToBytes_length]) (by simpa using C.stage.rootSlot_log)
        (by decide)]
      exact hInv.log_hash
    · rw [hmem, h1]
      rw [walkReadBytes_log_of_write (m := s.mem) (z := C.stage.z)
        (a := C.stage.cst + ((BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat - 1))
        (w := 1) (off := 32) (w' := 4) (bs := [b])
        (by simp) (walkCstByte_log_sep (C := C) (s := s) hInv hbyte) (by decide)]
      exact hInv.log_hash
  have hstep9 := closeIfThen109Term (C := C) (s := s) r c8 hpc hpre hinc hop hsub
    hInv.ptrs.2.2.2.1 hInv.ptrs.2.2.2.2.1
    (hInv.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs]))
    hInv.ptrs.2.2.2.2.2 hcall hread
  have hspw8 : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = 0 ∨
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat - 1 < C.wlen := by
    right
    have h := hInv.sp_le_wlen
    omega
  obtain ⟨s₉, L9⟩ := WalkLink.if_then109_i G C s hInv (hInv.pc_eq.symm.trans hpc) hpre
    hinc hop hsub hspzcap
    (hInv.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs]))
    hpreA hspw8
  have hs₉ : s₉ = close109S s r c8 := Ctrl.jump.inj (L9.step.symm.trans hstep9)
  rw [hs₉] at L9
  have hevclear : C.evlen + 1 ≤ G.evcap :=
    (walkEventReserve_clear L9.inv'
      (walkEmitC_of_not_contains (b := "if.end.i.i55") (by decide)) hklt).1
  have hev63 : C.evlen < 2 ^ 63 := by
    have h1 : C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := L9.inv'.evlen_le
    have h2 := G.ev63
    omega
  have hev64len : C.evlen + 1 < 2 ^ 64 := by
    have h1 := G.evcapLt
    omega
  have hreadL : readBytes (close109S s r c8).mem
      (C.stage.z + 8) 8 = some (natToBytes (BitVec.ofNat 64 C.evlen).toNat 8) := by
    have h := L9.inv'.log_len
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : C.evlen < 2 ^ 64)]
    simpa only [wordBytes] using h
  have hreadC : readBytes (close109S s r c8).mem
      (C.stage.z + 16) 8 = some (natToBytes (BitVec.ofNat 64 G.evcap).toNat 8) := by
    have h := L9.inv'.log_cap
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt G.evcapLt]
    simpa only [wordBytes] using h
  have hguard : evalICmp .ugt (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 G.evcap) = 0 := by
    have hsum : BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1 =
        BitVec.ofNat 64 (C.evlen + 1) := BitVec.ofNat_add_ofNat _ _
    rw [hsum]
    exact walkEvalICmp_ugt_ofNat_zero hev64len G.evcapLt (by omega)
  obtain ⟨s₁₀, L10⟩ := WalkLink.if_end_i_i55 (calls := stage2Calls stage2SubCalls) G
    (closeAfter109 C (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (close109S s r c8) L9.inv' rfl
    (L9.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    (L9.inv'.regs ("%cap", .ptr (C.stage.z + 16)) (by simp [walkStaticRegs]))
    hreadL hreadC
  have hbit₁₀ : (if evalICmp .ugt (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 G.evcap) = 1 then "if.end.i.i.i64" else "out_reserve.exit.i.i60") =
      "out_reserve.exit.i.i60" := by rw [hguard]; rfl
  rw [hbit₁₀] at L10
  have hstep10 := closeEndIITerm (calls := stage2Calls stage2SubCalls) G
    (closeAfter109 C (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (close109S s r c8) rfl
    (L9.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    (L9.inv'.regs ("%cap", .ptr (C.stage.z + 16)) (by simp [walkStaticRegs]))
    hreadL hreadC hguard
  have hs₁₀ : s₁₀ = closeEndIIS (closeAfter109 C
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s r c8) (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap) :=
    Ctrl.jump.inj (L10.step.symm.trans hstep10)
  rw [hs₁₀] at L10
  have hst10 : lookupName (closeEndIIS (closeAfter109 C
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s r c8) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap)).env "%add.i.i.i58" =
      some (.int 64 (BitVec.ofNat 64 (C.evlen + 1))) := by
    rw [closeEndIIS_add, BitVec.ofNat_add_ofNat]
  have hs10 : lookupName (closeEndIIS (closeAfter109 C
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s r c8) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap)).env "%conv115.i" = some (.int 8 c8) := by
    rw [closeEndIIS_other (C := closeAfter109 C
          (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
        (s := close109S s r c8) (nl := BitVec.ofNat 64 C.evlen)
        (nc := BitVec.ofNat 64 G.evcap) (n := "%conv115.i") (by decide),
      close109S_conv115]
  have hc11 : (closeC₁₂ C
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)).events.length ≤
      (closeC₁₂ C (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)).k :=
    L10.inv'.events_le_of_tight
      (walkEmitC_of_not_contains (b := "out_reserve.exit.i.i60") (by decide))
  obtain ⟨s₁₁, L11⟩ := WalkLink.out_reserve_exit_i_i60 (calls := stage2Calls stage2SubCalls) G
    (closeC₁₂ C (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (closeEndIIS (closeAfter109 C (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s r c8) (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)) L10.inv' rfl
    (L10.inv'.regs ("%z", .ptr C.stage.z) (by simp [walkStaticRegs]))
    L10.inv'.log_base G.evLt hs10
    (closeEndIIS_oval _ _ _ _) hst10
    (L10.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    hev63 hev64len hc11 hklt
  have hstep11 := closeEmitTerm G
    (closeC₁₂ C (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (closeEndIIS (closeAfter109 C (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s r c8) (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)) rfl
    (L10.inv'.regs ("%z", .ptr C.stage.z) (by simp [walkStaticRegs]))
    L10.inv'.log_base G.evLt hs10
    (closeEndIIS_oval _ _ _ _) hst10
    (L10.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    hev63 hev64len
  have hs₁₁ : s₁₁ = closeEmitS (closeC₁₂ C
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (closeEndIIS (closeAfter109 C (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
        (close109S s r c8) (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap)) c8 :=
    Ctrl.jump.inj (L11.step.symm.trans hstep11)
  rw [hs₁₁] at L11
  refine ⟨_, Seg.measure (Seg.tail L9 (Seg.tail L10 (Seg.tail L11 (Seg.nil L11.inv')))),
    rfl, ?_, ?_, ?_⟩
  · have : lookupName
        (closeEmitS (closeC₁₂ C (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
          (closeEndIIS (closeAfter109 C
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
            (close109S s r c8) (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap))
          c8).env "%sub.i" = lookupName s.env "%sub.i" := by
      rw [closeEmitS_other (C := closeC₁₂ C
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
          (s := closeEndIIS (closeAfter109 C
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
            (close109S s r c8) (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap))
          (k := c8) (n := "%sub.i") (by decide),
        closeEndIIS_other (C := closeAfter109 C
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
          (s := close109S s r c8) (nl := BitVec.ofNat 64 C.evlen)
          (nc := BitVec.ofNat 64 G.evcap) (n := "%sub.i") (by decide),
        close109S_other (s := s) (r := r) (c8 := c8) (n := "%sub.i") (by decide)]
    rw [this, hsub]
  · simp only [evalOperand]
    rw [closeEmitRun_other (C := closeC₁₂ C
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)) (s := closeEndIIS (closeAfter109 C
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
        (close109S s r c8) (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap))
        (n := "%inc.i") (by decide),
      closeEndIIS_other (C := closeAfter109 C
          (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
        (s := close109S s r c8) (nl := BitVec.ofNat 64 C.evlen)
        (nc := BitVec.ofNat 64 G.evcap) (n := "%inc.i") (by decide),
      close109S_other (s := s) (r := r) (c8 := c8) (n := "%inc.i") (by decide)]
    exact LeanLLVM.evalOperand_reg_of hInv.inc_reg
  · rw [closeEmitRun_other (C := closeC₁₂ C
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)) (s := closeEndIIS (closeAfter109 C
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
        (close109S s r c8) (BitVec.ofNat 64 C.evlen) (BitVec.ofNat 64 G.evcap))
        (n := "%nep") (by decide),
      closeEndIIS_other (C := closeAfter109 C
          (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
        (s := close109S s r c8) (nl := BitVec.ofNat 64 C.evlen)
        (nc := BitVec.ofNat 64 G.evcap) (n := "%nep") (by decide),
      close109S_other (s := s) (r := r) (c8 := c8) (n := "%nep") (by decide)]
    exact hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])

/-- **The closing bracket's merge.**  The type stack's byte is the bracket's marker
(`2`) and the state stack's is below `2`, so the run merges. -/
theorem closeBracketMerge_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 93)
    (hsp : C.sp ≠ 0)
    {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2)
    (hb1 : b1.toNat = 2) (hb2 : b2.toNat < 2)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  have hseg5 := closePrefixBracketSeg (calls := stage2Calls stage2SubCalls) G C s hInv hhead
    hbe hsp
  have hInv5 := hseg5.inv'
  have hk5 : (closeC₂ C).k = C.k := rfl
  have h8₅ : lookupName (closeBracketS₅ s).env "%8" =
      some (.int 8 (BitVec.ofNat 8 93)) := by
    have h := hInv5.iter.reg8
    rw [hk5, hbe] at h
    exact h
  have f : CloseStackFacts G (closeC₂ C) (closeBracketS₅ s) :=
    closeStackFacts (G := G) (C := closeC₂ C) (s := closeBracketS₅ s) hInv5
      (by show (closeC₂ C).sp ≠ 0; exact hsp)
  have hmark5 : (closeC₂ C).tyMap ((closeC₂ C).sp - 1) = b1 := by
    simpa only [closeC₂] using hmark
  have hreadT : readBytes (closeBracketS₅ s).mem
      ((closeC₂ C).stage.ctype +
        (BitVec.ofNat 32 (closeC₂ C).sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b1] := by
    rw [← hmark5]; exact f.tyread
  have L6 : WalkLink (stage2Calls stage2SubCalls) G (closeC₂ C) (closeBracketS₅ s)
      (closeC₃ C)
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)) :=
    mlStep₆c (calls := stage2Calls stage2SubCalls) G (closeC₂ C) (closeBracketS₅ s) hInv5
      rfl f.sp h8₅ f.ct f.q63 hreadT (closeAgree_93 hb1)
  have hidx : lookupName
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)).env "%idxprom65.i" =
      some (.int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) :=
    closeSel_idx _ _ _ _ _ _
  have hcmp : lookupName
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)).env "%cmp61.i" =
      some (.int 1 (walkSelBit (BitVec.ofNat 8 93))) :=
    closeSel_cmp _ _ _ _ _ _
  have hreadS : readBytes
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)).mem
      (C.stage.cst + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b2] := by
    have h := f.stread
    rw [hstate] at h
    exact h
  obtain ⟨s₇, L7, hs₇⟩ := walkIfEnd74_at (calls := stage2Calls stage2SubCalls) G
    (closeC₃ C) (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93)
      b1 (stackSelBit (BitVec.ofNat 8 93) b1)) L6.inv' rfl f.cs hidx f.q63 hreadS hcmp
  have hbit₇ : walkSelBit (BitVec.ofNat 8 93) = (0 : BitVec 1) := closeSelBit_93
  have hpc₇ : (if walkSelBit (BitVec.ofNat 8 93) = (1 : BitVec 1) then "cond.true.i"
      else "cond.end.i") = "cond.end.i" := by rw [hbit₇]; rfl
  have hs₇' : s₇ = ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0 := by
    rw [hs₇, hbit₇]
  have L7' : WalkLink (stage2Calls stage2SubCalls) G (closeC₃ C)
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)) (closeC₄b C)
      (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
        (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0) := by
    rw [hpc₇] at L7
    rw [hs₇'] at L7
    exact L7
  have h15 : evalOperand (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0) (.reg "%15") =
      some (.int 8 (BitVec.ofNat 8 b2.toNat)) :=
    closeByte_val _ _ _ b2 0
  obtain ⟨s₈, L8, hs₈⟩ := WalkLink.cond_end_i_at (calls := stage2Calls stage2SubCalls) G
    (closeC₄b C) _ L7'.inv' rfl h15
  have hult : evalICmp .ult (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 2) = 1 :=
    closeUlt_one (show b2.toNat < 256 from UInt8.toNat_lt b2) (by decide) hb2
  have hbit₈ : (if evalICmp .ult (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 2) = 1 then
      "if.then109.i" else "cleanup104.i") = "if.then109.i" := by
    rw [hult]; rfl
  rw [hbit₈] at L8
  have hs₈' : s₈ = closeBracket109S (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp
      C.stage.ctype (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1))
      C.stage.cst (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0) b2 := by
    rw [hs₈, hbit₈]
    rfl
  have hInv8 : WalkInv G (closeC₁₀b C) s₈ := L8.inv'
  have hpc8 : s₈.pc = "if.then109.i" := by rw [hs₈']; rfl
  have hpre8 : s₈.pre = some "cond.end.i" := by rw [hs₈']; rfl
  have hmem8 : s₈.mem = s.mem := by rw [hs₈']; rfl
  have hnext8 : s₈.next = s.next := by rw [hs₈']; rfl
  -- the after-value call resolves here
  have hspz : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat =
      C.sp - 1 := by
    rw [closeSub_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have h := hInv.depth_cap
      simp only [stage2StackExtent] at h
      omega)]
  have hspzcap : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat ≤
      stage2StackExtent := by
    have h := hInv.depth_cap
    simp only [stage2StackExtent] at h ⊢
    omega
  have hpreA8 : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s₈.mem s₈.next := by
    rw [hmem8, hnext8]
    exact hpreA
  obtain ⟨r, hcall, hpost, hfr⟩ := s2AfterValueContract.resolves (next := s₈.next) hpreA8
  obtain ⟨m, hm, -, hmem, hrn⟩ := hpost
  have hbyte : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat - 1 + 1 ≤
      stage2StackExtent := by
    have h520 : stage2StackExtent = 520 := rfl
    rw [h520] at hspzcap ⊢
    omega
  have hread : readBytes r.mem (C.stage.z + 32) 4 = some (natToBytes 0 4) := by
    obtain h1 | ⟨b, h1⟩ := stage2AfterValue_form hm
    · rw [hmem, h1]
      rw [walkReadBytes_log_of_write (m := s₈.mem) (z := C.stage.z)
        (a := G.next0 + 8) (w := 4) (off := 32) (w' := 4) (bs := wordBytes 4 1)
        (by simp [wordBytes, natToBytes_length]) (by simpa using C.stage.rootSlot_log)
        (by decide)]
      exact L8.inv'.log_hash
    · rw [hmem, h1]
      rw [walkReadBytes_log_of_write (m := s₈.mem) (z := C.stage.z)
        (a := C.stage.cst + ((BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat - 1))
        (w := 1) (off := 32) (w' := 4) (bs := [b])
        (by simp) (walkCstByte_log_sep (C := closeC₁₀b C) (s := s₈) L8.inv' hbyte)
        (by decide)]
      exact L8.inv'.log_hash
  have hsub8 : lookupName s₈.env "%sub.i" = some (.int 32
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)) := by
    rw [hs₈']
    rw [closeBracket109S_other _ _ "%sub.i" (by decide),
      closeByte_other _ _ _ _ _ "%sub.i" (by decide)]
    exact closeSel_sub (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
      (stackSelBit (BitVec.ofNat 8 93) b1)
  have hstep9 := closeIfThen109Term (C := closeC₁₀b C) (s := s₈) r (BitVec.ofNat 8 4)
    hpc8 (p := "cond.end.i") (op := .imm (.int 8 (BitVec.ofNat 8 4)))
    hpre8 (by decide) (by simp [evalOperand]) hsub8 hInv8.ptrs.2.2.2.1
    hInv8.ptrs.2.2.2.2.1
    (hInv8.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs]))
    hInv8.ptrs.2.2.2.2.2 hcall hread
  have hspw8 : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = 0 ∨
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat - 1 <
        (closeC₁₀b C).wlen := by
    right
    have hw : (closeC₁₀b C).wlen = C.wlen := rfl
    rw [hw]
    have h := hInv.sp_le_wlen
    omega
  obtain ⟨s₉, L9⟩ := WalkLink.if_then109_i G (closeC₁₀b C) s₈ hInv8 rfl
    hpre8 (p := "cond.end.i") (op := .imm (.int 8 (BitVec.ofNat 8 4)))
    (c8 := BitVec.ofNat 8 4) (by decide) (by simp [evalOperand]) hsub8 hspzcap
    (hInv8.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs]))
    hpreA8 hspw8
  have hs₉ : s₉ = close109S s₈ r (BitVec.ofNat 8 4) :=
    Ctrl.jump.inj (L9.step.symm.trans hstep9)
  rw [hs₉] at L9
  -- `if.end.i.i55`
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have hevclear : C.evlen + 1 ≤ G.evcap :=
    (walkEventReserve_clear L9.inv'
      (walkEmitC_of_not_contains (b := "if.end.i.i55") (by decide)) hklt).1
  have hev63 : C.evlen < 2 ^ 63 := by
    have h1 : C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := L9.inv'.evlen_le
    have h2 := G.ev63
    omega
  have hev64len : C.evlen + 1 < 2 ^ 64 := by
    have h1 := G.evcapLt
    omega
  have hreadL : readBytes (close109S s₈ r (BitVec.ofNat 8 4)).mem
      (C.stage.z + 8) 8 = some (natToBytes (BitVec.ofNat 64 C.evlen).toNat 8) := by
    have h := L9.inv'.log_len
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : C.evlen < 2 ^ 64)]
    simpa only [wordBytes] using h
  have hreadC : readBytes (close109S s₈ r (BitVec.ofNat 8 4)).mem
      (C.stage.z + 16) 8 = some (natToBytes (BitVec.ofNat 64 G.evcap).toNat 8) := by
    have h := L9.inv'.log_cap
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt G.evcapLt]
    simpa only [wordBytes] using h
  have hguard : evalICmp .ugt (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 G.evcap) = 0 := by
    have hsum : BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1 =
        BitVec.ofNat 64 (C.evlen + 1) := BitVec.ofNat_add_ofNat _ _
    rw [hsum]
    exact walkEvalICmp_ugt_ofNat_zero hev64len G.evcapLt (by omega)
  obtain ⟨s₁₀, L10⟩ := WalkLink.if_end_i_i55 (calls := stage2Calls stage2SubCalls) G
    (closeAfter109 (closeC₁₀b C)
    (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (close109S s₈ r (BitVec.ofNat 8 4)) L9.inv' rfl
    (L9.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    (L9.inv'.regs ("%cap", .ptr (C.stage.z + 16)) (by simp [walkStaticRegs]))
    hreadL hreadC
  have hbit₁₀ : (if evalICmp .ugt (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 G.evcap) = 1 then "if.end.i.i.i64" else "out_reserve.exit.i.i60") =
      "out_reserve.exit.i.i60" := by rw [hguard]; rfl
  rw [hbit₁₀] at L10
  have hstep10 := closeEndIITerm (calls := stage2Calls stage2SubCalls) G
    (closeAfter109 (closeC₁₀b C)
    (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (close109S s₈ r (BitVec.ofNat 8 4)) rfl
    (L9.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    (L9.inv'.regs ("%cap", .ptr (C.stage.z + 16)) (by simp [walkStaticRegs]))
    hreadL hreadC hguard
  have hs₁₀ : s₁₀ = closeEndIIS (closeAfter109 (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap) :=
    Ctrl.jump.inj (L10.step.symm.trans hstep10)
  rw [hs₁₀] at L10
  -- `out_reserve.exit.i.i60`
  have hst10 : lookupName (closeEndIIS (closeAfter109 (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap)).env "%add.i.i.i58" =
      some (.int 64 (BitVec.ofNat 64 (C.evlen + 1))) := by
    rw [closeEndIIS_add, BitVec.ofNat_add_ofNat]
  have hs10 : lookupName (closeEndIIS (closeAfter109 (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap)).env "%conv115.i" = some (.int 8 (BitVec.ofNat 8 4)) := by
    rw [closeEndIIS_other _ _ _ _ _ (by decide),
      close109S_conv115]
  have hc11 : (closeC₁₂ (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)).events.length ≤
      (closeC₁₂ (closeC₁₀b C)
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)).k :=
    L10.inv'.events_le_of_tight
      (walkEmitC_of_not_contains (b := "out_reserve.exit.i.i60") (by decide))
  obtain ⟨s₁₁, L11⟩ := WalkLink.out_reserve_exit_i_i60 (calls := stage2Calls stage2SubCalls) G
    (closeC₁₂ (closeC₁₀b C) (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (closeEndIIS (closeAfter109 (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap)) L10.inv' rfl
    (L10.inv'.regs ("%z", .ptr C.stage.z) (by simp [walkStaticRegs]))
    L10.inv'.log_base G.evLt hs10
    (closeEndIIS_oval _ _ _ _)
    hst10
    (L10.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    hev63 hev64len hc11 hklt
  have hstep11 := closeEmitTerm G
    (closeC₁₂ (closeC₁₀b C) (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (closeEndIIS (closeAfter109 (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap)) rfl
    (L10.inv'.regs ("%z", .ptr C.stage.z) (by simp [walkStaticRegs]))
    L10.inv'.log_base G.evLt hs10
    (closeEndIIS_oval _ _ _ _) hst10
    (L10.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    hev63 hev64len
  have hs₁₁ : s₁₁ = closeEmitS (closeC₁₂ (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (closeEndIIS (closeAfter109 (closeC₁₀b C)
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
        (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 8 4) :=
    Ctrl.jump.inj (L11.step.symm.trans hstep11)
  rw [hs₁₁] at L11
  -- the composition, counted at eleven
  have hseg11 : WalkSegment (stage2Calls stage2SubCalls) G C s
      (closeCEnd (closeC₁₀b C) (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)
        (BitVec.ofNat 8 4))
      (closeEmitS (closeC₁₂ (closeC₁₀b C)
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
        (closeEndIIS (closeAfter109 (closeC₁₀b C)
          (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
          (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 8 4)) 11 :=
    hseg5.trans (Seg.measure (Seg.tail L6 (Seg.tail L7' (Seg.tail L8 (Seg.tail L9
      (Seg.tail L10 (Seg.tail L11 (Seg.nil L11.inv'))))))))
  refine WalkDispatchResult.merge _ _ 11 (C.sp - 1) (C.k + 1) "out_reserve.exit.i.i60"
    (.reg "%sub.i") (.reg "%inc.i") (BitVec.ofNat 64 G.nep) hseg11 rfl rfl ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · show phiIncoming "out_reserve.exit.i.i60" cleanupSpIncoming = some (.reg "%sub.i")
    decide
  · simp only [evalOperand]
    have hpeel : lookupName
        (closeEmitS (closeC₁₂ (closeC₁₀b C)
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
          (closeEndIIS (closeAfter109 (closeC₁₀b C)
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
            (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
            (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 8 4)).env "%sub.i" =
        lookupName s₈.env "%sub.i" := by
      rw [closeEmitS_other (C := closeC₁₂ (closeC₁₀b C)
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
          (s := closeEndIIS (closeAfter109 (closeC₁₀b C)
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
            (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
            (BitVec.ofNat 64 G.evcap)) (k := BitVec.ofNat 8 4) (n := "%sub.i")
          (by decide),
        closeEndIIS_other (C := closeC₁₂ (closeC₁₀b C)
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
          (s := close109S s₈ r (BitVec.ofNat 8 4))
          (nl := BitVec.ofNat 64 C.evlen) (nc := BitVec.ofNat 64 G.evcap)
          (n := "%sub.i") (by decide),
        close109S_other (s := s₈) (r := r) (c8 := BitVec.ofNat 8 4)
          (n := "%sub.i") (by decide)]
    rw [hpeel, hsub8,
      closeSub_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap)]
  · show phiIncoming "out_reserve.exit.i.i60" cleanupKIncoming = some (.reg "%inc.i")
    decide
  · exact LeanLLVM.evalOperand_reg_of L11.inv'.inc_reg
  · exact L11.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
      (by simp [walkStaticRegs])
  · omega
  · exact closeCap G hklt
  · have h := hInv.depth_cap
    simp only [stage2StackExtent] at h ⊢
    omega
  · show C.sp - 1 ≤ C.wlen
    have h := hInv.sp_le_wlen
    omega
  · exact closePrice G (by omega)

/-- **The closing brace's merge.**  The type stack's byte is the brace's marker (`1`)
and the state stack's is `0` or `3`, so the run merges. -/
theorem closeBraceMerge_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)))
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 125)
    (hsp : C.sp ≠ 0)
    {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2)
    (hb1 : b1.toNat = 1) (hb2 : b2.toNat = 0 ∨ b2.toNat = 3)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have hseg5 := closePrefixBraceSeg (calls := stage2Calls stage2SubCalls) G C s hInv hhead
    hbe hsp
  have hInv5 := hseg5.inv'
  have hk5 : (closeC₂ C).k = C.k := rfl
  have h8₅ : lookupName (closeBraceS₅ s).env "%8" =
      some (.int 8 (BitVec.ofNat 8 125)) := by
    have h := hInv5.iter.reg8
    rw [hk5, hbe] at h
    exact h
  have f : CloseStackFacts G (closeC₂ C) (closeBraceS₅ s) :=
    closeStackFacts (G := G) (C := closeC₂ C) (s := closeBraceS₅ s) hInv5
      (by show (closeC₂ C).sp ≠ 0; exact hsp)
  have hmark5 : (closeC₂ C).tyMap ((closeC₂ C).sp - 1) = b1 := by
    simpa only [closeC₂] using hmark
  have hreadT : readBytes (closeBraceS₅ s).mem
      ((closeC₂ C).stage.ctype +
        (BitVec.ofNat 32 (closeC₂ C).sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b1] := by
    rw [← hmark5]; exact f.tyread
  have L6 : WalkLink (stage2Calls stage2SubCalls) G (closeC₂ C) (closeBraceS₅ s)
      (closeC₃ C)
      (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)) :=
    mlStep₆c (calls := stage2Calls stage2SubCalls) G (closeC₂ C) (closeBraceS₅ s) hInv5
      rfl f.sp h8₅ f.ct f.q63 hreadT (closeAgree_125 hb1)
  have hidx : lookupName
      (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)).env "%idxprom65.i" =
      some (.int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) :=
    closeSel_idx _ _ _ _ _ _
  have hcmp : lookupName
      (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)).env "%cmp61.i" =
      some (.int 1 (walkSelBit (BitVec.ofNat 8 125))) :=
    closeSel_cmp _ _ _ _ _ _
  have hreadS : readBytes
      (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)).mem
      (C.stage.cst + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b2] := by
    have h := f.stread
    rw [hstate] at h
    exact h
  obtain ⟨s₇, L7, hs₇⟩ := walkIfEnd74_at (calls := stage2Calls stage2SubCalls) G
    (closeC₃ C) (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125)
      b1 (stackSelBit (BitVec.ofNat 8 125) b1)) L6.inv' rfl f.cs hidx f.q63 hreadS hcmp
  have hbit₇ : walkSelBit (BitVec.ofNat 8 125) = (1 : BitVec 1) := closeSelBit_125
  have hpc₇ : (if walkSelBit (BitVec.ofNat 8 125) = (1 : BitVec 1) then "cond.true.i"
      else "cond.end.i") = "cond.true.i" := by rw [hbit₇]; rfl
  have hs₇' : s₇ = ifEnd74Out (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 1 := by
    rw [hs₇, hbit₇]
  have L7' : WalkLink (stage2Calls stage2SubCalls) G (closeC₃ C)
      (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)) (closeC₄c C)
      (ifEnd74Out (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
        (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1)) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 1) := by
    rw [hpc₇] at L7
    rw [hs₇'] at L7
    exact L7
  have h15₇ : evalOperand (ifEnd74Out (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 1) (.reg "%15") =
      some (.int 8 (BitVec.ofNat 8 b2.toNat)) :=
    closeByte_val _ _ _ b2 1
  have L8 : WalkLink (stage2Calls stage2SubCalls) G (closeC₄c C)
      (ifEnd74Out (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
        (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1)) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 1)
      (closeC₅c C) (closeJump _ "NodeBlock27") :=
    closeCondTrue_at (calls := stage2Calls stage2SubCalls) G (closeC₄c C) _ L7'.inv' rfl
  have h15₈ : evalOperand (closeJump (ifEnd74Out (stackSelOut (closeBraceS₅ s) C.sp
      C.stage.ctype (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1))
      C.stage.cst (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 1)
      "NodeBlock27") (.reg "%15") = some (.int 8 (BitVec.ofNat 8 b2.toNat)) := h15₇
  obtain ⟨s₉, L9, hs₉⟩ := WalkLink.NodeBlock27_at (calls := stage2Calls stage2SubCalls) G
    (closeC₅c C) _ L8.inv' rfl (x1 := BitVec.ofNat 8 b2.toNat) h15₈
  -- the two state-stack values the brace merges at
  rcases hb2 with h0 | h3
  · -- state byte `0`: `LeafBlock23`'s equality
    have hslt : evalICmp .slt (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 := by
      rw [h0]; decide
    have heq : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 0) = 1 := by
      rw [h0]; decide
    have hpc₉ : (if evalICmp .slt (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 then
        "LeafBlock23" else "LeafBlock25") = "LeafBlock23" := by rw [hslt]; rfl
    have hc₉ : ({ closeC₅c C with block := (if evalICmp .slt
        (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 then
        "LeafBlock23" else "LeafBlock25") } : WalkCarry G) = closeC₆a C := by
      rw [hpc₉]
    rw [hc₉] at L9
    have h15₉ : evalOperand s₉ (.reg "%15") = some (.int 8 (BitVec.ofNat 8 b2.toNat)) := by
      rw [hs₉]
      simpa only [evalOperand, State.bind,
        lookupName_cons_ne (k := "%Pivot28") (n := "%15") _ _ (by decide)] using h15₈
    obtain ⟨s₁₀, L10, hs₁₀⟩ := WalkLink.LeafBlock23_at (calls := stage2Calls stage2SubCalls) G
      (closeC₆a C) s₉ L9.inv' rfl (x1 := BitVec.ofNat 8 b2.toNat) h15₉
    have hbit₁₀ : (if evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 0) = 1 then
        "if.then109.i" else "cleanup104.i") = "if.then109.i" := by rw [heq]; rfl
    rw [hbit₁₀] at L10
    have hs₁₀' : s₁₀ = closeJump (s₉.bind "%SwitchLeaf24"
        (.int 1 (evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 0)))) "if.then109.i" := by
      rw [hs₁₀]
      simp only [hbit₁₀]
      rfl
    have hInv₁₀ : WalkInv G (closeC₁₀a C) s₁₀ := L10.inv'
    have hpc10 : s₁₀.pc = "if.then109.i" := by rw [hs₁₀']
    have hpre10 : s₁₀.pre = some "LeafBlock23" := by
      rw [hs₁₀', hs₉]
      simp only [closeJump, State.bind, hpc₉]
    have hsub10 : lookupName s₁₀.env "%sub.i" = some (.int 32
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)) := by
      rw [hs₁₀', hs₉]
      simp only [closeJump, State.bind,
        lookupName_cons_ne (k := "%SwitchLeaf24") (n := "%sub.i") _ _ (by decide),
        lookupName_cons_ne (k := "%Pivot28") (n := "%sub.i") _ _ (by decide)]
      rw [closeByte_other (s := stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
          (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1))
        C.stage.cst ((BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) b2 1
        "%sub.i" (by decide)]
      exact closeSel_sub (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)
    have hmem10 : s₁₀.mem = s.mem := by rw [hs₁₀', hs₉]; rfl
    have hnext10 : s₁₀.next = s.next := by rw [hs₁₀', hs₉]; rfl
    have hpreA10 : s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
         .ptr C.stage.ctype, .ptr C.stage.cst] s₁₀.mem s₁₀.next := by
      rw [hmem10, hnext10]; exact hpreA
    obtain ⟨sd, htail, hpreS, hsubS, hk2S, hnepS⟩ :=
      closeAfterValueSeg (C := closeC₁₀a C) G s₁₀ hInv₁₀ hpc10 hpre10
        (p := "LeafBlock23") (op := .imm (.int 8 (BitVec.ofNat 8 2)))
        (c8 := BitVec.ofNat 8 2) (by decide)
        (by simp [evalOperand]) hsub10 hpreA10 (by show (closeC₁₀a C).sp ≠ 0; exact hsp) hklt
    have hseg13 : WalkSegment (stage2Calls stage2SubCalls) G C s
        (closeCEnd (closeC₁₀a C) (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)
          (BitVec.ofNat 8 2)) sd 13 :=
      (hseg5.trans (Seg.measure (Seg.tail L6 (Seg.tail L7' (Seg.tail L8 (Seg.tail L9
        (Seg.tail L10 (Seg.nil L10.inv')))))))).trans htail
    refine WalkDispatchResult.merge _ _ 13 (C.sp - 1) (C.k + 1)
      "out_reserve.exit.i.i60" (.reg "%sub.i") (.reg "%inc.i") (BitVec.ofNat 64 G.nep)
      hseg13 rfl rfl hpreS ?_ ?_ ?_ hk2S hnepS ?_ ?_ ?_ ?_ ?_
    · show phiIncoming "out_reserve.exit.i.i60" cleanupSpIncoming = some (.reg "%sub.i")
      decide
    · simp only [evalOperand]
      rw [hsubS, closeSub_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap)]
    · show phiIncoming "out_reserve.exit.i.i60" cleanupKIncoming = some (.reg "%inc.i")
      decide
    · omega
    · exact closeCap G hklt
    · have h := hInv.depth_cap
      simp only [stage2StackExtent] at h ⊢
      omega
    · show C.sp - 1 ≤ C.wlen
      have h := hInv.sp_le_wlen
      omega
    · exact closePrice G (by omega)
  · -- state byte `3`: `LeafBlock25`'s equality
    have hslt : evalICmp .slt (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 0 := by
      rw [h3]; decide
    have heq : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 := by
      rw [h3]; decide
    have hpc₉ : (if evalICmp .slt (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 then
        "LeafBlock23" else "LeafBlock25") = "LeafBlock25" := by rw [hslt]; rfl
    have hc₉ : ({ closeC₅c C with block := (if evalICmp .slt
        (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 then
        "LeafBlock23" else "LeafBlock25") } : WalkCarry G) = closeC₆b C := by
      rw [hpc₉]
    rw [hc₉] at L9
    have h15₉ : evalOperand s₉ (.reg "%15") = some (.int 8 (BitVec.ofNat 8 b2.toNat)) := by
      rw [hs₉]
      simpa only [evalOperand, State.bind,
        lookupName_cons_ne (k := "%Pivot28") (n := "%15") _ _ (by decide)] using h15₈
    obtain ⟨s₁₀, L10, hs₁₀⟩ := WalkLink.LeafBlock25_at (calls := stage2Calls stage2SubCalls) G
      (closeC₆b C) s₉ L9.inv' rfl (x1 := BitVec.ofNat 8 b2.toNat) h15₉
    have hbit₁₀ : (if evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 then
        "if.then109.i" else "cleanup104.i") = "if.then109.i" := by rw [heq]; rfl
    rw [hbit₁₀] at L10
    have hs₁₀' : s₁₀ = closeJump (s₉.bind "%SwitchLeaf26"
        (.int 1 (evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3)))) "if.then109.i" := by
      rw [hs₁₀]
      simp only [hbit₁₀]
      rfl
    have hInv₁₀ : WalkInv G (closeC₁₀c C) s₁₀ := L10.inv'
    have hpc10 : s₁₀.pc = "if.then109.i" := by rw [hs₁₀']
    have hpre10 : s₁₀.pre = some "LeafBlock25" := by
      rw [hs₁₀', hs₉]
      simp only [closeJump, State.bind, hpc₉]
    have hsub10 : lookupName s₁₀.env "%sub.i" = some (.int 32
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)) := by
      rw [hs₁₀', hs₉]
      simp only [closeJump, State.bind,
        lookupName_cons_ne (k := "%SwitchLeaf26") (n := "%sub.i") _ _ (by decide),
        lookupName_cons_ne (k := "%Pivot28") (n := "%sub.i") _ _ (by decide)]
      rw [closeByte_other (s := stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
          (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1))
        C.stage.cst ((BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) b2 1
        "%sub.i" (by decide)]
      exact closeSel_sub (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)
    have hmem10 : s₁₀.mem = s.mem := by rw [hs₁₀', hs₉]; rfl
    have hnext10 : s₁₀.next = s.next := by rw [hs₁₀', hs₉]; rfl
    have hpreA10 : s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
         .ptr C.stage.ctype, .ptr C.stage.cst] s₁₀.mem s₁₀.next := by
      rw [hmem10, hnext10]; exact hpreA
    obtain ⟨sd, htail, hpreS, hsubS, hk2S, hnepS⟩ :=
      closeAfterValueSeg (C := closeC₁₀c C) G s₁₀ hInv₁₀ hpc10 hpre10
        (p := "LeafBlock25") (op := .imm (.int 8 (BitVec.ofNat 8 2)))
        (c8 := BitVec.ofNat 8 2) (by decide)
        (by simp [evalOperand]) hsub10 hpreA10 (by show (closeC₁₀c C).sp ≠ 0; exact hsp) hklt
    have hseg13 : WalkSegment (stage2Calls stage2SubCalls) G C s
        (closeCEnd (closeC₁₀c C) (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)
          (BitVec.ofNat 8 2)) sd 13 :=
      (hseg5.trans (Seg.measure (Seg.tail L6 (Seg.tail L7' (Seg.tail L8 (Seg.tail L9
        (Seg.tail L10 (Seg.nil L10.inv')))))))).trans htail
    refine WalkDispatchResult.merge _ _ 13 (C.sp - 1) (C.k + 1)
      "out_reserve.exit.i.i60" (.reg "%sub.i") (.reg "%inc.i") (BitVec.ofNat 64 G.nep)
      hseg13 rfl rfl hpreS ?_ ?_ ?_ hk2S hnepS ?_ ?_ ?_ ?_ ?_
    · show phiIncoming "out_reserve.exit.i.i60" cleanupSpIncoming = some (.reg "%sub.i")
      decide
    · simp only [evalOperand]
      rw [hsubS, closeSub_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap)]
    · show phiIncoming "out_reserve.exit.i.i60" cleanupKIncoming = some (.reg "%inc.i")
      decide
    · omega
    · exact closeCap G hklt
    · have h := hInv.depth_cap
      simp only [stage2StackExtent] at h ⊢
      omega
    · show C.sp - 1 ≤ C.wlen
      have h := hInv.sp_le_wlen
      omega
    · exact closePrice G (by omega)

/-- **The closing bracket's state-stack refusal.**  The marker agrees but the state
byte is at least `2`, so `cond.end.i` sends the run through `cleanup104.i` to the
refusal copy — nine links. -/
theorem closeStateBracket_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 93)
    (hsp : C.sp ≠ 0)
    {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2)
    (hb1 : b1.toNat = 2) (hb2 : ¬ b2.toNat < 2)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkRefuseAt (stage2Calls stage2SubCalls) G C s := by
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have hseg5 := closePrefixBracketSeg (calls := stage2Calls stage2SubCalls) G C s hInv hhead
    hbe hsp
  have hInv5 := hseg5.inv'
  have hk5 : (closeC₂ C).k = C.k := rfl
  have h8₅ : lookupName (closeBracketS₅ s).env "%8" =
      some (.int 8 (BitVec.ofNat 8 93)) := by
    have h := hInv5.iter.reg8
    rw [hk5, hbe] at h
    exact h
  have f : CloseStackFacts G (closeC₂ C) (closeBracketS₅ s) :=
    closeStackFacts (G := G) (C := closeC₂ C) (s := closeBracketS₅ s) hInv5
      (by show (closeC₂ C).sp ≠ 0; exact hsp)
  have hmark5 : (closeC₂ C).tyMap ((closeC₂ C).sp - 1) = b1 := by
    simpa only [closeC₂] using hmark
  have hreadT : readBytes (closeBracketS₅ s).mem
      ((closeC₂ C).stage.ctype +
        (BitVec.ofNat 32 (closeC₂ C).sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b1] := by
    rw [← hmark5]; exact f.tyread
  have L6 : WalkLink (stage2Calls stage2SubCalls) G (closeC₂ C) (closeBracketS₅ s)
      (closeC₃ C)
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)) :=
    mlStep₆c (calls := stage2Calls stage2SubCalls) G (closeC₂ C) (closeBracketS₅ s) hInv5
      rfl f.sp h8₅ f.ct f.q63 hreadT (closeAgree_93 hb1)
  have hidx : lookupName
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)).env "%idxprom65.i" =
      some (.int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) :=
    closeSel_idx _ _ _ _ _ _
  have hcmp : lookupName
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)).env "%cmp61.i" =
      some (.int 1 (walkSelBit (BitVec.ofNat 8 93))) :=
    closeSel_cmp _ _ _ _ _ _
  have hreadS : readBytes
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)).mem
      (C.stage.cst + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b2] := by
    have h := f.stread
    rw [hstate] at h
    exact h
  obtain ⟨s₇, L7, hs₇⟩ := walkIfEnd74_at (calls := stage2Calls stage2SubCalls) G
    (closeC₃ C) (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93)
      b1 (stackSelBit (BitVec.ofNat 8 93) b1)) L6.inv' rfl f.cs hidx f.q63 hreadS hcmp
  have hbit₇ : walkSelBit (BitVec.ofNat 8 93) = (0 : BitVec 1) := closeSelBit_93
  have hpc₇ : (if walkSelBit (BitVec.ofNat 8 93) = (1 : BitVec 1) then "cond.true.i"
      else "cond.end.i") = "cond.end.i" := by rw [hbit₇]; rfl
  have hs₇' : s₇ = ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0 := by
    rw [hs₇, hbit₇]
  have L7' : WalkLink (stage2Calls stage2SubCalls) G (closeC₃ C)
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)) (closeC₄b C)
      (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
        (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0) := by
    rw [hpc₇] at L7
    rw [hs₇'] at L7
    exact L7
  have h15 : lookupName (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0).env "%15" =
      some (.int 8 (BitVec.ofNat 8 b2.toNat)) :=
    lookupName_of_evalOperand_reg
      (closeByte_val (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
        (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0)
  have hult : evalICmp .ult (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 2) = 0 :=
    closeUlt_zero (UInt8.toNat_lt b2) (by decide) hb2
  have hv' : lookupName (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0).env "%idxprom.i" =
      some (.int 64 (BitVec.ofNat 64 j)) := by
    rw [closeByte_other (s := stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
        (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1))
      C.stage.cst ((BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) b2 0
      "%idxprom.i" (by decide)]
    rw [closeSel_other (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
      (stackSelBit (BitVec.ofNat 8 93) b1) "%idxprom.i" (by decide)]
    rw [closeBracketS₅_other s "%idxprom.i" (by decide)]
    exact lookupName_of_evalOperand_reg hv
  have he' : lookupName (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0).env "%e" =
      some (.ptr C.stage.e) :=
    L7'.inv'.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs])
  have htail := closeStateTailSeg (calls := stage2Calls stage2SubCalls) G (closeC₄b C)
    (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93)
      b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0)
    L7'.inv' rfl h15 hult hv' he' hj hj64
  have hseg9 : WalkSegment (stage2Calls stage2SubCalls) G C s (closeCR C j)
      (clS₉ C j (clS₈ (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
        (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0))) 9 :=
    (hseg5.trans (Seg.measure (Seg.tail L6 (Seg.tail L7' (Seg.nil L7'.inv'))))).trans htail
  have hword : readBytes (clS₉ C j (clS₈ (ifEnd74Out (stackSelOut (closeBracketS₅ s)
      C.sp C.stage.ctype (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1))
      C.stage.cst (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0))).mem
      (C.stage.e + 8) 8 = some (wordBytes 8 j) :=
    refuseSegment_word_of_store (m := (clS₈ (ifEnd74Out (stackSelOut (closeBracketS₅ s)
      C.sp C.stage.ctype (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1))
      C.stage.cst (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0)).mem)
      (e := C.stage.e) (v := j)
  exact closeRefusePkg G C s hseg9 hword hj hklt (by omega)

/-- **The closing brace's state-stack refusal.**  The marker agrees but the state
byte is neither `0` nor `3`, so the leaf refuses at `cleanup104.i` — eleven links. -/
theorem closeStateBrace_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)))
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 125)
    (hsp : C.sp ≠ 0)
    {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2)
    (hb1 : b1.toNat = 1) (hb0 : b2.toNat ≠ 0) (hb3 : b2.toNat ≠ 3)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkRefuseAt (stage2Calls stage2SubCalls) G C s := by
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have hseg5 := closePrefixBraceSeg (calls := stage2Calls stage2SubCalls) G C s hInv hhead
    hbe hsp
  have hInv5 := hseg5.inv'
  have hk5 : (closeC₂ C).k = C.k := rfl
  have h8₅ : lookupName (closeBraceS₅ s).env "%8" =
      some (.int 8 (BitVec.ofNat 8 125)) := by
    have h := hInv5.iter.reg8
    rw [hk5, hbe] at h
    exact h
  have f : CloseStackFacts G (closeC₂ C) (closeBraceS₅ s) :=
    closeStackFacts (G := G) (C := closeC₂ C) (s := closeBraceS₅ s) hInv5
      (by show (closeC₂ C).sp ≠ 0; exact hsp)
  have hmark5 : (closeC₂ C).tyMap ((closeC₂ C).sp - 1) = b1 := by
    simpa only [closeC₂] using hmark
  have hreadT : readBytes (closeBraceS₅ s).mem
      ((closeC₂ C).stage.ctype +
        (BitVec.ofNat 32 (closeC₂ C).sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b1] := by
    rw [← hmark5]; exact f.tyread
  have L6 : WalkLink (stage2Calls stage2SubCalls) G (closeC₂ C) (closeBraceS₅ s)
      (closeC₃ C)
      (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)) :=
    mlStep₆c (calls := stage2Calls stage2SubCalls) G (closeC₂ C) (closeBraceS₅ s) hInv5
      rfl f.sp h8₅ f.ct f.q63 hreadT (closeAgree_125 hb1)
  have hidx : lookupName
      (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)).env "%idxprom65.i" =
      some (.int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) :=
    closeSel_idx _ _ _ _ _ _
  have hcmp : lookupName
      (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)).env "%cmp61.i" =
      some (.int 1 (walkSelBit (BitVec.ofNat 8 125))) :=
    closeSel_cmp _ _ _ _ _ _
  have hreadS : readBytes
      (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)).mem
      (C.stage.cst + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b2] := by
    have h := f.stread
    rw [hstate] at h
    exact h
  obtain ⟨s₇, L7, hs₇⟩ := walkIfEnd74_at (calls := stage2Calls stage2SubCalls) G
    (closeC₃ C) (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125)
      b1 (stackSelBit (BitVec.ofNat 8 125) b1)) L6.inv' rfl f.cs hidx f.q63 hreadS hcmp
  have hbit₇ : walkSelBit (BitVec.ofNat 8 125) = (1 : BitVec 1) := closeSelBit_125
  have hpc₇ : (if walkSelBit (BitVec.ofNat 8 125) = (1 : BitVec 1) then "cond.true.i"
      else "cond.end.i") = "cond.true.i" := by rw [hbit₇]; rfl
  have hs₇' : s₇ = ifEnd74Out (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 1 := by
    rw [hs₇, hbit₇]
  have L7' : WalkLink (stage2Calls stage2SubCalls) G (closeC₃ C)
      (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1)) (closeC₄c C)
      (ifEnd74Out (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
        (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1)) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 1) := by
    rw [hpc₇] at L7
    rw [hs₇'] at L7
    exact L7
  have h15₇ : evalOperand (ifEnd74Out (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 1) (.reg "%15") =
      some (.int 8 (BitVec.ofNat 8 b2.toNat)) :=
    closeByte_val _ _ _ b2 1
  have L8 : WalkLink (stage2Calls stage2SubCalls) G (closeC₄c C)
      (ifEnd74Out (stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
        (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1)) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 1)
      (closeC₅c C) (closeJump _ "NodeBlock27") :=
    closeCondTrue_at (calls := stage2Calls stage2SubCalls) G (closeC₄c C) _ L7'.inv' rfl
  have h15₈ : evalOperand (closeJump (ifEnd74Out (stackSelOut (closeBraceS₅ s) C.sp
      C.stage.ctype (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1))
      C.stage.cst (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 1)
      "NodeBlock27") (.reg "%15") = some (.int 8 (BitVec.ofNat 8 b2.toNat)) := h15₇
  obtain ⟨s₉, L9, hs₉⟩ := WalkLink.NodeBlock27_at (calls := stage2Calls stage2SubCalls) G
    (closeC₅c C) _ L8.inv' rfl (x1 := BitVec.ofNat 8 b2.toNat) h15₈
  by_cases hslt : evalICmp .slt (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1
  · -- `LeafBlock23`, and the state byte is not `0`
    have heq0 : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 0) = 0 :=
      closeEq_zero (UInt8.toNat_lt b2) (by decide) hb0
    have hpc₉ : (if evalICmp .slt (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 then
        "LeafBlock23" else "LeafBlock25") = "LeafBlock23" := by rw [hslt]; rfl
    have hc₉ : ({ closeC₅c C with block := (if evalICmp .slt
        (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 then
        "LeafBlock23" else "LeafBlock25") } : WalkCarry G) = closeC₆a C := by
      rw [hpc₉]
    rw [hc₉] at L9
    have h15₉ : evalOperand s₉ (.reg "%15") = some (.int 8 (BitVec.ofNat 8 b2.toNat)) := by
      rw [hs₉]
      simpa only [evalOperand, State.bind,
        lookupName_cons_ne (k := "%Pivot28") (n := "%15") _ _ (by decide)] using h15₈
    obtain ⟨s₁₀, L10, hs₁₀⟩ := WalkLink.LeafBlock23_at (calls := stage2Calls stage2SubCalls) G
      (closeC₆a C) s₉ L9.inv' rfl (x1 := BitVec.ofNat 8 b2.toNat) h15₉
    have hbit₁₀ : (if evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 0) = 1 then
        "if.then109.i" else "cleanup104.i") = "cleanup104.i" := by rw [heq0]; rfl
    rw [hbit₁₀] at L10
    have hs₁₀' : s₁₀ = closeJump (s₉.bind "%SwitchLeaf24"
        (.int 1 (evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 0))))
        "cleanup104.i" := by
      rw [hs₁₀]; simp only [hbit₁₀]; rfl
    have hv₁₀ : evalOperand s₁₀ (.reg "%idxprom.i") =
        some (.int 64 (BitVec.ofNat 64 j)) := by
      rw [hs₁₀', hs₉]
      simp only [evalOperand, closeJump, State.bind,
        lookupName_cons_ne (k := "%SwitchLeaf24") (n := "%idxprom.i") _ _ (by decide),
        lookupName_cons_ne (k := "%Pivot28") (n := "%idxprom.i") _ _ (by decide)]
      rw [closeByte_other (s := stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
          (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1))
        C.stage.cst ((BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) b2 1
        "%idxprom.i" (by decide)]
      rw [closeSel_other (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1) "%idxprom.i" (by decide)]
      rw [closeBraceS₅_other s "%idxprom.i" (by decide)]
      exact hv
    have he₁₀ : lookupName s₁₀.env "%e" = some (.ptr C.stage.e) := by
      rw [hs₁₀', hs₉]
      simp only [closeJump, State.bind,
        lookupName_cons_ne (k := "%SwitchLeaf24") (n := "%e") _ _ (by decide),
        lookupName_cons_ne (k := "%Pivot28") (n := "%e") _ _ (by decide)]
      rw [closeByte_other (s := stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
          (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1))
        C.stage.cst ((BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) b2 1
        "%e" (by decide)]
      rw [closeSel_other (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1) "%e" (by decide)]
      rw [closeBraceS₅_other s "%e" (by decide)]
      exact he
    have L11 := clStep₉ (calls := stage2Calls stage2SubCalls) G
      { closeC₆a C with block := "cleanup104.i" } s₁₀ L10.inv' rfl hv₁₀ he₁₀ hj hj64
    have hseg11 : WalkSegment (stage2Calls stage2SubCalls) G C s (closeCR C j)
        (clS₉ C j s₁₀) 11 :=
      hseg5.trans (Seg.measure (Seg.tail L6 (Seg.tail L7' (Seg.tail L8 (Seg.tail L9
        (Seg.tail L10 (Seg.tail L11 (Seg.nil L11.inv'))))))))
    exact closeRefusePkg G C s hseg11
      (refuseSegment_word_of_store (m := s₁₀.mem) (e := C.stage.e) (v := j))
      hj hklt (by omega)
  · -- `LeafBlock25`, and the state byte is not `3`
    have hzero : evalICmp .slt (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 0 :=
      bitZeroOfNeOne hslt
    have heq3 : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 0 :=
      closeEq_zero (UInt8.toNat_lt b2) (by decide) hb3
    have hpc₉ : (if evalICmp .slt (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 then
        "LeafBlock23" else "LeafBlock25") = "LeafBlock25" := by rw [hzero]; rfl
    have hc₉ : ({ closeC₅c C with block := (if evalICmp .slt
        (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 then
        "LeafBlock23" else "LeafBlock25") } : WalkCarry G) = closeC₆b C := by
      rw [hpc₉]
    rw [hc₉] at L9
    have h15₉ : evalOperand s₉ (.reg "%15") = some (.int 8 (BitVec.ofNat 8 b2.toNat)) := by
      rw [hs₉]
      simpa only [evalOperand, State.bind,
        lookupName_cons_ne (k := "%Pivot28") (n := "%15") _ _ (by decide)] using h15₈
    obtain ⟨s₁₀, L10, hs₁₀⟩ := WalkLink.LeafBlock25_at (calls := stage2Calls stage2SubCalls) G
      (closeC₆b C) s₉ L9.inv' rfl (x1 := BitVec.ofNat 8 b2.toNat) h15₉
    have hbit₁₀ : (if evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1 then
        "if.then109.i" else "cleanup104.i") = "cleanup104.i" := by rw [heq3]; rfl
    rw [hbit₁₀] at L10
    have hs₁₀' : s₁₀ = closeJump (s₉.bind "%SwitchLeaf26"
        (.int 1 (evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3))))
        "cleanup104.i" := by
      rw [hs₁₀]; simp only [hbit₁₀]; rfl
    have hv₁₀ : evalOperand s₁₀ (.reg "%idxprom.i") =
        some (.int 64 (BitVec.ofNat 64 j)) := by
      rw [hs₁₀', hs₉]
      simp only [evalOperand, closeJump, State.bind,
        lookupName_cons_ne (k := "%SwitchLeaf26") (n := "%idxprom.i") _ _ (by decide),
        lookupName_cons_ne (k := "%Pivot28") (n := "%idxprom.i") _ _ (by decide)]
      rw [closeByte_other (s := stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
          (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1))
        C.stage.cst ((BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) b2 1
        "%idxprom.i" (by decide)]
      rw [closeSel_other (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1) "%idxprom.i" (by decide)]
      rw [closeBraceS₅_other s "%idxprom.i" (by decide)]
      exact hv
    have he₁₀ : lookupName s₁₀.env "%e" = some (.ptr C.stage.e) := by
      rw [hs₁₀', hs₉]
      simp only [closeJump, State.bind,
        lookupName_cons_ne (k := "%SwitchLeaf26") (n := "%e") _ _ (by decide),
        lookupName_cons_ne (k := "%Pivot28") (n := "%e") _ _ (by decide)]
      rw [closeByte_other (s := stackSelOut (closeBraceS₅ s) C.sp C.stage.ctype
          (BitVec.ofNat 8 125) b1 (stackSelBit (BitVec.ofNat 8 125) b1))
        C.stage.cst ((BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) b2 1
        "%e" (by decide)]
      rw [closeSel_other (closeBraceS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 125) b1
        (stackSelBit (BitVec.ofNat 8 125) b1) "%e" (by decide)]
      rw [closeBraceS₅_other s "%e" (by decide)]
      exact he
    have L11 := clStep₉ (calls := stage2Calls stage2SubCalls) G
      { closeC₆b C with block := "cleanup104.i" } s₁₀ L10.inv' rfl hv₁₀ he₁₀ hj hj64
    have hseg11 : WalkSegment (stage2Calls stage2SubCalls) G C s (closeCR C j)
        (clS₉ C j s₁₀) 11 :=
      hseg5.trans (Seg.measure (Seg.tail L6 (Seg.tail L7' (Seg.tail L8 (Seg.tail L9
        (Seg.tail L10 (Seg.tail L11 (Seg.nil L11.inv'))))))))
    exact closeRefusePkg G C s hseg11
      (refuseSegment_word_of_store (m := s₁₀.mem) (e := C.stage.e) (v := j))
      hj hklt (by omega)

/-- **The closing delimiter with a container open.**  Both bytes enter
`if.then53.i`; at a positive depth the nesting check compares the type stack's byte
with the byte's own marker, and the state stack's byte at the same index selects the
merge or the state stack's refusal.  The three sub-routes per byte are the switch's
premise, and the result is the one the arm reaches. -/
theorem closeWithOpen_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {v : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 v))
    (hv : v = BitVec.ofNat 8 93 ∨ v = BitVec.ofNat 8 125)
    (hsp : C.sp ≠ 0)
    {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    {j : Nat} (hvj : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have hbe0 : v = BitVec.ofNat 8 (entryByte G C.k).toNat := by
    have h8' : lookupName s.env "%8" = some (.int 8 v) := lookupName_of_evalOperand_reg h8
    have h := Option.some.inj (h8'.symm.trans hInv.iter.reg8)
    simpa using h
  rcases hv with rfl | rfl
  · -- the closing bracket
    have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 93 := hbe0.symm
    by_cases hb1 : b1.toNat = 2
    · by_cases hb2 : b2.toNat < 2
      · exact closeBracketMerge_at G C s hInv hhead h8 hbe hsp hmark hstate hb1 hb2
          hpreA
      · exact WalkDispatchResult.ofRefuseAt
          (closeStateBracket_at G C s hInv hhead h8 hbe hsp hmark hstate hb1
            (fun hlt => hb2 hlt) hvj he hj hj64)
    · exact WalkDispatchResult.ofRefuseAt
        (closeMarkerBracket_at (calls := stage2Calls stage2SubCalls) G C s hInv hhead hbe
          hsp (by rw [hmark]; exact hb1) hvj he hj hj64 hklt)
  · -- the closing brace
    have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 125 := hbe0.symm
    by_cases hb1 : b1.toNat = 1
    · by_cases hb0 : b2.toNat = 0
      · exact closeBraceMerge_at G C s hInv hhead h8 hbe hsp hmark hstate hb1
          (Or.inl hb0) hpreA
      · by_cases hb3 : b2.toNat = 3
        · exact closeBraceMerge_at G C s hInv hhead h8 hbe hsp hmark hstate hb1
            (Or.inr hb3) hpreA
        · exact WalkDispatchResult.ofRefuseAt
            (closeStateBrace_at G C s hInv hhead h8 hbe hsp hmark hstate hb1 hb0 hb3
              hvj he hj hj64)
    · exact WalkDispatchResult.ofRefuseAt
        (closeMarkerBrace_at (calls := stage2Calls stage2SubCalls) G C s hInv hhead hbe
          hsp (by rw [hmark]; exact hb1) hvj he hj hj64 hklt)

/-- **The opener's product, with the push's two bytes.**  The depth-one head the
opener produces carries `ifEnd24TyByte b` on the type stack and the zero on the state
stack at the index the opener wrote — what a closing delimiter's at-document facts
need. -/
theorem containerOpen_depth_one_stacks {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {b : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 b))
    (hopen : b = BitVec.ofNat 8 91 ∨ b = BitVec.ofNat 8 123)
    (hsp519 : C.sp ≤ 519)
    {rd : BitVec 32}
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hcont : C.k + 1 < G.nep) :
    ∃ (Cd' : WalkCarry G) (sd' : State),
      WalkInv G Cd' sd' ∧ Cd'.block = walkLoopHead ∧ Cd'.sp = C.sp + 1 ∧
        Cd'.k = C.k + 1 ∧ Cd'.tyMap C.sp = ifEnd24TyByte b ∧
        Cd'.stMap C.sp = ifEnd24StByte := by
  have hbe0 : b = BitVec.ofNat 8 (entryByte G C.k).toNat := by
    have h8' : lookupName s.env "%8" = some (.int 8 b) := lookupName_of_evalOperand_reg h8
    have h := Option.some.inj (h8'.symm.trans hInv.iter.reg8)
    simpa using h
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
  have tail : ∀ (Cd : WalkCarry G) (sd : State),
      Cd = openC₉ (openHeadC C) b →
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd 9 →
      evalOperand sd (.reg "%inc33.i") = some (.int 32 (BitVec.ofNat 32 (C.sp + 1))) →
      evalOperand sd (.reg "%inc.i") = some (.int 64 (BitVec.ofNat 64 (C.k + 1))) →
      lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) →
      sd.pre = some "out_reserve.exit.i.i" →
      ∃ (Cd' : WalkCarry G) (sd' : State),
        WalkInv G Cd' sd' ∧ Cd'.block = walkLoopHead ∧ Cd'.sp = C.sp + 1 ∧
          Cd'.k = C.k + 1 ∧ Cd'.tyMap C.sp = ifEnd24TyByte b ∧
          Cd'.stMap C.sp = ifEnd24StByte := by
    intro Cd sd hCd hseg hspv hk2 hnepv hpre
    subst Cd
    have hguard : C.k + 1 < (BitVec.ofNat 64 G.nep).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (openNep_lt G)]
      exact hcont
    obtain ⟨-, hinvB, -⟩ :=
      walkBack_step_at (calls := stage2Calls stage2SubCalls) (G := G)
        (C := openC₉ (openHeadC C) b) (s := sd) hseg.inv' rfl
        (p := "out_reserve.exit.i.i") hpre
        (by decide : phiIncoming "out_reserve.exit.i.i" cleanupSpIncoming =
          some (.reg "%inc33.i"))
        hspv
        (by decide : phiIncoming "out_reserve.exit.i.i" cleanupKIncoming =
          some (.reg "%inc.i"))
        hk2 hnepv hguard
    obtain ⟨s'', hl''⟩ :=
      WalkLink.whileBody (calls := stage2Calls stage2SubCalls) G
        { openC₉ (openHeadC C) b with block := "while.body.i", inner := walkInnerCap G }
        (cleanup478Out sd (C.sp + 1) (C.k + 1)) hinvB rfl rfl
        (cleanup478Out_k (s := sd) (spv := C.sp + 1) (k2 := C.k + 1))
        (cleanup478Out_sp (s := sd) (spv := C.sp + 1) (k2 := C.k + 1))
        (by show C.k < C.k + 1; omega)
        (by show C.k + 1 < G.nep; exact hcont)
        (by show C.sp + 1 ≤ stage2StackExtent
            have h520 : stage2StackExtent = 520 := rfl
            omega)
        (by show C.sp + 1 ≤ (openC₉ (openHeadC C) b).wlen
            show C.sp + 1 ≤ max C.wlen (C.sp + 1)
            exact le_max_right _ _)
    refine ⟨_, s'', hl''.inv', rfl, rfl, rfl, ?_, ?_⟩
    · show (openC₉ (openHeadC C) b).tyMap C.sp = ifEnd24TyByte b
      dsimp only [openC₉, openHeadC]
      rw [if_pos rfl]
    · show (openC₉ (openHeadC C) b).stMap C.sp = ifEnd24StByte
      dsimp only [openC₉, openHeadC]
      rw [if_pos rfl]
  rcases hopen with hb | hb
  · have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 91 :=
      hbe0.symm.trans hb
    have hh := openBracketHead G C s hInv hblock (by rw [← hb]; exact h8) hbe
    have ht := openTailSeg G (openHeadC C) (openBrS₄ s) hh.inv' rfl hbe0 hsp519
      (by rw [openBrS₄_mem]; exact hrd)
      (by rw [openBrS₄_mem, openBrS₄_next]; exact hpreV)
      r hcall hret hklt
    refine tail _ _ rfl (hh.trans ht) ?_ ?_ ?_ rfl
    · simp only [evalOperand]
      exact openS₉_inc33 (openHeadC C) (openBrS₄ s) r rd b
    · simp only [evalOperand]
      rw [openS₉_inc (openHeadC C) (openBrS₄ s) r rd b]
      exact LeanLLVM.evalOperand_reg_of hh.inv'.inc_reg
    · rw [openS₉_nep (openHeadC C) (openBrS₄ s) r rd b]
      exact hh.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
        (by simp [walkStaticRegs])
  · have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 123 :=
      hbe0.symm.trans hb
    have hh := openBraceHead G C s hInv hblock (by rw [← hb]; exact h8) hbe
    have ht := openTailSeg G (openHeadC C) (openBcS₄ s) hh.inv' rfl hbe0 hsp519
      (by rw [openBcS₄_mem]; exact hrd)
      (by rw [openBcS₄_mem, openBcS₄_next]; exact hpreV)
      r hcall hret hklt
    refine tail _ _ rfl (hh.trans ht) ?_ ?_ ?_ rfl
    · simp only [evalOperand]
      exact openS₉_inc33 (openHeadC C) (openBcS₄ s) r rd b
    · simp only [evalOperand]
      rw [openS₉_inc (openHeadC C) (openBcS₄ s) r rd b]
      exact LeanLLVM.evalOperand_reg_of hh.inv'.inc_reg
    · rw [openS₉_nep (openHeadC C) (openBcS₄ s) r rd b]
      exact hh.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
        (by simp [walkStaticRegs])

/-! ### The two refusals the head switch has and no arm reached

Two states the switch sends to a refusal the census had no arm for.  Both are the
delimitation boundary's own, which is why they are here beside `closeWithOpen_at` and
`containerOpen_depth_one_stacks`:

* **`}` at depth zero.**  `LeafBlock15`'s equality is true at `125`, so the run enters
  `if.then53.i` through `NodeBlock17 → LeafBlock15` and the depth test sends it to
  `if.then56.i` — the *same* two blocks the closing bracket's refusal reaches, but not
  through the bracket's pivots: `NodeBlock11`'s `%Pivot12` is `slt %8, 93` and
  `LeafBlock9`'s `%SwitchLeaf10` is `eq %8, 93`, while this route reads `NodeBlock17`'s
  `%Pivot18` (`slt %8, 125`) and `LeafBlock15`'s `%SwitchLeaf16` (`eq %8, 125`).  The
  count is the bracket refusal's — six links — and the offset store is the same one, so
  the word is `refuseSegment_word_of_store`'s at the block the run actually took.
* **A container opener at depth `520`.**  `if.end.i`'s `ugt %sp.i.0248, 519` is taken at
  the stack's staged extent, so the run leaves the opener route for `if.then21.i`'s
  offset store and the copy.  `WalkInv.depth_cap` bounds the depth by `520` and nothing
  below it, so `C.sp = 520` is the arm's premise rather than a consequence; the three
  blocks are `if.then.i`'s call, `if.end.i`'s taken bite and `if.then21.i`'s store.

Both are refusals of the delimitation, and both carry the copy's own word: the store is
at `%e + 8` and reads back at it, exactly as the other three refusal stores do. -/

/-- **`if.end.i`'s guard is taken at `520`.**  The test is `ugt %sp.i.0248, 519`, and a
depth at the stacks' staged extent is the one value it admits. -/
theorem openUgt519_one {sp : Nat} (h : sp = 520) :
    evalICmp .ugt (BitVec.ofNat 32 sp) (BitVec.ofNat 32 519) = 1 := by
  subst h
  decide

/-- `if.end.i`'s target on the cap: the same bite as `openS₆From`, taken. -/
abbrev openCapS₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s₅ : State) : State :=
  { s₅.bind "%cmp19.i"
      (.int 1 (evalICmp .ugt (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 519))) with
    pc := "if.then21.i", pre := some s₅.pc }

/-- `if.then21.i`'s target: the refusal's offset store at `%e + 8`, at the copy. -/
def openCapS₇ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (j : Nat) (s₆ : State) : State :=
  { { s₆ with
      env := ("%off1.i.i38", .ptr (C.stage.e + 8)) :: s₆.env
      mem := writeBytes s₆.mem (C.stage.e + 8) (wordBytes 8 j) } with
    pc := "if.then", pre := some s₆.pc }

/-- **`if.then21.i`'s link, at its named target.**  `WalkLink.if_then21_i` is the store's
instance; the state is `openCapS₇`'s, which is the same function read at the block's own
cells. -/
theorem openCapStoreLink {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then21.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkLink calls G C s { C with block := "if.then", eoff := j, refusal := true }
      (openCapS₇ C j s) := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then21_i G C s hInv hblock hv he hj hj64
  have hstep : step calls stage2Body s =
      .jump (openCapS₇ C j s) :=
    walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then21_i)
      (off := "%off1.i.i38") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e)
      (j := j) (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then21_i_find) rfl rfl
      he (by exact lookupName_of_evalOperand_reg hv) hj64
  have hs' : s' = openCapS₇ C j s := Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)
  rw [hs'] at hlink
  exact hlink

/-- **A name the open bracket's pivots do not bind reads through them.** -/
theorem openBrS₄_other (s : State) (n : String)
    (h1 : "%Pivot22" ≠ n) (h2 : "%Pivot20" ≠ n) (h3 : "%Pivot12" ≠ n)
    (h4 : "%SwitchLeaf8" ≠ n) :
    lookupName (openBrS₄ s).env n = lookupName s.env n := by
  simp only [openBrS₄, openBrS₃, openBrS₂, openBrS₁, State.bind,
    lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2, lookupName_cons_ne _ _ h3,
    lookupName_cons_ne _ _ h4]

/-- **A name the open brace's pivots do not bind reads through them.** -/
theorem openBcS₄_other (s : State) (n : String)
    (h1 : "%Pivot22" ≠ n) (h2 : "%Pivot20" ≠ n) (h3 : "%Pivot18" ≠ n)
    (h4 : "%SwitchLeaf14" ≠ n) :
    lookupName (openBcS₄ s).env n = lookupName s.env n := by
  simp only [openBcS₄, openBcS₃, openBcS₂, openBcS₁, State.bind,
    lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2, lookupName_cons_ne _ _ h3,
    lookupName_cons_ne _ _ h4]

/-- **A name `if.then.i` does not bind reads through it**: the call's three cells are the
block's own. -/
theorem openS₅_other (s : State) (r : CallOutcome) (rd : BitVec 32) (n : String)
    (h1 : "%tobool15.not.i" ≠ n) (h2 : "%call14.i" ≠ n) (h3 : "%9" ≠ n) :
    lookupName (openS₅ s r rd).env n = lookupName s.env n := by
  simp only [openS₅, stateAt, cells, lookupName_cons_ne _ _ h1,
    lookupName_cons_ne _ _ h2, lookupName_cons_ne _ _ h3]

/-- **A name the depth guard does not bind reads through it.** -/
theorem openCapS₆_other {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s₅ : State)
    (n : String) (h : "%cmp19.i" ≠ n) :
    lookupName (openCapS₆ C s₅).env n = lookupName s₅.env n := by
  simp only [State.bind, lookupName_cons_ne _ _ h]

/-- **The cap's three blocks**, at an arbitrary `if.then.i` state: the value-position call
(the answer `1` leaves for `if.end.i`), the `ugt` bite taken at `520`, and the offset
store to the copy.  The word the copy loads is the store's, at the position the store
wrote. -/
theorem openCapTailSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then.i")
    (hsp520 : C.sp = 520)
    {rd : BitVec 32}
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1))
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    ∃ (Cd : WalkCarry G) (sd : State),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd 3 ∧
      Cd.block = "if.then" ∧ Cd.eoff = j ∧ Cd.stage = C.stage ∧
      readBytes sd.mem (C.stage.e + 8) 8 = some (wordBytes 8 j) := by
  -- the call's answer is `1`, so the branch's bit is clear and the edge is `if.end.i`
  have hroot : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)) :=
    hInv.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  have hpc₅ : s.pc = "if.then.i" := by rw [hInv.pc_eq, hblock]
  have hstep₅ : step (stage2Calls stage2SubCalls) stage2Body s = .jump (openS₅ s r rd) :=
    openIfThenI_term C s hpc₅ hroot hrd hInv.depth_reg
      (hInv.ptrs.2.2.2.1) (hInv.ptrs.2.2.2.2.1) hcall hret
  have hx : ∀ r', stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r' →
      r'.ret = .int 32 (BitVec.ofNat 32 1) := by
    intro r' h'
    rw [Option.some.inj (h'.symm.trans hcall)]
    exact hret
  obtain ⟨s₅, hl₅⟩ :=
    WalkLink.if_then_i G C s hInv hblock hroot hrd hpreV hx
  have hbit₅ : (if evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0) = 1 then
      "if.then16.i" else "if.end.i") = "if.end.i" := by
    rw [show evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0) = (0 : BitVec 1) from
      by decide]
    rfl
  rw [hbit₅] at hl₅
  have hs₅ : s₅ = openS₅ s r rd := Ctrl.jump.inj (hl₅.step.symm.trans hstep₅)
  rw [hs₅] at hl₅
  -- the depth guard, taken at `520`
  have hstep₅' : evalOperand (openS₅ s r rd) (.reg "%sp.i.0248") =
      some (.int 32 (BitVec.ofNat 32 C.sp)) := by
    exact LeanLLVM.evalOperand_reg_of hl₅.inv'.depth_reg
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.if_end_i_at (calls := stage2Calls stage2SubCalls) G (openC₅ C) (openS₅ s r rd)
      hl₅.inv' rfl hstep₅'
  have hbit₆ : evalICmp .ugt (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 519) = 1 :=
    openUgt519_one hsp520
  have hb₆ : (if evalICmp .ugt (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 519) = 1 then
      "if.then21.i" else "if.end24.i") = "if.then21.i" := by
    rw [hbit₆]
    exact ite_eq_left rfl
  have hs₆' : s₆ = openCapS₆ C (openS₅ s r rd) := by
    rw [hs₆, hb₆]
  rw [hs₆'] at hl₆
  rw [hb₆] at hl₆
  -- the offset store, at the position the entry carries
  have hv₆ : evalOperand (openCapS₆ C (openS₅ s r rd)) (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 j)) := by
    simp only [evalOperand, openCapS₆_other C (openS₅ s r rd) "%idxprom.i" (by decide),
      openS₅_other s r rd "%idxprom.i" (by decide) (by decide) (by decide)]
    exact hv
  have he₆ : lookupName (openCapS₆ C (openS₅ s r rd)).env "%e" = some (.ptr C.stage.e) := by
    rw [openCapS₆_other C (openS₅ s r rd) "%e" (by decide),
      openS₅_other s r rd "%e" (by decide) (by decide) (by decide)]
    exact he
  have hl₇ : WalkLink (stage2Calls stage2SubCalls) G
      { openC₅ C with block := "if.then21.i" } (openCapS₆ C (openS₅ s r rd))
      { { openC₅ C with block := "if.then21.i" } with
        block := "if.then", eoff := j, refusal := true }
      (openCapS₇ { openC₅ C with block := "if.then21.i" } j (openCapS₆ C (openS₅ s r rd))) :=
    openCapStoreLink (calls := stage2Calls stage2SubCalls) G
      { openC₅ C with block := "if.then21.i" } (openCapS₆ C (openS₅ s r rd)) hl₆.inv' rfl
      hv₆ he₆ hj hj64
  refine ⟨{ { openC₅ C with block := "if.then21.i" } with
      block := "if.then", eoff := j, refusal := true },
    openCapS₇ { openC₅ C with block := "if.then21.i" } j
      (openCapS₆ C (openS₅ s r rd)), ?_, rfl, rfl, rfl, ?_⟩
  · exact Seg.measure (Seg.tail hl₅ (Seg.tail hl₆ (Seg.tail hl₇ (Seg.nil hl₇.inv'))))
  · simpa only [openCapS₇] using
      refuseSegment_word_of_store (m := (openCapS₆ C (openS₅ s r rd)).mem) (e := C.stage.e)
        (v := j)

/-- **A name the answer-`0` branch does not bind reads through it**: the call's three cells
are `if.then.i`'s own, and the refusal's branch binds none of the offset's. -/
theorem openRefS₅_other (s : State) (r : CallOutcome) (rd : BitVec 32) (n : String)
    (h1 : "%tobool15.not.i" ≠ n) (h2 : "%call14.i" ≠ n) (h3 : "%9" ≠ n) :
    lookupName (openRefS₅ s r rd).env n = lookupName s.env n := by
  simp only [openRefS₅, stateAt, cells, lookupName_cons_ne _ _ h1,
    lookupName_cons_ne _ _ h2, lookupName_cons_ne _ _ h3]

/-- **`if.then16.i`'s link, at its named target.**  `WalkLink.if_then16_i_at` is the
store's instance; the state is `openRefS₆`'s, which is the same function read at the
block's own cells. -/
theorem openRefStoreLink {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then16.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkLink calls G C s { C with block := "if.then", eoff := j, refusal := true }
      (openRefS₆ C j s) := by
  obtain ⟨s', hlink, hs'⟩ := WalkLink.if_then16_i_at (calls := calls) G C s hInv hblock
    hv he hj hj64
  rw [hs'] at hlink
  exact hlink

/-- **The answer-`0` refusal's two blocks**, at an arbitrary `if.then.i` state: the
value-position call's zero leaves `if.then.i` for `if.then16.i`, whose offset store reaches
the copy.  The word the copy loads is the store's, at the position the store wrote. -/
theorem openRefTailSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "if.then.i")
    {rd : BitVec 32}
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 0))
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    ∃ (Cd : WalkCarry G) (sd : State),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd 2 ∧
      Cd.block = "if.then" ∧ Cd.eoff = j ∧ Cd.stage = C.stage ∧
      readBytes sd.mem (C.stage.e + 8) 8 = some (wordBytes 8 j) := by
  -- the call's zero sets the branch's bit, so the edge is `if.then16.i`
  have hroot : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)) :=
    hInv.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  have hpc₅ : s.pc = "if.then.i" := by rw [hInv.pc_eq, hblock]
  have hstep₅ : step (stage2Calls stage2SubCalls) stage2Body s = .jump (openRefS₅ s r rd) :=
    openRefIfThenI_term C s hpc₅ hroot hrd hInv.depth_reg
      (hInv.ptrs.2.2.2.1) (hInv.ptrs.2.2.2.2.1) hcall hret
  have hx : ∀ r', stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r' →
      r'.ret = .int 32 (BitVec.ofNat 32 0) := by
    intro r' h'
    rw [Option.some.inj (h'.symm.trans hcall)]
    exact hret
  obtain ⟨s₅, hl₅⟩ :=
    WalkLink.if_then_i G C s hInv hblock hroot hrd hpreV hx
  have hbit₅ : (if evalICmp .eq (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) = 1 then
      "if.then16.i" else "if.end.i") = "if.then16.i" := by
    rw [show evalICmp .eq (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) = (1 : BitVec 1) from
      by decide]
    exact ite_eq_left rfl
  rw [hbit₅] at hl₅
  have hs₅ : s₅ = openRefS₅ s r rd := Ctrl.jump.inj (hl₅.step.symm.trans hstep₅)
  rw [hs₅] at hl₅
  -- the offset store, at the position the entry carries
  have hv₅ : evalOperand (openRefS₅ s r rd) (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 j)) := by
    simp only [evalOperand, openRefS₅_other s r rd "%idxprom.i" (by decide) (by decide)
      (by decide)]
    exact hv
  have he₅ : lookupName (openRefS₅ s r rd).env "%e" = some (.ptr C.stage.e) := by
    rw [openRefS₅_other s r rd "%e" (by decide) (by decide) (by decide)]
    exact he
  have hl₆ : WalkLink (stage2Calls stage2SubCalls) G { openC₅ C with block := "if.then16.i" }
      (openRefS₅ s r rd)
      { { openC₅ C with block := "if.then16.i" } with
        block := "if.then", eoff := j, refusal := true }
      (openRefS₆ { openC₅ C with block := "if.then16.i" } j (openRefS₅ s r rd)) :=
    openRefStoreLink (calls := stage2Calls stage2SubCalls) G
      { openC₅ C with block := "if.then16.i" } (openRefS₅ s r rd) hl₅.inv' rfl
      hv₅ he₅ hj hj64
  refine ⟨{ { openC₅ C with block := "if.then16.i" } with
      block := "if.then", eoff := j, refusal := true },
    openRefS₆ { openC₅ C with block := "if.then16.i" } j (openRefS₅ s r rd),
    ?_, rfl, rfl, rfl, ?_⟩
  · exact Seg.measure (Seg.tail hl₅ (Seg.tail hl₆ (Seg.nil hl₆.inv')))
  · simpa only [openRefS₆] using
      refuseSegment_word_of_store (m := (openRefS₅ s r rd).mem) (e := C.stage.e) (v := j)
/-- **A container opener at depth `520`**: the head's four pivots to `if.then.i`, then the
cap's three blocks to the copy.  Seven links, priced at `7 + 2 ≤ 32`, and the store's word
read at the copy's own load. -/
theorem containerOpenCap_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {b : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 b))
    (hopen : b = BitVec.ofNat 8 91 ∨ b = BitVec.ofNat 8 123)
    (hsp520 : C.sp = 520)
    {rd : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1))
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkRefuseAt (stage2Calls stage2SubCalls) G C s := by
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have h8' : lookupName s.env "%8" = some (.int 8 b) := lookupName_of_evalOperand_reg h8
  have hbe0 : b = BitVec.ofNat 8 (entryByte G C.k).toNat := by
    have h := Option.some.inj (h8'.symm.trans hInv.iter.reg8)
    simpa using h
  rcases hopen with hb | hb
  · have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 91 :=
      hbe0.symm.trans hb
    have hh := openBracketHead G C s hInv hhead (by rw [← hb]; exact h8) hbe
    have hv' : evalOperand (openBrS₄ s) (.reg "%idxprom.i") =
        some (.int 64 (BitVec.ofNat 64 j)) := by
      simp only [evalOperand, openBrS₄_other s "%idxprom.i" (by decide) (by decide)
        (by decide) (by decide)]
      exact hv
    have he' : lookupName (openBrS₄ s).env "%e" = some (.ptr C.stage.e) := by
      rw [openBrS₄_other s "%e" (by decide) (by decide) (by decide) (by decide)]
      exact he
    obtain ⟨Cd, sd, hseg, hblk, heoff, hstage, hword⟩ :=
      openCapTailSeg G (openHeadC C) (openBrS₄ s) hh.inv' rfl
        (by simpa only [openHeadC] using hsp520)
        (by rw [openBrS₄_mem]; exact hread)
        (by rw [openBrS₄_mem, openBrS₄_next]; exact hpreV) r hcall hret hv' he' hj hj64
    refine ⟨Cd, sd, 7, ⟨hh.trans hseg, hblk, ?_⟩, ?_,
      refusePrice_of_le G C (p := 7) (by omega) hklt⟩
    · exact ⟨j, hj, by rw [hstage]; exact hword⟩
    · rw [heoff]
      exact hj
  · have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 123 :=
      hbe0.symm.trans hb
    have hh := openBraceHead G C s hInv hhead (by rw [← hb]; exact h8) hbe
    have hv' : evalOperand (openBcS₄ s) (.reg "%idxprom.i") =
        some (.int 64 (BitVec.ofNat 64 j)) := by
      simp only [evalOperand, openBcS₄_other s "%idxprom.i" (by decide) (by decide)
        (by decide) (by decide)]
      exact hv
    have he' : lookupName (openBcS₄ s).env "%e" = some (.ptr C.stage.e) := by
      rw [openBcS₄_other s "%e" (by decide) (by decide) (by decide) (by decide)]
      exact he
    obtain ⟨Cd, sd, hseg, hblk, heoff, hstage, hword⟩ :=
      openCapTailSeg G (openHeadC C) (openBcS₄ s) hh.inv' rfl
        (by simpa only [openHeadC] using hsp520)
        (by rw [openBcS₄_mem]; exact hread)
        (by rw [openBcS₄_mem, openBcS₄_next]; exact hpreV) r hcall hret hv' he' hj hj64
    refine ⟨Cd, sd, 7, ⟨hh.trans hseg, hblk, ?_⟩, ?_,
      refusePrice_of_le G C (p := 7) (by omega) hklt⟩
    · exact ⟨j, hj, by rw [hstage]; exact hword⟩
    · rw [heoff]
      exact hj

/-- **A container opener whose value-position answer is `0`**: `if.then.i`'s branch is
taken, so the run is the head's four pivots, the call's refusal and `if.then16.i`'s offset
store — six links to the refusal copy, priced at `6 + 2 ≤ 32`.  The answer `0` is the
*state's*, not the byte's: the callee is the block's own call, and its zero is what selects
this arm.  The word the copy loads is the store's, at the position the entry carries. -/
theorem containerOpenRefuse_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {b : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 b))
    (hopen : b = BitVec.ofNat 8 91 ∨ b = BitVec.ofNat 8 123)
    {rd : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 0))
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) :
    WalkRefuseAt (stage2Calls stage2SubCalls) G C s := by
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have h8' : lookupName s.env "%8" = some (.int 8 b) := lookupName_of_evalOperand_reg h8
  have hbe0 : b = BitVec.ofNat 8 (entryByte G C.k).toNat := by
    have h := Option.some.inj (h8'.symm.trans hInv.iter.reg8)
    simpa using h
  rcases hopen with hb | hb
  · have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 91 :=
      hbe0.symm.trans hb
    have hh := openBracketHead G C s hInv hhead (by rw [← hb]; exact h8) hbe
    have hv' : evalOperand (openBrS₄ s) (.reg "%idxprom.i") =
        some (.int 64 (BitVec.ofNat 64 j)) := by
      simp only [evalOperand, openBrS₄_other s "%idxprom.i" (by decide) (by decide)
        (by decide) (by decide)]
      exact hv
    have he' : lookupName (openBrS₄ s).env "%e" = some (.ptr C.stage.e) := by
      rw [openBrS₄_other s "%e" (by decide) (by decide) (by decide) (by decide)]
      exact he
    obtain ⟨Cd, sd, hseg, hblk, heoff, hstage, hword⟩ :=
      openRefTailSeg G (openHeadC C) (openBrS₄ s) hh.inv' rfl
        (by rw [openBrS₄_mem]; exact hread)
        (by rw [openBrS₄_mem, openBrS₄_next]; exact hpreV) r hcall hret hv' he' hj hj64
    refine ⟨Cd, sd, 6, ⟨hh.trans hseg, hblk, ?_⟩, ?_,
      refusePrice_of_le G C (p := 6) (by omega) hklt⟩
    · exact ⟨j, hj, by rw [hstage]; exact hword⟩
    · rw [heoff]
      exact hj
  · have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 123 :=
      hbe0.symm.trans hb
    have hh := openBraceHead G C s hInv hhead (by rw [← hb]; exact h8) hbe
    have hv' : evalOperand (openBcS₄ s) (.reg "%idxprom.i") =
        some (.int 64 (BitVec.ofNat 64 j)) := by
      simp only [evalOperand, openBcS₄_other s "%idxprom.i" (by decide) (by decide)
        (by decide) (by decide)]
      exact hv
    have he' : lookupName (openBcS₄ s).env "%e" = some (.ptr C.stage.e) := by
      rw [openBcS₄_other s "%e" (by decide) (by decide) (by decide) (by decide)]
      exact he
    obtain ⟨Cd, sd, hseg, hblk, heoff, hstage, hword⟩ :=
      openRefTailSeg G (openHeadC C) (openBcS₄ s) hh.inv' rfl
        (by rw [openBcS₄_mem]; exact hread)
        (by rw [openBcS₄_mem, openBcS₄_next]; exact hpreV) r hcall hret hv' he' hj hj64
    refine ⟨Cd, sd, 6, ⟨hh.trans hseg, hblk, ?_⟩, ?_,
      refusePrice_of_le G C (p := 6) (by omega) hklt⟩
    · exact ⟨j, hj, by rw [hstage]; exact hword⟩
    · rw [heoff]
      exact hj

/-- **`}` at depth zero with a positive count**: the head's four pivots reach
`if.then53.i` through `NodeBlock17` and `LeafBlock15`, and the depth test's true arm
stores the entry's position at `%e + 8` before the copy.  Six links, the closing
bracket's count at different pivots. -/
theorem closeBraceZero_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)))
    (hsp : C.sp = 0)
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) (hk : C.k < G.nep) :
    WalkRefuseAt (stage2Calls stage2SubCalls) G C s := by
  -- the byte, at each pivot's own state
  have h8₁ : evalOperand (closeBcS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 125)) := by
    simpa only [closeBcS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₂ : evalOperand (closeBcS₂ (closeBcS₁ s)) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 125)) := by
    simpa only [closeBcS₂, closeBcS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₃ : evalOperand (closeBcS₃ (closeBcS₂ (closeBcS₁ s))) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 125)) := by
    simpa only [closeBcS₃, closeBcS₂, closeBcS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot18") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  -- the position and the refusal record, at the depth test's own source
  have hv₅ : evalOperand (refuseS₅ (closeBcS₄ (closeBcS₃ (closeBcS₂ (closeBcS₁ s)))))
      (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)) := by
    simpa only [refuseS₅, closeBcS₄, closeBcS₃, closeBcS₂, closeBcS₁, evalOperand,
      State.bind,
      lookupName_cons_ne (k := "%cmp54.i") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf16") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot18") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%idxprom.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%idxprom.i") _ _ (by decide)] using hv
  have he₅ : lookupName
      (refuseS₅ (closeBcS₄ (closeBcS₃ (closeBcS₂ (closeBcS₁ s))))).env "%e" =
      some (.ptr C.stage.e) := by
    simpa only [refuseS₅, closeBcS₄, closeBcS₃, closeBcS₂, closeBcS₁, State.bind,
      lookupName_cons_ne (k := "%cmp54.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf16") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot18") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%e") _ _ (by decide)] using he
  -- the six links, each at the state the previous one names
  have L₁ : WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := "NodeBlock19" } (closeBcS₁ s) :=
    closeBcStep₁ G C s hInv hhead h8
  have L₂ : WalkLink (stage2Calls stage2SubCalls) G { C with block := "NodeBlock19" }
      (closeBcS₁ s) { C with block := "NodeBlock17" } (closeBcS₂ (closeBcS₁ s)) :=
    closeBcStep₂ G { C with block := "NodeBlock19" } (closeBcS₁ s) L₁.inv' rfl h8₁
  have L₃ : WalkLink (stage2Calls stage2SubCalls) G { C with block := "NodeBlock17" }
      (closeBcS₂ (closeBcS₁ s)) { C with block := "LeafBlock15" }
      (closeBcS₃ (closeBcS₂ (closeBcS₁ s))) :=
    closeBcStep₃ G { C with block := "NodeBlock17" } (closeBcS₂ (closeBcS₁ s)) L₂.inv' rfl h8₂
  have L₄ : WalkLink (stage2Calls stage2SubCalls) G { C with block := "LeafBlock15" }
      (closeBcS₃ (closeBcS₂ (closeBcS₁ s))) (closeC₁ C)
      (closeBcS₄ (closeBcS₃ (closeBcS₂ (closeBcS₁ s)))) :=
    closeBcStep₄ G { C with block := "LeafBlock15" }
      (closeBcS₃ (closeBcS₂ (closeBcS₁ s))) L₃.inv' rfl h8₃
  have L₅ : WalkLink (stage2Calls stage2SubCalls) G (closeC₁ C)
      (closeBcS₄ (closeBcS₃ (closeBcS₂ (closeBcS₁ s))))
      { closeC₁ C with block := "if.then56.i" }
      (refuseS₅ (closeBcS₄ (closeBcS₃ (closeBcS₂ (closeBcS₁ s))))) :=
    refuseStep₅ G (closeC₁ C)
      (closeBcS₄ (closeBcS₃ (closeBcS₂ (closeBcS₁ s)))) L₄.inv' rfl hsp
  have L₆ : WalkLink (stage2Calls stage2SubCalls) G { closeC₁ C with block := "if.then56.i" }
      (refuseS₅ (closeBcS₄ (closeBcS₃ (closeBcS₂ (closeBcS₁ s)))))
      (closeCR C j) (refuseS₆ C j
        (refuseS₅ (closeBcS₄ (closeBcS₃ (closeBcS₂ (closeBcS₁ s)))))) :=
    refuseStep₆ G { closeC₁ C with block := "if.then56.i" }
      (refuseS₅ (closeBcS₄ (closeBcS₃ (closeBcS₂ (closeBcS₁ s))))) L₅.inv' rfl hv₅ he₅ hj hj64
  have hseg : WalkSegment (stage2Calls stage2SubCalls) G C s (closeCR C j)
      (refuseS₆ C j (refuseS₅ (closeBcS₄ (closeBcS₃ (closeBcS₂ (closeBcS₁ s)))))) 6 :=
    Seg.measure (Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄
      (Seg.tail L₅ (Seg.tail L₆ (Seg.nil L₆.inv')))))))
  exact closeRefusePkg G C s hseg
    (by
      simpa only [refuseS₆] using
        refuseSegment_word_of_store (m := (refuseS₅ (closeBcS₄ (closeBcS₃ (closeBcS₂
          (closeBcS₁ s))))).mem) (e := C.stage.e) (v := j))
    hj hk (by omega)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.closeWithOpen_at
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_depth_one_stacks
#print axioms LeanLLVM.Refinement.WalkScope.openCapTailSeg
#print axioms LeanLLVM.Refinement.WalkScope.openCapStoreLink
#print axioms LeanLLVM.Refinement.WalkScope.containerOpenCap_at
#print axioms LeanLLVM.Refinement.WalkScope.openRefS₅_other
#print axioms LeanLLVM.Refinement.WalkScope.openRefStoreLink
#print axioms LeanLLVM.Refinement.WalkScope.openRefTailSeg
#print axioms LeanLLVM.Refinement.WalkScope.containerOpenRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.closeBraceZero_at

end WalkScope
end LeanLLVM.Refinement
