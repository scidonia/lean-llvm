/-
The last entry's terminal dispatch: one arm per control-flow arm of the head's switch.

## The census, from the pinned IR

`NodeBlock21` opens a comparison tree on the entry's first byte `%8`; the leaves send the
walk to six places, and each is a control-flow arm the dispatch must cover:

| arm | tests | block |
|---|---|---|
| string opener | `%8 = 34` | `sw.bb202.i` |
| comma | `44 ≤ %8 < 58`, `%8 = 44` | `if.then127.i` |
| colon | `44 ≤ %8 < 58`, `%8 = 58` | `if.then173.i` |
| open bracket, open brace | `91 ≤ %8 < 123`, `%8 = 91` / `123 ≤ %8 ≤ 124`, `%8 = 123` | `if.then.i` |
| close bracket, close brace | `91 ≤ %8 ≤ 122`, `%8 = 93` / `125 ≤ %8`, `%8 = 125` | `if.then53.i` |
| everything else | every leaf's equality test clear | `sw.default.i` |

`HeadArm` is that census as a value, and `HeadArm.complete` says every byte has one: the
classification is exhaustive *by theorem*, and no arm borrows another's class.

## The arms the layer proves, and the arm it preserves

`LastEntryArm` is the dispatch's evidence, one constructor per arm class, and `.dispatch`
turns it into the actual `WalkDispatchResult`:

* `.scalar` — `sw.default.i`'s arm with the tag test's true arm (a digit or `-`, the
  plain-value path): `scalarMerge_at`'s eleven links, its three tail links and the merge.
  This is the arm that covers the one-byte document `0`, and it is the one the old
  universal residue excluded.
* `.highByte` — the same default arm through `NodeBlock19 → NodeBlock17 → LeafBlock15`,
  i.e. the bytes 126 and 127 and the class-C span's `'t'`-and-above route: the preserved
  long default-path proof, `hlastFacts_of_staging` → `WalkDispatchResult.ofHlastMerge`.
  Its byte-class restriction is stated here and nowhere else; it is one arm, not the
  last entry's shape.
* `.stringOpener` — `sw.bb202.i` with no entry left: a bare opener is refused
  (`quoteRefuse_at`'s five links).
* `.closingZero` — `if.then53.i` at depth zero: `]` with nothing open is refused
  (`bracketRefuse_at`'s six links).
* `.commaZero`, `.colonZero` — the comma's and the colon's depth-zero refusal:
  `if.then127.i → if.then130.i` and `if.then173.i → if.then176.i` store the entry's
  position and reach the copy (`commaRefuse_at`'s and `colonRefuse_at`'s six links).
  These are the arms the documents `,` and `:` take.
* `.commaAboveZero` — the comma with an entry left and a container open: the container
  pair's four sub-routes (`commaBraceMerge_at`, `commaBraceRefuse_at`,
  `commaBracketMerge_at`, `commaBracketRefuse_at`), eight links each.  The type stack's
  byte at `%sp - 1` selects the brace route or the bracket one, and the state stack's
  byte at the same index selects the merge or the refusal.
* `.colonAboveZero` — the colon with an entry left and a container open: the marker's
  three sub-routes, the brace pair at eight links (`colonBraceMerge_at`,
  `colonBraceRefuse_at`) and the marker's own refusal at seven (`colonMarkerRefuse_at`).
  A brace marker reads the state stack's byte (`1` merges, anything else refuses); any
  other marker refuses on its own byte.
* `.containerOpen` — `[` and `{`, both of which enter `if.then.i`: the four head links
  (`NodeBlock21 → NodeBlock19 → NodeBlock11 → LeafBlock7` at `91`, `NodeBlock21 →
  NodeBlock19 → NodeBlock17 → LeafBlock13` at `123`) and the tail's five — the
  value-position call, `if.end.i`'s depth guard, the push, the event reserve and the tag
  (`containerOpenMerge_at`, nine links).  The head's target states are the operands'
  literals, the tail's are `openS₅`…`openS₉`, and the block's own `let`-bound states are
  named by the three `step` theorems, so the composition is a chain of named states.
* `.closeWithOpen` — `]` and `}` with a container open: both enter `if.then53.i`, and at a
  positive depth the nesting check compares the type stack's byte with the byte's own
  marker.  Agreement reads the state stack's byte at the same index: `]` merges at `0`
  and `1` (eleven links, `closeBracketMerge_at`), `}` at `0` and `3` (thirteen links,
  `closeBraceMerge_at`); a marker disagreement is `mismatchedRefuse_at`'s refusal (seven
  links, `closeMarkerBracket_at` / `closeMarkerBrace_at`), and a state byte outside the
  merge's set is the state stack's refusal (nine and eleven links,
  `closeStateBracket_at` / `closeStateBrace_at`).  `closeWithOpen_at` is the four
  sub-routes under the region's depth and byte premises.
* `.letters` — the default arm's letter and high-byte route on the **scan-free** class:
  the bytes below `110` in the signed order whose tag test is clear, through
  `lettersSpan`'s four links below `if.else387.i` (`NodeBlock62`, `LeafBlock54`,
  `if.else405.i`, `if.then413.i`), with the head's chain to the seam (eleven links: the
  four pivots, `sw.default.i`'s *failing* count test, the bound, the whitespace check and
  the seam) and the tail's three calls on their empty arm — `11 + 4 + 3 + 1 = 19`,
  `lettersCleanupMerge_at`.  On the no-run class the seam's `%ee.1.i` is the entry's end,
  so the copy call's test is `ult v v` and no scan is entered; the run class's scan is
  `.run`'s, which is the continuing level's (see below).
* `.fLetter` — the byte `102` (`'f'`) on the scan-free class: the letters span's sibling,
  `LeafBlock54`'s *true* arm at `if.then397.i` (kind `9`), composed by `fSpan` and
  `fCleanupMerge_at` — nineteen links at the last entry, no byte term.
* `.classC` — the class-C span's leaves on the scan-free class, the bytes `110 … 125`:
  `110` via `LeafBlock56`'s true arm (`if.then403.i`, kind `10`), `111 … 115` via its else
  arm, `116` from `LeafBlock58` itself (kind `8`) and `117 … 125` via its else arm.  The
  span is the byte's own `Seg` at `nS ≤ 5` (`c56TrueSpan`, `c56ElseSpan`, `c58TrueSpan`,
  `c58ElseSpan`) and `classCMerge_at` composes the tail and the merge — `11 + nS + 4 ≤ 20`.
* `.supplied` — **the last entry's run class, with its price obstruction.**  The byte
  before the entry's end is whitespace, so the token's own scan traverses `[k, v)`; at the
  last entry `v = %4` is the document's length and the merge's byte credit is
  `entryPos G G.nep - entryPos G C.k = 0`, so the 32-link allowance has to carry the run's
  visits and the scan's out of five links.  The class is left to the caller rather than
  bounded; its constructor's docstring states the arithmetic.

  The field is that arm's own counted segment to the endpoint it reaches, with the
  endpoint's facts — *not* a bundle about the last entry, and no class premise on any
  other arm.  **No other class remains here:** the letters route is `LastEntryArm.letters`
  at the scan-free class, the `'f'` leaf's is `.fLetter`, the class-C leaves' is
  `.classC`, and `HcontArm.letters`/`.fLetter`/`.classC`/`.run` are the continuing twins.

Every constructor's endpoint is either the merge or the refusal copy, and every one
carries its count; the price is the dispatch's own (`WalkDispatchResult`'s), so
`WalkLoopEnd` no longer asks for a residue whose class conditions are the high bytes'.

## Why the classification is separate from the guard

Being the last entry says the entry stream is exhausted (`%inc.i = %nep`), which is what
`sw.default.i`'s count test and `cond.end349.i`'s `phi` read.  It says nothing about
which character the entry starts with: that is `%8`, and `HeadArm` classifies it.  The two
questions are answered by different facts, and this module keeps them apart.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalar
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpeners
import LeanLLVM.Refinement.JsonStage2WalkDispatchThreeOfRun
import LeanLLVM.Refinement.JsonStage2WalkDispatchCommaArms
import LeanLLVM.Refinement.JsonStage2WalkDispatchColonArms
import LeanLLVM.Refinement.JsonStage2WalkDispatchBase
import LeanLLVM.Refinement.JsonStage2WalkDispatchClosers
import LeanLLVM.Refinement.JsonStage2WalkDispatchLetters
import LeanLLVM.Refinement.JsonStage2WalkDispatchFLetter
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassC

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The head switch's census -/

/-- **A marker byte whose brace bit is set is the brace's own marker.**  The brace bit
is the equality test on the byte, so a set bit is `b1 = 1` and the type-stack read is the
literal the brace routes take. -/
theorem uint8_eq_one_of_colonBit {b : UInt8} (h : colonBit b = 1) : b = 1 := by
  have hb : BitVec.ofNat 8 b.toNat = BitVec.ofNat 8 1 :=
    (evalICmp_eq_one_iff _ _).1 h
  refine (UInt8.toNat_inj (a := b) (b := 1)).1 ?_
  have := congrArg BitVec.toNat hb
  simpa using this

/-- **The head switch's arms**, as the pinned IR emits them: one constructor per leaf the
comparison tree reaches, with the tests that select it.  `HeadArm.complete` says every
byte has one. -/
inductive HeadArm (x : BitVec 8) : Prop
  /-- `%8 = 34`: the string opener, `LeafBlock → sw.bb202.i`. -/
  | stringOpener (h : evalICmp .eq x (BitVec.ofNat 8 34) = 1)
  /-- `44 ≤ %8 < 58` and `%8 = 44`: the comma, `NodeBlock5 → NodeBlock → LeafBlock1`. -/
  | comma (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
      (h : evalICmp .eq x (BitVec.ofNat 8 44) = 1)
  /-- `44 ≤ %8 < 58` and `%8 = 58`: the colon, `LeafBlock3`. -/
  | colon (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
      (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 0)
      (h : evalICmp .eq x (BitVec.ofNat 8 58) = 1)
  /-- `91 ≤ %8 < 123` and `%8 = 91`: the open bracket, `LeafBlock7 → if.then.i`. -/
  | openBracket (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
      (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1)
      (h : evalICmp .eq x (BitVec.ofNat 8 91) = 1)
  /-- `91 ≤ %8 ≤ 122` and `%8 = 93`: the close bracket, `LeafBlock9 → if.then53.i`. -/
  | closeBracket (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
      (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 0)
      (h : evalICmp .eq x (BitVec.ofNat 8 93) = 1)
  /-- `123 ≤ %8 ≤ 124` and `%8 = 123`: the open brace, `LeafBlock13 → if.then.i`. -/
  | openBrace (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
      (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1)
      (h : evalICmp .eq x (BitVec.ofNat 8 123) = 1)
  /-- `%8 = 125`: the close brace, `LeafBlock15 → if.then53.i`. -/
  | closeBrace (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
      (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
      (h : evalICmp .eq x (BitVec.ofNat 8 125) = 1)
  /-- Every leaf's equality test clear: `sw.default.i`, with the sub-route's pivots. -/
  | defaultValue (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
      (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
      (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
      (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
  | defaultValueLow (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
      (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
      (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0)
  | defaultValueMid (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
      (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
      (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 0)
      (hne58 : evalICmp .eq x (BitVec.ofNat 8 58) = 0)
  | defaultValueBracket (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
      (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1)
      (hne91 : evalICmp .eq x (BitVec.ofNat 8 91) = 0)
  | defaultValueBracketHigh (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
      (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 0)
      (hne93 : evalICmp .eq x (BitVec.ofNat 8 93) = 0)
  | defaultValueBrace (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
      (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1)
      (hne123 : evalICmp .eq x (BitVec.ofNat 8 123) = 0)
  | defaultValueHigh (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
      (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
      (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
      (hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0)

/-- **Every byte has an arm.**  The comparison tree's tests are each one bit, so the
split below is exhaustive; the zero branches are `bitZeroOfNeOne`'s. -/
theorem HeadArm.complete (x : BitVec 8) : HeadArm x := by
  by_cases h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1
  · -- the low half: `NodeBlock5`
    by_cases h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1
    · -- below 44: `LeafBlock`
      by_cases h34 : evalICmp .eq x (BitVec.ofNat 8 34) = 1
      · exact .stringOpener h34
      · exact .defaultValueLow h91 h44 (bitZeroOfNeOne h34)
    · have h44' : evalICmp .slt x (BitVec.ofNat 8 44) = 0 := bitZeroOfNeOne h44
      by_cases h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1
      · -- `44 ≤ %8 < 58`: `LeafBlock1`
        by_cases h44e : evalICmp .eq x (BitVec.ofNat 8 44) = 1
        · exact .comma h44' h44e
        · exact .defaultValue h91 h44' h58 (bitZeroOfNeOne h44e)
      · -- `58 ≤ %8 < 91`: `LeafBlock3`
        have h58' : evalICmp .slt x (BitVec.ofNat 8 58) = 0 := bitZeroOfNeOne h58
        by_cases h58e : evalICmp .eq x (BitVec.ofNat 8 58) = 1
        · exact .colon h44' h58' h58e
        · exact .defaultValueMid h91 h44' h58' (bitZeroOfNeOne h58e)
  · -- the high half: `NodeBlock19`
    have h91' : evalICmp .slt x (BitVec.ofNat 8 91) = 0 := bitZeroOfNeOne h91
    by_cases h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1
    · -- 91 ≤ %8 < 123: `NodeBlock11`
      by_cases h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1
      · -- `LeafBlock7`
        by_cases h91e : evalICmp .eq x (BitVec.ofNat 8 91) = 1
        · exact .openBracket h91' h123 h93 h91e
        · exact .defaultValueBracket h91' h123 h93 (bitZeroOfNeOne h91e)
      · -- `LeafBlock9`
        have h93' : evalICmp .slt x (BitVec.ofNat 8 93) = 0 := bitZeroOfNeOne h93
        by_cases h93e : evalICmp .eq x (BitVec.ofNat 8 93) = 1
        · exact .closeBracket h91' h123 h93' h93e
        · exact .defaultValueBracketHigh h91' h123 h93' (bitZeroOfNeOne h93e)
    · -- 123 ≤ %8: `NodeBlock17`
      have h123' : evalICmp .slt x (BitVec.ofNat 8 123) = 0 := bitZeroOfNeOne h123
      by_cases h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1
      · -- `LeafBlock13`
        by_cases h123e : evalICmp .eq x (BitVec.ofNat 8 123) = 1
        · exact .openBrace h91' h123' h125 h123e
        · exact .defaultValueBrace h91' h123' h125 (bitZeroOfNeOne h123e)
      · -- `LeafBlock15`
        have h125' : evalICmp .slt x (BitVec.ofNat 8 125) = 0 := bitZeroOfNeOne h125
        by_cases h125e : evalICmp .eq x (BitVec.ofNat 8 125) = 1
        · exact .closeBrace h91' h123' h125' h125e
        · exact .defaultValueHigh h91' h123' h125' (bitZeroOfNeOne h125e)

/-! ### The dispatch's evidence, by arm -/

/-- **The last entry's terminal dispatch, as the arm it took.**  One constructor per arm
class the layer proves or preserves; `.dispatch` is the function into
`WalkDispatchResult`.

Each constructor carries only its own arm's premises: the scalar arm's byte class and
tail supply, the high-byte arm's residue (the one class-restricted bundle, kept as *one*
arm), the two refusals' own bits and cells, and — for the arms whose segments are still
owed — that arm's counted segment and endpoint facts. -/
inductive LastEntryArm (calls : Calls) {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) : Type
  /-- **`sw.default.i` with the tag test's true arm**: the plain-value path. -/
  | scalar {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
      (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
      (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
      (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
      (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
      {b35 : UInt8}
      (hread35 : readBytes (scalarEndS C s x (BitVec.ofNat 64 (C.k + 1))
        (BitVec.ofNat 64 G.nep) G.n (BitVec.ofNat 64 (entryPos G C.k))).mem
        ((G.b - 1) + G.n) 1 = some [b35])
      (hb13 : evalICmp .slt (head35 b35) (BitVec.ofNat 8 13) = 0)
      (hb32 : evalICmp .slt (head35 b35) (BitVec.ofNat 8 32) = 0)
      (hbne32 : evalICmp .eq (head35 b35) (BitVec.ofNat 8 32) = 0)
      (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
        evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
      (r₁ r₂ r₃ : CallOutcome) {rdv : BitVec 32} {xA : BitVec 32}
      (hreadT : readBytes
        (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
          G.n (BitVec.ofNat 64 (entryPos G C.k)) b35).mem (C.stage.tok + 16)
          (natToBytes (7 : Nat) 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
      (hpre₁ : s2ValuePosPre
        [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
         .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
        (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
          G.n (BitVec.ofNat 64 (entryPos G C.k)) b35).mem (C.stage.tok + 16)
          (natToBytes (7 : Nat) 4))
        (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) G.n
          (BitVec.ofNat 64 (entryPos G C.k)) b35).next)
      (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
        [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
         .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
        (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
          G.n (BitVec.ofNat 64 (entryPos G C.k)) b35).mem (C.stage.tok + 16)
          (natToBytes (7 : Nat) 4))
        (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) G.n
          (BitVec.ofNat 64 (entryPos G C.k)) b35).next = some r₁)
      (hret₁ : r₁.ret = .int 32 xA)
      (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
      (hzread : readBytes
        (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
          G.n (BitVec.ofNat 64 (entryPos G C.k)) b35).mem (C.stage.tok + 16)
          (natToBytes (7 : Nat) 4)) C.stage.z 8 = some (wordBytes 8 G.ev))
      (hpre₂ : s2ScalarValuePre
        [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c,
         .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
         .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next)
      (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
        [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c,
         .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
         .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next = some r₂)
      (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
      (hev64 : G.ev < 2 ^ 64)
      (hpre₃ : s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
         .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next)
      (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
        [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
         .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next =
        some r₃) : LastEntryArm calls G C s
  /-- **The high-byte default arm**: the bytes 126 and 127, the preserved
  class-restricted path. -/
  | highByte (r : HlastResidue G C s) : LastEntryArm calls G C s
  /-- **A bare string opener with no entry left**: refused at `if.then205.i`. -/
  | stringOpener {inc nep : BitVec 64}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34)))
      (hinc : evalOperand s (.reg "%inc.i") = some (.int 64 inc))
      (hnep : evalOperand s (.reg "%nep") = some (.int 64 nep))
      (hge : evalICmp .ult inc nep = 0)
      (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 G.n)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e)) : LastEntryArm calls G C s
  /-- **A closing bracket at depth zero with nothing open**: refused at `if.then56.i`. -/
  | closingZero {j : Nat}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
      (hsp : C.sp = 0)
      (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : LastEntryArm calls G C s
  /-- **A comma at depth zero**: nothing is open for it to separate, so the run leaves
  `if.then127.i` for `if.then130.i`, stores the entry's position at `%e + 8` and reaches
  the refusal copy — six links (`commaRefuse_at`). -/
  | commaZero {j : Nat}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
      (hsp : C.sp = 0)
      (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : LastEntryArm calls G C s
  /-- **A colon at depth zero**: the same refusal at `if.then173.i → if.then176.i`, six
  links (`colonRefuse_at`). -/
  | colonZero {j : Nat}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
      (hsp : C.sp = 0)
      (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : LastEntryArm calls G C s
  /-- **The comma above depth zero**: the container pair's four sub-routes.  The type
  stack's byte at `%sp - 1` is the brace's marker (`1`) or another container; the state
  stack's byte at the same index is `1` (merge, eight links) or not (refusal, eight
  links).  The merge keeps the depth and advances the index by one; the refusal stores
  the entry's position at `%e + 8`. -/
  | commaAboveZero (b1 b2 : UInt8)
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
      (hsp : C.sp ≠ 0)
      (hmark : C.tyMap (C.sp - 1) = b1)
      (hstate : C.stMap (C.sp - 1) = b2) : LastEntryArm calls G C s
  /-- **The colon above depth zero**: the marker's three sub-routes.  A brace marker
  (`1`) reads the state stack's byte at `%sp - 1`: `1` merges (eight links, depth kept,
  index advanced) and anything else refuses; any other marker refuses on its own byte
  (`colonMarkerRefuse_at`, seven links). -/
  | colonAboveZero (b1 b2 : UInt8)
      (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
      (hsp : C.sp ≠ 0)
      (hmark : C.tyMap (C.sp - 1) = b1)
      (hstate : C.stMap (C.sp - 1) = b2) : LastEntryArm calls G C s
  /-- **The container openers `[` and `{` at the last entry**: both enter `if.then.i`,
  and the four head links beside the tail's five reach the merge — nine links
  (`containerOpenMerge_at`).  The byte class is the arm's, the depth's `519`-guard and the
  root slot's zero word are the block's, and the callee's staging and answer are the
  call's, exactly as the scalar arm carries its own three calls. -/
  | containerOpen {b : BitVec 8}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 b))
      (hopen : b = BitVec.ofNat 8 91 ∨ b = BitVec.ofNat 8 123)
      (hsp519 : C.sp ≤ 519)
      (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
      (hpreV : s2ValuePosPre
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
      (r : CallOutcome)
      (hcall : stage2Calls stage2SubCalls "s2_value_pos"
        [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
      (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) : LastEntryArm calls G C s
  /-- **The closing delimiter with a container open**: `]` and `}` at a positive depth.
  Both bytes enter `if.then53.i`, and the nesting check's two stack bytes select the
  merge or a refusal — `closeWithOpen_at`'s four sub-routes.  The depth's index is the
  carry's, the marker and the state byte are the stacks' at it, and the offset store's
  three cells are the refusal sub-routes' own. -/
  | closeWithOpen {v : BitVec 8}
      (h8 : evalOperand s (.reg "%8") = some (.int 8 v))
      (hv : v = BitVec.ofNat 8 93 ∨ v = BitVec.ofNat 8 125)
      (hsp : C.sp ≠ 0)
      {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
      (hstate : C.stMap (C.sp - 1) = b2)
      (hpreA : s2AfterValuePre
        [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
         .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
      {j : Nat}
      (hvj : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
      (he : lookupName s.env "%e" = some (.ptr C.stage.e))
      (hj : j ≤ G.n) (hj64 : j < 2 ^ 64) : LastEntryArm calls G C s
  /-- **A default-arm letter or high byte on the scan-free class**, at the last entry: the
  bytes below `110` in the signed order whose tag test is clear.  The span below
  `if.else387.i` is `lettersSpan`'s four links, the kind it leaves is `0`, and the arm's two
  segments are the class's own — the head's chain to the seam (the four pivots,
  `sw.default.i`'s *failing* count test, `cond.end349.i`'s bound, the whitespace check's four
  and the seam: eleven links) and the tail's three calls on their empty arm — so the count is
  `11 + 4 + 3 + 1 = 19` and the price `19 + 2 = 21 ≤ 32` is inside the entry allowance.

  The class is the scan-free one, and here the reason is the byte before the entry's end: on
  the no-run class the seam's `%ee.1.i` is the entry's end (`LeafBlock37`'s else arm), so the
  copy call's `ult %ee.1.i %cond350.i` is `ult v v` and the walk leaves for the merge.  On
  the run class that cell is the run's stop and the scan runs; that class is `.supplied`'s
  at this level, because the terminal index's byte credit is zero, and `HcontArm.run`'s at
  the continuing one. -/
  | letters {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
      (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
        evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
      (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
      (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
      {Cm : WalkCarry G} {sm : State}
      (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm 11)
      (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
      (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
      {Ct : WalkCarry G} {st : State} {tok : Nat}
      (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
        (LetS413 sm x) Ct st 3)
      (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
      (htok : lookupName st.env "%t352.i" = some (.ptr tok)) : LastEntryArm calls G C s
  /-- **The byte `102` (`'f'`) on the scan-free class**, at the last entry: the letters
  span's *true* arm.  `LeafBlock54`'s `eq %8, 102` is set there, so the walk takes
  `if.then397.i`'s empty body to `if.then413.i` (`%.sink372`'s kind `9`) rather than the
  letters route's `if.else405.i` (kind `0`).  `fSpan` is the four links, and the arm's two
  segments are the class's own — the head's chain to the seam (eleven links at the last
  entry) and the tail's three calls on their empty arm — so the count is `11 + 4 + 3 + 1 =
  19` and the price `19 + 2 = 21 ≤ 32` is inside the entry allowance, with no byte term:
  the token ends where the entry does, so the copy call's test is `ult v v`.

  The class is the scan-free one for the same reason `.letters` is: the tail's three calls
  end at `if.end473.i`.  A run at `102` is `.run`'s, whose span is the same four links. -/
  | fLetter {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
      (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
        evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
      (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
      (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
      {Cm : WalkCarry G} {sm : State}
      (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm 11)
      (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
      (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
      {Ct : WalkCarry G} {st : State} {tok : Nat}
      (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
        (FS413 sm x) Ct st 3)
      (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
      (htok : lookupName st.env "%t352.i" = some (.ptr tok)) : LastEntryArm calls G C s
  /-- **The class-C span's leaves on the scan-free class**, at the last entry: the bytes
  `110 … 125` in the signed order, whose route below `if.else387.i` is one of four — `110`
  through `LeafBlock56`'s true arm (`if.then403.i`, kind `10`), `111 … 115` through its
  else arm, `116` from `LeafBlock58` itself (kind `8`), and `117 … 125` through
  `LeafBlock58`'s else arm.  The span is the byte's own (`c56TrueSpan`, `c56ElseSpan`,
  `c58TrueSpan`, `c58ElseSpan`) and enters at `nS ≤ 5`, which is what the class's four
  routes cost; the tail's three calls end at `if.end473.i` on their empty arm, so the
  count is `nH + nS + 3 + 1` and the price `nH + nS + 6 ≤ 32` at `nH ≤ 12`, `nS ≤ 5` — no
  byte term, because the token ends where the entry does.  `126`/`127` take the last
  route and are `.highByte`'s; `.run` is the same four routes with a run. -/
  | classC {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
      (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
      (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
        evalICmp .eq x (BitVec.ofNat 8 125) = 1)
      {Cm : WalkCarry G} {sm : State}
      (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm 11)
      (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
      (h8m : evalOperand sm (.reg "%8") = some (.int 8 x))
      {Cs : WalkCarry G} {ss : State} {nS : Nat}
      (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
      (hs : Cs.block = "if.then413.i") (hnS : nS ≤ 5)
      {Ct : WalkCarry G} {st : State} {tok : Nat}
      (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
      (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
      (htok : lookupName st.env "%t352.i" = some (.ptr tok)) : LastEntryArm calls G C s
  /-- **The last entry's run class, and its price obstruction.**  The byte before the
  entry's end is whitespace, so the whitespace skip runs, the token's end `%ee.1.i` is the
  run's stop `k < G.n`, and the copy call's test `ult k %cond350.i` is true — the
  extra-token scan traverses `[k, G.n)` and the merge follows its exit.

  **Why it is not proved here, exactly.**  `WalkDispatchResult.merge`'s price is
  `p + 2 ≤ 32·Δk + 8·ΔA` with `ΔA = entryPos G k2 - entryPos G C.k` at the merge's own
  index `k2`, and at the last entry `k2 = C.k + 1 = G.nep`, so
  `ΔA = entryPos G G.nep - entryPos G C.k = 0` (`walkEntryPos_at_nep`): the byte credit is
  **zero**.  The path's fixed part is twenty-four links — the head's eleven, the span's at
  most five, the tail's three, the landing's three, and the exit's and the merge's one each
  — so with the price's own two, twenty-six of the thirty-two are gone, and the run's
  whitespace visits *and* the scan's share the six that remain: a run and a scan of more
  than one visit each exceed it.  The continuing level's `.run` prices the same path
  because `C.k + 1 < G.nep` gives a positive `ΔA`; that is the only difference between the
  two levels, and it is a difference in the *price the dispatch states*, not in the walk.

  The class is therefore left to the caller rather than stated with a bound on the run's
  length, which would exclude documents the walk accepts.  The field is the arm's own
  result — the endpoint it reaches with the count and the price. -/
  | supplied (r : WalkDispatchResult (stage2Calls stage2SubCalls) G C s) :
      LastEntryArm calls G C s

/-- **The dispatch, from the arm.**  Each proved arm runs its own theorem; the preserved
high-byte arm is `hlastFacts_of_staging` → `ofHlastMerge`; the last entry's run arm is its
own result, carried. -/
theorem LastEntryArm.dispatch {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hnot : ¬ (C.k + 1 < G.nep)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s →
      WalkDispatchResult (stage2Calls stage2SubCalls) G C s
  | .scalar h8 h91 h44 h58 hne44 hread35 hb13 hb32 hbne32 hbit r₁ r₂ r₃ hreadT hpre₁
      hcall₁ hret₁ hbit0T hzread hpre₂ hcall₂ hret₂ hev64 hpre₃ hcall₃ =>
    scalarMerge_at G C s hInv hblock h8 h91 h44 h58 hne44 hnot hread35 hb13 hb32 hbne32
      hbit r₁ r₂ r₃ hreadT hpre₁ hcall₁ hret₁ hbit0T hzread hpre₂ hcall₂ hret₂ hev64 hpre₃
      hcall₃
  | .highByte r =>
    WalkDispatchResult.ofHlastMerge G C s hInv hblock
      (hlastFacts_of_staging (rdv := r.rdv) (xA := r.xA) G C s hInv hblock hnot
        r.hlt125 r.hne125 r.hb13 r.hb32 r.hbne13 r.r₁ r.r₂ r.r₃
        r.hreadT r.hpre₁ r.hcall₁ r.hret₁ r.hbit0T r.hzread
        r.hpre₂ r.hcall₂ r.hret₂ r.hev64 r.hpre₃ r.hcall₃)
  | .stringOpener h8 hinc hnep hge hv he =>
    (fun ⟨Cd, sd, p, hseg, herr, hprice⟩ =>
      WalkDispatchResult.refuse Cd sd p hseg.seg hseg.block hseg.word herr hprice)
      (quoteRefuse_at G C s hInv hblock h8 hinc hnep hge hv he
        (WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)))
  | .closingZero h8 hsp hv he hj hj64 =>
    (fun ⟨Cd, sd, p, hseg, herr, hprice⟩ =>
      WalkDispatchResult.refuse Cd sd p hseg.seg hseg.block hseg.word herr hprice)
      (bracketRefuse_at G C s hInv hblock h8 hsp hv he hj hj64
        (WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)))
  | .commaZero h8 hsp hv he hj hj64 =>
    WalkDispatchResult.ofRefuseAt (commaRefuse_at G C s hInv hblock h8 hsp hv he hj hj64
      (WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)))
  | .colonZero h8 hsp hv he hj hj64 =>
    WalkDispatchResult.ofRefuseAt (colonRefuse_at G C s hInv hblock h8 hsp hv he hj hj64
      (WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)))
  | .commaAboveZero b1 b2 h8 hsp hmark hstate => by
    by_cases hb1 : colonBit b1 = 1
    · have hmark1 : C.tyMap (C.sp - 1) = 1 := by
        rw [hmark]; exact uint8_eq_one_of_colonBit hb1
      by_cases hb2 : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1
      · exact commaBraceMerge_at G C s hInv hblock h8 hsp hmark1 hstate hb2
      · exact commaBraceRefuse_at G C s hInv hblock h8 hsp hmark1 hstate
          (bitZeroOfNeOne hb2)
    · have hbit : pairBit (BitVec.ofNat 8 b1.toNat) = 0 := by
        simpa only [pairBit, colonBit] using bitZeroOfNeOne hb1
      by_cases hb2 : colonBit b2 = 1
      · exact commaBracketMerge_at G C s hInv hblock h8 hsp hmark hstate hbit hb2
      · exact commaBracketRefuse_at G C s hInv hblock h8 hsp hmark hstate hbit
          (bitZeroOfNeOne hb2)
  | .colonAboveZero b1 b2 h8 hsp hmark hstate => by
    by_cases hb1 : colonBit b1 = 1
    · by_cases hb2 : colonBit b2 = 1
      · exact colonBraceMerge_at G C s hInv hblock h8 hsp hmark hstate hb1 hb2
      · exact colonBraceRefuse_at G C s hInv hblock h8 hsp hmark hstate hb1
          (bitZeroOfNeOne hb2)
    · exact colonMarkerRefuse_at G C s hInv hblock h8 hsp hmark (bitZeroOfNeOne hb1)
  | .containerOpen h8 hopen hsp519 hrd hpreV r hcall hret =>
    containerOpenMerge_at G C s hInv hblock h8 hopen hsp519 hrd hpreV r hcall hret
  | .closeWithOpen h8 hv hsp hmark hstate hpreA hvj he hj hj64 =>
    closeWithOpen_at G C s hInv hblock h8 hv hsp hmark hstate hpreA hvj he hj hj64
  | .letters h8 hbit h110 hne102 hHead hm hmk h8m hTail ht htk htok => by
    obtain ⟨Cd, sd, p, hseg, hblockD, hkD, hpreD, hincD, hnepD, hpriceD⟩ :=
      lettersCleanupMerge_at G C s hInv hblock h8 hbit h110 hne102 hHead hm hmk h8m
        hTail ht htk htok (by omega) (by omega)
    have hspv : evalOperand sd (Operand.reg "%sp.i.0248") =
        some (.int 32 (BitVec.ofNat 32 Cd.sp)) := hseg.inv'.depth_reg
    have hguard : C.k < G.nep :=
      WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
    have hnep64 : G.nep < 2 ^ 64 := by
      have h := G.nep_le
      have h2 := G.maxDoc
      simp only [stage2MaxDocument] at h2
      omega
    have hcap : C.k + 1 ≤ (BitVec.ofNat 64 G.nep).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
      omega
    refine WalkDispatchResult.merge Cd sd p Cd.sp (C.k + 1) "if.end473.i"
      (Operand.reg "%sp.i.0248") (Operand.reg "%inc.i") (BitVec.ofNat 64 G.nep)
      hseg hblockD hkD hpreD (by decide) hspv (by decide) ?_ hnepD
      (by omega) hcap hseg.inv'.depth_cap hseg.inv'.sp_le_wlen hpriceD
    · -- the merge's index cell is the header's increment, at the entry's successor
      simpa only [evalOperand] using hincD
  | .fLetter h8 hbit h110 h102 hHead hm hmk h8m hTail ht htk htok => by
    obtain ⟨Cd, sd, p, hseg, hblockD, hkD, hpreD, hincD, hnepD, hpriceD⟩ :=
      fCleanupMerge_at G C s hInv hblock h8 hbit h110 h102 hHead hm hmk h8m
        hTail ht htk htok (by omega) (by omega)
    have hspv : evalOperand sd (Operand.reg "%sp.i.0248") =
        some (.int 32 (BitVec.ofNat 32 Cd.sp)) := hseg.inv'.depth_reg
    have hguard : C.k < G.nep :=
      WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
    have hnep64 : G.nep < 2 ^ 64 := by
      have h := G.nep_le
      have h2 := G.maxDoc
      simp only [stage2MaxDocument] at h2
      omega
    have hcap : C.k + 1 ≤ (BitVec.ofNat 64 G.nep).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
      omega
    refine WalkDispatchResult.merge Cd sd p Cd.sp (C.k + 1) "if.end473.i"
      (Operand.reg "%sp.i.0248") (Operand.reg "%inc.i") (BitVec.ofNat 64 G.nep)
      hseg hblockD hkD hpreD (by decide) hspv (by decide) ?_ hnepD
      (by omega) hcap hseg.inv'.depth_cap hseg.inv'.sp_le_wlen hpriceD
    · -- the merge's index cell is the header's increment, at the entry's successor
      simpa only [evalOperand] using hincD
  | .classC h8 h110 h125 hHead hm hmk h8m hSpan hs hnS hTail ht htk htok => by
    obtain ⟨Cd, sd, p, hseg, hblockD, hkD, hpreD, hincD, hnepD, hpriceD⟩ :=
      classCMerge_at G C s hInv hblock h8 h110 h125 hHead hm hmk h8m hSpan hs hnS
        hTail ht htk htok (by omega) (by omega)
    have hspv : evalOperand sd (Operand.reg "%sp.i.0248") =
        some (.int 32 (BitVec.ofNat 32 Cd.sp)) := hseg.inv'.depth_reg
    have hguard : C.k < G.nep :=
      WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
    have hnep64 : G.nep < 2 ^ 64 := by
      have h := G.nep_le
      have h2 := G.maxDoc
      simp only [stage2MaxDocument] at h2
      omega
    have hcap : C.k + 1 ≤ (BitVec.ofNat 64 G.nep).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep64]
      omega
    refine WalkDispatchResult.merge Cd sd p Cd.sp (C.k + 1) "if.end473.i"
      (Operand.reg "%sp.i.0248") (Operand.reg "%inc.i") (BitVec.ofNat 64 G.nep)
      hseg hblockD hkD hpreD (by decide) hspv (by decide) ?_ hnepD
      (by omega) hcap hseg.inv'.depth_cap hseg.inv'.sp_le_wlen hpriceD
    · -- the merge's index cell is the header's increment, at the entry's successor
      simpa only [evalOperand] using hincD
  | .supplied r => r

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.HeadArm.complete
#print axioms LeanLLVM.Refinement.WalkScope.LastEntryArm.dispatch

end WalkScope
end LeanLLVM.Refinement
