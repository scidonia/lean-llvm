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
* `.containerOpen` — `[` and `{`, both of which enter `if.then.i`: the four head links
  (`NodeBlock21 → NodeBlock19 → NodeBlock11 → LeafBlock7` at `91`, `NodeBlock21 →
  NodeBlock19 → NodeBlock17 → LeafBlock13` at `123`) and the tail's five — the
  value-position call, `if.end.i`'s depth guard, the push, the event reserve and the tag
  (`containerOpenMerge_at`, nine links).  The head's target states are the operands'
  literals, the tail's are `openS₅`…`openS₉`, and the block's own `let`-bound states are
  named by the three `step` theorems, so the composition is a chain of named states.
* `.supplied` — the arms whose segments are the remaining obligation, in the order the
  closure handoff names them:
  * **the comma and the colon above depth zero** (four sub-routes each: two merge routes
    and two refusals, e.g. `if.end150.i`/`if.end162.i` into `cleanup478.i` and
    `if.then147.i`/`if.then159.i` into `if.then`).  Their links are present as well
    (`WalkLink.if_end133_i`, `if_then141_i_at`, `if_end150_i`, `if_else153_i_at`,
    `if_end162_i`; `stackMarkerRefuse_at` for the marker's own refusal), and they are
    *blocked on their witness*: every one of them is at `C.sp ≠ 0`, while the layer's only
    depth-zero seed is `walkSeed` (`sp = 0`).  The depth-one state a document reaches is
    `containerOpen_depth_one`'s product (`JsonStage2WalkDispatchOpeners`), and these routes
    have yet to be stated at it, so an arm landed here would have no regression.
  * **the closing delimiter with an open container** — the same depth-one state to be
    stated at, plus `stateStackRefuse_at`'s state-stack byte for its refusal sub-route.
  * **the default arm's letter routes** (the tag test's clear arm: `if.else387.i → NodeBlock62 →
    LeafBlock54 → if.then413.i`).  Reachable at the seed (byte `a`), and the pieces exist —
    `walkHeadChainASeg`'s six links, the whitespace check, `consumer_tail_seg` — but the
    token's own scan (`walkScanToMerge`) sits between them, so the segment is the scan's
    induction rather than a handful of links.

  The field is that arm's own counted segment to the endpoint it reaches, with the
  endpoint's facts — *not* a bundle about the last entry, and no class premise on any
  other arm.

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

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The head switch's census -/

/-- A one-bit value that is not `1` is `0`. -/
theorem bitZeroOfNeOne {b : BitVec 1} (h : ¬ b = 1) : b = 0 := by
  have h2 : b.toNat < 2 := b.isLt
  have h1 : b.toNat ≠ 1 := by
    intro hh
    exact h (BitVec.eq_of_toNat_eq (by rw [hh]; rfl))
  have h0 : b.toNat = 0 := by omega
  exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)

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

/-- **A refusal is the dispatch's `refuse` alternative.**  A counted run from the head to
the refusal copy, with the word the copy loads and a price inside the remaining credit,
*is* that alternative: the segment, its endpoint's block and word, and the endpoint's
offset bound are the fields, field for field.  So an arm whose run is a refusal builds
its result from the witness without restating any of it. -/
theorem WalkDispatchResult.ofRefuseAt {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (h : WalkRefuseAt calls G C s) :
    WalkDispatchResult calls G C s := by
  obtain ⟨Cd, sd, p, hseg, herr, hprice⟩ := h
  exact WalkDispatchResult.refuse Cd sd p hseg.seg hseg.block hseg.word herr hprice

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
  /-- **The arms whose segment is the remaining obligation**: the comma and colon above
  depth zero, the closing delimiter with an open container, and the default arm's letter
  routes.  The field is that arm's own result — the endpoint it reaches with the count and
  the price — and no other arm's class is a premise of it. -/
  | supplied (r : WalkDispatchResult (stage2Calls stage2SubCalls) G C s) :
      LastEntryArm calls G C s

/-- **The dispatch, from the arm.**  Each proved arm runs its own theorem; the preserved
high-byte arm is `hlastFacts_of_staging` → `ofHlastMerge`; the supplied arm is its own
result, carried. -/
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
  | .containerOpen h8 hopen hsp519 hrd hpreV r hcall hret =>
    containerOpenMerge_at G C s hInv hblock h8 hopen hsp519 hrd hpreV r hcall hret
  | .supplied r => r

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.HeadArm.complete
#print axioms LeanLLVM.Refinement.WalkScope.LastEntryArm.dispatch

end WalkScope
end LeanLLVM.Refinement
