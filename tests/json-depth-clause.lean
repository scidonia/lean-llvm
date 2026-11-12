/-
The depth clause's oracle gate: the admission verdict against the reference
parser's own outcome, on the documents whose nesting the clause decides.

The clause reads the stage-1 depth counter's fold over the document's structural
delimiter sequence (`kernelDepthOf`, `LeanLLVM/JsonKernelDomain.lean`), and the
certificate proves the reference parser refuses for depth exactly when that
measurement is past its bound (`depth_measured_no_refusal`,
`depth_refusal_deep`, `LeanLLVM/JsonKernelCertificate.lean`).  This scenario
observes the two sides together, on documents rather than on the statements:

* the deep-but-balanced class — `probes/bench/json/scale-4096.json`, the
  document the domain's own page names (179 opener bytes at a nesting depth of
  2), and two string-heavy documents whose bracket bytes sit inside string
  bodies — is admitted, is *not* refused for depth by the reference, and is
  answered by the reference with the value its bytes spell;
* the depth boundary — 128 nested arrays admitted, 129 refused — keeps the
  reference's own `depthExceeded` on the refused side;
* the control reproduces the deleted clause (an opener *count*) and shows it
  refuses the deep-but-balanced class while agreeing on the boundary, so the
  gate's scale-class rows are what distinguish the two clauses and the gate is
  not vacuous against a reverted clause.

Elaborated by `nix develop -c lake env lean tests/json-depth-clause.lean`.  A
`#guard` that does not hold stops elaboration with a nonzero exit status;
nothing outside the elaborated program is written.
-/
import LeanLLVM.JsonKernelCertificate

namespace JsonDepthClauseScenario

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement

/-- A document from its bytes. -/
def doc (bs : List Nat) : ByteArray := ByteArray.mk (bs.map UInt8.ofNat).toArray

/-- The number of copies of a byte. -/
def rep (n : Nat) (b : Nat) : List Nat := List.replicate n b

/-- The measured nesting depth, as the clause reads it. -/
def measured (d : ByteArray) : Nat := kernelDepthOf d

/-- The reference parser's depth verdict on the document. -/
def refusedForDepth (d : ByteArray) : Bool :=
  decide (parseBytes Limits.default d = .error .depthExceeded)

/-- The reference accepts the document. -/
def accepted (d : ByteArray) : Bool :=
  match parseBytes Limits.default d with
  | .ok _ => true
  | .error _ => false

/-- The deleted clause, reproduced: a document is inside the nesting bound when
it carries at most `kernelMaxDepth` opener bytes.  Nothing calls this; it is the
gate's control. -/
def openers (d : ByteArray) : Nat :=
  (d.data.toList).countP (fun b => b = 0x5B || b = 0x7B)

/-- The deleted clause's depth decision. -/
def legacyRefusesDepth (d : ByteArray) : Bool := decide (kernelMaxDepth < openers d)

/-- The bench fixture the domain's page names: 179 opener bytes at nesting depth
2.  Read as committed, not restated, so the row is the document the ledger's
number is about. -/
def deepBalanced : ByteArray := (include_str "../probes/bench/json/scale-4096.json").toUTF8

/-- A document whose 200 bracket bytes are all inside one string body: nesting
depth 0, and the deleted clause counted the whole of it. -/
def stringHeavy : ByteArray := doc ([0x22] ++ rep 200 0x5B ++ [0x22])

/-- The probe's opener-rich document: 129 brackets inside a string. -/
def openerRich : ByteArray := doc ([0x22] ++ rep 129 0x5B ++ [0x22])

/-- The boundary: 128 nested arrays, closed. -/
def depth128 : ByteArray := doc (rep 128 0x5B ++ rep 128 0x5D)

/-- One past the boundary: 129 nested arrays, closed. -/
def depth129 : ByteArray := doc (rep 129 0x5B ++ rep 129 0x5D)

/-! ### The deep-but-balanced class is admitted and answered -/

-- The fixture's shape: the measurement is the nesting depth, not the count.
#guard measured deepBalanced = 2
#guard openers deepBalanced = 179
#guard refusedForDepth deepBalanced = false
#guard admitted deepBalanced = true

-- The reference accepts it, and the tape decodes to the array of 64 objects the
-- bytes spell.
#guard match parseBytes Limits.default deepBalanced with
  | .ok t =>
      match decodeTape t with
      | some (.array vs) => vs.length = 178
      | _ => false
  | .error _ => false

-- The string-heavy class: bracket bytes inside a string body contribute nothing.
#guard measured stringHeavy = 0
#guard measured openerRich = 0
#guard refusedForDepth stringHeavy = false
#guard admitted stringHeavy = true
#guard admitted openerRich = true
#guard match parseBytes Limits.default openerRich with
  | .ok t => (decodeTape t).isSome
  | .error _ => false

/-! ### The boundary -/

#guard measured depth128 = 128
#guard refusedForDepth depth128 = false
#guard admitted depth128 = true
#guard match parseBytes Limits.default depth128 with
  | .ok t => (decodeTape t).isSome
  | .error _ => false

#guard measured depth129 = 129
#guard refusedForDepth depth129 = true
#guard admitted depth129 = false
#guard match admitted depth129, parseBytes Limits.default depth129 with
  | false, .error .depthExceeded => true
  | _, _ => false

-- The corpus's own depth rows keep their verdicts: the default profile admits
-- both of them, and the refusal `depth-three-refused.json` carries in the
-- manifest is the `depth2` profile's, not the default one's.
#guard measured (include_str "json/corpus/depth-two-ok.json").toUTF8 = 2
#guard admitted (include_str "json/corpus/depth-two-ok.json").toUTF8 = true
#guard admitted (include_str "json/corpus/depth-three-refused.json").toUTF8 = true
#guard refusedForDepth (include_str "json/corpus/depth-three-refused.json").toUTF8 = false

/-! ### The oracle: admission's verdict against the reference's, row by row -/

/-- The depth-relevant rows.  The clause decides nesting; the comparison is
`admitted = not refused for depth` on documents whose only possible refusal is
depth, which is why the policy class is not in this list (admission refuses those
by its second clause and the reference by its character policy, so the equality
is not the depth clause's statement there). -/
def rows : List ByteArray :=
  [ deepBalanced, stringHeavy, openerRich, depth128, depth129,
    (include_str "json/corpus/depth-two-ok.json").toUTF8,
    (include_str "json/corpus/depth-three-refused.json").toUTF8,
    (include_str "json/corpus/doc-nested.json").toUTF8 ]

/-- The gate's comparison: a clause's verdict against the reference parser's
depth verdict, on every row. -/
def agreesWithReference (f : ByteArray → Bool) : Bool :=
  rows.all (fun d => f d = !refusedForDepth d)

-- The clause agrees with the reference on every row.
#guard agreesWithReference admitted = true

-- The rows are not all the same verdict, so the agreement above is not the
-- vacuous one: both sides appear.
#guard (rows.filter admitted).length = 7
#guard (rows.filter refusedForDepth).length = 1

/-- The deleted clause's decision, reproduced in full for the control: non-empty,
inside the input bound, and at most `kernelMaxDepth` opener bytes.  The character
policy is not restated — no row here carries a policy refusal. -/
def legacyAdmitted (d : ByteArray) : Bool :=
  d.size ≠ 0 && d.size ≤ kernelMaxInput && !legacyRefusesDepth d

-- The control, on the gate's own comparator: the deleted clause disagrees with
-- the reference exactly on the deep-but-balanced class, so a clause reverted to
-- the opener count reddens the gate and this scenario is not vacuous.
#guard legacyAdmitted deepBalanced = false
#guard legacyAdmitted stringHeavy = false
#guard legacyAdmitted openerRich = false
#guard legacyAdmitted depth128 = true
#guard legacyAdmitted depth129 = false
#guard agreesWithReference legacyAdmitted = false
#guard (rows.filter (fun d => legacyAdmitted d ≠ admitted d)).length = 3

end JsonDepthClauseScenario
