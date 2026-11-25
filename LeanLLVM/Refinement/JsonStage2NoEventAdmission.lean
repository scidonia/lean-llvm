/-
The admitted input domain of the no-event fast path.

The walk theorem (`JsonStage2NoEventWalkReference.stage2NoEventWalkReferenceRun_terminal`) and
the transfer chain (`JsonEventBridgeFinal.eventsOfBytes_valueOfEvents_scalar`) are
statements about a document.  Neither states which documents the deployment lets
reach the walk: that is decided before the entry is called, by the selector's
`admission` (`LeanLLVM/JsonKernelDomain.lean`), and it is the domain the "same
caller-visible result on the admitted input domain" claim is relative to.  This
module names that domain and proves what follows from it.

# The clauses, and where each is checked

`admission` decides four clauses over the caller's bytes, in this order
(`LeanLLVM/JsonKernelDomain.lean:482-491`):

* **non-empty** — `admission`'s `emptyInput` clause.  The pipeline's own staging
  carries `0 < bs.length` because `Γ_utf8.pre` requires it
  (`JsonPipelineSpec.lean:42`); the route's control is
  `probes/json/route/DomainCheck.lean:33`.
* **the input bound** — `admission`'s `inputTooLong` clause against
  `kernelMaxInput = Limits.default.maxInput = 1048576`
  (`LeanLLVM/JSON/Parse.lean:34-35`, `JsonKernelDomain.lean:57`); the
  reference parser refuses a longer document before it reads a byte
  (`Parse.lean:390-392`).  Control: `DomainCheck.lean:38`.
* **the depth bound** — `admission`'s `depthBound` clause against
  `kernelMaxDepth = Limits.default.maxDepth = 128` (`Parse.lean:34-35`,
  `JsonKernelDomain.lean:60`), the number read off the stage-1 depth
  counter's fold over the document's structural delimiters
  (`JsonKernelDomain.docDepth`, certified by
  `JsonKernelCertificate.admission_documentDomain`).  Controls: `DomainCheck.lean:44-47`
  (128 admitted, 129 refused by the reference) and the route evidence's
  "depth 128 fast, 129/520/521 fall back with depthExceeded"
  (`probes/json/route/README.md:238`).  The bound also keeps the walk inside its
  own container stack: `kernel/json/stage2_noevent.c:78` declares
  `uint8_t stk[MAXD]` with `MAXD = 520` (`kernel/json/stage2.c:188`);
  `depth_lt_stack` below.
* **the character policy** — `admission`'s `policyRefusal` clause, the
  reference's own body scanner run at every quote (`JsonKernelDomain.lean:470`),
  pinned over the fourteen policy rows by `DomainCheck.lean:116-156` and
  `probes/json/route/check.sh:817-850` (`policy-expected`, then the byte
  binding; the route evidence records the agreement at
  `probes/json/route/README.md:238`).

Two further conditions complete the *admitted input domain* the arrow is stated
on, and neither is one of `admission`'s clauses:

* **the reference accepts the document** — `∃ t, parseBytes Limits.default … = .ok t`
  (`Parse.lean:390-404`).  The walk's obligation is a value equality with the
  reference, so it is vacuous where the reference refuses; the driver's NE7
  comparison is stated only over the documents the arm is admitted to
  (`tests/json-noevent/check.sh:92-105`).  The existence is the domain's clause;
  the walk theorem does not take it as a hypothesis — it reads the tie from the
  accept row, whose `parsed` field is the equality at that row's own tape.  An
  admitted document yields a parse, and a producer that builds the row at that
  parse places it there.
* **the document is valid UTF-8** — `Utf8Chars` (`LeanLLVM/JSON/Utf8.lean:87`).
  The no-event *stage-2* entry does not check this: the pipeline entry's stage 1
  does, in `kernel/json/utf8.c`, and its word is zero exactly when the staged
  window is a valid prefix (`JsonUtf8Steps.utf8_stage_refines`), with the
  complete-character case at `n % 64 ≠ 0` stated as `Utf8Chars` itself by
  `utf8_stage_refines_chars` (`JsonUtf8Steps.lean:7126`).  At `n % 64 = 0`
  that word is weaker than `Utf8Chars`; there the clause is carried by the
  reference's own strictness, which `referenceAccepts` supplies but whose
  implication is not proved here.  So this conjunct is a hypothesis about what
  the caller supplies, not a theorem of this module.

`Stage2NoEventRouteAdmits` is the four clauses `admission` decides;
`Stage2NoEventAdmitted` adds the two carried conditions.  Nothing in either is
stated as a negation.

# The hypothesis this module cannot state in Lean

The *native* two-phase decision — `probes/json/route/shim.c`'s phase one and
`probes/json/route/policy.c`'s phase two, driven through
`RouteMain.decide2` — is compared with `admission` by the probe's agreement
check, not modelled here: there is no Lean definition of the C accumulator's
execution, only the oracle it is compared against and the refinement claims
around it.  That agreement ("two-phase admission agrees with `admission`" on
every compared row, `probes/json/route/README.md:238`) is therefore the
hypothesis that the deployment's yes/no is `admission`'s yes/no; it is checked by
`probes/json/route/check.sh` and not by this module.

# What is proved, and what is not

Proved: the structure's four clauses make the selector's decision `ok`
(`admission_ok`, the inverse of `JsonKernelCertificate.admission_ok`), the
deployment's decision plus the two carried conditions rebuilds the structure
(`stage2NoEventAdmitted_of_admission`), an admitted document yields a reference
parse (`hparse`), the input bound is the
reference's (`length_le_referenceInput`), the depth clause keeps the walk's
stack from overflowing (`depth_lt_stack`), the reference does not refuse an
admitted document for depth, capacity or policy (`documentDomain`, read off the
kernel's certificate), and the staging's four capacity words fit their 64-bit
slots at an admitted length (`capacities_fit`).

The transfer chain's remaining premises are *run* facts, not document facts, and
are neither restated nor claimed here: `hrel : Stage2Records bs arena rs toks`,
`hrow : obs = consumeRecords bs arena rs`, `hwithin`, `hb : ∀ r ∈ rs, r.Bounded`,
`htoks : t.tokens = toks` and `hev : evs = …` are statements about the walk's
memory and the records it emitted (`JsonEventBridgeFinal.lean:75-85`), which no
predicate over `bs` alone can imply.  This module names the domain those facts
are taken at; it does not prove the pipeline.
-/
import LeanLLVM.JsonKernelCertificate
import LeanLLVM.JSON.Utf8

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The bounds the deployment and the walk read -/

/-- The no-event walk's container-stack capacity.  `kernel/json/stage2_noevent.c:78`
declares `uint8_t stk[MAXD]`, and `MAXD` is `520` at
`kernel/json/stage2.c:188`; the depth clause's `128` is what keeps a document
inside it (`depth_lt_stack`). -/
def stage2NoEventStackDepth : Nat := 520

/-! ### The selector's four clauses -/

/-- The four clauses `admission` decides over the caller's bytes, in its own
order: non-empty, inside the reference's input bound, inside its depth bound, and
clean under its character policy.  Each field is named after the clause that
checks it; `admission_ok` below says this conjunction is what the selector's
`ok` amounts to. -/
structure Stage2NoEventRouteAdmits (bs : List UInt8) : Prop where
  /-- `admission`'s `emptyInput` clause (`JsonKernelDomain.lean:482-483`); the
  staging's `0 < bs.length` clause (`JsonPipelineSpec.lean:42`). -/
  nonempty : 0 < bs.length
  /-- `admission`'s `inputTooLong` clause against `kernelMaxInput`, the
  reference's `Limits.default.maxInput` (`JsonKernelDomain.lean:484`). -/
  withinInputBound : bs.length ≤ kernelMaxInput
  /-- `admission`'s `depthBound` clause against `kernelMaxDepth`, the
  reference's `Limits.default.maxDepth` (`JsonKernelDomain.lean:485-486`). -/
  withinDepthBound : docDepth (ByteString.literal bs) ≤ (kernelMaxDepth : Int)
  /-- `admission`'s character-policy clause (`JsonKernelDomain.lean:487-491`):
  the reference's own body scan reports no surrogate or noncharacter. -/
  policyClean : policyRefusal (ByteString.literal bs) = none

/-- **The whole admitted input domain.**  The selector's four clauses, plus the
reference's acceptance (the value obligation's right-hand side exists) and the
stage-1 gate's UTF-8 validity.  The last two are conditions of the *call*, not
clauses of `admission`; the module docstring says where each is checked.

This structure is strictly narrower than what `admission` lets through: `{]` is
non-empty, inside both bounds, policy-clean and UTF-8-valid, so the selector says
`ok`, while `Stage2NoEventAdmitted` excludes it because the reference refuses it.
The arrow stated on this domain is therefore a statement about documents both
the deployment and the reference accept. -/
structure Stage2NoEventAdmitted (bs : List UInt8) : Prop
    extends Stage2NoEventRouteAdmits bs where
  /-- The stage-1 UTF-8 gate (`kernel/json/utf8.c`); at `n % 64 ≠ 0` its zero
  word is equivalent to this predicate (`utf8_stage_refines_chars`). -/
  utf8Valid : Utf8Chars (ByteString.literal bs)
  /-- The reference accepts the document, existentially.  This is the domain's
  clause, not the walk theorem's premise: the accept row carries the parse
  equality at its own tape, which a producer building the row at this parse
  supplies.  `Parse.lean:390-404` and the driver's NE7 comparison. -/
  referenceAccepts : ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t

/-! ### The selector's decision at the domain -/

/-- **The route's four clauses are the selector's `ok`.**  Each clause discharges
one `if` of `admission`; the character-policy clause is the `none` the final
match needs.  This is the direction the fast path uses: a caller that has the
clauses gets the decision the installer's manifest names. -/
theorem Stage2NoEventRouteAdmits.admission_ok {bs : List UInt8}
    (h : Stage2NoEventRouteAdmits bs) :
    (admission (ByteString.literal bs)).isOk = true := by
  obtain ⟨hnon, hlen, hdep, hpol⟩ := h
  have hsize : (ByteString.literal bs).size = bs.length := ByteString.size_literal bs
  unfold admission
  rw [ite_eq_right (by rw [hsize]; omega),
      ite_eq_right (by rw [hsize]; omega),
      ite_eq_right (by omega),
      hpol]
  rfl

/-- The same at the admitted domain. -/
theorem Stage2NoEventAdmitted.admission_ok {bs : List UInt8}
    (h : Stage2NoEventAdmitted bs) :
    (admission (ByteString.literal bs)).isOk = true :=
  h.toStage2NoEventRouteAdmits.admission_ok

/-- **The deployment's decision rebuilds the domain.**  A caller that has the
selector's `ok` (or, through the probe's agreement check, the native decision's
yes), the stage-1 gate's UTF-8 verdict, and the reference's tape at the document,
has `Stage2NoEventAdmitted`.  The four clauses are `admission_ok`'s, read
backwards. -/
theorem stage2NoEventAdmitted_of_admission {bs : List UInt8}
    (h : (admission (ByteString.literal bs)).isOk = true)
    (hutf8 : Utf8Chars (ByteString.literal bs))
    (hparse : ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t) :
    Stage2NoEventAdmitted bs := by
  obtain ⟨hnon, hlen, hdep, hpol⟩ := admission_ok h
  exact
    { nonempty := by rw [ByteString.size_literal] at hnon; exact hnon
      withinInputBound := by rw [ByteString.size_literal] at hlen; exact hlen
      withinDepthBound := by omega
      policyClean := hpol
      utf8Valid := hutf8
      referenceAccepts := hparse }

/-! ### What admission gives the walk -/

/-- **The domain's parse.**  The reference's acceptance is a conjunct of the
domain, so a tape the parser returns exists at every admitted document.  The
walk theorem does not consume this existence as a hypothesis — its accept row
carries `parsed : parseBytes … = .ok t` at the row's own tape, which is the tie
the transfer chain needs; an admitted document is one where a producer can build
that row.  The tape's identity (`htoks`) and the run facts beside it are the
walk's, not the domain's. -/
theorem Stage2NoEventAdmitted.hparse {bs : List UInt8}
    (h : Stage2NoEventAdmitted bs) :
    ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t :=
  h.referenceAccepts

/-- **The input bound is the reference's.**  `kernelMaxInput` is
`Limits.default.maxInput`, restated in `JsonKernelDomain` so the domain module
need not import the parser's limit structure. -/
theorem Stage2NoEventAdmitted.length_le_referenceInput {bs : List UInt8}
    (h : Stage2NoEventAdmitted bs) : bs.length ≤ Limits.default.maxInput := by
  have hlen := h.withinInputBound
  simpa [kernelMaxInput, Limits.default] using hlen

/-- **The depth clause keeps the document inside the walk's stack capacity.**  The
reference admits 128 levels and the no-event walk's stack holds 520 frames
(`kernel/json/stage2_noevent.c:78`, `kernel/json/stage2.c:188`), so an admitted
document's structural depth is far below the capacity.  That the walk's own
depth register never exceeds the document's structural depth (`sp ≤ docDepth`) is
the entry's property, not this theorem's. -/
theorem Stage2NoEventAdmitted.depth_lt_stack {bs : List UInt8}
    (h : Stage2NoEventAdmitted bs) :
    docDepth (ByteString.literal bs) < (stage2NoEventStackDepth : Int) := by
  have hd := h.withinDepthBound
  have hs : ((kernelMaxDepth : Int) < (stage2NoEventStackDepth : Int)) := by decide
  omega

/-- **The kernel's document clauses at the admitted domain.**  The selector's
decision excludes the three outcomes the pipeline ABI cannot answer — depth,
capacity and the character policy — so an admitted document the reference refuses
is refused for a syntax reason (that the walk reports the same refusal is the
walk theorem's content, not this one's).  This is
`JsonKernelCertificate.admission_documentDomain` (`:1567`) read across
`admission_ok` (`:1527`); the certificate's own proof is not repeated. -/
theorem Stage2NoEventAdmitted.documentDomain {bs : List UInt8}
    (h : Stage2NoEventAdmitted bs) :
    0 < (ByteString.literal bs).size ∧
    (ByteString.literal bs).size ≤ Limits.default.maxInput ∧
    (∀ e : ParseError,
      parseBytes Limits.default (ByteString.literal bs) = .error e →
        e ≠ .depthExceeded ∧ e ≠ .outOfCapacity ∧ ¬ isPolicyError e) :=
  admission_documentDomain _ h.admission_ok

/-- **The staging's capacity words fit their 64-bit slots.**  `JsonKernelDomain`
records that the four capacity functions are not admission clauses but are sized
from `doc.size`; at an admitted length each of them stays below `2^64`, so the
words the wrapper stores for them are not truncated. -/
theorem Stage2NoEventAdmitted.capacities_fit {bs : List UInt8}
    (h : Stage2NoEventAdmitted bs) :
    kernelEpCap bs.length < 2 ^ 64 ∧ kernelXpCap bs.length < 2 ^ 64 ∧
    kernelDstCap bs.length < 2 ^ 64 ∧ kernelEvCap bs.length < 2 ^ 64 := by
  have hlen := h.withinInputBound
  simp only [kernelMaxInput] at hlen
  have hdiv : (bs.length + 63) / 64 ≤ bs.length + 63 := Nat.div_le_self _ _
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [kernelEpCap, kernelXpCap, kernelDstCap, kernelEvCap, kernelBlocks]
     omega)

/-! ### Axiom footprints -/

#print axioms Stage2NoEventRouteAdmits.admission_ok
#print axioms Stage2NoEventAdmitted.admission_ok
#print axioms stage2NoEventAdmitted_of_admission
#print axioms Stage2NoEventAdmitted.hparse
#print axioms Stage2NoEventAdmitted.length_le_referenceInput
#print axioms Stage2NoEventAdmitted.depth_lt_stack
#print axioms Stage2NoEventAdmitted.documentDomain
#print axioms Stage2NoEventAdmitted.capacities_fit

end LeanLLVM.Refinement
