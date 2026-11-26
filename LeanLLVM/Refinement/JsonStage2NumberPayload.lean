/-
The number payload at the lexeme the document holds.

The relation's number row names the document's own bytes: `Stage2Records`,
`Stage2EventRel` and `TokenRecord` all take the lexeme `lex` beside the reader's
decimal `d`, and `Stage2NoEventWalkRecordSupplyOfParse` derives that `d` from the
token's RFC 8259 fact by `StrtodReader.reader_complete`.  The walk's number arm
does the same through this module's `stage2NumFast_writes_strtodSpec_of_reader`:
`valueArms_numFast_model`, `stage2NoEventWalkValueNumber`, the arm route and the
row all name the document's slice `lex` and read it with `StrtodReader.reader`.
The reader's normal form `d.lexeme` is not the document's lexeme whenever the
scanner's `E`/`+` spelling is used — `Decimal.lexeme` renders the marker as
`0x65` and the exponent sign as `0x2D` or nothing, so no well-formed
decomposition spells `1E5` or `1e+5` — which is why the arm cannot ask the slice
to be `d.lexeme`: that premise has no witness at such a document
(`numberSlice_ne_eDoc`), while the restated premise does
(`eDoc_numberArm_witness`).

This module supplies the lemma that restatement needs and the obstruction that
says why it is needed:

* **the payload at any accepted spelling.**  `numFastEmitted_of_reader` reads
  `numFastEmitted`'s own definition: the dispatch is `StrtodReader.reader`'s
  decimal and each branch model reads the lexeme through the same reader, so the
  conversion's value depends on the reader's decimal and not on the bytes'
  spelling.  `numberPayload_of_reader` is the eight bytes,
  `numberPayload_spelling_invariant` two spellings of one decimal, and
  `stage2NumFast_writes_strtodSpec_of_reader` the helper's accepted answer at
  the document's lexeme — `stage2NumFast_writes_strtodSpec` with its `d.lexeme`
  premises replaced by a reader witness at `lex`.
* **the obstruction.**  `lexeme_mem` reads `Decimal.lexeme`'s bytes: with a
  well-formed decomposition they are digits, `.`, the `e` marker and a `-`
  sign.  So `0x45` and `0x2B` are absent (`lexeme_no_upperE`,
  `lexeme_no_plus`), no well-formed `d` has `d.lexeme` equal to `1E5`
  (`lexeme_ne_eDoc`), and the shape the arm used to state has no witness at that
  document (`numberSlice_ne_eDoc`).  `eDoc_payload` is the positive control: at
  the same document the reader's decimal's payload is `strtodSpec`'s, by the
  lemma above, and `eDoc_numberArm_witness` is the restated arm's premise set at
  that document.

The emitted body's own writing of those bytes is a separate statement, stated at
the IR body (`NumFastBodyArm`, `JsonStage2NumFastArm`) and not claimed here; the
walk's selection answers the `num_fast_el1` slot with the model
(`stage2Calls_num_fast_el1`), which is why a model-level payload lemma is what
its arm can be restated against.

**The scan's tie to the reader.**  `stage2NumFast` tests
`numLexScan` before it converts.  The tree relates the *reader's* acceptance to
the tree's scanner (`reader_isSome_eq_numLexB`), and
`JsonStage2Body.numLexScan_accepts_iff_numLexB` supplies the missing half, from
the emitted control flow's index-based scan to that structural scan:

  `numLexScan_accepts_iff_numLexB :
     (numLexScan lex).2 = true ↔ numLexB (ByteString.literal lex) = true`

`numLexScan_accepts_of_reader` composes it with the reader's tie, so a reader
witness at the document's lexeme carries the scan's acceptance:

  `numLexScan_accepts_of_reader :
     reader (ByteString.literal lex) = some d → (numLexScan lex).2 = true`

No number arm names the acceptance as a premise: the sites that read the lexeme
derive it from the `hread` they already carry.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2Hsem
import LeanLLVM.Refinement.JsonStage2NoEventWalkRecordSupplyOfParse
import LeanLLVM.StrtodReader

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open ByteString

/-! ### The payload at the reader's decimal, whichever way the document spells it

`numFastEmitted` matches on `StrtodReader.reader bs`, and its three branch models
(`StrtodTier1.tier1Emitted`, `numTier2Binary`, `StrtodTier3.tier3Emitted`) take
the lexeme only through the same reader: `tier1Emitted read bs` is
`match read bs with | some d => tier1Binary d | none => …`, and likewise tier 3.
So two byte strings the reader agrees on convert to the same value, and a
well-formed decimal's own lexeme is one of them (`reader_lexeme`). -/

/-- **Two spellings of one decimal convert alike.**  Both sides are
`numFastEmitted`'s dispatch at the reader's `d`, and each branch's model reads the
lexeme through `StrtodReader.reader` and no further. -/
theorem numFastEmitted_reader_eq {bs bs' : Bytes} {d : Decimal}
    (h : StrtodReader.reader bs = some d) (h' : StrtodReader.reader bs' = some d) :
    numFastEmitted bs = numFastEmitted bs' := by
  -- The dispatch and the three branch models are the only readers of the bytes.
  simp only [numFastEmitted, StrtodTier1.tier1Emitted, StrtodTier3.tier3Emitted, h, h']

/-- **The payload at an accepted lexeme.**  At any byte string the reader reads
as a well-formed decimal, the emitted conversion's value is `strtodSpec`'s of
that decimal — the reader's normal form is not needed. -/
theorem numFastEmitted_of_reader {bs : Bytes} {d : Decimal}
    (h : StrtodReader.reader bs = some d) (hwf : d.wellFormed) :
    numFastEmitted bs = strtodSpec d := by
  have hspec := numFastEmitted_strtodSpec d hwf
  have h' : StrtodReader.reader d.lexeme = some d := StrtodReader.reader_lexeme hwf
  rw [numFastEmitted_reader_eq (bs' := d.lexeme) h h', hspec]

/-- **The eight payload bytes at an accepted lexeme.**  The record's payload is
`strtodSpec`'s encoding of the reader's decimal, whatever the document's spelling
is. -/
theorem numberPayload_of_reader {lex : List UInt8} {d : Decimal}
    (h : StrtodReader.reader (ByteString.literal lex) = some d) (hwf : d.wellFormed) :
    (numFastEmitted (ByteString.literal lex)).toBits = (strtodSpec d).toBits := by
  rw [numFastEmitted_of_reader h hwf]

/-- **One payload for two spellings.**  This is the equality a read-back needs
between a document's spelling (`1E5`) and the reader's normal form (`1e5`). -/
theorem numberPayload_spelling_invariant {lex lex' : List UInt8} {d : Decimal}
    (h : StrtodReader.reader (ByteString.literal lex) = some d)
    (h' : StrtodReader.reader (ByteString.literal lex') = some d)
    (hwf : d.wellFormed) :
    (numFastEmitted (ByteString.literal lex)).toBits =
      (numFastEmitted (ByteString.literal lex')).toBits := by
  rw [numFastEmitted_of_reader h hwf, numFastEmitted_of_reader h' hwf]

/-- **`num_fast_el1`'s accepted answer at the document's lexeme.**
`stage2NumFast_writes_strtodSpec` at a lexeme whose reader reads `d`, with no
premise about `d.lexeme`'s bytes.  The scan's acceptance is not a premise:
`numLexScan_accepts_of_reader` derives it from `hread`. -/
theorem stage2NumFast_writes_strtodSpec_of_reader {p out err : Nat} {n : BitVec 64}
    {mem : Mem} {next : Nat} {lex : List UInt8} {d : Decimal}
    (hlex : readBytes mem p n.toNat = some lex)
    (hread : StrtodReader.reader (ByteString.literal lex) = some d)
    (hwf : d.wellFormed) :
    stage2NumFast [.ptr p, .int 64 n, .ptr out, .ptr err] mem next =
      some { ret := .int 32 (BitVec.ofNat 32 1),
             mem := writeBytes mem out (wordBytes 8 (strtodSpec d).toBits),
             next := next } := by
  have hscan := numLexScan_accepts_of_reader hread
  have hp := numFastEmitted_of_reader (bs := ByteString.literal lex) hread hwf
  simp only [stage2NumFast, hlex, hscan, ite_true, hp]

/-! ### `Decimal.lexeme`'s bytes

The reader's normal form is the decomposition rendered: an optional `-`, the
`int`'s digits, an optional `.` and the fraction's digits, an optional `e` with
an optional `-` and the exponent's digits.  With the decomposition well formed
each digit run is digits, so the marker is `0x65` and never `0x45`, and `+` never
appears.

The rendering's four shapes and the lexeme's are `rfl`, so the case analysis below
rewrites with those rather than unfolding the definitions under a `match`. -/

/-- `ByteString.mem_cons` with the head and the tail implicit, so the split is a
projection: `rcases mem_cons_iff.mp hb with rfl | hb`. -/
theorem mem_cons_iff {a b : UInt8} {bs : Bytes} :
    b ∈ (a +: bs) ↔ b = a ∨ b ∈ bs :=
  ByteString.mem_cons a b bs

/-- **An `int` part is digits.**  Its two constructors are a lone `0` and a
`1`–`9` lead with a digit tail. -/
theorem intPart_all {bs : Bytes} (h : IntPart bs) : ∀ b ∈ bs, IsDigitB b = true := by
  cases h with
  | zero =>
      intro b hb
      rcases mem_cons_iff.mp hb with rfl | hb
      · decide
      · exact absurd hb (ByteString.not_mem_empty b)
  | lead h1 h2 hr =>
      intro b hb
      rcases mem_cons_iff.mp hb with rfl | hb
      · simp only [IsDigitB, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨UInt8.le_trans (by decide : (0x30 : UInt8) ≤ 0x31) h1, h2⟩
      · exact digits0_all hr b hb

/-- `Decimal.body`'s first shape (`int` alone): the bytes are `int`'s. -/
theorem body_none_none (neg : Bool) (ip : Bytes) :
    Decimal.body (⟨neg, ip, none, none⟩ : Decimal) = ip := rfl

/-- `Decimal.body`'s second shape (`int "." frac`). -/
theorem body_some_none (neg : Bool) (ip fs : Bytes) :
    Decimal.body (⟨neg, ip, some fs, none⟩ : Decimal) = ip ++ (0x2E +: fs) := rfl

/-- `Decimal.body`'s third shape (`int exp`): the marker is `0x65`. -/
theorem body_none_some (neg : Bool) (ip : Bytes) (s : Bool) (ds : Bytes) :
    Decimal.body (⟨neg, ip, none, some (s, ds)⟩ : Decimal) =
      ip ++ (0x65 +: (Decimal.signBytes s ++ ds)) := rfl

/-- `Decimal.body`'s fourth shape (`int "." frac exp`). -/
theorem body_some_some (neg : Bool) (ip fs : Bytes) (s : Bool) (ds : Bytes) :
    Decimal.body (⟨neg, ip, some fs, some (s, ds)⟩ : Decimal) =
      (ip ++ (0x2E +: fs)) ++ (0x65 +: (Decimal.signBytes s ++ ds)) := rfl

/-- **The lexeme is the sign and the body.** -/
theorem lexeme_eq (neg : Bool) (ip : Bytes) (fr : Option Bytes)
    (ex : Option (Bool × Bytes)) :
    Decimal.lexeme (⟨neg, ip, fr, ex⟩ : Decimal) =
      Decimal.signBytes neg ++ Decimal.body (⟨neg, ip, fr, ex⟩ : Decimal) := rfl

/-- **A body's bytes are digits, the `.`, the `e` and a `-`.**  The four shapes
are `Decimal.body`'s, and the `-` is the exponent's sign. -/
theorem body_mem {neg : Bool} {ip : Bytes} {fr : Option Bytes}
    {ex : Option (Bool × Bytes)} (hip : IntPart ip)
    (hfr : ∀ fs, fr = some fs → Digits fs)
    (hex : ∀ s ds, ex = some (s, ds) → Digits ds) :
    ∀ b ∈ Decimal.body (⟨neg, ip, fr, ex⟩ : Decimal),
      IsDigitB b = true ∨ b = 0x2E ∨ b = 0x65 ∨ b = 0x2D := by
  intro b hb
  cases fr with
  | none =>
      cases ex with
      | none =>
          rw [body_none_none] at hb
          exact Or.inl (intPart_all hip b hb)
      | some p =>
          obtain ⟨s, ds⟩ := p
          rw [body_none_some] at hb
          rcases ByteString.mem_append.mp hb with hb | hb
          · exact Or.inl (intPart_all hip b hb)
          · rcases mem_cons_iff.mp hb with rfl | hb
            · exact Or.inr (Or.inr (Or.inl rfl))
            · rcases ByteString.mem_append.mp hb with hb | hb
              · cases s with
                | false =>
                    rw [Decimal.signBytes_false] at hb
                    exact absurd hb (ByteString.not_mem_empty b)
                | true =>
                    rw [Decimal.signBytes_true] at hb
                    rcases mem_cons_iff.mp hb with rfl | hb
                    · exact Or.inr (Or.inr (Or.inr rfl))
                    · exact absurd hb (ByteString.not_mem_empty b)
              · exact Or.inl (digits_all (hex s ds rfl) b hb)
  | some fs =>
      cases ex with
      | none =>
          rw [body_some_none] at hb
          rcases ByteString.mem_append.mp hb with hb | hb
          · exact Or.inl (intPart_all hip b hb)
          · rcases mem_cons_iff.mp hb with rfl | hb
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl (digits_all (hfr fs rfl) b hb)
      | some p =>
          obtain ⟨s, ds⟩ := p
          rw [body_some_some] at hb
          rcases ByteString.mem_append.mp hb with hb | hb
          · rcases ByteString.mem_append.mp hb with hb | hb
            · exact Or.inl (intPart_all hip b hb)
            · rcases mem_cons_iff.mp hb with rfl | hb
              · exact Or.inr (Or.inl rfl)
              · exact Or.inl (digits_all (hfr fs rfl) b hb)
          · rcases mem_cons_iff.mp hb with rfl | hb
            · exact Or.inr (Or.inr (Or.inl rfl))
            · rcases ByteString.mem_append.mp hb with hb | hb
              · cases s with
                | false =>
                    rw [Decimal.signBytes_false] at hb
                    exact absurd hb (ByteString.not_mem_empty b)
                | true =>
                    rw [Decimal.signBytes_true] at hb
                    rcases mem_cons_iff.mp hb with rfl | hb
                    · exact Or.inr (Or.inr (Or.inr rfl))
                    · exact absurd hb (ByteString.not_mem_empty b)
              · exact Or.inl (digits_all (hex s ds rfl) b hb)

/-- **A lexeme's bytes are digits, the `.`, the `e` and a `-`.**  The sign adds
no byte but `-`. -/
theorem lexeme_mem {d : Decimal} (hwf : d.wellFormed) :
    ∀ b ∈ d.lexeme, IsDigitB b = true ∨ b = 0x2E ∨ b = 0x65 ∨ b = 0x2D := by
  obtain ⟨neg, ip, fr, ex⟩ := d
  simp only [Decimal.wellFormed] at hwf
  obtain ⟨hip, hfr, hex⟩ := hwf
  intro b hb
  rw [lexeme_eq] at hb
  rcases ByteString.mem_append.mp hb with hb | hb
  · cases neg with
    | false =>
        rw [Decimal.signBytes_false] at hb
        exact absurd hb (ByteString.not_mem_empty b)
    | true =>
        rw [Decimal.signBytes_true] at hb
        rcases mem_cons_iff.mp hb with rfl | hb
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact absurd hb (ByteString.not_mem_empty b)
  · exact body_mem hip hfr hex b hb

/-- **The reader's normal form never spells `E`.** -/
theorem lexeme_no_upperE {d : Decimal} (hwf : d.wellFormed) : 0x45 ∉ d.lexeme := by
  intro hmem
  rcases lexeme_mem hwf 0x45 hmem with h | h | h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- **The reader's normal form never spells `+`.** -/
theorem lexeme_no_plus {d : Decimal} (hwf : d.wellFormed) : 0x2B ∉ d.lexeme := by
  intro hmem
  rcases lexeme_mem hwf 0x2B hmem with h | h | h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- **`1E5` is not any well-formed decomposition's normal form.**  The reader
normalises `E` away, so the slice premise the arm used to carry — the document's
bytes are `d.lexeme` — has no witness at the relation's own exponent-spelling
control. -/
theorem lexeme_ne_eDoc {d : Decimal} (hwf : d.wellFormed) :
    d.lexeme.data.toList ≠ eDoc := by
  intro h
  have hmem : 0x45 ∈ d.lexeme.data.toList := by
    rw [h]
    simp [eDoc]
  have hmem' : 0x45 ∈ d.lexeme := by
    rw [ByteString.mem_def, ByteString.toList_eq_data_toList]
    exact hmem
  exact lexeme_no_upperE hwf hmem'

/-- **The normal-form slice premise at `1E5`.**  The number arm formerly asked
the document's slice to be `d.lexeme` (at `stage2NoEventWalkValueRow_number` and
its arm route); at a document whose span is `1E5` the slice is `eDoc`, which is
no well-formed `d`'s normal form, so that premise is uninhabited there.  The arm
now names the slice `lex` instead, and `eDoc_numberArm_witness` inhabits it. -/
theorem numberSlice_ne_eDoc {bs : List UInt8} {d : Decimal} {lane stop : Nat}
    (hwf : d.wellFormed) (h : (bs.drop lane).take (stop - lane) = eDoc) :
    (bs.drop lane).take (stop - lane) ≠ d.lexeme.data.toList := by
  intro hcon
  exact lexeme_ne_eDoc hwf (hcon.symm.trans h)

/-! ### The positive control

At `1E5` the reader's decimal exists and is well formed, so the payload is
`strtodSpec`'s of it by `numFastEmitted_of_reader` — the premise the arm cannot
state at that document is not needed for the payload. -/

/-- The reader's decimal for `1E5` is well formed: one digit, no fraction, an
unsigned one-digit exponent. -/
theorem eDecimal_wf : eDecimal.wellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · show IntPart (ByteString.literal [0x31])
    have h : ByteString.literal [0x31] = 0x31 +: (empty : Bytes) := by
      apply ByteString.eq_of_toList_eq
      simp
    rw [h]
    exact IntPart.lead (by decide) (by decide) Digits0.nil
  · intro fs hfs
    exact absurd hfs (by simp [eDecimal])
  · intro s ds hds
    have hds' : (false, ByteString.literal [0x35]) = (s, ds) := by
      simpa [eDecimal] using hds
    rw [Prod.mk.injEq] at hds'
    obtain ⟨-, h2⟩ := hds'
    have h : ByteString.literal [0x35] = 0x35 +: (empty : Bytes) := by
      apply ByteString.eq_of_toList_eq
      simp
    rw [← h2, h]
    exact Digits.one (by decide)

/-- **`1E5`'s payload.**  The document's spelling is absorbed at the reader: the
accepted lexeme's eight bytes are `strtodSpec`'s of the reader's decimal. -/
theorem eDoc_payload :
    (numFastEmitted (ByteString.literal eDoc)).toBits = (strtodSpec eDecimal).toBits :=
  numberPayload_of_reader eDoc_reader eDecimal_wf

/-! ### The restated arm's premises at `1E5`

The arm names the document's own bytes `lex`, reads them with the reader, and
slices the document against `lex`.  At `1E5` the old premise — the slice is
`d.lexeme` — was uninhabited (`numberSlice_ne_eDoc`); the restated one is
inhabited, and this is its witness. -/

/-- The `1E5` document's three bytes, in memory at address zero. -/
def eDocMem : Mem := [(0, 0x31), (1, 0x45), (2, 0x35)]

/-- The document's bytes as a memory read. -/
theorem eDocMem_reads : readBytes eDocMem 0 3 = some eDoc := by decide

/-- **The restated arm's premises, inhabited at `1E5`.**  A document whose bytes
are the three of `1E5`, a lane at zero and `q` at three: `hlex` is the read of
the document's own slice, `hread` reads that slice as `eDecimal`, `hwf` is its
grammaticality, the payload is `strtodSpec`'s of the reader's decimal, and
`hstop`/`hslice` name the slice `lex` itself.  The scan's acceptance is not a
conjunct: `numLexScan_accepts_of_reader` carries it from `hread`.  The slice
premise the arm used to carry — the document's bytes are `d.lexeme` — had no
witness at this document; this one does. -/
theorem eDoc_numberArm_witness :
    ∃ (mem : Mem) (lane q : Nat) (lex : List UInt8) (d : Decimal),
      readBytes mem lane (q - lane) = some lex ∧
      StrtodReader.reader (ByteString.literal lex) = some d ∧
      d.wellFormed ∧
      (numFastEmitted (ByteString.literal lex)).toBits = (strtodSpec d).toBits ∧
      q = lane + lex.length ∧
      (eDoc.drop lane).take (q - lane) = lex := by
  refine ⟨eDocMem, 0, 3, eDoc, eDecimal, ?_, eDoc_reader, eDecimal_wf, eDoc_payload,
    ?_, ?_⟩
  · simpa [eDocMem, eDoc] using eDocMem_reads
  · simp [eDoc]
  · simp [eDoc]

/-! ### Axiom footprints -/

#print axioms numFastEmitted_reader_eq
#print axioms numFastEmitted_of_reader
#print axioms numberPayload_of_reader
#print axioms numberPayload_spelling_invariant
#print axioms stage2NumFast_writes_strtodSpec_of_reader
#print axioms mem_cons_iff
#print axioms intPart_all
#print axioms body_none_none
#print axioms body_some_none
#print axioms body_none_some
#print axioms body_some_some
#print axioms lexeme_eq
#print axioms body_mem
#print axioms lexeme_mem
#print axioms lexeme_no_upperE
#print axioms lexeme_no_plus
#print axioms lexeme_ne_eDoc
#print axioms numberSlice_ne_eDoc
#print axioms eDecimal_wf
#print axioms eDoc_payload
#print axioms eDocMem_reads
#print axioms eDoc_numberArm_witness

end LeanLLVM.Refinement
