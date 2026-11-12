/-
The JSON kernel's certified domain: the document-side predicate a caller checks
before it hands a document to the native pipeline, and the three outcomes the
route distinguishes.

The native pipeline is certified against `pipelineSpecPre`
(`LeanLLVM/Refinement/JsonPipelineSpec.lean`), whose document clauses are a
non-empty input inside `Limits.default.maxInput`, no nesting deeper than
`Limits.default.maxDepth`, no token exhaustion, and — as the wrapper's own
stricter requirement — no character-policy refusal.  The pipeline's ABI carries
no depth limit (its stage-2 walk pushes 520 frames) and no character-policy
slot (its verdict is the RFC 8259 one), so a document outside those clauses
must not reach it: the route reports it as outside the certified domain and
answers it with the scalar parser.

`admission` is that decision, and it is a *boundary*, not a wall.  Each clause
is one checker:

* `0 < doc.size` and `doc.size ≤ kernelMaxInput` — arithmetic;
* `docDepth` is the document's nesting depth: the maximum of the stage-1 depth
  counter's fold over the document's structural delimiter sequence
  (`structTokensFrom`, the `{`/`[`/`}`/`]` bytes outside string bodies, in
  document order — the sequence the stage-1 index stream carries).  The fold is
  the counter's own (`deltaZ`, `DepthCountRefine.depthSpec`), and
  `LeanLLVM/JsonKernelCertificate.lean` proves that the reference parser refuses
  for depth exactly when this measured maximum is past its bound;
* `policyRefusal` scans the document's quotes and runs the reference's own body
  scanner at each, reporting the reference's reason and byte.  It looks at
  every quote, not only the ones a well-formed document would open, because a
  policy refusal must never be missed — a false positive only narrows the
  domain, and the scalar parser still answers it;
* the pointer-arithmetic widths the units need are consequences of the input
  bound and are discharged in the certificate, not decided here.

The clauses are separate functions and separate certificate theorems.  Widening
the domain later — including to a total fast path — means removing a clause
from `admission` and dropping its certificate, not renegotiating the interface:
the fallback arm is what makes the API total today, and it is expected to
shrink as checkers are proved.
-/
import LeanLLVM.JSON.Scan
import LeanLLVM.Refinement.DepthCountRefine

-- The `structTokensFrom` match's equation binders are what its termination proof
-- reads, so the linter's report that they are unused is about the generated
-- equation lemma rather than about the definition.
set_option linter.unusedVariables false

namespace LeanLLVM.Refinement

open LeanLLVM.JSON
open LeanLLVM.Refinement.DepthCountRefine

/-- The input bound the certificate's depth and length clauses are stated at.
It is `Limits.default.maxInput`, restated here because this module is the
domain's own statement and does not import the parser's limit structure. -/
def kernelMaxInput : Nat := 1048576

/-- The reference parser's nesting bound (`Limits.default.maxDepth`). -/
def kernelMaxDepth : Nat := 128

/-! ### The depth the clause reads

The stage-1 depth counter's fold, made a document-side function.  The counter
(`tests/v16/depth_count.ll`, proved by `DepthCountRefine.depth_count_refines`)
walks a token sequence, adds `+1` per `{`/`[` and `-1` per `}`/`]`, and reports
the final depth and the sum of the running depths after each token.  Its step is
`deltaZ`; the maximum of those running depths bounds the document's nesting, and
the two statistics the kernel returns are read off the same run
(`maxDepthTokens_eq_run_max`, `depthRun_step`).

The token sequence is the document's *structural* delimiters: a string body
contributes no token, and a string is skipped by the reference's own body
scanner (`scanCharsEnd`), so the sequence is the one the stage-1 index stream
carries rather than a second reading of the bytes.  The certificate proves the
parser agrees with this measurement. -/

/-- A bracket byte: the four the depth counter steps on. -/
def delimTok (b : UInt8) : Bool :=
  b = 0x5B || b = 0x7B || b = 0x5D || b = 0x7D

theorem delimTok_open {c : UInt8} (h : IsOpenB c = true) : delimTok c = true := by
  simp only [IsOpenB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | rfl <;> decide

theorem delimTok_close {c : UInt8} (h : IsCloseB c = true) : delimTok c = true := by
  simp only [IsCloseB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | rfl <;> decide

theorem deltaZ_open {c : UInt8} (h : IsOpenB c = true) : deltaZ c = 1 := by
  simp only [IsOpenB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | rfl <;> decide

theorem deltaZ_close {c : UInt8} (h : IsCloseB c = true) : deltaZ c = -1 := by
  simp only [IsCloseB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | rfl <;> decide

theorem lt_of_getElem? {bs : Bytes} {i : Nat} {c : UInt8} (h : bs[i]? = some c) :
    i < bs.size := by
  have := (ByteString.getElem?_eq_some_iff.mp h).1
  rwa [ByteString.length_eq_size] at this

/-- The stop a successful body scan reports is past the position it started at. -/
theorem scanCharsEnd_stop_gt {bs : Bytes} {i off : Nat} {cs : List Nat}
    {stop : { n : Nat // n ≤ bs.size }} (h : scanCharsEnd bs i off = .ok (cs, stop)) :
    i < stop.val := by
  obtain ⟨rest, hs, hdrop⟩ := scanCharsEnd_sound h
  have hstr := scanCharsFrom_sound hs
  have hlt := strChars_suffix_lt hstr
  have hlen : (bs.drop stop.val).length = bs.size - stop.val := by
    rw [ByteString.length_drop, ByteString.length_eq_size]
  rw [hdrop] at hlen
  have hleni : (bs.drop i).length = bs.size - i := by
    rw [ByteString.length_drop, ByteString.length_eq_size]
  rw [hleni] at hlt
  omega

def structTokensFrom (bs : Bytes) (i : Nat) : List UInt8 :=
  match h : bs[i]? with
  | none => []
  | some c =>
      if hq : c = 0x22 then
        match hs : scanCharsEnd bs (i + 1) 0 with
        | .ok (_, stop) => structTokensFrom bs stop.val
        | .error _ => []
      else (if delimTok c then [c] else []) ++ structTokensFrom bs (i + 1)
termination_by bs.size - i
decreasing_by
  · have hgt := scanCharsEnd_stop_gt hs
    omega
  · have hlt : i < bs.size := lt_of_getElem? h
    omega

def maxDepthTokens : List UInt8 → Int
  | [] => 0
  | c :: ts => max 0 (maxDepthTokens ts + deltaZ c)

theorem maxDepthTokens_nonneg (ts : List UInt8) : 0 ≤ maxDepthTokens ts := by
  induction ts with
  | nil => simp [maxDepthTokens]
  | cons c ts ih => simp only [maxDepthTokens]; omega

theorem maxDepthTokens_compute (c : UInt8) (ts : List UInt8) :
    maxDepthTokens (c :: ts) = max 0 (maxDepthTokens ts + deltaZ c) := rfl

theorem maxDepthTokens_open {c : UInt8} (ts : List UInt8) (h : IsOpenB c = true) :
    maxDepthTokens (c :: ts) = maxDepthTokens ts + 1 := by
  rw [maxDepthTokens_compute, deltaZ_open h]
  have := maxDepthTokens_nonneg ts
  omega

theorem maxDepthTokens_close {c : UInt8} (ts : List UInt8) (h : IsCloseB c = true) :
    maxDepthTokens (c :: ts) = max 0 (maxDepthTokens ts - 1) := by
  rw [maxDepthTokens_compute, deltaZ_close h]
  simp only [Int.sub_eq_add_neg]


/-- The counter's running depth after each token, starting at zero: the values
`stepZ`'s first component takes along the fold, entry `k` being the depth after
`k` tokens. -/
def depthRun (ts : List UInt8) : List Int := ts.scanl (fun b c => b + deltaZ c) 0

theorem max_comm_int (a b : Int) : max a b = max b a := by
  by_cases h : a ≤ b
  · rw [show max a b = b from by omega, show max b a = b from by omega]
  · rw [show max a b = a from by omega, show max b a = a from by omega]

theorem scanl_add_shift (ts : List UInt8) : ∀ (b d : Int),
    ts.scanl (fun x c => x + deltaZ c) (b + d) =
      (ts.scanl (fun x c => x + deltaZ c) b).map (fun x => x + d) := by
  induction ts with
  | nil => intro b d; rw [List.scanl_nil, List.scanl_nil]; rfl
  | cons c ts ih =>
      intro b d
      rw [List.scanl_cons, List.scanl_cons, List.map_cons]
      rw [show b + d + deltaZ c = (b + deltaZ c) + d from by omega, ih]

theorem depthRun_step (c : UInt8) (ts : List UInt8) :
    depthRun (c :: ts) = 0 :: (depthRun ts).map (fun x => x + deltaZ c) := by
  rw [depthRun, List.scanl_cons]
  congr 1
  exact scanl_add_shift ts 0 (deltaZ c)

theorem map_add_add (l : List Int) (a b : Int) :
    (l.map (fun x => x + a)).map (fun x => x + b) = l.map (fun x => x + (a + b)) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      simp only [List.map_cons, ih]
      congr 1
      omega

theorem foldr_max_map_add (ts : List UInt8) (d : Int) :
    ((depthRun ts).map (fun x => x + d)).foldr max 0 =
      max 0 (d + (depthRun ts).foldr max 0) := by
  induction ts generalizing d with
  | nil =>
      rw [depthRun, List.scanl_nil]
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      have hz : max (0 : Int) 0 = 0 := by omega
      rw [hz]
      by_cases hd : 0 ≤ d <;> omega
  | cons c ts ih =>
      rw [depthRun_step]
      simp only [List.map_cons, List.foldr_cons]
      rw [map_add_add (depthRun ts) (deltaZ c) d, ih (deltaZ c + d), ih (deltaZ c)]
      by_cases hd : 0 ≤ d
      · omega
      · have hd' : d < 0 := by omega
        omega

/-- **The clause's number is the counter's run.**  The measured depth is the
maximum of the running depths of the counter's fold over the same token
sequence, so it is read off the counter rather than computed by a second
arithmetic. -/
theorem maxDepthTokens_eq_run_max (ts : List UInt8) :
    maxDepthTokens ts = (depthRun ts).foldr max 0 := by
  induction ts with
  | nil =>
      rw [depthRun, List.scanl_nil]
      show maxDepthTokens [] = max (0 : Int) 0
      rw [show maxDepthTokens [] = (0 : Int) from rfl]
      omega
  | cons c ts ih =>
      rw [maxDepthTokens, ih, depthRun_step, List.foldr_cons]
      rw [foldr_max_map_add]
      omega

def depthAt (bs : Bytes) (i : Nat) : Int := maxDepthTokens (structTokensFrom bs i)

theorem structTokensFrom_none {bs : Bytes} {i : Nat} (h : bs[i]? = none) :
    structTokensFrom bs i = [] := by
  rw [structTokensFrom.eq_def, h]

theorem structTokensFrom_none_succ {bs : Bytes} {i : Nat} (h : bs[i]? = none) :
    bs[i + 1]? = none := by
  have hge : bs.size ≤ i := ge_of_getElem?_eq_none h
  cases hb : bs[i + 1]? with
  | none => rfl
  | some c =>
      have hlt := lt_of_getElem? hb
      omega

theorem structTokensFrom_quote {bs : Bytes} {i : Nat} (h : bs[i]? = some 0x22)
    {cs : List Nat} {stop : { n : Nat // n ≤ bs.size }}
    (hs : scanCharsEnd bs (i + 1) 0 = .ok (cs, stop)) :
    structTokensFrom bs i = structTokensFrom bs stop.val := by
  rw [structTokensFrom.eq_def, h]
  repeat split
  all_goals simp_all
  all_goals rw [hs]

theorem structTokensFrom_step {bs : Bytes} {i : Nat} {c : UInt8}
    (h : bs[i]? = some c) (hc : c ≠ 0x22) :
    structTokensFrom bs i = (if delimTok c then [c] else []) ++ structTokensFrom bs (i + 1) := by
  rw [structTokensFrom.eq_def, h]
  repeat split
  all_goals simp_all

theorem structTokensFrom_inert {bs : Bytes} {i : Nat} {c : UInt8}
    (h : bs[i]? = some c) (hc : c ≠ 0x22) (hd : delimTok c = false) :
    structTokensFrom bs i = structTokensFrom bs (i + 1) := by
  rw [structTokensFrom_step h hc, hd]
  rfl

theorem structTokensFrom_open {bs : Bytes} {i : Nat} {c : UInt8}
    (h : bs[i]? = some c) (hc : c ≠ 0x22) (hd : IsOpenB c = true) :
    structTokensFrom bs i = c :: structTokensFrom bs (i + 1) := by
  rw [structTokensFrom_step h hc, delimTok_open hd]
  rfl

theorem structTokensFrom_close {bs : Bytes} {i : Nat} {c : UInt8}
    (h : bs[i]? = some c) (hc : c ≠ 0x22) (hd : IsCloseB c = true) :
    structTokensFrom bs i = c :: structTokensFrom bs (i + 1) := by
  rw [structTokensFrom_step h hc, delimTok_close hd]
  rfl

/-! ### Skipping inert runs -/

theorem structTokensFrom_run (bs : Bytes) :
    ∀ (i : Nat) (d : Nat), (∀ (k : Nat) (b : UInt8), i ≤ k → k < i + d → bs[k]? = some b →
        b ≠ 0x22 ∧ delimTok b = false) →
      structTokensFrom bs i = structTokensFrom bs (i + d) := by
  intro i d
  induction d generalizing i with
  | zero => intro _; simp
  | succ d ih =>
      intro hrun
      have hstep : structTokensFrom bs i = structTokensFrom bs (i + 1) := by
        cases hb : bs[i]? with
        | none =>
            rw [structTokensFrom_none hb, structTokensFrom_none (structTokensFrom_none_succ hb)]
        | some b =>
            obtain ⟨h1, h2⟩ := hrun i b (by omega) (by omega) hb
            exact structTokensFrom_inert hb h1 h2
      rw [hstep, ih (i + 1) ?_]
      · congr 1; omega
      · intro k b hk hkb hget
        exact hrun k b (by omega) (by omega) hget

theorem ne_quote_of_space {b : UInt8} (h : IsSpaceB b = true) : b ≠ 0x22 ∧ delimTok b = false := by
  have hb : b = 0x20 ∨ b = 0x09 ∨ b = 0x0A ∨ b = 0x0D := by
    simpa [IsSpaceB, Bool.or_eq_true, decide_eq_true_eq, or_assoc] using h
  rcases hb with rfl | rfl | rfl | rfl <;> decide

theorem ne_quote_of_open {b : UInt8} (h : IsOpenB b = true) : b ≠ 0x22 ∧ delimTok b = true := by
  simp only [IsOpenB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | rfl <;> decide

theorem ne_quote_of_close {b : UInt8} (h : IsCloseB b = true) : b ≠ 0x22 ∧ delimTok b = true := by
  simp only [IsCloseB, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | rfl <;> decide

/-- A byte of `spaceRun`'s run is whitespace. -/
theorem spaceRun_space (bs : Bytes) (k : Nat) {b : UInt8} (hk : k < spaceRun bs)
    (hb : bs[k]? = some b) : IsSpaceB b = true := by
  induction bs using ByteString.induction_on generalizing k with
  | h0 => simp [ByteString.getElem?_empty] at hb
  | hs a t ih =>
      rw [spaceRun_cons] at hk
      by_cases hsp : IsSpaceB a = true
      · rw [if_pos hsp] at hk
        cases k with
        | zero =>
            simp only [ByteString.getElem?_cons_zero] at hb
            injection hb with hb
            subst hb
            exact hsp
        | succ m =>
            exact ih m (by omega) (by simpa only [ByteString.getElem?_cons_succ] using hb)
      · rw [if_neg hsp] at hk
        omega

/-- The scan does not see the whitespace `skipFrom` steps over. -/
theorem depthAt_skipFrom (bs : Bytes) (i : Nat) :
    depthAt bs i = depthAt bs (skipFrom bs i) := by
  rw [skipFrom_def]
  have hr : structTokensFrom bs i
      = structTokensFrom bs (i + spaceRun (bs.drop i)) := by
    refine structTokensFrom_run bs i (spaceRun (bs.drop i)) ?_
    intro k b hk hkb hget
    have hdrop : (bs.drop i)[k - i]? = some b := by
      rw [ByteString.getElem?_drop, Nat.add_sub_of_le hk]
      simpa using hget
    have hk' : k - i < spaceRun (bs.drop i) := by omega
    exact ne_quote_of_space (spaceRun_space (bs.drop i) (k - i) hk' hdrop)
  rw [depthAt, depthAt, hr]

theorem depthAt_open_step {bs : Bytes} {i : Nat} {c : UInt8}
    (h : bs[i]? = some c) (ho : IsOpenB c = true) :
    depthAt bs i = depthAt bs (i + 1) + 1 := by
  obtain ⟨hq, _⟩ := ne_quote_of_open ho
  rw [depthAt, structTokensFrom_open h hq ho, maxDepthTokens_open _ ho, depthAt]

theorem depthAt_close_step {bs : Bytes} {i : Nat} {c : UInt8}
    (h : bs[i]? = some c) (hc : IsCloseB c = true) :
    depthAt bs i = max 0 (depthAt bs (i + 1) - 1) := by
  obtain ⟨hq, _⟩ := ne_quote_of_close hc
  rw [depthAt, structTokensFrom_close h hq hc, maxDepthTokens_close _ hc, depthAt]

theorem depthAt_inert_step {bs : Bytes} {i : Nat} {c : UInt8}
    (h : bs[i]? = some c) (hq : c ≠ 0x22) (hd : delimTok c = false) :
    depthAt bs i = depthAt bs (i + 1) := by
  rw [depthAt, structTokensFrom_inert h hq hd, depthAt]

theorem depthAt_quote_step {bs : Bytes} {i : Nat} {cs : List Nat}
    {stop : { n : Nat // n ≤ bs.size }}
    (h : bs[i]? = some 0x22) (hs : scanCharsEnd bs (i + 1) 0 = .ok (cs, stop)) :
    depthAt bs i = depthAt bs stop.val := by
  rw [depthAt, structTokensFrom_quote h hs, depthAt]

/-- The scan takes a number run's bytes without a string or a bracket. -/
theorem numRun_getElem (l : Bytes) (k : Nat) {b : UInt8}
    (h : (numRun l)[k]? = some b) : NumConstituent b = true := by
  induction l using ByteString.induction_on generalizing k with
  | h0 =>
      rw [numRun_empty] at h
      rw [ByteString.getElem?_empty] at h
      exact absurd h (by simp)
  | hs a t ih =>
      rw [numRun_cons] at h
      by_cases hc : NumConstituent a = true
      · rw [if_pos hc] at h
        rcases k with _ | m
        · simp only [ByteString.getElem?_cons_zero] at h
          injection h with h
          subst h
          exact hc
        · exact ih m (by simpa only [ByteString.getElem?_cons_succ] using h)
      · rw [if_neg hc] at h
        rw [ByteString.getElem?_empty] at h
        exact absurd h (by simp)

theorem constituent_inert {b : UInt8} (h : NumConstituent b = true) :
    b ≠ 0x22 ∧ delimTok b = false := by
  have hb : ((((IsDigitB b = true ∨ b = 0x2E) ∨ b = 0x65) ∨ b = 0x45) ∨ b = 0x2B) ∨
      b = 0x2D := by
    simpa [NumConstituent, Bool.or_eq_true, decide_eq_true_eq] using h
  rcases hb with ((((hd | h2) | h3) | h4) | h5) | h6
  · simp only [IsDigitB, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨h1, h2⟩ := hd
    refine ⟨?_, ?_⟩
    · intro heq; rw [heq] at h1; exact absurd h1 (by decide)
    · simp only [delimTok, Bool.or_eq_false_iff]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
        (rw [decide_eq_false_iff_not]; intro heq; rw [heq] at h2; exact absurd h2 (by decide))
  · subst h2; decide
  · subst h3; decide
  · subst h4; decide
  · subst h5; decide
  · subst h6; decide

/-- The document's measured nesting depth: the maximum of the counter's running
depth over the document's structural delimiter sequence, relative to the
position the parser starts at.  A number, because it is compared with the
reference's bound. -/
def docDepth (bs : Bytes) : Int := depthAt bs (skipFrom bs 0)

/-- The measured depth as the bound's own type.  It is never negative, so the
truncation is the identity (`docDepth_nonneg`). -/
def kernelDepthOf (bs : ByteArray) : Nat := (docDepth bs).toNat

theorem docDepth_nonneg (bs : Bytes) : 0 ≤ docDepth bs := by
  rw [docDepth]
  exact maxDepthTokens_nonneg _

/-- Why a document is outside the certified domain.  Every reason names the
clause that failed; the fallback's answer is the reference parser's, and the
outcome is reported as a fallback rather than as a certified refusal. -/
inductive KernelRefusal where
  /-- The empty document is outside every record's domain. -/
  | emptyInput
  /-- The document is longer than the record's input bound. -/
  | inputTooLong (bound : Nat)
  /-- The document nests deeper than the reference's bound admits. -/
  | depthBound (measured : Nat)
  /-- The reference refuses an unpaired surrogate escape at this byte. -/
  | unpairedSurrogate (pos : Nat)
  /-- The reference refuses a noncharacter at this byte. -/
  | noncharacter (pos : Nat)
deriving DecidableEq, Repr

/-- The reason a caller sees for an out-of-domain document. -/
def KernelRefusal.message : KernelRefusal → String
  | .emptyInput =>
      "outside the kernel's domain: the empty document"
  | .inputTooLong bound =>
      s!"outside the kernel's domain: the document is longer than {bound} bytes"
  | .depthBound measured =>
      s!"outside the kernel's domain: the document nests {measured} levels deep, past the {kernelMaxDepth} the reference admits"
  | .unpairedSurrogate pos =>
      s!"outside the kernel's domain: the reference refuses an unpaired surrogate at byte {pos}"
  | .noncharacter pos =>
      s!"outside the kernel's domain: the reference refuses a noncharacter at byte {pos}"

/-- The character-policy check at one byte: if it is a quote, the reference's
own body scanner runs on the body and its policy refusal is reported at the
byte the reference names.  The scan is the reference's (`scanCharsEnd`), so the
reason and position are the reference's, not a second implementation's. -/
def policyRefusalAt (doc : ByteArray) (i : Nat) : Option KernelRefusal :=
  if doc[i]? = some 0x22 then
    match scanCharsEnd doc (i + 1) 0 with
    | .error (.unpairedSurrogate off) => some (.unpairedSurrogate (i + 1 + off))
    | .error (.noncharacter off) => some (.noncharacter (i + 1 + off))
    | _ => none
  else none

/-- The document's first character-policy refusal, at the byte the reference
names. -/
def policyRefusal (doc : ByteArray) : Option KernelRefusal :=
  (List.range doc.size).findSome? (policyRefusalAt doc)

/-- Whether the document carries a quote whose body the reference refuses under
its character policy. -/
def policyScan (doc : ByteArray) : Bool :=
  (policyRefusal doc).isSome

/-- The certified domain's decision procedure.  `ok` admits the document to the
native pipeline; `error` names the clause that kept it out.  The reason order is
the one the route reports: empty, over-long, too deep, then the character
policy. -/
def admission (doc : ByteArray) : Except KernelRefusal Unit :=
  if doc.size = 0 then .error .emptyInput
  else if kernelMaxInput < doc.size then .error (.inputTooLong kernelMaxInput)
  else if (kernelMaxDepth : Int) < docDepth doc then
    .error (.depthBound (docDepth doc).toNat)
  else
    match policyRefusal doc with
    | some r => .error r
    | none => .ok ()

/-- `admission`'s yes-or-no projection, for a caller that has no room for the
reason. -/
def admitted (doc : ByteArray) : Bool := (admission doc).isOk

/-! ### The buffers the wrapper constructs from the input length

None of these is an admission clause: the record's staging pre is discharged by
construction from `doc.size`.  `kernelEpCap` is the entry stream's capacity
(`64` entries per block plus the emitter's nine-entry reserve), `kernelXpCap`
the escape list's, `kernelDstCap` the arena's (`n + 64` for the expander's
decoding slack) and `kernelEvCap` the event stream's (`13` bytes per input
byte at the encoding's worst case).  They are here so the probe and the library
size the same buffers from the same numbers. -/

/-- The document's 64-byte blocks. -/
def kernelBlocks (n : Nat) : Nat := (n + 63) / 64

/-- The entry stream's capacity, in words. -/
def kernelEpCap (n : Nat) : Nat := 64 * kernelBlocks n + 9

/-- The escape list's capacity, in words. -/
def kernelXpCap (n : Nat) : Nat := 64 * kernelBlocks n + 8

/-- The arena's capacity, in bytes. -/
def kernelDstCap (n : Nat) : Nat := n + 64

/-- The event stream's capacity, in bytes. -/
def kernelEvCap (n : Nat) : Nat := 13 * n + 128

/-- The staged document window's base: three bytes of prefix room and the
32-byte read-past tail.  The probe stages the window at address 0, so the
document's base is this. -/
def kernelBase : Nat := 3

end LeanLLVM.Refinement
