/-
The emitted stage-2 body's stores and its number path, against `Γ_stage2`.

`JsonStage2Contract` states the record `leanllvm_json_stage2` satisfies and does
not exhibit a body for it.  This module is the part of that body a proof in this
slice can reach, and it says which part that is:

* **the output layer, modelled from the emitted text and proved.**  Every write
  `stage2.c` makes to the caller's event stream goes through `out_raw`, and every
  write it makes to the caller's arena is the decoder's, at `z->ar + z->alen`
  after `z_arena_reserve` has checked the reserve.  `outBlob`/`emitBlobs` model
  the first and `arenaAppend` the second; the theorems say where the bytes land,
  what the cursor becomes, that a reserve violation is a refusal rather than a
  write, and that nothing outside the written extent changes.  The ABI wrapper's
  own three stores and its verdict are modelled by `stage2Report` and
  `stage2Verdict`, and `stage2Run_boundary` turns a walk's report into
  `Γ_stage2`'s post at those stores.
* **the number path, dispatched and composed.**  The replacement's observable is
  binary64 and its specification is `strtodSpec`; `num_fast_el1` dispatches to
  three classes, and the three conversions are proved elsewhere
  (`StrtodTier1.emittedRefinesOn_tier1`, `ElGuardRefine.elGuardRefinesOn`,
  `StrtodTier3.emittedRefinesOn_tier3`) at models the dispatch does not name.
  `numClassOf` is the dispatch as the emitted tests read, `numEff` is the
  emitted `eff` with its saturating accumulator, and the theorems below prove
  that the emitted tests select exactly `StrtodRefine`'s classes at the
  accumulators they read — so the three proved models compose at one function,
  `numFastEmitted`, and `numFastEmitted_strtodSpec` is
  `∀ d, d.wellFormed → numFastEmitted d.lexeme = strtodSpec d`.

# The pin

`stage2Src` is the emitted text, and the `#guard`s below are the pin: each one
asserts that a line the model encodes is present in `kernel/json/stage2.c`
verbatim.  It is a *text* pin, not an instruction pin — it does not see the
emission of that text — and it is checked when this module is elaborated, so a
change to the source that the model does not carry fails elaboration rather than
leaving the model describing a file that has moved.  `stage2Src_control` shows
the same search finds nothing when the text is not there, so the marker is known
to discriminate: presence would otherwise be provable by a search that matches
nothing.

# What is proved, and what is not

Proved below:

* the emitters' writes, cursors and frames, with the fault (`__builtin_trap`) as
  the emitter's `none` rather than as a write;
* the ABI wrapper's stores: the two cursors always, the refusal slot exactly on
  refusal, and the verdict's two values;
* `stage2Run_boundary`: given a staging and a walk report in the record's own
  vocabulary, the emitted wrapper's stores make `Γ_stage2`'s post true — the
  verdict, both cursors with their growth bounds, the arena and event prefixes,
  the refusal word's two sides, and the frame as `Owns`;
* the report's clauses, and the two walk facts they are read from: the reserve's
  slack (`Stage2Run.reserve_of_arenaLe`), `Owns` at the extent the post names
  (`Stage2Run.walkOwning_of_written`, from the walk's own write extent and the
  caller's staging), both cursors' bounds from the walk facts
  (`Stage2Run.arenaLe_of_spans`, `Stage2Run.evLe_of_oneRecordPerEntry`), with the
  entry count (`Stage2Run.nep_le`) and the records' thirteen-bytes-per-entry sum
  (`records_total_le`, `evlen_le_of_records`) proved outright;
* the completion budget, **stated and not claimed**: `Stage2WalkCompletes` is
  completion at `stage2Budget` at the ABI's thirteen arguments, its value is the
  three-word term `stage2Budget_at_abi`, the adapter reads the same number
  (`Γ_stage2at_budget`), and `stage2WalkObligation_iff_completion` proves the
  standalone statement is exactly the obligation's first conjunct — so the loop's
  budget is named where its consumer reads it, and what is missing is the loop;
* the number path: the emitted dispatch's counters are the specification's, its
  three classes are `Tier1`, `Tier2` and `Fallback` at the kernel's decision,
  and the three proved tier models therefore compose to
  `EmittedConversionRefines numFastEmitted kernelDecides`, hence to
  `strtodSpec` on every well-formed lexeme.

Not proved, and named with the obligation each would need:

* **the walk's loop.**  `s2_walk`'s emitted body is pinned in
  `LeanLLVM/Refinement/JsonStage2IR.lean` — `stage2Body` is
  `probes/install/ir/stage2.candidate.ll` parsed, with the derivation recorded
  there (the number path's binary64 helpers out of line, the eight staging objects
  flattened to parameters) — and `stage2Calls` is the call environment the body's
  census closes over.  The obligation is `Stage2WalkObligation`, a `Satisfies`
  instance for that body at the adapter's record; `stage2_walk_yields_record`
  turns it into this record's post at the ABI's thirteen arguments, and
  `satisfies_calls_stage2` turns it into the `CallSatisfies` the pipeline's
  stage-2 slot takes.  What is not proved is the loop: its first conjunct is a
  completion budget for a 165-block body, and `Stage2Run`'s fields are the report
  it produces once reached — the arena cursor `alen` and its bound
  `alen ≤ ndst0 + n`, the event cursor `evlen` and its bound `evlen ≤ nev0 + 13 * n`,
  the last reserve's slack `alen + 64 ≤ dstcap`, the walk's region claim `Owns`
  over `[(dst, alen + 64), (ev, evlen)]`, the refusal bit, and the offset's bound
  `eoff ≤ n`.  Each is a clause `Γ_stage2`'s post names, so the walk's obligation
  is still stated in the record's vocabulary rather than in this module's.  The
  budget is stated at the ABI's arguments in *The completion budget, stated*, and
  the clauses are reduced there to what the loop's trace must carry: the reserve's
  slack and `Owns` follow from the arena's bound, the caller's capacity and the
  walk's write extent; both cursors' bounds follow from the two walk facts, whose
  arithmetic is proved; the refusal bit and `eoff ≤ n` remain the loop's own,
  because nothing in the record's vocabulary names the run's state at the refusal
  arm.
* **the emitters' invocation trace.**  `emitBlobs_len_le` bounds the cursor by
  `13 * n` when at most `n` blobs of at most thirteen bytes each are emitted, and
  `arenaAppend` bounds the arena by the body's own length.  That there is at most
  one event record per entry, and that the escaped bodies' lengths sum inside the
  document, are walk facts (`Stage2OneRecordPerEntry`, `Stage2SpansInside`); what
  is proved here is what each buys — `evlen_le_of_records` from the record
  grouping, `arenaLe_of_spans` from the extents — and what the loop owes is the
  trace that satisfies them.
* **the number path's locals.**  `numEff` and the mantissa read `d`'s
  decomposition, which is what `StrtodReader.reader` returns; that the emitted
  accumulators `ip`, `fr`, `idig`, `fdig`, `exp10` equal those fields is the
  per-local agreement `StrtodReader`'s docstring names — including `num_d8_el1`'s
  eight-digit group value and the two caps (`idig < 19`, `exp10 < 100000`).  The
  caps are inert on the branches proved here (`numEff_eq_eff_of_gate`,
  `numMant`), which is why the agreement that remains is an equality of values
  and not a second arithmetic.
* **`num_fast_el1`'s control flow.**  `numClassOf` is the emitted nest of tests
  as the source writes it, pinned by text; that the compiled branch structure is
  that nest is an emission question, not a model question.

The one place the number path *does* reach an unproved platform statement is
tier 1's, and it is inherited: `emittedRefinesOn_tier1` identifies the single
IEEE operation with `roundMag`, which `StrtodTier1`'s docstring states and this
module does not add to or weaken.
-/
import LeanLLVM.Refinement.JsonStage2Contract
import LeanLLVM.Refinement.JsonStage2IR
import LeanLLVM.StrtodReader
import LeanLLVM.ElGuardRefine

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open ByteString
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_writeBytes_frame)
open LeanLLVM.StrtodRefine (Tier1 Tier2 Tier2Eligible Fallback IsNormal IsSubnormal IsTie
  EmittedRefinesOn EmittedConversionRefines digitCount eff expValue fracDigits intDigits
  branch_cover)

/-! ### The emitted text, and the pin

The pin's marker is a substring search: `occurs hay needle` is `true` exactly when
`needle` appears in `hay`, as a list of characters.  A `#guard` rather than a
proposition for the reason `JsonEntryIR`'s pin gives: the search runs on `String`
primitives, which the kernel does not reduce, so a proposition about it could not
be closed by reflexivity.  What the pin buys is that a line the model encodes
below is a line of the file beside it. -/

/-- `kernel/json/stage2.c`, as this module reads it. -/
def stage2Src : String := include_str "../../kernel/json/stage2.c"

/-- `needle` occurs in `hay`. -/
def occurs (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

-- The marker discriminates: the same search, on a mutation of a line that *is*
-- present, reports absence.  Without this control a marker that matched nothing
-- would satisfy every presence check below; with it, the checks above are known
-- to be about the text.
#guard !occurs stage2Src "if (z->alen + need <= z->acap) return; // absent"

-- The arena's reserve, its fault, and its slack (`stage2.c:59-62`, `:834-841`).
#guard occurs stage2Src "#define US_SLACK 64"
#guard occurs stage2Src "if (z->alen + need <= z->acap) return;"
-- The event stream's reserve and its fault (`stage2.c:79-87`).
#guard occurs stage2Src "if (o->len + need <= o->cap) return;"
-- The two faults are the same emitted statement, and there are two of them.
#guard (stage2Src.splitOn "__builtin_trap();").length = 3
-- `out_raw`'s store and the emitters built on it (`stage2.c:103-114`).
#guard occurs stage2Src "o->len += n;"
#guard occurs stage2Src "static inline void out_tag(Out *o, uint8_t t) { out_raw(o, &t, 1); }"
-- The record's thirteen bytes (`stage2.c:1197-1205`).
#guard occurs stage2Src "out_reserve(&z->ev, 13);"
#guard occurs stage2Src "e[0] = (uint8_t)(key ? T_KEY : T_STR);"
#guard occurs stage2Src "memcpy(e + 1, &ol, 4);"
#guard occurs stage2Src "memcpy(e + 5, &rec, 8);"
#guard occurs stage2Src "z->ev.len += 13;"
-- The arena's reserve and the escaped body's cursor (`stage2.c:1170-1185`).
#guard occurs stage2Src "z_arena_reserve(z, (size_t)len + US_SLACK);"
#guard occurs stage2Src "z->alen += outn;"
-- The wrapper's three stores and its verdict (`stage2.c:1286-1291`).
#guard occurs stage2Src "uint64_t r = s2_walk(&s, S2_VAL | S2_STR | S2_EV, &z, &e);"
#guard occurs stage2Src "*ndst = (uint64_t)z.alen;"
#guard occurs stage2Src "*nev = (uint64_t)z.ev.len;"
#guard occurs stage2Src "if (!r) *err = e.off;"
#guard occurs stage2Src "return r ? 1 : 0;"
-- The record tags (`stage2.c:103-106`, `:1197`): a number's record is tag 7.
#guard occurs stage2Src "T_OBJ = 1, T_OBJ_END = 2, T_ARR = 3, T_ARR_END = 4"
#guard occurs stage2Src "T_KEY = 5, T_STR = 6, T_NUM = 7"
-- The number dispatch (`stage2.c:424-460`).
#guard occurs stage2Src "int64_t eff = exp10 - (int64_t)fdig;"
#guard occurs stage2Src "uint64_t nd = idig + fdig;"
#guard occurs stage2Src "if (nd <= 19 && eff >= EPOW_MIN && eff <= EPOW_MAX) {"
#guard occurs stage2Src "if (nd <= 15 && eff >= -22 && eff <= 22) {"
#guard occurs stage2Src "if (num_el_el1(mant, eff, &d)) {"
#guard occurs stage2Src "uint64_t mant = ip * NUMF_EL1_P10[fdig] + fr;"
-- The two caps the counter model is inert under (`stage2.c:390`, `:418`).
#guard occurs stage2Src "if (idig < 19) ip = ip * 10 + (uint64_t)(p[i] - '0');"
#guard occurs stage2Src "if (exp10 < 100000) exp10 = exp10 * 10 + (int64_t)(p[i] - '0');"
#guard occurs stage2Src "#define EPOW_MIN (-45)"
#guard occurs stage2Src "#define EPOW_MAX (45)"

/-! ### The event stream's writer

`out_raw` in the event stream's mode (`o->hash = 0`, which `z_init` fixes for
`z->ev`): reserve, store, advance.  The reserve's violation is
`__builtin_trap()`, and a trap is not an outcome the record describes, so the
model has no result there — `none`, which no theorem below consumes as a
success. -/

/-- One blob of the event stream, as `out_raw` writes it: the caller's buffer at
its cursor, and the cursor advanced by the blob's length.  `none` is the reserve
check's fault. -/
def outBlob (mem : Mem) (ev len cap : Nat) (bs : List UInt8) : Option (Mem × Nat) :=
  if len + bs.length ≤ cap then some (writeBytes mem (ev + len) bs, len + bs.length)
  else none

/-- `out_tag`: one byte. -/
def outTag (mem : Mem) (ev len cap : Nat) (t : Nat) : Option (Mem × Nat) :=
  outBlob mem ev len cap [UInt8.ofNat t]

/-- `out_u64`: the eight bytes of `v`, low byte first (`natToBytes`'s order). -/
def outU64 (mem : Mem) (ev len cap : Nat) (v : Nat) : Option (Mem × Nat) :=
  outBlob mem ev len cap (wordBytes 8 v)

/-- `T_NUM` (`stage2.c:104`). -/
def stage2TagNum : Nat := 7

/-- The number record's payload: tag `T_NUM` and the eight bytes of the value's
`toBits`.  Nine bytes, within the record's thirteen. -/
def numberRecord (bits : Nat) : List (List UInt8) :=
  [[UInt8.ofNat stage2TagNum], wordBytes 8 bits]

/-- A sequence of blobs, each reserved and written in turn.  This is the shape of
the walk's event writes: `out_tag`, `out_u64`, and the thirteen-byte record are
all one call each, and the fold's cursor is the caller's own `*nev`. -/
def emitBlobs (mem : Mem) (ev len cap : Nat) : List (List UInt8) → Option (Mem × Nat)
  | [] => some (mem, len)
  | b :: bs =>
      match outBlob mem ev len cap b with
      | none => none
      | some p => emitBlobs p.1 ev p.2 cap bs

/-- The fold's empty case, by definition. -/
theorem emitBlobs_nil (mem : Mem) (ev len cap : Nat) :
    emitBlobs mem ev len cap [] = some (mem, len) := rfl

/-- The fold's cons case, by definition. -/
theorem emitBlobs_cons (mem : Mem) (ev len cap : Nat) (b : List UInt8)
    (bs : List (List UInt8)) :
    emitBlobs mem ev len cap (b :: bs) =
      (match outBlob mem ev len cap b with
       | none => none
       | some p => emitBlobs p.1 ev p.2 cap bs) := rfl

/-- Writing two byte runs in turn is writing their concatenation. -/
theorem writeBytes_append (mem : Mem) (start : Nat) :
    ∀ (a b : List UInt8),
      writeBytes mem start (a ++ b) = writeBytes (writeBytes mem start a) (start + a.length) b
  | [], _ => rfl
  | x :: xs, b => by
      show writeBytes (writeByte mem start x) (start + 1) (xs ++ b) =
        writeBytes (writeBytes (writeByte mem start x) (start + 1) xs)
          (start + (xs.length + 1)) b
      rw [writeBytes_append (writeByte mem start x) (start + 1) xs b]
      congr 1
      omega

/-- A successful blob is the store it describes. -/
theorem outBlob_spec {mem : Mem} {ev len cap : Nat} {bs : List UInt8}
    {mem' : Mem} {len' : Nat} (h : outBlob mem ev len cap bs = some (mem', len')) :
    mem' = writeBytes mem (ev + len) bs ∧ len' = len + bs.length := by
  unfold outBlob at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Option.some.inj h
    exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

/-- A successful fold stores the blobs' concatenation at the cursor it started
from, and returns the cursor past it. -/
theorem emitBlobs_spec {mem : Mem} {ev len cap : Nat} {blobs : List (List UInt8)}
    {mem' : Mem} {len' : Nat} (h : emitBlobs mem ev len cap blobs = some (mem', len')) :
    mem' = writeBytes mem (ev + len) blobs.flatten ∧
      len' = len + blobs.flatten.length := by
  induction blobs generalizing mem len with
  | nil =>
      rw [emitBlobs_nil] at h
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      exact ⟨rfl, rfl⟩
  | cons b bs ih =>
      rw [emitBlobs_cons] at h
      cases hb : outBlob mem ev len cap b with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some p =>
          obtain ⟨m1, l1⟩ := p
          rw [hb] at h
          obtain ⟨hm1, hl1⟩ := outBlob_spec hb
          have h' := ih (mem := m1) (len := l1) h
          obtain ⟨hm', hl'⟩ := h'
          subst hm1 hl1
          refine ⟨?_, ?_⟩
          · rw [hm', List.flatten_cons, writeBytes_append]
            congr 1
            omega
          · rw [hl']
            simp only [List.flatten_cons, List.length_append]
            omega

/-- The fold changes nothing outside the extent from its cursor: the three
constants, the record's thirteen bytes and the tag's one, are all inside it. -/
theorem emitBlobs_frame {mem : Mem} {ev len cap : Nat} {blobs : List (List UInt8)}
    {mem' : Mem} {len' : Nat} (h : emitBlobs mem ev len cap blobs = some (mem', len')) :
    UnchangedOn (inRegions [(ev + len, blobs.flatten.length)]) mem mem' := by
  obtain ⟨hm', hl'⟩ := emitBlobs_spec h
  subst hm'
  intro a ha
  have hout : ¬ (ev + len ≤ a ∧ a < ev + len + blobs.flatten.length) :=
    fun hc => ha ⟨(ev + len, blobs.flatten.length), List.mem_cons_self .., hc.1, hc.2⟩
  refine readByte_writeBytes_outside mem blobs.flatten ?_
  by_cases hlt : a < ev + len
  · exact Or.inl hlt
  · exact Or.inr (by omega)

/-- The blobs' total is their widths' sum. -/
theorem flatten_length (blobs : List (List UInt8)) :
    blobs.flatten.length = (blobs.map List.length).sum := by
  induction blobs with
  | nil => rfl
  | cons b bs ih => simp [List.flatten_cons, ih]

/-- A list of widths each at most `w` sums to at most `w` times its length. -/
theorem sum_le_mul_length {w : Nat} :
    ∀ {l : List Nat}, (∀ x ∈ l, x ≤ w) → l.sum ≤ w * l.length
  | [], _ => by simp
  | x :: xs, hw => by
      have hx : x ≤ w := hw x (List.mem_cons_self ..)
      have hxs : ∀ y ∈ xs, y ≤ w := fun y hy => hw y (List.mem_cons_of_mem x hy)
      have ih := sum_le_mul_length hxs
      simp only [List.sum_cons, List.length_cons]
      rw [Nat.mul_succ]
      omega

/-- A list of widths each at most `w`, over at most `n` blobs, sums to at most
`w * n`. -/
theorem sum_le_of_forall_le {w : Nat} {l : List Nat} {n : Nat}
    (hwidth : ∀ x ∈ l, x ≤ w) (hcount : l.length ≤ n) : l.sum ≤ w * n := by
  have h1 := sum_le_mul_length hwidth
  have h2 : w * l.length ≤ w * n := Nat.mul_le_mul_left w hcount
  omega

/-- **The event stream's cursor stays inside the record's promise.**  If the walk
emits at most one record per input byte and no record is wider than
`stage2RecordBytes`, then the cursor the fold returns is at most
`nev0 + 13 * n` — the bound `Γ_stage2`'s post states and `pipelineStaging`
already carries. -/
theorem emitBlobs_len_le {mem : Mem} {ev len cap n : Nat} {blobs : List (List UInt8)}
    {mem' : Mem} {len' : Nat}
    (hwidth : ∀ b ∈ blobs, b.length ≤ stage2RecordBytes)
    (hcount : blobs.length ≤ n)
    (h : emitBlobs mem ev len cap blobs = some (mem', len')) :
    len' ≤ len + stage2RecordBytes * n := by
  obtain ⟨-, hl'⟩ := emitBlobs_spec h
  rw [hl']
  have hsum : blobs.flatten.length ≤ stage2RecordBytes * n := by
    rw [flatten_length]
    exact sum_le_of_forall_le (l := blobs.map List.length)
      (fun x hx => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        exact hwidth b hb) (by simpa using hcount)
  omega

/-- The number record is nine bytes: the tag and the value's eight. -/
theorem numberRecord_width (bits : Nat) :
    ((numberRecord bits).flatten).length = 1 + 8 := by
  unfold numberRecord
  simp [wordBytes, natToBytes_length]

/-- The number record is within the record's thirteen bytes. -/
theorem numberRecord_le (bits : Nat) :
    ((numberRecord bits).flatten).length ≤ stage2RecordBytes := by
  rw [numberRecord_width, stage2RecordBytes]
  omega

/-! ### The arena

`z_arena_reserve(z, len + US_SLACK)` refuses a reserve that does not fit, then
the escaped body's decoder writes at `dst` and the walk advances `z->alen` by the
decoded length.  `arenaAppend` is that step: the reserve check at the body's own
length plus the slack, the decoder's `on` bytes at the cursor, and the cursor
advanced.  The decoder is a call (`leanllvm_json_escape_expand`), so its write is
the caller's `bs` parameter with `on = bs.length`, and `on ≤ len` is the escape
unit's own post — the decoded form is never longer than its input. -/

/-- One escaped body's arena step: the reserve at `len + 64`, `on` bytes written
at the cursor, and the cursor advanced by `on`.  `none` is the reserve's fault,
or a decoder result longer than the body it decoded. -/
def arenaAppend (mem : Mem) (dst alen acap : Nat) (len on : Nat) (bs : List UInt8) :
    Option (Mem × Nat) :=
  if alen + len + stage2ArenaReserve ≤ acap ∧ on = bs.length ∧ on ≤ len then
    some (writeBytes mem (dst + alen) bs, alen + on)
  else none

/-- A successful append stores at the cursor and advances by the decoded length. -/
theorem arenaAppend_spec {mem : Mem} {dst alen acap len on : Nat} {bs : List UInt8}
    {mem' : Mem} {alen' : Nat} (h : arenaAppend mem dst alen acap len on bs = some (mem', alen')) :
    mem' = writeBytes mem (dst + alen) bs ∧ alen' = alen + on ∧ on = bs.length ∧ on ≤ len := by
  unfold arenaAppend at h
  split at h
  · obtain ⟨hcap, hon, hle⟩ := ‹_ ∧ _ ∧ _›
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    exact ⟨rfl, rfl, hon, hle⟩
  · exact absurd h (by simp)

/-- The reserve the append checked is the one whose slack the record's post names:
a successful append keeps the cursor's reserve inside the capacity. -/
theorem arenaAppend_reserve {mem : Mem} {dst alen acap len on : Nat} {bs : List UInt8}
    {mem' : Mem} {alen' : Nat} (h : arenaAppend mem dst alen acap len on bs = some (mem', alen')) :
    alen + len + stage2ArenaReserve ≤ acap := by
  unfold arenaAppend at h
  split at h
  · exact ‹_ ∧ _ ∧ _›.1
  · exact absurd h (by simp)

/-- The append changes nothing outside the bytes it wrote. -/
theorem arenaAppend_frame {mem : Mem} {dst alen acap len on : Nat} {bs : List UInt8}
    {mem' : Mem} {alen' : Nat} (h : arenaAppend mem dst alen acap len on bs = some (mem', alen')) :
    UnchangedOn (inRegions [(dst + alen, on)]) mem mem' := by
  obtain ⟨hm', -, hon, -⟩ := arenaAppend_spec h
  subst hm'
  subst hon
  intro a ha
  have hout : ¬ (dst + alen ≤ a ∧ a < dst + alen + bs.length) :=
    fun hc => ha ⟨(dst + alen, bs.length), List.mem_cons_self .., hc.1, hc.2⟩
  refine readByte_writeBytes_outside mem bs ?_
  by_cases hlt : a < dst + alen
  · exact Or.inl hlt
  · exact Or.inr (by omega)

/-! ### The ABI wrapper

`leanllvm_json_stage2`'s tail (`stage2.c:1286-1291`) is four statements: the walk
runs, the two cursors are stored back, the refusal offset is stored when the walk
refused, and the return is `r ? 1 : 0`.  `stage2Report` is the stores and
`stage2Verdict` the word.  The model writes the refusal slot first; the three
objects are separate (the record's pre says so, `DisjointRegions`), so the order
among them is immaterial to the memory a caller observes, which is the only thing
the lemmas below read. -/

/-- The wrapper's return word (`stage2.c:1291`): `r ? 1 : 0`, where `refusal` is
`r = 0`. -/
def stage2Verdict (refusal : Bool) : BitVec 64 := if refusal then 0 else 1

/-- The wrapper's stores, as a memory transformer: `*err` when the walk refused,
then `*nev` and `*ndst` always, each an eight-byte word. -/
def stage2Report (mem : Mem) (ndst nev err : Nat) (alen evlen : Nat) (refusal : Bool)
    (eoff : Nat) : Mem :=
  writeBytes
    (writeBytes (if refusal then writeBytes mem err (wordBytes 8 eoff) else mem)
      nev (wordBytes 8 evlen))
    ndst (wordBytes 8 alen)

/-- An eight-byte word written at an address reads back there. -/
theorem readBytes_wordBytes_same {mem : Mem} {addr v : Nat} :
    readBytes (writeBytes mem addr (wordBytes 8 v)) addr 8 = some (wordBytes 8 v) := by
  have h := readBytes_writeBytes_same mem (wordBytes 8 v) (addr := addr)
  rwa [show (wordBytes 8 v).length = 8 from natToBytes_length v 8] at h

/-- A store of an eight-byte word does not disturb a range that ends at or below
it, or starts at or above its end. -/
theorem readBytes_wordBytes_frame {mem : Mem} {addr v p n : Nat}
    (h : p + n ≤ addr ∨ addr + 8 ≤ p) :
    readBytes (writeBytes mem addr (wordBytes 8 v)) p n = readBytes mem p n := by
  refine readBytes_writeBytes_frame mem (wordBytes 8 v) addr p n ?_
  rwa [show (wordBytes 8 v).length = 8 from natToBytes_length v 8]

/-- A single byte outside an eight-byte word's store is unchanged. -/
theorem readByte_wordBytes_outside {mem : Mem} {addr v a : Nat}
    (h : a < addr ∨ addr + 8 ≤ a) :
    readByte (writeBytes mem addr (wordBytes 8 v)) a = readByte mem a := by
  have hlen : (wordBytes 8 v).length = 8 := natToBytes_length v 8
  rw [← hlen] at h
  exact readByte_writeBytes_outside mem (wordBytes 8 v) h

/-- The verdict is the ABI's word: `0` or `1`, and nothing else. -/
theorem stage2Verdict_range (refusal : Bool) :
    stage2Verdict refusal = 0 ∨ stage2Verdict refusal = 1 := by
  cases refusal <;> simp [stage2Verdict]

/-- The arena cursor is reported back at `*ndst`: the last store is that one, so
the read-back needs nothing about the other slots. -/
theorem stage2Report_ndst (mem : Mem) (ndst nev err : Nat) (alen evlen : Nat)
    (refusal : Bool) (eoff : Nat) :
    readBytes (stage2Report mem ndst nev err alen evlen refusal eoff) ndst 8 =
      some (wordBytes 8 alen) := by
  unfold stage2Report
  rw [readBytes_wordBytes_same]

/-- The event cursor is reported back at `*nev`, when the cursor slot is not the
arena's. -/
theorem stage2Report_nev {mem : Mem} {ndst nev err : Nat} {alen evlen : Nat}
    {refusal : Bool} {eoff : Nat} (hdisj : ndst + 8 ≤ nev ∨ nev + 8 ≤ ndst) :
    readBytes (stage2Report mem ndst nev err alen evlen refusal eoff) nev 8 =
      some (wordBytes 8 evlen) := by
  unfold stage2Report
  rw [readBytes_wordBytes_frame (p := nev) (n := 8) (by omega)]
  rw [readBytes_wordBytes_same]

/-- On refusal the refusal slot carries the walk's offset. -/
theorem stage2Report_err_refusal {mem : Mem} {ndst nev err : Nat} {alen evlen eoff : Nat}
    (hnd : ndst + 8 ≤ err ∨ err + 8 ≤ ndst)
    (hnv : nev + 8 ≤ err ∨ err + 8 ≤ nev) :
    readBytes (stage2Report mem ndst nev err alen evlen true eoff) err 8 =
      some (wordBytes 8 eoff) := by
  unfold stage2Report
  rw [readBytes_wordBytes_frame (p := err) (n := 8) (by omega)]
  rw [readBytes_wordBytes_frame (p := err) (n := 8) (by omega)]
  rw [ite_eq_left rfl]
  rw [readBytes_wordBytes_same]

/-- On acceptance the refusal slot is not written, so a caller reads what it
staged. -/
theorem stage2Report_err_accept {mem : Mem} {ndst nev err : Nat} {alen evlen eoff : Nat}
    (hnd : ndst + 8 ≤ err ∨ err + 8 ≤ ndst)
    (hnv : nev + 8 ≤ err ∨ err + 8 ≤ nev) :
    readBytes (stage2Report mem ndst nev err alen evlen false eoff) err 8 =
      readBytes mem err 8 := by
  unfold stage2Report
  rw [readBytes_wordBytes_frame (p := err) (n := 8) (by omega)]
  rw [readBytes_wordBytes_frame (p := err) (n := 8) (by omega)]
  rw [ite_eq_right (by decide)]

/-- Every byte the wrapper writes is in one of the three slots, whichever the
verdict: the refusal slot is a store or nothing, and the two cursors are stores. -/
theorem stage2Report_frame (mem : Mem) (ndst nev err : Nat) (alen evlen : Nat)
    (refusal : Bool) (eoff : Nat) :
    UnchangedOn (inRegions [(ndst, 8), (nev, 8), (err, 8)]) mem
      (stage2Report mem ndst nev err alen evlen refusal eoff) := by
  intro a ha
  have houtNdst : ¬ (ndst ≤ a ∧ a < ndst + 8) :=
    fun hc => ha ⟨(ndst, 8), by simp, hc.1, hc.2⟩
  have houtNev : ¬ (nev ≤ a ∧ a < nev + 8) :=
    fun hc => ha ⟨(nev, 8), by simp, hc.1, hc.2⟩
  have houtErr : ¬ (err ≤ a ∧ a < err + 8) :=
    fun hc => ha ⟨(err, 8), by simp, hc.1, hc.2⟩
  unfold stage2Report
  rw [readByte_wordBytes_outside (by
    rcases Nat.lt_or_ge a ndst with h | h
    · exact Or.inl h
    · exact Or.inr (by have := houtNdst; omega))]
  rw [readByte_wordBytes_outside (by
    rcases Nat.lt_or_ge a nev with h | h
    · exact Or.inl h
    · exact Or.inr (by have := houtNev; omega))]
  cases refusal
  · rfl
  · exact readByte_wordBytes_outside (by
      rcases Nat.lt_or_ge a err with h | h
      · exact Or.inl h
      · exact Or.inr (by have := houtErr; omega))

/-! ### The staging and the walk's report, in the record's vocabulary

`s2_walk`'s body is pinned in `JsonStage2IR`; what its loop owes the wrapper is
exactly the record's own post, minus the wrapper's four statements:
the two cursors it left, its refusal and that refusal's offset, the region it
wrote, and the reserve its last arena append checked.  `Stage2Run` is that
object, spelled in `Γ_stage2`'s pre and post vocabulary rather than this module's,
so the obligation the missing walk carries is stated where its consumer reads it.
`Stage2Run.pre` proves the record's precondition from the staging half, and
`stage2Run_boundary` proves the record's post at `stage2Report` from the report
half. -/

/-- The caller's staging (`stage2Pre`'s clauses) and the walk's report, at the
record's own numbers.  The first twenty-one fields are the pre, clause for
clause; `arenaGe` onwards are the post's clauses about the walk. -/
structure Stage2Run (args : List Value) (mem m0 : Mem) where
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
  /-- The arena's cursor as the walk left it. -/
  alen : Nat
  /-- The event stream's cursor as the walk left it. -/
  evlen : Nat
  /-- The walk's refusal, as the wrapper's input: the bit `stage2Verdict` coerces
  to the verdict word.  That it is `s2_walk`'s C return is the flattening's
  re-indexing, not a clause — the flattened body's return is a register the
  wrapper reads, while `Satisfies` relates an outcome and the memory it leaves,
  so no record can state the equality. -/
  refusal : Bool
  /-- The refusal offset: the number the wrapper stores at the refusal slot on
  refusal, whose store `stage2Boundary_of_parts` reads back as `errRefuse`.  The
  record carries the number; the store is the wrapper's. -/
  eoff : Nat
  /-- The arguments are `stage2.h`'s thirteen slots. -/
  args_eq : args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
    .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
    .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
    .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err]
  /-- The document is readable. -/
  doc : readBytes mem b n = some bs
  /-- The decoder's read-past tail is staged. -/
  tail : HasBytes mem (b + n) stage2ReadTail
  /-- The entry stream is readable. -/
  entries : readLanes32 mem ep nep = some ent
  /-- The entry positions are in document order. -/
  order : ent.Pairwise (· < ·)
  /-- The entry positions are inside the document. -/
  inside : ∀ q ∈ ent, q < n
  /-- The escape list's bytes are staged. -/
  esc : HasBytes mem xp (4 * nxp)
  /-- The arena is staged. -/
  arenaCap : HasBytes mem dst dstcap
  /-- The arena has room for the document and the decoder's slack. -/
  arenaRoom : ndst0 + n + stage2ArenaReserve ≤ dstcap
  /-- The event stream is staged. -/
  evCap : HasBytes mem ev evcap
  /-- The event stream has room for one record per input byte. -/
  evRoom : nev0 + stage2RecordBytes * n ≤ evcap
  /-- The arena's cursor slot reads as staged. -/
  ndstRead : readBytes mem ndst 8 = some (wordBytes 8 ndst0)
  /-- The event cursor's slot reads as staged. -/
  nevRead : readBytes mem nev 8 = some (wordBytes 8 nev0)
  /-- The refusal slot is staged. -/
  errBytes : HasBytes mem err 8
  /-- The document's positions fit the entry stream's 32-bit words. -/
  maxDoc : n ≤ stage2MaxDocument
  /-- The staged objects are separate. -/
  separate : DisjointRegions
    (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)
  /-- The arena cursor only appends. -/
  arenaGe : ndst0 ≤ alen
  /-- The arena grows by at most the document's own bytes. -/
  arenaLe : alen ≤ ndst0 + n
  /-- The event cursor only appends. -/
  evGe : nev0 ≤ evlen
  /-- The event stream grows by at most thirteen bytes per input byte. -/
  evLe : evlen ≤ nev0 + stage2RecordBytes * n
  /-- The last arena reserve still left the decoder's slack inside the capacity. -/
  reserve : alen + stage2ArenaReserve ≤ dstcap
  /-- The walk wrote only its arena's extent and its event prefix, and left both
  present throughout: `Owns` over the two extents, which is the half of
  `stage2Frame` the wrapper does not write. -/
  walkOwning : Owns (inRegions [(dst, alen + stage2ArenaReserve), (ev, evlen)]) mem m0
  /-- **The stored word's bound.**  On refusal the number the wrapper stores is
  inside the document — `stage2Boundary`'s refusal clause demands exactly this of
  the word at the refusal slot (`verdict = 0 → ∃ e, e ≤ n ∧ readBytes m err 8 =
  some (wordBytes 8 e)`), and this field is that demand's hypothesis.  It is a
  property of the value the run produces, not of the path that computed it. -/
  offLe : refusal = true → eoff ≤ n
  /-- **The arena's capacity is a 64-bit number.**  `stage2Boundary` states it
  (`dstcap < 2 ^ 64`), and this is that statement's producer: the ABI carries the
  capacity as an eight-byte word, so the number the record names is the word's
  value.  The clause places the arena's write extent inside the staging and makes
  `alen` fit a cursor slot's width. -/
  dstcapLt : dstcap < 2 ^ 64
  /-- **The event stream's capacity is a 64-bit number**, for the same reason:
  `stage2Boundary`'s `evcap < 2 ^ 64`. -/
  evcapLt : evcap < 2 ^ 64

namespace Stage2Run

variable {args : List Value} {mem m0 : Mem}

/-- **The staging is the record's precondition.**  The first half of a
`Stage2Run` is `stage2Pre`'s thirteen witnesses and its clauses, so a walk that
produced this report was called inside the record's domain. -/
theorem pre (h : Stage2Run args mem m0) (next : Nat) : Γ_stage2.pre args mem next := by
  obtain ⟨b, n, ep, nep, xp, nxp, dst, dstcap, ndst, ev, evcap, nev, err, bs, ent,
    ndst0, nev0, alen, evlen, refusal, eoff, args_eq, doc, tail, entries, order,
    inside, esc, arenaCap, arenaRoom, evCap, evRoom, ndstRead, nevRead, errBytes,
    maxDoc, separate, -⟩ := h
  exact ⟨b, n, ep, nep, xp, nxp, dst, dstcap, ndst, ev, evcap, nev, err, bs, ent,
    ndst0, nev0, args_eq, doc, tail, entries, order, inside, esc, arenaCap, arenaRoom,
    evCap, evRoom, ndstRead, nevRead, errBytes, maxDoc, separate⟩

/-- The arena and event-stream cursors are inside the objects the caller staged:
the arena's by its reserve, the event stream's by its write room. -/
theorem extents (h : Stage2Run args mem m0) :
    h.alen + stage2ArenaReserve ≤ h.dstcap ∧ h.evlen ≤ h.evcap :=
  ⟨h.reserve, le_trans h.evLe h.evRoom⟩

end Stage2Run

/-- **The three slot regions are separate**, read off the record's own
`DisjointRegions`: the list's last three entries are the cursor slots, so the
sixth entry's tail carries the three pairs. -/
theorem stage2Regions_slots {b n ep nep xp nxp dst ndst0 ev evcap ndst nev err : Nat}
    (h : DisjointRegions (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)) :
    (ndst + 8 ≤ nev ∨ nev + 8 ≤ ndst) ∧
      (ndst + 8 ≤ err ∨ err + 8 ≤ ndst) ∧
      (nev + 8 ≤ err ∨ err + 8 ≤ nev) := by
  simp only [DisjointRegions, stage2Regions] at h
  simp only [List.pairwise_cons, List.Pairwise.nil, and_true] at h
  obtain ⟨-, -, -, -, -, hs, ht, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have := hs (nev, 8) (by simp); simpa using this
  · have := hs (err, 8) (by simp); simpa using this
  · have := ht (err, 8) (by simp); simpa using this

/-- The refusal slot is outside the walk's two staged extents, from the record's
`DisjointRegions`: the walk wrote neither the arena's reserve past its cursor nor
the event stream's capacity. -/
theorem stage2Regions_err_outside {b n ep nep xp nxp dst ndst0 ev evcap ndst nev err : Nat}
    (h : DisjointRegions (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)) :
    (dst + (ndst0 + n + stage2ArenaReserve) ≤ err ∨ err + 8 ≤ dst) ∧
      (ev + evcap ≤ err ∨ err + 8 ≤ ev) := by
  simp only [DisjointRegions, stage2Regions] at h
  simp only [List.pairwise_cons, List.Pairwise.nil, and_true] at h
  obtain ⟨-, -, -, hdst, hev, -, -⟩ := h
  refine ⟨?_, ?_⟩
  · have := hdst (err, 8) (by simp); simpa using this
  · have := hev (err, 8) (by simp); simpa using this

/-- The two extents the walk owns are entries of the record's write list. -/
theorem walkExtent_mem (dst alen ev evlen ndst nev err : Nat) :
    (dst, alen + stage2ArenaReserve) ∈ stage2Writes dst alen ev evlen ndst nev err ∧
      (ev, evlen) ∈ stage2Writes dst alen ev evlen ndst nev err := by
  simp [stage2Writes]

/-- A region list contained in another denotes a smaller predicate. -/
theorem inRegions_mono {rs ss : List (Nat × Nat)} (h : ∀ r ∈ rs, r ∈ ss) {a : Nat}
    (ha : inRegions rs a) : inRegions ss a := by
  obtain ⟨r, hr, hi⟩ := ha
  exact ⟨r, h r hr, hi⟩

/-- The two extent-membership facts the boundary proof reads: a byte of an
extent at the head of a two-region list, and one at the tail. -/
theorem inRegions_head_extent {b n c m k : Nat} (hk : k < n) :
    inRegions [(b, n), (c, m)] (b + k) :=
  ⟨(b, n), List.mem_cons_self .., Nat.le_add_right b k, Nat.add_lt_add_left hk b⟩

theorem inRegions_tail_extent {b n c m k : Nat} (hk : k < m) :
    inRegions [(b, n), (c, m)] (c + k) :=
  ⟨(c, m), by simp, Nat.le_add_right c k, Nat.add_lt_add_left hk c⟩

/-- A byte present before the wrapper's stores is present after them. -/
theorem stage2Report_present {mem : Mem} {ndst nev err alen evlen eoff : Nat} {refusal : Bool}
    {a : Nat} (h : present mem a) :
    present (stage2Report mem ndst nev err alen evlen refusal eoff) a := by
  unfold stage2Report
  exact present_writeBytes _ ndst (wordBytes 8 alen) <|
    present_writeBytes _ nev (wordBytes 8 evlen) <|
      (by cases refusal with
        | false => exact h
        | true => exact present_writeBytes _ err (wordBytes 8 eoff) h)

/-- **The wrapper's stores make the record's post true, from the walk's report and
the six facts about the wrapper's memory.**  The facts are the wrapper's own —
both cursors' read-backs, the refusal word's two sides, presence, and the three
slots' frame — and `stage2Run_boundary` supplies them from `stage2Report`'s
lemmas at the emitted stores. -/
theorem stage2Boundary_of_parts {args : List Value} {mem m0 m : Mem}
    (h : Stage2Run args mem m0)
    (ndstAt : readBytes m h.ndst 8 = some (wordBytes 8 h.alen))
    (nevAt : readBytes m h.nev 8 = some (wordBytes 8 h.evlen))
    (errRefuse : h.refusal = true → readBytes m h.err 8 = some (wordBytes 8 h.eoff))
    (errAccept : h.refusal = false → readBytes m h.err 8 = readBytes m0 h.err 8)
    (pres : ∀ a, present m0 a → present m a)
    (frameSlots : UnchangedOn (inRegions [(h.ndst, 8), (h.nev, 8), (h.err, 8)]) m0 m) :
    stage2Boundary args mem m (.int 64 (stage2Verdict h.refusal)) := by
  obtain ⟨hslot1, hslot2, hslot3⟩ := stage2Regions_slots h.separate
  -- the walk left the refusal slot alone, so its bytes are the caller's
  obtain ⟨herrDst, herrEv⟩ := stage2Regions_err_outside h.separate
  have herrWalk : readBytes m0 h.err 8 = readBytes mem h.err 8 := by
    have halen : h.alen ≤ h.ndst0 + h.n := h.arenaLe
    have hevlen : h.evlen ≤ h.evcap := le_trans h.evLe h.evRoom
    refine readBytes_eq_of_UnchangedOn h.walkOwning.unchanged (a := h.err) (n := 8) ?_
    intro k hk hp
    rcases hp with ⟨r, hr, hlo, hhi⟩
    rcases List.mem_cons.mp hr with rfl | hr'
    · rcases herrDst with hle | hle <;> omega
    · rcases List.mem_cons.mp hr' with rfl | hnil
      · rcases herrEv with hle | hle <;> omega
      · exact absurd hnil (by simp)
  -- a byte the walk's region owns is present in the wrapper's memory
  have hpresentWalk : ∀ a, inRegions [(h.dst, h.alen + stage2ArenaReserve), (h.ev, h.evlen)] a →
      present m a := fun a ha => pres a (h.walkOwning.present a ha)
  -- the two prefixes
  obtain ⟨arena, hArena⟩ := LeanLLVM.readBytes_of_hasBytes m h.dst h.alen fun k hk =>
    hpresentWalk (h.dst + k) (inRegions_head_extent
      (Nat.lt_of_lt_of_le hk (Nat.le_add_right h.alen stage2ArenaReserve)))
  obtain ⟨evs, hEvs⟩ := LeanLLVM.readBytes_of_hasBytes m h.ev h.evlen fun k hk =>
    hpresentWalk (h.ev + k) (inRegions_tail_extent hk)
  -- the frame: the walk's two extents and the wrapper's three slots
  have hframe : UnchangedOn
      (inRegions (stage2Writes h.dst h.alen h.ev h.evlen h.ndst h.nev h.err)) mem m := by
    intro a ha
    have houtWalk : ¬ inRegions [(h.dst, h.alen + stage2ArenaReserve), (h.ev, h.evlen)] a :=
      fun hc => ha (inRegions_mono (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr'
        · simp [stage2Writes]
        · rcases List.mem_cons.mp hr' with rfl | hnil
          · simp [stage2Writes]
          · exact absurd hnil (by simp)) hc)
    have houtSlots : ¬ inRegions [(h.ndst, 8), (h.nev, 8), (h.err, 8)] a :=
      fun hc => ha (inRegions_mono (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr'
        · simp [stage2Writes]
        · rcases List.mem_cons.mp hr' with rfl | hr''
          · simp [stage2Writes]
          · rcases List.mem_cons.mp hr'' with rfl | hnil
            · simp [stage2Writes]
            · exact absurd hnil (by simp)) hc)
    exact (frameSlots a houtSlots).trans (h.walkOwning.unchanged a houtWalk)
  -- presence of every byte of the record's write list
  have hpresent : ∀ a,
      inRegions (stage2Writes h.dst h.alen h.ev h.evlen h.ndst h.nev h.err) a → present m a := by
    intro a ha
    obtain ⟨r, hr, hlo, hhi⟩ :=
      (show inRegions (stage2Writes h.dst h.alen h.ev h.evlen h.ndst h.nev h.err) a from ha)
    simp only [stage2Writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hpresentWalk a ⟨(h.dst, h.alen + stage2ArenaReserve),
        List.mem_cons_self .., hlo, hhi⟩
    · have hk : a - h.ndst < 8 := by omega
      have hp := LeanLLVM.readBytes_some_present m h.ndst 8 (wordBytes 8 h.alen)
        ndstAt (a - h.ndst) hk
      simpa [show h.ndst + (a - h.ndst) = a by omega] using hp
    · exact hpresentWalk a ⟨(h.ev, h.evlen), by simp, hlo, hhi⟩
    · have hk : a - h.nev < 8 := by omega
      have hp := LeanLLVM.readBytes_some_present m h.nev 8 (wordBytes 8 h.evlen)
        nevAt (a - h.nev) hk
      simpa [show h.nev + (a - h.nev) = a by omega] using hp
    · have hk : a - h.err < 8 := by omega
      have hread : readBytes m h.err 8 = some (wordBytes 8 h.eoff) ∨
          readBytes m h.err 8 = readBytes mem h.err 8 := by
        cases hb : h.refusal with
        | true => exact Or.inl (errRefuse hb)
        | false => exact Or.inr ((errAccept hb).trans herrWalk)
      rcases hread with hr | hr
      · have hp := LeanLLVM.readBytes_some_present m h.err 8 (wordBytes 8 h.eoff) hr
          (a - h.err) hk
        simpa [show h.err + (a - h.err) = a by omega] using hp
      · obtain ⟨vs, hvs⟩ := h.errBytes
        rw [← hr] at hvs
        have hp := LeanLLVM.readBytes_some_present m h.err 8 vs hvs (a - h.err) hk
        simpa [show h.err + (a - h.err) = a by omega] using hp
  refine ⟨h.b, h.n, h.ep, h.nep, h.xp, h.nxp, h.dst, h.dstcap, h.ndst, h.ev, h.evcap,
    h.nev, h.err, stage2Verdict h.refusal, h.ndst0, h.nev0, h.alen, h.evlen, arena, evs,
    h.args_eq, rfl, stage2Verdict_range h.refusal, h.ndstRead, h.nevRead, ndstAt, nevAt,
    h.arenaGe, h.arenaLe, h.evGe, h.evLe, h.dstcapLt, h.evcapLt, le_trans h.evLe h.evRoom,
    h.reserve, hArena, hEvs, ?_, ?_,
    ⟨hframe, hpresent⟩⟩
  · intro hzero
    cases hb : h.refusal with
    | true => exact ⟨h.eoff, h.offLe hb, errRefuse hb⟩
    | false =>
        have h1 : stage2Verdict h.refusal = (1 : BitVec 64) := by rw [hb]; rfl
        rw [h1] at hzero
        exact absurd hzero (by decide)
  · intro hone
    cases hb : h.refusal with
    | false => exact (errAccept hb).trans herrWalk
    | true =>
        have h0 : stage2Verdict h.refusal = (0 : BitVec 64) := by rw [hb]; rfl
        rw [h0] at hone
        exact absurd hone (by decide)

/-- **The wrapper's stores make the record's post true.**  `Γ_stage2`'s post is
`stage2Boundary` at a non-`ub` outcome, and the boundary's six facts about the
wrapper's memory are the emitted stores' own: `stage2Run_boundary` is
`stage2Boundary_of_parts` at `stage2Report`. -/
theorem stage2Run_boundary {args : List Value} {mem m0 : Mem} {next : Nat}
    (h : Stage2Run args mem m0) :
    Γ_stage2.post args mem next
      (.ret (some (.int 64 (stage2Verdict h.refusal)))
        (stage2Report m0 h.ndst h.nev h.err h.alen h.evlen h.refusal h.eoff)) := by
  obtain ⟨hslot1, hslot2, hslot3⟩ := stage2Regions_slots h.separate
  exact stage2Boundary_of_parts h
    (stage2Report_ndst m0 h.ndst h.nev h.err h.alen h.evlen h.refusal h.eoff)
    (stage2Report_nev hslot1)
    (by
      intro hr
      rw [hr]
      exact stage2Report_err_refusal (mem := m0) (ndst := h.ndst) (nev := h.nev)
        (err := h.err) (alen := h.alen) (evlen := h.evlen) (eoff := h.eoff) hslot2 hslot3)
    (by
      intro hr
      rw [hr]
      exact stage2Report_err_accept (mem := m0) (ndst := h.ndst) (nev := h.nev)
        (err := h.err) (alen := h.alen) (evlen := h.evlen) (eoff := h.eoff) hslot2 hslot3)
    (fun a ha => stage2Report_present ha)
    (stage2Report_frame m0 h.ndst h.nev h.err h.alen h.evlen h.refusal h.eoff)

/-! ### The report's clauses, and the walk facts that produce them

`Stage2Run` is the report a model of `s2_walk` produces, and its fields from
`arenaGe` onwards are the six clauses `Γ_stage2`'s post names.  They are not six
independent obligations.  What follows says what each is a consequence of, so
that a loop owes its own trace and the arithmetic only:

* **the arena's bound** (clause 1, `arenaLe`) is the escaped bodies' extents —
  ordered along the document, each ending inside it — together with the
  decoder's output never being longer than the body it decoded
  (`arenaAppend_spec`'s `on ≤ len`, the escape unit's own post).
  `Stage2SpansInside` names that trace and `Stage2Run.arenaLe_of_spans` reads the
  bound off it, the sum telescoping (`ordered_sum_le`).  The extents are *not* a
  field of `Stage2Run`: the report records the arena's cursor, which is their
  sum, and a sum of `Nat`s does not name its summands — so what a loop must
  carry is the extents it scanned, and this is the proposition they satisfy;
* **the event cursor's bound** (clause 2, `evLe`) is one record per entry
  (`Stage2OneRecordPerEntry`), because the entry stream's positions are strictly
  increasing inside the document and therefore number at most the document's
  bytes.  That count half is a consequence of the precondition, not of the loop:
  `Stage2Run.nep_le` reads it off `readLanes32_length` and
  `length_le_of_pairwise_lt` at the pre's own clauses, and the per-record
  arithmetic is `records_total_le`/`evlen_le_of_records`;
* **the reserve's slack** (clause 3, `reserve`) is not a second obligation: the
  arena's bound and the caller's staged capacity give it
  (`Stage2Run.reserve_of_arenaLe`);
* **`Owns` over the two extents** (clause 4, `walkOwning`) is the walk's `Owns`
  at the extent it *writes*, `[(dst, alen), (ev, evlen)]`, plus the caller's
  staging and the arena's bound: the sixty-four bytes past the cursor were
  present before the walk ran and the walk does not write them, so their presence
  afterwards is the caller's promise read through the walk's frame
  (`owns_reserve_of_owns_extent`,
  `Stage2Run.walkOwning_of_written`).  The record's clause names the larger
  extent, and the larger extent is what the caller stages;
* **the refusal bit** (clause 5) and **`eoff ≤ n`** (clause 6) are where the
  vocabulary stops, and the reason is the evaluator's shape rather than the
  walk's: `Satisfies` relates an outcome and the memory it leaves, and exposes
  neither a trace nor a step count, so nothing stated here can say *how* the run
  computed its outcome — which is what "the bit is `s2_walk`'s return" and "the
  offset came from the scan" are.  What the post does read survives: on refusal
  the refusal slot holds the word `eoff` (the wrapper's store, `errRefuse` in
  `stage2Boundary_of_parts`), and `stage2Boundary`'s refusal clause demands
  `e ≤ n` of that word — `offLe` is precisely that demand's hypothesis, and
  `refusal` is the bit `stage2Verdict` coerces.  So clause 6 is a statement
  about the value the run produces, and clause 5 is the flattening's
  re-indexing: a `Bool` field, not a proposition a record could state. -/

section

-- The budget's statement below is at the adapter's record, so the flattened
-- body's names are read here for the length of this section only.
open LeanLLVM.Refinement.JsonStage2IR

/-! #### Extents inside a window, and records per entry -/

/-- **Ordered extents inside a window sum inside it.**  Half-open intervals in
increasing order, each beginning at or after `lo` and ending at or before `hi`,
have lengths summing to at most `hi - lo`.  The conclusion is stated additively
(`sum + lo ≤ hi`) so that the induction's tail, which starts where the head ends,
never subtracts. -/
theorem ordered_sum_le (lo hi : Nat) :
    ∀ (sp : List (Nat × Nat)), sp.Pairwise (fun r s => r.1 + r.2 ≤ s.1) →
      (∀ r ∈ sp, r.1 + r.2 ≤ hi) → (∀ r ∈ sp, lo ≤ r.1) → lo ≤ hi →
      (sp.map fun r => r.2).sum + lo ≤ hi
  | [], _, _, _, hlh => by simpa using hlh
  | r :: t, hord, hend, hstart, _ => by
      have hhead : r.1 + r.2 ≤ hi := hend r (List.mem_cons_self ..)
      have hp := List.pairwise_cons.mp hord
      have htail : t.Pairwise (fun r s => r.1 + r.2 ≤ s.1) := hp.2
      have hlo : lo ≤ r.1 := hstart r (List.mem_cons_self ..)
      have hend' : ∀ s ∈ t, s.1 + s.2 ≤ hi := fun s hs => hend s (List.mem_cons_of_mem r hs)
      have ih := ordered_sum_le (r.1 + r.2) hi t htail hend' hp.1 hhead
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The sum form `arenaLe` reads: extents ordered and inside the document, from
the document's first byte. -/
theorem sum_le_of_ordered (hi : Nat) {sp : List (Nat × Nat)}
    (hord : sp.Pairwise (fun r s => r.1 + r.2 ≤ s.1))
    (hend : ∀ r ∈ sp, r.1 + r.2 ≤ hi) : (sp.map fun r => r.2).sum ≤ hi := by
  have := ordered_sum_le 0 hi sp hord hend (fun r _ => Nat.zero_le r.1) (Nat.zero_le hi)
  omega

/-- **The escaped bodies' lengths sum inside the document**, so the arena grows
by at most the document's own bytes. -/
theorem arenaLe_of_spans {alen ndst0 n : Nat} {sp : List (Nat × Nat)}
    (hord : sp.Pairwise (fun r s => r.1 + r.2 ≤ s.1))
    (hend : ∀ r ∈ sp, r.1 + r.2 ≤ n)
    (hgrowth : alen ≤ ndst0 + (sp.map fun r => r.2).sum) :
    alen ≤ ndst0 + n := by
  have := sum_le_of_ordered n hord hend
  omega

/-- The event records' bytes, grouped: the blob fold's total is the sum of the
groups' widths. -/
theorem records_flatten_length (records : List (List (List UInt8))) :
    records.flatten.flatten.length = (records.map fun r => r.flatten.length).sum := by
  induction records with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.flatten_cons, List.flatten_append, List.length_append, ih,
        List.map_cons, List.sum_cons]

/-- **Thirteen bytes per entry.**  A grouping of the event writes into records,
one per entry and none wider than `stage2RecordBytes`, totals at most thirteen
bytes per entry — `emitBlobs_len_le`'s arithmetic at the count a walk actually
has. -/
theorem records_total_le {records : List (List (List UInt8))} {nep : Nat}
    (hlen : records.length = nep)
    (hwidth : ∀ r ∈ records, r.flatten.length ≤ stage2RecordBytes) :
    records.flatten.flatten.length ≤ stage2RecordBytes * nep := by
  rw [records_flatten_length]
  refine sum_le_of_forall_le (w := stage2RecordBytes) (n := nep) ?_ ?_
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact hwidth r hr
  · simp [hlen]

/-- **The fold's cursor, from the record grouping.**  `emitBlobs_spec` at the
grouped blobs: a walk that emits one record per entry leaves the event cursor at
most `13 * nep` past where it started. -/
theorem evlen_le_of_records {mem : Mem} {ev len cap : Nat}
    {records : List (List (List UInt8))} {mem' : Mem} {len' : Nat} {nep : Nat}
    (hlen : records.length = nep)
    (hwidth : ∀ r ∈ records, r.flatten.length ≤ stage2RecordBytes)
    (h : emitBlobs mem ev len cap records.flatten = some (mem', len')) :
    len' ≤ len + stage2RecordBytes * nep := by
  obtain ⟨-, hl'⟩ := emitBlobs_spec h
  have := records_total_le hlen hwidth
  omega

/-! #### The reserve window, and the two extents' separation -/

/-- **The two extents the walk owns are separated**, read off the record's own
`DisjointRegions` at the arena's and the event stream's entries. -/
theorem stage2Regions_arena_ev {b n ep nep xp nxp dst ndst0 ev evcap ndst nev err : Nat}
    (h : DisjointRegions (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)) :
    dst + (ndst0 + n + stage2ArenaReserve) ≤ ev ∨ ev + evcap ≤ dst := by
  simp only [DisjointRegions, stage2Regions, List.pairwise_cons, List.Pairwise.nil,
    and_true] at h
  obtain ⟨-, -, -, hs, -⟩ := h
  have := hs (ev, evcap) (by simp)
  simpa using this

/-- **The reserve window is the caller's, not the walk's.**  `Owns` at
`[(dst, alen + 64), (ev, evlen)]` — the extent `Γ_stage2`'s post names — follows
from `Owns` at the extent the walk writes, `[(dst, alen), (ev, evlen)]`, the
arena's staged capacity, and the two extents' separation: a byte of the
sixty-four-byte reserve was present before the walk ran (`HasBytes` at the
capacity), the walk writes nothing there, and the event extent cannot reach it. -/
theorem owns_reserve_of_owns_extent {mem m0 : Mem} {dst alen ev evlen dstcap : Nat}
    (h : Owns (inRegions [(dst, alen), (ev, evlen)]) mem m0)
    (harena : HasBytes mem dst dstcap)
    (hres : alen + stage2ArenaReserve ≤ dstcap)
    (hsep : dst + alen + stage2ArenaReserve ≤ ev ∨ ev + evlen ≤ dst) :
    Owns (inRegions [(dst, alen + stage2ArenaReserve), (ev, evlen)]) mem m0 := by
  have hsub : ∀ a, inRegions [(dst, alen), (ev, evlen)] a →
      inRegions [(dst, alen + stage2ArenaReserve), (ev, evlen)] a := by
    intro a ha
    obtain ⟨r, hr, hlo, hhi⟩ := ha
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨(dst, alen + stage2ArenaReserve), List.mem_cons_self .., hlo, by omega⟩
    · rcases List.mem_cons.mp hr' with rfl | hnil
      · exact ⟨(ev, evlen), by simp, hlo, hhi⟩
      · exact absurd hnil (by simp)
  refine ⟨h.unchanged.mono hsub, ?_⟩
  intro a ha
  obtain ⟨r, hr, hlo, hhi⟩ := ha
  rcases List.mem_cons.mp hr with rfl | hr'
  · rcases Nat.lt_or_ge a (dst + alen) with hlt | hge
    · exact h.present a ⟨(dst, alen), List.mem_cons_self .., hlo, hlt⟩
    · have hk : a - dst < dstcap := by omega
      obtain ⟨vs, hvs⟩ := harena
      obtain ⟨b, hb⟩ := readBytes_some_present mem dst dstcap vs hvs (a - dst) hk
      rw [show dst + (a - dst) = a by omega] at hb
      have hnot : ¬ inRegions [(dst, alen), (ev, evlen)] a := by
        rintro ⟨s, hs, hslo, hshi⟩
        rcases List.mem_cons.mp hs with rfl | hs'
        · omega
        · rcases List.mem_cons.mp hs' with rfl | hnil
          · rcases hsep with hsep | hsep <;> omega
          · exact absurd hnil (by simp)
      have heq : readByte m0 a = readByte mem a := h.unchanged a hnot
      exact ⟨b, by rw [heq]; exact hb⟩
  · rcases List.mem_cons.mp hr' with rfl | hnil
    · exact h.present a ⟨(ev, evlen), by simp, hlo, hhi⟩
    · exact absurd hnil (by simp)

/-! #### The two walk facts, and the clauses they give -/

/-- The walk's arena trace: the extents of the escaped bodies it decoded, as
intervals of the document.  They are ordered (the walk scans the document once),
each ends inside it, and the arena grows by at most their total, because the
decoder's output is never longer than the body it decoded.

The extents are not a field of `Stage2Run`: the report records the arena's
cursor, which is their *sum*, and a sum of `Nat`s does not name its summands.  A
model of the loop carries the extents it scanned; this is the proposition it then
satisfies, and `Stage2Run.arenaLe_of_spans` is the bound it buys. -/
def Stage2SpansInside {args : List Value} {mem m0 : Mem} (h : Stage2Run args mem m0)
    (sp : List (Nat × Nat)) : Prop :=
  sp.Pairwise (fun r s => r.1 + r.2 ≤ s.1) ∧
    (∀ r ∈ sp, r.1 + r.2 ≤ h.n) ∧
    h.alen ≤ h.ndst0 + (sp.map fun r => r.2).sum

/-- **One event record per entry**, as the cursor's bound: thirteen bytes an
entry and no more, which is the count `emitBlobs_len_le` needs at the entry
stream rather than at the document. -/
def Stage2OneRecordPerEntry {args : List Value} {mem m0 : Mem}
    (h : Stage2Run args mem m0) : Prop :=
  h.evlen ≤ h.nev0 + stage2RecordBytes * h.nep

namespace Stage2Run

variable {args : List Value} {mem m0 : Mem}

/-- The entry stream has no more entries than the document has bytes: its
positions are strictly increasing and inside the document. -/
theorem nep_le (h : Stage2Run args mem m0) : h.nep ≤ h.n := by
  rw [← readLanes32_length mem h.ep h.nep h.ent h.entries]
  exact length_le_of_pairwise_lt h.order h.inside

/-- The arena's bound gives the reserve's slack at the caller's capacity. -/
theorem reserve_of_arenaLe (h : Stage2Run args mem m0) (hle : h.alen ≤ h.ndst0 + h.n) :
    h.alen + stage2ArenaReserve ≤ h.dstcap := by
  have := h.arenaRoom
  omega

/-- The arena's bound, from the walk's spans. -/
theorem arenaLe_of_spans (h : Stage2Run args mem m0) {sp : List (Nat × Nat)}
    (hf : Stage2SpansInside h sp) : h.alen ≤ h.ndst0 + h.n :=
  LeanLLVM.Refinement.arenaLe_of_spans hf.1 hf.2.1 hf.2.2

/-- The event cursor's bound, from one record per entry and the entry count. -/
theorem evLe_of_oneRecordPerEntry (h : Stage2Run args mem m0)
    (hone : Stage2OneRecordPerEntry h) :
    h.evlen ≤ h.nev0 + stage2RecordBytes * h.n := by
  have h1 := h.nep_le
  have h2 : stage2RecordBytes * h.nep ≤ stage2RecordBytes * h.n :=
    Nat.mul_le_mul_left _ h1
  have hone' := hone
  simp only [Stage2OneRecordPerEntry] at hone'
  omega

/-- **The report's `Owns` clause, from the walk's own write extent and the
arena's bound.**  The reserve's slack is `reserve_of_arenaLe` at that bound, not
a separate obligation of the walk; the staging covers the reserve window. -/
theorem walkOwning_of_written (h : Stage2Run args mem m0)
    (hw : Owns (inRegions [(h.dst, h.alen), (h.ev, h.evlen)]) mem m0)
    (hle : h.alen ≤ h.ndst0 + h.n) :
    Owns (inRegions [(h.dst, h.alen + stage2ArenaReserve), (h.ev, h.evlen)]) mem m0 := by
  refine owns_reserve_of_owns_extent hw h.arenaCap (h.reserve_of_arenaLe hle) ?_
  have hevl := le_trans h.evLe h.evRoom
  have hsep := stage2Regions_arena_ev h.separate
  rcases hsep with hsep | hsep <;> omega

end Stage2Run

/-! ### The completion budget, stated

`Stage2WalkObligation`'s first conjunct is a budget at which the pinned body
returns.  It is expressible here, and this section states it without inhabiting
it:

* **the budget is a term, not a hypothesis.**  `stage2Budget` reads three of the
  ABI's thirteen words — the entry count, the document's length and the escape
  list's count — and `stage2Budget_at_abi` is that term at the argument shape
  `Γ_stage2.pre` admits.  The two `#guard`s below read it: `72` at one entry and
  one document byte, and `0` off the ABI's shape, so the first is a statement
  about the argument list and not about a match that accepts anything.  The
  budget depends on no memory (`stage2Budget`'s parameter is unused), so it is a
  numeral per staging and needs no `readBytes` witness of its own;
* **through the adapter it is the same number.**  `Γ_stage2at`'s budget at the
  twenty-one flattened arguments is `stage2Budget` at the ABI's thirteen
  (`Γ_stage2at_budget`), so completion at the record's budget is completion at a
  function of the thirteen words rather than at a term the body's parameters
  hide;
* **the standalone statement is the obligation's completion half.**
  `Stage2WalkCompletes` states, at the ABI's arguments, that the pinned body
  returns some value within `stage2Budget`, and
  `stage2WalkObligation_iff_completion` proves it is exactly the first conjunct
  of `Stage2WalkObligation` beside the post — so naming the budget weakens
  nothing.

What this vocabulary cannot state is a budget's *tightness*, and it does not need
to: `runFuel` is asked for a budget and answers with an outcome or with nothing,
so "the budget is enough" and "the run completes at it" are one proposition, and
completion transfers to every larger budget (`stage2WalkCompletes_mono`, from
`runFuel_mono`).  There is no step-count fact above the completion conjunct that
a loop proof would then discharge separately.

What resists is the conjunct itself.  `stage2Body` is 165 blocks whose dispatch
reads the document's bytes and the entry stream, so a completion proof needs a
per-arm trace with a measure that decreases — the entry index consumed, then the
document position — and that induction is the same one the six clauses above are
read from.  No statement in this module supplies a trace, so the budget is
stated and not claimed: stating it is what lets the clauses stay downstream of
it rather than being restated as hypotheses. -/

/-- **The record's budget is a term of three of the ABI's thirteen words.** -/
theorem stage2Budget_at_abi (b n ep nep xp nxp dst dstcap ndst ev evcap nev err : Nat)
    (mem : Mem) :
    stage2Budget [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
        .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
        .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
        .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err] mem
      = stage2EntryAllowance * (BitVec.ofNat 64 nep).toNat
        + stage2ByteAllowance * (BitVec.ofNat 64 n).toNat
        + stage2PositionAllowance * (BitVec.ofNat 64 nxp).toNat
        + stage2FinalisationAllowance := rfl

/-- The budget is positive at every staging the record admits, so the completion
conjunct never asks a run for zero steps. -/
theorem stage2Budget_pos_of_pre {args : List Value} {mem : Mem} {next : Nat}
    (h : Γ_stage2.pre args mem next) : 0 < stage2Budget args mem := by
  obtain ⟨b, n, ep, nep, xp, nxp, dst, dstcap, ndst, ev, evcap, nev, err, _bs, _ent,
    _ndst0, _nev0, hargs, -⟩ := h
  subst hargs
  rw [stage2Budget_at_abi b n ep nep xp nxp dst dstcap ndst ev evcap nev err mem]
  unfold stage2FinalisationAllowance
  omega

/-- The adapter's budget at the flattened arguments is the record's own, at the
ABI's thirteen: the eight staging objects contribute nothing to the walk's
fuel. -/
theorem Γ_stage2at_budget (d c ctype cst tok s z e nkSlot nxpSlot : Nat) {a13 : List Value}
    (hlen : a13.length = 13) (mem : Mem) :
    (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).budget
        (stage2Args a13 d c ctype cst tok s z e) mem = stage2Budget a13 mem := by
  show stage2Budget ((stage2Args a13 d c ctype cst tok s z e).take 13) mem
      = stage2Budget a13 mem
  rw [stage2Args_take13 a13 hlen]

/-- **The walk's completion at the record's own budget**, at the ABI's thirteen
arguments, with the seven appended objects staged.  Stated and not claimed: what
discharges it is the loop.  The staging hypothesis is not decorativeness — the
body's first store is to `%c.i`, so a completion statement that did not stage the
appended objects would be about a body whose stores could not be justified.  The
two count slots are carried beside the seven for the same reason and at the same
place: they are the pipeline's, the ABI does not carry them, and their separation
from the seven is what the caller reads back after the run. -/
def Stage2WalkCompletes (d c ctype cst tok s z e nkSlot nxpSlot : Nat) (sub : Calls) : Prop :=
  ∀ a13 mem next, Γ_stage2.pre a13 mem next →
    stage2StagedPre a13 mem c ctype cst tok s z e nkSlot nxpSlot →
    ∃ v m, runFuel (stage2Calls sub) (stage2Budget a13 mem) stage2Body
      (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
      = some (.ret v m)

/-- **The standalone completion statement is the obligation's first conjunct**,
beside the post's second.  The two directions are the adapter's precondition and
`stage2Args_take13`: a caller's arguments are the flattened ones read at the
thirteen-slot prefix, the staging goes with them, and the budget goes with both. -/
theorem stage2WalkObligation_iff_completion
    (d c ctype cst tok s z e nkSlot nxpSlot : Nat) (sub : Calls) :
    Stage2WalkObligation d c ctype cst tok s z e nkSlot nxpSlot sub ↔
      Stage2WalkCompletes d c ctype cst tok s z e nkSlot nxpSlot sub ∧
        (∀ args mem next,
          (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).pre args mem next →
          ∀ o, BehFromState (stage2Calls sub) stage2Body
              (EntryState stage2Body args mem next) o →
            (Γ_stage2at d c ctype cst tok s z e nkSlot nxpSlot).post args mem next o) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a13 mem next hpre hstaged
      have hlen : a13.length = 13 := stage2Pre_length hpre
      obtain ⟨v, m, hrun⟩ :=
        (h (stage2Args a13 d c ctype cst tok s z e) mem next
          (Γ_stage2at_pre hpre hstaged)).1
      refine ⟨v, m, ?_⟩
      simp only [Γ_stage2at] at hrun
      rw [stage2Args_take13 a13 hlen] at hrun
      exact hrun
    · intro args mem next hpre o hbeh
      exact (h args mem next hpre).2 o hbeh
  · intro ⟨hcom, hpost⟩ args mem next hpre
    obtain ⟨a13, hargs, hpre13, hstaged⟩ := hpre
    subst hargs
    have hlen : a13.length = 13 := stage2Pre_length hpre13
    refine ⟨?_, hpost (stage2Args a13 d c ctype cst tok s z e) mem next
      ⟨a13, rfl, hpre13, hstaged⟩⟩
    obtain ⟨v, m, hrun⟩ := hcom a13 mem next hpre13 hstaged
    refine ⟨v, m, ?_⟩
    simp only [Γ_stage2at]
    rw [stage2Args_take13 a13 hlen]
    exact hrun

/-- **A larger budget is not a second obligation.**  Completion at one budget is
completion at every larger one (`runFuel_mono`); together with `runFuel`'s
outcome-or-nothing answer, this is why the budget's adequacy is the completion
conjunct and not a separate fact about the body's blocks. -/
theorem stage2WalkCompletes_mono {d c ctype cst tok s z e nkSlot nxpSlot : Nat} {sub : Calls}
    {B B' : List Value → Mem → Nat}
    (h : ∀ a13 mem next, Γ_stage2.pre a13 mem next →
      ∃ v m, runFuel (stage2Calls sub) (B a13 mem) stage2Body
        (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
        = some (.ret v m))
    (hle : ∀ a13 mem, B a13 mem ≤ B' a13 mem) :
    ∀ a13 mem next, Γ_stage2.pre a13 mem next →
      ∃ v m, runFuel (stage2Calls sub) (B' a13 mem) stage2Body
        (EntryState stage2Body (stage2Args a13 d c ctype cst tok s z e) mem next)
        = some (.ret v m) := by
  intro a13 mem next hpre
  obtain ⟨v, m, hrun⟩ := h a13 mem next hpre
  refine ⟨v, m, ?_⟩
  have hmono := runFuel_mono hrun (d := B' a13 mem - B a13 mem)
  rw [Nat.add_sub_of_le (hle a13 mem)] at hmono
  exact hmono

-- The budget at one entry and one document byte is `32 + 8 + 32`: the term is a
-- numeral of the arguments, and this is its value there.
#guard stage2Budget [.ptr 0, .int 64 1, .ptr 0, .int 64 1, .ptr 0, .int 64 0, .ptr 0,
  .int 64 0, .ptr 0, .ptr 0, .int 64 0, .ptr 0, .ptr 0] [] = 72

-- The control: a list that is not the ABI's thirteen draws no fuel, so the guard
-- above is a statement about the argument list and not about a match that accepts
-- anything.
#guard stage2Budget [] [] = 0

/-- info: 'LeanLLVM.Refinement.stage2WalkObligation_iff_completion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.stage2WalkObligation_iff_completion

/-- info: 'LeanLLVM.Refinement.Stage2Run.walkOwning_of_written' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.Stage2Run.walkOwning_of_written

/-- info: 'LeanLLVM.Refinement.records_total_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.records_total_le

end

/-! ### The number path: the emitted dispatch, and the three proved models

`num_fast_el1` converts a lexeme in three classes.  The dispatch
(`stage2.c:424-460`, pinned above) reads five locals — the integer and fraction
accumulators `ip`/`fr`, their digit counts `idig`/`fdig`, and the exponent
accumulator `exp10` — and tests `nd = idig + fdig` and `eff = exp10 - fdig`.

The three conversions are proved against models in this tree
(`StrtodTier1.emittedRefinesOn_tier1`, `ElGuardRefine.elGuardRefinesOn`,
`StrtodTier3.emittedRefinesOn_tier3`); what none of them states is *which input
takes which branch*.  That is what this section proves, at the emitted tests:

* `expAcc` is `exp10`'s saturating fold (`if (exp10 < 100000) exp10 = exp10 * 10
  + digit`) and `numEff` is `exp10 - fdig` at it;
* `expAcc_le_digitsNat` and `expAcc_eq_or_frozen` are the fold's two facts: the
  saturating accumulator is never above the exact one, and it is the exact one
  unless it has frozen at or above `100000`;
* `numEff_eq_eff` shows the freeze cannot reach a class the fast path takes: a
  frozen accumulator is at least `100000` and the fraction has at most nineteen
  digits, so the emitted `eff` is outside `[-45, 45]` — outside every gate
  below, and (by `expAcc_le_digitsNat`) so is the specification's;
* `numClassOf` is the emitted nest of tests, and `numClassOf_tier1`,
  `numClassOf_kernel` and `numClassOf_fallback` are the three selections at
  `StrtodRefine`'s classes.

Then `numFastEmitted` is the emitted conversion as one `Bytes → Binary64`
function — the reader's decomposition, the dispatch's choice, and that branch's
proved model — and `numFastEmitted_refines` is `EmittedConversionRefines` at it.
`numFastEmitted_strtodSpec` is the consequence on every well-formed lexeme.

The observable is binary64, which is the ruling: `strtodSpec` names eight bytes,
and eight bytes cannot name the lexeme they came from.  A theorem equating the
emitted output with a lexeme-carrying reference value would be false for any two
lexemes denoting the same double, so the statement here is the byte value and
nothing else. -/

/-- One digit's step of the exact accumulator (`Decimal.digitsNat`'s fold). -/
def digStep (a : Nat) (b : UInt8) : Nat := a * 10 + (b.toNat - 0x30)

/-- One digit's step of the emitted accumulator: `if (exp10 < 100000) exp10 =
exp10 * 10 + digit`, i.e. frozen once it reaches `100000`
(`stage2.c:418`). -/
def satStep (a : Nat) (b : UInt8) : Nat := if a < 100000 then a * 10 + (b.toNat - 0x30) else a

/-- The emitted exponent accumulator at the exponent's digits: the saturating
fold, at zero. -/
def expAcc (bs : Bytes) : Nat := bs.data.toList.foldl satStep 0

/-- `Decimal.digitsNat` is the exact fold, as this section names it. -/
theorem digitsNat_eq_foldl (bs : Bytes) :
    Decimal.digitsNat bs = bs.data.toList.foldl digStep 0 := rfl

/-- The exact fold is monotone in its accumulator. -/
theorem digStep_mono {a a' : Nat} (b : UInt8) (h : a ≤ a') : digStep a b ≤ digStep a' b := by
  unfold digStep
  exact Nat.add_le_add_right (Nat.mul_le_mul_right 10 h) _

/-- The exact fold is monotone in its accumulator. -/
theorem foldl_digStep_mono (l : List UInt8) {a a' : Nat} (h : a ≤ a') :
    l.foldl digStep a ≤ l.foldl digStep a' := by
  induction l generalizing a a' with
  | nil => exact h
  | cons b bs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (digStep_mono b h)

/-- A saturating step never exceeds the exact one, at the same accumulator. -/
theorem satStep_le_digStep (a : Nat) (b : UInt8) : satStep a b ≤ digStep a b := by
  unfold satStep digStep
  split
  · exact Nat.le_refl _
  · have h1 : a * 1 ≤ a * 10 := Nat.mul_le_mul_left a (by decide)
    simp only [Nat.mul_one] at h1
    omega

/-- **The saturating accumulator never exceeds the exact one.** -/
theorem foldl_satStep_le_digStep (a : Nat) : ∀ l : List UInt8,
    l.foldl satStep a ≤ l.foldl digStep a
  | [] => Nat.le_refl a
  | b :: bs => by
      rw [List.foldl_cons, List.foldl_cons]
      exact Nat.le_trans (foldl_satStep_le_digStep (satStep a b) bs)
        (foldl_digStep_mono bs (satStep_le_digStep a b))

/-- The emitted exponent accumulator is at most the exact one. -/
theorem expAcc_le_digitsNat (bs : Bytes) : expAcc bs ≤ Decimal.digitsNat bs := by
  rw [digitsNat_eq_foldl]
  exact foldl_satStep_le_digStep 0 bs.data.toList

/-- Once the emitted accumulator reaches `100000` it stops changing. -/
theorem foldl_satStep_frozen (a : Nat) (h : 100000 ≤ a) :
    ∀ l : List UInt8, l.foldl satStep a = a
  | [] => rfl
  | b :: bs => by
      rw [List.foldl_cons]
      rw [show satStep a b = a from by simp [satStep, show ¬ a < 100000 by omega]]
      exact foldl_satStep_frozen a h bs

/-- **Below `100000` the accumulator is the exact fold.**  A fold that never
reaches the saturating threshold never took the frozen branch, so it is
`digStep`'s fold at every step. -/
theorem foldl_satStep_eq_digStep_of_lt (a : Nat) : ∀ l : List UInt8,
    l.foldl satStep a < 100000 → l.foldl satStep a = l.foldl digStep a
  | [], _ => rfl
  | b :: bs, h => by
      rw [List.foldl_cons] at h ⊢
      have hs : satStep a b = digStep a b := by
        by_cases ha : a < 100000
        · simp only [satStep, digStep, ha, ite_true]
        · exfalso
          have hsat : satStep a b = a := by simp only [satStep, ha, ite_false]
          have hf := foldl_satStep_frozen (satStep a b) (by rw [hsat]; omega) bs
          rw [hsat] at h hf
          rw [hf] at h
          omega
      rw [hs] at h ⊢
      exact foldl_satStep_eq_digStep_of_lt (digStep a b) bs h

/-- **The accumulator is the exact value, or it has frozen above the range.**
This is the whole of the emitted exponent's correctness: the freeze happens only
after the value has passed `100000`, and every fast-path gate is inside
`[-45, 45]`. -/
theorem expAcc_eq_or_frozen (bs : Bytes) :
    expAcc bs = Decimal.digitsNat bs ∨ 100000 ≤ expAcc bs := by
  rcases Nat.lt_or_ge (expAcc bs) 100000 with h | h
  · left
    rw [digitsNat_eq_foldl]
    exact foldl_satStep_eq_digStep_of_lt 0 bs.data.toList h
  · exact Or.inr h

/-! #### The emitted `eff`, and why a frozen accumulator cannot be in range -/

/-- The emitted exponent's value with its sign, at the saturating accumulator
(`stage2.c:418-421`). -/
def expVal (d : Decimal) : Int :=
  match d.ex with
  | none => 0
  | some (s, ds) => if s then -((expAcc ds : Nat) : Int) else ((expAcc ds : Nat) : Int)

/-- The emitted `eff = exp10 - fdig`. -/
def numEff (d : Decimal) : Int := expVal d - (fracDigits d : Int)

/-- `fracDigits` is inside the digit count. -/
theorem fracDigits_le_digitCount (d : Decimal) : fracDigits d ≤ digitCount d :=
  Nat.le_add_left (fracDigits d) (intDigits d)

/-- The fraction's digit count at the fast path's own bound: at most nineteen. -/
theorem fracDigits_le_nineteen {d : Decimal} (hnd : digitCount d ≤ 19) :
    fracDigits d ≤ 19 := by
  have := fracDigits_le_digitCount d
  omega

/-- **A frozen accumulator is outside every gate.**  With at most nineteen
fraction digits, an accumulator at or above `100000` puts the emitted `eff` below
`-45` or above `45`. -/
theorem numEff_far_of_frozen {d : Decimal} {ds : Bytes} (hx : d.ex = some (true, ds))
    (hnd : digitCount d ≤ 19) (hfrozen : 100000 ≤ expAcc ds) : numEff d < -45 := by
  have hfd := fracDigits_le_nineteen hnd
  have hge : (100000 : Int) ≤ (expAcc ds : Int) := by exact_mod_cast hfrozen
  have hle : ((fracDigits d : Nat) : Int) ≤ 19 := by exact_mod_cast hfd
  unfold numEff expVal
  rw [hx]
  show -((expAcc ds : Nat) : Int) - (fracDigits d : Int) < -45
  omega

/-- The positive sign's form of the same fact. -/
theorem numEff_far_of_frozen_pos {d : Decimal} {ds : Bytes} (hx : d.ex = some (false, ds))
    (hnd : digitCount d ≤ 19) (hfrozen : 100000 ≤ expAcc ds) : 45 < numEff d := by
  have hfd := fracDigits_le_nineteen hnd
  have hge : (100000 : Int) ≤ (expAcc ds : Int) := by exact_mod_cast hfrozen
  have hle : ((fracDigits d : Nat) : Int) ≤ 19 := by exact_mod_cast hfd
  unfold numEff expVal
  rw [hx]
  show ((expAcc ds : Nat) : Int) - (fracDigits d : Int) > 45
  omega

/-- **The emitted `eff` is the specification's wherever a gate can be taken.**
If the emitted `eff` is inside `[-45, 45]` then the accumulator had not frozen,
and the emitted value is `StrtodRefine.eff`. -/
theorem numEff_eq_eff_of_numGates {d : Decimal} (hnd : digitCount d ≤ 19)
    (hgate : -45 ≤ numEff d ∧ numEff d ≤ 45) : numEff d = eff d := by
  cases hx : d.ex with
  | none => simp only [numEff, expVal, eff, expValue, hx]
  | some p =>
      obtain ⟨s, ds⟩ := p
      rcases expAcc_eq_or_frozen ds with h | h
      · simp only [numEff, expVal, eff, expValue, hx, h]
      · cases s
        · exact absurd (numEff_far_of_frozen_pos hx hnd h) (by omega)
        · exact absurd (numEff_far_of_frozen hx hnd h) (by omega)

/-- **The emitted `eff` is the specification's wherever the specification's is in
range** — the direction the spec-to-emitted selection needs.  A frozen
accumulator is at least `100000` and the exact one is at least as large
(`expAcc_le_digitsNat`), so the specification's `eff` is out of range too. -/
theorem numEff_eq_eff_of_specRange {d : Decimal} (hnd : digitCount d ≤ 19)
    (hrange : -45 ≤ eff d ∧ eff d ≤ 45) : numEff d = eff d := by
  have hfd := fracDigits_le_nineteen hnd
  cases hx : d.ex with
  | none => simp only [numEff, expVal, eff, expValue, hx]
  | some p =>
      obtain ⟨s, ds⟩ := p
      rcases expAcc_eq_or_frozen ds with h | h
      · simp only [numEff, expVal, eff, expValue, hx, h]
      · have hle : (100000 : Int) ≤ (Decimal.digitsNat ds : Int) := by
          have hge : (100000 : Nat) ≤ Decimal.digitsNat ds :=
            Nat.le_trans h (expAcc_le_digitsNat ds)
          exact_mod_cast hge
        have hfdi : ((fracDigits d : Nat) : Int) ≤ 19 := by exact_mod_cast hfd
        cases s
        · simp only [eff, expValue, hx] at hrange
          omega
        · simp only [eff, expValue, hx] at hrange
          omega

/-- **The emitted `eff` either is the specification's or is already out of the
fast range** — the form the fallback's selection reads, where neither side's
range is known in advance. -/
theorem numEff_eq_or_far {d : Decimal} (hnd : digitCount d ≤ 19) :
    numEff d = eff d ∨ numEff d < -45 ∨ 45 < numEff d := by
  cases hx : d.ex with
  | none => exact Or.inl (by simp only [numEff, expVal, eff, expValue, hx])
  | some p =>
      obtain ⟨s, ds⟩ := p
      rcases expAcc_eq_or_frozen ds with h | h
      · exact Or.inl (by simp only [numEff, expVal, eff, expValue, hx, h])
      · cases s
        · exact Or.inr (Or.inr (numEff_far_of_frozen_pos hx hnd h))
        · exact Or.inr (Or.inl (numEff_far_of_frozen hx hnd h))

/-! #### The dispatch, as the emitted tests read -/

/-- The three classes the emitted dispatch selects. -/
inductive NumClass where
  | tier1
  | kernel
  | fallback
deriving DecidableEq, Repr

/-- **The emitted dispatch** (`stage2.c:424-460`): the outer gate on `nd` and
`eff`, the inner tier-1 test, and the kernel's own decision.  `kernelOk` is the
`num_el_el1` call's return, which `ElGuardRefine.elTier2Code` models. -/
def numClassOf (nd : Nat) (e : Int) (kernelOk : Bool) : NumClass :=
  if nd ≤ 19 ∧ -45 ≤ e ∧ e ≤ 45 then
    if nd ≤ 15 ∧ -22 ≤ e ∧ e ≤ 22 then .tier1
    else if kernelOk then .kernel else .fallback
  else .fallback

/-- The kernel branch's selection, at a variable decision: the two gates, the
tier-1 test's failure, and the kernel's own return. -/
theorem numClassOf_kernel_at (nd : Nat) (e : Int) (k : Bool)
    (hgate : nd ≤ 19 ∧ -45 ≤ e ∧ e ≤ 45)
    (hnotier1 : ¬ (nd ≤ 15 ∧ -22 ≤ e ∧ e ≤ 22)) (hk : k = true) :
    numClassOf nd e k = .kernel := by
  unfold numClassOf
  rw [ite_eq_left hgate, ite_eq_right hnotier1, hk]
  rfl

/-- the fallback's, when the gate holds and the kernel declined -/
theorem numClassOf_fallback_at (nd : Nat) (e : Int) (k : Bool)
    (hgate : nd ≤ 19 ∧ -45 ≤ e ∧ e ≤ 45)
    (hnotier1 : ¬ (nd ≤ 15 ∧ -22 ≤ e ∧ e ≤ 22)) (hk : k = false) :
    numClassOf nd e k = .fallback := by
  unfold numClassOf
  rw [ite_eq_left hgate, ite_eq_right hnotier1, hk]
  rfl

/-- The emitted kernel's decision, as the guard model's: `num_el_el1` returned
`some` code.  `ElGuardRefine` defines `elTier2Code` as the fields that call
returns, so this is the same decision at the model. -/
def kernelDecides (d : Decimal) : Bool :=
  (LeanLLVM.ElGuardRefine.elTier2Code d.mantissa d.exponent).isSome

/-- **The emitted tests select tier 1 exactly where the specification's tier 1
is.** -/
theorem numClassOf_tier1 {d : Decimal} (h : Tier1 d) :
    numClassOf (digitCount d) (numEff d) (kernelDecides d) = .tier1 := by
  have hnd : digitCount d ≤ 15 := h.1
  have hlo : -22 ≤ eff d := h.2.1
  have hhi : eff d ≤ 22 := h.2.2
  have heff : numEff d = eff d :=
    numEff_eq_eff_of_specRange (by omega) ⟨by omega, by omega⟩
  have hgate : digitCount d ≤ 19 ∧ -45 ≤ numEff d ∧ numEff d ≤ 45 := by
    rw [heff]; exact ⟨by omega, by omega, by omega⟩
  have hinner : digitCount d ≤ 15 ∧ -22 ≤ numEff d ∧ numEff d ≤ 22 := by
    rw [heff]; exact ⟨hnd, hlo, hhi⟩
  unfold numClassOf
  rw [ite_eq_left hgate, ite_eq_left hinner]

/-- **The emitted tests select the kernel exactly where `Tier2` is** — the
eligible non-tier-1 lexemes at the kernel's decision. -/
theorem numClassOf_kernel {d : Decimal} (h : Tier2 d kernelDecides) :
    numClassOf (digitCount d) (numEff d) (kernelDecides d) = .kernel := by
  have hnt1 : ¬ Tier1 d := h.1
  have hnd : digitCount d ≤ 19 := h.2.1.1
  have hlo : -45 ≤ eff d := h.2.1.2.1
  have hhi : eff d ≤ 45 := h.2.1.2.2
  have hk : kernelDecides d = true := h.2.2
  have heff : numEff d = eff d := numEff_eq_eff_of_specRange hnd ⟨hlo, hhi⟩
  have hgate : digitCount d ≤ 19 ∧ -45 ≤ numEff d ∧ numEff d ≤ 45 := by
    rw [heff]; exact ⟨hnd, hlo, hhi⟩
  have hnotier1 : ¬ (digitCount d ≤ 15 ∧ -22 ≤ numEff d ∧ numEff d ≤ 22) := by
    rw [heff]
    intro hs
    exact hnt1 ⟨hs.1, hs.2.1, hs.2.2⟩
  exact numClassOf_kernel_at _ _ _ hgate hnotier1 hk

/-- **The emitted tests select the fallback exactly where `Fallback` is.**  Either
the outer gate is not taken — the emitted `eff` is out of range, and then the
specification's is too (`numEff_eq_or_far`) — or it is taken and the kernel
declined. -/
theorem numClassOf_fallback {d : Decimal} (h : Fallback d kernelDecides) :
    numClassOf (digitCount d) (numEff d) (kernelDecides d) = .fallback := by
  have hnt1 : ¬ Tier1 d := h.1
  have hcase : ¬ Tier2Eligible d ∨ kernelDecides d = false := h.2
  by_cases hgate : digitCount d ≤ 19 ∧ -45 ≤ numEff d ∧ numEff d ≤ 45
  · have heff : numEff d = eff d := numEff_eq_eff_of_numGates hgate.1 ⟨hgate.2.1, hgate.2.2⟩
    have hnotier1 : ¬ (digitCount d ≤ 15 ∧ -22 ≤ numEff d ∧ numEff d ≤ 22) := by
      rw [heff]
      intro hs
      exact hnt1 ⟨hs.1, hs.2.1, hs.2.2⟩
    rcases hcase with helig | hk
    · -- eligibility contradicts the gate at the specification's `eff`
      rw [heff] at hgate
      exact absurd ⟨hgate.1, hgate.2.1, hgate.2.2⟩ helig
    · exact numClassOf_fallback_at _ _ _ hgate hnotier1 hk
  · unfold numClassOf
    rw [ite_eq_right hgate]

/-! #### The tier-2 model, and the three clauses composed -/

/-- The emitted tier-2 result, as an encoding: the guard's code with the lexeme's
sign.  `none` (the kernel declined) is not reached by the clause below. -/
def numTier2Binary (d : Decimal) : Binary64 :=
  match LeanLLVM.ElGuardRefine.elTier2Code d.mantissa d.exponent with
  | none => .inf false
  | some c => .fin d.neg c.expField c.mant

/-- The mantissa bound the guard's own statement requires: under nineteen digits
the mantissa is inside the emitted `uint64_t`. -/
theorem mantissa_lt_two_pow_64 {d : Decimal} (hwf : d.wellFormed)
    (hnd : digitCount d ≤ 19) : d.mantissa < 2 ^ 64 := by
  have hlt := StrtodTier1.mantissa_lt_pow hwf
  have h19 : (10 : Nat) ^ digitCount d ≤ 10 ^ 19 := Nat.pow_le_pow_right (by decide) hnd
  have hbig : (10 : Nat) ^ 19 < 2 ^ 64 := by decide
  omega

/-- The overflow threshold is positive. -/
theorem overflowTicks_pos : 0 < overflowTicks := by
  unfold overflowTicks
  have h := Nat.pow_lt_pow_right (a := 2) (by decide) (show 2044 < 2098 by decide)
  omega

/-- A zero mantissa rounds to zero, whatever the denominator. -/
theorem roundMag_zero {D : Nat} (hD : 0 < D) : roundMag 0 D = .fin ⟨0, 0⟩ := by
  have ho : 0 < overflowTicks * D := Nat.mul_pos overflowTicks_pos hD
  have hsub : subCode 0 D = ⟨0, 0⟩ := by
    unfold subCode
    simp only [Nat.zero_div, Nat.zero_mod]
    rw [ite_eq_left hD]
  unfold roundMag
  rw [ite_eq_right (by omega)]
  rw [ite_eq_left (Nat.mul_pos hD (Nat.pow_pos (by decide)))]
  exact congrArg Mag.fin hsub

/-- **The tier-2 model is `strtodSpec`.**  `ElGuardRefine.elGuardRefinesOn` says
the guard's code is `roundMag`'s magnitude at the mantissa and exponent
`num_el_el1` is handed; the mantissa is `d.mantissa` and the exponent is
`d.exponent`, so the code is `d.ticks`'s magnitude and the sign is the lexeme's.
The zero mantissa is the one case outside the guard's statement, and it rounds to
zero on both sides. -/
theorem numTier2Binary_eq_strtodSpec {d : Decimal} (hwf : d.wellFormed)
    (hnd : digitCount d ≤ 19) (h : kernelDecides d = true) :
    numTier2Binary d = strtodSpec d := by
  unfold kernelDecides at h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  unfold numTier2Binary
  rw [hc]
  have hticks : LeanLLVM.ElGuardRefine.valueTicks d.mantissa d.exponent = d.ticks := rfl
  by_cases hzero : d.mantissa = 0
  · -- `elTier2Code`'s zero branch returns `⟨0, 0⟩`
    unfold LeanLLVM.ElGuardRefine.elTier2Code at hc
    cases hp : LeanLLVM.ElGuardRefine.epowAt d.exponent with
    | none => rw [hp] at hc; exact absurd hc (by simp)
    | some t =>
        rw [hp] at hc
        simp only at hc
        rw [hzero] at hc
        simp only [ite_true, Option.some.injEq] at hc
        subst hc
        have hP : d.ticks.1 = 0 := by
          rw [← hticks]
          unfold LeanLLVM.ElGuardRefine.valueTicks
          split <;> simp only [hzero, Nat.zero_mul]
        have hspec : strtodSpec d = .fin d.neg 0 0 := by
          unfold strtodSpec
          rw [hP, roundMag_zero (Decimal.ticks_den_pos d)]
        rw [hspec]
  · have hpos : 0 < d.mantissa := Nat.pos_of_ne_zero hzero
    have h64 := mantissa_lt_two_pow_64 hwf hnd
    have hguard := LeanLLVM.ElGuardRefine.elGuardRefinesOn d.mantissa d.exponent c
      hpos h64 hc
    have hspec : strtodSpec d = Binary64.fin d.neg c.expField c.mant := by
      unfold strtodSpec
      rw [← hticks, hguard]
    rw [hspec]

/-- **The emitted `num_fast` conversion**, as one byte-level function: the
reader's decomposition of the lexeme, the dispatch's choice at the counters, and
the chosen branch's proved model.  The reader is `StrtodReader.reader`, whose
`reader_lexeme` is the decomposition's round trip; the dispatch's counters are
`digitCount`/`numEff`; and a lexeme the reader refuses is `.+inf`, which no
clause below reads (every clause is at a well-formed `d`, and `reader_lexeme`
applies). -/
def numFastEmitted : Bytes → Binary64 := fun bs =>
  match StrtodReader.reader bs with
  | none => .inf false
  | some d =>
      match numClassOf (digitCount d) (numEff d) (kernelDecides d) with
      | .tier1 => StrtodTier1.tier1Emitted StrtodReader.reader bs
      | .kernel => numTier2Binary d
      | .fallback => StrtodTier3.tier3Emitted StrtodReader.reader bs

/-- The tier-1 branch is the tier-1 model's output. -/
theorem numFastEmitted_eq_tier1 {d : Decimal} (hwf : d.wellFormed) (h : Tier1 d) :
    numFastEmitted d.lexeme =
      StrtodTier1.tier1Emitted StrtodReader.reader d.lexeme := by
  simp only [numFastEmitted, StrtodReader.reader_lexeme hwf, numClassOf_tier1 h]

/-- The kernel branch is the guard model's output. -/
theorem numFastEmitted_eq_kernel {d : Decimal} (hwf : d.wellFormed)
    (h : Tier2 d kernelDecides) :
    numFastEmitted d.lexeme = numTier2Binary d := by
  simp only [numFastEmitted, StrtodReader.reader_lexeme hwf, numClassOf_kernel h]

/-- The fallback branch is the sticky conversion's output. -/
theorem numFastEmitted_eq_fallback {d : Decimal} (hwf : d.wellFormed)
    (h : Fallback d kernelDecides) :
    numFastEmitted d.lexeme =
      StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme := by
  simp only [numFastEmitted, StrtodReader.reader_lexeme hwf, numClassOf_fallback h]

/-- **The tier-1 clause**, from `StrtodTier1.emittedRefinesOn_tier1` at
`StrtodReader.reader`: the reader's obligation is `reader_lexeme`, so no reader
parameter remains. -/
theorem numFastEmitted_tier1 : EmittedRefinesOn numFastEmitted Tier1 := by
  intro d hwf h1
  rw [numFastEmitted_eq_tier1 hwf h1]
  exact StrtodReader.tier1_no_reader d hwf h1

/-- **The kernel clause**, from the guard's decision (`ElGuardRefine`) at the
mantissa and exponent the emitted call is handed. -/
theorem numFastEmitted_tier2 : EmittedRefinesOn numFastEmitted (fun d => Tier2 d kernelDecides) := by
  intro d hwf h2
  rw [numFastEmitted_eq_kernel hwf h2]
  exact numTier2Binary_eq_strtodSpec hwf h2.2.1.1 h2.2.2

/-- **The fallback clause**, from `StrtodTier3.emittedRefinesOn_tier3` at the
same reader. -/
theorem numFastEmitted_fallback :
    EmittedRefinesOn numFastEmitted (fun d => Fallback d kernelDecides) := by
  intro d hwf h3
  rw [numFastEmitted_eq_fallback hwf h3]
  exact StrtodReader.tier3_no_reader kernelDecides d hwf h3

/-- **Any class mask inherits the statement.**  The three branches cover every
well-formed lexeme (`branch_cover`), so a clause at any predicate `p` reads one
of them: this is why `IsNormal`, `IsSubnormal` and `IsTie` need no clause of
their own — they name inputs the three branches already cover. -/
theorem emittedRefinesOn_of_classes {emitted : Bytes → Binary64} {kd : Decimal → Bool}
    (h1 : EmittedRefinesOn emitted Tier1)
    (h2 : EmittedRefinesOn emitted (fun d => Tier2 d kd))
    (h3 : EmittedRefinesOn emitted (fun d => Fallback d kd))
    (p : Decimal → Prop) : EmittedRefinesOn emitted p := by
  intro d hwf _
  rcases branch_cover d kd with hc | hc | hc
  · exact h1 d hwf hc
  · exact h2 d hwf hc
  · exact h3 d hwf hc

/-- **The emitted `num_fast` conversion refines `strtodSpec`.**  The three
branches' clauses, and the three magnitude classes as consequences of them. -/
theorem numFastEmitted_refines : EmittedConversionRefines numFastEmitted kernelDecides :=
  ⟨numFastEmitted_tier1, numFastEmitted_tier2, numFastEmitted_fallback,
   emittedRefinesOn_of_classes numFastEmitted_tier1 numFastEmitted_tier2
     numFastEmitted_fallback IsNormal,
   emittedRefinesOn_of_classes numFastEmitted_tier1 numFastEmitted_tier2
     numFastEmitted_fallback IsSubnormal,
   emittedRefinesOn_of_classes numFastEmitted_tier1 numFastEmitted_tier2
     numFastEmitted_fallback IsTie⟩

/-- **The number path's contract**: on every well-formed lexeme the emitted
conversion's eight bytes are `strtodSpec`'s.  This is the binary64 observable the
ruling selects; it is not, and cannot be, a lexeme-preserving equality. -/
theorem numFastEmitted_strtodSpec (d : Decimal) (hwf : d.wellFormed) :
    numFastEmitted d.lexeme = strtodSpec d :=
  LeanLLVM.StrtodRefine.emittedConversionRefines_universal numFastEmitted_refines d hwf

/-- **The number record's payload is the specification's eight bytes.**  The
event stream's number record carries `toBits` of the value the conversion
returned (`stage2.c:1201`'s `out_u64(o, dbits(d))`); at every well-formed lexeme
that is `strtodSpec`'s encoding, so the bytes the record writes are the
specification's. -/
theorem numberPayload_eq_strtodSpec (d : Decimal) (hwf : d.wellFormed) :
    (numFastEmitted d.lexeme).toBits = (strtodSpec d).toBits := by
  rw [numFastEmitted_strtodSpec d hwf]

/-- The number record's bytes, spelled: the tag and the eight bytes
`numberPayload_eq_strtodSpec` identifies. -/
theorem numberRecord_bytes (d : Decimal) :
    numberRecord (strtodSpec d).toBits =
      [[UInt8.ofNat stage2TagNum], wordBytes 8 (strtodSpec d).toBits] :=
  rfl

/-! ### The pin, and what it moves

`s2_walk`'s emitted body is pinned in `LeanLLVM/Refinement/JsonStage2IR.lean`, and
`Stage2WalkObligation` is this module's missing walk as a proposition about that
body.  Two things move from assumed to read off the pin: the body returns a value
at every `ret` (which is what lets a `Satisfies` obligation at the body become a
`CallSatisfies` at a call site), and the obligation yields this record's post at
the ABI's own arguments, so a proof of the loop needs no second statement of what
it owes.  What has not moved is the loop: `Stage2Run` is still the report a model
of the walk must produce, and the completion budget is still the obligation that
resists — now stated on its own (`Stage2WalkCompletes`) and proved identical to
the obligation's first conjunct, with the six clauses reduced to the trace the
loop carries. -/

/-- **The pinned body returns a value at every `ret`, re-exported where the walk's
report is stated.**  A `Satisfies` obligation on the pinned body becomes a
call-site selection only because every `ret` of that body carries a value, and
that is a fact about the pinned AST rather than a hypothesis at the call site. -/
theorem stage2Body_retsValued_at_pin :
    retsValued LeanLLVM.Refinement.JsonStage2IR.stage2Body = true :=
  LeanLLVM.Refinement.JsonStage2IR.stage2Body_retsValued

/-! ### Axiom footprints

The emitted layer's declarations are at `[propext, Quot.sound]` or below;
`numFastEmitted_refines` inherits `Classical.choice` from the three tier models
it composes (`StrtodTier1`'s adapter and `StrtodTier3`'s), exactly as those
modules' own pins record. -/

#print axioms stage2Boundary_of_parts
#print axioms stage2Run_boundary
#print axioms ordered_sum_le
#print axioms arenaLe_of_spans
#print axioms evlen_le_of_records
#print axioms stage2Regions_arena_ev
#print axioms owns_reserve_of_owns_extent
#print axioms Stage2Run.nep_le
#print axioms Stage2Run.arenaLe_of_spans
#print axioms Stage2Run.evLe_of_oneRecordPerEntry
#print axioms Stage2Run.walkOwning_of_written
#print axioms stage2Budget_at_abi
#print axioms stage2Budget_pos_of_pre
#print axioms Γ_stage2at_budget
#print axioms stage2WalkObligation_iff_completion
#print axioms stage2WalkCompletes_mono
#print axioms numFastEmitted_refines
#print axioms numFastEmitted_strtodSpec
#print axioms stage2Body_retsValued_at_pin

end LeanLLVM.Refinement
