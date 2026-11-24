/-
`od_gap_recover`'s whole-function contract: the emitted body's run at the model's
rule.

`JsonStage2HelperOdGap` states the rule `stage2GapRecover` and its post at the
call boundary; the branch modules run the body's units.  This module composes
them: from one staging of the cursor and the document window, the pinned body
runs to `void` and writes exactly the record the rule names — the three words at
the cursor's `e` field, at the offset and with the tag the rule's case table
selects.

Two conventions the statement follows, both the tree's:

* the selection is `stage2Calls stage2SubCalls`, not a parameter, because
  `stage2Calls sub` forwards every symbol it does not answer itself and an
  arbitrary `sub` leaves `num_fast_el1` unconstrained (`JsonStage2Body`,
  `Stage2WalkObligation`'s docstring);
* the body's answer is compared to the model's record, not to its memory.  The
  body's frame holds the call's two slots (`%d` at the caller's `next`, `%ei` at
  `next + 8`), and `num_fast_el1` writes one of them, so the returned memory is
  the record's three words plus those slots and nothing else.  `m = mem` is the
  no-write arm's stronger statement.
-/
import LeanLLVM.Refinement.JsonStage2HelperIROdGapRun
import LeanLLVM.Refinement.JsonStage2HelperIROdGapSteps
import LeanLLVM.Refinement.JsonStage2HelperIROdGapNumber
import LeanLLVM.Refinement.JsonStage2HelperIROdGapSecondScan
import LeanLLVM.Refinement.JsonStage2HelperIROdGapLiteral
import LeanLLVM.Refinement.JsonStage2HelperIROdGapRuleCases

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_writeBytes_frame readBytes_length)
open LeanLLVM.Refinement.BlockEval (stateAt cells denoteCode_gep8_reg)

/-! ### The staging

The cursor's six words at the offsets the rule reads (`0`, `8`, `16`, `24`, `32`,
`1112`), the index word the selection takes, the window's bytes one at a time,
and the three literal reads the capture passes as appended parameters.  `next` is
the caller's allocator base: the body's two slots live at `next` and
`next + 8`, and the record's address must avoid them, which is `hsep`.

The record's address is the cursor's own `e` word, `c + odGapCurE`; `hsep` is a
premise at the helper's boundary, not a consequence — the walk's own staging
supplies it, and a lone call cannot derive where its caller's frame is. -/

/-- The staging `od_gap_recover`'s run starts from. -/
structure OdGapPrep (mem : Mem) (next c pos lt lf ln : Nat) (win : List UInt8) where
  /-- The document's base. -/
  b : Nat
  /-- The document's length. -/
  n : Nat
  /-- The index array. -/
  ix : Nat
  /-- The index count. -/
  nix : Nat
  /-- The next index. -/
  k : Nat
  /-- The refusal record's address. -/
  e : Nat
  /-- The token's end boundary: the selected index word, or the length. -/
  ip : Nat
  hb : readBytes mem c 8 = some (natToBytes b 8)
  hb64 : b < 2 ^ 64
  hn : readBytes mem (c + odGapCurN) 8 = some (natToBytes n 8)
  hn64 : n < 2 ^ 64
  hix : readBytes mem (c + odGapCurIx) 8 = some (natToBytes ix 8)
  hix64 : ix < 2 ^ 64
  hnix : readBytes mem (c + odGapCurNix) 8 = some (natToBytes nix 8)
  hnix64 : nix < 2 ^ 64
  hk : readBytes mem (c + odGapCurK) 8 = some (natToBytes k 8)
  hk64 : k < 2 ^ 64
  hk63 : k < 2 ^ 63
  he : readBytes mem (c + odGapCurE) 8 = some (natToBytes e 8)
  he64 : e < 2 ^ 64
  /-- The index selection: the 32-bit word at `ix + 4k`, or the length. -/
  hidx : k < nix → readBytes mem (ix + 4 * k) 4 = some (natToBytes ip 4)
  hip32 : k < nix → ip < 2 ^ 32
  hnip : nix ≤ k → ip = n
  /-- The token's start is at or below the boundary. -/
  hposip : pos ≤ ip
  hip64 : ip < 2 ^ 64
  hip63 : ip < 2 ^ 63
  /-- The window's bytes, one address at a time, and its length. -/
  hbytes : gapBytesAt mem win b ip
  hlen : win.length = ip
  /-- The three literal reads. -/
  hlt : readBytes mem lt 4 = some gapTrueLit
  hlf : readBytes mem lf 5 = some gapFalseLit
  hln : readBytes mem ln 4 = some gapNullLit
  /-- The record's address is disjoint from the body's two slots. -/
  hsep : DisjointRegions [(next, (Ty.double).sizeBytes + (Ty.int 64).sizeBytes),
    (c + odGapCurE, 24)]
  /-- The document window ends before the body's two slots: the number-acceptance
  row runs the second scan after `num_fast_el1` writes `%d` at `next`, and the
  window is read from `b`.  This is derivable from `Γ_stage2_noevent`'s watermark
  (`b + n ≤ next`) and the invariant's `ip < n`, so it is not a new caller
  burden. -/
  hwin : b + ip ≤ next ∨ next + 16 ≤ b

/-- The effect the rule's write is: no write, or the record at `e`. -/
def gapEffectOf (e : Nat) : GapWrite → GapRecoverEffect
  | .none => .unchanged
  | .err off tag => .wrote e off tag

/-- `stagedState` is `EntryState`: both bind the parameters to the arguments. -/
theorem stagedState_eq_entryState (f : Function) (args : List Value) (mem : Mem)
    (next : Nat) : stagedState f args mem next = EntryState f args mem next := rfl

/-! ### The window as one read

The scan reads the document one byte at a time (`gapBytesAt`); the rule reads it
as a range (`readBytes mem b ip`).  The two agree, which is the rewrite the
composition needs and not a missing lemma. -/

/-- A byte-wise description of a range is the range's own read. -/
theorem readBytes_of_gapBytesAt {mem : Mem} {bytes : List UInt8} {b ip : Nat}
    (h : gapBytesAt mem bytes b ip) (hlen : bytes.length = ip) :
    readBytes mem b ip = some bytes := by
  induction ip generalizing b bytes with
  | zero =>
      cases bytes with
      | nil => rfl
      | cons x xs => simp at hlen
  | succ ip ih =>
      cases bytes with
      | nil => simp at hlen
      | cons x xs =>
          have h0 : readByte mem b = some x := by
            have := h 0 (by omega)
            simpa using this
          have hlen' : xs.length = ip := by simpa using hlen
          have htail : gapBytesAt mem xs (b + 1) ip := by
            intro i hi
            have hh := h (i + 1) (by omega)
            rw [show b + (i + 1) = b + 1 + i from by omega] at hh
            simpa using hh
          show (match readByte mem b with
            | none => none
            | some byte => match readBytes mem (b + 1) ip with
                           | none => none
                           | some bs => some (byte :: bs)) = some (x :: xs)
          rw [h0, ih htail hlen']

/-! ### The rule at a staging

The six words, the index selection, and the window determine the rule's answer:
it is `gapRecoverWrite`'s write, lifted to the effect at the cursor's `e`. -/

theorem stage2GapRecoverRule_of_prep {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win) :
    stage2GapRecoverRule mem c pos =
      some (gapEffectOf P.e (gapRecoverWrite win P.ip pos)) := by
  have wb : stage2ReadWord mem c 8 = some P.b := gap_readWord P.hb P.hb64
  have hn : stage2ReadWord mem (c + 8) 8 = some P.n := by
    have := gap_readWord P.hn P.hn64
    simpa only [odGapCurN] using this
  have hix : stage2ReadWord mem (c + 16) 8 = some P.ix := by
    have := gap_readWord P.hix P.hix64
    simpa only [odGapCurIx] using this
  have hnix : stage2ReadWord mem (c + 24) 8 = some P.nix := by
    have := gap_readWord P.hnix P.hnix64
    simpa only [odGapCurNix] using this
  have hk : stage2ReadWord mem (c + 32) 8 = some P.k := by
    have := gap_readWord P.hk P.hk64
    simpa only [odGapCurK] using this
  have he : stage2ReadWord mem (c + 1112) 8 = some P.e := by
    have := gap_readWord P.he P.he64
    simpa only [odGapCurE] using this
  have hidx : ∀ (_ : P.k < P.nix), stage2ReadWord mem (P.ix + 4 * P.k) 4 = some P.ip := by
    intro hklt
    exact gap_readWord4 (P.hidx hklt) (P.hip32 hklt)
  have hbytes : readBytes mem P.b P.ip = some win :=
    readBytes_of_gapBytesAt P.hbytes P.hlen
  unfold stage2GapRecoverRule
  simp only [odGapCurN, odGapCurIx, odGapCurNix, odGapCurK, odGapCurE]
  simp only [wb, hn, hix, hnix, hk, he]
  by_cases hklt : P.k < P.nix
  · simp only [if_pos hklt, hidx hklt, hbytes]
    cases gapRecoverWrite win P.ip pos <;> rfl
  · simp only [if_neg hklt, ← P.hnip (by omega), hbytes]
    cases gapRecoverWrite win P.ip pos <;> rfl

/-! ### The entry prefix

The two branches of the index selection reach `cond.end` with the boundary word
in `%cond` and the token's position in `%t.0.val`; three control steps, the two
allocations included in the state the entry leaves.  Both branches are stated at
the same postcondition, so the composition below reads the boundary without
knowing which one ran. -/

theorem gapSizeBytes_double : (Ty.double).sizeBytes = 8 := rfl

theorem gapSizeBytes_i64 : (Ty.int 64).sizeBytes = 8 := rfl

/-- The prep's disjointness, as the arithmetic the reads consume. -/
theorem odGapPrep_sep {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win) :
    next + 16 ≤ c + odGapCurE ∨ c + odGapCurE + 24 ≤ next := by
  have h := P.hsep
  unfold DisjointRegions at h
  have h1 : (next + (8 + 8) ≤ c + odGapCurE ∨ c + odGapCurE + 24 ≤ next) := by
    have hp := List.pairwise_cons.mp h
    have hh := hp.1 (c + odGapCurE, 24) (by simp)
    simpa only [gapSizeBytes_double, gapSizeBytes_i64] using hh
  have hcE : odGapCurE = 1112 := rfl
  omega

/-- The staged entry state, spelled out. -/
theorem gapEntryState_eq {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win) :
    EntryState odGapRecoverBody
        [.ptr c, .int 64 (BitVec.ofNat 64 pos), .ptr lt, .ptr lf, .ptr ln]
        mem next =
      { env := [("%c", .ptr c), ("%t.0.val", .int 64 (BitVec.ofNat 64 pos)),
                ("%littrue", .ptr lt), ("%litfalse", .ptr lf), ("%litnull", .ptr ln)],
        mem := mem, next := next, pc := "entry", pre := none } := rfl
/-! ### The entry prefix

Two control steps — the entry block's two allocations folded into the state it
leaves, and the index selection's branch — reach `cond.end` with the boundary
word in `%cond` and the token's position still in `%t.0.val`.  The two branches
are separate statements because their `cond.end` step reads different cells, and
the composition below keeps the boundary in `%conv`/`%5` so that the step is the
one the branch module proved. -/

/-- The staged entry state's argument list. -/
def odGapEntryArgs (c pos lt lf ln : Nat) : List Value :=
  [.ptr c, .int 64 (BitVec.ofNat 64 pos), .ptr lt, .ptr lf, .ptr ln]

/-- The unsigned comparison at one is the natural order below `2 ^ 64`. -/
theorem gap_ult_of_one {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : evalICmp .ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 1#1) : a < b := by
  rw [evalICmp, BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  by_contra hc
  rw [decide_eq_false (by omega)] at h
  exact absurd h (by decide)

/-- The entry's own eight instructions leave the two slots allocated and the
branch decided: two control steps to `cond.end` through `cond.true`. -/
theorem gapPrefix_true {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (hklt : P.k < P.nix) :
    ∃ s : State,
      (∀ k, runFuel (stage2Calls stage2SubCalls) (2 + k) odGapRecoverBody
          (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) =
        runFuel (stage2Calls stage2SubCalls) k odGapRecoverBody s) ∧
      s.pc = "cond.end" ∧ s.pre = some "cond.true" ∧ s.mem = mem ∧
      s.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes ∧
      lookupName s.env "%0" = some (.ptr P.b) ∧
      lookupName s.env "%c" = some (.ptr c) ∧
      lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) ∧
      lookupName s.env "%d" = some (.ptr next) ∧
      lookupName s.env "%ei" = some (.ptr (next + (Ty.double).sizeBytes)) ∧
      lookupName s.env "%littrue" = some (.ptr lt) ∧
      lookupName s.env "%litfalse" = some (.ptr lf) ∧
      lookupName s.env "%litnull" = some (.ptr ln) ∧
      lookupName s.env "%conv" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
  let s0 : State :=
    { env := [("%c", .ptr c), ("%t.0.val", .int 64 (BitVec.ofNat 64 pos)),
              ("%littrue", .ptr lt), ("%litfalse", .ptr lf), ("%litnull", .ptr ln)],
      mem := mem, next := next, pc := "entry", pre := none }
  have hentry : EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next = s0 := rfl
  have hc0 : lookupName s0.env "%c" = some (.ptr c) := by simp only [s0]; block_lk
  have hb0 : readBytes s0.mem c 8 = some (natToBytes P.b 8) := P.hb
  have hk0 : readBytes s0.mem (c + 32) 8 = some (natToBytes P.k 8) := by
    simpa only [s0, odGapCurK] using P.hk
  have hnix0 : readBytes s0.mem (c + 24) 8 = some (natToBytes P.nix 8) := by
    simpa only [s0, odGapCurNix] using P.hnix
  let env1 : Env := gapEntryEnv s0.env next c P.b P.k P.nix
  let s1 : State := stateAt env1 { s0 with next := s0.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes, pc := "cond.true", pre := some "entry" }
  have hbit : evalICmp .ult (BitVec.ofNat 64 P.k) (BitVec.ofNat 64 P.nix) = 1#1 :=
    gap_ult_one P.hk64 P.hnix64 hklt
  have h1 : step (stage2Calls stage2SubCalls) odGapRecoverBody s0 = .jump s1 := by
    have hh := gap_step_entry (calls := stage2Calls stage2SubCalls) (env := s0.env)
      (s := s0) (c := c) (b := P.b) (k := P.k) (nix := P.nix) rfl hc0 hb0 P.hb64 hk0
      P.hk64 hnix0 P.hnix64
    rw [hbit, if_pos rfl] at hh
    have hst : stateAt s0.env s0 = s0 := rfl
    simpa only [hst, s1, env1] using hh
  have hc1 : lookupName env1 "%c" = some (.ptr c) := by
    simp only [env1, gapEntryEnv]; block_lk
  have h1cell : lookupName env1 "%1" = some (.int 64 (BitVec.ofNat 64 P.k)) := by
    simp only [env1, gapEntryEnv]; block_lk
  have hix1 : readBytes s1.mem (c + 16) 8 = some (natToBytes P.ix 8) := by
    simpa only [s1, stateAt, odGapCurIx] using P.hix
  have hidx1 : readBytes s1.mem (P.ix + P.k * 4) 4 = some (natToBytes P.ip 4) := by
    rw [Nat.mul_comm]
    simpa only [s1, stateAt] using P.hidx hklt
  let env2 : Env := ("%conv", .int 64 (BitVec.ofNat 64 P.ip)) ::
    ("%4", .int 32 (BitVec.ofNat 32 P.ip)) :: ("%arrayidx", .ptr (P.ix + P.k * 4)) ::
    ("%3", .ptr P.ix) :: ("%ix", .ptr (c + 16)) :: env1
  let s2 : State := stateAt env2 { s1 with pc := "cond.end", pre := some "cond.true" }
  have h2 : step (stage2Calls stage2SubCalls) odGapRecoverBody s1 = .jump s2 := by
    have hh := gap_step_condTrue (calls := stage2Calls stage2SubCalls) (env := env1)
      (s := s1) (c := c) (k := P.k) (ix := P.ix) (idx := P.ip) rfl rfl hc1 h1cell
      hix1 P.hix64 P.hk64 P.hk63 hidx1 (P.hip32 hklt)
    have hst : stateAt env1 s1 = s1 := rfl
    simpa only [hst, s2, env2] using hh
  have hd2 : lookupName env2 "%d" = some (.ptr next) := by
    simp only [env2, env1, gapEntryEnv]; block_lk
  have hei2 : lookupName env2 "%ei" = some (.ptr (next + (Ty.double).sizeBytes)) := by
    simp only [env2, env1, gapEntryEnv]; block_lk
  have hlt2 : lookupName env2 "%littrue" = some (.ptr lt) := by
    simp only [env2, s0]; block_lk
  have hlf2 : lookupName env2 "%litfalse" = some (.ptr lf) := by
    simp only [env2, s0]; block_lk
  have hln2 : lookupName env2 "%litnull" = some (.ptr ln) := by
    simp only [env2, s0]; block_lk
  have hconv2 : lookupName env2 "%conv" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simp only [env2, lookupName_cons_self]
  have ht2 : lookupName env2 "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) := by
    simp only [env2, env1, gapEntryEnv]; block_lk
  have h02 : lookupName env2 "%0" = some (.ptr P.b) := by
    simp only [env2, env1, gapEntryEnv]; block_lk
  have hc2 : lookupName env2 "%c" = some (.ptr c) := by
    simp only [env2, env1, gapEntryEnv]; block_lk
  refine ⟨s2, ?_, rfl, rfl, ?_, (by simp only [s2, s1, s0, stateAt]), h02, hc2, ht2, hd2, hei2, hlt2, hlf2, hln2, hconv2⟩
  · intro k
    rw [hentry, show 2 + k = 1 + (1 + k) from by omega,
      runFuel_jump_prefix h1 (1 + k), runFuel_jump_prefix h2 k]
  · simp only [s2, s1, s0, stateAt]

/-- The same two steps through `cond.false`: no index word is read, and the
length is the boundary. -/
theorem gapPrefix_false {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (hnk : ¬ P.k < P.nix) :
    ∃ s : State,
      (∀ k, runFuel (stage2Calls stage2SubCalls) (2 + k) odGapRecoverBody
          (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) =
        runFuel (stage2Calls stage2SubCalls) k odGapRecoverBody s) ∧
      s.pc = "cond.end" ∧ s.pre = some "cond.false" ∧ s.mem = mem ∧
      s.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes ∧
      lookupName s.env "%0" = some (.ptr P.b) ∧
      lookupName s.env "%c" = some (.ptr c) ∧
      lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) ∧
      lookupName s.env "%d" = some (.ptr next) ∧
      lookupName s.env "%ei" = some (.ptr (next + (Ty.double).sizeBytes)) ∧
      lookupName s.env "%littrue" = some (.ptr lt) ∧
      lookupName s.env "%litfalse" = some (.ptr lf) ∧
      lookupName s.env "%litnull" = some (.ptr ln) ∧
      lookupName s.env "%5" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
  let s0 : State :=
    { env := [("%c", .ptr c), ("%t.0.val", .int 64 (BitVec.ofNat 64 pos)),
              ("%littrue", .ptr lt), ("%litfalse", .ptr lf), ("%litnull", .ptr ln)],
      mem := mem, next := next, pc := "entry", pre := none }
  have hentry : EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next = s0 := rfl
  have hc0 : lookupName s0.env "%c" = some (.ptr c) := by simp only [s0]; block_lk
  have hb0 : readBytes s0.mem c 8 = some (natToBytes P.b 8) := P.hb
  have hk0 : readBytes s0.mem (c + 32) 8 = some (natToBytes P.k 8) := by
    simpa only [s0, odGapCurK] using P.hk
  have hnix0 : readBytes s0.mem (c + 24) 8 = some (natToBytes P.nix 8) := by
    simpa only [s0, odGapCurNix] using P.hnix
  let env1 : Env := gapEntryEnv s0.env next c P.b P.k P.nix
  let s1 : State := stateAt env1 { s0 with next := s0.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes, pc := "cond.false", pre := some "entry" }
  have hbit : evalICmp .ult (BitVec.ofNat 64 P.k) (BitVec.ofNat 64 P.nix) = 0#1 := by
    rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one
      (evalICmp .ult (BitVec.ofNat 64 P.k) (BitVec.ofNat 64 P.nix)) with h | h
    · exact h
    · exact absurd (gap_ult_of_one P.hk64 P.hnix64 h) hnk
  have h1 : step (stage2Calls stage2SubCalls) odGapRecoverBody s0 = .jump s1 := by
    have hh := gap_step_entry (calls := stage2Calls stage2SubCalls) (env := s0.env)
      (s := s0) (c := c) (b := P.b) (k := P.k) (nix := P.nix) rfl hc0 hb0 P.hb64 hk0
      P.hk64 hnix0 P.hnix64
    rw [hbit] at hh
    rw [if_neg (by decide)] at hh
    have hst : stateAt s0.env s0 = s0 := rfl
    simpa only [hst, s1, env1] using hh
  have hc1 : lookupName env1 "%c" = some (.ptr c) := by
    simp only [env1, gapEntryEnv]; block_lk
  have hn1 : readBytes s1.mem (c + 8) 8 = some (natToBytes P.n 8) := by
    simpa only [s1, stateAt, odGapCurN] using P.hn
  let env2 : Env := ("%5", .int 64 (BitVec.ofNat 64 P.ip)) ::
    ("%n", .ptr (c + 8)) :: env1
  let s2 : State := stateAt env2 { s1 with pc := "cond.end", pre := some "cond.false" }
  have hnp : P.n = P.ip := (P.hnip (by omega)).symm
  have h2 : step (stage2Calls stage2SubCalls) odGapRecoverBody s1 = .jump s2 := by
    have hh := gap_step_condFalse (calls := stage2Calls stage2SubCalls) (env := env1)
      (s := s1) (c := c) (n := P.n) rfl rfl hc1 hn1 P.hn64
    have hst : stateAt env1 s1 = s1 := rfl
    rw [hst] at hh
    simpa only [s2, env2, ← hnp] using hh
  have hd2 : lookupName env2 "%d" = some (.ptr next) := by
    simp only [env2, env1, gapEntryEnv]; block_lk
  have hei2 : lookupName env2 "%ei" = some (.ptr (next + (Ty.double).sizeBytes)) := by
    simp only [env2, env1, gapEntryEnv]; block_lk
  have hlt2 : lookupName env2 "%littrue" = some (.ptr lt) := by
    simp only [env2, s0]; block_lk
  have hlf2 : lookupName env2 "%litfalse" = some (.ptr lf) := by
    simp only [env2, s0]; block_lk
  have hln2 : lookupName env2 "%litnull" = some (.ptr ln) := by
    simp only [env2, s0]; block_lk
  have h52 : lookupName env2 "%5" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simp only [env2, lookupName_cons_self]
  have ht2 : lookupName env2 "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) := by
    simp only [env2, env1, gapEntryEnv]; block_lk
  have h02 : lookupName env2 "%0" = some (.ptr P.b) := by
    simp only [env2, env1, gapEntryEnv]; block_lk
  have hc2 : lookupName env2 "%c" = some (.ptr c) := by
    simp only [env2, env1, gapEntryEnv]; block_lk
  refine ⟨s2, ?_, rfl, rfl, ?_, (by simp only [s2, s1, s0, stateAt]), h02, hc2, ht2, hd2, hei2, hlt2, hlf2, hln2, h52⟩
  · intro k
    rw [hentry, show 2 + k = 1 + (1 + k) from by omega,
      runFuel_jump_prefix h1 (1 + k), runFuel_jump_prefix h2 k]
  · simp only [s2, s1, s0, stateAt]

/-! ### The window's end

From the scan's own seed the first loop runs to its end and `cleanup82` returns
the caller's memory.  The model's rule writes nothing at that exit, which is the
no-write row's second path. -/

/-- `hnextS` is the scan invariant's ninth cell, supplied by `gapPrefix_*`'s own
`hnextP`. -/
private theorem gapScan_to_cleanup_none {mem : Mem} {bytes : List UInt8}
    {ip b pos c next lt lf ln : Nat}
    (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (hEe : gapEe bytes ip pos = ip) (hposlt : pos < ip) (hiplt : ip < 2 ^ 63)
    (s : State) (hpc : s.pc = "land.rhs") (hpre : s.pre = some "cond.end")
    (hmem : s.mem = mem)
    (hnextS : s.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes)
    (hb : lookupName s.env "%0" = some (.ptr b))
    (hcur : lookupName s.env "%c" = some (.ptr c))
    (ht : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hd : lookupName s.env "%d" = some (.ptr next))
    (hei : lookupName s.env "%ei" = some (.ptr (next + (Ty.double).sizeBytes)))
    (hltc : lookupName s.env "%littrue" = some (.ptr lt))
    (hlfc : lookupName s.env "%litfalse" = some (.ptr lf))
    (hlnc : lookupName s.env "%litnull" = some (.ptr ln)) :
    ∃ j : Nat, j ≤ (ip + 1) * 5 + 1 ∧
      runFuel (stage2Calls stage2SubCalls) j odGapRecoverBody s = some (.ret none mem) := by
  have hinv : gapScanInv bytes ip b pos c next lt lf ln mem ip s pos :=
    gapScanInv_seed hposlt hiplt hpc hpre hmem hnextS hb hcur ht hcond hd hei hltc hlfc hlnc
  obtain ⟨e, j, hj, _, hexit, hrun⟩ :=
    gapScanLoop_run (calls := stage2Calls stage2SubCalls) (cur := c) (next := next)
      (lt := lt) (lf := lf) (ln := ln) hbytes hblen s pos hinv 1
  have hpcE : e.pc = "cleanup82" := by
    rcases hexit with ⟨leaf, cc, hpc1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
      | ⟨hpc2, _⟩
    · exfalso; omega
    · exact hpc2
  obtain ⟨hret, _⟩ :=
    gap_scan_cleanup82_continue (calls := stage2Calls stage2SubCalls) hpcE hexit
  have hmemE : e.mem = mem := by
    rcases hexit with ⟨leaf, cc, hpc1, hpre1, hm, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
      | ⟨_, hm, _⟩
    · rw [hpcE] at hpc1
      exact absurd hpc1 (by decide)
    · exact hm
  refine ⟨j + 1, by omega, ?_⟩
  rw [show j + 1 = j + 1 from rfl, hrun]
  exact gapNum_runFuel_ret_void hret hmemE
/-! ### `cond.end`'s two edges

The boundary test is `%t.0.val < %cond`; the block leaves for `land.rhs` when it
holds and for `while.end` when it does not.  The two branch modules' steps are
specialised here at the predicate the composition has already decided: `pos < ip`
on one edge, `pos = ip` on the other. -/

theorem gapCondEnd_landRhs_true {pos ip : Nat} {s : State}
    (hpc : s.pc = "cond.end") (hpre : s.pre = some "cond.true")
    (ht : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)))
    (hconv : lookupName s.env "%conv" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hip64 : ip < 2 ^ 64) (hpos : pos < ip) :
    step (stage2Calls stage2SubCalls) odGapRecoverBody s =
      .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 pos)
          (BitVec.ofNat 64 ip))) :: ("%cond", .int 64 (BitVec.ofNat 64 ip)) :: s.env)
        { s with pc := "land.rhs", pre := some "cond.end" }) := by
  have hbit : evalICmp .ult (BitVec.ofNat 64 pos) (BitVec.ofNat 64 ip) = 1#1 :=
    gap_ult_one (by omega) hip64 hpos
  have hh := gap_step_condEnd_fromTrue (calls := stage2Calls stage2SubCalls) (env := s.env)
    (s := s) (p0 := pos) (idx := ip) hpc hpre ht hconv hip64
  rw [hbit, if_pos rfl] at hh
  have hst : stateAt s.env s = s := rfl
  simpa only [hst, ← hbit] using hh

theorem gapCondEnd_whileEnd_true {pos ip : Nat} {s : State}
    (hpc : s.pc = "cond.end") (hpre : s.pre = some "cond.true")
    (ht : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)))
    (hconv : lookupName s.env "%conv" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hip64 : ip < 2 ^ 64) (hpos : pos = ip) :
    step (stage2Calls stage2SubCalls) odGapRecoverBody s =
      .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 pos)
          (BitVec.ofNat 64 ip))) :: ("%cond", .int 64 (BitVec.ofNat 64 ip)) :: s.env)
        { s with pc := "while.end", pre := some "cond.end" }) := by
  have hbit : evalICmp .ult (BitVec.ofNat 64 pos) (BitVec.ofNat 64 ip) = 0#1 := by
    rw [hpos]; exact gap_ult_self _
  have hh := gap_step_condEnd_fromTrue (calls := stage2Calls stage2SubCalls) (env := s.env)
    (s := s) (p0 := pos) (idx := ip) hpc hpre ht hconv hip64
  rw [hbit] at hh
  rw [if_neg (by decide)] at hh
  have hst : stateAt s.env s = s := rfl
  simpa only [hst, ← hbit] using hh

theorem gapCondEnd_landRhs_false {pos ip : Nat} {s : State}
    (hpc : s.pc = "cond.end") (hpre : s.pre = some "cond.false")
    (ht : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)))
    (h5 : lookupName s.env "%5" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hip64 : ip < 2 ^ 64) (hpos : pos < ip) :
    step (stage2Calls stage2SubCalls) odGapRecoverBody s =
      .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 pos)
          (BitVec.ofNat 64 ip))) :: ("%cond", .int 64 (BitVec.ofNat 64 ip)) :: s.env)
        { s with pc := "land.rhs", pre := some "cond.end" }) := by
  have hbit : evalICmp .ult (BitVec.ofNat 64 pos) (BitVec.ofNat 64 ip) = 1#1 :=
    gap_ult_one (by omega) hip64 hpos
  have hh := gap_step_condEnd_fromFalse (calls := stage2Calls stage2SubCalls) (env := s.env)
    (s := s) (p0 := pos) (n := ip) hpc hpre ht h5 hip64
  rw [hbit, if_pos rfl] at hh
  have hst : stateAt s.env s = s := rfl
  simpa only [hst, ← hbit] using hh

theorem gapCondEnd_whileEnd_false {pos ip : Nat} {s : State}
    (hpc : s.pc = "cond.end") (hpre : s.pre = some "cond.false")
    (ht : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)))
    (h5 : lookupName s.env "%5" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hip64 : ip < 2 ^ 64) (hpos : pos = ip) :
    step (stage2Calls stage2SubCalls) odGapRecoverBody s =
      .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 pos)
          (BitVec.ofNat 64 ip))) :: ("%cond", .int 64 (BitVec.ofNat 64 ip)) :: s.env)
        { s with pc := "while.end", pre := some "cond.end" }) := by
  have hbit : evalICmp .ult (BitVec.ofNat 64 pos) (BitVec.ofNat 64 ip) = 0#1 := by
    rw [hpos]; exact gap_ult_self _
  have hh := gap_step_condEnd_fromFalse (calls := stage2Calls stage2SubCalls) (env := s.env)
    (s := s) (p0 := pos) (n := ip) hpc hpre ht h5 hip64
  rw [hbit] at hh
  rw [if_neg (by decide)] at hh
  have hst : stateAt s.env s = s := rfl
  simpa only [hst, ← hbit] using hh

/-! ### The zero-gap return

`pos = ip`: the boundary test fails, `while.end`'s equality holds, and
`cleanup82` returns the caller's memory.  Two steps after `cond.end`. -/

theorem gapWhileEnd_to_cleanup {ip : Nat} {s : State}
    (hpc : s.pc = "while.end") (hpre : s.pre = some "cond.end")
    (ht : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hip64 : ip < 2 ^ 64) :
    step (stage2Calls stage2SubCalls) odGapRecoverBody s =
      .jump (stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 ip)
          (BitVec.ofNat 64 ip))) :: ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 ip)) :: s.env)
        { s with pc := "cleanup82", pre := some "while.end" }) := by
  have hh := gap_step_whileEnd_fromCondEnd (calls := stage2Calls stage2SubCalls)
    (env := s.env) (s := s) (ip := ip) hpc hpre ht hcond hip64
  have hst : stateAt s.env s = s := rfl
  simpa only [hst] using hh
/-! ### The no-write rows

`gapRecoverWrite` answers `none` exactly when the first loop reaches `ip`; the
body then writes nothing on either of its two paths — `pos = ip` straight from
`cond.end`, and `pos < ip` through the scan to `cleanup82`.  Both index branches
are stated, because `cond.true` and `cond.false` reach `cond.end` with different
cells. -/

theorem gapExtraWrite_ne_none (bytes : List UInt8) (ip ee : Nat) :
    gapExtraWrite bytes ip ee ≠ GapWrite.none := by
  intro h; unfold gapExtraWrite at h; simp at h

theorem gapLiteralWrite_ne_none (bytes : List UInt8) (ip pos ee : Nat)
    (seg lit : List UInt8) : gapLiteralWrite bytes ip pos ee seg lit ≠ GapWrite.none := by
  intro h
  unfold gapLiteralWrite at h
  cases hh : litCheck seg lit <;> simp [hh, gapExtraWrite] at h

theorem gapAfterLoop_ne_none (bytes : List UInt8) (ip pos ee : Nat) :
    gapAfterLoop bytes ip pos ee ≠ GapWrite.none := by
  intro h
  unfold gapAfterLoop at h
  dsimp only at h
  split at h
  · split at h
    · unfold gapExtraWrite at h; simp at h
    · simp at h
  · split at h
    · exact gapLiteralWrite_ne_none bytes ip pos ee _ _ h
    · split at h
      · exact gapLiteralWrite_ne_none bytes ip pos ee _ _ h
      · split at h
        · exact gapLiteralWrite_ne_none bytes ip pos ee _ _ h
        · simp at h

/-- The rule writes nothing exactly when the first loop reaches the boundary. -/
theorem gapRecoverWrite_none_iff {bytes : List UInt8} {ip pos : Nat} :
    gapRecoverWrite bytes ip pos = GapWrite.none ↔ gapEe bytes ip pos = ip := by
  unfold gapRecoverWrite
  by_cases h : gapEe bytes ip pos = ip
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    constructor
    · intro hh
      exact absurd hh (gapAfterLoop_ne_none bytes ip pos (gapEe bytes ip pos))
    · intro hh; exact absurd hh h

theorem gapRun_none_scan_true {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (hklt : P.k < P.nix) (hposlt : pos < P.ip) (hEe : gapEe win P.ip pos = P.ip) :
    ∃ B : Nat, B ≤ 4 + (P.ip + 1) * 5 ∧
      runFuel (stage2Calls stage2SubCalls) B odGapRecoverBody
        (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) = some (.ret none mem) := by
  obtain ⟨s, hrun, hpc, hpre, hmem, hnextP, h0, hcur, ht, hd, hei, hltc, hlfc, hlnc, hconv⟩ :=
    gapPrefix_true P hklt
  let sH : State := stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 pos)
      (BitVec.ofNat 64 P.ip))) :: ("%cond", .int 64 (BitVec.ofNat 64 P.ip)) :: s.env)
    { s with pc := "land.rhs", pre := some "cond.end" }
  have hstep : step (stage2Calls stage2SubCalls) odGapRecoverBody s = .jump sH :=
    gapCondEnd_landRhs_true (s := s) hpc hpre ht hconv P.hip64 hposlt
  have hHb : lookupName sH.env "%0" = some (.ptr P.b) := by
    simp only [sH, stateAt]; block_lk
  have hHt : lookupName sH.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) := by
    simp only [sH, stateAt]; block_lk
  have hHc : lookupName sH.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simp only [sH, stateAt]; block_lk
  have hHcur : lookupName sH.env "%c" = some (.ptr c) := by
    simp only [sH, stateAt]; block_lk
  have hHm : sH.mem = mem := by simp only [sH, stateAt]; exact hmem
  have hHnext : sH.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes := by
    simp only [sH, stateAt]; exact hnextP
  obtain ⟨j, hj, hrun2⟩ := gapScan_to_cleanup_none (mem := mem) (bytes := win)
    (ip := P.ip) (b := P.b) (pos := pos) (c := c) (next := next) (lt := lt) (lf := lf)
    (ln := ln) P.hbytes P.hlen hEe hposlt P.hip63 sH rfl rfl hHm hHnext hHb hHcur hHt hHc
    hd hei hltc hlfc hlnc
  refine ⟨2 + 1 + j, by omega, ?_⟩
  rw [show 2 + 1 + j = 2 + (1 + j) from by omega]
  rw [hrun (1 + j), runFuel_jump_prefix hstep j]
  exact hrun2

theorem gapRun_none_scan_false {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (hnk : ¬ P.k < P.nix) (hposlt : pos < P.ip) (hEe : gapEe win P.ip pos = P.ip) :
    ∃ B : Nat, B ≤ 4 + (P.ip + 1) * 5 ∧
      runFuel (stage2Calls stage2SubCalls) B odGapRecoverBody
        (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) = some (.ret none mem) := by
  obtain ⟨s, hrun, hpc, hpre, hmem, hnextP, h0, hcur, ht, hd, hei, hltc, hlfc, hlnc, h5⟩ :=
    gapPrefix_false P hnk
  let sH : State := stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 pos)
      (BitVec.ofNat 64 P.ip))) :: ("%cond", .int 64 (BitVec.ofNat 64 P.ip)) :: s.env)
    { s with pc := "land.rhs", pre := some "cond.end" }
  have hstep : step (stage2Calls stage2SubCalls) odGapRecoverBody s = .jump sH :=
    gapCondEnd_landRhs_false (s := s) hpc hpre ht h5 P.hip64 hposlt
  have hHb : lookupName sH.env "%0" = some (.ptr P.b) := by
    simp only [sH, stateAt]; block_lk
  have hHt : lookupName sH.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) := by
    simp only [sH, stateAt]; block_lk
  have hHc : lookupName sH.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simp only [sH, stateAt]; block_lk
  have hHcur : lookupName sH.env "%c" = some (.ptr c) := by
    simp only [sH, stateAt]; block_lk
  have hHm : sH.mem = mem := by simp only [sH, stateAt]; exact hmem
  have hHnext : sH.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes := by
    simp only [sH, stateAt]; exact hnextP
  obtain ⟨j, hj, hrun2⟩ := gapScan_to_cleanup_none (mem := mem) (bytes := win)
    (ip := P.ip) (b := P.b) (pos := pos) (c := c) (next := next) (lt := lt) (lf := lf)
    (ln := ln) P.hbytes P.hlen hEe hposlt P.hip63 sH rfl rfl hHm hHnext hHb hHcur hHt hHc
    hd hei hltc hlfc hlnc
  refine ⟨2 + 1 + j, by omega, ?_⟩
  rw [show 2 + 1 + j = 2 + (1 + j) from by omega]
  rw [hrun (1 + j), runFuel_jump_prefix hstep j]
  exact hrun2

/-- The zero-gap run: five steps from the entry, and the memory comes back as it
went in.  Stated once per index branch. -/
theorem gapRun_none_atIp_true {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (hklt : P.k < P.nix) (hpos : pos = P.ip) :
    ∃ B : Nat, B ≤ 5 ∧
      runFuel (stage2Calls stage2SubCalls) B odGapRecoverBody
        (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) = some (.ret none mem) := by
  obtain ⟨s, hrun, hpc, hpre, hmem, hnextP, h0, hcur, ht, hd, hei, hltc, hlfc, hlnc, hconv⟩ :=
    gapPrefix_true P hklt
  have ht' : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simpa only [hpos] using ht
  let sW : State := stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 pos)
      (BitVec.ofNat 64 P.ip))) :: ("%cond", .int 64 (BitVec.ofNat 64 P.ip)) :: s.env)
    { s with pc := "while.end", pre := some "cond.end" }
  have hstep : step (stage2Calls stage2SubCalls) odGapRecoverBody s = .jump sW :=
    gapCondEnd_whileEnd_true (s := s) hpc hpre ht hconv P.hip64 hpos
  have hWt : lookupName sW.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simp only [sW, stateAt]; block_lk
  have hWc : lookupName sW.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simp only [sW, stateAt]; block_lk
  let sC : State := stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 P.ip)
      (BitVec.ofNat 64 P.ip))) :: ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 P.ip)) :: sW.env)
    { sW with pc := "cleanup82", pre := some "while.end" }
  have hstep2 : step (stage2Calls stage2SubCalls) odGapRecoverBody sW = .jump sC :=
    gapWhileEnd_to_cleanup (s := sW) rfl rfl hWt hWc P.hip64
  have hmC : sC.mem = mem := by simp only [sC, sW, stateAt]; exact hmem
  have hret : step (stage2Calls stage2SubCalls) odGapRecoverBody sC = .ret none sC :=
    gap_step_cleanup82 (calls := stage2Calls stage2SubCalls) (env := sC.env) (s := sC) rfl
  refine ⟨5, by omega, ?_⟩
  rw [show 5 = 2 + (1 + (1 + 1)) from by omega, hrun (1 + (1 + 1)),
    runFuel_jump_prefix hstep (1 + 1), runFuel_jump_prefix hstep2 1]
  exact gapNum_runFuel_ret_void hret hmC

theorem gapRun_none_atIp_false {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (hnk : ¬ P.k < P.nix) (hpos : pos = P.ip) :
    ∃ B : Nat, B ≤ 5 ∧
      runFuel (stage2Calls stage2SubCalls) B odGapRecoverBody
        (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) = some (.ret none mem) := by
  obtain ⟨s, hrun, hpc, hpre, hmem, hnextP, h0, hcur, ht, hd, hei, hltc, hlfc, hlnc, h5⟩ :=
    gapPrefix_false P hnk
  have ht' : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simpa only [hpos] using ht
  let sW : State := stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 pos)
      (BitVec.ofNat 64 P.ip))) :: ("%cond", .int 64 (BitVec.ofNat 64 P.ip)) :: s.env)
    { s with pc := "while.end", pre := some "cond.end" }
  have hstep : step (stage2Calls stage2SubCalls) odGapRecoverBody s = .jump sW :=
    gapCondEnd_whileEnd_false (s := s) hpc hpre ht h5 P.hip64 hpos
  have hWt : lookupName sW.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simp only [sW, stateAt]; block_lk
  have hWc : lookupName sW.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simp only [sW, stateAt]; block_lk
  let sC : State := stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 P.ip)
      (BitVec.ofNat 64 P.ip))) :: ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 P.ip)) :: sW.env)
    { sW with pc := "cleanup82", pre := some "while.end" }
  have hstep2 : step (stage2Calls stage2SubCalls) odGapRecoverBody sW = .jump sC :=
    gapWhileEnd_to_cleanup (s := sW) rfl rfl hWt hWc P.hip64
  have hmC : sC.mem = mem := by simp only [sC, sW, stateAt]; exact hmem
  have hret : step (stage2Calls stage2SubCalls) odGapRecoverBody sC = .ret none sC :=
    gap_step_cleanup82 (calls := stage2Calls stage2SubCalls) (env := sC.env) (s := sC) rfl
  refine ⟨5, by omega, ?_⟩
  rw [show 5 = 2 + (1 + (1 + 1)) from by omega, hrun (1 + (1 + 1)),
    runFuel_jump_prefix hstep (1 + 1), runFuel_jump_prefix hstep2 1]
  exact gapNum_runFuel_ret_void hret hmC

/-- **The no-write row of `od_gap_recover`.**  When the rule writes nothing — the
first loop reaches `ip` — the body returns `void` with the caller's memory, on
either of its two paths and through either index branch. -/
theorem odGapRecover_run_none {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (hnone : gapRecoverWrite win P.ip pos = GapWrite.none) :
    ∃ B : Nat, B ≤ 4 + (P.ip + 1) * 5 ∧
      runFuel (stage2Calls stage2SubCalls) B odGapRecoverBody
        (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) =
        some (.ret none mem) ∧
      (∃ eff, stage2GapRecoverRule mem c pos = some eff ∧
        (eff = .unchanged → mem = mem) ∧
        (∀ (e off tag : Nat), eff = .wrote e off tag →
          readBytes mem e 4 = some (wordBytes 4 0) ∧
          readBytes mem (e + 8) 8 = some (wordBytes 8 off) ∧
          readBytes mem (e + 16) 8 = some (wordBytes 8 tag) ∧
          UnchangedOutside mem mem
            [(e, 4), (e + 8, 8), (e + 16, 8),
             (next, (Ty.double).sizeBytes),
             (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)])) := by
  have hEe : gapEe win P.ip pos = P.ip := gapRecoverWrite_none_iff.mp hnone
  have hrule : stage2GapRecoverRule mem c pos = some .unchanged := by
    rw [stage2GapRecoverRule_of_prep P, hnone]; rfl
  have hclause : ∃ eff, stage2GapRecoverRule mem c pos = some eff ∧
      (eff = .unchanged → mem = mem) ∧
      (∀ (e off tag : Nat), eff = .wrote e off tag →
        readBytes mem e 4 = some (wordBytes 4 0) ∧
        readBytes mem (e + 8) 8 = some (wordBytes 8 off) ∧
        readBytes mem (e + 16) 8 = some (wordBytes 8 tag) ∧
        UnchangedOutside mem mem
          [(e, 4), (e + 8, 8), (e + 16, 8),
           (next, (Ty.double).sizeBytes),
           (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)]) := by
    refine ⟨.unchanged, hrule, fun _ => rfl, ?_⟩
    intro e off tag hbad
    cases hbad
  by_cases hpos : pos = P.ip
  · by_cases hklt : P.k < P.nix
    · obtain ⟨B, hB, hrun⟩ := gapRun_none_atIp_true P hklt hpos
      exact ⟨B, by omega, hrun, hclause⟩
    · obtain ⟨B, hB, hrun⟩ := gapRun_none_atIp_false P hklt hpos
      exact ⟨B, by omega, hrun, hclause⟩
  · have hposlt : pos < P.ip := lt_of_le_of_ne P.hposip hpos
    by_cases hklt : P.k < P.nix
    · obtain ⟨B, hB, hrun⟩ := gapRun_none_scan_true P hklt hposlt hEe
      exact ⟨B, by omega, hrun, hclause⟩
    · obtain ⟨B, hB, hrun⟩ := gapRun_none_scan_false P hklt hposlt hEe
      exact ⟨B, by omega, hrun, hclause⟩

/-! ### Axiom footprints -/

#print axioms odGapRecover_run_none
#print axioms gapRun_none_scan_true
#print axioms gapRun_none_atIp_true
#print axioms gapPrefix_true
#print axioms gapPrefix_false
#print axioms gapScan_to_cleanup_none
#print axioms stage2GapRecoverRule_of_prep
#print axioms readBytes_of_gapBytesAt
#print axioms gapRecoverWrite_none_iff
#print axioms gapLitLoop_run
#print axioms gapLit_exitRun
#print axioms gapLitInv_seed
/-! ### `if.end`'s other edge, and the first-byte classes

The number test's false arm leaves `if.end` for `if.else` with the same six cells;
the byte it loaded decides which of the four arms the dispatch selects.  The
bridges below turn the body's `icmp`/`add` test at `%7` into the model's
`gapNumStart`, and the window's segment into the range `num_fast_el1` reads. -/

/-- `if.end` on the number test's false arm: the byte at `%arrayidx9`, the minus
test, the digit test and their `or`, with the branch into `if.else`. -/
theorem gapNum_step_ifEnd_nonNum {calls : Calls} {env : Env} {s : State}
    {base se : Nat} {t : BitVec 64} {v7 : BitVec 8}
    (hpc : s.pc = "if.end")
    (h0 : lookupName env "%0" = some (.ptr base))
    (ht : lookupName env "%t.0.val" = some (.int 64 t))
    (hse : (t.signExtend 64).toNat = se) (hse63 : se < 2 ^ 63)
    (hbyte : readBytes s.mem (base + se) 1 = some (natToBytes v7.toNat 1))
    (hbit : (evalICmp .eq v7 (BitVec.ofNat 8 45) |||
      evalICmp .ult (v7 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapNumIfEndEnv env base se v7)
        { s with pc := "if.else", pre := some "if.end" }) := by
  let env' : Env := gapNumIfEndEnv env base se v7
  have hcode : denoteCode calls odGapRecoverIfEndInstrs (stateAt env s) =
      some (stateAt env' s) := by
    unfold odGapRecoverIfEndInstrs
    refine Eq.trans (denoteCode_gep8_reg calls env s "%arrayidx9" "%0" "%t.0.val"
      h0 ht (by rw [hse]; exact hse63) _) ?_
    rw [hse]
    refine Eq.trans (gap_denote_load8 calls
      (("%arrayidx9", .ptr (base + se)) :: env) s "%7" "%arrayidx9"
      (by block_lk) hbyte _) ?_
    refine Eq.trans (gap_denote_icmp_eq_imm calls
      (("%7", .int 8 v7) :: ("%arrayidx9", .ptr (base + se)) :: env) s
      "%cmp11" "%7" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_add_imm calls
      (("%cmp11", .int 1 (evalICmp .eq v7 (BitVec.ofNat 8 45))) ::
        ("%7", .int 8 v7) :: ("%arrayidx9", .ptr (base + se)) :: env) s
      "%8" "%7" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_icmp_ult_imm calls
      (("%8", .int 8 (v7 + BitVec.ofNat 8 208)) ::
        ("%cmp11", .int 1 (evalICmp .eq v7 (BitVec.ofNat 8 45))) ::
        ("%7", .int 8 v7) :: ("%arrayidx9", .ptr (base + se)) :: env) s
      "%or.cond" "%8" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_or_reg calls
      (("%or.cond", .int 1 (evalICmp .ult (v7 + BitVec.ofNat 8 208)
          (BitVec.ofNat 8 10))) ::
        ("%8", .int 8 (v7 + BitVec.ofNat 8 208)) ::
        ("%cmp11", .int 1 (evalICmp .eq v7 (BitVec.ofNat 8 45))) ::
        ("%7", .int 8 v7) :: ("%arrayidx9", .ptr (base + se)) :: env) s
      "%or.cond127" "%cmp11" "%or.cond" (by block_lk) (by block_lk) []) ?_
    rfl
  refine gapNum_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env' s) (name := "if.end") (is := odGapRecoverIfEndInstrs)
    (term := Term.condbr (Operand.reg "%or.cond127") "if.then19" "if.else")
    (c := .jump (stateAt env' (gapNumJump s "if.else" "if.end" s.mem s.next)))
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_end
  · exact hcode
  · rw [gap_execTerm_condbr_zero
      (by simp only [env', gapNumIfEndEnv, cells, stateAt, evalOperand, hbit]
          rw [lookupName_cons_self]
          rfl)]
    simp only [stateAt, hpc, gapNumJump]

/-- An equality at one is the words being equal. -/
theorem gapICmpEq_one_iff {w : Nat} {x y : BitVec w} :
    evalICmp .eq x y = 1#1 ↔ x = y := by
  unfold evalICmp
  by_cases h : x = y <;> simp [h]

/-- `BitVec.ofBool` is `1` exactly at a true bit. -/
theorem odGap_ofBool_one_iff {b : Bool} :
    BitVec.ofBool b = 1#1 ↔ b = true := by
  cases b <;> decide

/-- `icmp eq` is one exactly at equal words. -/
theorem odGap_evalICmp_eq_one_iff {w : Nat} {x y : BitVec w} :
    evalICmp .eq x y = 1#1 ↔ x = y := by
  unfold evalICmp
  rw [odGap_ofBool_one_iff, decide_eq_true_iff]

/-- `icmp ult` is one exactly at the unsigned order on `Nat` readings. -/
theorem odGap_evalICmp_ult_one_iff {w : Nat} {x y : BitVec w} :
    evalICmp .ult x y = 1#1 ↔ x.toNat < y.toNat := by
  unfold evalICmp
  rw [odGap_ofBool_one_iff, BitVec.ult_iff_toNat_lt]

/-- Two small `Nat`s are equal exactly when their eight-bit words are. -/
theorem odGap_ofNat8_eq_iff {a b : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    BitVec.ofNat 8 a = BitVec.ofNat 8 b ↔ a = b := by
  rw [BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- The byte plus `208` reads as its distance from `'0'`, modulo the byte. -/
theorem odGap_byte_add_toNat (ch : UInt8) :
    (gapByte ch + BitVec.ofNat 8 208).toNat = (ch.toNat + 208) % 2 ^ 8 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  unfold gapByte
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ch.toNat_lt,
    Nat.mod_eq_of_lt (by decide : 208 < 2 ^ 8)]

/-- **The number test, at the byte.**  The body's `'-'`/digit test holds exactly
at the model's list-level condition. -/
theorem odGapNumberByte_iff (ch : UInt8) :
    gapNumberByte (gapByte ch) ↔
      ch.toNat = 45 ∨ (48 ≤ ch.toNat ∧ ch.toNat ≤ 57) := by
  unfold gapNumberByte
  have hlt : ch.toNat < 2 ^ 8 := ch.toNat_lt
  constructor
  · intro h
    rcases h with h | h
    · left
      have heq := odGap_evalICmp_eq_one_iff.1 h
      simpa only [gapByte] using
        (odGap_ofNat8_eq_iff (a := ch.toNat) (b := 45) (by omega) (by decide)).1 heq
    · right
      have hu' : (ch.toNat + 208) % 2 ^ 8 < 10 := by
        have hu := odGap_evalICmp_ult_one_iff.1 h
        rw [odGap_byte_add_toNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by decide : 10 < 2 ^ 8)] at hu
        exact hu
      by_cases hc : ch.toNat < 48
      · exfalso
        rw [Nat.mod_eq_of_lt (by omega)] at hu'
        omega
      · constructor <;> omega
  · intro h
    rcases h with h | ⟨h1, h2⟩
    · left
      refine odGap_evalICmp_eq_one_iff.2 ?_
      simpa only [gapByte] using
        (odGap_ofNat8_eq_iff (a := ch.toNat) (b := 45) (by omega) (by decide)).2 (by omega)
    · right
      rw [odGap_evalICmp_ult_one_iff, odGap_byte_add_toNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by decide : 10 < 2 ^ 8)]
      have hsum : ch.toNat + 208 = (ch.toNat - 48) + 2 ^ 8 := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega

/-- The model's list-level number condition is the same byte condition. -/
theorem odGapNumberCondition_iff (ch : UInt8) :
    (ch = 0x2D ∨ (0x30 ≤ ch ∧ ch ≤ 0x39)) ↔
      ch.toNat = 45 ∨ (48 ≤ ch.toNat ∧ ch.toNat ≤ 57) := by
  have h2d : (0x2D : UInt8).toNat = 45 := by decide
  have h30 : (0x30 : UInt8).toNat = 48 := by decide
  have h39 : (0x39 : UInt8).toNat = 57 := by decide
  have h1 : (ch = 0x2D) ↔ ch.toNat = 45 := by
    rw [← UInt8.toNat_inj, h2d]
  have h2 : (0x30 ≤ ch) ↔ 48 ≤ ch.toNat := by
    rw [UInt8.le_iff_toNat_le, h30]
  have h3 : (ch ≤ 0x39) ↔ ch.toNat ≤ 57 := by
    rw [UInt8.le_iff_toNat_le, h39]
  rw [h1, h2, h3]

/-- The body's number test and the model's list-level condition agree. -/
theorem odGapNumberByte_iff' (ch : UInt8) :
    gapNumberByte (gapByte ch) ↔ (ch = 0x2D ∨ (0x30 ≤ ch ∧ ch ≤ 0x39)) :=
  (odGapNumberByte_iff ch).trans (odGapNumberCondition_iff ch).symm

/-- The window's segment as the range `num_fast_el1` and `lit_check` read. -/
theorem readBytes_gapSegment {mem : Mem} {win : List UInt8} {b ip pos ee : Nat}
    (hbytes : gapBytesAt mem win b ip) (hlen : win.length = ip)
    (hpos : pos ≤ ee) (hee : ee ≤ ip) :
    readBytes mem (b + pos) (ee - pos) = some (gapSegment win pos ee) := by
  have h : readBytes mem b ip = some win := readBytes_of_gapBytesAt hbytes hlen
  have h' : readBytes mem b (pos + (ip - pos)) = some win := by
    rw [show pos + (ip - pos) = ip from by omega]; exact h
  obtain ⟨_, hsuf⟩ := readBytes_split mem b pos (ip - pos) h'
  have h'' : readBytes mem (b + pos) ((ee - pos) + (ip - ee)) = some (win.drop pos) := by
    rw [show (ee - pos) + (ip - ee) = ip - pos from by omega]; exact hsuf
  obtain ⟨hpre, _⟩ := readBytes_split mem (b + pos) (ee - pos) (ip - ee) h''
  simpa only [gapSegment] using hpre

/-- The token's window length, as the word the call passes: the body subtracts
`%t.0.val` from `%ee.0.lcssa` in 64-bit arithmetic, and the `Nat` difference is
the same below `2 ^ 64`. -/
theorem gapSub_toNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat = a - b := by
  have hx : (BitVec.ofNat 64 a).toNat = a := gap_word64 ha
  have hy : (BitVec.ofNat 64 b).toNat = b := gap_word64 hb
  have h := BitVec.toNat_sub (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)
  rw [hx, hy] at h
  rw [h, show 2 ^ 64 - b + a = (a - b) + 2 ^ 64 from by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ### Axiom footprints -/

#print axioms gapNum_step_ifEnd_nonNum
#print axioms odGapNumberByte_iff'
#print axioms odGapNumberCondition_iff
#print axioms odGap_byte_add_toNat
#print axioms readBytes_gapSegment
#print axioms gapSub_toNat
#print axioms gapICmpEq_one_iff

end LeanLLVM.Refinement
namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)
open LeanLLVM.Refinement.BlockEval (stateAt cells denoteCode_gep8_reg)
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_writeBytes_frame readBytes_length)

/-! ### The window as a range, and its token segment -/

/-- The byte-at-a-time window reads back as one range. -/
theorem odGapBytesAt_readBytes {mem : Mem} {bytes : List UInt8} {b ip : Nat}
    (h : gapBytesAt mem bytes b ip) (hlen : bytes.length = ip) :
    readBytes mem b ip = some bytes := by
  induction ip generalizing bytes b with
  | zero =>
      cases bytes with
      | nil => rfl
      | cons y ys => simp at hlen
  | succ n ih =>
      cases bytes with
      | nil => simp at hlen
      | cons x xs =>
          have hlen' : xs.length = n := by simp at hlen; omega
          have hx : readByte mem b = some x := by
            have := h 0 (by omega)
            simpa using this
          have hxs : gapBytesAt mem xs (b + 1) n := by
            intro i hi
            have := h (i + 1) (by omega)
            rw [show b + (i + 1) = (b + 1) + i from by omega, List.getD_cons_succ] at this
            exact this
          have hrec := ih hxs hlen'
          simp only [readBytes, hx, hrec]

/-- The token's window `[pos, ee)` as one range read of the document. -/
theorem odGapSegment_readBytes {mem : Mem} {bytes : List UInt8} {b pos ee ip : Nat}
    (h : readBytes mem b ip = some bytes) (hpe : pos ≤ ee) (hee : ee ≤ ip) :
    readBytes mem (b + pos) (ee - pos) = some (gapSegment bytes pos ee) := by
  have hle : pos ≤ ip := le_trans hpe hee
  have h' : readBytes mem b (pos + (ip - pos)) = some bytes := by
    rw [Nat.add_sub_cancel' hle]; exact h
  obtain ⟨-, htail⟩ := readBytes_split mem b pos (ip - pos) h'
  have h'' : readBytes mem (b + pos) ((ee - pos) + (ip - ee)) = some (bytes.drop pos) := by
    rw [show (ee - pos) + (ip - ee) = ip - pos from by omega]; exact htail
  exact (readBytes_split mem (b + pos) (ee - pos) (ip - ee) h'').1

/-- A list's byte inside its first `k`. -/
theorem odGap_getD_take {l : List UInt8} {k j : Nat} (hj : j < k) :
    (l.take k).getD j 0 = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
    if_pos hj]

/-- The first `k` of two lists agree when their bytes do. -/
theorem odGap_take_eq {a b : List UInt8} {k : Nat}
    (hka : k ≤ a.length) (hkb : k ≤ b.length)
    (hpre : ∀ j, j < k → a.getD j 0 = b.getD j 0) :
    a.take k = b.take k := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < k
  · have hja : j < a.length := lt_of_lt_of_le hj hka
    have hjb : j < b.length := lt_of_lt_of_le hj hkb
    rw [List.getElem?_take, List.getElem?_take, if_pos hj, if_pos hj,
      List.getElem?_eq_getElem hja, List.getElem?_eq_getElem hjb]
    congr 1
    have hg := hpre j hj
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hja, List.getElem?_eq_getElem hjb,
      Option.getD_some, Option.getD_some] at hg
  · rw [List.getElem?_take, List.getElem?_take, if_neg hj, if_neg hj]

/-- The token segment's byte at an offset is the document's at `pos + j`. -/
theorem odGapSegment_getD {bytes : List UInt8} {pos ee j : Nat} (hj : j < ee - pos) :
    (gapSegment bytes pos ee).getD j 0 = bytes.getD (pos + j) 0 := by
  unfold gapSegment
  rw [odGap_getD_take (by omega), gap_getD_drop_add]

/-- The token segment's length, inside the window. -/
theorem odGapSegment_length {bytes : List UInt8} {pos ee : Nat}
    (hpe : pos ≤ ee) (hee : ee ≤ bytes.length) :
    (gapSegment bytes pos ee).length = ee - pos := by
  unfold gapSegment
  rw [List.length_take, List.length_drop]
  omega

/-! ### `lit_check` as a scan

`litCheck` is the first differing position, or the shorter length where one list
is a strict prefix.  `odGapLitScan` is the same function with the position as an
accumulator, which is what the composition's prefix facts consume. -/

/-- `litCheck` with the position carried. -/
def odGapLitScan : List UInt8 → List UInt8 → Nat → Option Nat
  | [], [], _ => none
  | [], _ :: _, k => some k
  | _ :: _, [], k => some k
  | a :: as, b :: bs, k => if a = b then odGapLitScan as bs (k + 1) else some k

/-- The accumulator form is `litCheck` plus the offset. -/
theorem odGapLitScan_map_add (a b : List UInt8) (k : Nat) :
    (litCheck a b).map (· + k) = odGapLitScan a b k := by
  induction a generalizing b k with
  | nil =>
      cases b with
      | nil => rfl
      | cons y ys => simp [litCheck, odGapLitScan]
  | cons x xs ih =>
      cases b with
      | nil => simp [litCheck, odGapLitScan]
      | cons y ys =>
          simp only [litCheck, odGapLitScan]
          by_cases h : x = y
          · rw [if_pos h, if_pos h, ← ih ys (k + 1)]
            cases hlit : litCheck xs ys with
            | none => rfl
            | some v => simp only [Option.map]; congr 1; omega
          · rw [if_neg h, if_neg h]
            simp only [Option.map]
            congr 1
            omega

/-- **`litCheck` is the scan at zero.** -/
theorem odGapLitCheck_eq_scan (a b : List UInt8) :
    litCheck a b = odGapLitScan a b 0 := by
  have h := odGapLitScan_map_add a b 0
  simpa using h

/-- The scan at an accumulator carries a matching prefix. -/
theorem odGapLitScan_drop_add {a b : List UInt8} {k n : Nat}
    (hka : k ≤ a.length) (hkb : k ≤ b.length)
    (hpre : ∀ j, j < k → a.getD j 0 = b.getD j 0) :
    odGapLitScan a b n = odGapLitScan (a.drop k) (b.drop k) (n + k) := by
  induction k generalizing a b n with
  | zero => simp
  | succ k ih =>
      cases a with
      | nil => simp at hka
      | cons x as =>
          cases b with
          | nil => simp at hkb
          | cons y ys =>
              have hxy : x = y := by
                have := hpre 0 (by omega); simpa using this
              subst hxy
              simp only [odGapLitScan, if_pos rfl, List.drop_succ_cons]
              rw [ih (a := as) (b := ys) (n := n + 1) (by simpa using hka)
                (by simpa using hkb)
                (fun j hj => by have := hpre (j + 1) (by omega); simpa using this)]
              rw [show n + 1 + k = n + (k + 1) from by omega]
              simp

/-- A first difference after a shared prefix, at the prefix's length. -/
theorem odGapLitScan_firstDiff (pre as bs : List UInt8) (x y : UInt8) (n : Nat)
    (h : x ≠ y) :
    odGapLitScan (pre ++ x :: as) (pre ++ y :: bs) n = some (n + pre.length) := by
  induction pre generalizing n with
  | nil =>
      simp only [List.nil_append, odGapLitScan, if_neg h, List.length_nil, Nat.add_zero]
  | cons p ps ih =>
      simp only [List.cons_append, odGapLitScan, if_pos rfl]
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (n + 1)

/-- The first list is a strict prefix of the second. -/
theorem odGapLitScan_short (pre rest : List UInt8) (n : Nat) (h : rest ≠ []) :
    odGapLitScan pre (pre ++ rest) n = some (n + pre.length) := by
  induction pre generalizing n with
  | nil =>
      cases rest with
      | nil => exact absurd rfl h
      | cons y ys => simp only [List.nil_append, odGapLitScan, List.length_nil, Nat.add_zero]
  | cons p ps ih =>
      simp only [List.cons_append, odGapLitScan, if_pos rfl]
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (n + 1)

/-- The second list is a strict prefix of the first. -/
theorem odGapLitScan_long (pre rest : List UInt8) (n : Nat) (h : rest ≠ []) :
    odGapLitScan (pre ++ rest) pre n = some (n + pre.length) := by
  induction pre generalizing n with
  | nil =>
      cases rest with
      | nil => exact absurd rfl h
      | cons y ys => simp only [List.nil_append, odGapLitScan, List.length_nil, Nat.add_zero]
  | cons p ps ih =>
      simp only [List.cons_append, odGapLitScan, if_pos rfl]
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (n + 1)

/-- Equal lists have no refusal position. -/
theorem odGapLitCheck_eq_none {a b : List UInt8} (h : a = b) : litCheck a b = none := by
  subst h
  induction a with
  | nil => rfl
  | cons x xs ih => simp [litCheck, ih]

/-- **The refusal at a first difference.** -/
theorem odGapLitCheck_of_firstDiff {a b : List UInt8} {c : Nat}
    (hca : c < a.length) (hcb : c < b.length)
    (hpre : ∀ j, j < c → a.getD j 0 = b.getD j 0)
    (hne : a.getD c 0 ≠ b.getD c 0) :
    litCheck a b = some c := by
  have hda := List.drop_eq_getElem_cons (l := a) hca
  have hdb := List.drop_eq_getElem_cons (l := b) hcb
  have hta := List.take_append_drop c a
  have htb := List.take_append_drop c b
  have htake : a.take c = b.take c :=
    odGap_take_eq (Nat.le_of_lt hca) (Nat.le_of_lt hcb) hpre
  have hne' : a[c] ≠ b[c] := by
    intro h
    apply hne
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hca, List.getElem?_eq_getElem hcb, Option.getD_some]
    exact h
  have e1 : a = a.take c ++ a[c] :: a.drop (c + 1) := by
    conv => lhs; rw [← hta, hda]
  have e2 : b = b.take c ++ b[c] :: b.drop (c + 1) := by
    conv => lhs; rw [← htb, hdb]
  rw [odGapLitCheck_eq_scan, e1, e2, htake, odGapLitScan_firstDiff _ _ _ _ _ 0 hne']
  congr 1
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hcb)]
  omega

/-- **The refusal where the first list is a strict prefix.** -/
theorem odGapLitCheck_of_short {a b : List UInt8}
    (hlen : a.length < b.length)
    (hpre : ∀ j, j < a.length → a.getD j 0 = b.getD j 0) :
    litCheck a b = some a.length := by
  have htake : a.take a.length = b.take a.length :=
    odGap_take_eq (le_rfl) (Nat.le_of_lt hlen) hpre
  have hb : b = a ++ b.drop a.length := by
    conv => lhs; rw [← List.take_append_drop a.length b, ← htake, List.take_length]
  have hrest : b.drop a.length ≠ [] := by
    intro h
    have := List.length_drop (l := b) (i := a.length)
    rw [h] at this
    simp at this
    omega
  rw [odGapLitCheck_eq_scan, hb]
  simpa using odGapLitScan_short _ _ 0 hrest

/-- **The refusal where the second list is a strict prefix.** -/
theorem odGapLitCheck_of_long {a b : List UInt8}
    (hlen : b.length < a.length)
    (hpre : ∀ j, j < b.length → a.getD j 0 = b.getD j 0) :
    litCheck a b = some b.length := by
  have htake : a.take b.length = b.take b.length :=
    odGap_take_eq (Nat.le_of_lt hlen) le_rfl hpre
  have ha : a = b ++ a.drop b.length := by
    conv => lhs; rw [← List.take_append_drop b.length a, htake, List.take_length]
  have hrest : a.drop b.length ≠ [] := by
    intro h
    have := List.length_drop (l := a) (i := b.length)
    rw [h] at this
    simp at this
    omega
  rw [odGapLitCheck_eq_scan, ha]
  simpa using odGapLitScan_long _ _ 0 hrest

/-- The empty segment against a nonempty literal refuses at `0`. -/
theorem odGapLitCheck_nil_left {lit : List UInt8} (h : lit ≠ []) :
    litCheck [] lit = some 0 := by
  cases lit with
  | nil => exact absurd rfl h
  | cons y ys => rfl

/-- The number arm's refusal write: the tag-1 record at `pos + ei`. -/
theorem odGapAfterLoop_number {bytes : List UInt8} {ip pos ee : Nat}
    (hch : bytes.getD pos 0 = 0x2D ∨
      (0x30 ≤ bytes.getD pos 0 ∧ bytes.getD pos 0 ≤ 0x39))
    (hacc : (numLexScan (gapSegment bytes pos ee)).2 = false) :
    gapAfterLoop bytes ip pos ee =
      GapWrite.err (pos + (numLexScan (gapSegment bytes pos ee)).1) gapTagNumber := by
  unfold gapAfterLoop
  simp only [hch, if_pos, hacc, Bool.false_eq_true, if_false]

/-- The number arm's acceptance falls through to the second token's write. -/
theorem odGapAfterLoop_number_accept {bytes : List UInt8} {ip pos ee : Nat}
    (hch : bytes.getD pos 0 = 0x2D ∨
      (0x30 ≤ bytes.getD pos 0 ∧ bytes.getD pos 0 ≤ 0x39))
    (hacc : (numLexScan (gapSegment bytes pos ee)).2 = true) :
    gapAfterLoop bytes ip pos ee = gapExtraWrite bytes ip ee := by
  unfold gapAfterLoop
  simp only [hch, if_pos, hacc, if_true]

/-- The literal arm's refusal: the tag-2 record at `pos + i`. -/
theorem odGapAfterLoop_literal {bytes lit : List UInt8} {ip pos ee i : Nat} {ch : UInt8}
    (hch : bytes.getD pos 0 = ch)
    (hnotnum : ¬ (ch = 0x2D ∨ (0x30 ≤ ch ∧ ch ≤ 0x39)))
    (hsel : ch = 0x74 ∨ ch = 0x66 ∨ ch = 0x6E)
    (hlitT : ch = 0x74 → lit = gapTrueLit)
    (hlitF : ch = 0x66 → lit = gapFalseLit)
    (hlitN : ch = 0x6E → lit = gapNullLit)
    (hlit : litCheck (gapSegment bytes pos ee) lit = some i) :
    gapAfterLoop bytes ip pos ee = GapWrite.err (pos + i) gapTagLiteral := by
  unfold gapAfterLoop
  simp only [hch, hnotnum, if_false]
  rcases hsel with h | h | h
  · subst h
    have hlit' : litCheck (gapSegment bytes pos ee) gapTrueLit = some i := by
      rw [← hlitT rfl]; exact hlit
    rw [if_pos rfl]
    simp only [gapLiteralWrite, hlit']
  · subst h
    have hlit' : litCheck (gapSegment bytes pos ee) gapFalseLit = some i := by
      rw [← hlitF rfl]; exact hlit
    rw [if_neg (by decide : ¬ (0x66 : UInt8) = 0x74), if_pos rfl]
    simp only [gapLiteralWrite, hlit']
  · subst h
    have hlit' : litCheck (gapSegment bytes pos ee) gapNullLit = some i := by
      rw [← hlitN rfl]; exact hlit
    rw [if_neg (by decide : ¬ (0x6E : UInt8) = 0x74),
      if_neg (by decide : ¬ (0x6E : UInt8) = 0x66), if_pos rfl]
    simp only [gapLiteralWrite, hlit']

/-- The literal arm's acceptance falls through to the second token's write. -/
theorem odGapAfterLoop_literal_accept {bytes lit : List UInt8} {ip pos ee : Nat} {ch : UInt8}
    (hch : bytes.getD pos 0 = ch)
    (hnotnum : ¬ (ch = 0x2D ∨ (0x30 ≤ ch ∧ ch ≤ 0x39)))
    (hsel : ch = 0x74 ∨ ch = 0x66 ∨ ch = 0x6E)
    (hlitT : ch = 0x74 → lit = gapTrueLit)
    (hlitF : ch = 0x66 → lit = gapFalseLit)
    (hlitN : ch = 0x6E → lit = gapNullLit)
    (hlit : litCheck (gapSegment bytes pos ee) lit = none) :
    gapAfterLoop bytes ip pos ee = gapExtraWrite bytes ip ee := by
  unfold gapAfterLoop
  simp only [hch, hnotnum, if_false]
  rcases hsel with h | h | h
  · subst h
    have hlit' : litCheck (gapSegment bytes pos ee) gapTrueLit = none := by
      rw [← hlitT rfl]; exact hlit
    rw [if_pos rfl]
    simp only [gapLiteralWrite, hlit', if_true]
  · subst h
    have hlit' : litCheck (gapSegment bytes pos ee) gapFalseLit = none := by
      rw [← hlitF rfl]; exact hlit
    rw [if_neg (by decide : ¬ (0x66 : UInt8) = 0x74), if_pos rfl]
    simp only [gapLiteralWrite, hlit', if_true]
  · subst h
    have hlit' : litCheck (gapSegment bytes pos ee) gapNullLit = none := by
      rw [← hlitN rfl]; exact hlit
    rw [if_neg (by decide : ¬ (0x6E : UInt8) = 0x74),
      if_neg (by decide : ¬ (0x6E : UInt8) = 0x66), if_pos rfl]
    simp only [gapLiteralWrite, hlit', if_true]

/-- The non-scalar first byte: the tag-3 record at `pos`. -/
theorem odGapAfterLoop_scalar {bytes : List UInt8} {ip pos ee : Nat} {ch : UInt8}
    (hch : bytes.getD pos 0 = ch)
    (hnotnum : ¬ (ch = 0x2D ∨ (0x30 ≤ ch ∧ ch ≤ 0x39)))
    (h74 : ch ≠ 0x74) (h66 : ch ≠ 0x66) (h6E : ch ≠ 0x6E) :
    gapAfterLoop bytes ip pos ee = GapWrite.err pos gapTagScalar := by
  unfold gapAfterLoop
  simp only [hch, hnotnum, if_false, h74, h66, h6E, if_neg]



/-! ### The record's words and the frame

`err_set` writes the record's three words; a caller observes them read back, and
every address outside the record and the two staging slots keeps its byte. -/

theorem odGapSizeBytes_double : (Ty.double).sizeBytes = 8 := rfl
theorem odGapSizeBytes_i64 : (Ty.int 64).sizeBytes = 8 := rfl

/-- `err_set`'s three stores do not touch an address outside `[e, e + 24)`. -/
theorem odGap_readByte_errSetMsg {m : Mem} {e off tag a : Nat}
    (h1 : a < e ∨ e + 4 ≤ a) (h2 : a < e + 8 ∨ e + 16 ≤ a)
    (h3 : a < e + 16 ∨ e + 24 ≤ a) :
    readByte (stage2ErrSetMsg m e off tag) a = readByte m a := by
  unfold stage2ErrSetMsg stage2ErrSet
  rw [readByte_writeBytes_outside (m := writeBytes (writeBytes m e (wordBytes 4 0)) (e + 8)
        (wordBytes 8 off)) (bs := wordBytes 8 tag) (start := e + 16)
        (by simp only [wordBytes, natToBytes_length]; omega),
      readByte_writeBytes_outside (m := writeBytes m e (wordBytes 4 0))
        (bs := wordBytes 8 off) (start := e + 8)
        (by simp only [wordBytes, natToBytes_length]; omega),
      readByte_writeBytes_outside (m := m) (bs := wordBytes 4 0) (start := e)
        (by simp only [wordBytes, natToBytes_length]; omega)]

/-- The record's own regions, in the list the frame names. -/
theorem odGap_frame_outside {e next a : Nat}
    (hout : ∀ r ∈ [(e, 4), (e + 8, 8), (e + 16, 8), (next, 8), (next + 8, 8)],
      ¬ (r.1 ≤ a ∧ a < r.1 + r.2)) :
    (a < e ∨ e + 4 ≤ a) ∧ (a < e + 8 ∨ e + 16 ≤ a) ∧ (a < e + 16 ∨ e + 24 ≤ a) := by
  have h1 := hout (e, 4) (by simp)
  have h2 := hout (e + 8, 8) (by simp)
  have h3 := hout (e + 16, 8) (by simp)
  omega

/-- **The frame at a record written over a memory.**  A byte outside the record
and the two slots reads as it did before the record's stores. -/
theorem odGap_unchangedOutside_errSetMsg {ref m : Mem} {e next off tag : Nat}
    (h : UnchangedOutside ref m
      [(e, 4), (e + 8, 8), (e + 16, 8), (next, 8), (next + 8, 8)]) :
    UnchangedOutside ref (stage2ErrSetMsg m e off tag)
      [(e, 4), (e + 8, 8), (e + 16, 8), (next, 8), (next + 8, 8)] := by
  intro a hout
  obtain ⟨h1, h2, h3⟩ := odGap_frame_outside hout
  rw [odGap_readByte_errSetMsg (m := m) (off := off) (tag := tag) h1 h2 h3]
  exact h a hout

/-- Two half-open slots cover one contiguous interval: an address outside both is
outside the whole `[next, next + 16)`. -/
theorem odGap_not_in_slots {a next : Nat}
    (h1 : ¬ (next ≤ a ∧ a < next + 8))
    (h2 : ¬ (next + 8 ≤ a ∧ a < next + 16)) :
    a < next ∨ next + 16 ≤ a := by
  by_cases ha : a < next
  · exact Or.inl ha
  · right
    by_contra hc
    push_neg at hc
    rcases Nat.lt_or_ge a (next + 8) with h | h
    · exact h1 ⟨by omega, h⟩
    · exact h2 ⟨h, by omega⟩

/-- **The frame at a slot write.**  A write inside the two staging slots is
invisible outside them. -/
theorem odGap_unchangedOutside_slotWrite {mem : Mem} {start : Nat} {bs : List UInt8}
    {next : Nat} (hstart : next ≤ start) (hlen : start + bs.length ≤ next + 16) :
    UnchangedOutside mem (writeBytes mem start bs)
      [(next, (Ty.double).sizeBytes), (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)] := by
  intro a hout
  rw [readByte_writeBytes_outside mem bs (by
    have h1 := hout (next, (Ty.double).sizeBytes) (by simp)
    have h2 := hout (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes) (by simp)
    simp only [odGapSizeBytes_double] at h1 h2 ⊢
    rcases odGap_not_in_slots h1 h2 with h | h
    · left; omega
    · right; omega)]

/-- A plain record write's frame: the literal and scalar rows write only the
record's three words, so every byte outside them is the caller's. -/
theorem odGap_unchangedOutside_record {mem : Mem} {e off tag : Nat} :
    UnchangedOutside mem (stage2ErrSetMsg mem e off tag)
      [(e, 4), (e + 8, 8), (e + 16, 8)] := by
  unfold stage2ErrSetMsg stage2ErrSet
  refine UnchangedOutside.write_le (a := e + 16) (w := 8)
    (UnchangedOutside.write_le (a := e + 8) (w := 8)
      (UnchangedOutside.write_le (a := e) (w := 4) (UnchangedOutside.refl' mem _)
        ⟨(e, 4), by simp, le_rfl, by omega⟩ (by simp [wordBytes, natToBytes_length]))
      ⟨(e + 8, 8), by simp, by omega, by omega⟩ (by simp [wordBytes, natToBytes_length]))
    ⟨(e + 16, 8), by simp, by omega, by omega⟩ (by simp [wordBytes, natToBytes_length])

/-- The block's `BitVec` difference is the `Nat` difference at `ofNat`. -/
theorem gapSub_eq_ofNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [gapSub_toNat hba ha hb, gap_word64 (by omega)]

/-- The compare bound `%cond.i` is the smaller of the two lengths. -/
theorem gapLit_cond_min {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if evalICmp .ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 1 then
        BitVec.ofNat 64 a else BitVec.ofNat 64 b) = BitVec.ofNat 64 (min a b) := by
  by_cases h : a < b
  · have h1 : evalICmp .ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 1#1 :=
      gap_ult_one ha hb h
    rw [h1, if_pos (by decide), Nat.min_eq_left (by omega)]
  · have hz : evalICmp .ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 0#1 := by
      rcases LeanLLVM.Refinement.BlockEval.bitVec1_eq_zero_or_one
        (evalICmp .ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)) with h' | h'
      · exact h'
      · exact absurd (gap_ult_of_one ha hb h') h
    rw [hz, if_neg (by decide), Nat.min_eq_right (by omega)]

/-! ### Axiom footprints -/

#print axioms odGapLitCheck_of_firstDiff
#print axioms odGapNumberByte_iff
#print axioms odGapAfterLoop_number
#print axioms odGap_unchangedOutside_errSetMsg




/-! ### Small arithmetic -/

/-- Two small words add as their naturals. -/
theorem odGap_add_toNat {a b : Nat} (h : a + b < 2 ^ 64) :
    ((BitVec.ofNat 64 a) + (BitVec.ofNat 64 b)).toNat = a + b := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : b < 2 ^ 64), Nat.mod_eq_of_lt h]

/-- The token length the body subtracts is the segment's length. -/
theorem odGap_sub_toNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64) :
    ((BitVec.ofNat 64 a) - (BitVec.ofNat 64 b)).toNat = a - b := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
  have h : 2 ^ 64 - b + a = 2 ^ 64 + (a - b) := by omega
  rw [h, Nat.add_comm (2 ^ 64) (a - b), Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ### The refusal record's memory -/

/-- **The number refusal's record and frame.**  The helper wrote `%ei` at
`next + 8`; the record's three words are the model's and every byte outside the
record and the two slots is the caller's. -/
theorem odGap_memory_numberRefusal {mem : Mem} {next e pos off : Nat} :
    readBytes (stage2ErrSetMsg (writeBytes mem (next + 8) (wordBytes 8 off)) e
        (pos + off) 1) e 4 = some (wordBytes 4 0) ∧
      readBytes (stage2ErrSetMsg (writeBytes mem (next + 8) (wordBytes 8 off)) e
        (pos + off) 1) (e + 8) 8 = some (wordBytes 8 (pos + off)) ∧
      readBytes (stage2ErrSetMsg (writeBytes mem (next + 8) (wordBytes 8 off)) e
        (pos + off) 1) (e + 16) 8 = some (wordBytes 8 1) ∧
      UnchangedOutside mem
        (stage2ErrSetMsg (writeBytes mem (next + 8) (wordBytes 8 off)) e (pos + off) 1)
        [(e, 4), (e + 8, 8), (e + 16, 8), (next, 8), (next + 8, 8)] := by
  refine ⟨stage2ErrSetMsg_ok_read _ _ _ _, stage2ErrSetMsg_off_read _ _ _ _,
    stage2ErrSetMsg_msg_read _ _ _ _, ?_⟩
  refine odGap_unchangedOutside_errSetMsg ?_
  intro a hout
  have h1 := hout (next, 8) (by simp)
  have h2 := hout (next + 8, 8) (by simp)
  have h3 : a < next + 8 ∨ next + 16 ≤ a := by
    rcases odGap_not_in_slots h1 h2 with h | h <;> omega
  rw [readByte_writeBytes_outside mem (wordBytes 8 off) (start := next + 8) (by
    simp only [wordBytes, natToBytes_length]; omega)]

/-- **The accepting rows' record and frame.**  The helper wrote `%d` at `next`;
the record's three words are the model's and every byte outside the record and
the two slots is the caller's. -/
theorem odGap_memory_accept {mem : Mem} {next e off tag : Nat} {val : List UInt8}
    (hval : val.length = 8) :
    readBytes (stage2ErrSetMsg (writeBytes mem next val) e off tag) e 4 =
        some (wordBytes 4 0) ∧
      readBytes (stage2ErrSetMsg (writeBytes mem next val) e off tag) (e + 8) 8 =
        some (wordBytes 8 off) ∧
      readBytes (stage2ErrSetMsg (writeBytes mem next val) e off tag) (e + 16) 8 =
        some (wordBytes 8 tag) ∧
      UnchangedOutside mem (stage2ErrSetMsg (writeBytes mem next val) e off tag)
        [(e, 4), (e + 8, 8), (e + 16, 8), (next, 8), (next + 8, 8)] := by
  refine ⟨stage2ErrSetMsg_ok_read _ _ _ _, stage2ErrSetMsg_off_read _ _ _ _,
    stage2ErrSetMsg_msg_read _ _ _ _, ?_⟩
  refine odGap_unchangedOutside_errSetMsg ?_
  intro a hout
  have h1 := hout (next, 8) (by simp)
  have h2 := hout (next + 8, 8) (by simp)
  have h3 : a < next ∨ next + 16 ≤ a := odGap_not_in_slots h1 h2
  rw [readByte_writeBytes_outside mem val (start := next) (by omega)]


/-- **`num_fast_el1`'s refusing outcome at the emitted argument list.**  A pure
computation: the four-element argument match reduces, the token length is the
segment's, and the scan refuses. -/
theorem odGap_stage2NumFast_refuse {mem : Mem} {b pos ee next : Nat} {seg : List UInt8}
    (hsub : (BitVec.ofNat 64 ee - BitVec.ofNat 64 pos).toNat = ee - pos)
    (hseg : readBytes mem (b + pos) (ee - pos) = some seg)
    (hacc : (numLexScan seg).2 = false) :
    stage2NumFast [.ptr (b + pos), .int 64 (BitVec.ofNat 64 ee - BitVec.ofNat 64 pos),
        .ptr next, .ptr (next + 8)] mem (next + 16) =
      some ⟨.int 32 (BitVec.ofNat 32 0),
        writeBytes mem (next + 8) (wordBytes 8 (numLexScan seg).1), next + 16⟩ := by
  simp only [stage2NumFast, hsub, hseg, hacc, Bool.false_eq_true, if_false]

/-! ### The number refusal at `if.end` -/

/-- **The number refusal row's body.**  At `if.end` with the number test true and
`num_fast_el1` refusing, the body writes the tag-1 record at `pos + ei` and
returns `void`, in four control steps. -/
theorem odGap_numberRefusal_ifEnd {mem : Mem} {c pos b e ip ee next : Nat}
    {bytes : List UInt8} {s : State}
    (hpc : s.pc = "if.end") (hmem : s.mem = mem)
    (h0 : lookupName s.env "%0" = some (.ptr b))
    (ht : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)))
    (hee : lookupName s.env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 ee)))
    (hd : lookupName s.env "%d" = some (.ptr next))
    (hei : lookupName s.env "%ei" = some (.ptr (next + 8)))
    (hc : lookupName s.env "%c" = some (.ptr c))
    (hnext : s.next = next + 16)
    (hbytesAt : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (hposlt : pos < ip) (hposee : pos ≤ ee) (heele : ee ≤ ip)
    (hpos64 : pos < 2 ^ 64) (hip64 : ip < 2 ^ 64) (hip63 : ip < 2 ^ 63)
    (he : readBytes mem (c + 1112) 8 = some (natToBytes e 8)) (he64 : e < 2 ^ 64)
    (hfield : c + odGapCurE + 8 ≤ next ∨ next + 16 ≤ c + odGapCurE)
    (hnum : gapNumberByte (gapByte (bytes.getD pos 0)))
    (hacc : (numLexScan (gapSegment bytes pos ee)).2 = false) :
    runFuel (stage2Calls stage2SubCalls) 4 odGapRecoverBody s =
      some (.ret none (stage2ErrSetMsg
        (writeBytes mem (next + 8) (wordBytes 8 (numLexScan (gapSegment bytes pos ee)).1))
        e (pos + (numLexScan (gapSegment bytes pos ee)).1) 1)) := by
  have hbytes : readBytes mem b ip = some bytes := readBytes_of_gapBytesAt hbytesAt hblen
  have hseg : readBytes mem (b + pos) (ee - pos) = some (gapSegment bytes pos ee) :=
    odGapSegment_readBytes hbytes hposee heele
  have hbyte : readBytes s.mem (b + pos) 1 =
      some (natToBytes (gapByte (bytes.getD pos 0)).toNat 1) := by
    rw [hmem]; exact gap_readOne hbytesAt hposlt rfl
  have hse : ((BitVec.ofNat 64 pos).signExtend 64).toNat = pos :=
    gap_signExtend_ofNat pos hpos64
  have hse63 : pos < 2 ^ 63 := by omega
  have hoffle : (numLexScan (gapSegment bytes pos ee)).1 ≤ ip := by
    have h1 := numLexScan_fst_le (gapSegment bytes pos ee)
    have h2 := odGapSegment_length hposee (by rw [hblen]; exact heele)
    calc (numLexScan (gapSegment bytes pos ee)).1
        ≤ (gapSegment bytes pos ee).length := h1
      _ = ee - pos := h2
      _ ≤ ee := Nat.sub_le _ _
      _ ≤ ip := heele
  have hoff64 : (numLexScan (gapSegment bytes pos ee)).1 < 2 ^ 64 := by omega
  have hsub : (BitVec.ofNat 64 ee - BitVec.ofNat 64 pos).toNat = ee - pos :=
    odGap_sub_toNat hposee (by omega)
  have hcall : stage2Calls stage2SubCalls "num_fast_el1"
      [.ptr (b + pos), .int 64 (BitVec.ofNat 64 ee - BitVec.ofNat 64 pos),
        .ptr next, .ptr (next + 8)] s.mem s.next =
      some ⟨.int 32 (BitVec.ofNat 32 0),
        writeBytes mem (next + 8) (wordBytes 8 (numLexScan (gapSegment bytes pos ee)).1),
        next + 16⟩ := by
    rw [stage2Calls_num_fast_el1, hmem, hnext]
    exact odGap_stage2NumFast_refuse hsub hseg hacc
  have hfield' : c + 1112 + 8 ≤ next ∨ next + 16 ≤ c + 1112 := by
    simpa only [odGapCurE] using hfield
  have hrec : readBytes (writeBytes mem (next + 8) (wordBytes 8 (numLexScan (gapSegment bytes pos ee)).1)) (c + 1112) 8 =
      some (natToBytes e 8) := by
    rw [readBytes_writeBytes_frame _ _ (p := c + 1112) (n := 8) (start := next + 8)
      (by simp only [wordBytes, natToBytes_length]; omega)]
    exact he
  have h10 : readBytes (writeBytes mem (next + 8) (wordBytes 8 (numLexScan (gapSegment bytes pos ee)).1)) (next + 8) 8 =
      some (natToBytes (BitVec.ofNat 64 (numLexScan (gapSegment bytes pos ee)).1).toNat 8) := by
    rw [gap_word64 hoff64]
    have hs := readBytes_writeBytes_same mem (wordBytes 8 (numLexScan (gapSegment bytes pos ee)).1) (addr := next + 8)
    rw [show (wordBytes 8 (numLexScan (gapSegment bytes pos ee)).1).length = 8 from by
      simp only [wordBytes, natToBytes_length]] at hs
    simpa only [wordBytes] using hs
  have hoffpos : (numLexScan (gapSegment bytes pos ee)).1 + pos < 2 ^ 64 := by
    have h := Nat.add_le_add hoffle (le_of_lt hposlt)
    omega
  have hconv : gapNumThen25Mem (writeBytes mem (next + 8) (wordBytes 8 (numLexScan (gapSegment bytes pos ee)).1)) e
      (BitVec.ofNat 64 (numLexScan (gapSegment bytes pos ee)).1) (BitVec.ofNat 64 pos) =
      stage2ErrSetMsg (writeBytes mem (next + 8) (wordBytes 8 (numLexScan (gapSegment bytes pos ee)).1)) e (pos + (numLexScan (gapSegment bytes pos ee)).1) 1 := by
    unfold gapNumThen25Mem stage2ErrSetMsg stage2ErrSet
    simp only [wordBytes]
    rw [odGap_add_toNat hoffpos, Nat.add_comm (numLexScan (gapSegment bytes pos ee)).1 pos]
  have hrun := gap_number_refusal_outcome (nf := stage2SubCalls) (env := s.env) (s := s)
    hpc h0 ht hee hd hei hc hse hse63 hbyte hnum hcall
    (by decide : (BitVec.ofNat 32 0) = 0#32) hrec he64 h10
  simpa only [stateAt, hconv] using hrun

/-- **`num_fast_el1`'s accepting outcome at the emitted argument list.** -/
theorem odGap_stage2NumFast_accept {mem : Mem} {b pos ee next : Nat} {seg : List UInt8}
    (hsub : (BitVec.ofNat 64 ee - BitVec.ofNat 64 pos).toNat = ee - pos)
    (hseg : readBytes mem (b + pos) (ee - pos) = some seg)
    (hacc : (numLexScan seg).2 = true) :
    stage2NumFast [.ptr (b + pos), .int 64 (BitVec.ofNat 64 ee - BitVec.ofNat 64 pos),
        .ptr next, .ptr (next + 8)] mem (next + 16) =
      some ⟨.int 32 (BitVec.ofNat 32 1),
        writeBytes mem next
          (wordBytes 8 (numFastEmitted (JSON.ByteString.literal seg)).toBits), next + 16⟩ := by
  simp only [stage2NumFast, hsub, hseg, hacc, if_true]

/-- **The number acceptance row's body.**  At `if.end` with the number test true
and `num_fast_el1` accepting, the body reaches `if.end67`, runs the second scan,
and returns `void` with the tag-4 record at `gapS2`; the returned memory is the
record plus the helper's `%d` slot. -/
theorem odGap_numberAccept_ifEnd {mem : Mem} {c pos b e ip ee next : Nat}
    {bytes : List UInt8} {s : State}
    (hpc : s.pc = "if.end") (hmem : s.mem = mem)
    (h0 : lookupName s.env "%0" = some (.ptr b))
    (ht : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)))
    (hee : lookupName s.env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 ee)))
    (hd : lookupName s.env "%d" = some (.ptr next))
    (hei : lookupName s.env "%ei" = some (.ptr (next + 8)))
    (hc : lookupName s.env "%c" = some (.ptr c))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hnext : s.next = next + 16)
    (hbytesAt : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (hposlt : pos < ip) (hposee : pos ≤ ee) (heele : ee ≤ ip)
    (hpos64 : pos < 2 ^ 64) (hip64 : ip < 2 ^ 64) (hip63 : ip < 2 ^ 63)
    (he : readBytes mem (c + 1112) 8 = some (natToBytes e 8)) (he64 : e < 2 ^ 64)
    (hfield : c + odGapCurE + 8 ≤ next ∨ next + 16 ≤ c + odGapCurE)
    (hwin : b + ip ≤ next ∨ next + 16 ≤ b)
    (hnum : gapNumberByte (gapByte (bytes.getD pos 0)))
    (hacc : (numLexScan (gapSegment bytes pos ee)).2 = true) :
    ∃ j : Nat, j ≤ 3 + (1 + (ip + 1) * 5 + 2) ∧
      runFuel (stage2Calls stage2SubCalls) j odGapRecoverBody s =
        some (.ret none (stage2ErrSetMsg
          (writeBytes mem next
            (wordBytes 8 (numFastEmitted (JSON.ByteString.literal (gapSegment bytes pos ee))).toBits))
          e (gapS2 bytes ip ee) 4)) ∧
      readBytes (stage2ErrSetMsg
          (writeBytes mem next
            (wordBytes 8 (numFastEmitted (JSON.ByteString.literal (gapSegment bytes pos ee))).toBits))
          e (gapS2 bytes ip ee) 4) e 4 = some (wordBytes 4 0) ∧
      readBytes (stage2ErrSetMsg
          (writeBytes mem next
            (wordBytes 8 (numFastEmitted (JSON.ByteString.literal (gapSegment bytes pos ee))).toBits))
          e (gapS2 bytes ip ee) 4) (e + 8) 8 = some (wordBytes 8 (gapS2 bytes ip ee)) ∧
      readBytes (stage2ErrSetMsg
          (writeBytes mem next
            (wordBytes 8 (numFastEmitted (JSON.ByteString.literal (gapSegment bytes pos ee))).toBits))
          e (gapS2 bytes ip ee) 4) (e + 16) 8 = some (wordBytes 8 4) ∧
      UnchangedOutside mem
        (stage2ErrSetMsg
          (writeBytes mem next
            (wordBytes 8 (numFastEmitted (JSON.ByteString.literal (gapSegment bytes pos ee))).toBits))
          e (gapS2 bytes ip ee) 4)
        [(e, 4), (e + 8, 8), (e + 16, 8), (next, 8), (next + 8, 8)] := by
  have hbytes : readBytes mem b ip = some bytes := readBytes_of_gapBytesAt hbytesAt hblen
  have hseg : readBytes mem (b + pos) (ee - pos) = some (gapSegment bytes pos ee) :=
    odGapSegment_readBytes hbytes hposee heele
  have hbyte : readBytes s.mem (b + pos) 1 =
      some (natToBytes (gapByte (bytes.getD pos 0)).toNat 1) := by
    rw [hmem]; exact gap_readOne hbytesAt hposlt rfl
  have hse : ((BitVec.ofNat 64 pos).signExtend 64).toNat = pos :=
    gap_signExtend_ofNat pos hpos64
  have hse63 : pos < 2 ^ 63 := by omega
  have hsub : (BitVec.ofNat 64 ee - BitVec.ofNat 64 pos).toNat = ee - pos :=
    odGap_sub_toNat hposee (by omega)
  have hval : (wordBytes 8
      (numFastEmitted (JSON.ByteString.literal (gapSegment bytes pos ee))).toBits).length = 8 := by
    simp only [wordBytes, natToBytes_length]
  have hcall : stage2Calls stage2SubCalls "num_fast_el1"
      [.ptr (b + pos), .int 64 (BitVec.ofNat 64 ee - BitVec.ofNat 64 pos),
        .ptr next, .ptr (next + 8)] s.mem s.next =
      some ⟨.int 32 (BitVec.ofNat 32 1),
        writeBytes mem next
          (wordBytes 8 (numFastEmitted (JSON.ByteString.literal (gapSegment bytes pos ee))).toBits),
        next + 16⟩ := by
    rw [stage2Calls_num_fast_el1, hmem, hnext]
    exact odGap_stage2NumFast_accept hsub hseg hacc
  have hfield' : c + 1112 + 8 ≤ next ∨ next + 16 ≤ c + 1112 := by
    simpa only [odGapCurE] using hfield
  let val := wordBytes 8 (numFastEmitted (JSON.ByteString.literal (gapSegment bytes pos ee))).toBits
  let mem' := writeBytes mem next val
  let sA : State := stateAt
    (gapNumberAcceptEnv s.env b pos (gapByte (bytes.getD pos 0))
      (BitVec.ofNat 64 pos) (BitVec.ofNat 64 ee) (BitVec.ofNat 32 1))
    (gapNumberAcceptState s mem' (next + 16))
  have hpcA : sA.pc = "if.end67" := rfl
  have hmemA : sA.mem = mem' := rfl
  have h0A : lookupName sA.env "%0" = some (.ptr b) := by
    simp only [sA, stateAt, gapNumberAcceptEnv, gapNumThen19Env, gapNumIfEndEnv, cells]
    block_lk
  have hcA : lookupName sA.env "%c" = some (.ptr c) := by
    simp only [sA, stateAt, gapNumberAcceptEnv, gapNumThen19Env, gapNumIfEndEnv, cells]
    block_lk
  have heeA : lookupName sA.env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 ee)) := by
    simp only [sA, stateAt, gapNumberAcceptEnv, gapNumThen19Env, gapNumIfEndEnv, cells]
    block_lk
  have hcondA : lookupName sA.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) := by
    simp only [sA, stateAt, gapNumberAcceptEnv, gapNumThen19Env, gapNumIfEndEnv, cells]
    exact hcond
  have heA : readBytes mem' (c + 1112) 8 = some (natToBytes e 8) := by
    rw [show mem' = writeBytes mem next val from rfl,
      readBytes_writeBytes_frame _ _ (p := c + 1112) (n := 8) (start := next)
        (by simp only [val, wordBytes, natToBytes_length]; omega)]
    exact he
  have hbytesA : gapBytesAt mem' bytes b ip := by
    intro i hi
    rw [show mem' = writeBytes mem next val from rfl,
      readByte_writeBytes_outside mem val (start := next) (by
        simp only [val, wordBytes, natToBytes_length]
        rcases hwin with h | h <;> omega)]
    exact hbytesAt i hi
  obtain ⟨j2, hj2, hrun2, _hxw, _hoff, _htag⟩ :=
    gapWs_secondScan_run (mem := mem') (bytes := bytes) (ip := ip) (b := b)
      (ee := ee) (c := c) (e := e) (s := sA) hpcA hmemA h0A hcA heeA hcondA
      heA he64 hbytesA hblen heele hip63
  have hrun1 := gap_number_accept_run (nf := stage2SubCalls) (env := s.env) (s := s)
    hpc h0 ht hee hd hei hse hse63 hbyte hnum hcall
    (by decide : (BitVec.ofNat 32 1) ≠ 0#32) (k := j2)
  have hrun : runFuel (stage2Calls stage2SubCalls) (3 + j2) odGapRecoverBody s =
      some (.ret none (stage2ErrSetMsg mem' e (gapS2 bytes ip ee) 4)) := by
    rw [show runFuel (stage2Calls stage2SubCalls) (3 + j2) odGapRecoverBody s =
      runFuel (stage2Calls stage2SubCalls) j2 odGapRecoverBody sA from by
        simpa only [sA, val, mem', stateAt] using hrun1]
    exact hrun2
  obtain ⟨h1, h2, h3, h4⟩ := odGap_memory_accept (mem := mem) (next := next)
    (e := e) (off := gapS2 bytes ip ee) (tag := 4) (val := val) hval
  exact ⟨3 + j2, by omega, hrun, h1, h2, h3, h4⟩

/-! ### Axiom footprints -/

#print axioms odGap_numberRefusal_ifEnd
#print axioms odGap_numberAccept_ifEnd
#print axioms odGap_memory_numberRefusal
#print axioms odGap_memory_accept
#print axioms odGapSegment_readBytes
#print axioms odGapLitScan_map_add
#print axioms odGap_unchangedOutside_record
#print axioms gapSub_eq_ofNat
#print axioms gapLit_cond_min

end LeanLLVM.Refinement
namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)
open LeanLLVM.Refinement.BlockEval (stateAt cells denoteCode_gep8_reg bitVec1_eq_zero_or_one)
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_writeBytes_frame readBytes_length)

/-- **The scalar refusal row's body.**  At `if.end` with the first byte in no
arm's class, the body leaves for `if.else`, the dispatch refuses at `pos`, and
`cleanup82` returns `void` with the tag-3 record.  Two steps before the dispatch,
at most five through it, and one to return. -/
theorem odGap_scalar_ifEnd {mem : Mem} {c pos b e ip next : Nat}
    {win : List UInt8} {s : State}
    (hpc : s.pc = "if.end") (hmem : s.mem = mem)
    (h0 : lookupName s.env "%0" = some (.ptr b))
    (ht : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)))
    (hc : lookupName s.env "%c" = some (.ptr c))
    (hbytesAt : gapBytesAt mem win b ip) (hblen : win.length = ip)
    (hposlt : pos < ip)
    (hpos64 : pos < 2 ^ 64) (hip63 : ip < 2 ^ 63)
    (he : readBytes mem (c + 1112) 8 = some (natToBytes e 8)) (he64 : e < 2 ^ 64)
    (hch : gapScalarStart (win.getD pos 0)) :
    ∃ j : Nat, j ≤ 8 ∧
      runFuel (stage2Calls stage2SubCalls) j odGapRecoverBody s =
        some (.ret none (stage2ErrSetMsg mem e pos 3)) := by
  have hnotnum : ¬ gapNumberByte (gapByte (win.getD pos 0)) :=
    fun h => hch.1 ((odGapNumberByte_iff' (win.getD pos 0)).mp h)
  have hbit : (evalICmp .eq (gapByte (win.getD pos 0)) (BitVec.ofNat 8 45) |||
      evalICmp .ult (gapByte (win.getD pos 0) + BitVec.ofNat 8 208)
        (BitVec.ofNat 8 10)) = 0#1 := by
    have h1 : evalICmp .eq (gapByte (win.getD pos 0)) (BitVec.ofNat 8 45) = 0#1 := by
      rcases bitVec1_eq_zero_or_one _ with h | h
      · exact h
      · exact absurd (Or.inl h) hnotnum
    have h2 : evalICmp .ult (gapByte (win.getD pos 0) + BitVec.ofNat 8 208)
        (BitVec.ofNat 8 10) = 0#1 := by
      rcases bitVec1_eq_zero_or_one _ with h | h
      · exact h
      · exact absurd (Or.inr h) hnotnum
    rw [h1, h2]
    rfl
  have hbyte : readBytes s.mem (b + pos) 1 =
      some (natToBytes (gapByte (win.getD pos 0)).toNat 1) := by
    rw [hmem]
    exact gap_readOne (h := hbytesAt) (hc := hposlt) (hbyte := rfl)
  have hse : ((BitVec.ofNat 64 pos).signExtend 64).toNat = pos :=
    gap_signExtend_ofNat pos hpos64
  have hse63 : pos < 2 ^ 63 := by omega
  have hstep1 : step (stage2Calls stage2SubCalls) odGapRecoverBody (stateAt s.env s) =
      .jump (stateAt (gapNumIfEndEnv s.env b pos (gapByte (win.getD pos 0)))
        { s with pc := "if.else", pre := some "if.end" }) :=
    gapNum_step_ifEnd_nonNum (calls := stage2Calls stage2SubCalls) (env := s.env)
      (s := s) hpc h0 ht hse hse63 hbyte hbit
  let s1 : State := stateAt (gapNumIfEndEnv s.env b pos (gapByte (win.getD pos 0)))
    { s with pc := "if.else", pre := some "if.end" }
  have h7 : lookupName s1.env "%7" = some (.int 8 (gapByte (win.getD pos 0))) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have hc1 : lookupName s1.env "%c" = some (.ptr c) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have ht1 : lookupName s1.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have hmem1 : s1.mem = mem := by simp only [s1, stateAt]; exact hmem
  have hrec1 : readBytes s1.mem (c + 1112) 8 = some (natToBytes e 8) := by
    rw [hmem1]; exact he
  have hbad102 : gapByte (win.getD pos 0) ≠ BitVec.ofNat 8 102 := by
    intro h
    refine hch.2.2.1 ?_
    rw [← gapLit_gapByte_eq]
    rw [show BitVec.ofNat 8 102 = gapByte (0x66 : UInt8) from by decide] at h
    exact h
  have hbad110 : gapByte (win.getD pos 0) ≠ BitVec.ofNat 8 110 := by
    intro h
    refine hch.2.2.2 ?_
    rw [← gapLit_gapByte_eq]
    rw [show BitVec.ofNat 8 110 = gapByte (0x6E : UInt8) from by decide] at h
    exact h
  have hbad116 : gapByte (win.getD pos 0) ≠ BitVec.ofNat 8 116 := by
    intro h
    refine hch.2.1 ?_
    rw [← gapLit_gapByte_eq]
    rw [show BitVec.ofNat 8 116 = gapByte (0x74 : UInt8) from by decide] at h
    exact h
  obtain ⟨e', j3, hj3, hpc3, hpre3, hmem3, _, _, _, hrun3⟩ :=
    gapLit_dispatch_refuse (calls := stage2Calls stage2SubCalls) (env := s1.env)
      (s := s1) (cur := c) (r := e)
      (t := BitVec.ofNat 64 pos) (x := gapByte (win.getD pos 0))
      rfl h7 hbad102 hbad110 hbad116 hc1 hrec1 he64 ht1
  have hrecEq : writeBytes
      (writeBytes (writeBytes s1.mem e (natToBytes 0 4)) (e + 8)
        (natToBytes (BitVec.ofNat 64 pos).toNat 8))
      (e + 16) (natToBytes 3 8) = stage2ErrSetMsg mem e pos 3 := by
    rw [hmem1]
    simp only [stage2ErrSetMsg, stage2ErrSet, wordBytes,
      gap_word64 hpos64]
  have hret : step (stage2Calls stage2SubCalls) odGapRecoverBody e' = .ret none e' :=
    gap_step_cleanup82 (calls := stage2Calls stage2SubCalls) (env := e'.env) (s := e') hpc3
  have hrunRet : runFuel (stage2Calls stage2SubCalls) 1 odGapRecoverBody e' =
      some (.ret none (stage2ErrSetMsg mem e pos 3)) := by
    refine gapNum_runFuel_ret_void hret ?_
    rw [hmem3, hrecEq]
  refine ⟨1 + (j3 + 1), by omega, ?_⟩
  have hstep1' : step (stage2Calls stage2SubCalls) odGapRecoverBody s = .jump s1 := by
    simpa only [s1, stateAt] using hstep1
  rw [show 1 + (j3 + 1) = 1 + (j3 + 1) from rfl,
    runFuel_jump_prefix hstep1' (j3 + 1)]
  have hrun3' : runFuel (stage2Calls stage2SubCalls) (j3 + 1) odGapRecoverBody s1 =
      runFuel (stage2Calls stage2SubCalls) 1 odGapRecoverBody e' := by
    simpa only [stateAt] using hrun3 1
  rw [hrun3']
  exact hrunRet
/-! ### Axiom footprints -/

#print axioms odGap_scalar_ifEnd

end LeanLLVM.Refinement
