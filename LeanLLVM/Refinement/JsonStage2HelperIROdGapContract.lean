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
  refine ⟨s2, ?_, rfl, rfl, ?_, h02, hc2, ht2, hd2, hei2, hlt2, hlf2, hln2, hconv2⟩
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
  refine ⟨s2, ?_, rfl, rfl, ?_, h02, hc2, ht2, hd2, hei2, hlt2, hlf2, hln2, h52⟩
  · intro k
    rw [hentry, show 2 + k = 1 + (1 + k) from by omega,
      runFuel_jump_prefix h1 (1 + k), runFuel_jump_prefix h2 k]
  · simp only [s2, s1, s0, stateAt]

/-! ### The window's end

From the scan's own seed the first loop runs to its end and `cleanup82` returns
the caller's memory.  The model's rule writes nothing at that exit, which is the
no-write row's second path. -/

theorem gapScan_to_cleanup_none {mem : Mem} {bytes : List UInt8}
    {ip b pos c next lt lf ln : Nat}
    (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (hEe : gapEe bytes ip pos = ip) (hposlt : pos < ip) (hiplt : ip < 2 ^ 63)
    (s : State) (hpc : s.pc = "land.rhs") (hpre : s.pre = some "cond.end")
    (hmem : s.mem = mem) (hb : lookupName s.env "%0" = some (.ptr b))
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
    gapScanInv_seed hposlt hiplt hpc hpre hmem hb hcur ht hcond hd hei hltc hlfc hlnc
  obtain ⟨e, j, hj, _, hexit, hrun⟩ :=
    gapScanLoop_run (calls := stage2Calls stage2SubCalls) (cur := c) (next := next)
      (lt := lt) (lf := lf) (ln := ln) hbytes hblen s pos hinv 1
  have hpcE : e.pc = "cleanup82" := by
    rcases hexit with ⟨leaf, cc, hpc1, _⟩ | ⟨hpc2, _⟩
    · exfalso; omega
    · exact hpc2
  obtain ⟨hret, _⟩ :=
    gap_scan_cleanup82_continue (calls := stage2Calls stage2SubCalls) hpcE hexit
  have hmemE : e.mem = mem := by
    rcases hexit with ⟨leaf, cc, hpc1, hpre1, hm, _⟩ | ⟨_, hm, _⟩
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
  obtain ⟨s, hrun, hpc, hpre, hmem, h0, hcur, ht, hd, hei, hltc, hlfc, hlnc, hconv⟩ :=
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
  obtain ⟨j, hj, hrun2⟩ := gapScan_to_cleanup_none (mem := mem) (bytes := win)
    (ip := P.ip) (b := P.b) (pos := pos) (c := c) (next := next) (lt := lt) (lf := lf)
    (ln := ln) P.hbytes P.hlen hEe hposlt P.hip63 sH rfl rfl hHm hHb hHcur hHt hHc
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
  obtain ⟨s, hrun, hpc, hpre, hmem, h0, hcur, ht, hd, hei, hltc, hlfc, hlnc, h5⟩ :=
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
  obtain ⟨j, hj, hrun2⟩ := gapScan_to_cleanup_none (mem := mem) (bytes := win)
    (ip := P.ip) (b := P.b) (pos := pos) (c := c) (next := next) (lt := lt) (lf := lf)
    (ln := ln) P.hbytes P.hlen hEe hposlt P.hip63 sH rfl rfl hHm hHb hHcur hHt hHc
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
  obtain ⟨s, hrun, hpc, hpre, hmem, h0, hcur, ht, hd, hei, hltc, hlfc, hlnc, hconv⟩ :=
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
  obtain ⟨s, hrun, hpc, hpre, hmem, h0, hcur, ht, hd, hei, hltc, hlfc, hlnc, h5⟩ :=
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
#print axioms readBytes_gapSegment
#print axioms gapSub_toNat
#print axioms gapICmpEq_one_iff

end LeanLLVM.Refinement
