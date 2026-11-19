/-
# The seam's three calls, produced from the seam's staged words

`JsonStage2WalkDispatchSeams`' `HcontSeamCalls` states the seam's three calls as one
group — the value-position call, the scalar call's emit arm and the copy call, each with
its precondition at the staged argument list, its answer and the memory it leaves — and
`HcontSeamAbi` is that group at each of the walk's five seams.  This module produces the
group, so a class that reaches `if.then413.i` hands the seam's *staged words* and nothing
else.

## The chain

At a seam state the three callees' answers are not independent of each other:

* **the answer, from `answers`.**  `s2_value_pos`, `od_scalar_value` and
  `s2_after_value` resolve at their staged argument lists (`s2ValuePosContract.answers`,
  `s2ScalarValueContract.answers`, `s2AfterValueContract.answers`), so each call row's
  `hcall` is one application of the contract at a precondition this module *derives*;
* **the postcondition, from `sound`.**  The value-position answer's returned word and the
  memory and counter it hands back are `s2ValuePos_sound`'s post.  It writes nothing and
  moves no cursor, so the scalar call's row is stated at `r₁.mem`/`r₁.next` = the seam's
  own memory and counter;
* **the frame, from `framed`.**  Each call's answer differs from the memory it was handed
  only inside its `foot`, and every observation the *next* call needs is an atom outside
  that list.  The frames are discharged by `seamFrame_atom` below, the region-list form of
  the atom rule: `readBytes_of_frame_atom` is that statement and lives in
  `PipelineDischarge`, downstream of this module's chain, so the same rule is reached here
  through its upstream congruence form `readBytes_of_frame` (`JsonStage2StringStageFacts`)
  with the atom's own byte list;
* **the next call's precondition at the memory the previous one left.**  The kind store is
  `if.then413.i`'s first instruction, so the scalar call's staging is stated where the call
  is made, and the copy call's byte is the seam's state-stack top carried across both the
  store and the scalar call.

## The region ledger, per call

Each call is listed with the memory it starts in, the regions it may write (`foot`), the
observations the next call needs, and the lemma that keeps each one.

| call | starts in | may write | kept for the next call | by |
|---|---|---|---|---|
| `s2_value_pos` | `seamKindStore Cs s cA` (the seam's kind store: `writeBytes s.mem (tok + 16) (natToBytes cA.toNat 4)`) | nothing (`s2ValuePosFoot = []`) | the memory and counter the next call's row is stated at | the post's `r.mem = mem` and `r.next = next` (`s2ValuePos_sound`); the empty foot is the atom rule's empty instance |
| `od_scalar_value` | `r₁.mem`, that same memory | `s2ScalarValueFoot`: the stream's cursor word `(z + 8, 8)`, the appended record `(G.ev + len, 13)`, the refusal record `(e, 24)` | the **type** stack's top byte at `ctype + (sp − 1)` (`s2AfterValuePre` reads `ct`), inside `%ctype.i`'s staged extent | `seamFrame_atom` at `s2ScalarValue_framed`, with `seamCtypeByte_log_sep`, `seamCtypeByte_ev_sep` and `seamCtypeByte_err_sep` as the three disjointness facts |
| `s2_after_value` | `r₂.mem`, the scalar answer's memory | `(G.next0 + 8, 4)` at depth zero, else `(cst + (sp − 1), 1)` (`s2AfterValueFoot`) | nothing in this group: it is the last call | — |

Across the seam's own kind store, which precedes all three:

| observation | extent | kept by |
|---|---|---|
| the log's base word | `(z, 8)` | `seam_kindStore_keeps_log` |
| the log's capacity word | `(z + 16, 8)` | `seam_kindStore_keeps_log` |
| the type stack's top byte | `ctype + (sp − 1)`, one byte | `seam_kindStore_keeps_stackByte` |
| the state stack's top byte | `cst + (sp − 1)`, one byte | `seam_kindStore_keeps_stackByte` |
| the root slot's word | `(G.next0 + 8, 4)` | `walkReadBytes_rootSlot_of_tokStore` (the store is inside the token record) |

Two entries take the atom rule at a one-byte list rather than at a list read off a
`readBytes`: the staging predicates ask for `readByte`, so the atom is taken at `[b]` and
read back by `readByte_of_atom_one`.  The root slot keeps its own lemma because the store
sits inside the token record and the region-pair ordering is not what places it — the
token extent is.

## The two rows with no producer

Two of the staged rows are *not* consequences of the invariant, and their producers are
named so a class's document row can carry them where it is read:

* **`hpreS`** — the scalar staging's first two words are the cursor record's base and its
  error pointer (`%c.i`'s `%base`/`%e`), which `entry` stores and no block of the walk
  rewrites but `WalkInv` does not carry (`JsonStage2StringStageFacts`' named gaps `hbase`
  and `he`); the token's two words and the delivered window are the entry's own.  Producer:
  the class's document row at the seam's entry.
* **`hemit`** — the scalar call answers `1` there, i.e. the token emitted a record.  This is
  the class's fact that the token at the seam is a value: a number (`kind = 7`), a literal
  (`8`, `9`, `10`) or a matched literal window.  Producer: the class's document row, which
  reads the token's kind and the window the literal arm is decided by.

`hemit` at the `if.else405.i` edge has no producer, and that is a fact about the model
rather than about this module: `stage2ScalarValue` answers `0` at `kind = 0`
(`stage2ErrSetMsg`'s refusal), and the kind word at the seam is the literal the `phi`
selected.  `hcontSeamCalls_no_kind_zero` below proves that no `HcontSeamCalls` exists at a
kind-`0` store, which is what that edge writes.  Since `HcontSeamKind.hcA` fixes `calls.cA`
to the field's literal, `HcontSeamAbi.scan` — the field at `if.else405.i`'s `0` — is
refuted by that theorem, so `HcontSeamAbi G` has no inhabitant and neither does
`HcontSeamStaging`'s `scan` field.  The kind-`0` leaves need the refusal arm's rows
(`r₂.ret = 0` and the `if.then432.i` continuation) rather than the emit arm's.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeams

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The frame rule, and the words the seam's kind store misses

`if.then413.i`'s first instruction stores the `phi`'s literal at `%t352.i + 16`, the token
record's kind word.  The three calls' argument lists read the two stacks, the log and the
root slot, so every one of those words survives it: the store is inside the token record
and the staging separates that record from the rest. -/

/-- **The memory the seam's kind store leaves.**  The first call's argument list and the
copy call's test are read at this memory, so the group's rows name it. -/
abbrev seamKindStore {m0 : Mem} {G : WalkGeom m0} (Cs : WalkCarry G) (s : State)
    (cA : BitVec 32) : Mem :=
  writeBytes s.mem (Cs.stage.tok + 16) (natToBytes cA.toNat 4)

/-- **The atom's frame, over a region list.**  `BytesAt.frame` keeps an atom from a byte
agreement; this reaches the same conclusion from `UnchangedOutside` and the region list the
caller's staging states, which is the form the walk has.  It is `readBytes_of_frame_atom`'s
statement, and that lemma lives in `PipelineDischarge`, downstream of this module's chain,
so the rule is taken at its upstream congruence form (`readBytes_of_frame`) with the atom's
own byte list. -/
theorem seamFrame_atom {m0 m : Mem} {R : List (Nat × Nat)} {a : Nat} {bs : List UInt8}
    (h : UnchangedOutside m0 m R)
    (hsep : ∀ r ∈ R, r.1 + r.2 ≤ a ∨ a + bs.length ≤ r.1)
    (hb : readBytes m0 a bs.length = some bs) :
    readBytes m a bs.length = some bs := by
  rw [readBytes_of_frame h hsep]
  exact hb

/-- **A one-byte atom is its byte.** -/
theorem readByte_of_atom_one {m : Mem} {a : Nat} {b : UInt8}
    (h : readBytes m a 1 = some [b]) : readByte m a = some b := by
  have hb := readByte_of_readBytes h (k := 0) (by decide)
  simpa using hb

/-- **A byte at an extent of one is a one-byte atom.** -/
theorem atom_one_of_readByte {m : Mem} {a : Nat} {b : UInt8}
    (h : readByte m a = some b) : readBytes m a 1 = some [b] := by
  rw [LeanLLVM.Refinement.JsonEntrySteps.readBytes_one, h]
  rfl

/-- **`s2_value_pos`'s answer survives a store outside the two stacks.**  Its only reads
are the two tops, so a store that misses both stack extents leaves the answer alone. -/
theorem stage2ValuePos_writeBytes_outside {m : Mem} {a : Nat} {v : List UInt8}
    {sp rd ct cs : Nat}
    (hct : a + v.length ≤ ct ∨ ct + stage2StackExtent ≤ a)
    (hcs : a + v.length ≤ cs ∨ cs + stage2StackExtent ≤ a)
    (hsp : sp ≤ stage2StackExtent) :
    stage2ValuePos (writeBytes m a v) sp rd ct cs = stage2ValuePos m sp rd ct cs := by
  have h520 : 0 < stage2StackExtent := by decide
  by_cases h0 : sp = 0
  · simp only [stage2ValuePos, h0, ↓reduceIte]
  · have hsub : sp - 1 < stage2StackExtent := by omega
    have h1 : readByte (writeBytes m a v) (ct + (sp - 1)) = readByte m (ct + (sp - 1)) := by
      refine readByte_writeBytes_outside m v ?_
      rcases hct with h | h
      · right
        exact le_trans h (Nat.le_add_right ct (sp - 1))
      · left
        omega
    have h2 : readByte (writeBytes m a v) (cs + (sp - 1)) = readByte m (cs + (sp - 1)) := by
      refine readByte_writeBytes_outside m v ?_
      rcases hcs with h | h
      · right
        exact le_trans h (Nat.le_add_right cs (sp - 1))
      · left
        omega
    simp only [stage2ValuePos, h0, ↓reduceIte, h1, h2]

/-- **The kind store misses the type stack's extent.** -/
theorem seamStore_ctype_sep {m0 : Mem} {G : WalkGeom m0} (Cs : WalkCarry G) :
    Cs.stage.tok + 16 + 4 ≤ Cs.stage.ctype ∨
      Cs.stage.ctype + stage2StackExtent ≤ Cs.stage.tok + 16 := by
  have hp := staged_pair Cs.stage.separate
    (r := (Cs.stage.tok, stage2TokenExtent)) (q := (Cs.stage.ctype, stage2StackExtent))
    (by simp [stage2WalkRegions, stage2StagedWrites])
    (by simp [stage2WalkRegions, stage2StagedWrites])
    (by intro hne
        have h2 : stage2TokenExtent = stage2StackExtent := congrArg Prod.snd hne
        simp only [stage2TokenExtent, stage2StackExtent] at h2
        exact absurd h2 (by decide))
  simp only [stage2TokenExtent, stage2StackExtent] at hp ⊢
  omega

/-- **The kind store misses the state stack's extent.** -/
theorem seamStore_cst_sep {m0 : Mem} {G : WalkGeom m0} (Cs : WalkCarry G) :
    Cs.stage.tok + 16 + 4 ≤ Cs.stage.cst ∨
      Cs.stage.cst + stage2StackExtent ≤ Cs.stage.tok + 16 := by
  have hp := staged_pair Cs.stage.separate
    (r := (Cs.stage.tok, stage2TokenExtent)) (q := (Cs.stage.cst, stage2StackExtent))
    (by simp [stage2WalkRegions, stage2StagedWrites])
    (by simp [stage2WalkRegions, stage2StagedWrites])
    (by intro hne
        have h2 : stage2TokenExtent = stage2StackExtent := congrArg Prod.snd hne
        simp only [stage2TokenExtent, stage2StackExtent] at h2
        exact absurd h2 (by decide))
  simp only [stage2TokenExtent, stage2StackExtent] at hp ⊢
  omega

/-- **The kind store misses a stack byte's extent.** -/
theorem seamStore_stack_sep {m0 : Mem} {G : WalkGeom m0} (Cs : WalkCarry G) {base : Nat}
    (hb : base = Cs.stage.ctype ∨ base = Cs.stage.cst) :
    Cs.stage.tok + 16 + 4 ≤ base ∨ base + stage2StackExtent ≤ Cs.stage.tok + 16 := by
  rcases hb with hb | hb
  · rw [hb]; exact seamStore_ctype_sep Cs
  · rw [hb]; exact seamStore_cst_sep Cs

/-- **The kind store misses the log's extent.**  The log is one of the seven staged
objects and the token record another. -/
theorem seamStore_log_sep {m0 : Mem} {G : WalkGeom m0} (Cs : WalkCarry G) {off : Nat}
    (hoff : off + 8 ≤ stage2LogExtent) :
    Cs.stage.z + off + 8 ≤ Cs.stage.tok + 16 ∨
      Cs.stage.tok + 16 + 4 ≤ Cs.stage.z + off := by
  have hp := staged_pair Cs.stage.separate
    (r := (Cs.stage.z, stage2LogExtent)) (q := (Cs.stage.tok, stage2TokenExtent))
    (by simp [stage2WalkRegions, stage2StagedWrites])
    (by simp [stage2WalkRegions, stage2StagedWrites])
    (by intro hne
        have h2 : stage2LogExtent = stage2TokenExtent := congrArg Prod.snd hne
        simp only [stage2LogExtent, stage2TokenExtent] at h2
        exact absurd h2 (by decide))
  simp only [stage2TokenExtent, stage2LogExtent] at hp hoff ⊢
  omega

/-- **The kind store keeps a log word.**  The atom rule at the store's own region list:
the log word's extent and the store's region are ordered by the staging. -/
theorem seam_kindStore_keeps_log {m0 : Mem} {G : WalkGeom m0} (Cs : WalkCarry G) (s : State)
    {cA : BitVec 32} {off : Nat} (hoff : off + 8 ≤ stage2LogExtent) {bs : List UInt8}
    (hbs : readBytes s.mem (Cs.stage.z + off) 8 = some bs) :
    readBytes (seamKindStore Cs s cA) (Cs.stage.z + off) 8 = some bs := by
  have hlen : bs.length = 8 :=
    JsonEntrySteps.readBytes_length s.mem (Cs.stage.z + off) 8 hbs
  have hmain : readBytes (seamKindStore Cs s cA) (Cs.stage.z + off) bs.length = some bs := by
    refine seamFrame_atom (a := Cs.stage.z + off) (bs := bs)
      (unchangedOutside_writeBytes_own s.mem (Cs.stage.tok + 16) (natToBytes cA.toNat 4)) ?_ ?_
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [natToBytes_length]
      rcases seamStore_log_sep Cs hoff with h | h
      · right
        rw [hlen]
        exact h
      · left; exact h
    · rw [hlen]
      exact hbs
  rwa [hlen] at hmain

/-- **The kind store keeps a stack byte.**  One-byte atom at the stack's top. -/
theorem seam_kindStore_keeps_stackByte {m0 : Mem} {G : WalkGeom m0} (Cs : WalkCarry G)
    (s : State) {cA : BitVec 32} {base : Nat}
    (hb : base = Cs.stage.ctype ∨ base = Cs.stage.cst) {i : Nat}
    (hi : i < stage2StackExtent) {b : UInt8} (hbs : readByte s.mem (base + i) = some b) :
    readByte (seamKindStore Cs s cA) (base + i) = some b := by
  refine readByte_of_atom_one ?_
  refine seamFrame_atom (bs := [b]) (unchangedOutside_writeBytes_own s.mem (Cs.stage.tok + 16)
    (natToBytes cA.toNat 4)) ?_ (atom_one_of_readByte hbs)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rw [natToBytes_length]
  simp only [List.length_singleton]
  rcases seamStore_stack_sep Cs hb with h | h
  · left; omega
  · right; omega

/-- **The type stack's top byte is separated from the log.** -/
theorem seamCtypeByte_log_sep {m0 : Mem} {G : WalkGeom m0} {Cs : WalkCarry G} {s : State}
    (hInv : WalkInv G Cs s) {i : Nat} (hi : i + 1 ≤ stage2StackExtent) :
    Cs.stage.ctype + i + 1 ≤ Cs.stage.z ∨
      Cs.stage.z + stage2LogExtent ≤ Cs.stage.ctype + i := by
  have h := ctype_log_sep hInv
  simp only [stage2LogExtent] at h ⊢
  rcases h with h | h
  · left; omega
  · right; omega

/-- **The type stack's top byte is separated from the event stream.** -/
theorem seamCtypeByte_ev_sep {m0 : Mem} {G : WalkGeom m0} {Cs : WalkCarry G} {s : State}
    (hInv : WalkInv G Cs s) {i : Nat} (hi : i + 1 ≤ stage2StackExtent) :
    Cs.stage.ctype + i + 1 ≤ G.ev ∨ G.ev + G.evcap ≤ Cs.stage.ctype + i := by
  have h := ctype_ev_sep hInv
  rcases h with h | h
  · left; omega
  · right; omega

/-- **The type stack's top byte is separated from the refusal record.** -/
theorem seamCtypeByte_err_sep {m0 : Mem} {G : WalkGeom m0} {Cs : WalkCarry G} {s : State}
    (hInv : WalkInv G Cs s) {i : Nat} (hiw : i + 1 ≤ Cs.wlen) :
    Cs.stage.ctype + i + 1 ≤ Cs.stage.e ∨
      Cs.stage.e + stage2ErrorExtent ≤ Cs.stage.ctype + i := by
  have h := (stack_e_sep hInv).1
  simp only [stage2ErrorExtent] at h ⊢
  rcases h with h | h
  · left; omega
  · right; omega

/-- **A word `wordBytes` reads back is its value**, below the word's own width. -/
theorem bytesToNat_wordBytes8 {v : Nat} (hv : v < 2 ^ 64) :
    bytesToNat (wordBytes 8 v) = v := by
  rw [wordBytes, natToBytes_toNat, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]
  exact Nat.mod_eq_of_lt hv

/-! ### The seam's staged words

`HcontSeamStage` is a seam state's row: the invariant, the root slot's word, the
value-position test's answer at the seam's own memory, the scalar call's staging at the
memory the kind store leaves, the cursor record's error pointer and the scalar call's
emitted answer.  The group below derives the three call rows from it. -/

/-- **A seam's staged words.**  The four fields the invariant does not carry are the
class's document row's (`hroot`, `hval`, `hpreS`, `heErr`) and the emit row's (`hemit`);
nothing here is a call row, a segment or a bundle.

`hpreS` names the token's two cursor words and the delivered window because those are the
entry's, and `heErr` names the cursor record's error pointer for the frame's third region
(`s2ScalarValueFoot`'s refusal record): both are the gaps `JsonStage2StringStageFacts`
records as `hbase`/`he`, and the staging fixes neither.  `hval` is the value-position
test's answer at the seam: with `WalkInv.tyBytes`/`stBytes` it is
`walkValuePos_answer`'s map function, so the class supplies the two stack tops it reads. -/
structure HcontSeamStage {m0 : Mem} (G : WalkGeom m0) (Cs : WalkCarry G) (s : State)
    (cA0 : BitVec 32) : Type where
  /-- The seam state's invariant. -/
  hInv : WalkInv G Cs s
  /-- The root-done slot's word: the first call's second argument and the copy call's
  test. -/
  rdv : BitVec 32
  hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)
  /-- The value-position test's answer at the seam's own memory: `1`, the arm that takes
  the scalar call.  Producer: `walkValuePos_answer` and the class's two stack tops. -/
  hval : stage2ValuePos s.mem Cs.sp rdv.toNat Cs.stage.ctype Cs.stage.cst = some 1
  /-- The scalar call's staging, at the memory the kind store leaves. -/
  hpreS : s2ScalarValuePre
    [.ptr Cs.stage.c, .ptr Cs.stage.tok, .ptr Cs.stage.z]
    (seamKindStore Cs s cA0) s.next
  /-- The cursor record's error pointer, which the scalar call's refusal record is
  written through. -/
  heErr : stage2ReadWord (seamKindStore Cs s cA0) (Cs.stage.c + 1112) 8 = some Cs.stage.e
  /-- The scalar call's emitted answer: the token produced a record.  Producer: the
  class's document row at the token's kind and window. -/
  hemit : ∀ r, stage2Calls stage2SubCalls "od_scalar_value"
    [.ptr Cs.stage.c, .ptr Cs.stage.tok, .ptr Cs.stage.z] (seamKindStore Cs s cA0) s.next =
      some r → r.ret = .int 32 (BitVec.ofNat 32 1)

/-! ### The group, from the staged words

The three rows, chained: the preconditions are derived at the memory each call is made at,
the answers are the contracts' `answers`, the posts are `sound`'s, and the byte the copy
call reads is carried across the scalar call's frame by `seamFrame_atom`. -/

/-- **The seam's three call rows, from the seam's staged words** — as a subtype carrying
the two word agreements the `kind` group needs.  The value-position call resolves at the
post-store memory (its staging is the invariant's two stack bytes, which the kind store
keeps), hands the seam's memory and counter back (`sound`), and its word is `1` (`hval`
transported across the store, since `s2_value_pos` writes nothing).  The scalar call's
staging is `hpreS` at that memory, its answer is the emit row's, and the copy call's
staging is the invariant's state-stack top byte carried across the kind store
(`seam_kindStore_keeps_stackByte`) and across the scalar call's frame (`seamFrame_atom` at
`s2ScalarValue_framed`). -/
theorem hcontSeamCallsAt {m0 : Mem} {G : WalkGeom m0} {Cs : WalkCarry G} {s : State}
    {cA0 : BitVec 32} (st : HcontSeamStage G Cs s cA0) :
    ∃ calls : HcontSeamCalls G Cs s, calls.cA = cA0 ∧ calls.rdv = st.rdv := by
  have hct : Cs.stage.tok + 16 + (natToBytes cA0.toNat 4).length ≤ Cs.stage.ctype ∨
      Cs.stage.ctype + stage2StackExtent ≤ Cs.stage.tok + 16 :=
    seamStore_ctype_sep Cs
  have hcs : Cs.stage.tok + 16 + (natToBytes cA0.toNat 4).length ≤ Cs.stage.cst ∨
      Cs.stage.cst + stage2StackExtent ≤ Cs.stage.tok + 16 :=
    seamStore_cst_sep Cs
  -- the invariant's numeric clauses, as local facts for the width arguments
  have hwl : Cs.sp ≤ Cs.wlen := st.hInv.sp_le_wlen
  have hwcap : Cs.wlen ≤ stage2StackExtent := st.hInv.wlen_cap
  have hdsp : Cs.sp ≤ stage2StackExtent := st.hInv.depth_cap
  -- the depth word the calls pass
  have hsp32 : (BitVec.ofNat 32 Cs.sp).toNat = Cs.sp := walkAfterValue_sp st.hInv
  -- 1. the value-position call's staging, at the post-store memory
  have hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 Cs.sp), .int 32 st.rdv,
       .ptr Cs.stage.ctype, .ptr Cs.stage.cst] (seamKindStore Cs s cA0) s.next := by
    refine ⟨BitVec.ofNat 32 Cs.sp, st.rdv, Cs.stage.ctype, Cs.stage.cst, rfl, ?_⟩
    by_cases h0 : (BitVec.ofNat 32 Cs.sp).toNat = 0
    · exact Or.inl h0
    · have hi : (BitVec.ofNat 32 Cs.sp).toNat - 1 < Cs.wlen := by
        rw [hsp32]; omega
      have hicap : (BitVec.ofNat 32 Cs.sp).toNat - 1 < stage2StackExtent := by omega
      refine Or.inr
        ⟨⟨Cs.tyMap ((BitVec.ofNat 32 Cs.sp).toNat - 1), ?_⟩,
         ⟨Cs.stMap ((BitVec.ofNat 32 Cs.sp).toNat - 1), ?_⟩⟩
      · exact seam_kindStore_keeps_stackByte Cs s (Or.inl rfl) hicap (st.hInv.tyBytes.at hi)
      · exact seam_kindStore_keeps_stackByte Cs s (Or.inr rfl) hicap (st.hInv.stBytes.at hi)
  obtain ⟨r₁, hcall₁⟩ :=
    s2ValuePosContract.answers
      [.int 32 (BitVec.ofNat 32 Cs.sp), .int 32 st.rdv,
       .ptr Cs.stage.ctype, .ptr Cs.stage.cst] (seamKindStore Cs s cA0) s.next hpre₁
  -- 2. the answer's post: the seam's memory and counter, and the word `1`
  obtain ⟨v₁, hv₁, hret₁raw, hmem₁, hnext₁⟩ := s2ValuePos_sound hpre₁ hcall₁
  have hval₁ : stage2ValuePos (seamKindStore Cs s cA0) (BitVec.ofNat 32 Cs.sp).toNat
      st.rdv.toNat Cs.stage.ctype Cs.stage.cst = some 1 := by
    have h := stage2ValuePos_writeBytes_outside (m := s.mem) (a := Cs.stage.tok + 16)
      (v := natToBytes cA0.toNat 4) (sp := Cs.sp) (rd := st.rdv.toNat)
      (ct := Cs.stage.ctype) (cs := Cs.stage.cst) hct hcs hdsp
    rw [hsp32]
    rw [h, st.hval]
  have hv1 : v₁ = 1 := (Option.some.inj (by rw [hval₁] at hv₁; exact hv₁)).symm
  have hret₁ : r₁.ret = .int 32 (BitVec.ofNat 32 1) := by
    rw [hret₁raw, hv1]
  -- 3. the log's base word, kept across the kind store
  have hzread : readBytes (seamKindStore Cs s cA0) Cs.stage.z 8 = some (wordBytes 8 G.ev) :=
    seam_kindStore_keeps_log Cs s (off := 0) (by decide) st.hInv.log_base
  -- 4. the scalar call's staging and answer, at the memory the first call left
  have hpre₂ : s2ScalarValuePre
      [.ptr Cs.stage.c, .ptr Cs.stage.tok, .ptr Cs.stage.z] r₁.mem r₁.next := by
    rw [hmem₁, hnext₁]
    exact st.hpreS
  obtain ⟨r₂, hcall₂⟩ :=
    s2ScalarValueContract.answers
      [.ptr Cs.stage.c, .ptr Cs.stage.tok, .ptr Cs.stage.z] r₁.mem r₁.next hpre₂
  have hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1) := by
    refine st.hemit r₂ ?_
    rw [← hmem₁, ← hnext₁]
    exact hcall₂
  -- 5. the scalar answer's shape and frame, and the byte the copy call reads
  obtain ⟨m₂, ok₂, hr₂, hfr₂⟩ := s2ScalarValue_shape hpre₂ hcall₂
  have hrmem₂ : r₂.mem = m₂ := by rw [hr₂]
  have hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 Cs.sp), .ptr (G.next0 + 8),
       .ptr Cs.stage.ctype, .ptr Cs.stage.cst] r₂.mem r₂.next := by
    refine ⟨BitVec.ofNat 32 Cs.sp, G.next0 + 8, Cs.stage.ctype, Cs.stage.cst, rfl, ?_⟩
    by_cases h0 : (BitVec.ofNat 32 Cs.sp).toNat = 0
    · exact Or.inl h0
    · -- the scalar staging's own words, at the memory the call was handed
      obtain ⟨cS, tS, oS, hargs, base, e, pos, endp, kind, buf, len, cap, win, hbase, he,
        hpos, hend, hkind, hbuf, hlen2, hcap, hroom, hwin⟩ := st.hpreS
      simp only [List.cons.injEq, and_true, true_and, Value.ptr.injEq] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      have hqs : (BitVec.ofNat 32 Cs.sp).toNat - 1 + 1 ≤ stage2StackExtent := by
        rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0), hsp32]
        exact hdsp
      have hqw : (BitVec.ofNat 32 Cs.sp).toNat - 1 + 1 ≤ Cs.wlen := by
        rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0), hsp32]
        exact hwl
      -- the cursor record's error pointer is the staging's
      have heE : e = Cs.stage.e := by
        have h : stage2ReadWord (seamKindStore Cs s cA0) (Cs.stage.c + 1112) 8 = some e := he
        exact Option.some.inj (h.symm.trans st.heErr)
      -- the log's two words are the staging's
      have hbufv : buf = G.ev := by
        have h : some (bytesToNat (wordBytes 8 G.ev)) = some buf := by
          have hraw := hbuf
          simp only [stage2ReadWord] at hraw
          rw [hzread] at hraw
          exact hraw
        rw [← Option.some.inj h, bytesToNat_wordBytes8 G.evLt]
      have hcapv : cap = G.evcap := by
        have hcapS : readBytes (seamKindStore Cs s cA0) (Cs.stage.z + 16) 8 =
            some (wordBytes 8 G.evcap) :=
          seam_kindStore_keeps_log Cs s (off := 16) (by decide) st.hInv.log_cap
        have h : some (bytesToNat (wordBytes 8 G.evcap)) = some cap := by
          have hraw := hcap
          simp only [stage2ReadWord] at hraw
          rw [hcapS] at hraw
          exact hraw
        rw [← Option.some.inj h, bytesToNat_wordBytes8 G.evcapLt]
      -- the scalar call's frame, region by region
      have hfoot : s2ScalarValueFoot [.ptr Cs.stage.c, .ptr Cs.stage.tok, .ptr Cs.stage.z]
          r₁.mem r₁.next =
          [(Cs.stage.z + 8, 8), (buf + len, stage2RecordBytes)] ++
            [(e, stage2ErrorExtent)] := by
        rw [hmem₁]
        simp only [s2ScalarValueFoot, hbuf, hlen2, he, List.singleton_append]
      have hfr := hfr₂
      rw [hfoot] at hfr
      -- the byte the copy call reads: the type stack's top, at the seam
      have hsrc : readByte (seamKindStore Cs s cA0)
          (Cs.stage.ctype + ((BitVec.ofNat 32 Cs.sp).toNat - 1)) =
          some (Cs.tyMap ((BitVec.ofNat 32 Cs.sp).toNat - 1)) :=
        seam_kindStore_keeps_stackByte Cs s (Or.inl rfl) (by omega) (by
          refine st.hInv.tyBytes.at ?_
          omega)
      refine Or.inr ⟨Cs.tyMap ((BitVec.ofNat 32 Cs.sp).toNat - 1), ?_⟩
      refine readByte_of_atom_one ?_
      have hkeep : readBytes m₂
          (Cs.stage.ctype + ((BitVec.ofNat 32 Cs.sp).toNat - 1)) 1 =
          some [Cs.tyMap ((BitVec.ofNat 32 Cs.sp).toNat - 1)] := by
        refine seamFrame_atom (m0 := r₁.mem) (m := m₂)
          (bs := [Cs.tyMap ((BitVec.ofNat 32 Cs.sp).toNat - 1)]) hfr ?_ ?_
        · intro q hq
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with (rfl | rfl) | rfl
          · have h := seamCtypeByte_log_sep st.hInv hqs
            simp only [stage2LogExtent] at h ⊢
            rcases h with h | h
            · right
              exact le_trans h (by omega)
            · left
              omega
          · have h := seamCtypeByte_ev_sep st.hInv hqs
            rcases h with h | h
            · right
              rw [hbufv]
              exact le_trans h (Nat.le_add_right G.ev len)
            · left
              rw [hbufv]
              simp only [stage2RecordBytes] at hroom ⊢
              omega
          · obtain rfl := heE
            have h := seamCtypeByte_err_sep st.hInv hqw
            rcases h with h | h
            · right; exact h
            · left; exact h
        · rw [hmem₁]
          exact atom_one_of_readByte hsrc
      rw [hrmem₂]
      exact hkeep
  obtain ⟨r₃, hcall₃⟩ :=
    s2AfterValueContract.answers
      [.int 32 (BitVec.ofNat 32 Cs.sp), .ptr (G.next0 + 8),
       .ptr Cs.stage.ctype, .ptr Cs.stage.cst] r₂.mem r₂.next hpre₃
  exact ⟨
    { cA := cA0
      rdv := st.rdv
      r₁ := r₁
      xA := BitVec.ofNat 32 1
      hpre₁ := hpre₁
      hcall₁ := hcall₁
      hret₁ := hret₁
      hbit0 := by decide
      hzread := hzread
      r₂ := r₂
      hpre₂ := hpre₂
      hcall₂ := hcall₂
      hret₂ := hret₂
      hev64 := G.evLt
      r₃ := r₃
      hpre₃ := hpre₃
      hcall₃ := hcall₃ }, rfl, rfl⟩

/-- **The seam's group, from the staged words**, with the two word agreements the `kind`
group needs.  `HcontSeamCalls` is data, so the existential above is read at a classical
choice — the outcomes it names are the callees', not a hypothesis. -/
theorem hcontSeamCallsNonempty {m0 : Mem} {G : WalkGeom m0} {Cs : WalkCarry G}
    {s : State} {cA0 : BitVec 32} (st : HcontSeamStage G Cs s cA0) :
    Nonempty { calls : HcontSeamCalls G Cs s // calls.cA = cA0 ∧ calls.rdv = st.rdv } := by
  obtain ⟨calls, hcA, hrdv⟩ := hcontSeamCallsAt st
  exact ⟨⟨calls, hcA, hrdv⟩⟩

/-- **The seam's group, from the staged words.** -/
noncomputable def hcontSeamCallsOf {m0 : Mem} {G : WalkGeom m0} {Cs : WalkCarry G}
    {s : State} {cA0 : BitVec 32} (st : HcontSeamStage G Cs s cA0) :
    { calls : HcontSeamCalls G Cs s // calls.cA = cA0 ∧ calls.rdv = st.rdv } :=
  Classical.choice (hcontSeamCallsNonempty st)

/-- **A seam's kind group, from the staged words.**  `HcontSeamKind.hroot` is the root
slot's word at the seam's *own* memory (the store is what the calls are read at), so the
only transport is the `rdv` agreement. -/
noncomputable def hcontSeamKindOf {m0 : Mem} {G : WalkGeom m0} {Cs : WalkCarry G}
    {s : State} {cA0 : BitVec 32} (st : HcontSeamStage G Cs s cA0) :
    HcontSeamKind G Cs s cA0 :=
  let p := hcontSeamCallsOf st
  { calls := p.1
    hcA := p.2.1
    hroot := by
      have hrdv : p.1.rdv = st.rdv := p.2.2
      rw [hrdv]
      exact st.hroot }

/-! ### The five seams, from the staged rows

`HcontSeamAbi` is one `∀`-field per seam; the staging structure is the same five fields
at the seam states those fields name, so the group is a re-indexing of the rows rather
than a second assumption. -/

/-- **The seam's staged words at each of the walk's five seams.**  The four continuing
fields carry the kind literal `HcontSeamAbi` fixes for them (`0`, `9`, `10`, `8`); the
last entry's seam is a `Σ` over the literal because `HcontSeamAbi.last` states the calls
alone and the literal is the class's (the `.scalar` route's `7`, for instance).

`scan` is the field `hcontSeamCalls_no_literal_zero` refutes: at `if.else405.i`'s literal
the scalar call answers `0`, so that edge's rows are the refusal arm's, not this group's. -/
structure HcontSeamStaging {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The continuing run class's seam: the scan arm's `if.then413.i`, `if.else405.i`'s
  `0`. -/
  scan : ∀ (C : WalkCarry G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8),
    HcontSeamStage G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1) (BitVec.ofNat 32 0)
  /-- The `'f'` leaf's seam: `FS413`, `if.then397.i`'s `9`. -/
  scanF : ∀ (C : WalkCarry G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8),
    HcontSeamStage G (ContTailStartC C)
      (FS413 (contWsSeamS C (wsSlAt G sl b35 ix v k) k x1) x1) (BitVec.ofNat 32 9)
  /-- `110`'s leaf's seam: `ClsS413T`, `if.then403.i`'s `10`. -/
  scan56True : ∀ (C : WalkCarry G) (sl : State) (b35 : UInt8) (ix : BitVec 64)
    (v : BitVec 32) (k : Nat) (x1 : BitVec 8),
    HcontSeamStage G (ContTailStartC C)
      (ClsS413T (contWsSeamS C (wsSlAt G sl b35 ix v k) k x1) x1) (BitVec.ofNat 32 10)
  /-- `116`'s leaf's seam: `ClsS58T`, `LeafBlock58`'s `8`. -/
  scan58True : ∀ (C : WalkCarry G) (sl : State) (b35 : UInt8) (ix : BitVec 64)
    (v : BitVec 32) (k : Nat) (x1 : BitVec 8),
    HcontSeamStage G (ContTailStartC C)
      (ClsS58T (contWsSeamS C (wsSlAt G sl b35 ix v k) k x1) x1) (BitVec.ofNat 32 8)
  /-- The last entry's seam, at the literal the class's token selects. -/
  last : ∀ (C : WalkCarry G) (s : State) (x : BitVec 8) (inc nep : BitVec 64)
    (v : Nat) (ix : BitVec 64) (b35 : UInt8),
    Σ cA0 : BitVec 32,
      HcontSeamStage G (TailStartC C) (hlastTail C s x inc nep v ix b35) cA0

/-- **`HcontSeamAbi`, from the seam's staged words.**  Each field is the group the staging
row produces at the seam state the field names; the four continuing fields are
`hcontSeamKindOf`'s, which is the calls together with the root slot's word, and the last
entry's is `hcontSeamCallsOf`'s at the literal its row selects. -/
noncomputable def hcontSeamAbi {m0 : Mem} (G : WalkGeom m0) (hs : HcontSeamStaging G) :
    HcontSeamAbi G where
  scan := fun C sl b35 ix v k x1 => hcontSeamKindOf (hs.scan C sl b35 ix v k x1)
  scanF := fun C sl b35 ix v k x1 => hcontSeamKindOf (hs.scanF C sl b35 ix v k x1)
  scan56True := fun C sl b35 ix v k x1 => hcontSeamKindOf (hs.scan56True C sl b35 ix v k x1)
  scan58True := fun C sl b35 ix v k x1 => hcontSeamKindOf (hs.scan58True C sl b35 ix v k x1)
  last := fun C s x inc nep v ix b35 =>
    (hcontSeamCallsOf (hs.last C s x inc nep v ix b35).2).1

/-! ### The kind-`0` edge has no group

The seam's kind word is the literal `if.then413.i`'s `phi` selects, and `od_scalar_value`
answers `0` at `kind = 0`: `stage2ScalarValue`'s first arm writes the refusal record and
returns zero.  So a seam whose store writes `0` cannot carry `HcontSeamCalls`, whose third
row is the *emit* arm's answer (`hret₂ : r₂.ret = 1`).  The `if.else405.i` edge writes
exactly that literal, and it is the edge three of the six leaves into `if.then413.i` come
from. -/

/-- **`od_scalar_value` answers zero at a zero kind word.**  The model's first arm, read
off its own definition at the staging that makes the call resolve. -/
theorem s2ScalarValue_ret_of_kind_zero {c t o : Nat} {mem : Mem} {next : Nat}
    {r : CallOutcome}
    (hpre : s2ScalarValuePre [.ptr c, .ptr t, .ptr o] mem next)
    (hkind0 : stage2ReadWord mem (t + 16) 4 = some 0)
    (hcall : stage2Calls stage2SubCalls "od_scalar_value" [.ptr c, .ptr t, .ptr o] mem next =
      some r) :
    r.ret = .int 32 (BitVec.ofNat 32 0) := by
  obtain ⟨c', t', o', hargs, base, e, pos, endp, kind, buf, len, cap, win, hbase, he, hpos,
    hend, hkind, hbuf, hlen, hcap, hroom, hwin⟩ := hpre
  simp only [List.cons.injEq, List.nil_eq, and_true, true_and, Value.ptr.injEq] at hargs
  obtain ⟨rfl, rfl, rfl⟩ := hargs
  have hk0 : kind = 0 := Option.some.inj (hkind.symm.trans hkind0)
  rw [stage2Calls_od_scalar_value, stage2ScalarValueCall] at hcall
  simp only [stage2ScalarValue, hbase, he, hpos, hend, hkind, hk0, ↓reduceIte] at hcall
  rw [(Option.some.inj hcall).symm]

/-- **The kind store writes the literal's four bytes.**  The token's kind word at the
post-store memory is the store's own list read back. -/
theorem seamKindStore_word {m0 : Mem} {G : WalkGeom m0} (Cs : WalkCarry G) (s : State)
    {cA : BitVec 32} (hlt : cA.toNat < 2 ^ 32) :
    stage2ReadWord (seamKindStore Cs s cA) (Cs.stage.tok + 16) 4 = some cA.toNat := by
  have hread : readBytes (seamKindStore Cs s cA) (Cs.stage.tok + 16) 4 =
      some (natToBytes cA.toNat 4) := by
    simpa only [seamKindStore, natToBytes_length]
      using readBytes_writeBytes_same s.mem (natToBytes cA.toNat 4) (addr := Cs.stage.tok + 16)
  have hb : bytesToNat (natToBytes cA.toNat 4) = cA.toNat := by
    rw [natToBytes_toNat, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide]
    exact Nat.mod_eq_of_lt hlt
  show (readBytes (seamKindStore Cs s cA) (Cs.stage.tok + 16) 4).map bytesToNat = _
  rw [hread]
  show some (bytesToNat (natToBytes cA.toNat 4)) = some cA.toNat
  rw [hb]

/-- **No seam group exists at a kind-`0` store.**  `HcontSeamCalls`'s scalar row demands
the emit arm's answer (`hret₂`), and the model answers `0` there; the first row's post
places the scalar call at the post-store memory, so the two are about the same word. -/
theorem hcontSeamCalls_no_kind_zero {m0 : Mem} {G : WalkGeom m0} {Cs : WalkCarry G}
    {s : State} (calls : HcontSeamCalls G Cs s) (hcA : calls.cA.toNat = 0) : False := by
  have hpass := s2ValuePos_sound calls.hpre₁ calls.hcall₁
  obtain ⟨v, hv, hret, hmem, hnext⟩ := hpass
  have hkind0 : stage2ReadWord (seamKindStore Cs s calls.cA) (Cs.stage.tok + 16) 4 =
      some 0 := by
    have h := seamKindStore_word Cs s (cA := calls.cA) (by have := calls.cA.isLt; omega)
    rw [h, hcA]
  have hpre₂ : s2ScalarValuePre
      [.ptr Cs.stage.c, .ptr Cs.stage.tok, .ptr Cs.stage.z]
      (seamKindStore Cs s calls.cA) s.next := by
    have h := calls.hpre₂
    rw [hmem, hnext] at h
    exact h
  have hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr Cs.stage.c, .ptr Cs.stage.tok, .ptr Cs.stage.z]
      (seamKindStore Cs s calls.cA) s.next = some calls.r₂ := by
    have h := calls.hcall₂
    rw [hmem, hnext] at h
    exact h
  have hzero := s2ScalarValue_ret_of_kind_zero hpre₂ hkind0 hcall₂
  rw [calls.hret₂] at hzero
  exact absurd hzero (by decide)

/-- **No seam group exists at the `if.else405.i` edge.**  That edge's `phi` incoming is
the literal `0`, and `if.then413.i` stores it as the token's kind word. -/
theorem hcontSeamCalls_no_literal_zero {m0 : Mem} {G : WalkGeom m0} {Cs : WalkCarry G}
    {s : State} (calls : HcontSeamCalls G Cs s) (hcA : calls.cA = BitVec.ofNat 32 0) :
    False :=
  hcontSeamCalls_no_kind_zero calls (by rw [hcA]; decide)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.seamFrame_atom
#print axioms LeanLLVM.Refinement.WalkScope.readByte_of_atom_one
#print axioms LeanLLVM.Refinement.WalkScope.atom_one_of_readByte
#print axioms LeanLLVM.Refinement.WalkScope.stage2ValuePos_writeBytes_outside
#print axioms LeanLLVM.Refinement.WalkScope.seamStore_ctype_sep
#print axioms LeanLLVM.Refinement.WalkScope.seamStore_cst_sep
#print axioms LeanLLVM.Refinement.WalkScope.seamStore_stack_sep
#print axioms LeanLLVM.Refinement.WalkScope.seamStore_log_sep
#print axioms LeanLLVM.Refinement.WalkScope.seamCtypeByte_log_sep
#print axioms LeanLLVM.Refinement.WalkScope.seamCtypeByte_ev_sep
#print axioms LeanLLVM.Refinement.WalkScope.seamCtypeByte_err_sep
#print axioms LeanLLVM.Refinement.WalkScope.seam_kindStore_keeps_log
#print axioms LeanLLVM.Refinement.WalkScope.seam_kindStore_keeps_stackByte
#print axioms LeanLLVM.Refinement.WalkScope.bytesToNat_wordBytes8
#print axioms LeanLLVM.Refinement.WalkScope.hcontSeamCallsAt
#print axioms LeanLLVM.Refinement.WalkScope.hcontSeamCallsNonempty
#print axioms LeanLLVM.Refinement.WalkScope.hcontSeamCallsOf
#print axioms LeanLLVM.Refinement.WalkScope.hcontSeamKindOf
#print axioms LeanLLVM.Refinement.WalkScope.hcontSeamAbi
#print axioms LeanLLVM.Refinement.WalkScope.s2ScalarValue_ret_of_kind_zero
#print axioms LeanLLVM.Refinement.WalkScope.seamKindStore_word
#print axioms LeanLLVM.Refinement.WalkScope.hcontSeamCalls_no_kind_zero
#print axioms LeanLLVM.Refinement.WalkScope.hcontSeamCalls_no_literal_zero

end WalkScope
end LeanLLVM.Refinement
