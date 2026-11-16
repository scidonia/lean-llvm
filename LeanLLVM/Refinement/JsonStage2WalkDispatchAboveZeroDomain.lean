/-
The comma's and the colon's arms above depth zero, at documents that reach depth one.

`LastEntryArm.commaAboveZero`/`.colonAboveZero` and their `HcontArm` twins are the
container pair's and the marker's routes at `C.sp ≠ 0`.  Their segment is stated from the
loop head, so the regression has to exhibit them at a head a document actually reaches.
The layer's only depth-one producer is `containerOpen_depth_one`
(`JsonStage2WalkDispatchOpeners`): the opener's own merge and the header's pass, landing
at the entry immediately after the opener.  The documents are therefore the opener
followed by the delimiter, and nothing else:

| arm | document | bytes | entries | level |
|---|---|---|---|---|
| comma above zero | `[,` | `91, 44` | two | last entry |
| comma above zero (brace) | `{,` | `123, 44` | two | last entry |
| colon above zero | `[:` | `91, 58` | two | last entry |
| colon above zero (brace) | `{:` | `123, 58` | two | last entry |
| comma above zero | `[,0` | `91, 44, 48` | three | continuing |
| colon above zero | `[:0` | `91, 58, 48` | three | continuing |

`[0,` is not in the table, and the reason is a gap in the layer rather than a missing
arm: its comma sits at the third entry, and reaching it needs a head state after a
*continuing scalar merge*, which no producer states.  The continuing-scalar successor
head is the named gap; if it is produced later, `[0,` is an added row here, not a
replacement for the rows above.

The two stack bytes the arm reads are the opener's push, `ifEnd24TyByte` on the type
stack and `ifEnd24StByte` (zero) on the state stack, as `openC₉` defines the merge carry.
`containerOpen_depth_one` does not expose the reached carry's two maps, so a wrapper that
took the arm's fields one by one had to carry them as premises.  The continuing comma's arm
is produced from the state instead (`hcontArm_commaAboveZero_of_staging`,
`JsonStage2WalkDispatchAboveZeroOfStaging`), which reads the two maps off the carry by
witness, so `[,0`'s regression supplies nothing about the stacks.  The colon's two arms are
produced beside it — `hcontArm_colonAboveZero_of_staging` and
`lastEntryArm_colonAboveZero_of_staging` in the same module — and so is the comma's at the
last entry (`lastEntryArm_commaAboveZero_of_staging`), so `[:`, `{:` and `[,`/`{,` supply
nothing about the stacks either, and their theorems state the dispatch's result without the
two-map implication the by-hand wrappers needed.

The routes these documents reach are the refusals: the push leaves the state stack at
zero (`ifEnd24StByte_zero`), and every merge route tests it against `1` (bracket) or `3`
(brace), so the enum's case split at the push's bytes selects the refusal.  The merge
routes are wired and reachable in general, but the opener's product cannot select them;
the companion theorems those documents exercise are therefore `commaBracketRefuse_at`,
`commaBraceRefuse_at`, `colonMarkerRefuse_at` and `colonBraceRefuse_at`.

The negative control is the depth-zero documents `,` and `:`: the same byte detector
finds `44` and `58` there, so the byte premise holds, but the depth is the seed's zero
and the arms' `C.sp ≠ 0` premise is refuted.  The affirmative control for that depth
detector is the producer's `C'.sp = 1`, read off each reachability theorem below.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchAboveZeroOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpenersDomain

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

namespace WalkScope

/-! ### The documents, as the staging hands them over -/

/-- **A two-entry document whose first entry is an opener and whose second is a
delimiter.**  The two reads are the staged memory's, the counts are the ABI's, and the
entry stream's lanes are the two positions. -/
structure DelimiterLastDocument {m0 : Mem} (G : WalkGeom m0) (c d : UInt8) : Prop where
  /-- The document is two bytes long. -/
  len : G.n = 2
  /-- The entry stream holds two entries. -/
  count : G.nep = 2
  /-- The document's bytes are the opener and the delimiter. -/
  bytes : readBytes m0 G.b 2 = some [c, d]
  /-- The entry stream's lanes are the two positions. -/
  lanes : readLanes32 m0 G.ep 2 = some [0, 1]

/-- **A three-entry document whose first entry is an opener and whose second is a
delimiter**, so the delimiter's head has an entry left. -/
structure DelimiterContDocument {m0 : Mem} (G : WalkGeom m0) (c d e : UInt8) : Prop where
  /-- The document is three bytes long. -/
  len : G.n = 3
  /-- The entry stream holds three entries. -/
  count : G.nep = 3
  /-- The document's bytes are the opener, the delimiter and a trailing digit. -/
  bytes : readBytes m0 G.b 3 = some [c, d, e]
  /-- The entry stream's lanes are the three positions. -/
  lanes : readLanes32 m0 G.ep 3 = some [0, 1, 2]

/-! ### The documents' bytes and entry streams -/

/-- The two-entry document's byte list is the read's. -/
theorem DelimiterLastDocument.bs {m0 : Mem} {G : WalkGeom m0} {c d : UInt8}
    (h : DelimiterLastDocument G c d) : G.bs = [c, d] := by
  have hread : readBytes m0 G.b G.n = some [c, d] := by rw [h.len]; exact h.bytes
  exact Option.some.inj (G.doc.symm.trans hread)

/-- The two-entry document's entry stream is the read's. -/
theorem DelimiterLastDocument.ent {m0 : Mem} {G : WalkGeom m0} {c d : UInt8}
    (h : DelimiterLastDocument G c d) : G.ent = [0, 1] := by
  have hread : readLanes32 m0 G.ep G.nep = some [0, 1] := by
    rw [h.count]; exact h.lanes
  exact Option.some.inj (G.entries.symm.trans hread)

/-- The two-entry document's first entry is at position zero. -/
theorem DelimiterLastDocument.entryPos_zero {m0 : Mem} {G : WalkGeom m0} {c d : UInt8}
    (h : DelimiterLastDocument G c d) : entryPos G 0 = 0 := by
  simp only [entryPos, h.ent, List.getD]
  rfl

/-- The two-entry document's second entry is at position one. -/
theorem DelimiterLastDocument.entryPos_one {m0 : Mem} {G : WalkGeom m0} {c d : UInt8}
    (h : DelimiterLastDocument G c d) : entryPos G 1 = 1 := by
  simp only [entryPos, h.ent, List.getD]
  rfl

/-- The two-entry document's first byte is the opener's. -/
theorem DelimiterLastDocument.entryByte_zero {m0 : Mem} {G : WalkGeom m0} {c d : UInt8}
    (h : DelimiterLastDocument G c d) : entryByte G 0 = c := by
  have hpos : entryPos G 0 = 0 := h.entryPos_zero
  have hbs : G.bs = [c, d] := h.bs
  simp only [entryByte, hpos, hbs, List.getD]
  rfl

/-- The two-entry document's second byte is the delimiter's. -/
theorem DelimiterLastDocument.entryByte_one {m0 : Mem} {G : WalkGeom m0} {c d : UInt8}
    (h : DelimiterLastDocument G c d) : entryByte G 1 = d := by
  have hpos : entryPos G 1 = 1 := h.entryPos_one
  have hbs : G.bs = [c, d] := h.bs
  simp only [entryByte, hpos, hbs, List.getD]
  rfl

/-- The three-entry document's byte list is the read's. -/
theorem DelimiterContDocument.bs {m0 : Mem} {G : WalkGeom m0} {c d e : UInt8}
    (h : DelimiterContDocument G c d e) : G.bs = [c, d, e] := by
  have hread : readBytes m0 G.b G.n = some [c, d, e] := by rw [h.len]; exact h.bytes
  exact Option.some.inj (G.doc.symm.trans hread)

/-- The three-entry document's entry stream is the read's. -/
theorem DelimiterContDocument.ent {m0 : Mem} {G : WalkGeom m0} {c d e : UInt8}
    (h : DelimiterContDocument G c d e) : G.ent = [0, 1, 2] := by
  have hread : readLanes32 m0 G.ep G.nep = some [0, 1, 2] := by
    rw [h.count]; exact h.lanes
  exact Option.some.inj (G.entries.symm.trans hread)

/-- The three-entry document's first entry is at position zero. -/
theorem DelimiterContDocument.entryPos_zero {m0 : Mem} {G : WalkGeom m0} {c d e : UInt8}
    (h : DelimiterContDocument G c d e) : entryPos G 0 = 0 := by
  simp only [entryPos, h.ent, List.getD]
  rfl

/-- The three-entry document's second entry is at position one. -/
theorem DelimiterContDocument.entryPos_one {m0 : Mem} {G : WalkGeom m0} {c d e : UInt8}
    (h : DelimiterContDocument G c d e) : entryPos G 1 = 1 := by
  simp only [entryPos, h.ent, List.getD]
  rfl

/-- The three-entry document's first byte is the opener's. -/
theorem DelimiterContDocument.entryByte_zero {m0 : Mem} {G : WalkGeom m0} {c d e : UInt8}
    (h : DelimiterContDocument G c d e) : entryByte G 0 = c := by
  have hpos : entryPos G 0 = 0 := h.entryPos_zero
  have hbs : G.bs = [c, d, e] := h.bs
  simp only [entryByte, hpos, hbs, List.getD]
  rfl

/-- The three-entry document's second byte is the delimiter's. -/
theorem DelimiterContDocument.entryByte_one {m0 : Mem} {G : WalkGeom m0} {c d e : UInt8}
    (h : DelimiterContDocument G c d e) : entryByte G 1 = d := by
  have hpos : entryPos G 1 = 1 := h.entryPos_one
  have hbs : G.bs = [c, d, e] := h.bs
  simp only [entryByte, hpos, hbs, List.getD]
  rfl

/-! ### The push's type-stack bytes

The two opener bytes the documents test, at `ifEnd24TyByte`: `[` pushes `2` (the
bracket marker) and `{` pushes `1` (the brace marker).  The state stack's byte is zero
(`ifEnd24StByte_zero`), which is what sends the merge's test to the refusal.
-/

/-- `[`'s push writes `2` on the type stack. -/
theorem ifEnd24TyByte_of_91 : ifEnd24TyByte (BitVec.ofNat 8 91) = 2 := by decide

/-- `{`'s push writes `1` on the type stack. -/
theorem ifEnd24TyByte_of_123 : ifEnd24TyByte (BitVec.ofNat 8 123) = 1 := by decide

/-! ### The depth-one head each document reaches

`containerOpen_depth_one` composes the opener's merge and the header's pass; the entry
immediately after the opener is the delimiter, so its byte is the document's second.
-/

/-- **`[,`/`{,`/`[:`/`{:`'s depth-one head is the delimiter's.**  The opener is entry
zero at depth zero, so its product is a loop head one level deeper at entry one, and the
head's `%8` is the document's second byte. -/
theorem depthOne_last_reachable {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G} {c d : UInt8}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterLastDocument G c d)
    (hc : c = 91 ∨ c = 123)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 d.toNat)) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hInv := seededInv (S := S) hargs hnext hn
  have h8s : evalOperand (openerHead G S args next) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 c.toNat)) := by
    simpa only [evalOperand] using
      seed_head_byte G S (openerHead G S args next) h.entryByte_zero hInv
  have hopen : BitVec.ofNat 8 c.toNat = BitVec.ofNat 8 91 ∨
      BitVec.ofNat 8 c.toNat = BitVec.ofNat 8 123 := by
    rcases hc with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
  obtain ⟨C', s', hInv', hblock', hsp', hk'⟩ :=
    containerOpen_depth_one G (walkSeed G S) (openerHead G S args next) hInv
      (walkSeed_block G S) h8s hopen
      (by change (0 : Nat) ≤ 519; decide)
      hrd hpreV r hcall hret
      (by change (0 : Nat) + 1 < G.nep; rw [h.count]; decide)
  have hsp1 : C'.sp = 1 := by rw [hsp']; rfl
  have hk1 : C'.k = 1 := by rw [hk']; rfl
  refine ⟨C', s', hInv', hblock', hsp1, hk1, ?_⟩
  have hreg := hInv'.iter.reg8
  rw [hk1, h.entryByte_one] at hreg
  simpa only [evalOperand] using hreg

/-- **`[,0`/`[:0`'s depth-one head is the delimiter's, with an entry left.**  The
three-entry document's opener is entry zero at depth zero, so the head is one level
deeper at entry one and the continuing guard holds. -/
theorem depthOne_cont_reachable {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G} {c d e : UInt8}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G c d e)
    (hc : c = 91 ∨ c = 123)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      C'.k + 1 < G.nep ∧
      evalOperand s' (.reg "%8") = some (.int 8 (BitVec.ofNat 8 d.toNat)) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hInv := seededInv (S := S) hargs hnext hn
  have h8s : evalOperand (openerHead G S args next) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 c.toNat)) := by
    simpa only [evalOperand] using
      seed_head_byte G S (openerHead G S args next) h.entryByte_zero hInv
  have hopen : BitVec.ofNat 8 c.toNat = BitVec.ofNat 8 91 ∨
      BitVec.ofNat 8 c.toNat = BitVec.ofNat 8 123 := by
    rcases hc with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
  obtain ⟨C', s', hInv', hblock', hsp', hk'⟩ :=
    containerOpen_depth_one G (walkSeed G S) (openerHead G S args next) hInv
      (walkSeed_block G S) h8s hopen
      (by change (0 : Nat) ≤ 519; decide)
      hrd hpreV r hcall hret
      (by change (0 : Nat) + 1 < G.nep; rw [h.count]; decide)
  have hsp1 : C'.sp = 1 := by rw [hsp']; rfl
  have hk1 : C'.k = 1 := by rw [hk']; rfl
  have hguard : C'.k + 1 < G.nep := by rw [hk1, h.count]; omega
  refine ⟨C', s', hInv', hblock', hsp1, hk1, hguard, ?_⟩
  have hreg := hInv'.iter.reg8
  rw [hk1, h.entryByte_one] at hreg
  simpa only [evalOperand] using hreg

/-! ### The arms, through the real dispatch

Each wrapper inhabits its arm at the head the document reaches — through the class's
producer — and applies `LastEntryArm.dispatch` or `HcontArm.dispatch`.  No wrapper supplies
a stack byte: `lastEntryArm_commaAboveZero_of_staging` and the colon's two producers read
the reached carry's two maps off it by witness, so all four wrappers here state the
dispatch's result rather than asking their caller for the maps.  The producers' remaining
premises are the document's class and the depth, which is what the wrapper has.
-/

/-- **`[,`/`{,` reaches the comma's arm above depth zero.**  The opener is entry zero;
the reached head is at entry one and depth one.  The arm's stack bytes are the carry's,
which `lastEntryArm_commaAboveZero_of_staging` reads by witness, and the dispatch is the
real `LastEntryArm.dispatch` at the last entry. -/
theorem commaAboveZero_last_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G} {c : UInt8}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterLastDocument G c 44)
    (hc : c = 91 ∨ c = 123)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      WalkDispatchResult (stage2Calls stage2SubCalls) G C' s' := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, h8⟩ :=
    depthOne_last_reachable hargs hnext h hc hrd hpreV r hcall hret
  refine ⟨C', s', hInv', hblock', hsp1, hk1, ?_⟩
  have hnot : ¬ (C'.k + 1 < G.nep) := by rw [hk1, h.count]; omega
  exact walkDispatch_at_commaAboveZero_last_of_staging hInv' hblock' hnot
    (hclass_of_reg8 hInv' h8) (by rw [hsp1]; decide)

/-- **`[:`/`{:` reaches the colon's arm above depth zero.**  The class is the document's
own second byte, and the arm reads the reached carry's two stack bytes itself
(`lastEntryArm_colonAboveZero_of_staging`), so the theorem states the dispatch's result
rather than asking its caller for the maps. -/
theorem colonAboveZero_last_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G} {c : UInt8}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterLastDocument G c 58)
    (hc : c = 91 ∨ c = 123)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      WalkDispatchResult (stage2Calls stage2SubCalls) G C' s' := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, h8⟩ :=
    depthOne_last_reachable hargs hnext h hc hrd hpreV r hcall hret
  refine ⟨C', s', hInv', hblock', hsp1, hk1, ?_⟩
  have hnot : ¬ (C'.k + 1 < G.nep) := by rw [hk1, h.count]; omega
  exact walkDispatch_at_colonAboveZero_last_of_staging hInv' hblock' hnot
    (hclass_of_reg8 hInv' h8) (by rw [hsp1]; decide)

/-- **`[,0` reaches the comma's arm above depth zero on the continuing head.**  The two
stack bytes are the carry's, which `hcontArm_commaAboveZero_of_staging` reads by witness at
the reached head, and the class is the document's: `d = 44` is the arm's byte, so the
regression supplies the document and the opener's call and nothing about the state. -/
theorem commaAboveZero_cont_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G} {c e : UInt8}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G c 44 e)
    (hc : c = 91 ∨ c = 123)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      WalkDispatchResult (stage2Calls stage2SubCalls) G C' s' := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, hk, _h8⟩ :=
    depthOne_cont_reachable hargs hnext h hc hrd hpreV r hcall hret
  refine ⟨C', s', hInv', hblock', hsp1, hk1, ?_⟩
  have hclass : evalICmp .eq (hlastByte G C') (BitVec.ofNat 8 44) = 1 := by
    simp only [hlastByte, hk1, h.entryByte_one, show ((44 : UInt8)).toNat = 44 from rfl]
    exact walkEvalICmp_eq_self _
  exact walkDispatch_at_commaAboveZero_of_staging hInv' hblock' hk hclass
    (by rw [hsp1]; decide)

/-- **`[:0` reaches the colon's arm above depth zero on the continuing head.** -/
theorem colonAboveZero_cont_at_document {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G} {c e : UInt8}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : DelimiterContDocument G c 58 e)
    (hc : c = 91 ∨ c = 123)
    (hrd : readBytes (openerHead G S args next).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst]
      (openerHead G S args next).mem (openerHead G S args next).next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = 1 ∧ C'.k = 1 ∧
      WalkDispatchResult (stage2Calls stage2SubCalls) G C' s' := by
  obtain ⟨C', s', hInv', hblock', hsp1, hk1, hk, h8⟩ :=
    depthOne_cont_reachable hargs hnext h hc hrd hpreV r hcall hret
  refine ⟨C', s', hInv', hblock', hsp1, hk1, ?_⟩
  exact walkDispatch_at_colonAboveZero_of_staging hInv' hblock' hk
    (hclass_of_reg8 hInv' h8) (by rw [hsp1]; decide)

/-! ### The negative control

The depth-zero documents `,` and `:` carry the arms' bytes but not their depth.  The
byte conjunct is the affirmative control for the detector the absence is claimed with:
the same read finds `44` and `58` there. -/

/-- **The document `,` carries the comma's byte but the seed's depth is zero**, so the
above-zero arm's `C.sp ≠ 0` premise is refuted there. -/
theorem depthZero_no_commaAbove {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (44 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)) ∧
      ¬ ((walkSeed G S).sp ≠ 0) := by
  refine ⟨?_, ?_⟩
  · have hreg := seed_reg8 G S s h hInv
    have htoNat : ((44 : UInt8)).toNat = 44 := by decide
    rw [htoNat] at hreg
    simpa only [evalOperand] using hreg
  · simp [walkSeed]

/-- **The document `:` carries the colon's byte but the seed's depth is zero**, so the
above-zero arm's `C.sp ≠ 0` premise is refuted there. -/
theorem depthZero_no_colonAbove {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (58 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)) ∧
      ¬ ((walkSeed G S).sp ≠ 0) := by
  refine ⟨?_, ?_⟩
  · have hreg := seed_reg8 G S s h hInv
    have htoNat : ((58 : UInt8)).toNat = 58 := by decide
    rw [htoNat] at hreg
    simpa only [evalOperand] using hreg
  · simp [walkSeed]

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.depthOne_last_reachable
#print axioms LeanLLVM.Refinement.WalkScope.depthOne_cont_reachable
#print axioms LeanLLVM.Refinement.WalkScope.commaAboveZero_last_at_document
#print axioms LeanLLVM.Refinement.WalkScope.colonAboveZero_last_at_document
#print axioms LeanLLVM.Refinement.WalkScope.commaAboveZero_cont_at_document
#print axioms LeanLLVM.Refinement.WalkScope.colonAboveZero_cont_at_document
#print axioms LeanLLVM.Refinement.WalkScope.depthZero_no_commaAbove
#print axioms LeanLLVM.Refinement.WalkScope.depthZero_no_colonAbove

end WalkScope
end LeanLLVM.Refinement
