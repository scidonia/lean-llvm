/-
The container openers' domain, at the documents that take them.

`HcontArm.containerOpen` is the continuing head's arm for `[` and `{`, and
`LastEntryArm.containerOpen` is the same class at the last entry.  This module exhibits
each at a **document**, so the classification is inhabited at an input rather than only
shaped:

| arm | document | head byte | entries | level |
|---|---|---|---|---|
| `containerOpen` | `[0]` | `91` | two | continuing |
| `containerOpen` | `{"a":1}` | `123` | five | continuing |
| `containerOpen` | `[` | `91` | one | last entry |

The byte is read off the staged document (`WalkGeom.doc`, `WalkGeom.entries`,
`entryByte`/`entryPos`), and the state is the seed's own handoff
(`walkSeedInvariant_geometry`), so each arm's byte class is a fact about the input.  The
dispatch theorem then runs the arm through the real `.dispatch` — `HcontArm.dispatch` at
the two continuing heads, `LastEntryArm.dispatch` at the last entry — so what is inhabited
is the arm *and* its result.

What the document does not fix is the call's own staging: the root slot's zero word, the
callee's `s2ValuePosPre`, the call's outcome and its answer are the opener's tail
premises, and they are hypotheses here exactly as they are fields of the arm.

The negative control is the document `0`: its head byte is `48`, and the arm's own byte
premise — the read that names `91` or `123` — fails there, so the class that `[0]` and
`{"a":1}` take is absent at a scalar's head.  The three byte-class facts are stated with
one detector, so the presence above is a claim about the byte rather than about the
document being one long.  The arms read the same fact at their byte's literal, because
that is the form the constructor's fields name.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchArmsDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpeners

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

namespace WalkScope

/-! ### The documents, as the staging hands them over -/

/-- **The document `[0]`.**  Two bytes, two entries, and the entry stream's lanes are the
two positions: the opener is the head of a continuing run. -/
structure BracketHeadDocument {m0 : Mem} (G : WalkGeom m0) : Prop where
  /-- The document is two bytes long. -/
  len : G.n = 2
  /-- The entry stream holds two entries. -/
  count : G.nep = 2
  /-- The document's bytes are `[` and `0`. -/
  bytes : readBytes m0 G.b 2 = some [91, 48]
  /-- The entry stream's lanes are the two positions. -/
  lane : readLanes32 m0 G.ep 2 = some [0, 1]

/-- **The document `{"a":1}`.**  Seven bytes, five entries — `{`, the string `"a"`, the
colon, the scalar `1` and the close brace — so the opener heads a continuing run. -/
structure BraceHeadDocument {m0 : Mem} (G : WalkGeom m0) : Prop where
  /-- The document is seven bytes long. -/
  len : G.n = 7
  /-- The entry stream holds five entries. -/
  count : G.nep = 5
  /-- The document's bytes, in order. -/
  bytes : readBytes m0 G.b 7 = some [123, 34, 97, 34, 58, 49, 125]
  /-- The entry stream's lanes are the five positions. -/
  lane : readLanes32 m0 G.ep 5 = some [0, 1, 4, 5, 6]

/-! ### The two documents' bytes and entry streams -/

/-- The document `[0]`'s bytes. -/
theorem BracketHeadDocument.bs {m0 : Mem} {G : WalkGeom m0}
    (h : BracketHeadDocument G) : G.bs = [91, 48] := by
  have hd := G.doc
  rw [h.len, h.bytes] at hd
  exact (Option.some.inj hd).symm

/-- The document `[0]`'s entry stream. -/
theorem BracketHeadDocument.ent {m0 : Mem} {G : WalkGeom m0}
    (h : BracketHeadDocument G) : G.ent = [0, 1] := by
  have he := G.entries
  rw [h.count, h.lane] at he
  exact (Option.some.inj he).symm

/-- The document `[0]`'s first entry is its first byte. -/
theorem BracketHeadDocument.entryPos_zero {m0 : Mem} {G : WalkGeom m0}
    (h : BracketHeadDocument G) : entryPos G 0 = 0 := by
  have hent := h.ent
  simp only [entryPos, hent, List.getD]
  rfl

/-- The document `[0]`'s head byte is `[`. -/
theorem BracketHeadDocument.entryByte_zero {m0 : Mem} {G : WalkGeom m0}
    (h : BracketHeadDocument G) : entryByte G 0 = 91 := by
  have hpos := h.entryPos_zero
  have hbs := h.bs
  simp only [entryByte, hpos, hbs, List.getD]
  rfl

/-- The document `{"a":1}`'s bytes. -/
theorem BraceHeadDocument.bs {m0 : Mem} {G : WalkGeom m0}
    (h : BraceHeadDocument G) : G.bs = [123, 34, 97, 34, 58, 49, 125] := by
  have hd := G.doc
  rw [h.len, h.bytes] at hd
  exact (Option.some.inj hd).symm

/-- The document `{"a":1}`'s entry stream. -/
theorem BraceHeadDocument.ent {m0 : Mem} {G : WalkGeom m0}
    (h : BraceHeadDocument G) : G.ent = [0, 1, 4, 5, 6] := by
  have he := G.entries
  rw [h.count, h.lane] at he
  exact (Option.some.inj he).symm

/-- The document `{"a":1}`'s first entry is its first byte. -/
theorem BraceHeadDocument.entryPos_zero {m0 : Mem} {G : WalkGeom m0}
    (h : BraceHeadDocument G) : entryPos G 0 = 0 := by
  have hent := h.ent
  simp only [entryPos, hent, List.getD]
  rfl

/-- The document `{"a":1}`'s head byte is `{`. -/
theorem BraceHeadDocument.entryByte_zero {m0 : Mem} {G : WalkGeom m0}
    (h : BraceHeadDocument G) : entryByte G 0 = 123 := by
  have hpos := h.entryPos_zero
  have hbs := h.bs
  simp only [entryByte, hpos, hbs, List.getD]
  rfl

/-! ### The seeded head's byte

`WalkIter.reg8` at the seed's zero index: the head's `%8` is the document's first byte. -/

/-- **The seeded head's `%8` is the document's first byte.** -/
theorem seed_head_byte {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State) {c : UInt8}
    (hc : entryByte G 0 = c) (hInv : WalkInv G (walkSeed G S) s) :
    lookupName s.env "%8" = some (.int 8 (BitVec.ofNat 8 c.toNat)) := by
  have hk : (walkSeed G S).k = 0 := rfl
  have hiter := hInv.iter.reg8
  rw [hk, hc] at hiter
  exact hiter

/-! ### The byte's class at the three documents

One detector — the head's `%8` read at either of the two bytes that enter `if.then.i` —
read at each document's head.  The two documents satisfy it; the digit `0` does not, which
is what makes the presence a claim about the byte. -/

/-- **`[0]`'s head byte is an opener**: `%8` is `[`. -/
theorem bracketHead_opener {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : BracketHeadDocument G) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 91)) ∨
      evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 123)) := by
  have hreg := seed_head_byte G S s h.entryByte_zero hInv
  have ht : ((91 : UInt8)).toNat = 91 := by decide
  rw [ht] at hreg
  exact Or.inl hreg

/-- **`{"a":1}`'s head byte is an opener**: `%8` is `{`. -/
theorem braceHead_opener {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : BraceHeadDocument G) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 91)) ∨
      evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 123)) := by
  have hreg := seed_head_byte G S s h.entryByte_zero hInv
  have ht : ((123 : UInt8)).toNat = 123 := by decide
  rw [ht] at hreg
  exact Or.inr hreg

/-- **The scalar `0`'s head byte is not an opener.**  The same detector at the digit
`48`: the head's `%8` is that byte, and it is neither `91` nor `123`, so neither disjunct
can be the read. -/
theorem digitHead_not_opener {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (48 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    ¬ (evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 91)) ∨
        evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 123))) := by
  have hreg0 := seed_reg8 G S s h hInv
  have ht : ((48 : UInt8)).toNat = 48 := by decide
  rw [ht] at hreg0
  rintro (h8 | h8)
  · have hbad : some (Value.int 8 (BitVec.ofNat 8 91)) =
        some (Value.int 8 (BitVec.ofNat 8 48)) := h8.symm.trans hreg0
    exact absurd hbad (by decide)
  · have hbad : some (Value.int 8 (BitVec.ofNat 8 123)) =
        some (Value.int 8 (BitVec.ofNat 8 48)) := h8.symm.trans hreg0
    exact absurd hbad (by decide)

/-! ### The arms at the documents -/

/-- **`[0]`'s head takes the continuing entry's opener arm.**  The byte class is the
document's, the depth is the seed's, and the tail's five links are the arm's own. -/
def containerOpen_cont_bracket_arm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : BracketHeadDocument G) (hInv : WalkInv G (walkSeed G S) s)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s := by
  have hreg := seed_head_byte G S s h.entryByte_zero hInv
  have ht : ((91 : UInt8)).toNat = 91 := by decide
  rw [ht] at hreg
  exact .containerOpen hreg (Or.inl rfl) (by show (0 : Nat) ≤ 519; omega) hrd hpreV r
    hcall hret

/-- **`{"a":1}`'s head takes the continuing entry's opener arm.** -/
def containerOpen_cont_brace_arm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : BraceHeadDocument G) (hInv : WalkInv G (walkSeed G S) s)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s := by
  have hreg := seed_head_byte G S s h.entryByte_zero hInv
  have ht : ((123 : UInt8)).toNat = 123 := by decide
  rw [ht] at hreg
  exact .containerOpen hreg (Or.inr rfl) (by show (0 : Nat) ≤ 519; omega) hrd hpreV r
    hcall hret

/-- **The one-byte document `[` takes the last entry's opener arm.**  The entry stream
is exhausted after the opener, so the level is the last entry's — the same byte class and
the same nine links, at the head that has no successor. -/
def containerOpen_last_arm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (91 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 (BitVec.ofNat 32 0),
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    LastEntryArm (stage2Calls stage2SubCalls) G (walkSeed G S) s := by
  have hreg := seed_reg8 G S s h hInv
  have ht : ((91 : UInt8).toNat = 91) := by decide
  rw [ht] at hreg
  exact .containerOpen hreg (Or.inl rfl) (by show (0 : Nat) ≤ 519; omega) hrd hpreV r
    hcall hret

/-! ### The dispatch, through the real `.dispatch` -/

/-- The state the entry run hands the loop, at the documents' staging. -/
abbrev openerHead {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (args : List Value)
    (next : Nat) : State :=
  walkSeedFinalState G S
    (EntryState stage2Body
      (stage2Args args S.d S.c S.ctype S.cst S.tok S.s S.z S.e) m0 next)
    (entryPos G 0) (entryByte G 0)

/-- **The dispatch at `[0]`.**  `HcontArm.dispatch` at the seeded head: the continuing
guard is the document's `0 + 1 < 2`, and the result is the merge the opener's nine links
reach. -/
theorem containerOpen_bracket_dispatch {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : BracketHeadDocument G)
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
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hk : (walkSeed G S).k + 1 < G.nep := by
    rw [h.count]
    show 0 + 1 < 2
    omega
  exact HcontArm.dispatch (seededInv (S := S) hargs hnext hn) (walkSeed_block G S) hk
    (containerOpen_cont_bracket_arm G S _ h (seededInv (S := S) hargs hnext hn)
      hrd hpreV r hcall hret)

/-- **The dispatch at `{"a":1}`.**  The same arm at the brace's route through
`NodeBlock17` and `LeafBlock13`, with the continuing guard the five entries give. -/
theorem containerOpen_brace_dispatch {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : BraceHeadDocument G)
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
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hk : (walkSeed G S).k + 1 < G.nep := by
    rw [h.count]
    show 0 + 1 < 5
    omega
  exact HcontArm.dispatch (seededInv (S := S) hargs hnext hn) (walkSeed_block G S) hk
    (containerOpen_cont_brace_arm G S _ h (seededInv (S := S) hargs hnext hn)
      hrd hpreV r hcall hret)

/-- **The dispatch at `[`.**  `LastEntryArm.dispatch` at the seeded head: the entry
stream is exhausted (`¬ (0 + 1 < 1)`), and the arm's nine links still reach the merge. -/
theorem containerOpen_last_dispatch {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : OneByteDocument G (91 : UInt8))
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
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hnot : ¬ ((walkSeed G S).k + 1 < G.nep) := by
    rw [h.count]
    show ¬ (0 + 1 < 1)
    omega
  exact LastEntryArm.dispatch (seededInv (S := S) hargs hnext hn) (walkSeed_block G S) hnot
    (containerOpen_last_arm G S _ h (seededInv (S := S) hargs hnext hn)
      hrd hpreV r hcall hret)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.BracketHeadDocument.entryByte_zero
#print axioms LeanLLVM.Refinement.WalkScope.BraceHeadDocument.entryByte_zero
#print axioms LeanLLVM.Refinement.WalkScope.bracketHead_opener
#print axioms LeanLLVM.Refinement.WalkScope.braceHead_opener
#print axioms LeanLLVM.Refinement.WalkScope.digitHead_not_opener
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_cont_bracket_arm
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_cont_brace_arm
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_last_arm
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_bracket_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_brace_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_last_dispatch

end WalkScope
end LeanLLVM.Refinement
