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

## The cap's arm, at the deep document

`HcontArm.openAtCap`/`LastEntryArm.openAtCap` are `[` and `{` at the stacks' staged extent,
and the input that puts a head there is the opener repeated: entry `k` sits at depth `k`.
`DeepNestDocument` is that staged document (`[`×`m` with `m ≥ 521`, lanes `0 … m - 1`), and
`openAtCap_last_at_deep_document`/`openAtCap_cont_at_deep_document` are the arm at entry
`520`, at the two levels the `521`- and `522`-entry documents give.

**What these state exactly.**  The arm covers *every* invariant state with `C.sp = 520` —
that is the whole of totality, because the census asks for an arm at each state the
invariant admits, and this premise is that state's own depth.  The staged document shows
the *bytes* exist and puts the arm's byte class on the input (`entryByte_of_lt`).  What is
**not** claimed is document-level reachability: that the walk arrives at a depth-`520`
head from the seeded one.  `C.sp = 520` is a premise here for exactly that reason — the
span is 520 applications of `containerOpen_depth_one_stacks`, each needing the
`s2_value_pos` staging at that intermediate state (the root word's preservation across the
opener's writes, then the call's answer), and neither that iteration nor a `Nat` recursion
over the walk's depth exists anywhere in this tree.  Should depth `520` turn out
unreachable from the seed, the arm is vacuous at its own premise and harmless: never wrong,
only unused.  The sentence is here so that a later reader who needs reachability knows it
is this work — a per-step staging lemma and a depth recursion — and not a missing case of
the census.  Beside them is the depth control: the seed's depth is `0`, so `[0]`'s head
refutes the cap's premise (`seed_not_at_cap`) and takes `.containerOpen` instead.

Each arm is the producer's now (`hcontArm_containerOpen91_of_staging`,
`hcontArm_containerOpen123_of_staging`, `lastEntryArm_containerOpen91_of_staging` and
`lastEntryArm_containerOpen123_of_staging`, `JsonStage2WalkDispatchOpenersOfStaging`), so a
wrapper supplies the document's class test, the `519` boundary at the seed's zero depth and
the call's four premises, and nothing else: the byte, the arm's `hopen` disjunction and the
depth it reads at the route are the producer's.

What the document does not fix is the call's own staging: the root slot's zero word, the
callee's `s2ValuePosPre`, the call's outcome and its answer are the opener's tail
premises, and they are hypotheses here because the invariant carries the root slot's
*presence* and not its value, and names no callee contract.

The negative control is the document `0`: its head byte is `48`, and the arm's own byte
premise — the read that names `91` or `123` — fails there, so the class that `[0]` and
`{"a":1}` take is absent at a scalar's head.  The three byte-class facts are stated with
one detector, so the presence above is a claim about the byte rather than about the
document being one long.  The class the producer takes is the census's `eq` test at the
byte's literal (`bracketHead_class`, `braceHead_class`, `openerDoc_class91`), which is the
form `HcontClass`'s `.openBracket`/`.openBrace` constructors hold.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchArmsDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpenersOfStaging

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

/-- **`[0]`'s head byte is the open bracket's class.**  The producer takes the census's
byte test at `hlastByte`; at the seed the head byte is the document's first, so the test is
the reflexive one at the literal. -/
theorem bracketHead_class {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (h : BracketHeadDocument G) :
    evalICmp .eq (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 91) = 1 := by
  simp only [hlastByte, show (walkSeed G S).k = 0 from rfl, h.entryByte_zero,
    show ((91 : UInt8)).toNat = 91 from rfl]
  exact walkEvalICmp_eq_self _

/-- **`{"a":1}`'s head byte is the open brace's class.** -/
theorem braceHead_class {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (h : BraceHeadDocument G) :
    evalICmp .eq (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 123) = 1 := by
  simp only [hlastByte, show (walkSeed G S).k = 0 from rfl, h.entryByte_zero,
    show ((123 : UInt8)).toNat = 123 from rfl]
  exact walkEvalICmp_eq_self _

/-- **The one-byte document `[`'s head byte is the open bracket's class**, at the seed's
zero index. -/
theorem openerDoc_class91 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (h : OneByteDocument G (91 : UInt8)) :
    evalICmp .eq (hlastByte G (walkSeed G S)) (BitVec.ofNat 8 91) = 1 := by
  simp only [hlastByte, show (walkSeed G S).k = 0 from rfl, h.entryByte_zero,
    show ((91 : UInt8)).toNat = 91 from rfl]
  exact walkEvalICmp_eq_self _

/-- **`[0]`'s head takes the continuing entry's opener arm.**  The producer reads the
byte off the invariant and fills the arm's disjunction from the class, so the wrapper
supplies the class, the seed's depth and the call. -/
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
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  hcontArm_containerOpen91_of_staging (walkSeed G S) s hInv (bracketHead_class G S h)
    (by show (0 : Nat) ≤ 519; omega) hrd hpreV r hcall hret

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
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  hcontArm_containerOpen123_of_staging (walkSeed G S) s hInv (braceHead_class G S h)
    (by show (0 : Nat) ≤ 519; omega) hrd hpreV r hcall hret

/-- **The one-byte document `[` takes the last entry's opener arm.**  The entry stream is
exhausted after the opener, so the level is the last entry's — the same byte class and the
same nine links, at the head that has no successor. -/
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
    LastEntryArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  lastEntryArm_containerOpen91_of_staging (walkSeed G S) s hInv (openerDoc_class91 G S h)
    (by show (0 : Nat) ≤ 519; omega) hrd hpreV r hcall hret

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

/-! ### The deep document, and the cap's arm at its head

The cap arm is `[` and `{` at depth `520`, and the document that reaches such a head is the
opener repeated: entry `k` sits at depth `k`, so entry `520` sits at depth `520` — the
stacks' staged extent.  `DeepNestDocument` is that staged input, and the two theorems below
are the arm at its head, at both levels: `521` entries make the deep head the last entry's,
`522` make it a continuing one.

**What the two theorems do and do not state.**  They cover every invariant head at the
document's depth `520`: the byte is the document's own (derived by `entryByte_of_lt`), the
class test and the depth register are the invariant's, and the result is the real
`.dispatch`'s `refuse`.  `C.sp = 520` at `C.k = 520` is a hypothesis, and *only* that: the
census's totality is "an arm at each state the invariant admits", and that state's depth is
the premise the arm carries, so nothing in the bundle's statement turns on reaching it from
the seed.  Document-level reachability is therefore not claimed — it would be 520
applications of `containerOpen_depth_one_stacks`, each needing the value-position call's
staging at that intermediate state, and neither that iteration nor a `Nat` recursion over
the walk's depth is built in this tree.  If depth `520` were unreachable from the seed the
arm would be vacuous at that premise and harmless — never wrong, only unused.  A later
reader who needs the reachability now knows the work it is: a per-step staging lemma and a
depth recursion. -/

/-- **A document of `m` openers**, all `[`, with `m ≥ 521` entries: the least is the
document `[`×521, whose 521st entry is the opener at the stacks' staged extent.  The entry
stream's lanes are `0 … m - 1`, so entry `k` is the document's `k`th byte. -/
structure DeepNestDocument {m0 : Mem} (G : WalkGeom m0) (m : Nat) : Prop where
  /-- The document is `m` bytes long. -/
  len : G.n = m
  /-- The entry stream holds `m` entries. -/
  count : G.nep = m
  /-- Every byte is the open bracket. -/
  bytes : readBytes m0 G.b m = some (List.replicate m (91 : UInt8))
  /-- The entry stream's lanes are the document's own positions. -/
  lanes : readLanes32 m0 G.ep m = some (List.range m)
  /-- The deep head's index is inside the stream. -/
  ge : 521 ≤ m

/-- The deep document's byte list is the read's. -/
theorem DeepNestDocument.bs {m0 : Mem} {G : WalkGeom m0} {m : Nat}
    (h : DeepNestDocument G m) : G.bs = List.replicate m (91 : UInt8) := by
  have hread : readBytes m0 G.b G.n = some (List.replicate m (91 : UInt8)) := by
    rw [h.len]; exact h.bytes
  exact Option.some.inj (G.doc.symm.trans hread)

/-- The deep document's lanes are the read's. -/
theorem DeepNestDocument.ent {m0 : Mem} {G : WalkGeom m0} {m : Nat}
    (h : DeepNestDocument G m) : G.ent = List.range m := by
  have hread : readLanes32 m0 G.ep G.nep = some (List.range m) := by
    rw [h.count]; exact h.lanes
  exact Option.some.inj (G.entries.symm.trans hread)

/-- The deep document's entry at an index inside the stream is that index. -/
theorem DeepNestDocument.entryPos_of_lt {m0 : Mem} {G : WalkGeom m0} {m : Nat}
    (h : DeepNestDocument G m) {k : Nat} (hk : k < m) : entryPos G k = k := by
  simp only [entryPos, h.ent]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk),
    Option.getD_some, List.getElem_range]

/-- The deep document's byte at an index inside the stream is the opener. -/
theorem DeepNestDocument.entryByte_of_lt {m0 : Mem} {G : WalkGeom m0} {m : Nat}
    (h : DeepNestDocument G m) {k : Nat} (hk : k < m) : entryByte G k = 91 := by
  simp only [entryByte, h.entryPos_of_lt hk, h.bs]
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left hk, Option.getD_some]

/-- **The cap's arm at the deep head, the last entry's level.**  At the document `[`×521
every entry is the opener's byte, so an invariant head at entry `520` with depth `520` is
the state whose push guard is taken: `LastEntryArm.dispatch` at `.openAtCap` returns the
refusal, at the byte the document carries.  The call's staging, the root slot's zero word
and the answer are the arm's premises, as at `.containerOpen`; the depth is the arm's own
premise, so this covers every such head and claims nothing about reaching one from the seed
(the section's note says why, and what that work would be). -/
theorem openAtCap_last_at_deep_document {m0 : Mem} {G : WalkGeom m0}
    (h : DeepNestDocument G 521) {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k = 520) (hsp : C.sp = 520)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  have hnot : ¬ (C.k + 1 < G.nep) := by
    rw [hk, h.count]
    show ¬ (520 + 1 < 521)
    omega
  have hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1 := by
    simp only [hlastByte, hk, h.entryByte_of_lt (k := 520) (by decide)]
    exact walkEvalICmp_eq_self _
  exact LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_openAtCap91_of_staging C s hInv hclass hsp hrd hpreV r hcall hret)

/-- **The cap's arm at the deep head, the continuing level.**  The document `[`×522 puts
an entry after the deep one, so an invariant head at entry `520` with depth `520` is a
continuing head and `HcontArm.dispatch` at `.openAtCap` returns the refusal.  The depth is
the arm's own premise, so the statement covers every such head; reaching one from the seed
is not claimed and is not needed by the census (the section's note). -/
theorem openAtCap_cont_at_deep_document {m0 : Mem} {G : WalkGeom m0}
    (h : DeepNestDocument G 522) {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k = 520) (hsp : C.sp = 520)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  have hkcont : C.k + 1 < G.nep := by
    rw [hk, h.count]
    show 520 + 1 < 522
    omega
  have hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1 := by
    simp only [hlastByte, hk, h.entryByte_of_lt (k := 520) (by decide)]
    exact walkEvalICmp_eq_self _
  exact HcontArm.dispatch hInv hblock hkcont
    (hcontArm_openAtCap91_of_staging C s hInv hclass hsp hrd hpreV r hcall hret)

/-- **The depth control: the shallow opener's document refutes the cap arm's premise.**
`[0`'s head is the seed's, whose depth is `0`, so the byte's arm there is
`.containerOpen`'s — the same two bytes and the other side of the `519` test.  This is the
pair that makes the cap's `C.sp = 520` a claim about the depth rather than about the
byte. -/
theorem seed_not_at_cap {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (walkSeed G S).sp = 0 ∧ ¬ ((walkSeed G S).sp = 520) := by
  refine ⟨rfl, ?_⟩
  simp [walkSeed]

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.BracketHeadDocument.entryByte_zero
#print axioms LeanLLVM.Refinement.WalkScope.BraceHeadDocument.entryByte_zero
#print axioms LeanLLVM.Refinement.WalkScope.bracketHead_opener
#print axioms LeanLLVM.Refinement.WalkScope.braceHead_opener
#print axioms LeanLLVM.Refinement.WalkScope.digitHead_not_opener
#print axioms LeanLLVM.Refinement.WalkScope.bracketHead_class
#print axioms LeanLLVM.Refinement.WalkScope.braceHead_class
#print axioms LeanLLVM.Refinement.WalkScope.openerDoc_class91
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_cont_bracket_arm
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_cont_brace_arm
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_last_arm
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_bracket_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_brace_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.containerOpen_last_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.DeepNestDocument.entryPos_of_lt
#print axioms LeanLLVM.Refinement.WalkScope.DeepNestDocument.entryByte_of_lt
#print axioms LeanLLVM.Refinement.WalkScope.openAtCap_last_at_deep_document
#print axioms LeanLLVM.Refinement.WalkScope.openAtCap_cont_at_deep_document
#print axioms LeanLLVM.Refinement.WalkScope.seed_not_at_cap

end WalkScope
end LeanLLVM.Refinement
