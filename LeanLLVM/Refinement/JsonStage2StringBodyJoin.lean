import LeanLLVM.Refinement.JsonStage2StringBodyArms

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The callee arms' join

Both callee arms end with two eight-byte writes whose *order* differs from the
model's, and the join needs exactly two facts:

* **the slot write absorbs the arm's clear** — proved below
  (`s2StringBodySlot_absorb`): the body stores `0` at its slot before the call and
  the callee stores the arm's word there, so the second write is the memory;
* **two in-place writes over disjoint regions commute** — proved below as
  `writeBytes_comm_of_present`, at the shape the join uses:

      readBytes A a X.length ≠ none → readBytes A b Y.length ≠ none →
      (a + X.length ≤ b ∨ b + Y.length ≤ a) →
      writeBytes (writeBytes A a X) b Y = writeBytes (writeBytes A b Y) a X

  It is not `writeBytes_absent_comm_witness`'s claim (that one is false, and the
  witness is why): two *absent* regions are ordered by the write sequence, which is
  the one thing that distinguishes the two sides.  **One region present is enough**,
  and those forms are `writeBytes_comm_of_present_left` (the first region's presence)
  and `writeBytes_comm_of_present_right` (the second's): the present region's write
  is a replacement in place, which leaves the address sequence alone, so the other
  write meets the same addresses on both sides and appends the same cells in the same
  order.  Presence is stated existentially — the bytes *written* and the bytes
  *present* are different lists of the same length — and it survives the inductive
  step's byte write by `readBytes_writeByte_above`/`_below`, one for each side of the
  region.  The joins below take the one-sided forms wherever the moved write is the
  slot's: a moved write needs the region it crosses into, not its own, and the
  slot's own presence is not something the staging states.

**A write-order join's cost is the distance between the model's write position and
the body's, measured in intervening regions — every unit of distance is one
commutation.**  The body writes the slot early (the callee does it, before `outn`'s
word), the model writes it last, so the decoded arm is three moves (absorb the
arm's clear, then commute the slot past `outn` and `outn` past `xj`/`dst`) and the
refused arm is one more.  A reader who knows the distance will not expect one move.
The first of those moves needs a lemma this section does not yet have —
`writeBytes_absorb_one`: a write to a region that is **present**, followed by
intervening writes disjoint from it, is absorbed by a later write to that region.
Its proof is an induction over the memory showing that an in-place write changes no
cell's *position*, which is what the two preservations above supply one byte at a
time.

**The absorption is an artefact of the direction, and moving the *clear* rightwards
is what makes it cheap.**  Two directions reach the adjacency, and they do not cost
the same, because the target's slot write comes **last**:

* moving the **clear** rightwards to meet the slot costs **four** moves — past
  `dst`, past `xj`, the absorption itself, then the slot past `outn`;
* moving the **slot** leftwards towards the clear costs **seven** — the same three
  crossings to reach it, the absorption, and then three back, because the model's
  memory has the slot last and it has to return.

**The absorption's route, and the canonical form that does not work.**  The first
idea was to make the shape definitional — a map `memUpd A a n bs` re-valuing the
region's cells, with `writeBytes A a bs = memUpd A a bs.length bs` proved once.  It
fails, and the witness is `writeByte_not_map_of_duplicate`: **`writeByte` replaces the
*first* cell at an address, and a map replaces every cell there**, so with a
duplicated address the two disagree.  The equivalence therefore needs
duplicate-freedom *as well as* presence, and duplicate-freedom is exactly the staging
clause the join may not add — so the canonical route is closed here, and it is closed
by the same wall `readByte_not_determined_by_reads` shows: the memory's list order
carries information its bytes do not.

**The absorption itself survives duplicates**, because both of its sides replace the
*same* first occurrences — which is why the direct induction over the memory is the
route, not a map lemma.  It needs the presence of the regions its crossings move
**into** — `dst` and `xj` — because an absent region is *appended*, and the two sides
of a crossing then append in different orders, so the lists differ while every read
agrees.  The erased region's own presence is not among them: its write is overwritten
by the last write to the same place before any reader observes the memory, so whether
it appended is invisible in the surviving list.  That is the same wall for the third
time, now quantitative — presence is what makes the crossed write a replacement in
place, and the absorption needs it on the two regions it crosses into.  The join has
it: `dst` and `xj` are staged (the writing caller's buffers), and the third region,
`ei`, is the caller's own stack slot, whose presence the staging does not state.

The lemma is proved above (`writeBytes_absorb_one`), and **it is not a walk**: the
earlier clear crosses `dst`, then `xj`, and the two writes to the erased region end
up adjacent, where `writeBytes_writeBytes_same` erases the first.  Two commutations
and one absorption — which is the four-move count, vindicated: the retraction two
rounds ago (that commutations cannot remove a write) was wrong because adjacency plus
`writeBytes_writeBytes_same` *is* the removal.

Its hypotheses are five: **two presences** (the two regions the crossings move into,
not the erased one) and **three pairwise disjointnesses** (one per pair).  Each
crossing spends a presence and a disjointness, which is why the conclusion's one
region needed five facts in the statement.

**The refused arm's chain, written out.**  Its body writes six times:
`clear(ei)`, the callee's `offset(ei)`, `scan(xj)`, then the record's three words at
`e`, `e + 8`, `e + 16`.  The model writes five: the record's three, `scan(xj)`, then
the slot at `ei`.  So the join is

* the clear absorbed by the callee's own `ei` write — they are **adjacent**, so
  `writeBytes_writeBytes_same` does it (`s2StringBodySlot_absorb` outside a type
  argument);
* `scan(xj)` moved right past the record's three words — 3 crossings;
* the `ei` write moved right to the end — 4 crossings;

**seven commutations, and ten pairwise disjointnesses** (five regions: `ei`, `xj`,
`e`, `e + 8`, `e + 16`), the last three pairs being the record's own words, which are
disjoint from each other (`4`, `8`, `8` bytes at `e`, `e + 8`, `e + 16`).  The
decoded arm's three crossings are the same two moves at a shorter distance: **the
model's write order charges for the record's three words, and the decoded arm never
writes a record at all.**  That is the two arms' difference, measured.

**Neither count is reachable with commutations alone, and the typecheck says why.**
The statement typechecks with its conclusion as a hypothesis (the produced-form
check: if `example (…) (h : <the equality>) : <the equality> := h` elaborates, the
terms are the ones the callee produces), and the same check shows the gap: the
source order is
`clear, dst, xj, slot, outn` and the target is `dst, xj, outn, slot`.  Commuting a
write never *removes* one, so the `clear` must be **erased**, not moved — and the
only eraser is a write to the same region, which the target's `slot` is, but only
after `outn`, i.e. not adjacent to the `clear` in any order the commutations can
produce while keeping the target's order.  So the absorption is necessary after all,
and it is `writeBytes_absorb_one` — the lemma this section previously concluded was
an artefact.  **Two counts and one retraction are recorded here on purpose**: the
leftward count (three) reached the adjacency but not the target; the rightward
count (four) reached neither without erasing; and the erasure is the induction.

What the typecheck *did* establish is worth keeping: the source term is the body's
own, the target term is the model's plus the slot at `next = ei`, and the two differ
exactly by the clear's erasure — which is the whole of what the induction must show.

For the record, the two facts that direction would have needed:

* **position preservation** — a write over a *present* region changes values only,
  so every cell keeps its position and the memory's *shape* is unchanged.  That is
  what rules out `b`'s append moving when the `a`-region is rewritten first, the
  hypothesis the commutation route could not supply;
* **region extensionality** — two memories that agree at every address outside a
  region, and each hold that region present, agree after being rewritten there with
  the same bytes.  That is what lets a final in-place write erase an earlier one
  whose values differ — **but it is false as stated**, and
  `readByte_not_determined_by_reads` is the witness: a duplicated address answers
  every read as the memory without it does, so two different lists have the same
  byte everywhere.  The true statement needs **duplicate-freedom** on the memory's
  address sequence, which no module in this cone supplies; so the absorption is
  either proved by a direct induction over the memory with two region cursors (no
  extensionality), or the staging gains a `Nodup` clause.  That choice is the
  closing's, not the lemma's, and it is the last shape question the row has.

With both, `writeBytes_absorb_one` is an induction whose region extent is
*constant* (both `ei` writes are eight bytes, so no length negotiation enters) and
whose outside-agreement is carried by `readBytes_writeByte_above`/`_below`.

**And the method, three times over**: a lemma written for one purpose has twice
become the next lemma's prerequisite — `readBytes_writeByte_below` was written for
the commutation, `_above` as its dual, and the absorption needs both, as the
instrument that carries a presence past a write on either side.  That is what a
vocabulary converging on the right side conditions looks like, and the practical
reason to state a fact at the weakest side condition its *use* needs rather than at
the strongest its proof can reach.  -/

/-- **The slot write absorbs the arm's clear.**  The body writes `0` at the slot
before the call and the callee writes the arm's word there; the second write is the
memory, because the first one made the region present and both are eight bytes. -/
theorem s2StringBodySlot_absorb (a : Mem) (ei : Nat) (w : BitVec 64) :
    writeBytes (writeBytes a ei (natToBytes (0#64).toNat 8)) ei
        (natToBytes w.toNat 8) =
      writeBytes a ei (natToBytes w.toNat 8) :=
  writeBytes_writeBytes_same a ei (natToBytes (0#64).toNat 8) (natToBytes w.toNat 8)
    (by simp [natToBytes_length])


/-
**The instruments, and where each was learned.**  This module's memory and control
work produced one instrument per failure, and they are recorded here because each is
cheaper than the failure it came from:

* **price a path by its heavy states × the values its terminal spells**, paid where the
  terminal is proved — a lemma's proof is not re-elaborated at its call site;
* **count a stated obligation's lemmas before writing them** — a route that fails at a
  hypothesis is naming the theorem's subject;
* **a missing lemma can be a direction** — before proving "X absorbs Y across Z", ask
  which of the two writes is being moved;
* **a commutation count fits permutations; an erasure is not one** — compare multisets
  of writes, and count crossings in the shorter direction (a round trip is one of the
  ways a count can be wrong);
* **a hypothesis a lemma needs is the union over every crossing it makes** — the
  conclusion names one region, the proof crosses three;
* **state the statement alone first**, in the file and options the proof will live in
  (`lean <module>`, not `/tmp`: scratch leaves `autoImplicit` on);
* **a map is not a write** — a canonical form must agree with the operation, on lengths
  (presence) *and* multiplicity (duplicates);
* **a lemma and its dual are one statement with constants flipped** — write the dual as
  a substitution, check it, and the proof mirrors;
* **name the term**: a statement whose state has many cells, or whose memory term is
  deep, is a `whnf` liability — and **the depth can be in a hypothesis's type**, not
  only in the goal.  Before composing, print the terminal's conclusion and ask how deep
  its memory term is; deeper than two `writeBytes` and it needs a named-outcome variant
  *before* any composition starts;
* **a chain is not a proof script** — the count and the order are what a reader needs,
  but each rewrite's arguments are the state that move leaves, so a crossing costs about
  two instantiations and the goal, not the chain, says at what;
* **a fact the caller has is not a fact the lemma has** — state the hypothesis; and
* **the check must be the one the artifact's context performs** — a build's exit status
  must gate the commit, not decorate it, and a check run under other options has not
  been run.
-/

/-- **The decoded arm's facts, bundled.**  The third position of "name the term": the
hypothesis *list*.  A statement that mentions one argument of this type does not make the
elaborator spell sixteen laminate-bearing propositions. -/
structure s2StringBodyDecodedFacts (e : State) (p dst ei outn xp xj : Nat)
    (len sub conv nxp : BitVec 64) (extra : Mem) (nx : Nat) (call : BitVec 64)
    (outj out : List UInt8) (j1 k : Nat) : Prop where
  hpc : e.pc = "land.lhs.true"
  hsub : lookupName e.env "%sub.ptr.sub" = some (.int 64 sub)
  hlen : lookupName e.env "%len" = some (.int 64 len)
  hconv : lookupName e.env "%conv" = some (.int 64 conv)
  hbit7 : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1
  hp : lookupName e.env "%p" = some (.ptr p)
  hdst : lookupName e.env "%dst" = some (.ptr dst)
  hei : lookupName e.env "%ei" = some (.ptr ei)
  hxp : lookupName e.env "%xp" = some (.ptr xp)
  hxj : lookupName e.env "%xj" = some (.ptr xj)
  hnxp : lookupName e.env "%nxp" = some (.int 64 nxp)
  hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
    [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
     .int 64 sub] (writeBytes e.mem ei (natToBytes (0#64).toNat 8)) e.next =
    some { ret := .int 64 call, mem := extra, next := nx }
  hbit9 : evalICmp .eq call 0xffffffffffffffff#64 = 0#1
  houtn : lookupName e.env "%outn" = some (.ptr outn)
  hextra : extra = s2StringBodyExpandMem e.mem ei dst xj out outj
  hcall : call = BitVec.ofNat 64 out.length
  hlenOut : out.length < 2 ^ 64
  hdst_p : readBytes e.mem dst out.length ≠ none
  hxj_p : readBytes e.mem xj 8 ≠ none
  houtn_p : readBytes e.mem outn 8 ≠ none
  hd_ei : ei + 8 ≤ dst ∨ dst + out.length ≤ ei
  hx_ei : ei + 8 ≤ xj ∨ xj + 8 ≤ ei
  hd_xj : dst + out.length ≤ xj ∨ xj + 8 ≤ dst
  ho_ei : ei + 8 ≤ outn ∨ outn + 8 ≤ ei
  ho_d : outn + 8 ≤ dst ∨ dst + out.length ≤ outn
  ho_x : outn + 8 ≤ xj ∨ xj + 8 ≤ outn

/-- The inside test's environment, named: the two cells `land.lhs.true` builds over the
exit's. -/
def s2StringBodyLhsEnv (e : State) (sub len conv : BitVec 64) : Env :=
  ("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
    ("%add", .int 64 (sub + len)) :: e.env

/-- The `if.end14` entry state, named: the inside test's environment over the expander's
output.  Rule four at the state — a step whose conclusion names this is narrow again. -/
def s2StringBodyIfEnd15State (e : State) (sub len conv : BitVec 64) (call : BitVec 64)
    (extra : Mem) (nx : Nat) : State :=
  stateAt (s2StringBodyIfEndEnv (s2StringBodyLhsEnv e sub len conv) call)
    { e with mem := extra, next := nx, pc := "if.end15", pre := some "if.end" }

/-- The `cleanup` entry state after the length's write, named. -/
def s2StringBodyCleanupState (e : State) (sub len conv : BitVec 64) (call : BitVec 64)
    (extra : Mem) (nx outn : Nat) : State :=
  stateAt (s2StringBodyIfEndEnv (s2StringBodyLhsEnv e sub len conv) call)
    ({ e with mem := writeBytes extra outn (natToBytes call.toNat 8), next := nx, pc := "cleanup47", pre := some "if.end15" })

/-! ### The contract

The body's whole run: the entry's test, the scan for the body's first position, the
inside test's two readings of one comparison, and the expander's answer.  The plan
below is the one the parts were written for —

* the entry's `%cmp3` splits into the scan (the cursor below the count) and the
  short arm straight to `if.then` (the cursor at or past it);
* the scan is the prefix-carrying instance, so its exit's counter *is* the model's
  `j1`;
* the inside test's `%cmp7` is the window's emptiness (`%cmp1`'s reading at `j1`),
  and `%cmp9` is the expander's word;
* `Post` is by cases on the returned form, and the memory equality is the arm's
  join — no join at all on the body-itself form, the absorbed cursor write and the
  decoded join on `2`, the record's reconciliation and the refused join on `0`.

Every join is applied at the staging's pairwise separated regions, and each takes
the presence of the ones its crossings move into — `dst`, `xj`, `outn` and the
record's `e`, which is why `s2StringBodyPre` states those four.  The fifth region,
the body's own slot, is crossed against and never replaced in: its own presence buys
nothing, and the staging does not state it. -/

/-- A word the staging reads is below `256 ^ w`, so an eight-byte word is below
`2 ^ 64` — the bound the entry's `ptrtoint` and the scan's `i64` arithmetic need. -/
theorem stage2ReadWord_lt {mem : Mem} {a w v : Nat}
    (h : stage2ReadWord mem a w = some v) : v < 256 ^ w := by
  unfold stage2ReadWord at h
  cases hr : readBytes mem a w with
  | none => rw [hr] at h; cases h
  | some bs =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hb := bytesToNat_lt bs
      rwa [readBytes_length_some hr] at hb

/-- The eight-byte case: `256 ^ 8` is `2 ^ 64`. -/
theorem stage2ReadWord_lt_64 {mem : Mem} {a v : Nat}
    (h : stage2ReadWord mem a 8 = some v) : v < 2 ^ 64 := by
  have h' := stage2ReadWord_lt h
  have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  omega

/-- **The contract's conclusion from a state**: the run completes at the state's own
fuel and answers the model's form with the contract's post and footprint.  The
scan's continuation is stated at this shape so each exit arm is proved at its own
fuel and lifted to the contract's budget. -/
def s2StringBodyConcludes (args : List Value) (mem : Mem) (next : Nat) (k : Nat)
    (e : State) : Prop :=
  ∃ o : CallOutcome,
    runFuel s2StringBodyCalls k s2StringBodyBody e = some (.ret (some o.ret) o.mem) ∧
    s2StringBodyPost args mem next o ∧
    UnchangedOutside mem o.mem (s2StringBodyFoot args mem next)

/-- **The body-itself form's post**: the model answered form `1` with the empty slot,
and the two memories are the same because the cursor write is the staging's own —
`hself` is that write being a no-op. -/
theorem s2StringBodyPost_of_bodyItself {mem : Mem} {next c p dst outn xp xj j1 : Nat}
    {len nxp : BitVec 64}
    (h : stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat =
      some (writeBytes (writeBytes mem xj (wordBytes 8 j1)) outn
        (wordBytes 8 len.toNat), 1, []))
    (hself : writeBytes mem xj (wordBytes 8 j1) = mem) :
    s2StringBodyPost
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next
      ⟨.int 32 (BitVec.ofNat 32 1),
        writeBytes mem outn (natToBytes len.toNat 8), next + 8⟩ := by
  refine ⟨writeBytes (writeBytes mem xj (wordBytes 8 j1)) outn
    (wordBytes 8 len.toNat), 1, [], h, rfl, ?_, rfl⟩
  simp only [hself]
  rfl

/-- **The model's body-itself answer at a scan exit**: `j1` is the counter and the
window there is empty, so the two forms' first branch is taken — the cursor word
and the extent's word, form `1`, empty slot. -/
theorem s2StringBodyModel_bodyItself {mem : Mem} {c p dst outn xp xj j1 : Nat}
    {len nxp : BitVec 64} {base j0 : Nat} {ps : List Nat}
    (hbase : stage2ReadWord mem c 8 = some base)
    (hj0 : stage2ReadWord mem xj 8 = some j0)
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hnxp0 : nxp.toNat ≠ 0)
    (hj1 : j1 = j0 + ((ps.drop j0).takeWhile (fun q => decide (q < p - base))).length)
    (hempty : ((ps.drop j1).takeWhile
      (fun q => decide (q < p - base + len.toNat))).isEmpty = true) :
    stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat =
      some (writeBytes (writeBytes mem xj (wordBytes 8 j1)) outn
        (wordBytes 8 len.toNat), 1, []) := by
  simp only [stage2StringBody, hbase, hj0, hps]
  rw [if_neg hnxp0, ← hj1]
  rw [if_pos hempty]

/-- **The model's decoded answer at a scan exit**: the window is non-empty, the
body's bytes are the staging's read, and the decoder's result is the callee's —
the decoded prefix at `dst`, the advanced cursor, the decoded length at `outn`,
form `2` and the length as the slot's word. -/
theorem s2StringBodyModel_decoded {mem : Mem} {c p dst outn xp xj j1 k : Nat}
    {len nxp : BitVec 64} {base j0 : Nat} {ps : List Nat} {body out : List UInt8}
    (hbase : stage2ReadWord mem c 8 = some base)
    (hj0 : stage2ReadWord mem xj 8 = some j0)
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (hnxp0 : nxp.toNat ≠ 0)
    (hj1 : j1 = j0 + ((ps.drop j0).takeWhile (fun q => decide (q < p - base))).length)
    (hne : ((ps.drop j1).takeWhile
      (fun q => decide (q < p - base + len.toNat))).isEmpty = false)
    (hdec : escapeDecodeGo body 0 0
      (((ps.drop j1).takeWhile (fun q => decide (q < p - base + len.toNat))).map
        (fun q => q - (p - base))) [] = .decoded out k) :
    stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat =
      some (writeBytes
        (writeBytes (writeBytes mem dst out) xj (wordBytes 8 (j1 + k))) outn
        (wordBytes 8 out.length), 2, wordBytes 8 out.length) := by
  simp only [stage2StringBody, hbase, hj0, hps]
  rw [if_neg hnxp0, ← hj1]
  rw [if_neg (by simpa using hne)]
  simp only [hbody, hdec]

/-- **The model's refusing answer at a scan exit**: the decoder's refusal, the
body-relative offset written at the error record, form `0` and the offset as the
slot's word. -/
theorem s2StringBodyModel_refused {mem : Mem} {c p dst outn xp xj j1 k off e' : Nat}
    {len nxp : BitVec 64} {base j0 : Nat} {ps : List Nat} {body : List UInt8}
    (hbase : stage2ReadWord mem c 8 = some base)
    (hj0 : stage2ReadWord mem xj 8 = some j0)
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (he : stage2ReadWord mem (c + 1112) 8 = some e')
    (hnxp0 : nxp.toNat ≠ 0)
    (hj1 : j1 = j0 + ((ps.drop j0).takeWhile (fun q => decide (q < p - base))).length)
    (hne : ((ps.drop j1).takeWhile
      (fun q => decide (q < p - base + len.toNat))).isEmpty = false)
    (hr : escapeDecodeGo body 0 0
      (((ps.drop j1).takeWhile (fun q => decide (q < p - base + len.toNat))).map
        (fun q => q - (p - base))) [] = .refused off k) :
    stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat =
      some (writeBytes (stage2ErrSetMsg mem e' (p - base + off) 0) xj
        (wordBytes 8 (j1 + k)), 0, wordBytes 8 off) := by
  simp only [stage2StringBody, hbase, hj0, hps]
  rw [if_neg hnxp0, ← hj1]
  rw [if_neg (by simpa using hne)]
  simp only [hbody, hr, he]

/-- A read framed past one written region, in the orientation `RegionsApart` states. -/
theorem readBytes_writeBytes_apart {m : Mem} {a n start : Nat} {ws : List UInt8}
    (hsep : RegionsApart start ws.length a n) :
    readBytes (writeBytes m start ws) a n = readBytes m a n := by
  rcases hsep with h | h
  · rw [s2StringBodyReadBytes_above m ws n a start h]
  · rw [readBytes_writeBytes_below m ws n a start h]

/-- **The callee's three reads at the call's memory**: the cursor word, the position
list and the document's bytes, each framed past the slot's write and past the scan's.
The expander's clause reads exactly these, so both of its answers rebuild them here. -/
theorem s2StringBodyCallee_reads {mem xmem : Mem} {p xp xj : Nat} {len nxp : BitVec 64}
    {c1 ei : Nat} {ps : List Nat} {body : List UInt8}
    (hmem : xmem = writeBytes mem xj (wordBytes 8 c1))
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (hc1 : c1 < 2 ^ 64)
    (hxjp : RegionsApart xj 8 p len.toNat)
    (heip : RegionsApart ei 8 p len.toNat)
    (heixj : RegionsApart ei 8 xj 8)
    (heilan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ ei ∨ ei + 8 ≤ xp + 4 * j)
    (hjlan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * j) :
    stage2ReadWord (writeBytes xmem ei (natToBytes (0#64).toNat 8)) xj 8 = some c1 ∧
    readLanes32 (writeBytes xmem ei (natToBytes (0#64).toNat 8)) xp nxp.toNat = some ps ∧
    readBytes (writeBytes xmem ei (natToBytes (0#64).toNat 8)) p len.toNat = some body := by
  have hxjX : readBytes xmem xj 8 = some (wordBytes 8 c1) := by
    rw [hmem]
    exact readBytes_wordBytes_same
  have hxjC : readBytes (writeBytes xmem ei (natToBytes (0#64).toNat 8)) xj 8
      = some (wordBytes 8 c1) := by
    rw [readBytes_writeBytes_apart (ws := natToBytes (0#64).toNat 8)
      (by rw [natToBytes_length]; exact heixj)]
    exact hxjX
  have hlanX : readLanes32 xmem xp nxp.toNat = some ps := by
    rw [hmem]
    rw [readLanes32_writeBytes_away (start := xj) (ws := wordBytes 8 c1)
      (fun j hj => by
        have := hjlan j hj
        simpa [wordBytes, natToBytes_length] using this)]
    exact hps
  have hlanC : readLanes32 (writeBytes xmem ei (natToBytes (0#64).toNat 8)) xp
      nxp.toNat = some ps := by
    rw [readLanes32_writeBytes_away (start := ei) (ws := natToBytes (0#64).toNat 8)
      (fun j hj => by
        have := heilan j hj
        simpa [natToBytes_length] using this)]
    exact hlanX
  have hbodyX : readBytes xmem p len.toNat = some body := by
    rw [hmem]
    rw [readBytes_writeBytes_apart (m := mem) (ws := wordBytes 8 c1) hxjp]
    exact hbody
  have hbodyC : readBytes (writeBytes xmem ei (natToBytes (0#64).toNat 8)) p len.toNat
      = some body := by
    rw [readBytes_writeBytes_apart (ws := natToBytes (0#64).toNat 8)
      (by rw [natToBytes_length]; exact heip)]
    exact hbodyX
  exact ⟨stage2ReadWord_of_readBytes
      (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]; exact hc1) hxjC, hlanC, hbodyC⟩

/-- **The expander's accepting answer at the exit's memory**: the four reads the
callee makes are the staging's — framed past the slot's write and the scan's — and
its clause then answers with the decoded prefix, the advanced cursor and the slot's
word.  The counter's `takeWhile` is empty because the lane there is already past the
body's first position, so the callee's `j1` is the exit's counter. -/
theorem s2StringBodyExpand_decoded_at_exit {mem xmem : Mem} {ch p dst xp xj : Nat}
    {len nxp : BitVec 64} {base c1 ei next lane : Nat} {ps : List Nat}
    {body out : List UInt8} {k : Nat}
    (hmem : xmem = writeBytes mem xj (wordBytes 8 c1))
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (hlane : ps[c1]? = some lane) (hge : p - base ≤ lane)
    (hp0 : p - base < 2 ^ 64) (hc1 : c1 < 2 ^ 64)
    (hxjp : RegionsApart xj 8 p len.toNat)
    (heip : RegionsApart ei 8 p len.toNat)
    (heixj : RegionsApart ei 8 xj 8)
    (heilan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ ei ∨ ei + 8 ≤ xp + 4 * j)
    (hjlan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * j)
    (hdec : escapeDecodeGo body 0 0
      (((ps.drop c1).takeWhile (fun q => decide (q < p - base + len.toNat))).map
        (fun q => q - (p - base))) [] = .decoded out k) :
    s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 (BitVec.ofNat 64 (p - base))]
      (writeBytes xmem ei (natToBytes (0#64).toNat 8)) next =
    some { ret := .int 64 (BitVec.ofNat 64 out.length),
           mem := writeBytes
             (writeBytes
               (writeBytes (writeBytes xmem ei (natToBytes (0#64).toNat 8)) dst out)
               xj (wordBytes 8 (c1 + k)))
             ei (wordBytes 8 out.length),
           next := next } := by
  obtain ⟨hxjW, hlanC, hbodyC⟩ :=
    s2StringBodyCallee_reads hmem hps hbody hc1 hxjp heip heixj heilan hjlan
  have hdrop : ps.drop c1 = lane :: ps.drop (c1 + 1) := drop_eq_cons_of_getElem? hlane
  have htake0 : ((ps.drop c1).takeWhile (fun q => decide (q < p - base))).length = 0 := by
    rw [hdrop, List.takeWhile_cons_of_neg (by
      have hlt : ¬ (lane < p - base) := by omega
      simpa using hlt)]
    rfl
  have hdec' : escapeDecodeGo body 0 0
      (((ps.drop (c1 + ((ps.drop c1).takeWhile (fun q => decide (q < p - base))).length)).takeWhile
        (fun q => decide (q < p - base + len.toNat))).map (fun q => q - (p - base))) []
      = .decoded out k := by
    rw [show c1 + ((ps.drop c1).takeWhile (fun q => decide (q < p - base))).length = c1 from by
      rw [htake0]; omega]
    exact hdec
  have h := escapeExpand8_decoded (p := p) (len := len.toNat) (dst := dst) (ei := ei)
    (xp := xp) (xj := xj) (nxp := nxp.toNat) (pos0 := p - base)
    (mem := writeBytes xmem ei (natToBytes (0#64).toNat 8)) (next := next)
    (j0 := c1) (ps := ps) (body := body) (out := out) (k := k)
    hxjW hlanC hbodyC len.isLt nxp.isLt hp0 hdec'
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, htake0, Nat.add_zero]
    using h


/-- **The expander's refusing answer at the exit's memory**: the same three reads,
the record's body-relative offset at the slot, the advanced cursor and all-ones as
the returned word. -/
theorem s2StringBodyExpand_refused_at_exit {mem xmem : Mem} {ch p dst xp xj : Nat}
    {len nxp : BitVec 64} {base c1 ei next lane off : Nat} {ps : List Nat}
    {body : List UInt8} {k : Nat}
    (hmem : xmem = writeBytes mem xj (wordBytes 8 c1))
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (hlane : ps[c1]? = some lane) (hge : p - base ≤ lane)
    (hp0 : p - base < 2 ^ 64) (hc1 : c1 < 2 ^ 64)
    (hxjp : RegionsApart xj 8 p len.toNat)
    (heip : RegionsApart ei 8 p len.toNat)
    (heixj : RegionsApart ei 8 xj 8)
    (heilan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ ei ∨ ei + 8 ≤ xp + 4 * j)
    (hjlan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * j)
    (hr : escapeDecodeGo body 0 0
      (((ps.drop c1).takeWhile (fun q => decide (q < p - base + len.toNat))).map
        (fun q => q - (p - base))) [] = .refused off k) :
    s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 (BitVec.ofNat 64 (p - base))]
      (writeBytes xmem ei (natToBytes (0#64).toNat 8)) next =
    some { ret := .int 64 0xffffffffffffffff#64,
           mem := writeBytes
             (writeBytes (writeBytes xmem ei (natToBytes (0#64).toNat 8)) ei
               (wordBytes 8 off))
             xj (wordBytes 8 (c1 + k)),
           next := next } := by
  obtain ⟨hxjW, hlanC, hbodyC⟩ :=
    s2StringBodyCallee_reads hmem hps hbody hc1 hxjp heip heixj heilan hjlan
  have hdrop : ps.drop c1 = lane :: ps.drop (c1 + 1) := drop_eq_cons_of_getElem? hlane
  have htake0 : ((ps.drop c1).takeWhile (fun q => decide (q < p - base))).length = 0 := by
    rw [hdrop, List.takeWhile_cons_of_neg (by
      have hlt : ¬ (lane < p - base) := by omega
      simpa using hlt)]
    rfl
  have hr' : escapeDecodeGo body 0 0
      (((ps.drop (c1 + ((ps.drop c1).takeWhile (fun q => decide (q < p - base))).length)).takeWhile
        (fun q => decide (q < p - base + len.toNat))).map (fun q => q - (p - base))) []
      = .refused off k := by
    rw [show c1 + ((ps.drop c1).takeWhile (fun q => decide (q < p - base))).length = c1 from by
      rw [htake0]; omega]
    exact hr
  have h := escapeExpand8_refused (p := p) (len := len.toNat) (dst := dst) (ei := ei)
    (xp := xp) (xj := xj) (nxp := nxp.toNat) (pos0 := p - base)
    (mem := writeBytes xmem ei (natToBytes (0#64).toNat 8)) (next := next)
    (j0 := c1) (ps := ps) (body := body) (off := off) (k := k)
    hxjW hlanC hbodyC len.isLt nxp.isLt hp0 hr'
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, htake0, Nat.add_zero]
    using h

/-- **The scan's `if.then` exit finishes form `1`**: the counter reached the count,
so the window at `j1` is empty and the model answers the body itself.  The exit's
cursor word is the word the model writes, so the two memories are one term. -/
theorem s2StringBodyArm_scan_ifThen {mem : Mem} {next ch p dst outn xp xj : Nat}
    {len nxp : BitVec 64} {base j0 : Nat} {ps : List Nat} {env0 : Env} {ei : Nat}
    {x : State}
    (hbase : stage2ReadWord mem ch 8 = some base)
    (hj0 : stage2ReadWord mem xj 8 = some j0)
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hpc : x.pc = "if.then9")
    (hword : s2StringBodyScanExitWordP mem xj j0 ps (p - base) nxp.toNat env0 ei xp x)
    (hlen : lookupName x.env "%len" = some (.int 64 len))
    (houtn : lookupName x.env "%outn" = some (.ptr outn))
    (hei : lookupName x.env "%ei" = some (.ptr ei))
    (hnxp0 : nxp.toNat ≠ 0) :
    s2StringBodyConcludes
      [.ptr ch, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next 2 x := by
  obtain ⟨c1, hmem, hfix, -, -, -, -, -, -, hif, -⟩ := hword
  have hcN : c1 = nxp.toNat := hif hpc
  have hlen_ps : ps.length = nxp.toNat := (readLanes32_lane hps).1
  have hj1 : c1 = j0 + ((ps.drop j0).takeWhile (fun q => decide (q < p - base))).length :=
    s2StringBodyScanExit_j1 hfix (Or.inl hcN) hlen_ps
  have hnil : ps.drop (j0 + ((ps.drop j0).takeWhile
      (fun q => decide (q < p - base))).length) = [] := by
    rw [← hj1, hcN]
    exact List.drop_eq_nil_of_le (by omega)
  have hwin : ((ps.drop (j0 + ((ps.drop j0).takeWhile
      (fun q => decide (q < p - base))).length)).takeWhile
      (fun q => decide (q < p - base + len.toNat))).isEmpty = true := by
    rw [hnil]
    rfl
  have hwin' : ((ps.drop c1).takeWhile
      (fun q => decide (q < p - base + len.toNat))).isEmpty = true := by
    rw [hj1]
    exact hwin
  have hmodel := s2StringBodyModel_bodyItself (mem := mem) (c := ch) (p := p)
    (dst := dst) (outn := outn) (xp := xp) (xj := xj) (j1 := c1) (len := len)
    (nxp := nxp) (base := base) (j0 := j0) (ps := ps) hbase hj0 hps hnxp0 hj1 hwin'
  refine ⟨⟨.int 32 (BitVec.ofNat 32 1),
    writeBytes x.mem outn (natToBytes len.toNat 8), next + 8⟩, ?_, ?_, ?_⟩
  · exact s2StringBodyExit_ifThen9 (e := x) hpc hlen houtn hei
  · refine ⟨writeBytes (writeBytes mem xj (wordBytes 8 c1)) outn
      (wordBytes 8 len.toNat), 1, [], hmodel, rfl, ?_, rfl⟩
    rw [hmem]
    rfl
  · rw [hmem]
    simp only [s2StringBodyFoot]
    exact ((UnchangedOutside.refl' mem _).write_le (a := xj) (w := 8)
      ⟨(xj, 8), by simp, le_rfl, le_rfl⟩
      (by simp [wordBytes, natToBytes_length])).write_le (a := outn) (w := 8)
      ⟨(outn, 8), by simp, le_rfl, le_rfl⟩ (by simp [natToBytes_length])

/-- **The scan's lane exit finishes form `1`** when the lane at the counter is past
the window: the inside test's bit is `0`, `if.then` takes the body-itself answer,
and the model's window at `j1` is empty by the same lane. -/
theorem s2StringBodyArm_scan_landLhsTrue {mem : Mem} {next ch p dst outn xp xj : Nat}
    {len nxp : BitVec 64} {base j0 : Nat} {ps : List Nat} {env0 : Env} {ei : Nat}
    {x : State} {c1 lane : Nat} {conv : BitVec 64}
    (hbase : stage2ReadWord mem ch 8 = some base)
    (hj0 : stage2ReadWord mem xj 8 = some j0)
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hpc : x.pc = "land.lhs.true")
    (hmem : x.mem = writeBytes mem xj (wordBytes 8 c1))
    (hfix : s2StringBodyScanPrefix ps (p - base) j0 c1)
    (hlane : ps[c1]? = some lane) (hge : p - base ≤ lane)
    (hconv : lookupName x.env "%conv" = some (.int 64 conv)) (hconvq : conv.toNat = lane)
    (hsub : lookupName x.env "%sub.ptr.sub"
      = some (.int 64 (BitVec.ofNat 64 (p - base))))
    (hpast : p - base + len.toNat ≤ lane)
    (hp0 : p - base < 2 ^ 64) (hpw : p - base + len.toNat < 2 ^ 64)
    (hlen : lookupName x.env "%len" = some (.int 64 len))
    (houtn : lookupName x.env "%outn" = some (.ptr outn))
    (hei : lookupName x.env "%ei" = some (.ptr ei))
    (hnxp0 : nxp.toNat ≠ 0) :
    s2StringBodyConcludes
      [.ptr ch, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next 3 x := by
  have hlen_ps : ps.length = nxp.toNat := (readLanes32_lane hps).1
  have hj1 : c1 = j0 + ((ps.drop j0).takeWhile (fun q => decide (q < p - base))).length :=
    s2StringBodyScanExit_j1 hfix (Or.inr ⟨lane, hlane, hge⟩) hlen_ps
  have hwin : ((ps.drop c1).takeWhile
      (fun q => decide (q < p - base + len.toNat))).isEmpty = true :=
    s2StringBodyWindow_empty_of_lane hlane hpast
  have hmodel := s2StringBodyModel_bodyItself (mem := mem) (c := ch) (p := p)
    (dst := dst) (outn := outn) (xp := xp) (xj := xj) (j1 := c1) (len := len)
    (nxp := nxp) (base := base) (j0 := j0) (ps := ps) hbase hj0 hps hnxp0 hj1 hwin
  have hsum : ((BitVec.ofNat 64 (p - base)) + len).toNat = p - base + len.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp0,
      Nat.mod_eq_of_lt hpw]
  have hbit : evalICmpNat .ugt 64 ((BitVec.ofNat 64 (p - base)) + len).toNat
      conv.toNat = 0#1 := by
    rw [hsum, hconvq]
    exact evalICmpNat_ugt_zero hpw (by omega) hpast
  refine ⟨⟨.int 32 (BitVec.ofNat 32 1),
    writeBytes x.mem outn (natToBytes len.toNat 8), next + 8⟩, ?_, ?_, ?_⟩
  · exact s2StringBodyExit_landLhsTrue_toIfThen9 (e := x) hpc hsub hlen hconv hbit houtn hei
  · refine ⟨writeBytes (writeBytes mem xj (wordBytes 8 c1)) outn
      (wordBytes 8 len.toNat), 1, [], hmodel, rfl, ?_, rfl⟩
    rw [hmem]
    rfl
  · rw [hmem]
    simp only [s2StringBodyFoot]
    exact ((UnchangedOutside.refl' mem _).write_le (a := xj) (w := 8)
      ⟨(xj, 8), by simp, le_rfl, le_rfl⟩
      (by simp [wordBytes, natToBytes_length])).write_le (a := outn) (w := 8)
      ⟨(outn, 8), by simp, le_rfl, le_rfl⟩ (by simp [natToBytes_length])

/-- **The error record's three words are present**, from the staging's one extent:
the body writes `0`, the offset and the message pointer at `e`, `e + 8` and
`e + 16`, and the staging holds the record whole. -/
theorem s2StringBodyErr_presence {mem : Mem} {e : Nat} {bs : List UInt8}
    (h : readBytes mem e stage2ErrorExtent = some bs) :
    readBytes mem e 4 ≠ none ∧ readBytes mem (e + 8) 8 ≠ none ∧
      readBytes mem (e + 16) 8 ≠ none := by
  have h24 : readBytes mem e (4 + 20) = some bs := by
    rw [show (4 + 20 : Nat) = stage2ErrorExtent from by decide]
    exact h
  obtain ⟨h4, h20⟩ := readBytes_split mem e 4 20 h24
  obtain ⟨-, h16⟩ := readBytes_split mem (e + 4) 4 16 h20
  obtain ⟨h8, h8'⟩ := readBytes_split mem (e + 8) 8 8 (by
    rwa [show (e + 4) + 4 = e + 8 from by omega] at h16)
  refine ⟨?_, ?_, ?_⟩
  · rw [h4]; simp
  · rw [h8]; simp
  · rw [show e + 16 = e + 8 + 8 from by omega, h8']; simp

/-- **The body's budget as a term of its arguments**: the entry's one step, the
scan's `(N + 1) * 2`, and the longest arm's five.  The same shape as
`stage2Budget`: a caller reads the budget off the arguments rather than the run. -/
def s2StringBodyBudget (args : List Value) : Nat :=
  match args with
  | [.ptr _, .ptr _, .int 64 _, .ptr _, .ptr _, .ptr _, .ptr _, .int 64 nxp] =>
      1 + (nxp.toNat + 1) * 2 + 5
  | _ => 0

/-! ### The refused arm's memory, named

Six `writeBytes` deep, the arm's memory is past the point where a statement's
parenthesisation is transcribable — the module's rule four, met from the other
side: the nesting limit is not only about reaching a subterm, it is about the
statement being writable at all.  The three memories are named here, and the two
steps the arm spends on them are equalities between the identifiers. -/

/-- The refused arm's memory as the body writes it: the scan's cursor word,
`if.end`'s clear, the callee's offset, its cursor word, then the record's three. -/
def s2StringBodyRefusedRun (mem : Mem) (ei xj c1 e' : Nat)
    (Woff Wj R0 R1 R2 : List UInt8) : Mem :=
  writeBytes
    (writeBytes
      (writeBytes
        (writeBytes
          (writeBytes
            (writeBytes
              (writeBytes mem xj (wordBytes 8 c1))
              ei (natToBytes (0#64).toNat 8))
            ei Woff)
          xj Wj)
        e' R0)
      (e' + (8#64).toNat) R1)
    (e' + (16#64).toNat) R2

/-- The same chain with the scan's cursor write erased — the join's left side. -/
def s2StringBodyRefusedErased (mem : Mem) (ei xj e' : Nat)
    (Woff Wj R0 R1 R2 : List UInt8) : Mem :=
  writeBytes
    (writeBytes
      (writeBytes
        (writeBytes
          (writeBytes
            (writeBytes mem ei (natToBytes (0#64).toNat 8))
            ei Woff)
          xj Wj)
        e' R0)
      (e' + (8#64).toNat) R1)
    (e' + (16#64).toNat) R2

/-- The model's refused memory at this call, in its own write order — the join's
right side. -/
def s2StringBodyRefusedModel (mem : Mem) (ei xj e' : Nat)
    (Woff Wj R0 R1 R2 : List UInt8) : Mem :=
  writeBytes
    (writeBytes
      (writeBytes
        (writeBytes
          (writeBytes mem e' R0) (e' + (8#64).toNat) R1)
        (e' + (16#64).toNat) R2)
      xj Wj)
    ei Woff

/-- **The scan's cursor write is erased**: `if.end`'s clear and the callee's offset
are adjacent and collapse, and one crossing then carries the callee's cursor write
past the erased one. -/
theorem s2StringBodyRefusedRun_erase (mem : Mem) {ei xj c1 e' : Nat}
    {Woff Wj R0 R1 R2 : List UInt8}
    (hWoff : Woff.length = 8)
    (hxj : readBytes mem xj (wordBytes 8 c1).length ≠ none)
    (hlen : (wordBytes 8 c1).length ≤ Wj.length)
    (hdis : xj + (wordBytes 8 c1).length ≤ ei ∨ ei + Woff.length ≤ xj) :
    s2StringBodyRefusedRun mem ei xj c1 e' Woff Wj R0 R1 R2 =
      s2StringBodyRefusedErased mem ei xj e' Woff Wj R0 R1 R2 := by
  simp only [s2StringBodyRefusedRun, s2StringBodyRefusedErased]
  rw [writeBytes_writeBytes_same
    (writeBytes mem xj (wordBytes 8 c1))
    ei (natToBytes (0#64).toNat 8) Woff (by simp [natToBytes_length, hWoff])]
  rw [writeBytes_writeBytes_same mem ei
    (natToBytes (0#64).toNat 8) Woff (by simp [natToBytes_length, hWoff])]
  exact congrArg (fun m =>
      writeBytes (writeBytes (writeBytes m e' R0) (e' + (8#64).toNat) R1)
        (e' + (16#64).toNat) R2)
    (writeBytes_absorb_single mem hxj hlen hdis)

/-- **The erased chain is the model's**: the join at the four regions it takes
present, `xj` and the record's three words.  The slot's write is the one every
crossing moves, so its own presence is never read. -/
theorem s2StringBodyRefusedErased_join (mem : Mem) {ei xj e' : Nat}
    {Woff Wj R0 R1 R2 : List UInt8}
    (hWoff : Woff.length = 8)
    (hxj : readBytes mem xj Wj.length ≠ none)
    (he0 : readBytes mem e' R0.length ≠ none)
    (he1 : readBytes mem (e' + (8#64).toNat) R1.length ≠ none)
    (he2 : readBytes mem (e' + (16#64).toNat) R2.length ≠ none)
    (h1 : ei + Woff.length ≤ xj ∨ xj + Wj.length ≤ ei)
    (h2 : ei + Woff.length ≤ e' ∨ e' + R0.length ≤ ei)
    (h3 : ei + Woff.length ≤ e' + (8#64).toNat ∨
      e' + (8#64).toNat + R1.length ≤ ei)
    (h4 : ei + Woff.length ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + R2.length ≤ ei)
    (h5 : xj + Wj.length ≤ e' ∨ e' + R0.length ≤ xj)
    (h6 : xj + Wj.length ≤ e' + (8#64).toNat ∨
      e' + (8#64).toNat + R1.length ≤ xj)
    (h7 : xj + Wj.length ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + R2.length ≤ xj)
    (h8 : e' + R0.length ≤ e' + (8#64).toNat ∨
      e' + (8#64).toNat + R1.length ≤ e')
    (h9 : e' + R0.length ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + R2.length ≤ e')
    (h10 : e' + (8#64).toNat + R1.length ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + R2.length ≤ e' + (8#64).toNat) :
    s2StringBodyRefusedErased mem ei xj e' Woff Wj R0 R1 R2 =
      s2StringBodyRefusedModel mem ei xj e' Woff Wj R0 R1 R2 := by
  simp only [s2StringBodyRefusedErased, s2StringBodyRefusedModel]
  exact s2StringBodyMemory_refused mem hWoff hxj he0 he1 he2 h1 h2 h3 h4 h5 h6 h7 h8
    h9 h10

/-! ### The refused arm's memory, as stages

A rewrite inside a named memory requires unfolding it, so a name is not enough for
a term a proof must rewrite *inside*: each rewrite site needs a stage.  The stages
are one `writeBytes` over the previous one, so every equality and every frame step
is between shallow identifiers and the seven-deep term never appears in a statement
again.  The first stage is the scan's own cursor write, because the arm's memory
starts where the scan left it. -/

/-- The scan's cursor write. -/
def s2StringBodyRefusedC0 (mem : Mem) (xj c1 : Nat) : Mem :=
  writeBytes mem xj (wordBytes 8 c1)

/-- `if.end`'s clear at the body's slot. -/
def s2StringBodyRefusedC1 (mem : Mem) (ei xj c1 : Nat) : Mem :=
  writeBytes (s2StringBodyRefusedC0 mem xj c1) ei (natToBytes (0#64).toNat 8)

/-- The callee's body-relative offset, at the same slot. -/
def s2StringBodyRefusedC2 (mem : Mem) (ei xj c1 offN : Nat) : Mem :=
  writeBytes (s2StringBodyRefusedC1 mem ei xj c1) ei (wordBytes 8 offN)

/-- The callee's cursor word. -/
def s2StringBodyRefusedC3 (mem : Mem) (ei xj c1 offN k : Nat) : Mem :=
  writeBytes (s2StringBodyRefusedC2 mem ei xj c1 offN) xj (wordBytes 8 (c1 + k))

/-- The record's first word. -/
def s2StringBodyRefusedC4 (mem : Mem) (ei xj c1 e' offN k : Nat) : Mem :=
  writeBytes (s2StringBodyRefusedC3 mem ei xj c1 offN k) e'
    (natToBytes (0#32).toNat 4)

/-- The record's second word: the body-relative offset added to the document's. -/
def s2StringBodyRefusedC5 (mem : Mem) (ei xj c1 e' offN k p base : Nat) : Mem :=
  writeBytes (s2StringBodyRefusedC4 mem ei xj c1 e' offN k) (e' + (8#64).toNat)
    (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8)

/-- The record's third word: the arm's final memory. -/
def s2StringBodyRefusedC6 (mem : Mem) (ei xj c1 e' offN k p base : Nat) : Mem :=
  writeBytes (s2StringBodyRefusedC5 mem ei xj c1 e' offN k p base)
    (e' + (16#64).toNat) (natToBytes (0#64).toNat 8)

/-- The callee's call memory and its two writes, as stages three deep. -/
def s2StringBodyRefusedExtra (mem : Mem) (ei xj c1 offN k : Nat) : Mem :=
  s2StringBodyRefusedC3 mem ei xj c1 offN k

/-- **The record's three words are the staged three**, stated between identifiers. -/
theorem s2StringBodyIfThen12Mem_staged (mem : Mem) (ei xj c1 e' offN k p base : Nat) :
    s2StringBodyIfThen12Mem (s2StringBodyRefusedExtra mem ei xj c1 offN k) e'
      (BitVec.ofNat 64 offN) (BitVec.ofNat 64 (p - base))
      = s2StringBodyRefusedC6 mem ei xj c1 e' offN k p base := rfl

/-- **The callee's two slot writes collapse**: they are adjacent at the staged
form, so the offset write is the memory. -/
theorem s2StringBodyRefusedC2_collapse (mem : Mem) (ei xj c1 offN : Nat) :
    s2StringBodyRefusedC2 mem ei xj c1 offN
      = writeBytes (s2StringBodyRefusedC0 mem xj c1) ei (wordBytes 8 offN) := by
  simp only [s2StringBodyRefusedC2, s2StringBodyRefusedC1]
  rw [writeBytes_writeBytes_same (s2StringBodyRefusedC0 mem xj c1) ei
    (natToBytes (0#64).toNat 8) (wordBytes 8 offN)
    (by simp [natToBytes_length, wordBytes])]

/-- **The scan's cursor write is erased, at the stages**: the collapse puts the
callee's offset adjacent to the scan's write, and one crossing then carries the
callee's cursor write past it. -/
theorem s2StringBodyRefusedC3_erase (mem : Mem) {ei xj c1 offN k : Nat}
    (hxj : readBytes mem xj (wordBytes 8 c1).length ≠ none)
    (hlen : (wordBytes 8 c1).length ≤ (wordBytes 8 (c1 + k)).length)
    (hdis : xj + (wordBytes 8 c1).length ≤ ei ∨
      ei + (wordBytes 8 offN).length ≤ xj) :
    s2StringBodyRefusedC3 mem ei xj c1 offN k
      = writeBytes (writeBytes mem ei (wordBytes 8 offN)) xj
          (wordBytes 8 (c1 + k)) := by
  rw [s2StringBodyRefusedC3, s2StringBodyRefusedC2_collapse, s2StringBodyRefusedC0]
  exact writeBytes_absorb_single mem hxj hlen hdis

/-- **The staged memory is the model's.**  The erase puts the scan's write out of
the chain and the collapse puts the callee's offset beside it; restoring the slot's
clear makes the chain the erased form the join is stated at, and the join then gives
the model's order. -/
theorem s2StringBodyRefusedC6_join (mem : Mem) {ei xj c1 e' offN k p base : Nat}
    (hxj : readBytes mem xj (wordBytes 8 c1).length ≠ none)
    (hlen : (wordBytes 8 c1).length ≤ (wordBytes 8 (c1 + k)).length)
    (hdis : xj + (wordBytes 8 c1).length ≤ ei ∨
      ei + (wordBytes 8 offN).length ≤ xj)
    (hWoff : (wordBytes 8 offN).length = 8)
    (hxj' : readBytes mem xj (wordBytes 8 (c1 + k)).length ≠ none)
    (he0 : readBytes mem e' (natToBytes (0#32).toNat 4).length ≠ none)
    (he1 : readBytes mem (e' + (8#64).toNat)
      (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length
      ≠ none)
    (he2 : readBytes mem (e' + (16#64).toNat)
      (natToBytes (0#64).toNat 8).length ≠ none)
    (h1 : ei + (wordBytes 8 offN).length ≤ xj ∨
      xj + (wordBytes 8 (c1 + k)).length ≤ ei)
    (h2 : ei + (wordBytes 8 offN).length ≤ e' ∨
      e' + (natToBytes (0#32).toNat 4).length ≤ ei)
    (h3 : ei + (wordBytes 8 offN).length ≤ e' + (8#64).toNat ∨
      e' + (8#64).toNat +
        (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length
        ≤ ei)
    (h4 : ei + (wordBytes 8 offN).length ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + (natToBytes (0#64).toNat 8).length ≤ ei)
    (h5 : xj + (wordBytes 8 (c1 + k)).length ≤ e' ∨
      e' + (natToBytes (0#32).toNat 4).length ≤ xj)
    (h6 : xj + (wordBytes 8 (c1 + k)).length ≤ e' + (8#64).toNat ∨
      e' + (8#64).toNat +
        (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length
        ≤ xj)
    (h7 : xj + (wordBytes 8 (c1 + k)).length ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + (natToBytes (0#64).toNat 8).length ≤ xj)
    (h8 : e' + (natToBytes (0#32).toNat 4).length ≤ e' + (8#64).toNat ∨
      e' + (8#64).toNat +
        (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length
        ≤ e')
    (h9 : e' + (natToBytes (0#32).toNat 4).length ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + (natToBytes (0#64).toNat 8).length ≤ e')
    (h10 : e' + (8#64).toNat +
        (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length
        ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + (natToBytes (0#64).toNat 8).length ≤ e' + (8#64).toNat) :
    s2StringBodyRefusedC6 mem ei xj c1 e' offN k p base
      = s2StringBodyRefusedModel mem ei xj e' (wordBytes 8 offN)
          (wordBytes 8 (c1 + k)) (natToBytes (0#32).toNat 4)
          (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8)
          (natToBytes (0#64).toNat 8) := by
  rw [s2StringBodyRefusedC6, s2StringBodyRefusedC5, s2StringBodyRefusedC4,
    s2StringBodyRefusedC3_erase mem hxj hlen hdis]
  rw [← writeBytes_writeBytes_same mem ei (natToBytes (0#64).toNat 8)
    (wordBytes 8 offN) (by simp [natToBytes_length, wordBytes])]
  exact s2StringBodyRefusedErased_join mem hWoff hxj' he0 he1 he2 h1 h2 h3 h4
    h5 h6 h7 h8 h9 h10

/-- The model's memory at this call, staged: the record's message set, the cursor
and the slot. -/
def s2StringBodyRefusedM0 (mem : Mem) (ei xj c1 e' offN k p base : Nat) : Mem :=
  writeBytes
    (writeBytes (stage2ErrSetMsg mem e' (p - base + offN) 0) xj
      (wordBytes 8 (c1 + k)))
    ei (wordBytes 8 offN)

/-- **The model's order is the staged order**: the record's three words are
`stage2ErrSetMsg`, which is the reconciliation, and the rest is the same chain. -/
theorem s2StringBodyRefusedModel_reconciles (mem : Mem) {ei xj c1 e' offN k p base : Nat}
    (hoffN : offN < 2 ^ 64) (hp0 : p - base < 2 ^ 64)
    (hsumW : offN + (p - base) < 2 ^ 64) :
    s2StringBodyRefusedModel mem ei xj e' (wordBytes 8 offN) (wordBytes 8 (c1 + k))
        (natToBytes (0#32).toNat 4)
        (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8)
        (natToBytes (0#64).toNat 8)
      = s2StringBodyRefusedM0 mem ei xj c1 e' offN k p base := by
  simp only [s2StringBodyRefusedModel, s2StringBodyRefusedM0]
  rw [s2StringBodyErrRecord_reconciles mem e' (BitVec.ofNat 64 offN)
    (BitVec.ofNat 64 (p - base)) (p - base) rfl hp0 (by
      rw [show (BitVec.ofNat 64 offN).toNat = offN from by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffN]]
      exact hsumW)]
  rw [show (BitVec.ofNat 64 offN).toNat = offN from by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffN]]

/-- **The expander's refusing answer at variable leaves**: its memory is the callee's
chain with `Woff`/`Wj` as lists rather than the literal words.  A consumer that names
the stage then unifies by structure; comparing a chain whose leaves are literals is
what costs, not its depth. -/
theorem s2StringBodyExpand_refused_named {mem xmem : Mem} {p dst xp xj : Nat}
    {len nxp : BitVec 64} {base c1 ei next lane offN k : Nat} {ps : List Nat}
    {body : List UInt8} {Woff Wj : List UInt8}
    (hmem : xmem = writeBytes mem xj (wordBytes 8 c1))
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (hlane : ps[c1]? = some lane) (hge : p - base ≤ lane)
    (hp0 : p - base < 2 ^ 64) (hc1 : c1 < 2 ^ 64)
    (hWoff : Woff = wordBytes 8 offN) (hWj : Wj = wordBytes 8 (c1 + k))
    (hxjp : RegionsApart xj 8 p len.toNat)
    (heip : RegionsApart ei 8 p len.toNat)
    (heixj : RegionsApart ei 8 xj 8)
    (heilan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ ei ∨ ei + 8 ≤ xp + 4 * j)
    (hjlan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * j)
    (hr : escapeDecodeGo body 0 0
      (((ps.drop c1).takeWhile (fun q => decide (q < p - base + len.toNat))).map
        (fun q => q - (p - base))) [] = .refused offN k) :
    s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 (BitVec.ofNat 64 (p - base))]
      (writeBytes xmem ei (natToBytes (0#64).toNat 8)) next =
    some { ret := .int 64 0xffffffffffffffff#64,
           mem := writeBytes
             (writeBytes (writeBytes xmem ei (natToBytes (0#64).toNat 8)) ei Woff)
             xj Wj,
           next := next } := by
  rw [hWoff, hWj]
  exact s2StringBodyExpand_refused_at_exit (ch := 0) (dst := dst) (next := next)
    (hps := hps) (hbody := hbody) (hlane := hlane) (hge := hge) (hp0 := hp0)
    (hc1 := hc1) (hxjp := hxjp) (heip := heip) (heixj := heixj)
    (heilan := heilan) (hjlan := hjlan) (hmem := hmem) (hr := hr)

/-- The arm's run, every leaf a variable: the callee's answer comes from the named
derivation, and the exit lemma takes the memory it produced. -/
theorem s2StringBodyArm_scan_refused_run {mem extra : Mem} {x : State}
    {ch p dst outn xp xj : Nat} {len nxp : BitVec 64}
    {base j0 c1 ei next lane offN k e' : Nat} {ps : List Nat} {body : List UInt8}
    {conv : BitVec 64} {Woff Wj : List UInt8}
    (hpc : x.pc = "land.lhs.true")
    (hmem : x.mem = writeBytes mem xj (wordBytes 8 c1))
    (hC0 : s2StringBodyRefusedC0 mem xj c1
      = writeBytes mem xj (wordBytes 8 c1))
    (hexpMem : extra
      = writeBytes
          (writeBytes (writeBytes (s2StringBodyRefusedC0 mem xj c1) ei
            (natToBytes (0#64).toNat 8)) ei Woff) xj Wj)
    (hWoff : Woff = wordBytes 8 offN) (hWj : Wj = wordBytes 8 (c1 + k))
    (hlane : ps[c1]? = some lane) (hge : p - base ≤ lane)
    (hlt : lane < p - base + len.toNat)
    (hconv : lookupName x.env "%conv" = some (.int 64 conv)) (hconvq : conv.toNat = lane)
    (hc : lookupName x.env "%c" = some (.ptr ch))
    (hsub : lookupName x.env "%sub.ptr.sub" =
      some (.int 64 (BitVec.ofNat 64 (p - base))))
    (hlen : lookupName x.env "%len" = some (.int 64 len))
    (hp : lookupName x.env "%p" = some (.ptr p))
    (hdst : lookupName x.env "%dst" = some (.ptr dst))
    (hei : lookupName x.env "%ei" = some (.ptr ei))
    (hxp : lookupName x.env "%xp" = some (.ptr xp))
    (hxj : lookupName x.env "%xj" = some (.ptr xj))
    (hnxp : lookupName x.env "%nxp" = some (.int 64 nxp))
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (hrec : stage2ReadWord mem (ch + 1112) 8 = some e')
    (hp0 : p - base < 2 ^ 64) (hpw : p - base + len.toNat < 2 ^ 64) (hc1 : c1 < 2 ^ 64)
    (hoffN : offN < 2 ^ 64)
    (hxjp : RegionsApart xj 8 p len.toNat)
    (heip : RegionsApart ei 8 p len.toNat)
    (heixj : RegionsApart ei 8 xj 8)
    (heilan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ ei ∨ ei + 8 ≤ xp + 4 * j)
    (hjlan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * j)
    (hwjLen : Wj.length = 8) (hc1k : c1 + k = c1 + k)
    (hxje : RegionsApart xj 8 (ch + 1112) 8)
    (heie : RegionsApart ei 8 (ch + 1112) 8)
    (hoff : readBytes extra ei 8 = some Woff)
    (hr : escapeDecodeGo body 0 0
      (((ps.drop c1).takeWhile (fun q => decide (q < p - base + len.toNat))).map
        (fun q => q - (p - base))) [] = .refused offN k) :
    runFuel s2StringBodyCalls 4 s2StringBodyBody x =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen12Mem extra e' (BitVec.ofNat 64 offN)
          (BitVec.ofNat 64 (p - base)))) := by
  have hsum : ((BitVec.ofNat 64 (p - base)) + len).toNat = p - base + len.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp0,
      Nat.mod_eq_of_lt hpw]
  have hbit7 : evalICmpNat .ugt 64 ((BitVec.ofNat 64 (p - base)) + len).toNat
      conv.toNat = 1#1 := by
    rw [hsum, hconvq]
    exact evalICmpNat_ugt_one hpw (by omega) hlt
  have he64 : e' < 2 ^ 64 := stage2ReadWord_lt_64 hrec
  have hrecB : readBytes mem (ch + (1112#64).toNat) 8 = some (wordBytes 8 e') := by
    simpa using readBytes_of_stage2ReadWord hrec
  have hrecE : readBytes extra (ch + (1112#64).toNat) 8 = some (wordBytes 8 e') := by
    rw [hexpMem]
    rw [readBytes_writeBytes_apart (ws := Wj)
      (show RegionsApart xj Wj.length (ch + (1112#64).toNat) 8 from by
        rcases hxje with h | h
        · exact Or.inl (by rw [hwjLen]; exact h)
        · exact Or.inr h)]
    rw [readBytes_writeBytes_apart (ws := Woff)
      (show RegionsApart ei Woff.length (ch + (1112#64).toNat) 8 from by
        rcases heie with h | h
        · exact Or.inl (by rw [hWoff]; simp [natToBytes_length]; exact h)
        · exact Or.inr h)]
    rw [readBytes_writeBytes_apart (ws := natToBytes (0#64).toNat 8)
      (show RegionsApart ei (natToBytes (0#64).toNat 8).length
        (ch + (1112#64).toNat) 8 from by
        rcases heie with h | h
        · exact Or.inl (by rw [natToBytes_length]; exact h)
        · exact Or.inr h)]
    rw [s2StringBodyRefusedC0]
    rw [readBytes_writeBytes_apart (ws := wordBytes 8 c1)
      (show RegionsApart xj (wordBytes 8 c1).length (ch + (1112#64).toNat) 8 from by
        rcases hxje with h | h
        · exact Or.inl (by rw [show (wordBytes 8 c1).length = 8 from
            natToBytes_length _ _]; exact h)
        · exact Or.inr h)]
    exact hrecB
  have hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 (BitVec.ofNat 64 (p - base))]
      (writeBytes x.mem ei (natToBytes (0#64).toNat 8)) x.next =
      some { ret := .int 64 0xffffffffffffffff#64, mem := extra, next := x.next } := by
    have h := s2StringBodyExpand_refused_named (xmem := s2StringBodyRefusedC0 mem xj c1)
      (Woff := Woff) (Wj := Wj) (next := x.next) (dst := dst) hC0 hps hbody hlane hge hp0 hc1 hWoff hWj hxjp heip
      heixj heilan hjlan hr
    have hx : x.mem = s2StringBodyRefusedC0 mem xj c1 := hmem.trans hC0.symm
    rw [hx]
    rw [← hexpMem] at h
    exact h
  simpa using s2StringBodyExit_refused (e := x) (off := BitVec.ofNat 64 offN) hpc hc hsub
    hlen hconv hbit7 hp hdst hei hxp hxj hnxp hexp (evalICmp_eq_one rfl)
    (by
      rw [show (BitVec.ofNat 64 offN).toNat = offN from by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffN]]
      change readBytes extra ei 8 = some (wordBytes 8 offN)
      rw [← hWoff]
      exact hoff)
    (by simpa using hrecE) he64

/-- **The expander's refusing answer, concluded at the stage**: its memory *is*
`s2StringBodyRefusedC3`, and the deep body appears only here, unfolded one stage at
a time — each a one-level delta, which is cheap where a single delta through all
three is not. -/
theorem s2StringBodyExpand_refused_staged {mem : Mem} {p dst xp xj : Nat}
    {len nxp : BitVec 64} {base c1 ei next lane offN k : Nat} {ps : List Nat}
    {body : List UInt8}
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (hlane : ps[c1]? = some lane) (hge : p - base ≤ lane)
    (hp0 : p - base < 2 ^ 64) (hc1 : c1 < 2 ^ 64)
    (hxjp : RegionsApart xj 8 p len.toNat)
    (heip : RegionsApart ei 8 p len.toNat)
    (heixj : RegionsApart ei 8 xj 8)
    (heilan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ ei ∨ ei + 8 ≤ xp + 4 * j)
    (hjlan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * j)
    (hr : escapeDecodeGo body 0 0
      (((ps.drop c1).takeWhile (fun q => decide (q < p - base + len.toNat))).map
        (fun q => q - (p - base))) [] = .refused offN k) :
    s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 (BitVec.ofNat 64 (p - base))]
      (writeBytes (s2StringBodyRefusedC0 mem xj c1) ei
        (natToBytes (0#64).toNat 8)) next =
    some { ret := .int 64 0xffffffffffffffff#64,
           mem := s2StringBodyRefusedC3 mem ei xj c1 offN k, next := next } := by
  rw [s2StringBodyRefusedC3, s2StringBodyRefusedC2, s2StringBodyRefusedC1]
  exact s2StringBodyExpand_refused_named (dst := dst) (next := next)
    (xmem := s2StringBodyRefusedC0 mem xj c1)
    (Woff := wordBytes 8 offN) (Wj := wordBytes 8 (c1 + k))
    rfl hps hbody hlane hge hp0 hc1 rfl rfl hxjp heip heixj heilan hjlan hr

/-- **The entry's short arm**: the cursor is at or past the count, so `%cmp3` is
`0` and the entry goes straight to `if.then`.  The model's `j1` is `j0` (the list
is exhausted at the cursor), the window is empty, and the answer is form `1` — and
the two memories agree because the model's cursor write is the write the staging
already read, so it is the memory. -/
theorem s2StringBodyArm_entry_ifThen {mem : Mem} {next c p dst outn xp xj : Nat}
    {len nxp : BitVec 64} {base j0 : Nat} {ps : List Nat} {body : List UInt8}
    {e : Nat}
    (hbase : stage2ReadWord mem c 8 = some base)
    (hj0 : stage2ReadWord mem xj 8 = some j0)
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hp64 : p < 2 ^ 64) (hble : base ≤ p)
    (hj63 : j0 < 2 ^ 63) (hN63 : nxp.toNat < 2 ^ 63)
    (hnle : nxp.toNat ≤ j0) (hnxp0 : nxp.toNat ≠ 0) :
    s2StringBodyConcludes
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next 4
      (stagedState s2StringBodyBody
        [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
          .int 64 nxp] mem next) := by
  obtain ⟨hpc, hc, hp, hlen, hdst, houtn, hxp, hxj, hnxp, hmem, hnext⟩ :=
    s2StringBodyStaged_entry mem next
  have hrun := s2StringBodyArm_bodyItself
    (env := (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).env)
    (s := stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next)
    hpc hc hp hxj hnxp hlen houtn
    (by simpa only [hmem] using readBytes_of_stage2ReadWord hbase)
    (stage2ReadWord_lt_64 hbase) hp64
    (by simpa only [hmem] using readBytes_of_stage2ReadWord hj0)
    (stage2ReadWord_lt_64 hj0)
    (by
      apply evalICmp_eq_zero
      intro hzero
      apply hnxp0
      have := congrArg BitVec.toNat hzero
      simpa using this)
    (s2StringBodyBit_cmp3_zero hj63 hN63 hnle)
  have hlen_ps : ps.length = nxp.toNat := (readLanes32_lane hps).1
  have hnil : ps.drop j0 = [] := List.drop_eq_nil_of_le (by omega)
  have hj1 : j0 + ((ps.drop j0).takeWhile (fun q => decide (q < p - base))).length
      = j0 := by
    rw [hnil]
    simp
  have hwin : ((ps.drop (j0 + ((ps.drop j0).takeWhile (fun q => decide (q < p - base))).length)).takeWhile
      (fun q => decide (q < p - base + len.toNat))).isEmpty = true := by
    rw [hj1, hnil]
    rfl
  have hmodel : stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat =
      some (writeBytes (writeBytes mem xj (wordBytes 8 j0)) outn
        (wordBytes 8 len.toNat), 1, []) := by
    simp only [stage2StringBody, hbase, hj0, hps]
    rw [if_neg hnxp0, if_pos hwin, hj1]
  refine ⟨⟨.int 32 (BitVec.ofNat 32 1),
    writeBytes mem outn (natToBytes len.toNat 8), next + 8⟩, ?_, ?_, ?_⟩
  · simpa only [stateAt, stagedState] using hrun
  · exact s2StringBodyPost_of_bodyItself hmodel
      (stage2ReadWord_writeBytes_self mem xj 8 j0 hj0)
  · simp only [s2StringBodyFoot, he]
    exact (UnchangedOutside.refl' mem _).write_le (a := outn) (w := 8)
      ⟨(outn, 8), by simp, le_rfl, le_rfl⟩ (by simp [natToBytes_length])

end LeanLLVM.Refinement
