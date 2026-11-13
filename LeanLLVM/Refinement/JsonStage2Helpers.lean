/-
The six helpers' contracts at the walk's call boundary.

`JsonStage2Body` models the six functions the emitted walk calls out of line —
`s2_init`, `s2_value_pos`, `s2_after_value`, `s2_string_body`, `od_scalar_value`
and `num_fast_el1` — and proves each model's own facts.  This module states, for
each, the record a *caller* reads: the staging it is called at, the answer, the
regions it may write, and the facts that turn the triple into a step — the call
resolves at the staging, every resolved answer satisfies the post, and every
resolved answer's memory is the caller's outside the regions.

**Why the regions are not optional.**  The model's `Calls` environment answers a
call with a whole `Mem`, and the semantics has no fresh frame per call: a callee's
writes are visible to its caller exactly as the walk's own stores are.  A block
that takes a call therefore owes two separate statements.  The *post* says what
the callee answered — which word the walk branches on, which words it reloads —
and the *footprint* says which bytes it may have moved, which is what keeps
`WalkInv.log_hash`, `WalkInv.log_alen` or `WalkInv.owning` true one step later.
The footprint is a region list read off the call's arguments, so a caller applies
it by membership (`HelperContract.keeps`, `CallsFootprint.keeps_of_not_mem`) or as
the caller's view (`HelperContract.view`, `CallerView_of_framed`) — the two
spellings the walk's frame rules already use, and one `HelperContract.resolves`
application gives the outcome, the post and the frame at once.

**What each region list is, and why it is read off the arguments.**  `s2_init`
writes the `S2` record at its argument's extent; `s2_value_pos` writes nothing;
`s2_after_value` writes the root flag or one container-stack byte at the running
depth; `s2_string_body` writes the cursor word, the decoded-length word, the
decoded body's prefix in a slot `len` wide and, on refusal, the error record the
cursor record points at; `num_fast_el1` writes the value on acceptance and the
offset on refusal, never both; `od_scalar_value` writes the stream's cursor word,
the record it appends at the stream's cursor and, on refusal, the error record.
Each of the six carries its three facts — `answers`, `sound` and `framed` — so
`HelperContract.resolves` applies at a call block for every helper the emitted
walk calls out of line (see "What is not stated here" for what stays open).
Each list is the union over the arms one call may take, because a footprint is
read from the arguments and the memory *before* the call and so cannot see which
arm the callee chose.  Where an arm writes less than the union — the literal tag's
one byte inside a thirteen-byte slot — the narrower write is a corollary of the
model's own `emitBlobs_spec`/`outBlob_spec` rather than a second region list.

**The four body-allocated objects.**  `%ei.i`, `%root_done.i`, `%xj.i` and
`%outn.i` are `alloca`s of the emitted wrapper, not among the eight staging
objects `stage2StagingArgs` passes, so their addresses are the allocator's and no
staged list contains them (`JsonStage2IR.allocaTypes` pins their widths).  Four of
the six helpers write them, and the region lists below name them at the pointers
their call passes: a walk step over a helper call needs an invariant whose region
claim covers the four as well as the seven staged objects, which is
`JsonStage2Scratch.stage2AllocaWrites`.

**The number helper's two exits.**  The emitted function converts a lexeme only
after its own lexical scan, and writes the first rejected position through `*err`
on the way out (`stage2.c:388`, `:400`, `:419`, `:425`); `JsonStage2Body`'s
`stage2NumFast` carries both exits with `numLexScan` as the scan.  The offset is
bounded by the lexeme's length (`numLexScan_fst_le`), which keeps the reported
position inside the token; the accepted arm's eight bytes are `numFastEmitted`'s,
whose `strtodSpec` clause `JsonStage2Body` proves.  The arg list decides, and the
post and the footprint carry both, because the walk branches on `r.ret`.

**What the string helper owes the arena's reservation.**  `z_arena_reserve.exit`
decodes one entry's body, and the walk then advances the arena's cursor by the
decoded length.  `WalkInv.pending_cursor` (`alen ≤ ndst0 + p`) survives that
advance only if the decoded length is inside the body's document extent, so the
staging asks for the escape list to be this body's own positions in document order
(`BodyPositionsSpaced`), and the accepting arms' bound `on ≤ len` is
`s2StringBody_outn_le`'s at that staging, read off `escapeDecodeGo_length_le`.
`WalkInv.pending_cursor` consumes that bound; it is the one datum the walk reads
from the call beyond the post and the frame.  The
spacing is the *list's* obligation — the stage-1 escape positions' token extent —
and not a fact about this function; a caller that cannot supply it has no bound on
the escaped form, and `docs/contract.md` §7.6 records that rather than assuming it
away.

**What is not stated here.**  One gap, deliberate and named, and one consequence
for the walk.

*Every helper's contract is proved of its model, and no model is a refinement of
an emitted body.*  Each of the six has `answers`, `sound` and `framed` as
theorems of `JsonStage2Body`'s model — `s2InitContract` and its five siblings
below — so a call block applies `HelperContract.resolves`, `keeps`,
`readBytes_eq` and `view` at the helper's own region list, and the decoded
length's bound is `s2StringBody_outn_le`'s.  What none of them is, is a statement
about the compiled function: the fixture declares all six
(`stage2.rewrites.tsv` class r2 — "their bodies are outside this fragment ...
each is resolved by the fixture's `Calls` environment at the record or tier
theorem that states its contract").  The models are transcriptions of
`kernel/json/stage2.c` pinned by `#guard`s in `JsonStage2Body`, and the
correspondence between a transcription and the compiled function is the pipeline's
body-faithfulness seam.  `docs/contract.md` §7.6 records that per helper.

*What the walk may now do, and the one thing it must still carry.*
`JsonStage2WalkScope`'s class F — the nineteen links whose callee is one of these
six — is unblocked at the contract level: each link's step is a `resolves`
application at the staging the block establishes, and the frame is the helper's
own region list composed with the block's other writes.  The walk's invariant must
still name the four body-allocated objects when it crosses a call that writes one
(`%ei.i`, `%root_done.i`, `%xj.i`, `%outn.i`, above): a claim covering only the
seven staged objects does not survive `s2_after_value`, `s2_string_body` or
`num_fast_el1`, and no staged list contains them because the allocator chose
their addresses.  That is a claim the walk states, not a fact this module can add:
`s2AfterValueFoot` says *where* the byte is written, and whether the invariant
covers that address is the invariant's own content.
-/
import LeanLLVM.Refinement.JsonStage2Body

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open ByteString
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### A region list's complement

A byte outside a region containing `start … start + n` lies below the interval or
above it.  The disjunction rather than the negation of the interval, because
`omega` proves this one without case-splitting on the hypothesis and so leaves no
`Classical.choice` in the footprint. -/
theorem outside_regions_lt_or_le {regions : List (Nat × Nat)} {start n : Nat}
    (hin : ∃ r ∈ regions, r.1 ≤ start ∧ start + n ≤ r.1 + r.2) :
    ∀ a, (∀ r ∈ regions, ¬ (r.1 ≤ a ∧ a < r.1 + r.2)) →
      a < start ∨ start + n ≤ a := by
  intro a ha
  rcases Nat.lt_or_ge a start with hlt | hge
  · exact Or.inl hlt
  · right
    rcases Nat.lt_or_ge a (start + n) with hin2 | hge2
    · obtain ⟨r, hr, rlo, rhi⟩ := hin
      exact absurd ⟨Nat.le_trans rlo hge, Nat.lt_of_lt_of_le hin2 rhi⟩ (ha r hr)
    · exact hge2

/-! ### Frame steps

A write and a region list.  These steps are what a model's straight-line writes
are composed with: a write whose bytes all lie inside one of the listed regions
leaves the rest of the list's complement alone, two frames over the same list
compose, and a frame over a narrower list is one over any list that covers it.
They are proved here rather than imported because the walk's region lists are
literals built from a call's arguments, and each step is one
`readByte_writeBytes_outside`. -/

/-- A memory is unchanged outside any region list, from itself. -/
theorem UnchangedOutside.refl' (mem : Mem) (R : List (Nat × Nat)) :
    UnchangedOutside mem mem R :=
  fun _ _ => rfl

/-- **A write inside one listed region extends a frame over that list.**  `hw` lets
a caller state a write's slot at an extent wider than the bytes written: the
decoded body's `len`-wide slot for a shorter decoded prefix, for instance. -/
theorem UnchangedOutside.write_le {mem m : Mem} {R : List (Nat × Nat)} {a w : Nat}
    (h : UnchangedOutside mem m R)
    (hin : ∃ q ∈ R, q.1 ≤ a ∧ a + w ≤ q.1 + q.2) {bs : List UInt8} (hw : bs.length ≤ w) :
    UnchangedOutside mem (writeBytes m a bs) R := by
  intro x hx
  rw [readByte_writeBytes_outside m bs ?_]
  exact h x hx
  obtain ⟨q, hq, lo, hi⟩ := hin
  exact outside_regions_lt_or_le (start := a) (n := bs.length)
    ⟨q, hq, lo, by omega⟩ x hx

/-- Two frames over the same list compose. -/
theorem UnchangedOutside.trans' {mem m₁ m₂ : Mem} {R : List (Nat × Nat)}
    (h₁ : UnchangedOutside mem m₁ R) (h₂ : UnchangedOutside m₁ m₂ R) :
    UnchangedOutside mem m₂ R :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

/-- A frame over a narrow list is one over any list that covers it. -/
theorem UnchangedOutside.of_subset {mem m : Mem} {R₀ R : List (Nat × Nat)}
    (h : UnchangedOutside mem m R₀)
    (hsub : ∀ q ∈ R₀, ∃ s ∈ R, s.1 ≤ q.1 ∧ q.1 + q.2 ≤ s.1 + s.2) :
    UnchangedOutside mem m R :=
  UnchangedOutside.widen h (fun _a ha q hq => by
    obtain ⟨s, hs, lo, hi⟩ := hsub q hq
    exact fun ⟨h₁, h₂⟩ => ha s hs ⟨Nat.le_trans lo h₁, Nat.lt_of_lt_of_le h₂ hi⟩)

/-- **A store list whose every store lies inside one region leaves the region's
complement alone.**  This is `stage2WriteStores`'s frame, which is `s2_init`'s
reply: fifteen stores at the `S2` record's own offsets. -/
theorem stage2WriteStores_frame {mem : Mem} {R : List (Nat × Nat)}
    {ws : List (Nat × List UInt8)}
    (h : ∀ p ∈ ws, ∃ q ∈ R, q.1 ≤ p.1 ∧ p.1 + p.2.length ≤ q.1 + q.2) :
    UnchangedOutside mem (stage2WriteStores mem ws) R := by
  induction ws generalizing mem with
  | nil => exact UnchangedOutside.refl' mem R
  | cons p rest ih =>
      obtain ⟨a, bs⟩ := p
      have hstep : UnchangedOutside mem (writeBytes mem a bs) R :=
        (UnchangedOutside.refl' mem R).write_le (h (a, bs) (List.mem_cons_self ..))
          (Nat.le_refl _)
      exact hstep.trans' (ih (mem := writeBytes mem a bs)
        (fun q hq => h q (List.mem_cons_of_mem _ hq)))

/-! ### The contract shape

A helper's record is six fields: the staging it is called at, the answer, the
regions it may write, and the three facts that tie the answer to the model. -/

/-- **A helper's contract at one selection.** -/
structure HelperContract (calls : Calls) (sym : String) where
  /-- The staging: the argument list is the emitted call's, and the words the
  callee reads are readable. -/
  pre : List Value → Mem → Nat → Prop
  /-- The answer: the returned word, and the memory's shape at the words the
  caller reloads. -/
  post : List Value → Mem → Nat → CallOutcome → Prop
  /-- The regions the callee may have written, read from its arguments. -/
  foot : List Value → Mem → Nat → List (Nat × Nat)
  /-- The call resolves at the staging: it is not the semantics' `ub`. -/
  answers : ∀ args mem next, pre args mem next → ∃ r, calls sym args mem next = some r
  /-- Every resolved answer satisfies the post. -/
  sound : ∀ args mem next, pre args mem next → ∀ r, calls sym args mem next = some r →
    post args mem next r
  /-- Every resolved answer differs from the handed-over memory only inside the
  footprint. -/
  framed : ∀ args mem next, pre args mem next → ∀ r, calls sym args mem next = some r →
    UnchangedOutside mem r.mem (foot args mem next)

namespace HelperContract

variable {calls : Calls} {sym : String}

/-- **A helper call, as a step's three facts**: it resolves, its answer satisfies
the post, and the memory it returns is the caller's outside the footprint.  This
is the single application a call block's `denoteCode` trace makes. -/
theorem resolves (c : HelperContract calls sym) {args : List Value} {mem : Mem}
    {next : Nat} (hpre : c.pre args mem next) :
    ∃ r, calls sym args mem next = some r ∧ c.post args mem next r ∧
      UnchangedOutside mem r.mem (c.foot args mem next) := by
  obtain ⟨r, hr⟩ := c.answers args mem next hpre
  exact ⟨r, hr, c.sound args mem next hpre r hr, c.framed args mem next hpre r hr⟩

/-- **A byte outside the footprint reads as it did before the call** — the
membership form, `keeps_of_not_mem` at this contract's foot. -/
theorem keeps (c : HelperContract calls sym) {args : List Value} {mem : Mem} {next : Nat}
    (hpre : c.pre args mem next) {r : CallOutcome}
    (hcall : calls sym args mem next = some r) {a : Nat}
    (ha : ∀ q ∈ c.foot args mem next, ¬ (q.1 ≤ a ∧ a < q.1 + q.2)) :
    readByte r.mem a = readByte mem a :=
  c.framed args mem next hpre r hcall a ha

/-- **A word the caller reloads after the call is the word it staged**, when the
word's whole range is outside the footprint: the shape `if.then328.i`'s
`load i64, ptr %outn.i` and `if.then109.i`'s `load i32, ptr %hash1.i.i` have. -/
theorem readBytes_eq (c : HelperContract calls sym) {args : List Value} {mem : Mem}
    {next : Nat} (hpre : c.pre args mem next) {r : CallOutcome}
    (hcall : calls sym args mem next = some r) :
    ∀ {a n : Nat},
      (∀ k, k < n → ∀ q ∈ c.foot args mem next, ¬ (q.1 ≤ a + k ∧ a + k < q.1 + q.2)) →
      readBytes r.mem a n = readBytes mem a n
  | a, 0, _ => rfl
  | a, n + 1, ha => by
      have hhead : readByte r.mem a = readByte mem a :=
        c.keeps hpre hcall (fun q hq => ha 0 (Nat.succ_pos n) q hq)
      have htail := readBytes_eq c hpre hcall (a := a + 1) (n := n) (fun k hk q hq => by
        have h := ha (k + 1) (by omega) q hq
        rwa [show a + (k + 1) = a + 1 + k by omega] at h)
      simp only [readBytes, hhead, htail]

/-- **A frame the callee proves over its own list is one over the caller's view**:
`CallerView` at the caller's regions followed by the footprint. -/
theorem view (c : HelperContract calls sym) {args : List Value} {mem : Mem} {next : Nat}
    (hpre : c.pre args mem next) {r : CallOutcome} {caller : List (Nat × Nat)}
    (hcall : calls sym args mem next = some r) :
    CallerView caller (c.foot args mem next) mem r.mem :=
  CallerView_of_framed (c.framed args mem next hpre r hcall)

end HelperContract

/-! ### The staging predicates

Each `pre` names the argument list the emitted call passes and the words the
callee reads at it, in the shape `JsonStage2Body`'s `stage2*_answers` take.
`s2ScalarValuePre` adds the event stream's room, because `od_scalar_value`'s `none`
arms besides an unreadable word are the reserve's fault (`emitBlobs` or `outTag`
answering `none`) — the source's `__builtin_trap`, which no outcome describes — so
a caller must present a stream that can hold the widest record the token can
produce.  `s2StringBodyPre` adds the escape list's spacing, because the decoded
length's bound is `escapeDecodeGo_length_le`'s and that lemma is about a spaced
list. -/

/-- **The escape list is this body's own positions, in document order** — the
spacing `escapeDecodeGo_length_le` takes.  Stated at the model's own readings, so
it is a property of the caller's staged list rather than a fact about
`s2_string_body`: `base`, `j0`, `ps` and `body` are the four words the body reads,
and the list the decoder is given is the staged list's window over the body's
document range, shifted to body-relative positions. -/
def BodyPositionsSpaced (mem : Mem) (c xj xp : Nat) (nxp p len : Nat) : Prop :=
  ∀ (base j0 : Nat) (ps : List Nat) (body : List UInt8),
    stage2ReadWord mem c 8 = some base →
    stage2ReadWord mem xj 8 = some j0 →
    readLanes32 mem xp nxp = some ps →
    readBytes mem p len = some body →
    Spaced body 0
      (((ps.drop (j0 + ((ps.drop j0).takeWhile (fun q => q < p - base)).length)).takeWhile
        (fun q => q < p - base + len)).map (fun q => q - (p - base)))

/-- Two regions do not meet: one ends at or before the other starts.  This is the
pairwise form of `DisjointRegions`' `Pairwise` step, at two named extents — the
shape a call's staging states for the objects it shares with the callee, and the
shape the memory joins consume. -/
def RegionsApart (a n b m : Nat) : Prop := a + n ≤ b ∨ b + m ≤ a

/-- **`s2_init`'s staging**: the emitted call's five arguments. -/
def s2InitPre (args : List Value) (_mem : Mem) (_next : Nat) : Prop :=
  ∃ (s b ep : Nat) (n nb : BitVec 64),
    args = [.ptr s, .ptr b, .int 64 n, .int 64 nb, .ptr ep]

/-- **`s2_value_pos`'s staging**: the four arguments and the top container's two
stack bytes, unless the depth is zero, where the callee reads nothing. -/
def s2ValuePosPre (args : List Value) (mem : Mem) (_next : Nat) : Prop :=
  ∃ (sp rd : BitVec 32) (ct cs : Nat),
    args = [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] ∧
    (sp.toNat = 0 ∨
      ((∃ c, readByte mem (ct + (sp.toNat - 1)) = some c) ∧
       (∃ s, readByte mem (cs + (sp.toNat - 1)) = some s)))

/-- **`s2_after_value`'s staging**: the four arguments and the top container's type
byte, unless the depth is zero, where the callee reads nothing. -/
def s2AfterValuePre (args : List Value) (mem : Mem) (_next : Nat) : Prop :=
  ∃ (sp : BitVec 32) (rd ct cs : Nat),
    args = [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] ∧
    (sp.toNat = 0 ∨ ∃ c, readByte mem (ct + (sp.toNat - 1)) = some c)

/-- **`s2_string_body`'s staging**: the eight arguments, the five words the
callee reads, the escape list's spacing at the body it is given, and the five
arithmetic facts the body's own 64-bit instructions need.

The last group is the body's, not the model's.  `entry` converts both addresses
with `ptrtoint`, which is `ub` at or above `2 ^ 64`, and subtracts them at
`i64`, while the model's `pos0` is a `Nat` subtraction: `p < 2^64` and
`base ≤ p` are what make the two agree.  `%add = pos0 + len` is a 64-bit add and
the model's window bound is `Nat`, so `p - base + len` must not wrap.  And the
scan's `getelementptr i32` sign-extends its index, which is the forward branch
only below `2 ^ 63`; the scan is entered exactly when the cursor is below the
count, so `j0` and the count are both bounded there.

**The staging's memory facts are reads, and that is enough.**  A body proof that
writes one of these words back needs the write to be a no-op, which is a lemma
composed at the use (`JsonStage2StringBody.stage2ReadWord_writeBytes_self`: a
region a `readBytes` returned is written back in place, byte by byte) rather than
a clause here — the read already says the bytes are present.  The spacing clause
is the only memory clause that had to be stated, because it is the one the
decoded-length bound cannot be derived from a read.

**The five regions, present and pairwise separated — and why presence is not a
convenience.**  `writeByte` appends absent addresses, so write order is
observable — with `ei`, `dst`, `outn` and the record's `e` absent, the body's
order (clear, `dst`, `xj`, slot, `outn`) and the model's (`dst`, `xj`, `outn`,
slot) are different lists, and `r.mem = writeBytes m next slot` fails.  The
two-byte witness is `JsonStage2StringBody.writeBytes_absent_comm_witness`.  So the
clause is the fact that makes the memory equality true, not a strengthening that
eases a proof: the model's write order and the body's meet only where every
region either writes is already present.

The five are the five `s2StringBodyFoot` names, in its order — the cursor word,
the decoded-length word, the decoded window at `dst`, the body's own `%ei` slot at
`next`, and the error record the cursor's second word points at — and the body
writes no other bytes on any arm.  The slot is the caller's staging here for the
reason the joins need it at this memory: the body's `alloca` advances the cursor
and does not populate bytes, so its later clear is the *second* write to the
region rather than the first. -/
def s2StringBodyPre (args : List Value) (mem : Mem) (next : Nat) : Prop :=
  ∃ (c p : Nat) (len : BitVec 64) (dst outn xp xj : Nat) (nxp : BitVec 64)
    (base j0 : Nat) (ps : List Nat) (body : List UInt8) (e : Nat),
    args = [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
      .int 64 nxp] ∧
    stage2ReadWord mem c 8 = some base ∧
    stage2ReadWord mem xj 8 = some j0 ∧
    readLanes32 mem xp nxp.toNat = some ps ∧
    readBytes mem p len.toNat = some body ∧
    stage2ReadWord mem (c + 1112) 8 = some e ∧
    BodyPositionsSpaced mem c xj xp nxp.toNat p len.toNat ∧
    p < 2 ^ 64 ∧
    base ≤ p ∧
    p - base + len.toNat < 2 ^ 64 ∧
    j0 < 2 ^ 63 ∧
    nxp.toNat < 2 ^ 63 ∧
    readBytes mem next 8 ≠ none ∧
    readBytes mem outn 8 ≠ none ∧
    readBytes mem dst len.toNat ≠ none ∧
    readBytes mem e stage2ErrorExtent ≠ none ∧
    RegionsApart xj 8 next 8 ∧
    RegionsApart xj 8 outn 8 ∧
    RegionsApart xj 8 dst len.toNat ∧
    RegionsApart xj 8 e stage2ErrorExtent ∧
    RegionsApart next 8 outn 8 ∧
    RegionsApart next 8 dst len.toNat ∧
    RegionsApart next 8 e stage2ErrorExtent ∧
    RegionsApart outn 8 dst len.toNat ∧
    RegionsApart outn 8 e stage2ErrorExtent ∧
    RegionsApart dst len.toNat e stage2ErrorExtent ∧
    -- the position list and the cursor word do not meet, which is what lets the
    -- scan re-read a lane after writing the cursor
    (∀ k, k < nxp.toNat → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)

/-- **`od_scalar_value`'s staging**: the three arguments; the cursor record's two
pointers; the token's three words; the delivered window (`endp - pos + 5` bytes,
because no literal is longer than five); the stream's three words, with room for
`stage2RecordBytes` more at its cursor. -/
def s2ScalarValuePre (args : List Value) (mem : Mem) (_next : Nat) : Prop :=
  ∃ c t o : Nat, args = [.ptr c, .ptr t, .ptr o] ∧
    ∃ (base e pos endp kind buf len cap : Nat) (win : List UInt8),
      stage2ReadWord mem c 8 = some base ∧
      stage2ReadWord mem (c + 1112) 8 = some e ∧
      stage2ReadWord mem t 8 = some pos ∧
      stage2ReadWord mem (t + 8) 8 = some endp ∧
      stage2ReadWord mem (t + 16) 4 = some kind ∧
      stage2ReadWord mem o 8 = some buf ∧
      stage2ReadWord mem (o + 8) 8 = some len ∧
      stage2ReadWord mem (o + 16) 8 = some cap ∧
      len + stage2RecordBytes ≤ cap ∧
      readBytes mem (base + pos) (max (endp - pos) 5) = some win

/-- **`num_fast_el1`'s staging**: the four arguments and the lexeme they span. -/
def s2NumFastPre (args : List Value) (mem : Mem) (_next : Nat) : Prop :=
  ∃ (p out err : Nat) (n : BitVec 64),
    args = [.ptr p, .int 64 n, .ptr out, .ptr err] ∧
    ∃ lex, readBytes mem p n.toNat = some lex

/-! ### The answers

Each `post` is the answer's shape, and each `foot` the regions the answer may have
written.  A `post` names what the walk's blocks read back: the returned word, and
the memory's shape at the words they reload.  A `foot` is a list of regions built
from the call's own arguments — so a caller checks membership by `simp` at the
concrete list — and where an arm's write is narrower than its slot the wider slot
is named and the narrower read is a corollary of the model's spec. -/

/-! #### `s2_init`: the staging record -/

/-- **`s2_init`'s answer.**  The `S2` record at `s`, the five fields the emitted
call passes and the ten the initialiser clears or sets to `NULL`.  `s2_init` is a
`void` call, so the returned word carries nothing. -/
def s2InitPost (args : List Value) (mem : Mem) (next : Nat) (r : CallOutcome) : Prop :=
  match args with
  | [.ptr s, .ptr b, .int 64 n, .int 64 nb, .ptr ep] =>
      r.ret = voidRet ∧
      r.mem = stage2WriteStores mem (s2InitStores s b n.toNat nb.toNat ep) ∧
      r.next = next
  | _ => False

/-- The one object `s2_init` writes: the `S2` record at its first argument. -/
def s2InitFoot (args : List Value) (_mem : Mem) (_next : Nat) : List (Nat × Nat) :=
  match args with
  | [.ptr s, .ptr _, .int 64 _, .int 64 _, .ptr _] => [(s, stage2StateExtent)]
  | _ => []

/-! #### `s2_value_pos`: a test, no write -/

/-- **`s2_value_pos`'s answer**: the value-position test's bit, and the caller's
memory back. -/
def s2ValuePosPost (args : List Value) (mem : Mem) (next : Nat)
    (r : CallOutcome) : Prop :=
  match args with
  | [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] =>
      ∃ v, stage2ValuePos mem sp.toNat rd.toNat ct cs = some v ∧
        r.ret = .int 32 (BitVec.ofNat 32 v) ∧ r.mem = mem ∧ r.next = next
  | _ => False

/-- `s2_value_pos` writes nothing. -/
def s2ValuePosFoot (_args : List Value) (_mem : Mem) (_next : Nat) : List (Nat × Nat) :=
  []

/-! #### `s2_after_value`: one flag or one stack byte -/

/-- **`s2_after_value`'s answer**: the caller's memory with the top container's
state advanced, or the root flag set at depth zero. -/
def s2AfterValuePost (args : List Value) (mem : Mem) (next : Nat)
    (r : CallOutcome) : Prop :=
  match args with
  | [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] =>
      ∃ m, stage2AfterValue mem sp.toNat rd ct cs = some m ∧
        r.ret = voidRet ∧ r.mem = m ∧ r.next = next
  | _ => False

/-- The one byte `s2_after_value` writes: the root flag at depth zero, the top
container's state byte above it. -/
def s2AfterValueFoot (args : List Value) (_mem : Mem) (_next : Nat) :
    List (Nat × Nat) :=
  match args with
  | [.int 32 sp, .ptr rd, .ptr _, .ptr cs] =>
      if sp.toNat = 0 then [(rd, 4)] else [(cs + (sp.toNat - 1), 1)]
  | _ => []

/-! #### `s2_string_body`: the decoded body -/

/-- **`s2_string_body`'s answer**: the form it took (`0` refusing, `1` the body
itself, `2` the escaped form) and the memory it left — the cursor word, the
decoded-length word and, on the escaped form, the decoded prefix at `dst`. -/
def s2StringBodyPost (args : List Value) (mem : Mem) (next : Nat)
    (r : CallOutcome) : Prop :=
  match args with
  | [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj, .int 64 nxp] =>
      ∃ (m : Mem) (form : Nat) (slot : List UInt8),
        stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat =
          some (m, form, slot) ∧
        r.ret = .int 32 (BitVec.ofNat 32 form) ∧
        r.mem = writeBytes m next slot ∧
        r.next = next + 8
  | _ => False

/-- **`s2_string_body`'s writes**: the cursor word, the decoded-length word, the
decoded prefix in a slot `len` wide, and — where the cursor record's error pointer
is readable — the error record it names.  The error region is in the list on the
accepting arms too, because the footprint is read before the call and cannot see
which arm ran; `stage2ErrorExtent` is the record's staged extent and the refusal
writes sixteen of its bytes. -/
def s2StringBodyFoot (args : List Value) (mem : Mem) (next : Nat) :
    List (Nat × Nat) :=
  match args with
  | [.ptr c, .ptr _, .int 64 len, .ptr dst, .ptr outn, .ptr _, .ptr xj, .int 64 _] =>
      [(xj, 8), (outn, 8), (dst, len.toNat), (next, 8)] ++
        (match stage2ReadWord mem (c + 1112) 8 with
         | some e => [(e, stage2ErrorExtent)]
         | none => [])
  | _ => []

/-! #### `od_scalar_value`: the appended record -/

/-- **The record an emitting arm appended**, at the caller's stream: the bytes at
the stream's cursor, and the cursor word advanced by the record's width.  The
record is given as an `EventRecord`, because that is the vocabulary the walk's
trace carries: `encodedBytes` is what the emitter writes, `encodedSize` the width
the cursor advances by.  The two `stage2ReadWord` clauses fix the record's base
and the cursor's old value, so the conclusion is about the caller's own stream
and not about a copy. -/
def s2ScalarValueAppend (mem m : Mem) (o : Nat) (rec : List UInt8) : Prop :=
  ∃ buf len : Nat,
    stage2ReadWord mem o 8 = some buf ∧
    stage2ReadWord mem (o + 8) 8 = some len ∧
    m = writeBytes (writeBytes mem (buf + len) rec) (o + 8)
      (wordBytes 8 (len + rec.length))

/-- **`od_scalar_value`'s answer**: `1` when it appended the token's record and
`0` when it refused, with the stream's cursor written back (`out_raw`'s
`o->len += n`) and the refusal's offset in the error record.

The second conjunct is the shape of an emission: when the call appended a record,
the memory is the caller's with that record's bytes at the stream's cursor and the
cursor word advanced by its width.  The first conjunct does not say *which*
record the arm wrote; without the second a link that owns the trace could not
advance it, because `s2ScalarValue`'s model hides the arm behind one equation. -/
def s2ScalarValuePost (args : List Value) (mem : Mem) (next : Nat)
    (r : CallOutcome) : Prop :=
  match args with
  | [.ptr c, .ptr t, .ptr o] =>
      (∃ (m : Mem) (ok : Nat),
        stage2ScalarValue mem c t o next = some ⟨.int 32 (BitVec.ofNat 32 ok), m, next⟩ ∧
        r.ret = .int 32 (BitVec.ofNat 32 ok) ∧ r.mem = m ∧ r.next = next) ∧
      (r.ret = .int 32 (BitVec.ofNat 32 1) →
        ∃ ev : EventRecord, s2ScalarValueAppend mem r.mem o ev.encodedBytes)
  | _ => False

/-- **`od_scalar_value`'s writes**: the stream's cursor word, the slot the record
is appended in at that cursor (`stage2RecordBytes` wide, the widest record), and
— where the cursor record's error pointer is readable — the error record.  The
record's buffer and cursor are read from the stream, so the slot is the call's own
`buf + len` and not a constant. -/
def s2ScalarValueFoot (args : List Value) (mem : Mem) (_next : Nat) :
    List (Nat × Nat) :=
  match args with
  | [.ptr c, .ptr _, .ptr o] =>
      [(o + 8, 8)] ++
        (match stage2ReadWord mem o 8, stage2ReadWord mem (o + 8) 8 with
         | some buf, some len => [(buf + len, stage2RecordBytes)]
         | _, _ => []) ++
        (match stage2ReadWord mem (c + 1112) 8 with
         | some e => [(e, stage2ErrorExtent)]
         | none => [])
  | _ => []

/-! #### `num_fast_el1`: the conversion, or the refusal offset -/

/-- **`num_fast_el1`'s answer**, with both exits.  The accepted lexeme's eight
bytes at `out` (`numFastEmitted`, whose `strtodSpec` clause `JsonStage2Body`
proves), or the refused position at `err` with its bound
(`numLexScan_fst_le`).  The two writes are disjoint by construction: the function
writes the value only where it accepts and the offset only where it refuses. -/
def s2NumFastPost (args : List Value) (mem : Mem) (next : Nat)
    (r : CallOutcome) : Prop :=
  match args with
  | [.ptr p, .int 64 n, .ptr out, .ptr err] =>
      ∃ lex, readBytes mem p n.toNat = some lex ∧
        ((((numLexScan lex).2 = true) ∧
          r.ret = .int 32 (BitVec.ofNat 32 1) ∧
          r.mem = writeBytes mem out
            (wordBytes 8 (numFastEmitted (ByteString.literal lex)).toBits) ∧
          r.next = next)
        ∨ (((numLexScan lex).2 = false) ∧
          r.ret = .int 32 (BitVec.ofNat 32 0) ∧
          r.mem = writeBytes mem err (wordBytes 8 (numLexScan lex).1) ∧
          r.next = next ∧ (numLexScan lex).1 ≤ n.toNat))
  | _ => False

/-- **`num_fast_el1`'s two slots**: the value and the offset.  One is written per
call, so the accepting arm's `err` and the refusing arm's `out` are the caller's
and both are named because the footprint cannot see which arm ran. -/
def s2NumFastFoot (args : List Value) (_mem : Mem) (_next : Nat) : List (Nat × Nat) :=
  match args with
  | [.ptr _, .int 64 _, .ptr out, .ptr err] => [(out, 8), (err, 8)]
  | _ => []

/-! ### Two write frames the models use

`od_scalar_value`'s refusal and the literal check are the two places a model's
write is not a single `writeBytes` at a caller-supplied address: `od_fail` stores
the record's `ok` word and its offset, and the literal check compares up to five
bytes. -/

/-- **`od_fail`'s frame**: the record's two stores, inside one region sixteen bytes
wide. -/
theorem stage2ErrSet_frame {mem : Mem} {R : List (Nat × Nat)} {e off : Nat}
    (hin : ∃ q ∈ R, q.1 ≤ e ∧ e + 16 ≤ q.1 + q.2) :
    UnchangedOutside mem (stage2ErrSet mem e off) R := by
  unfold stage2ErrSet
  exact (((UnchangedOutside.refl' mem R).write_le (a := e) (w := 16)
    (by obtain ⟨q, hq, lo, hi⟩ := hin; exact ⟨q, hq, lo, by omega⟩)
    (by simp [wordBytes, natToBytes_length])).write_le (a := e + 8) (w := 8)
    (by obtain ⟨q, hq, lo, hi⟩ := hin; exact ⟨q, hq, by omega, by omega⟩)
    (by simp [wordBytes, natToBytes_length]))

/-- **The refusal record's three stores, inside one region.**  `err_set` writes
`ok`, `off` and the message pointer, and the two helpers' refusal paths emit all
three; the region is the record's staged extent, twenty-four bytes, which is what
the walk's staged-writes list already claims. -/
theorem stage2ErrSetMsg_frame {mem : Mem} {R : List (Nat × Nat)} {e off msg : Nat}
    (hin : ∃ q ∈ R, q.1 ≤ e ∧ e + 24 ≤ q.1 + q.2) :
    UnchangedOutside mem (stage2ErrSetMsg mem e off msg) R := by
  unfold stage2ErrSetMsg
  exact (stage2ErrSet_frame (by obtain ⟨q, hq, lo, hi⟩ := hin; exact ⟨q, hq, lo, by omega⟩)).write_le
    (a := e + 16) (w := 8)
    (by obtain ⟨q, hq, lo, hi⟩ := hin; exact ⟨q, hq, by omega, by omega⟩)
    (by simp [wordBytes, natToBytes_length])

/-- **The literal bytes a token kind stands for are at most five.** -/
theorem stage2Literal_length {kind : Nat} {lit : List UInt8}
    (h : stage2Literal kind = some lit) : lit.length ≤ 5 := by
  unfold stage2Literal at h
  split at h
  · obtain rfl := Option.some.inj h; simp
  · split at h
    · obtain rfl := Option.some.inj h; simp
    · split at h
      · obtain rfl := Option.some.inj h; simp
      · simp at h

/-! ### The six contracts

Each instance is three facts at the emitted call: the staging makes the call
resolve, the answer it resolves to satisfies the post, and the memory it hands
back is the caller's outside the footprint.

A proof here reads the model at the call's own argument list and keeps the
outcome *abstract*: it derives `r`'s three fields from the call's value rather
than substituting the value for `r`.  That is not a stylistic choice.  A post
destructured at a literal outcome — `⟨voidRet, stage2WriteStores mem stores,
next⟩` — puts a fifteen-store recursive term in the scrutinee of every
projection the conjunction mentions, and the reducer then walks the store list
once for each field; the axiom pins below are the same, but the heartbeat cost is
three orders of magnitude larger.  Deriving `r.mem = …`, `r.ret = …` and
`r.next = …` as separate equations and assembling the post at the abstract `r`
avoids it: the equation `r = ⟨ret, mem, next⟩` is derived once, and each field
is read by rewriting with it in a goal that still names `r`.  The same reason
keeps the footprints out of the branch analysis: they are stated as a local
equation (`hfoot`) from the arguments the staging already supplies rather than
by letting the reducer unfold the match. -/

/-! #### `s2_init`: the staging record -/

/-- Every store `s2InitStores` makes lies inside the `S2` record's extent. -/
theorem s2InitStores_inside (s b n nb ep : Nat) {p : Nat × List UInt8}
    (hp : p ∈ s2InitStores s b n nb ep) :
    s ≤ p.1 ∧ p.1 + p.2.length ≤ s + stage2StateExtent := by
  simp only [s2InitStores, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    obtain rfl := h
    simp only [wordBytes, natToBytes_length, stage2StateExtent]
    constructor <;> omega

/-- **`s2_init`'s reply** at the five arguments the emitted call passes. -/
theorem s2Init_reply {mem : Mem} {next : Nat} {s b ep : Nat} {n nb : BitVec 64} :
    stage2Calls stage2SubCalls "s2_init"
        [.ptr s, .ptr b, .int 64 n, .int 64 nb, .ptr ep] mem next =
      some ⟨voidRet, stage2WriteStores mem (s2InitStores s b n.toNat nb.toNat ep),
        next⟩ :=
  rfl

theorem s2Init_answers {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2InitPre args mem next) :
    ∃ r, stage2Calls stage2SubCalls "s2_init" args mem next = some r := by
  obtain ⟨s, b, ep, n, nb, rfl⟩ := hpre
  exact ⟨_, s2Init_reply⟩

theorem s2Init_sound {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2InitPre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "s2_init" args mem next = some r) :
    s2InitPost args mem next r := by
  obtain ⟨s, b, ep, n, nb, rfl⟩ := hpre
  have hr : r = ⟨voidRet,
      stage2WriteStores mem (s2InitStores s b n.toNat nb.toNat ep), next⟩ :=
    Option.some.inj (h.symm.trans s2Init_reply)
  have h1 : r.ret = voidRet := by rw [hr]
  have h2 : r.mem = stage2WriteStores mem (s2InitStores s b n.toNat nb.toNat ep) := by
    rw [hr]
  have h3 : r.next = next := by rw [hr]
  exact ⟨h1, h2, h3⟩

theorem s2Init_framed {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2InitPre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "s2_init" args mem next = some r) :
    UnchangedOutside mem r.mem (s2InitFoot args mem next) := by
  obtain ⟨s, b, ep, n, nb, rfl⟩ := hpre
  have hmem : r.mem =
      stage2WriteStores mem (s2InitStores s b n.toNat nb.toNat ep) := by
    have hr : r = ⟨voidRet,
        stage2WriteStores mem (s2InitStores s b n.toNat nb.toNat ep), next⟩ :=
      Option.some.inj (h.symm.trans s2Init_reply)
    rw [hr]
  rw [hmem]
  refine stage2WriteStores_frame ?_
  intro p hp
  exact ⟨(s, stage2StateExtent), List.mem_cons_self ..,
    s2InitStores_inside s b n.toNat nb.toNat ep hp⟩

/-- **`s2_init`'s contract**: the `S2` record's initialisation. -/
def s2InitContract : HelperContract (stage2Calls stage2SubCalls) "s2_init" where
  pre := s2InitPre
  post := s2InitPost
  foot := s2InitFoot
  answers := fun _ _ _ hpre => s2Init_answers hpre
  sound := fun _ _ _ hpre _ h => s2Init_sound hpre h
  framed := fun _ _ _ hpre _ h => s2Init_framed hpre h

/-! #### `s2_value_pos`: the test -/

/-- **`s2_value_pos`'s reply** at the four arguments the emitted call passes. -/
theorem s2ValuePos_reply {mem : Mem} {next : Nat} {sp rd : BitVec 32} {ct cs : Nat} :
    stage2Calls stage2SubCalls "s2_value_pos" [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs]
        mem next =
      (stage2ValuePos mem sp.toNat rd.toNat ct cs).map
        (fun v => (⟨.int 32 (BitVec.ofNat 32 v), mem, next⟩ : CallOutcome)) :=
  rfl

theorem s2ValuePos_answers {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2ValuePosPre args mem next) :
    ∃ r, stage2Calls stage2SubCalls "s2_value_pos" args mem next = some r := by
  obtain ⟨sp, rd, ct, cs, rfl, hcase⟩ := hpre
  rw [s2ValuePos_reply]
  by_cases h0 : sp.toNat = 0
  · obtain ⟨v, hv⟩ := stage2ValuePos_zero mem rd.toNat ct cs
    rw [h0, hv]
    exact ⟨_, rfl⟩
  · rcases hcase with h1 | ⟨⟨c, hc⟩, ⟨s, hs⟩⟩
    · exact absurd h1 h0
    · obtain ⟨v, hv⟩ := stage2ValuePos_answers mem sp.toNat rd.toNat ct cs h0 hc hs
      rw [hv]
      exact ⟨_, rfl⟩

theorem s2ValuePos_sound {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2ValuePosPre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "s2_value_pos" args mem next = some r) :
    s2ValuePosPost args mem next r := by
  obtain ⟨sp, rd, ct, cs, rfl, -⟩ := hpre
  cases hv : stage2ValuePos mem sp.toNat rd.toNat ct cs with
  | none =>
      rw [s2ValuePos_reply, hv] at h
      cases h
  | some v =>
      have hr : r = ⟨.int 32 (BitVec.ofNat 32 v), mem, next⟩ :=
        Option.some.inj (h.symm.trans (by rw [s2ValuePos_reply, hv]; rfl))
      refine ⟨v, hv, ?_, ?_, ?_⟩
      · rw [hr]
      · rw [hr]
      · rw [hr]

theorem s2ValuePos_framed {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2ValuePosPre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "s2_value_pos" args mem next = some r) :
    UnchangedOutside mem r.mem (s2ValuePosFoot args mem next) := by
  obtain ⟨sp, rd, ct, cs, rfl, -⟩ := hpre
  cases hv : stage2ValuePos mem sp.toNat rd.toNat ct cs with
  | none =>
      rw [s2ValuePos_reply, hv] at h
      cases h
  | some v =>
      have hmem : r.mem = mem := by
        have hr : r = ⟨.int 32 (BitVec.ofNat 32 v), mem, next⟩ :=
          Option.some.inj (h.symm.trans (by rw [s2ValuePos_reply, hv]; rfl))
        rw [hr]
      rw [hmem]
      exact UnchangedOutside.refl' mem []

/-- **`s2_value_pos`'s contract**: the value-position test. -/
def s2ValuePosContract : HelperContract (stage2Calls stage2SubCalls) "s2_value_pos" where
  pre := s2ValuePosPre
  post := s2ValuePosPost
  foot := s2ValuePosFoot
  answers := fun _ _ _ hpre => s2ValuePos_answers hpre
  sound := fun _ _ _ hpre _ h => s2ValuePos_sound hpre h
  framed := fun _ _ _ hpre _ h => s2ValuePos_framed hpre h

/-! #### `s2_after_value`: one flag or one stack byte -/

/-- **`s2_after_value`'s reply** at the four arguments the emitted call passes. -/
theorem s2AfterValue_reply {mem : Mem} {next : Nat} {sp : BitVec 32} {rd ct cs : Nat} :
    stage2Calls stage2SubCalls "s2_after_value" [.int 32 sp, .ptr rd, .ptr ct, .ptr cs]
        mem next =
      (stage2AfterValue mem sp.toNat rd ct cs).map
        (fun m => (⟨voidRet, m, next⟩ : CallOutcome)) :=
  rfl

theorem s2AfterValue_answers {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2AfterValuePre args mem next) :
    ∃ r, stage2Calls stage2SubCalls "s2_after_value" args mem next = some r := by
  obtain ⟨sp, rd, ct, cs, rfl, hcase⟩ := hpre
  rw [s2AfterValue_reply]
  by_cases h0 : sp.toNat = 0
  · have hm : stage2AfterValue mem sp.toNat rd ct cs =
        some (writeBytes mem rd (wordBytes 4 1)) := by
      rw [stage2AfterValue]
      simp only [h0, ↓reduceIte]
    rw [hm]
    exact ⟨_, rfl⟩
  · rcases hcase with h1 | ⟨c, hc⟩
    · exact absurd h1 h0
    · obtain ⟨m, hm⟩ := stage2AfterValue_answers mem sp.toNat rd ct cs h0 hc
      rw [hm]
      exact ⟨_, rfl⟩

theorem s2AfterValue_sound {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2AfterValuePre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "s2_after_value" args mem next = some r) :
    s2AfterValuePost args mem next r := by
  obtain ⟨sp, rd, ct, cs, rfl, -⟩ := hpre
  cases hm : stage2AfterValue mem sp.toNat rd ct cs with
  | none =>
      rw [s2AfterValue_reply, hm] at h
      cases h
  | some m =>
      have hr : r = ⟨voidRet, m, next⟩ :=
        Option.some.inj (h.symm.trans (by rw [s2AfterValue_reply, hm]; rfl))
      refine ⟨m, hm, ?_, ?_, ?_⟩
      · rw [hr]
      · rw [hr]
      · rw [hr]

theorem s2AfterValue_framed {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2AfterValuePre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "s2_after_value" args mem next = some r) :
    UnchangedOutside mem r.mem (s2AfterValueFoot args mem next) := by
  obtain ⟨sp, rd, ct, cs, rfl, -⟩ := hpre
  cases hm : stage2AfterValue mem sp.toNat rd ct cs with
  | none =>
      rw [s2AfterValue_reply, hm] at h
      cases h
  | some m =>
      have hmem : r.mem = m := by
        have hr : r = ⟨voidRet, m, next⟩ :=
          Option.some.inj (h.symm.trans (by rw [s2AfterValue_reply, hm]; rfl))
        rw [hr]
      rw [hmem]
      have hfoot : s2AfterValueFoot [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next =
          (if sp.toNat = 0 then [(rd, 4)] else [(cs + (sp.toNat - 1), 1)]) := rfl
      rw [hfoot]
      unfold stage2AfterValue at hm
      by_cases h0 : sp.toNat = 0
      · simp only [h0, ↓reduceIte] at hm ⊢
        obtain rfl := (Option.some.inj hm).symm
        exact (UnchangedOutside.refl' mem [(rd, 4)]).write_le (a := rd) (w := 4)
          ⟨(rd, 4), List.mem_cons_self .., le_rfl, le_rfl⟩
          (by simp [wordBytes, natToBytes_length])
      · simp only [h0, ↓reduceIte] at hm ⊢
        cases hc : readByte mem (ct + (sp.toNat - 1)) with
        | none => rw [hc] at hm; cases hm
        | some c =>
            rw [hc] at hm
            obtain rfl := (Option.some.inj hm).symm
            exact (UnchangedOutside.refl' mem [(cs + (sp.toNat - 1), 1)]).write_le
              (a := cs + (sp.toNat - 1)) (w := 1)
              ⟨(cs + (sp.toNat - 1), 1), List.mem_cons_self .., le_rfl, le_rfl⟩
              (by simp)

/-- **`s2_after_value`'s contract**: the top container's state after a value. -/
def s2AfterValueContract :
    HelperContract (stage2Calls stage2SubCalls) "s2_after_value" where
  pre := s2AfterValuePre
  post := s2AfterValuePost
  foot := s2AfterValueFoot
  answers := fun _ _ _ hpre => s2AfterValue_answers hpre
  sound := fun _ _ _ hpre _ h => s2AfterValue_sound hpre h
  framed := fun _ _ _ hpre _ h => s2AfterValue_framed hpre h

/-! #### `s2_string_body`: the decoded body -/

/-- **`s2_string_body`'s reply** at the eight arguments the emitted call passes. -/
theorem s2StringBody_reply {mem : Mem} {next : Nat} {c p dst outn xp xj : Nat}
    {len nxp : BitVec 64} {m : Mem} {form : Nat} {slot : List UInt8}
    (hm : stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat =
      some (m, form, slot)) :
    stage2Calls stage2SubCalls "s2_string_body"
        [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
          .int 64 nxp] mem next =
      some ⟨.int 32 (BitVec.ofNat 32 form), writeBytes m next slot, next + 8⟩ := by
  rw [stage2Calls_s2_string_body, stage2StringBodyCall, hm]
  rfl

/-- **`s2_string_body`'s silence**: a model that answers nothing is an unresolved
call. -/
theorem s2StringBody_none {mem : Mem} {next : Nat} {c p dst outn xp xj : Nat}
    {len nxp : BitVec 64}
    (hm : stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat = none) :
    stage2Calls stage2SubCalls "s2_string_body"
        [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
          .int 64 nxp] mem next = none := by
  rw [stage2Calls_s2_string_body, stage2StringBodyCall, hm]
  rfl

theorem s2StringBody_answers {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2StringBodyPre args mem next) :
    ∃ r, stage2Calls stage2SubCalls "s2_string_body" args mem next = some r := by
  obtain ⟨c, p, len, dst, outn, xp, xj, nxp, _, _, _, _, _, rfl, hbase, hj0, hps,
    hbody, he, -⟩ := hpre
  obtain ⟨pr, hpr⟩ := stage2StringBody_answers mem c p len.toNat dst outn xp xj
    nxp.toNat hbase hj0 hps hbody he
  exact ⟨_, s2StringBody_reply hpr⟩

theorem s2StringBody_sound {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2StringBodyPre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "s2_string_body" args mem next = some r) :
    s2StringBodyPost args mem next r := by
  obtain ⟨c, p, len, dst, outn, xp, xj, nxp, _, _, _, _, _, rfl, -⟩ := hpre
  cases hm : stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat with
  | none =>
      rw [s2StringBody_none hm] at h
      cases h
  | some pr =>
      obtain ⟨m, form, slot⟩ := pr
      have hr : r = ⟨.int 32 (BitVec.ofNat 32 form), writeBytes m next slot, next + 8⟩ :=
        Option.some.inj (h.symm.trans (s2StringBody_reply hm))
      refine ⟨m, form, slot, hm, ?_, ?_, ?_⟩
      · rw [hr]
      · rw [hr]
      · rw [hr]

theorem s2StringBody_framed {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2StringBodyPre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "s2_string_body" args mem next = some r) :
    UnchangedOutside mem r.mem (s2StringBodyFoot args mem next) := by
  obtain ⟨c, p, len, dst, outn, xp, xj, nxp, base, j0, ps, body, e, rfl, hbase, hj0,
    hps, hbody, he, hspace, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hpre
  cases hm : stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat with
  | none =>
      rw [s2StringBody_none hm] at h
      cases h
  | some pr =>
      obtain ⟨m, form, slot⟩ := pr
      have hmem : r.mem = writeBytes m next slot := by
        have hr : r = ⟨.int 32 (BitVec.ofNat 32 form), writeBytes m next slot, next + 8⟩ :=
          Option.some.inj (h.symm.trans (s2StringBody_reply hm))
        rw [hr]
      rw [hmem]
      have hfoot : s2StringBodyFoot [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn,
          .ptr xp, .ptr xj, .int 64 nxp] mem next =
          ([(xj, 8), (outn, 8), (dst, len.toNat), (next, 8)] ++
            [(e, stage2ErrorExtent)]) := by
        simp only [s2StringBodyFoot, he]
      rw [hfoot]
      unfold stage2StringBody at hm
      simp only [hbase, hj0, hps, he] at hm
      split at hm
      · have hinj := Option.some.inj hm
        simp only [Prod.mk.injEq] at hinj
        obtain ⟨rfl, rfl, rfl⟩ := hinj
        exact (((UnchangedOutside.refl' mem _).write_le (a := xj) (w := 8)
          ⟨(xj, 8), by simp, le_rfl, le_rfl⟩
          (by simp [wordBytes, natToBytes_length])).write_le (a := outn) (w := 8)
          ⟨(outn, 8), by simp, le_rfl, le_rfl⟩
          (by simp [wordBytes, natToBytes_length])).write_le (a := next) (w := 8)
          ⟨(next, 8), by simp, le_rfl, le_rfl⟩ (by simp)
      · split at hm
        · simp at hm
        · rename_i body' hbody'
          split at hm
          · rename_i out k hdec
            have hinj := Option.some.inj hm
            simp only [Prod.mk.injEq] at hinj
            obtain ⟨rfl, rfl, rfl⟩ := hinj
            have hlen : out.length ≤ len.toNat := by
              have hle := escapeDecodeGo_length_le body'
                (hspace base j0 ps body' hbase hj0 hps hbody') 0 [] out k hdec
              have hbl : body'.length = len.toNat :=
                JsonEntrySteps.readBytes_length mem p len.toNat hbody'
              simp only [List.length_nil, Nat.zero_add] at hle
              omega
            exact ((((UnchangedOutside.refl' mem _).write_le (a := dst) (w := len.toNat)
              ⟨(dst, len.toNat), by simp, le_rfl, le_rfl⟩ hlen).write_le
              (a := xj) (w := 8) ⟨(xj, 8), by simp, le_rfl, le_rfl⟩
              (by simp [wordBytes, natToBytes_length])).write_le (a := outn) (w := 8)
              ⟨(outn, 8), by simp, le_rfl, le_rfl⟩
              (by simp [wordBytes, natToBytes_length])).write_le (a := next) (w := 8)
              ⟨(next, 8), by simp, le_rfl, le_rfl⟩
              (by simp [wordBytes, natToBytes_length])
          · rename_i off k href
            have hinj := Option.some.inj hm
            simp only [Prod.mk.injEq] at hinj
            obtain ⟨rfl, rfl, rfl⟩ := hinj
            exact ((stage2ErrSetMsg_frame
              (R := [(xj, 8), (outn, 8), (dst, len.toNat), (next, 8)] ++
                [(e, stage2ErrorExtent)])
              ⟨(e, stage2ErrorExtent), by simp, le_rfl, le_rfl⟩).write_le (a := xj) (w := 8)
              ⟨(xj, 8), by simp, le_rfl, le_rfl⟩
              (by simp [wordBytes, natToBytes_length])).write_le (a := next) (w := 8)
              ⟨(next, 8), by simp, le_rfl, le_rfl⟩
              (by simp [wordBytes, natToBytes_length])

/-- **`s2_string_body`'s contract**: the decoded body. -/
def s2StringBodyContract :
    HelperContract (stage2Calls stage2SubCalls) "s2_string_body" where
  pre := s2StringBodyPre
  post := s2StringBodyPost
  foot := s2StringBodyFoot
  answers := fun _ _ _ hpre => s2StringBody_answers hpre
  sound := fun _ _ _ hpre _ h => s2StringBody_sound hpre h
  framed := fun _ _ _ hpre _ h => s2StringBody_framed hpre h

/-- **The decoded length is inside the body's document extent** — the datum the
walk advances the arena's cursor by.  On the two accepting forms the model writes
the length at `outn`: the body-itself form's is `len`, and the escaped form's is
`escapeDecodeGo_length_le`'s at the caller's spaced list.  The refusal form leaves
the word alone, which is why the form is a hypothesis rather than a conclusion. -/
theorem s2StringBody_outn_le {mem : Mem} {c p dst outn xp xj : Nat} {len nxp : BitVec 64}
    {m : Mem} {form : Nat} {slot : List UInt8}
    (hm : stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat = some (m, form, slot))
    (hspace : BodyPositionsSpaced mem c xj xp nxp.toNat p len.toNat)
    (hform : form ≠ 0) :
    ∃ on : Nat, readBytes m outn 8 = some (wordBytes 8 on) ∧ on ≤ len.toNat := by
  unfold stage2StringBody at hm
  split at hm
  · rename_i base j0 ps hbase hj0 hps
    dsimp only at hm
    split at hm
    · have hinj := Option.some.inj hm
      simp only [Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, -⟩ := hinj
      refine ⟨len.toNat, ?_, le_rfl⟩
      exact readBytes_wordBytes_same (addr := outn) (v := len.toNat)
    · split at hm
      · simp at hm
      · rename_i body hbody
        split at hm
        · rename_i out k hdec
          have hinj := Option.some.inj hm
          simp only [Prod.mk.injEq] at hinj
          obtain ⟨rfl, rfl, -⟩ := hinj
          refine ⟨out.length, ?_, ?_⟩
          · exact readBytes_wordBytes_same (addr := outn) (v := out.length)
          · have hle := escapeDecodeGo_length_le body
              (hspace base j0 ps body hbase hj0 hps hbody) 0 [] out k hdec
            have hbl : body.length = len.toNat :=
              JsonEntrySteps.readBytes_length mem p len.toNat hbody
            simp only [List.length_nil, Nat.zero_add] at hle
            omega
        · rename_i off k href
          split at hm
          · have hinj := Option.some.inj hm
            simp only [Prod.mk.injEq] at hinj
            obtain ⟨rfl, rfl, -⟩ := hinj
            exact absurd rfl hform
          · simp at hm
  · simp at hm

/-! #### `od_scalar_value`: the appended record -/

/-- **A shorter read at one address is a prefix of a longer one there.**  The
delivered window is the token's `endp - pos` bytes plus the five a literal check
reads; this reads the token's own window out of it. -/
theorem readBytes_take_prefix {mem : Mem} {a n m : Nat} {bs : List UInt8}
    (hnm : n ≤ m) (h : readBytes mem a m = some bs) :
    readBytes mem a n = some (bs.take n) := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hnm
  exact (readBytes_split mem a n k h).1

/-- **A blob that fits its reserve is written.**  `outBlob`'s `none` is the
reserve's refusal, so a caller that shows the blob inside the remaining capacity
has the write. -/
theorem outBlob_complete {mem : Mem} {ev len cap : Nat} {bs : List UInt8}
    (h : len + bs.length ≤ cap) : ∃ p, outBlob mem ev len cap bs = some p := by
  unfold outBlob
  by_cases hc : len + bs.length ≤ cap
  · simp only [hc, ↓reduceIte]
    exact ⟨_, rfl⟩
  · exact absurd h hc

/-- **A fold whose every blob fits its reserve is written.**  The staging's room is
stated at the widest record, and this is what turns that room into the fold's
answer: `emitBlobs`'s `none` is the reserve's refusal at one of the blobs. -/
theorem emitBlobs_complete {mem : Mem} {ev len cap : Nat} {blobs : List (List UInt8)}
    (h : len + blobs.flatten.length ≤ cap) :
    ∃ p, emitBlobs mem ev len cap blobs = some p := by
  induction blobs generalizing mem len with
  | nil => exact ⟨_, rfl⟩
  | cons b bs ih =>
      rw [emitBlobs_cons]
      have hb : len + b.length ≤ cap := by
        simp only [List.flatten_cons, List.length_append] at h
        omega
      obtain ⟨p, hp⟩ := outBlob_complete (mem := mem) (ev := ev) (len := len) (cap := cap) hb
      obtain ⟨p1, p2⟩ := p
      rw [hp]
      obtain ⟨-, hl⟩ := outBlob_spec hp
      obtain ⟨q, hq⟩ := ih (mem := p1) (len := p2) (by
        rw [hl]
        simp only [List.flatten_cons, List.length_append] at h
        omega)
      exact ⟨q, hq⟩

theorem s2ScalarValue_answers {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2ScalarValuePre args mem next) :
    ∃ r, stage2Calls stage2SubCalls "od_scalar_value" args mem next = some r := by
  obtain ⟨c, t, o, rfl, base, e, pos, endp, kind, buf, len, cap, win, hbase, he, hpos,
    hend, hkind, hbuf, hlen, hcap, hroom, hwin⟩ := hpre
  rw [stage2Calls_od_scalar_value]
  unfold stage2ScalarValueCall stage2ScalarValue
  simp only [hbase, he, hpos, hend, hkind]
  have hlex : readBytes mem (base + pos) (endp - pos) =
      some (win.take (endp - pos)) :=
    readBytes_take_prefix (Nat.le_max_left _ _) hwin
  by_cases h0 : kind = 0
  · simp only [h0, ↓reduceIte]
    exact ⟨_, rfl⟩
  · simp only [h0, ↓reduceIte]
    by_cases h7 : kind = 7
    · simp only [h7, ↓reduceIte]
      simp only [hlex]
      by_cases hscan : (numLexScan (win.take (endp - pos))).2 = true
      · simp only [hscan]
        simp only [hbuf, hlen, hcap]
        obtain ⟨p, hp⟩ := emitBlobs_complete (mem := mem) (ev := buf) (len := len) (cap := cap)
          (blobs := numberRecord
            ((numFastEmitted (ByteString.literal (win.take (endp - pos)))).toBits))
          (by
            have hw := numberRecord_le
              ((numFastEmitted (ByteString.literal (win.take (endp - pos)))).toBits)
            omega)
        rw [hp]
        exact ⟨_, rfl⟩
      · simp only [hscan]
        exact ⟨_, rfl⟩
    · simp only [h7, ↓reduceIte]
      cases hlit : stage2Literal kind with
      | none => exact ⟨_, rfl⟩
      | some lit =>
          have hlit5 := stage2Literal_length hlit
          have hgot : readBytes mem (base + pos) lit.length =
              some (win.take lit.length) :=
            readBytes_take_prefix (le_trans hlit5 (Nat.le_max_right _ _)) hwin
          simp only [hgot]
          split
          · simp only [hbuf, hlen, hcap]
            obtain ⟨p, hp⟩ := outBlob_complete (mem := mem) (ev := buf) (len := len) (cap := cap)
              (bs := [UInt8.ofNat kind]) (by
                have hl : [UInt8.ofNat kind].length = 1 := rfl
                simp only [stage2RecordBytes] at hroom
                omega)
            have hpt : outTag mem buf len cap kind = some p := hp
            rw [hpt]
            exact ⟨_, rfl⟩
          · exact ⟨_, rfl⟩

/-- **`od_scalar_value`'s answer and frame in one reading**: the record's `ok`
word, the memory the call leaves, and the frame over the footprint.  The three
refusals write the error record; the two appending arms write the record at the
stream's cursor and then the cursor word, which is why the frames compose from the
inside out. -/
theorem s2ScalarValue_shape {args : List Value} {mem : Mem} {next : Nat} {r : CallOutcome}
    (hpre : s2ScalarValuePre args mem next)
    (h : stage2Calls stage2SubCalls "od_scalar_value" args mem next = some r) :
    ∃ (m : Mem) (ok : Nat), r = ⟨.int 32 (BitVec.ofNat 32 ok), m, next⟩ ∧
      UnchangedOutside mem m (s2ScalarValueFoot args mem next) := by
  obtain ⟨c, t, o, rfl, base, e, pos, endp, kind, buf, len, cap, win, hbase, he, hpos,
    hend, hkind, hbuf, hlen, hcap, hroom, hwin⟩ := hpre
  have hfoot : s2ScalarValueFoot [.ptr c, .ptr t, .ptr o] mem next =
      ([(o + 8, 8), (buf + len, stage2RecordBytes)] ++ [(e, stage2ErrorExtent)]) := by
    simp only [s2ScalarValueFoot, hbuf, hlen, he, List.singleton_append]
  rw [hfoot]
  rw [stage2Calls_od_scalar_value, stage2ScalarValueCall] at h
  simp only [stage2ScalarValue, hbase, he, hpos, hend, hkind] at h
  have hlex : readBytes mem (base + pos) (endp - pos) =
      some (win.take (endp - pos)) :=
    readBytes_take_prefix (Nat.le_max_left _ _) hwin
  by_cases h0 : kind = 0
  · simp only [h0, ↓reduceIte] at h
    exact ⟨_, 0, (Option.some.inj h).symm,
      stage2ErrSetMsg_frame ⟨(e, stage2ErrorExtent), by simp, le_rfl, le_rfl⟩⟩
  · simp only [h0, ↓reduceIte] at h
    by_cases h7 : kind = 7
    · simp only [h7, ↓reduceIte] at h
      simp only [hlex] at h
      by_cases hscan : (numLexScan (win.take (endp - pos))).2 = true
      · simp only [hscan] at h
        simp only [hbuf, hlen, hcap] at h
        obtain ⟨p, hp⟩ := emitBlobs_complete (mem := mem) (ev := buf) (len := len) (cap := cap)
          (blobs := numberRecord
            ((numFastEmitted (ByteString.literal (win.take (endp - pos)))).toBits))
          (by
            have hw := numberRecord_le
              ((numFastEmitted (ByteString.literal (win.take (endp - pos)))).toBits)
            omega)
        obtain ⟨p1, p2⟩ := p
        rw [hp] at h
        obtain ⟨hm', hl'⟩ := emitBlobs_spec hp
        rw [hm', hl'] at h
        exact ⟨_, 1, (Option.some.inj h).symm,
          ((UnchangedOutside.refl' mem _).write_le (a := buf + len) (w := stage2RecordBytes)
            ⟨(buf + len, stage2RecordBytes), by simp, le_rfl, le_rfl⟩
            (numberRecord_le
              ((numFastEmitted (ByteString.literal (win.take (endp - pos)))).toBits))).write_le
            (a := o + 8) (w := 8) ⟨(o + 8, 8), by simp, le_rfl, le_rfl⟩
            (by simp [wordBytes, natToBytes_length])⟩
      · simp only [hscan] at h
        exact ⟨_, 0, (Option.some.inj h).symm,
          stage2ErrSetMsg_frame ⟨(e, stage2ErrorExtent), by simp, le_rfl, le_rfl⟩⟩
    · simp only [h7, ↓reduceIte] at h
      cases hlit : stage2Literal kind with
      | none =>
          rw [hlit] at h
          exact ⟨_, 0, (Option.some.inj h).symm,
            stage2ErrSetMsg_frame ⟨(e, stage2ErrorExtent), by simp, le_rfl, le_rfl⟩⟩
      | some lit =>
          have hlit5 := stage2Literal_length hlit
          have hgot : readBytes mem (base + pos) lit.length =
              some (win.take lit.length) :=
            readBytes_take_prefix (le_trans hlit5 (Nat.le_max_right _ _)) hwin
          simp only [hlit, hgot] at h
          split at h
          · simp only [hbuf, hlen, hcap] at h
            obtain ⟨p, hp⟩ := outBlob_complete (mem := mem) (ev := buf) (len := len) (cap := cap)
              (bs := [UInt8.ofNat kind]) (by
                have hl : [UInt8.ofNat kind].length = 1 := rfl
                simp only [stage2RecordBytes] at hroom
                omega)
            obtain ⟨p1, p2⟩ := p
            have hpt : outTag mem buf len cap kind = some (p1, p2) := hp
            rw [hpt] at h
            obtain ⟨hm', hl'⟩ := outBlob_spec hp
            rw [hm', hl'] at h
            exact ⟨_, 1, (Option.some.inj h).symm,
              ((UnchangedOutside.refl' mem _).write_le (a := buf + len)
                (w := stage2RecordBytes) ⟨(buf + len, stage2RecordBytes), by simp, le_rfl,
                  le_rfl⟩ (by simp [stage2RecordBytes, List.length_cons])).write_le
                (a := o + 8) (w := 8) ⟨(o + 8, 8), by simp, le_rfl, le_rfl⟩
                (by simp [wordBytes, natToBytes_length])⟩
          · exact ⟨_, 0, (Option.some.inj h).symm,
              stage2ErrSetMsg_frame ⟨(e, stage2ErrorExtent), by simp, le_rfl, le_rfl⟩⟩

/-- **Which record an emitting arm appended.**  `ok = 1` is exactly the two
appending arms — the number scan's acceptance and a literal's match — so the
record is one of those two, and the memory's shape at it is the model's own
composition: the record's bytes at the stream's cursor, then the cursor word. -/
theorem s2ScalarValue_appended {c t o : Nat} {mem : Mem} {next : Nat}
    {r : CallOutcome} (hpre : s2ScalarValuePre [.ptr c, .ptr t, .ptr o] mem next)
    (h : stage2Calls stage2SubCalls "od_scalar_value" [.ptr c, .ptr t, .ptr o] mem next = some r)
    (hok : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    ∃ ev : EventRecord, s2ScalarValueAppend mem r.mem o ev.encodedBytes := by
  have h01 : (BitVec.ofNat 32 0) ≠ (BitVec.ofNat 32 1) := by decide
  obtain ⟨c', t', o', hargs, base, e, pos, endp, kind, buf, len, cap, win, hbase, he, hpos,
    hend, hkind, hbuf, hlen, hcap, hroom, hwin⟩ := hpre
  cases hargs
  have hlex : readBytes mem (base + pos) (endp - pos) =
      some (win.take (endp - pos)) :=
    readBytes_take_prefix (Nat.le_max_left _ _) hwin
  rw [stage2Calls_od_scalar_value, stage2ScalarValueCall] at h
  simp only [stage2ScalarValue, hbase, he, hpos, hend, hkind] at h
  by_cases h0 : kind = 0
  · simp only [h0, ↓reduceIte] at h
    exact absurd (by
      rw [(Option.some.inj h).symm] at hok
      simpa using hok) h01
  · simp only [h0, ↓reduceIte] at h
    by_cases h7 : kind = 7
    · simp only [h7, ↓reduceIte] at h
      simp only [hlex] at h
      by_cases hscan : (numLexScan (win.take (endp - pos))).2 = true
      · simp only [hscan] at h
        simp only [hbuf, hlen, hcap] at h
        obtain ⟨p, hp⟩ := emitBlobs_complete (mem := mem) (ev := buf) (len := len) (cap := cap)
          (blobs := numberRecord
            ((numFastEmitted (ByteString.literal (win.take (endp - pos)))).toBits))
          (by
            have hw := numberRecord_le
              ((numFastEmitted (ByteString.literal (win.take (endp - pos)))).toBits)
            omega)
        obtain ⟨p1, p2⟩ := p
        rw [hp] at h
        obtain ⟨hm', hl'⟩ := emitBlobs_spec hp
        rw [hm', hl'] at h
        refine ⟨EventRecord.number
          ((numFastEmitted (ByteString.literal (win.take (endp - pos)))).toBits), buf, len,
          hbuf, hlen, ?_⟩
        simp [EventRecord.encodedBytes, (Option.some.inj h).symm]
      · simp only [hscan] at h
        exact absurd (by
          rw [(Option.some.inj h).symm] at hok
          simpa using hok) h01
    · simp only [h7, ↓reduceIte] at h
      cases hlit : stage2Literal kind with
      | none =>
          rw [hlit] at h
          exact absurd (by
            rw [(Option.some.inj h).symm] at hok
            simpa using hok) h01
      | some lit =>
          have hlit5 := stage2Literal_length hlit
          have hgot : readBytes mem (base + pos) lit.length =
              some (win.take lit.length) :=
            readBytes_take_prefix (le_trans hlit5 (Nat.le_max_right _ _)) hwin
          simp only [hlit, hgot] at h
          split at h
          · simp only [hbuf, hlen, hcap] at h
            obtain ⟨p, hp⟩ := outBlob_complete (mem := mem) (ev := buf) (len := len) (cap := cap)
              (bs := [UInt8.ofNat kind]) (by
                have hl : [UInt8.ofNat kind].length = 1 := rfl
                simp only [stage2RecordBytes] at hroom
                omega)
            obtain ⟨p1, p2⟩ := p
            have hpt : outTag mem buf len cap kind = some (p1, p2) := hp
            rw [hpt] at h
            obtain ⟨hm', hl'⟩ := outBlob_spec hp
            rw [hm', hl'] at h
            refine ⟨EventRecord.tag kind, buf, len, hbuf, hlen, ?_⟩
            simp [EventRecord.encodedBytes, (Option.some.inj h).symm]
          · exact absurd (by
              rw [(Option.some.inj h).symm] at hok
              simpa using hok) h01

theorem s2ScalarValue_sound {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2ScalarValuePre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "od_scalar_value" args mem next = some r) :
    s2ScalarValuePost args mem next r := by
  obtain ⟨c, t, o, rfl, hrest⟩ := hpre
  have hpre' : s2ScalarValuePre [.ptr c, .ptr t, .ptr o] mem next := ⟨c, t, o, rfl, hrest⟩
  obtain ⟨m, ok, hr, -⟩ := s2ScalarValue_shape hpre' h
  have hval : stage2ScalarValue mem c t o next = some ⟨.int 32 (BitVec.ofNat 32 ok), m, next⟩ := by
    rw [← hr]
    rw [stage2Calls_od_scalar_value, stage2ScalarValueCall] at h
    exact h
  refine ⟨⟨m, ok, hval, ?_, ?_, ?_⟩, ?_⟩
  · rw [hr]
  · rw [hr]
  · rw [hr]
  · intro hok
    obtain ⟨ev, happ⟩ := s2ScalarValue_appended hpre' h hok
    exact ⟨ev, happ⟩

theorem s2ScalarValue_framed {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2ScalarValuePre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "od_scalar_value" args mem next = some r) :
    UnchangedOutside mem r.mem (s2ScalarValueFoot args mem next) := by
  obtain ⟨c, t, o, rfl, hrest⟩ := hpre
  have hpre' : s2ScalarValuePre [.ptr c, .ptr t, .ptr o] mem next := ⟨c, t, o, rfl, hrest⟩
  obtain ⟨m, _, hr, hframe⟩ := s2ScalarValue_shape hpre' h
  have hmem : r.mem = m := by rw [hr]
  rw [hmem]
  exact hframe

/-- **`od_scalar_value`'s contract**: the token's record or its refusal. -/
def s2ScalarValueContract :
    HelperContract (stage2Calls stage2SubCalls) "od_scalar_value" where
  pre := s2ScalarValuePre
  post := s2ScalarValuePost
  foot := s2ScalarValueFoot
  answers := fun _ _ _ hpre => s2ScalarValue_answers hpre
  sound := fun _ _ _ hpre _ h => s2ScalarValue_sound hpre h
  framed := fun _ _ _ hpre _ h => s2ScalarValue_framed hpre h

/-! #### `num_fast_el1`: the conversion, or the refusal offset -/

/-- **`num_fast_el1`'s reply** at the four arguments the emitted call passes.  The
scan's answer decides the arm, which is why the equation is stated with the scan's
`let` reduced. -/
theorem s2NumFast_reply {mem : Mem} {next : Nat} {p out err : Nat} {n : BitVec 64}
    {lex : List UInt8} (hlex : readBytes mem p n.toNat = some lex) :
    stage2Calls stage2SubCalls "num_fast_el1" [.ptr p, .int 64 n, .ptr out, .ptr err]
        mem next =
      (if (numLexScan lex).2 = true
       then some ⟨.int 32 (BitVec.ofNat 32 1),
         writeBytes mem out
           (wordBytes 8 (numFastEmitted (ByteString.literal lex)).toBits), next⟩
       else some ⟨.int 32 (BitVec.ofNat 32 0),
         writeBytes mem err (wordBytes 8 (numLexScan lex).1), next⟩) := by
  rw [stage2Calls_num_fast_el1]
  unfold stage2NumFast
  simp only [hlex]

theorem s2NumFast_answers {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2NumFastPre args mem next) :
    ∃ r, stage2Calls stage2SubCalls "num_fast_el1" args mem next = some r := by
  obtain ⟨p, out, err, n, rfl, lex, hlex⟩ := hpre
  rw [s2NumFast_reply hlex]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **The refusal's offset is inside the lexeme it was read from** — the bound the
post's refusing arm carries, and what keeps the reported position inside the
token's document extent. -/
theorem numLexScan_off_le {mem : Mem} {p n : Nat} {lex : List UInt8}
    (h : readBytes mem p n = some lex) : (numLexScan lex).1 ≤ n := by
  have hlen : lex.length = n := JsonEntrySteps.readBytes_length mem p n h
  rw [← hlen]
  exact numLexScan_fst_le lex

theorem s2NumFast_sound {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2NumFastPre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "num_fast_el1" args mem next = some r) :
    s2NumFastPost args mem next r := by
  obtain ⟨p, out, err, n, rfl, lex, hlex⟩ := hpre
  rw [s2NumFast_reply hlex] at h
  by_cases hs : (numLexScan lex).2 = true
  · simp only [hs] at h
    have hr : r = ⟨.int 32 (BitVec.ofNat 32 1),
        writeBytes mem out
          (wordBytes 8 (numFastEmitted (ByteString.literal lex)).toBits), next⟩ :=
      (Option.some.inj h).symm
    exact ⟨lex, hlex, Or.inl ⟨hs, by rw [hr], by rw [hr], by rw [hr]⟩⟩
  · simp only [hs] at h
    have hr : r = ⟨.int 32 (BitVec.ofNat 32 0),
        writeBytes mem err (wordBytes 8 (numLexScan lex).1), next⟩ :=
      (Option.some.inj h).symm
    exact ⟨lex, hlex, Or.inr ⟨by simpa using hs, by rw [hr], by rw [hr], by rw [hr],
      numLexScan_off_le hlex⟩⟩

theorem s2NumFast_framed {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2NumFastPre args mem next) {r : CallOutcome}
    (h : stage2Calls stage2SubCalls "num_fast_el1" args mem next = some r) :
    UnchangedOutside mem r.mem (s2NumFastFoot args mem next) := by
  obtain ⟨p, out, err, n, rfl, lex, hlex⟩ := hpre
  rw [s2NumFast_reply hlex] at h
  by_cases hs : (numLexScan lex).2 = true
  · simp only [hs] at h
    have hr : r = ⟨.int 32 (BitVec.ofNat 32 1),
        writeBytes mem out
          (wordBytes 8 (numFastEmitted (ByteString.literal lex)).toBits), next⟩ :=
      (Option.some.inj h).symm
    have hmem : r.mem = writeBytes mem out
        (wordBytes 8 (numFastEmitted (ByteString.literal lex)).toBits) := by rw [hr]
    rw [hmem]
    exact (UnchangedOutside.refl' mem [(out, 8), (err, 8)]).write_le (a := out) (w := 8)
      ⟨(out, 8), List.mem_cons_self .., le_rfl, le_rfl⟩
      (by simp [wordBytes, natToBytes_length])
  · simp only [hs] at h
    have hr : r = ⟨.int 32 (BitVec.ofNat 32 0),
        writeBytes mem err (wordBytes 8 (numLexScan lex).1), next⟩ :=
      (Option.some.inj h).symm
    have hmem : r.mem = writeBytes mem err (wordBytes 8 (numLexScan lex).1) := by rw [hr]
    rw [hmem]
    exact (UnchangedOutside.refl' mem [(out, 8), (err, 8)]).write_le (a := err) (w := 8)
      ⟨(err, 8), by simp, le_rfl, le_rfl⟩
      (by simp [wordBytes, natToBytes_length])

/-- **`num_fast_el1`'s contract**: the conversion, or the refusal's offset. -/
def s2NumFastContract : HelperContract (stage2Calls stage2SubCalls) "num_fast_el1" where
  pre := s2NumFastPre
  post := s2NumFastPost
  foot := s2NumFastFoot
  answers := fun _ _ _ hpre => s2NumFast_answers hpre
  sound := fun _ _ _ hpre _ h => s2NumFast_sound hpre h
  framed := fun _ _ _ hpre _ h => s2NumFast_framed hpre h

/-! ### Axiom footprints

Five of the six contracts print the standard footprint — `propext` and
`Quot.sound`.  `num_fast_el1`'s prints `Classical.choice` as well, inherited from
`JsonStage2Body.numLexScan_fst_le`, the lexeme bound its post's refusing arm
carries: the choice is the model module's, not this contract's.

The instrument is `#print axioms`, and a declaration proved with `sorry` prints
`sorryAx` under the same command — so a contract printing only
`[propext, Quot.sound]` is a fact about the proof rather than about the printer.
-/

#print axioms s2InitContract
#print axioms s2ValuePosContract
#print axioms s2AfterValueContract
#print axioms s2StringBodyContract
#print axioms s2ScalarValueContract
#print axioms s2NumFastContract
#print axioms s2StringBody_outn_le
#print axioms emitBlobs_complete
#print axioms readBytes_take_prefix
#print axioms HelperContract.resolves
#print axioms HelperContract.view
#print axioms LeanLLVM.Refinement.s2ScalarValue_appended

end LeanLLVM.Refinement
