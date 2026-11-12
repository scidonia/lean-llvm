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
The lists are the interface; three of the six fields the contract asks of each
helper — `answers`, `sound`, `framed` — are not yet supplied (see below).
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
(`BodyPositionsSpaced`), and the accepting arms' bound `on ≤ len` is the
consequence a caller reads off `escapeDecodeGo_length_le` at that staging.  The
spacing is the *list's* obligation — the stage-1 escape positions' token extent —
and not a fact about this function; a caller that cannot supply it has no bound on
the escaped form, and `docs/contract.md` §7.6 records that rather than assuming it
away.

**What is not stated here.**  Two gaps, both deliberate and both named.

*The six contract values are not proved.*  `HelperContract`'s three facts —
`answers`, `sound`, `framed` — are stated for each helper as the field that must
be supplied, and no value is defined here: the module carries the staging
predicates, the posts, the footprints and the frame steps, not the proofs that
the models satisfy them.  Nor is the string staging's consequence stated as a
theorem of its own: the decoded-length bound is recorded where it is read
(`BodyPositionsSpaced`'s docstring and `docs/contract.md` §7.6), not proved
here.  A caller can therefore read the interface and the region
lists, and cannot yet apply `HelperContract.resolves` at a call.  The three facts
per helper are model readings and frame compositions — `stage2*_answers` already
supplies the first for five of the six, and the frame steps below supply the third
once each arm's write is placed in a region — so the gap is proof engineering, not
a missing statement.  `docs/contract.md` §7.6 records it with the rest of the
helpers' correspondence.

*No helper's contract is proved against an emitted body.*  The fixture declares
all six (`stage2.rewrites.tsv` class r2 — "their bodies are outside this fragment
... each is resolved by the fixture's `Calls` environment at the record or tier
theorem that states its contract").  The models are transcriptions of
`kernel/json/stage2.c` pinned by `#guard`s in `JsonStage2Body`, and the
correspondence between a transcription and the compiled function is the pipeline's
body-faithfulness seam.
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

/-- **`s2_string_body`'s staging**: the eight arguments, the five words the callee
reads, and the escape list's spacing at the body it is given. -/
def s2StringBodyPre (args : List Value) (mem : Mem) (_next : Nat) : Prop :=
  ∃ (c p : Nat) (len : BitVec 64) (dst outn xp xj : Nat) (nxp : BitVec 64),
    args = [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
      .int 64 nxp] ∧
    (∃ base, stage2ReadWord mem c 8 = some base) ∧
    (∃ j0, stage2ReadWord mem xj 8 = some j0) ∧
    (∃ ps, readLanes32 mem xp nxp.toNat = some ps) ∧
    (∃ body, readBytes mem p len.toNat = some body) ∧
    (∃ e, stage2ReadWord mem (c + 1112) 8 = some e) ∧
    BodyPositionsSpaced mem c xj xp nxp.toNat p len.toNat

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
      ∃ (m : Mem) (form : Nat),
        stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat = some (m, form) ∧
        r.ret = .int 32 (BitVec.ofNat 32 form) ∧ r.mem = m ∧ r.next = next
  | _ => False

/-- **`s2_string_body`'s writes**: the cursor word, the decoded-length word, the
decoded prefix in a slot `len` wide, and — where the cursor record's error pointer
is readable — the error record it names.  The error region is in the list on the
accepting arms too, because the footprint is read before the call and cannot see
which arm ran; `stage2ErrorExtent` is the record's staged extent and the refusal
writes sixteen of its bytes. -/
def s2StringBodyFoot (args : List Value) (mem : Mem) (_next : Nat) :
    List (Nat × Nat) :=
  match args with
  | [.ptr c, .ptr _, .int 64 len, .ptr dst, .ptr outn, .ptr _, .ptr xj, .int 64 _] =>
      [(xj, 8), (outn, 8), (dst, len.toNat)] ++
        (match stage2ReadWord mem (c + 1112) 8 with
         | some e => [(e, 16)]
         | none => [])
  | _ => []

/-! #### `od_scalar_value`: the appended record -/

/-- **`od_scalar_value`'s answer**: `1` when it appended the token's record and
`0` when it refused, with the stream's cursor written back (`out_raw`'s
`o->len += n`) and the refusal's offset in the error record. -/
def s2ScalarValuePost (args : List Value) (mem : Mem) (next : Nat)
    (r : CallOutcome) : Prop :=
  match args with
  | [.ptr c, .ptr t, .ptr o] =>
      ∃ (m : Mem) (ok : Nat),
        stage2ScalarValue mem c t o next = some ⟨.int 32 (BitVec.ofNat 32 ok), m, next⟩ ∧
        r.ret = .int 32 (BitVec.ofNat 32 ok) ∧ r.mem = m ∧ r.next = next
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
         | some e => [(e, 16)]
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
        (((numLexScan lex).2 = true) ∧
          r.ret = .int 32 (BitVec.ofNat 32 1) ∧
          r.mem = writeBytes mem out
            (wordBytes 8 (numFastEmitted (ByteString.literal lex)).toBits) ∧
          r.next = next)
        ∨ (((numLexScan lex).2 = false) ∧
          r.ret = .int 32 (BitVec.ofNat 32 0) ∧
          r.mem = writeBytes mem err (wordBytes 8 (numLexScan lex).1) ∧
          r.next = next ∧ (numLexScan lex).1 ≤ n.toNat)
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

/-! ### Axiom footprints -/

#print axioms UnchangedOutside.write_le
#print axioms stage2WriteStores_frame
#print axioms stage2ErrSet_frame
#print axioms stage2Literal_length
#print axioms UnchangedOutside.of_subset

end LeanLLVM.Refinement