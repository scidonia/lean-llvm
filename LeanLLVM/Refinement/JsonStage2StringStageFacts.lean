/-
The string body at the walk's call site: its staging, and its footprint inside
the walk's frame.

`z_arena_reserve.exit` (`JsonStage2WalkCall`) calls `@s2_string_body` with eight
arguments and hands the answer to `NodeBlock31`.  Two facts at that call are the
caller's and not the callee's, and this module states them at an abstract memory
and an abstract staging so the walk layer can instantiate them:

* **the callee's precondition**, `s2StringBodyPre`, assembled from the reads the
  call's memory holds, the document's spacing fact and the staging's address
  facts (`s2StringBodyPre_of_staging`).  Its hypothesis list is the producer's
  target: each argument is one of those three, or one of the caller's arithmetic
  side conditions, and the docstring names which for every one;
* **the producer of that precondition at the walk's call**,
  `s2StringBodyPre_at_string_call`: all eight arguments at the block's own
  registers (`%c.i`, `%arrayidx10.i`, `%sub260.i`, `%xp`, `%nxp`, and the two
  `alloca` slots `walkStaticRegs` fixes), the memory the invariant carries and the
  cursor the call is made at.  Thirty of the assembler's thirty-seven hypotheses
  are derived there — the document's window, the escape list's lanes, the two
  presence clauses and every separation — and seven are named, each with the
  producer that would make it derivable.  It is the shape a consumer substitutes
  for `HstringFacts.hpreS` and for the link's `hpreS`.
* **the callee's footprint inside the walk's frame**: the frame the callee proves
  over `s2StringBodyFoot` is one over the walk's `walkWideAt` at the carry the link
  builds and the cursor the call left (`s2StringBodyFoot_frame_walkWideAt`), and
  the caller's presence over
  `walkStaged` survives the call (`s2StringBodyFoot_presence_walkStaged`).  The
  second needs no frame at all: every arm of the model is a write nest over the
  caller's memory, and a write adds cells and removes none, so presence is
  monotone through the call whatever the callee wrote.  That is why the staging's
  separation is not consumed here, and the docstrings say so rather than implying
  a use.
* **the precondition's transport to the call's memory**
  (`s2StringBodyPre_of_reads`, with `s2StringBodyPre_components` exposing the six
  clauses a consumer of the model needs): agreement at the five reads the
  precondition names, plus presence monotonicity, moves the whole predicate.  The
  separations and the bounds are about addresses, so they travel unchanged, and
  the spacing fact is the four reads (`BodyPositionsSpaced_of_reads`).  This is
  what a caller needs when the predicate is stated at a head's memory and the
  call is made after the walk's own stores; `walkReadBytes_two_writes` is the read
  across those two stores, and `walkLog_arena_sep`/`walkArena_ev_sep` are the
  staging separations the crossings read.
* **the decoded length at the answer's own memory**: the post's memory is the
  model's with the body's private `%ei` slot written at the call's `next`, and the
  precondition separates that slot from `%outn.i` (`s2StringBodyPre_next_outn`).
  So `s2StringBody_outn_le`'s word survives the slot's write
  (`s2StringBody_outn_at_call`, with the slot's width
  `stage2StringBody_slot_le`), and the decoded length and its bound are read at
  the answer's memory without a premise about the callee — which is what retires
  the walk bundle's length fields.

* **the accepting arm's four write entries and the crossings at them**
  (`s2StringBodyFrame_walkWideAt`, `s2StringBodyFrame_facts`): the arm writes the
  escape cursor, the decoded-length word, the destination window and the private
  slot; each lies inside the walk's list, which is how the callee's silence
  transfers to `walkWideAt`, and the log's and the trace's read equalities and the
  two carried stack copies are read out of that silence
  (`readBytes_of_frame`).  The silence is the callee's four entries rather than
  the run's list on purpose: `walkWideAt` *contains* the log and the stream as
  entries, so a frame over it says nothing about either.

The statements are at `mem : Mem` and at `G : WalkGeom m0`/`C : WalkCarry G`
rather than at a state's memory: the call's memory is the invariant's, and every
lemma here is about the two region lists the walk carries, not about a state.
-/
import LeanLLVM.Refinement.JsonStage2Helpers
import LeanLLVM.Refinement.JsonStage2WalkScope

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The staging's precondition at the call's argument list

`s2StringBodyPre` (`JsonStage2Helpers`) is an existential over thirteen witnesses
and thirty-eight conjuncts.  An existential is not something a producer can
target — it knows the witnesses, and it holds the conjuncts one at a time — so
this assembler states the same predicate with every witness and every conjunct
named.  Its only work is the existential's introduction; the content is the
hypothesis list.

**The hypothesis list is the producer's target.**  Every argument is one of:

* **a read the call's memory holds** — `base`, `j0`, `ps`, `body`, `e` are the
  five words `s2_string_body` reads, and `outn`, `dst` and the error record are
  the three presences its writes need.  At the walk's call these are the staging's
  own reads: the cursor record's base and error words, the escape list's lanes,
  the document's bytes, the allocated `%outn.i` slot's word and the arena
  window's bytes;
* **a document fact** — `hspaced` is `BodyPositionsSpaced`, which says the escape
  list's window over the body's document range is a `Spaced` list.  It is a
  property of the document's positions and the escape list, and it is the
  hypothesis `escapeDecodeGo_length_le` takes: the decoded length's bound cannot
  be derived from a read;
* **a staging-address fact** — the ten `RegionsApart` facts among the write
  regions, the ten against the document and the cursor record's error field, and
  the two lane exclusions.  They are the staging's separation read at the call's
  addresses: the geometry's `DisjointRegions` for the staged objects, the
  adapter's for the seven it appends, and the cursor's own arithmetic for the
  four `alloca` slots (`stage2AllocaWrites` places `%outn.i` at `+ 20` and
  `%xj.i` at `+ 12`, so their separations are offsets rather than objects).

The six bounds are **the caller's arithmetic**, not a fourth class: `p < 2 ^ 64`
and `base ≤ p` make the body's `ptrtoint`-and-subtract agree with the model's
`Nat` subtraction, `p - base + len.toNat < 2 ^ 64` keeps the model's window from
wrapping, `len.toNat + 1 < 2 ^ 64` excludes the one length the body's sentinel
confuses with a refusal, and `j0 < 2 ^ 63`/`nxp.toNat < 2 ^ 63` keep the scan's
sign-extended index forward.  A producer discharges them from the geometry's
address and document bounds, so they stay hypotheses here.

Nothing about the body's own `%ei` slot's presence appears: the slot is a region
the body's crossings move a write *into*, so each crossing spends the presence of
the region it moves into and not the slot's (`JsonStage2Helpers`' docstring on the
pre, and the handoff's Gap 2).  Adding it back would be a clause no caller can
supply and the callee does not need. -/
theorem s2StringBodyPre_of_staging {mem : Mem} {next : Nat}
    {c p dst outn xp xj : Nat} {len nxp : BitVec 64}
    {base j0 e : Nat} {ps : List Nat} {body : List UInt8}
    (hbase : stage2ReadWord mem c 8 = some base)
    (hj0 : stage2ReadWord mem xj 8 = some j0)
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hspaced : BodyPositionsSpaced mem c xj xp nxp.toNat p len.toNat)
    (hp_lt : p < 2 ^ 64)
    (hbase_le : base ≤ p)
    (hwrap : p - base + len.toNat < 2 ^ 64)
    (hlen_lt : len.toNat + 1 < 2 ^ 64)
    (hj0_lt : j0 < 2 ^ 63)
    (hnxp_lt : nxp.toNat < 2 ^ 63)
    (houtn : readBytes mem outn 8 ≠ none)
    (hdst : readBytes mem dst len.toNat ≠ none)
    (herr : readBytes mem e stage2ErrorExtent ≠ none)
    (hxj_next : RegionsApart xj 8 next 8)
    (hxj_outn : RegionsApart xj 8 outn 8)
    (hxj_dst : RegionsApart xj 8 dst len.toNat)
    (hxj_err : RegionsApart xj 8 e stage2ErrorExtent)
    (hnext_outn : RegionsApart next 8 outn 8)
    (hnext_dst : RegionsApart next 8 dst len.toNat)
    (hnext_err : RegionsApart next 8 e stage2ErrorExtent)
    (houtn_dst : RegionsApart outn 8 dst len.toNat)
    (houtn_err : RegionsApart outn 8 e stage2ErrorExtent)
    (hdst_err : RegionsApart dst len.toNat e stage2ErrorExtent)
    (hxj_p : RegionsApart xj 8 p len.toNat)
    (hxj_c : RegionsApart xj 8 (c + 1112) 8)
    (hnext_p : RegionsApart next 8 p len.toNat)
    (hnext_c : RegionsApart next 8 (c + 1112) 8)
    (hdst_p : RegionsApart dst len.toNat p len.toNat)
    (hdst_c : RegionsApart dst len.toNat (c + 1112) 8)
    (houtn_p : RegionsApart outn 8 p len.toNat)
    (houtn_c : RegionsApart outn 8 (c + 1112) 8)
    (herr_p : RegionsApart e stage2ErrorExtent p len.toNat)
    (herr_c : RegionsApart e stage2ErrorExtent (c + 1112) 8)
    (hxj_scan : ∀ k, k < nxp.toNat → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hnext_scan : ∀ k, k < nxp.toNat → xp + 4 * k + 4 ≤ next ∨ next + 8 ≤ xp + 4 * k) :
    s2StringBodyPre [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp,
      .ptr xj, .int 64 nxp] mem next :=
  ⟨c, p, len, dst, outn, xp, xj, nxp, base, j0, ps, body, e, rfl,
    hbase, hj0, hps, hbody, he, hspaced, hp_lt, hbase_le, hwrap, hlen_lt,
    hj0_lt, hnxp_lt, houtn, hdst, herr, hxj_next, hxj_outn, hxj_dst, hxj_err,
    hnext_outn, hnext_dst, hnext_err, houtn_dst, houtn_err, hdst_err,
    hxj_p, hxj_c, hnext_p, hnext_c, hdst_p, hdst_c, houtn_p, houtn_c, herr_p,
    herr_c, hxj_scan, hnext_scan⟩

/-! ### The body's footprint inside the walk's frame

The walk's call-site link (`WalkLink.z_arena_reserve_exit`) takes the callee's
frame and the caller's presence as supplied hypotheses, because the bridge from
`s2StringBodyFoot` to the walk's two lists is not a lemma of the layer the link
sits in.  These two statements are that bridge.

The foot's argument list is the call's, at the staging's addresses:

* `%xj.i` is `G.next0 + 12` (`walkStaticRegs`), not `+ 16`;
* `%outn.i` is `G.next0 + 20`;
* the destination is the arena's base word `G.dst` plus the log's `%z.val36`
  offset, named `A` here;
* the body pointer and the escape list are the caller's document and count.

`s2StringBodyFoot` ignores the body pointer, the escape list and the escape
count, so they appear in the list and nowhere in the proof; they are named so the
statement is the call's and not a reshaping of it. -/

/-- **The callee's frame is the walk's, at the carry the link builds and the
cursor the call left.**  Every entry of `s2StringBodyFoot` at the call's argument
list lies inside an entry of `walkWideAt` at the advanced carry and the interval
`(G.next0, m)`:

| foot entry | covered by | why |
|---|---|---|
| `(%xj.i, 8)` = `(G.next0 + 12, 8)` | the cursor's interval `(G.next0, m)` | `m ≥ 20`, from `hnext` and `hm` |
| `(%outn.i, 8)` = `(G.next0 + 20, 8)` | the cursor's interval `(G.next0, m)` | `m ≥ 28`, from `hnext` and `hm` |
| `(dst, len.toNat)` = `(G.dst + A, len.toNat)` | `(G.dst, C.alen + ext)` | `A ≤ C.alen`, `len.toNat ≤ ext` |
| the private `%ei` slot `(next, 8)` | the cursor's interval `(G.next0, m)` | `next + 8 ≤ G.next0 + m` (`hm`) |
| the error record `(e, stage2ErrorExtent)` | `stage2ReportScratch` | `e` is the staging's `%e` |

The list is the invariant's, not the fixed five-slot window of
`stage2AllocaWrites`: `WalkInv.frame` names the interval `walkWideAt G C (s.next -
G.next0)`, and the run's stack writes past `G.next0 + 36` are covered by the
interval alone.  The callee's three stack entries are therefore read against the
interval, which is what the two cursor hypotheses state.

Three of the rows are hypotheses rather than consequences of the staging:

* **`he`** fixes the cursor record's error field at the staging's `%e`.  It is the
  pre's own fifth read (`stage2ReadWord mem (c + 1112) 8`) with its witness named.
  The cursor record is one of the seven staging objects, its `%e` pointer at
  `+1112` is the adapter's staged value, and no block of the walk's chain stores
  through `%c.i + 1112`; no invariant clause carries the field's value, so the
  read is a named hypothesis whose producer is the staging together with the
  chain's silence at that offset.  At the foot it is what turns the error
  record's address from whatever the word holds into the staged object the seven
  appended writes already name — without it the foot's last entry is an arbitrary
  address outside every list the frame names.  A caller whose run is on an
  accepting arm does not need it: `s2StringBody_frame_of_form` below states that
  arm's frame at the four entries the body writes, and the refusal's record is
  the only entry `he` places.
* **`hAle`** is the log's arena word at most the carried cursor,
  `WalkInv.logArena_le`'s conclusion at the `%ar` read.  It is what places the
  callee's destination window inside the arena's carried prefix: the window
  starts at `G.dst + A` and the frame's arena entry starts at `G.dst`.
* **`hnext`** and **`hm`** place the callee's private `%ei` slot and the two
  `alloca` slots at `G.next0 + 12` and `+ 20` inside the interval.
  `s2_string_body` allocates eight bytes at the cursor it is called with
  (`s2StringBodyCall` advances `next` by the slot's width), so the returned cursor
  is `next + 8` and the caller's interval ends there; `hm` is that statement in
  the interval's own terms.  `hnext` is the lower end, `WalkInv.next_ge`'s
  conclusion at the call: the entry's four `alloca`s sit at `G.next0`, below every
  cursor the run reaches.  The pair is deliberately two inequalities about the
  cursor rather than the equality `next = G.next0 + 28`: a helper call moves the
  cursor past the bootstrap window, and the interval is what the invariant's frame
  names.

`hlen` is the call's own arithmetic: the extent argument is `%sub260.i`, and the
carry's advance is the same number.  A caller that instantiates `len` as
`BitVec.ofNat 64 ext` has `len.toNat = ext % 2 ^ 64 ≤ ext` by `Nat.mod_le`, which
is the hypothesis at that instantiation. -/
theorem s2StringBodyFoot_frame_walkWideAt {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {mem : Mem} {next m : Nat} {r : CallOutcome} {p A ext : Nat}
    {len nxp : BitVec 64}
    (he : stage2ReadWord mem (C.stage.c + 1112) 8 = some C.stage.e)
    (hAle : A ≤ C.alen)
    (hlen : len.toNat ≤ ext)
    (hnext : G.next0 + stage2BootstrapExtent ≤ next)
    (hm : next + 8 ≤ G.next0 + m)
    (hframe : UnchangedOutside mem r.mem
      (s2StringBodyFoot [.ptr C.stage.c, .ptr (G.b + p + 1), .int 64 len,
        .ptr (G.dst + A), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
        .int 64 nxp] mem next)) :
    UnchangedOutside mem r.mem
      (walkWideAt G { C with block := "NodeBlock31", alen := C.alen + ext, spans := C.spans ++ [(C.alen, ext)], pending := none } m) := by
  let C' : WalkCarry G := { C with block := "NodeBlock31", alen := C.alen + ext, spans := C.spans ++ [(C.alen, ext)], pending := none }
  change UnchangedOutside mem r.mem (walkWideAt G C' m)
  have hfoot : s2StringBodyFoot [.ptr C.stage.c, .ptr (G.b + p + 1), .int 64 len,
      .ptr (G.dst + A), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
      .int 64 nxp] mem next
      = [(G.next0 + 12, 8), (G.next0 + 20, 8), (G.dst + A, len.toNat),
         (next, 8), (C.stage.e, stage2ErrorExtent)] := by
    simp only [s2StringBodyFoot, he, List.cons_append, List.nil_append]
  -- the interval's entry, and the two `alloca` slots and the private slot inside it
  have hint : (G.next0, m) ∈ walkWideAt G C' m :=
    List.mem_append_right _ (List.mem_cons_self ..)
  have hb36 : G.next0 + 36 ≤ G.next0 + m := by
    simp only [stage2BootstrapExtent] at hnext
    omega
  have hdst : (G.dst, C'.alen) ∈ walkWideAt G C' m := by
    show (G.dst, C'.alen) ∈ walkPresent G C' ++ [(G.next0, m)]
    exact List.mem_append_left _ (by
      show (G.dst, C'.alen) ∈
        [(G.dst, C'.alen), (G.ev, C'.evlen)] ++
          stage2ReportScratch C'.stage.c C'.stage.ctype C'.stage.cst C'.stage.tok
            C'.stage.s C'.stage.z C'.stage.e C'.stage.d
      exact List.mem_append_left _ (List.mem_cons_self))
  have herr : (C.stage.e, stage2ErrorExtent) ∈ walkWideAt G C' m := by
    show (C.stage.e, stage2ErrorExtent) ∈ walkPresent G C' ++ [(G.next0, m)]
    exact List.mem_append_left _ (by
      show (C.stage.e, stage2ErrorExtent) ∈
        [(G.dst, C'.alen), (G.ev, C'.evlen)] ++
          stage2ReportScratch C'.stage.c C'.stage.ctype C'.stage.cst C'.stage.tok
            C'.stage.s C'.stage.z C'.stage.e C'.stage.d
      exact List.mem_append_right _ (by
        show (C.stage.e, stage2ErrorExtent) ∈
          stage2StagedWrites C'.stage.c C'.stage.ctype C'.stage.cst C'.stage.tok
              C'.stage.s C'.stage.z C'.stage.e ++ [(C'.stage.d, 8)]
        exact List.mem_append_left _ (by
          simp only [stage2StagedWrites]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))
  have hcov : ∀ r ∈ s2StringBodyFoot [.ptr C.stage.c, .ptr (G.b + p + 1),
      .int 64 len, .ptr (G.dst + A), .ptr (G.next0 + 20), .ptr G.xp,
      .ptr (G.next0 + 12), .int 64 nxp] mem next,
      ∃ q ∈ walkWideAt G C' m, q.1 ≤ r.1 ∧ r.1 + r.2 ≤ q.1 + q.2 := by
    intro r hr
    rw [hfoot] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, hint, by omega, by omega⟩
    · exact ⟨_, hint, by omega, by omega⟩
    · exact ⟨_, hdst, by show G.dst ≤ G.dst + A; omega,
        by show (G.dst + A) + len.toNat ≤ G.dst + (C.alen + ext); omega⟩
    · exact ⟨_, hint, by omega, by omega⟩
    · exact ⟨_, herr, le_rfl, le_rfl⟩
  refine UnchangedOutside.widen hframe ?_
  intro a ha r hr
  obtain ⟨q, hq, hqlo, hqhi⟩ := hcov r hr
  exact fun hin => ha q hq ⟨le_trans hqlo hin.1, lt_of_lt_of_le hin.2 hqhi⟩

/-- **The staged spacing, read off the precondition.**  `s2StringBodyPre` holds the
spacing fact under its own witnesses; at a literal argument list the witnesses are
those arguments, so the fact is the call's at the call's own numbers. -/
theorem s2StringBodyPre_spacing {mem : Mem} {next : Nat} {c p dst outn xp xj : Nat}
    {len : BitVec 64} {nxp : BitVec 64}
    (hpre : s2StringBodyPre [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn,
      .ptr xp, .ptr xj, .int 64 nxp] mem next) :
    BodyPositionsSpaced mem c xj xp nxp.toNat p len.toNat := by
  obtain ⟨c', p', len', dst', outn', xp', xj', nxp', _, _, _, _, _, hargs, _, _, _, _, _,
    hspace, -⟩ := hpre
  simp only [List.cons.injEq, and_true, true_and, Value.ptr.injEq, Value.int.injEq]
    at hargs
  obtain ⟨hc, hp, hlen, hdst, houtn, hxp, hxj, hnxp⟩ := hargs
  obtain hlenE := eq_of_heq hlen
  obtain hnxpE := eq_of_heq hnxp
  subst hc
  subst hp
  subst hdst
  subst houtn
  subst hxp
  subst hxj
  subst hlenE
  subst hnxpE
  exact hspace

/-- **The staged spacing is read through four reads.**  `BodyPositionsSpaced` is a
statement about the cursor record's base word, the escape cursor's slot, the
position lanes and the body's bytes; agreement at those four reads is agreement at
the spacing fact, whatever the memory is otherwise. -/
theorem BodyPositionsSpaced_of_reads {m m' : Mem} {c xj xp nxp p len : Nat}
    (hc : stage2ReadWord m' c 8 = stage2ReadWord m c 8)
    (hj : stage2ReadWord m' xj 8 = stage2ReadWord m xj 8)
    (hx : readLanes32 m' xp nxp = readLanes32 m xp nxp)
    (hb : readBytes m' p len = readBytes m p len)
    (hsp : BodyPositionsSpaced m c xj xp nxp p len) :
    BodyPositionsSpaced m' c xj xp nxp p len := by
  intro base j0 ps body h1 h2 h3 h4
  rw [hc] at h1
  rw [hj] at h2
  rw [hx] at h3
  rw [hb] at h4
  exact hsp base j0 ps body h1 h2 h3 h4

/-- **The body's precondition at any memory its five reads agree with.**  The body
reads eight things at the call — the cursor record's base word and its error field,
the escape cursor's slot, the position lanes and the document's bytes — and writes
only where the caller staged presence.  So agreement at those five reads, together
with presence monotonicity, moves the whole precondition: the twenty separations and
the six bounds are about addresses, and the spacing fact is the four reads
(`BodyPositionsSpaced_of_reads`).

This is the transport a caller needs when the precondition is stated at a memory an
earlier store has since moved: the walk's head bundles state it at the head's
memory, and the string body is called at link 8's, which has written the cursor
record's `%k` field and the `%outn.i` zero. -/
theorem s2StringBodyPre_of_reads {mem mem' : Mem} {next : Nat}
    {c p dst outn xp xj : Nat} {len nxp : BitVec 64}
    (hbaseA : stage2ReadWord mem' c 8 = stage2ReadWord mem c 8)
    (hj0A : stage2ReadWord mem' xj 8 = stage2ReadWord mem xj 8)
    (heA : stage2ReadWord mem' (c + 1112) 8 = stage2ReadWord mem (c + 1112) 8)
    (hpsA : readLanes32 mem' xp nxp.toNat = readLanes32 mem xp nxp.toNat)
    (hbodyA : readBytes mem' p len.toNat = readBytes mem p len.toNat)
    (hpres : ∀ a n, readBytes mem a n ≠ none → readBytes mem' a n ≠ none)
    (h : s2StringBodyPre [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp,
      .ptr xj, .int 64 nxp] mem next) :
    s2StringBodyPre [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp,
      .ptr xj, .int 64 nxp] mem' next := by
  obtain ⟨c', p', len', dst', outn', xp', xj', nxp', base, j0, ps, body, e', hargs,
    hb, hj, hp, hbd, he, hsp, hp_lt, hbase_le, hwrap, hlen_lt, hj0_lt, hnxp_lt,
    houtn, hdst, herr, hxj_next, hxj_outn, hxj_dst, hxj_err, hnext_outn, hnext_dst,
    hnext_err, houtn_dst, houtn_err, hdst_err, hxj_p, hxj_c, hnext_p, hnext_c,
    hdst_p, hdst_c, houtn_p, houtn_c, herr_p, herr_c, hxj_scan, hnext_scan⟩ := h
  simp only [List.cons.injEq, and_true, true_and, Value.ptr.injEq, Value.int.injEq]
    at hargs
  obtain ⟨hc, hpE, hlen, hdstE, houtnE, hxpE, hxjE, hnxpE⟩ := hargs
  obtain hlenE := eq_of_heq hlen
  obtain hnxpEE := eq_of_heq hnxpE
  subst hc; subst hpE; subst hdstE; subst houtnE; subst hxpE; subst hxjE
  subst hlenE; subst hnxpEE
  exact s2StringBodyPre_of_staging (mem := mem')
    (hbase := by rw [hbaseA]; exact hb)
    (hj0 := by rw [hj0A]; exact hj)
    (hps := by rw [hpsA]; exact hp)
    (hbody := by rw [hbodyA]; exact hbd)
    (he := by rw [heA]; exact he)
    (hspaced := BodyPositionsSpaced_of_reads hbaseA hj0A hpsA hbodyA hsp)
    (houtn := hpres _ _ houtn) (hdst := hpres _ _ hdst) (herr := hpres _ _ herr)
    hp_lt hbase_le hwrap hlen_lt hj0_lt hnxp_lt
    hxj_next hxj_outn hxj_dst hxj_err hnext_outn hnext_dst hnext_err
    houtn_dst houtn_err hdst_err hxj_p hxj_c hnext_p hnext_c hdst_p hdst_c
    houtn_p houtn_c herr_p herr_c hxj_scan hnext_scan

/-- **The precondition's six named clauses at its own memory.**  The witnesses a
producer supplies are not what a consumer of `s2StringBody` needs: the model's
reduction matches on three reads, and the decoder's bound needs the spacing.  This
exposes exactly those at the memory the predicate is stated at. -/
theorem s2StringBodyPre_components {mem : Mem} {next : Nat} {c p dst outn xp xj : Nat}
    {len nxp : BitVec 64}
    (h : s2StringBodyPre [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp,
      .ptr xj, .int 64 nxp] mem next) :
    (∃ base, stage2ReadWord mem c 8 = some base) ∧
    (∃ j0, stage2ReadWord mem xj 8 = some j0) ∧
    (∃ ps, readLanes32 mem xp nxp.toNat = some ps) ∧
    (∃ body, readBytes mem p len.toNat = some body) ∧
    (∃ e, stage2ReadWord mem (c + 1112) 8 = some e) ∧
    BodyPositionsSpaced mem c xj xp nxp.toNat p len.toNat := by
  obtain ⟨c', p', len', dst', outn', xp', xj', nxp', base, j0, ps, body, e, hargs,
    hb, hj, hp, hbd, he, hsp, -⟩ := h
  simp only [List.cons.injEq, and_true, true_and, Value.ptr.injEq, Value.int.injEq]
    at hargs
  obtain ⟨hc, hpE, hlen, hdstE, houtnE, hxpE, hxjE, hnxpE⟩ := hargs
  obtain hlenE := eq_of_heq hlen
  obtain hnxpEE := eq_of_heq hnxpE
  subst hc; subst hpE; subst hdstE; subst houtnE; subst hxpE; subst hxjE
  subst hlenE; subst hnxpEE
  exact ⟨⟨base, hb⟩, ⟨j0, hj⟩, ⟨ps, hp⟩, ⟨body, hbd⟩, ⟨e, he⟩, hsp⟩

/-- The eight-byte word's length, as the bound the frame's chaining wants. -/
theorem wordBytes_length_eight (k : Nat) : (wordBytes 8 k).length ≤ 8 :=
  le_of_eq (natToBytes_length k 8)

/-- **Four writes inside four listed entries.**  The shape both accepting arms of
`s2_string_body` have: the destination window, the escape cursor, the length word
and the private slot, each a listed entry at the byte widths given.  Stated with
the region list a variable so the arms instantiate it without re-elaborating the
frame's terms. -/
theorem UnchangedOutside.four_writes {mem : Mem} {R : List (Nat × Nat)}
    {xj outn dst next len : Nat} {o1 o2 o3 slot : List UInt8}
    (hxj : (xj, 8) ∈ R) (houtn : (outn, 8) ∈ R) (hdst : (dst, len) ∈ R)
    (hnext : (next, 8) ∈ R)
    (h1 : o1.length ≤ len) (h2 : o2.length ≤ 8) (h3 : o3.length ≤ 8)
    (h4 : slot.length ≤ 8) :
    UnchangedOutside mem
      (writeBytes (writeBytes (writeBytes (writeBytes mem dst o1) xj o2) outn o3)
        next slot) R :=
  ((((UnchangedOutside.refl' mem R).write_le (a := dst) (w := len)
    ⟨(dst, len), hdst, le_rfl, le_rfl⟩ h1).write_le (a := xj) (w := 8)
    ⟨(xj, 8), hxj, le_rfl, le_rfl⟩ h2).write_le (a := outn) (w := 8)
    ⟨(outn, 8), houtn, le_rfl, le_rfl⟩ h3).write_le (a := next) (w := 8)
    ⟨(next, 8), hnext, le_rfl, le_rfl⟩ h4

set_option maxHeartbeats 1600000 in
/-- **The body's writes on an accepting arm.**  Forms `1` and `2` write the escape
cursor, the decoded-length word, the destination window and the private slot — the
four entries below.  The refusing arm's error record is the fifth entry of
`s2StringBodyFoot`, and it is the only write `form ≠ 0` removes, which is why this
statement is the foot's frame minus that entry and needs no account of the cursor
record's error field.

The three reads are the model's own scrutinees: at a run that answers, the first
three are the words `stage2StringBody` matches on.  The decoded arm's window is
bounded by `hspace`: the expansion's output is no longer than the body it was
given (`escapeDecodeGo_length_le`), and the body's length is the argument's
(`readBytes_length`). -/
theorem s2StringBody_frame_of_form {mem : Mem} {c p len dst outn xp xj nxp next : Nat}
    {m : Mem} {form : Nat} {slot : List UInt8} {base j0 : Nat} {ps : List Nat}
    (hbase : stage2ReadWord mem c 8 = some base)
    (hj0 : stage2ReadWord mem xj 8 = some j0)
    (hps : readLanes32 mem xp nxp = some ps)
    (hspace : BodyPositionsSpaced mem c xj xp nxp p len)
    (hm : stage2StringBody mem c p len dst outn xp xj nxp = some (m, form, slot))
    (hform : form ≠ 0) :
    UnchangedOutside mem (writeBytes m next slot)
      [(xj, 8), (outn, 8), (dst, len), (next, 8)] := by
  unfold stage2StringBody at hm
  simp only [hbase, hj0, hps] at hm
  -- the four listed entries, at this call's numbers
  have hframeFour : ∀ {mem' : Mem} {o1 o2 o3 slot : List UInt8},
      o1.length ≤ len → o2.length ≤ 8 → o3.length ≤ 8 → slot.length ≤ 8 →
      UnchangedOutside mem'
        (writeBytes (writeBytes (writeBytes (writeBytes mem' dst o1) xj o2) outn o3)
          next slot)
        [(xj, 8), (outn, 8), (dst, len), (next, 8)] := by
    intro mem' o1 o2 o3 slot h1 h2 h3 h4
    exact UnchangedOutside.four_writes (by simp) (by simp) (by simp) (by simp)
      h1 h2 h3 h4
  split at hm
  · -- form `1`: the empty window; the cursor and the length word
    have hinj := Option.some.inj hm
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨rfl, -, rfl⟩ := hinj
    exact hframeFour (o1 := []) (slot := []) (by simp)
      (wordBytes_length_eight _) (wordBytes_length_eight _) (by simp)
  · split at hm
    · simp at hm
    · rename_i body hbody
      split at hm
      · -- form `2`: the decoded prefix and the three words
        rename_i out k hdec
        have hinj := Option.some.inj hm
        simp only [Prod.mk.injEq] at hinj
        have hle := escapeDecodeGo_length_le body
          (hspace base j0 ps body hbase hj0 hps hbody) 0 [] out k hdec
        have hbl : body.length = len := JsonEntrySteps.readBytes_length mem p len hbody
        simp only [List.length_nil, Nat.zero_add] at hle
        have hle' : out.length ≤ body.length := by simpa using hle
        have houtle : out.length ≤ len := by rw [hbl] at hle'; exact hle'
        obtain ⟨rfl, -, rfl⟩ := hinj
        exact hframeFour (o1 := out) (slot := wordBytes 8 out.length) houtle
          (wordBytes_length_eight _) (wordBytes_length_eight _)
          (wordBytes_length_eight _)
      · -- the refusing arm: form `0`
        rename_i off k href
        split at hm
        · have h0 : (0 : Nat) = form :=
            congrArg (fun p : Mem × Nat × List UInt8 => p.2.1) (Option.some.inj hm)
          exact absurd h0.symm hform
        · simp at hm

/-! ### The decoded length at the call's own memory

`s2StringBody_outn_le` states the length at the *model's* memory; the call's memory
is that memory with the body's private `%ei` slot written at the call's `next`
(`s2StringBodyPost`'s `r.mem = writeBytes m next slot`).  The pre keeps the slot
away from `%outn.i` (`RegionsApart next 8 outn 8`), so the word read at `outn` is
the same in both.  These three lemmas are what a consumer composes: the separation
projected off the pre, the slot's width, and the read at the call's memory. -/

/-- **The pre's slot/`%outn.i` separation**, read off the precondition at a literal
argument list. -/
theorem s2StringBodyPre_next_outn {mem : Mem} {next : Nat} {c p dst outn xp xj : Nat}
    {len nxp : BitVec 64}
    (hpre : s2StringBodyPre [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn,
      .ptr xp, .ptr xj, .int 64 nxp] mem next) :
    RegionsApart next 8 outn 8 := by
  obtain ⟨c', p', len', dst', outn', xp', xj', nxp', base, j0, ps, body, e', hargs,
    hb, hj, hp, hbd, he, hsp, hp_lt, hbase_le, hwrap, hlen_lt, hj0_lt, hnxp_lt,
    houtn, hdst, herr, hxj_next, hxj_outn, hxj_dst, hxj_err, hnext_outn, -⟩ := hpre
  simp only [List.cons.injEq, and_true, true_and, Value.ptr.injEq, Value.int.injEq]
    at hargs
  obtain ⟨hc, hpE, hlen, hdstE, houtnE, hxpE, hxjE, hnxpE⟩ := hargs
  obtain hlenE := eq_of_heq hlen
  obtain hnxpEE := eq_of_heq hnxpE
  subst hc; subst hpE; subst hdstE; subst houtnE; subst hxpE; subst hxjE
  subst hlenE; subst hnxpEE
  exact hnext_outn

/-- **The callee's private slot is at most eight bytes.**  The model's third
component is `[]` on the body-itself arm and the eight-byte `%ei` word on the
decoded and refusing ones, so a consumer reading `writeBytes m next slot` needs no
width beyond the `alloca`'s eight bytes. -/
theorem stage2StringBody_slot_le {mem : Mem} {c p len dst outn xp xj nxp : Nat}
    {base j0 : Nat} {ps : List Nat} {m : Mem} {form : Nat} {slot : List UInt8}
    (hbase : stage2ReadWord mem c 8 = some base)
    (hj0 : stage2ReadWord mem xj 8 = some j0)
    (hps : readLanes32 mem xp nxp = some ps)
    (hm : stage2StringBody mem c p len dst outn xp xj nxp = some (m, form, slot)) :
    slot.length ≤ 8 := by
  unfold stage2StringBody at hm
  simp only [hbase, hj0, hps] at hm
  split at hm
  · -- the body-itself arm writes no slot
    have hinj := Option.some.inj hm
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨-, -, rfl⟩ := hinj
    simp
  · split at hm
    · simp at hm
    · rename_i body hbody
      split at hm
      · -- the decoded arm's slot is the decoded length
        rename_i out k hdec
        have hinj := Option.some.inj hm
        simp only [Prod.mk.injEq] at hinj
        obtain ⟨-, -, rfl⟩ := hinj
        exact wordBytes_length_eight _
      · -- the refusing arm's slot is the body-relative offset
        rename_i off k href
        split at hm
        · have hinj := Option.some.inj hm
          simp only [Prod.mk.injEq] at hinj
          obtain ⟨-, -, rfl⟩ := hinj
          exact wordBytes_length_eight _
        · simp at hm

/-- **The decoded length at the caller's memory.**  `s2StringBody_outn_le`'s word
survives the private slot's write at `next`, because the pre separates them; so the
answer's length and its bound are the call's, at `writeBytes m next slot` — which is
`s2StringBodyPost`'s `r.mem`. -/
theorem s2StringBody_outn_at_call {mem : Mem} {c p dst outn xp xj : Nat}
    {len nxp : BitVec 64} {m : Mem} {form : Nat} {slot : List UInt8}
    {next base j0 : Nat} {ps : List Nat}
    (hbase : stage2ReadWord mem c 8 = some base)
    (hj0 : stage2ReadWord mem xj 8 = some j0)
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hspace : BodyPositionsSpaced mem c xj xp nxp.toNat p len.toNat)
    (hm : stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat =
      some (m, form, slot))
    (hform : form ≠ 0)
    (hsep : RegionsApart next 8 outn 8) :
    ∃ l, readBytes (writeBytes m next slot) outn 8 = some (wordBytes 8 l) ∧
      l ≤ len.toNat := by
  obtain ⟨l, hr, hle⟩ := s2StringBody_outn_le hm hspace hform
  have hslot := stage2StringBody_slot_le hbase hj0 hps hm
  refine ⟨l, ?_, hle⟩
  refine (walkReadBytes_writeBytes_outside (m := m) (v := slot) (start := next)
    (addr := outn) (n := 8) ?_).trans hr
  rcases hsep with h | h
  · exact Or.inr (by omega)
  · exact Or.inl h

/-! ### Presence survives the call

The walk's presence clause (`WalkInv.owned`) is over `walkStaged`, and the carry
the link builds moves only the arena cursor, the spans and the record in flight —
none of which `walkStaged` reads: its extents are the staging's and its scratch is
`C.stage`'s.  So the presence half is not about the carry at all, and not about
the foot either.  It is about the call's memory: every arm of `stage2StringBody`
answers with `writeBytes` applied to the caller's memory (the error record's three
stores included), and `hasBytes_writeBytes` says a write adds cells and removes
none.  That is why the staging's separation does not appear below: it is not
needed once presence is read as monotone under writes. -/

/-- **Presence is monotone through the string body's model.**  Every arm of
`stage2StringBody` writes over the memory it was handed — the empty arm's cursor
and length words, the decoded arm's prefix and two words, and the refusing arm's
record and cursor — so a range present before the call is present after it. -/
theorem stage2StringBody_hasBytes {mem : Mem} {c p len dst outn xp xj nxp : Nat}
    {m : Mem} {form : Nat} {slot : List UInt8}
    (hm : stage2StringBody mem c p len dst outn xp xj nxp = some (m, form, slot)) :
    ∀ {a k : Nat}, HasBytes mem a k → HasBytes m a k := by
  intro a k h
  unfold stage2StringBody at hm
  split at hm
  · simp only [] at hm
    split at hm
    · have hinj := Option.some.inj hm
      simp only [Prod.mk.injEq] at hinj
      obtain ⟨rfl, -, -⟩ := hinj
      exact hasBytes_writeBytes (hasBytes_writeBytes h)
    · split at hm
      · simp at hm
      · split at hm
        · have hinj := Option.some.inj hm
          simp only [Prod.mk.injEq] at hinj
          obtain ⟨rfl, -, -⟩ := hinj
          exact hasBytes_writeBytes (hasBytes_writeBytes (hasBytes_writeBytes h))
        · split at hm
          · have hinj := Option.some.inj hm
            simp only [Prod.mk.injEq] at hinj
            obtain ⟨rfl, -, -⟩ := hinj
            refine hasBytes_writeBytes ?_
            unfold stage2ErrSetMsg stage2ErrSet
            exact hasBytes_writeBytes (hasBytes_writeBytes (hasBytes_writeBytes h))
          · simp at hm
  · simp at hm

/-- **The caller's presence over `walkStaged` survives the call.**  The callee's
answer names its memory as `writeBytes` of the model's memory at the call's
cursor, and the model's memory carries the caller's cells by
`stage2StringBody_hasBytes`; two applications of `hasBytes_writeBytes` give the
conclusion.  The presence is stated at the carry the link builds, and `walkStaged`
does not read the fields the link moves, so its extent list is the caller's.

The hypothesis is the callee's own answer (`s2StringBodyPost`), whose producer at
the call is `s2StringBody_sound` from the pre assembled above and the call's
outcome.  The frame is not a hypothesis: presence does not need read equality,
because no arm of the model erases a cell. -/
theorem s2StringBodyFoot_presence_walkStaged {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {mem : Mem} {next : Nat} {r : CallOutcome}
    {p A ext : Nat} {len nxp : BitVec 64}
    (hpost : s2StringBodyPost [.ptr C.stage.c, .ptr (G.b + p + 1), .int 64 len,
      .ptr (G.dst + A), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
      .int 64 nxp] mem next r)
    (hmem : ∀ q ∈ walkStaged G C, HasBytes mem q.1 q.2) :
    ∀ q ∈ walkStaged G { C with block := "NodeBlock31", alen := C.alen + ext, spans := C.spans ++ [(C.alen, ext)], pending := none },
      HasBytes r.mem q.1 q.2 := by
  intro q hq
  have hq' : q ∈ walkStaged G C := hq
  obtain ⟨m, form, slot, hm, -, hrmem, -⟩ := hpost
  rw [hrmem]
  exact hasBytes_writeBytes (stage2StringBody_hasBytes hm (hmem q hq'))

/-- **A read outside the run's region list is the staging's read.**  The per-byte
form of `UnchangedOutside`, at a range the list misses. -/
theorem readBytes_of_frame {m0 m : Mem} {R : List (Nat × Nat)} {a N : Nat}
    (h : UnchangedOutside m0 m R)
    (hsep : ∀ r ∈ R, r.1 + r.2 ≤ a ∨ a + N ≤ r.1) :
    readBytes m a N = readBytes m0 a N := by
  induction N generalizing a with
  | zero => rfl
  | succ N ih =>
      have hb : readByte m a = readByte m0 a :=
        h a (fun r hr hlt => by rcases hsep r hr with h' | h' <;> omega)
      have ht : readBytes m (a + 1) N = readBytes m0 (a + 1) N :=
        ih (a := a + 1) (fun r hr => by rcases hsep r hr with h' | h' <;> omega)
      simp only [readBytes, hb, ht]

/-! ### The body's foot on an accepting arm, and the crossings it makes

`s2StringBody_frame_of_form` is the accepting arm's frame over the four entries the
arm writes; the contract's `foot` names five, the fifth being the refusal record the
same staging would have written had the arm refused.  A frame over four is a frame
over five — the wider list is the *weaker* claim — so `UnchangedOutside.of_covered`
closes the gap, and the resulting silence is what the caller's four crossings read.

The crossings are the caller's, not the callee's: the run's log, its event stream
and its two carried stacks all lie outside the body's write list, so the foot's
silence **is** their read equality.  That is why the log and the trace are read from
the foot rather than from the walk's widened frame — `walkWideAt` *contains* the log
and the stream as entries, so a frame over that list says nothing about either. -/

/-- **The walk's arena window and the event stream are separate.**  Both are ABI
regions, so the geometry's own separation orders them; the two are entries three
and four of `stage2Regions`. -/
theorem walkArena_ev_sep {m0 : Mem} (G : WalkGeom m0) :
    G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ G.ev ∨ G.ev + G.evcap ≤ G.dst := by
  have hp : (stage2Regions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev G.evcap
      G.ndst G.nev G.err).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := G.separate
  have h' := List.pairwise_iff_getElem.mp hp 3 4 (by simp [stage2Regions])
    (by simp [stage2Regions]) (by omega)
  simpa [stage2Regions] using h'

/-- **The walk's log and its arena window are separate.**  The log is one of the
seven staged objects and the arena one of the thirteen ABI ones, so the staging's
separation orders them. -/
theorem walkLog_arena_sep {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) :
    S.z + stage2LogExtent ≤ G.dst ∨ G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ S.z :=
  disjointRegions_against S.walk_separate
    (a := G.dst) (n := G.ndst0 + G.n + stage2ArenaReserve)
    (by simp [stage2WalkRegions, stage2Regions])
    (S.z, stage2LogExtent) (by simp [stage2WalkRegions, stage2StagedWrites])

/-- **A read across the two stores at the cursor record's `%k` field and `%outn.i`.**
The walk's `if.end207.i` writes the cursor record's `%k` word at `%c.i + 32` and
`if.end256.i` writes the `%outn.i` zero, and both stores sit inside the walk's write
extent.  A read that misses both is the caller's read, which is what transports a
head-stated precondition to the memory the string body is called at. -/
theorem walkReadBytes_two_writes {m : Mem} {v w : List UInt8} {c nt addr n : Nat}
    (h1 : addr + n ≤ c + 32 ∨ (c + 32) + v.length ≤ addr)
    (h2 : addr + n ≤ nt + 20 ∨ (nt + 20) + w.length ≤ addr) :
    readBytes (writeBytes (writeBytes m (c + 32) v) (nt + 20) w) addr n
      = readBytes m addr n := by
  rw [walkReadBytes_writeBytes_outside (m := writeBytes m (c + 32) v) (v := w)
      (start := nt + 20) (addr := addr) (n := n) h2,
    walkReadBytes_writeBytes_outside (m := m) (v := v) (start := c + 32)
      (addr := addr) (n := n) h1]

/-- **The callee's four write entries are inside the walk's frame.**  The accepting
arms write the escape cursor, the decoded-length word, the destination window and the
private slot, and every one of them lies inside an entry of `walkWideAt` at the carry
the call builds and the cursor the call leaves: the first two and the private slot in
the cursor's interval, the window in the arena's carried prefix.  That is the
coverage `UnchangedOutside.widen` needs to transfer the callee's silence from the
four entries to the run's own list.

No account of the refusal record's slot is needed: an accepting arm does not write
it, so the frame over the four entries is the frame the arm proves. -/
theorem s2StringBodyFrame_walkWideAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {mem : Mem} {next m : Nat} {r : CallOutcome} {A ext len : Nat}
    (hAle : A ≤ C.alen) (hlen : len ≤ ext)
    (hnext : G.next0 + stage2BootstrapExtent ≤ next) (hm : next + 8 ≤ G.next0 + m)
    (hframe : UnchangedOutside mem r.mem
      [(G.next0 + 12, 8), (G.next0 + 20, 8), (G.dst + A, len), (next, 8)]) :
    UnchangedOutside mem r.mem
      (walkWideAt G { C with block := "NodeBlock31", alen := C.alen + ext, spans := C.spans ++ [(C.alen, ext)], pending := none } m) := by
  let C' : WalkCarry G := { C with block := "NodeBlock31", alen := C.alen + ext, spans := C.spans ++ [(C.alen, ext)], pending := none }
  change UnchangedOutside mem r.mem (walkWideAt G C' m)
  have hge : G.next0 + 28 ≤ next := by
    simpa only [stage2BootstrapExtent] using hnext
  have hint : (G.next0, m) ∈ walkWideAt G C' m :=
    List.mem_append_right _ (List.mem_cons_self ..)
  have hdst : (G.dst, C'.alen) ∈ walkWideAt G C' m := by
    show (G.dst, C'.alen) ∈ walkPresent G C' ++ [(G.next0, m)]
    exact List.mem_append_left _ (by
      show (G.dst, C'.alen) ∈
        [(G.dst, C'.alen), (G.ev, C'.evlen)] ++
          stage2ReportScratch C'.stage.c C'.stage.ctype C'.stage.cst C'.stage.tok
            C'.stage.s C'.stage.z C'.stage.e C'.stage.d
      exact List.mem_append_left _ (List.mem_cons_self))
  have hcov : ∀ rr ∈ [(G.next0 + 12, 8), (G.next0 + 20, 8), (G.dst + A, len),
      (next, 8)], ∃ q ∈ walkWideAt G C' m, q.1 ≤ rr.1 ∧ rr.1 + rr.2 ≤ q.1 + q.2 := by
    intro rr hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, hint, by omega, by omega⟩
    · exact ⟨_, hint, by omega, by omega⟩
    · exact ⟨_, hdst, by show G.dst ≤ G.dst + A; omega,
        by show (G.dst + A) + len ≤ G.dst + (C.alen + ext); omega⟩
    · exact ⟨_, hint, by omega, by omega⟩
  refine UnchangedOutside.widen hframe ?_
  intro a ha rr hrr
  obtain ⟨q, hq, hqlo, hqhi⟩ := hcov rr hrr
  exact fun hin => ha q hq ⟨le_trans hqlo hin.1, lt_of_lt_of_le hin.2 hqhi⟩

/-- **The four crossings at the string body's call.**  The callee's four write
entries are the arms' whole footprint, so its silence outside them is the caller's
four read equalities, and its presence is presence monotonicity:

* the log's every field, inside `(z, stage2LogExtent)`;
* the event stream's written suffix at `(ev + nev0)`, inside `(ev, evcap)`;
* the two carried stack copies at their staged base, inside `(ctype, extent)`;
* the caller's presence over `walkStaged`, which no arm erases
  (`s2StringBodyFoot_presence_walkStaged`).

`hAwin` places the body's destination window inside the arena's *staged* extent —
the bound the log's arena word cannot give, because that word lags the carry — and
it is what the stack and log crossings read against the arena's entries. -/
theorem s2StringBodyFrame_facts {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) {p A ext len : Nat} {r : CallOutcome}
    (hpost : s2StringBodyPost
      [.ptr C.stage.c, .ptr (G.b + p + 1), .int 64 (BitVec.ofNat 64 ext),
       .ptr (G.dst + A), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
       .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next r)
    (hframe : UnchangedOutside s.mem r.mem
      [(G.next0 + 12, 8), (G.next0 + 20, 8), (G.dst + A, len), (s.next, 8)])
    (hAwin : A + len ≤ G.ndst0 + G.n + stage2ArenaReserve) :
    (∀ q ∈ walkStaged G { C with block := "NodeBlock31", alen := C.alen + ext, spans := C.spans ++ [(C.alen, ext)], pending := none }, HasBytes r.mem q.1 q.2) ∧
    (∀ off w, off + w ≤ stage2LogExtent →
      readBytes r.mem (C.stage.z + off) w = readBytes s.mem (C.stage.z + off) w) ∧
    (readBytes r.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length =
      readBytes s.mem (G.ev + G.nev0)
        (C.events.map EventRecord.encodedBytes).flatten.length) ∧
    WalkStackBytes r.mem C.stage.ctype C.tyMap C.wlen ∧
    WalkStackBytes r.mem C.stage.cst C.stMap C.wlen := by
  -- the staged objects' extents, at the cursor's watermark: numerals, because the
  -- crossings below compare them against offsets the frame names literally
  have hwZ : C.stage.z + 64 ≤ G.next0 := by
    have h := C.stage.sevenEnd (C.stage.z, stage2LogExtent) (by simp [stage2StagedWrites])
    simpa only [stage2LogExtent] using h
  have hwTy : C.stage.ctype + 520 ≤ G.next0 := by
    have h := C.stage.sevenEnd (C.stage.ctype, stage2StackExtent)
      (by simp [stage2StagedWrites])
    simpa only [stage2StackExtent] using h
  have hwSt : C.stage.cst + 520 ≤ G.next0 := by
    have h := C.stage.sevenEnd (C.stage.cst, stage2StackExtent)
      (by simp [stage2StagedWrites])
    simpa only [stage2StackExtent] using h
  have hwEv : G.ev + G.evcap ≤ G.next0 :=
    G.watermark (G.ev, G.evcap) (by simp [stage2Regions])
  have hLE : C.wlen ≤ 520 := by
    have h := hInv.wlen_cap
    simpa only [stage2StackExtent] using h
  have hnext : G.next0 ≤ s.next := by
    have h := hInv.next_ge
    simp only [stage2BootstrapExtent] at h
    omega
  refine ⟨s2StringBodyFoot_presence_walkStaged hpost hInv.owned, ?_, ?_, ?_, ?_⟩
  · -- the log, read through the arm's silence
    intro off w hoffw
    have hoffw' : off + w ≤ 64 := by simpa only [stage2LogExtent] using hoffw
    refine readBytes_of_frame hframe ?_
    intro rr hrr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrr
    rcases hrr with rfl | rfl | rfl | rfl
    · right; omega
    · right; omega
    · rcases walkLog_arena_sep C.stage with h | h
      · simp only [stage2LogExtent] at h
        right; omega
      · simp only [stage2ArenaReserve] at h
        have hAw := hAwin
        simp only [stage2ArenaReserve] at hAw
        left; omega
    · right; omega
  · -- the event stream, read through the foot's silence
    have hevcap : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
      have hsum := EventRecord.sum_encodedSize_le C.events
      simp only [stage2RecordBytes] at hsum
      have h4' := G.evRoom
      simp only [stage2RecordBytes] at h4'
      have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
          (C.events.map EventRecord.encodedSize).sum := by
        simp only [List.length_flatten, List.map_map]
        rfl
      have h1 : C.events.length ≤ G.nep := hInv.events_nep
      have h3 := G.nep_le
      omega
    refine readBytes_of_frame hframe ?_
    intro rr hrr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrr
    rcases hrr with rfl | rfl | rfl | rfl
    · right; omega
    · right; omega
    · rcases walkArena_ev_sep G with h | h
      · simp only [stage2ArenaReserve] at h
        have hAw := hAwin
        simp only [stage2ArenaReserve] at hAw
        left; omega
      · right; omega
    · right; omega
  · -- the type stack's copy
    intro i hi
    have hx : ∀ rr ∈ [(G.next0 + 12, 8), (G.next0 + 20, 8), (G.dst + A, len),
        (s.next, 8)], ¬ (rr.1 ≤ C.stage.ctype + i ∧ C.stage.ctype + i < rr.1 + rr.2) := by
      intro rr hrr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrr
      rcases hrr with rfl | rfl | rfl | rfl
      · intro hcon; omega
      · intro hcon; omega
      · rcases (stack_arena_sep hInv).1 with h | h
        · intro hcon; omega
        · simp only [stage2ArenaReserve] at h
          have hAw := hAwin
          simp only [stage2ArenaReserve] at hAw
          intro hcon; omega
      · intro hcon; omega
    rw [hframe (C.stage.ctype + i) hx]
    exact hInv.tyBytes i hi
  · -- the state stack's copy
    intro i hi
    have hx : ∀ rr ∈ [(G.next0 + 12, 8), (G.next0 + 20, 8), (G.dst + A, len),
        (s.next, 8)], ¬ (rr.1 ≤ C.stage.cst + i ∧ C.stage.cst + i < rr.1 + rr.2) := by
      intro rr hrr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrr
      rcases hrr with rfl | rfl | rfl | rfl
      · intro hcon; omega
      · intro hcon; omega
      · rcases (stack_arena_sep hInv).2 with h | h
        · intro hcon; omega
        · simp only [stage2ArenaReserve] at h
          have hAw := hAwin
          simp only [stage2ArenaReserve] at hAw
          intro hcon; omega
      · intro hcon; omega
    rw [hframe (C.stage.cst + i) hx]
    exact hInv.stBytes i hi

/-! ### The producer at the walk's string-body call

`HstringFacts.hpreS` (`JsonStage2WalkDispatchWitnessString`) and
`WalkLink.z_arena_reserve_exit` (`JsonStage2WalkCall`) both take the string body's
precondition as a supplied premise.  This section is its producer: the same
predicate, at the call's own argument list, read off `WalkInv`'s clauses, the
geometry, the staging and the call's registers.

The assembler above states the target with every witness and every conjunct named.
Here each conjunct is either derived or named, and the named ones carry the
producer that would make them derivable:

* **derived (30 of the 37).**  The document's body window (`hbody`) is a subrange
  of `G.b .. G.b + n + stage2ReadTail` — `WalkGeom.doc` for the document and
  `WalkGeom.tail` for the read-past bytes — transported to the walk's memory by
  `WalkInv.frame`.  The escape list's lanes (`hps`) are `WalkGeom.esc` plus the
  same transport.  The destination window's presence (`hdst`) is the arena's
  `walkStaged` entry, with the reservation's word bounded by the carried cursor
  (`logArena_le`) and the window placed inside it by `pending_cursor` and
  `pending_len`.  The error record's presence (`herr`) is the seven's `(e, 24)`
  entry.  The twenty `RegionsApart` facts and the two lane exclusions are the
  staging's separation (`WalkGeom.separate`, `WalkStage.separate`,
  `WalkStage.dSep`) read at the call's addresses, with the watermark placing every
  staged object at or below `G.next0` and the four `alloca` slots at or above it.
  Four of the six bounds (`p < 2 ^ 64`, `base ≤ p`, the window's non-wrapping and
  the sentinel exclusion) follow from `G.maxDoc`, the record in flight and `hfit`.
* **named (7 of the 37).**  The cursor record's base and error words, the `%xj.i`
  slot's word, the `%outn.i` slot's presence, the escape list's spacing, the scan
  index's sign bound and the escape count's sign bound.  Each is a fact the walk's
  vocabulary does not carry; the docstring names the producer for every one, and
  none is added to `WalkInv` (which the frame repair owns).

**The reservation's document room is not a hypothesis.**  The body's window runs
`G.b + p + 1 .. G.b + p + 1 + ext`, and `pending_len` gives `p + ext ≤ G.n`, so the
window ends at `G.b + G.n + 1` at the widest: its last byte is the document's first
read-past byte, which `WalkGeom.tail` stages and the document's region
(`(b, n + stage2ReadTail)`) covers.  So the producer reads the window out of
`G.doc` and `G.tail` concatenated, and nothing stronger than `pending_len` is
needed.  (The link's `hwin`, `C.alen + ext ≤ G.n`, is a different statement — it is
the appended span's room — and `pending_cursor`/`pending_len` give only
`C.alen + ext ≤ G.ndst0 + G.n`; it stays supplied there.)

Two hypotheses are not pre conjuncts: the document's address width (`hfit`, which
the body's `ptrtoint` needs) and the allocator cursor's placement (`hge`, finding
20: the invariant carries no `s.next`).

The nine named facts are all true at the loop's first string-body call, so the
statement is not vacuous there: `%c.i`'s base and error words are the `entry`
block's stores (`JsonStage2IR:213`, `220-221`), `%xj.i` and `%outn.i` its and
`if.end207.i`'s zeros (`227`, `655`), the cursor is `G.next0 + 28`, and the rest are
properties of the document and the caller's escape list.  What is missing is not a
state at which they hold but a `WalkInv` clause that carries them past the blocks
between the store and the call.  The register hypotheses (`%c.i`, `%xp`,
`%nxp`, `%arrayidx10.i`, `%sub260.i`) are the link's own and are carried rather than
consumed — the statement is the call's, so the numbers are named there; they are
spelled `_hc` and so on because the producer reads the *values*, not the bindings,
and dropping them would drop the call's vocabulary from its own producer.  Four of
them are the carriers' now: `%c.i`, `%xp` and `%nxp` are `walkStaticRegs`', so a
caller supplies `_hc`/`_hxp`/`_hnxp` from `WalkInv.regs`, and `%arrayidx10.i` is
the per-iteration `WalkIter.regarr`, which `WalkInv.iter` reads at every loop
state. -/

/-- **The lane reader through a run that wrote outside the list.** -/
theorem readLanes32_of_frame {m0 m : Mem} {R : List (Nat × Nat)} {a k : Nat}
    (h : UnchangedOutside m0 m R)
    (hsep : ∀ r ∈ R, r.1 + r.2 ≤ a ∨ a + 4 * k ≤ r.1) :
    readLanes32 m a k = readLanes32 m0 a k := by
  refine JsonEntrySteps.readLanes32_congr_bytes (m := m0) (m' := m) ?_
  intro j _hj
  exact h (a + j) (fun r hr hlt => by rcases hsep r hr with h' | h' <;> omega)

/-- **A flat read supplies the lanes.**  `readLanes32` is the four-byte grouping of
the same range, so a range read back whole is read back as lanes.  This is what
turns the staging's `HasBytes` over the escape list into the `readLanes32` the
precondition names. -/
theorem readLanes32_of_readBytes {m : Mem} (a k : Nat) :
    ∀ {bs : List UInt8}, readBytes m a (4 * k) = some bs →
      ∃ ps, readLanes32 m a k = some ps := by
  induction k generalizing a with
  | zero => intro _bs _; exact ⟨[], rfl⟩
  | succ k ih =>
      intro bs h
      have h4 : readBytes m a (4 + 4 * k) = some bs := by
        rwa [show 4 * (k + 1) = 4 + 4 * k from by omega] at h
      obtain ⟨hfirst, hrest⟩ := readBytes_split m a 4 (4 * k) h4
      obtain ⟨tl, htl⟩ := ih (a := a + 4) hrest
      refine ⟨bytesToNat (bs.take 4) :: tl, ?_⟩
      show (readBytes m a 4).bind (fun b4 => (readLanes32 m (a + 4) k).map
        (fun rest => bytesToNat b4 :: rest)) = some (bytesToNat (bs.take 4) :: tl)
      rw [hfirst, htl]
      rfl

/-- **An ABI object against the walk's seven appended objects.**  The adapter's
separation, read in the orientation a frame wants: the object ends before the
appended one starts, or the appended one ends before the object starts. -/
theorem walkWrites_against_abi {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G)
    {a n : Nat}
    (ha : (a, n) ∈ stage2Regions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err) :
    ∀ r ∈ stage2StagedWrites S.c S.ctype S.cst S.tok S.s S.z S.e,
      r.1 + r.2 ≤ a ∨ a + n ≤ r.1 := by
  have h : DisjointRegions (stage2Regions G.b G.n G.ep G.nep G.xp G.nxp G.dst
      G.ndst0 G.ev G.evcap G.ndst G.nev G.err ++
      stage2StagedWrites S.c S.ctype S.cst S.tok S.s S.z S.e) := by
    simpa only [stage2WalkRegions] using S.walk_separate
  exact disjointRegions_against h ha

/-- **A staged region the walk never writes, against the cursor's write list.**  The
list's two prefixes are inside their staged extents (`alen` and `evlen` grow inside
them), the seven and `%d.i` are separated from the region by the adapter's
staging (`WalkStage.separate`, `WalkStage.dSep`), and the cursor's interval starts
at `G.next0` — so a region staged entirely below `G.next0`, and separated from the
arena's and the event stream's staged extents, is outside every entry.

The two extents are hypotheses rather than `WalkInv`'s projections so the lemma is
about the addresses: `WalkInv.alen_le` and `WalkInv.evlen_le` introduce them. -/
theorem walkWideAt_abi_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {a n m : Nat}
    (ha : (a, n) ∈ stage2Regions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err)
    (harena : G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ a ∨ a + n ≤ G.dst)
    (hevent : G.ev + G.evcap ≤ a ∨ a + n ≤ G.ev)
    (hale : C.alen ≤ G.ndst0 + G.n)
    (hevcap : C.evlen ≤ G.evcap)
    (hwater : a + n ≤ G.next0) :
    ∀ q ∈ walkWideAt G C m, q.1 + q.2 ≤ a ∨ a + n ≤ q.1 := by
  intro q hq
  simp only [walkWideAt, walkPresent] at hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_cons.mp hq with rfl | hq
      · rcases harena with h | h
        · left; show G.dst + C.alen ≤ a; omega
        · right; show a + n ≤ G.dst; exact h
      · rcases List.mem_cons.mp hq with rfl | hq
        · rcases hevent with h | h
          · left; show G.ev + C.evlen ≤ a; omega
          · right; show a + n ≤ G.ev; exact h
        · exact absurd hq (by simp)
    · simp only [stage2ReportScratch] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact walkWrites_against_abi C.stage ha q hq
      · rcases List.mem_cons.mp hq with rfl | hq
        · rcases C.stage.dSep (a, n) (by
            simp only [stage2WalkRegions]; exact List.mem_append_left _ ha) with h | h
          · right; show a + n ≤ C.stage.d; exact h
          · left; show C.stage.d + 8 ≤ a; exact h
        · exact absurd hq (by simp)
  · rcases List.mem_cons.mp hq with rfl | hnil
    · right; exact hwater
    · exact absurd hnil (by simp)

/-- **The producer of the string body's precondition at the walk's call.**  The
witnesses are the staging's — `c = C.stage.c`, `xj = G.next0 + 12`,
`outn = G.next0 + 20` — and the argument list is the block's
(`JsonStage2WalkCall`'s `%add.ptr271.i` is `G.b + p + 1`, `%add.ptr.i` is
`G.dst + A.toNat`), with `p`, `off` and `ext` the record in flight's
(`C.pending`).

**Derived.**  `hbody` and `hps` are the staging's reads at the staging's memory,
transported across the walk by the frame (`WalkInv.frame`), because the document's
window and the escape list end at or below `G.next0` and the walk's write list
starts there or is separated from them.  `hdst` is the arena's `walkStaged` entry
(`WalkInv.owned`) narrowed to the reserved window, where `logArena_le` bounds
`A.toNat` by the carried cursor and `pending_cursor`/`pending_len` place
`A.toNat + ext` inside the staged extent.  `herr` is the seven's `(e, 24)` entry.
The twenty separations and the two lane exclusions are read off
`WalkGeom.separate`, `WalkStage.separate` and `WalkStage.dSep` at the call's
addresses.  The bounds follow from `G.maxDoc`, `G.bLt`, `G.nxpLt` and the geometry's
watermark.

**Named, with the producer that would make each derivable.**

* **`hbase`** — the cursor record's base word holds the document's base.  Producer:
  `entry`'s store of `%3` at `%c.i` (`JsonStage2IR:213`), which no block of the walk
  rewrites.  It is not a `WalkInv` clause, and `%c.i` lies inside `walkWide`, so
  the frame says nothing about it (the clause would be a value, not a silence).
* **`he`** — the cursor record's error pointer is the staging's `%e`.  Producer:
  `entry`'s store at `%c.i + 1112` (`JsonStage2IR:220-221`).  Same gap and same
  reason as `hbase`; the error record's *presence* is derived, its address is not.
* **`hj0`**, **`hj0_lt`** — the scan cursor's slot at `%xj.i`, and its sign bound.
  Producer: `entry`'s zero store (`JsonStage2IR:227`) and each body's write-back,
  with the index below the escape count.  `WalkInv` carries neither the four
  `alloca` slots' contents nor `s.next`, and a body's write-back leaves the slot
  free (`s2StringBodyPost`), so no clause can carry it.
* **`houtn`** — the decoded-length slot's presence.  Producer: `if.end207.i`'s zero
  store at `%outn.i` (`JsonStage2IR:655`).  `WalkInv.owned` deliberately omits the
  four `alloca` slots (`walkStaged`), so presence of that byte is not carried.
* **`hspaced`** — the escape list's spacing over the body's document range.  It is
  a property of the document's positions, not of the staging: `WalkGeom` states no
  `BodyPositionsSpaced` at all, and it cannot be transported from `m0` because two
  of the four reads it is about (`c`, `xj`) lie inside `walkWide`.
* **`hnxp_lt`** — the escape count's sign bound.  Producer: the escape list's
  staged extent (`4 * nxp` bytes exist, so the count is below the memory's size) or
  the caller's `%nxpSlot` word; no lemma in the tree converts `HasBytes` into a size
  bound, and `WalkGeom.nxpLt` stops at `2 ^ 64`.

**Two hypotheses that are not pre conjuncts.**

* **`hfit`** — `G.b + G.n + stage2ReadTail ≤ 2 ^ 64`: the document's window inside
  the 64-bit address space, which the body's `ptrtoint` needs.  Producer: the ABI's
  own address width (`stage2.h`), and the pipeline's staging, which reads the
  document out of a `Mem` a caller handed over; `WalkGeom` states `G.b < 2 ^ 64`
  and the document's length separately and never their sum.
* **`hge`** — `G.next0 + 28 ≤ s.next`: the allocator cursor's placement.  This is
  finding 20's missing clause: the seed's `walkSeedFinalState` leaves the cursor at
  `G.next0 + 28` and the allocator only advances, but `WalkInv` carries no `s.next`,
  so the facts that place the body's private `%ei` slot below every other object
  are the caller's.  **Producer: the walk's cursor pin** — the clause the frame
  repair is adding to `WalkInv` (either `s.next = G.next0 + C.nb` or this lower
  bound, whichever is uniform at the construction sites).  Until it lands the fact
  is the caller's.

**`hge` is one side of one fact, and the frame needs the other.**  This producer
uses only the lower bound: every object staged at or below `G.next0` must end
before the callee's private `%ei` slot, which sits at `s.next`.  The frame side
(`s2StringBodyFoot_frame_walkWideAt`) needs the upper one: the slot's eight bytes
lie inside the interval the invariant's frame names, at `G.next0 + m` with
`m = s.next + 8 - G.next0`.  `WalkInv.next_ge` supplies this producer's half and
the caller supplies the upper end as the interval's own extent, so no equality
relating `s.next` to the carry is needed: the interval is the run's cursor, and the
callee's returned cursor is its end. -/
theorem s2StringBodyPre_at_string_call {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s)
    {p off ext : Nat} (hpend : C.pending = some (p, off, ext))
    {A : BitVec 64}
    (hreadA : readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8))
    (_hc : lookupName s.env "%c.i" = some (.ptr C.stage.c))
    (_hxp : lookupName s.env "%xp" = some (.ptr G.xp))
    (_hnxp : lookupName s.env "%nxp" = some (.int 64 (BitVec.ofNat 64 G.nxp)))
    (_haj : lookupName s.env "%arrayidx10.i" = some (.ptr (G.b + p)))
    (_hsub : lookupName s.env "%sub260.i" = some (.int 64 (BitVec.ofNat 64 ext)))
    (hfit : G.b + G.n + stage2ReadTail ≤ 2 ^ 64)
    (hge : G.next0 + 28 ≤ s.next)
    {j0 : Nat} (hj0 : stage2ReadWord s.mem (G.next0 + 12) 8 = some j0)
    (hj0_lt : j0 < 2 ^ 63)
    (hbase : stage2ReadWord s.mem C.stage.c 8 = some G.b)
    (he : stage2ReadWord s.mem (C.stage.c + 1112) 8 = some C.stage.e)
    (houtnP : readBytes s.mem (G.next0 + 20) 8 ≠ none)
    (hnxp_lt : G.nxp < 2 ^ 63)
    (hspaced : BodyPositionsSpaced s.mem C.stage.c (G.next0 + 12) G.xp G.nxp
      (G.b + p + 1) ext) :
    s2StringBodyPre
      [.ptr C.stage.c, .ptr (G.b + p + 1), .int 64 (BitVec.ofNat 64 ext),
       .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
       .int 64 (BitVec.ofNat 64 G.nxp)] s.mem s.next := by
  -- the staging's numbers, at the record in flight
  have hplen : p + ext ≤ G.n := hInv.pending_len p off ext hpend
  have hcur : C.alen ≤ G.ndst0 + p := hInv.pending_cursor p off ext hpend
  have hAle : A.toNat ≤ C.alen := hInv.logArena_le hreadA
  have hale : C.alen ≤ G.ndst0 + G.n := hInv.alen_le
  have hevle : C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := hInv.evlen_le
  have hevcap : C.evlen ≤ G.evcap := by
    have := G.evRoom
    omega
  have hhub : A.toNat + ext ≤ G.ndst0 + G.n := by omega
  have hn32 : G.n < 2 ^ 64 := by
    have h := G.maxDoc
    simp only [stage2MaxDocument] at h
    omega
  have hextext : ext < 2 ^ 64 := by omega
  -- the watermark, at the regions this producer reads
  have hwDoc : G.b + (G.n + stage2ReadTail) ≤ G.next0 :=
    G.watermark (G.b, G.n + stage2ReadTail) (by simp [stage2Regions])
  have hwArena : G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ G.next0 :=
    G.watermark (G.dst, G.ndst0 + G.n + stage2ArenaReserve) (by simp [stage2Regions])
  have hwXp : G.xp + 4 * G.nxp ≤ G.next0 :=
    G.watermark (G.xp, 4 * G.nxp) (by simp [stage2Regions])
  have hwC : C.stage.c + stage2CursorExtent ≤ G.next0 :=
    C.stage.sevenEnd (C.stage.c, stage2CursorExtent) (by simp [stage2StagedWrites])
  have hwE : C.stage.e + stage2ErrorExtent ≤ G.next0 :=
    C.stage.sevenEnd (C.stage.e, stage2ErrorExtent) (by simp [stage2StagedWrites])
  -- the same four at their numerals: `stage2ReadTail` and `stage2CursorExtent` are
  -- compared against literal offsets below (the window's `+ 1`, the record's
  -- `+ 1112`), and `omega` reads a constant only as a numeral.
  have hfitNum : G.b + G.n + 32 ≤ 2 ^ 64 := by simpa only [stage2ReadTail] using hfit
  have hwDocNum : G.b + (G.n + 32) ≤ G.next0 := by simpa only [stage2ReadTail] using hwDoc
  have hwCNum : C.stage.c + 1192 ≤ G.next0 := by simpa only [stage2CursorExtent] using hwC
  -- the document, split into its window and the decoder's read-past tail
  obtain ⟨tailbs, htail⟩ := G.tail
  have hfull : readBytes m0 G.b (G.n + stage2ReadTail) = some (G.bs ++ tailbs) :=
    JsonEntrySteps.readBytes_append m0 G.n G.b G.bs stage2ReadTail tailbs G.doc htail
  have hlext : p + 1 + ext ≤ G.n + stage2ReadTail := by
    have := hplen
    simp only [stage2ReadTail]
    omega
  have htake := readBytes_take_prefix hlext hfull
  obtain ⟨-, hwindow⟩ := readBytes_split m0 G.b (p + 1) ext htake
  have hbodyM0 : readBytes m0 (G.b + p + 1) ext =
      some (((G.bs ++ tailbs).take (p + 1 + ext)).drop (p + 1)) := by
    rw [show G.b + p + 1 = G.b + (p + 1) from by omega]; exact hwindow
  -- the document's whole staged region, against every entry of the walk's list
  have hsplitDoc : DisjointRegions ([(G.b, G.n + stage2ReadTail)] ++
      [(G.ep, 4 * G.nep), (G.xp, 4 * G.nxp),
       (G.dst, G.ndst0 + G.n + stage2ArenaReserve), (G.ev, G.evcap),
       (G.ndst, 8), (G.nev, 8), (G.err, 8)]) := by
    simpa only [stage2Regions, List.cons_append, List.nil_append] using G.separate
  have hDocTail := disjointRegions_against hsplitDoc (a := G.b)
    (n := G.n + stage2ReadTail) (by simp)
  have hsepDoc : ∀ q ∈ walkWideAt G C (s.next - G.next0),
      q.1 + q.2 ≤ G.b + p + 1 ∨ G.b + p + 1 + ext ≤ q.1 := by
    intro q hq
    have h := walkWideAt_abi_sep (C := C) (a := G.b) (n := G.n + stage2ReadTail)
      (by simp [stage2Regions])
      (hDocTail (G.dst, G.ndst0 + G.n + stage2ArenaReserve) (by simp))
      (hDocTail (G.ev, G.evcap) (by simp)) hale hevcap hwDoc q hq
    rcases h with h | h
    · left; omega
    · right
      have h' : G.b + (G.n + 32) ≤ q.1 := by simpa only [stage2ReadTail] using h
      omega
  have hbody : readBytes s.mem (G.b + p + 1) ext =
      some (((G.bs ++ tailbs).take (p + 1 + ext)).drop (p + 1)) := by
    rw [readBytes_of_frame hInv.frame hsepDoc, hbodyM0]
  -- the escape list, whose region lies below the cursor too
  have hsplitXp : DisjointRegions ([(G.b, G.n + stage2ReadTail), (G.ep, 4 * G.nep),
      (G.xp, 4 * G.nxp)] ++
      [(G.dst, G.ndst0 + G.n + stage2ArenaReserve), (G.ev, G.evcap),
       (G.ndst, 8), (G.nev, 8), (G.err, 8)]) := by
    simpa only [stage2Regions, List.cons_append, List.nil_append] using G.separate
  have hXpTail := disjointRegions_against hsplitXp (a := G.xp) (n := 4 * G.nxp) (by simp)
  have hsepXp : ∀ q ∈ walkWideAt G C (s.next - G.next0),
      q.1 + q.2 ≤ G.xp ∨ G.xp + 4 * G.nxp ≤ q.1 :=
    walkWideAt_abi_sep (C := C) (a := G.xp) (n := 4 * G.nxp) (by simp [stage2Regions])
      (hXpTail (G.dst, G.ndst0 + G.n + stage2ArenaReserve) (by simp))
      (hXpTail (G.ev, G.evcap) (by simp)) hale hevcap hwXp
  obtain ⟨bs0, hbs0⟩ := G.esc
  obtain ⟨ps, hpsM0⟩ := readLanes32_of_readBytes (m := m0) G.xp G.nxp hbs0
  have hps : readLanes32 s.mem G.xp G.nxp = some ps := by
    rw [readLanes32_of_frame hInv.frame hsepXp, hpsM0]
  -- the arena's window, and the error record, from the staging's presence
  have hdst : readBytes s.mem (G.dst + A.toNat) ext ≠ none := by
    obtain ⟨w, hw⟩ := hInv.owned (G.dst, G.ndst0 + G.n + stage2ArenaReserve)
      (by simp [walkStaged])
    have hargA : A.toNat + (G.ndst0 + G.n + stage2ArenaReserve - A.toNat) =
        G.ndst0 + G.n + stage2ArenaReserve := by omega
    obtain ⟨-, hrest⟩ := readBytes_split s.mem G.dst A.toNat
      (G.ndst0 + G.n + stage2ArenaReserve - A.toNat) (by rw [hargA]; exact hw)
    have hle : ext ≤ G.ndst0 + G.n + stage2ArenaReserve - A.toNat := by omega
    have hread := readBytes_take_prefix hle hrest
    intro h
    rw [hread] at h
    cases h
  have herr : readBytes s.mem C.stage.e stage2ErrorExtent ≠ none := by
    obtain ⟨w, hw⟩ := hInv.owned (C.stage.e, stage2ErrorExtent)
      (by simp [walkStaged, stage2ReportScratch, stage2StagedWrites])
    intro h
    rw [hw] at h
    cases h
  -- the separations the twenty `RegionsApart` facts read, between the objects
  have hWritesDoc := walkWrites_against_abi C.stage (a := G.b)
    (n := G.n + stage2ReadTail) (by simp [stage2Regions])
  have hWritesDst := walkWrites_against_abi C.stage (a := G.dst)
    (n := G.ndst0 + G.n + stage2ArenaReserve) (by simp [stage2Regions])
  have hsplitW : DisjointRegions ([(C.stage.c, stage2CursorExtent)] ++
      [(C.stage.ctype, stage2StackExtent), (C.stage.cst, stage2StackExtent),
       (C.stage.tok, stage2TokenExtent), (C.stage.s, stage2StateExtent),
       (C.stage.z, stage2LogExtent), (C.stage.e, stage2ErrorExtent)]) := by
    simpa only [stage2StagedWrites, List.cons_append, List.nil_append] using
      C.stage.writes_separate
  have hWritesCE := disjointRegions_against hsplitW (a := C.stage.c)
    (n := stage2CursorExtent) (by simp)
  have hED := hWritesDoc (C.stage.e, stage2ErrorExtent) (by simp [stage2StagedWrites])
  have hAE := hWritesDst (C.stage.e, stage2ErrorExtent) (by simp [stage2StagedWrites])
  have hAC := hWritesDst (C.stage.c, stage2CursorExtent) (by simp [stage2StagedWrites])
  have hEC := hWritesCE (C.stage.e, stage2ErrorExtent) (by simp)
  have hAD := hDocTail (G.dst, G.ndst0 + G.n + stage2ArenaReserve) (by simp)
  have hADn : G.b + (G.n + 32) ≤ G.dst ∨ G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ G.b := by
    rcases hAD with h | h
    · exact Or.inr h
    · exact Or.inl (by simpa only [stage2ReadTail] using h)
  have hEDn : C.stage.e + stage2ErrorExtent ≤ G.b ∨ G.b + (G.n + 32) ≤ C.stage.e := by
    rcases hED with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa only [stage2ReadTail] using h)
  have hACn : C.stage.c + 1192 ≤ G.dst ∨
      G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ C.stage.c := by
    rcases hAC with h | h
    · exact Or.inl (by simpa only [stage2CursorExtent] using h)
    · exact Or.inr h
  have hECn : C.stage.e + stage2ErrorExtent ≤ C.stage.c ∨ C.stage.c + 1192 ≤ C.stage.e := by
    rcases hEC with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa only [stage2CursorExtent] using h)
  -- the six bounds
  have hnxpv : (BitVec.ofNat 64 G.nxp).toNat = G.nxp := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt G.nxpLt]
  have hlenv : (BitVec.ofNat 64 ext).toNat = ext := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hextext]
  have hp_lt : G.b + p + 1 < 2 ^ 64 := by omega
  have hbase_le : G.b ≤ G.b + p + 1 := by omega
  have hwrap : G.b + p + 1 - G.b + (BitVec.ofNat 64 ext).toNat < 2 ^ 64 := by
    rw [hlenv]; omega
  have hlen_lt : (BitVec.ofNat 64 ext).toNat + 1 < 2 ^ 64 := by
    rw [hlenv]; omega
  -- the twenty separations, at the staging's addresses
  have hxj_next : RegionsApart (G.next0 + 12) 8 s.next 8 := by
    unfold RegionsApart; left; omega
  have hxj_outn : RegionsApart (G.next0 + 12) 8 (G.next0 + 20) 8 := by
    unfold RegionsApart; left; omega
  have hxj_dst : RegionsApart (G.next0 + 12) 8 (G.dst + A.toNat) ext := by
    unfold RegionsApart; right; omega
  have hxj_err : RegionsApart (G.next0 + 12) 8 C.stage.e stage2ErrorExtent := by
    unfold RegionsApart; right; omega
  have hnext_outn : RegionsApart s.next 8 (G.next0 + 20) 8 := by
    unfold RegionsApart; right; omega
  have hnext_dst : RegionsApart s.next 8 (G.dst + A.toNat) ext := by
    unfold RegionsApart; right; omega
  have hnext_err : RegionsApart s.next 8 C.stage.e stage2ErrorExtent := by
    unfold RegionsApart; right; omega
  have houtn_dst : RegionsApart (G.next0 + 20) 8 (G.dst + A.toNat) ext := by
    unfold RegionsApart; right; omega
  have houtn_err : RegionsApart (G.next0 + 20) 8 C.stage.e stage2ErrorExtent := by
    unfold RegionsApart; right; omega
  have hdst_err : RegionsApart (G.dst + A.toNat) ext C.stage.e stage2ErrorExtent := by
    unfold RegionsApart
    rcases hAE with h | h
    · right; omega
    · left; omega
  have hxj_p : RegionsApart (G.next0 + 12) 8 (G.b + p + 1) ext := by
    unfold RegionsApart; right; omega
  have hxj_c : RegionsApart (G.next0 + 12) 8 (C.stage.c + 1112) 8 := by
    unfold RegionsApart; right; omega
  have hnext_p : RegionsApart s.next 8 (G.b + p + 1) ext := by
    unfold RegionsApart; right; omega
  have hnext_c : RegionsApart s.next 8 (C.stage.c + 1112) 8 := by
    unfold RegionsApart; right; omega
  have hdst_p : RegionsApart (G.dst + A.toNat) ext (G.b + p + 1) ext := by
    unfold RegionsApart
    rcases hADn with h | h
    · right; omega
    · left; omega
  have hdst_c : RegionsApart (G.dst + A.toNat) ext (C.stage.c + 1112) 8 := by
    unfold RegionsApart
    rcases hACn with h | h
    · right; omega
    · left; omega
  have houtn_p : RegionsApart (G.next0 + 20) 8 (G.b + p + 1) ext := by
    unfold RegionsApart; right; omega
  have houtn_c : RegionsApart (G.next0 + 20) 8 (C.stage.c + 1112) 8 := by
    unfold RegionsApart; right; omega
  have herr_p : RegionsApart C.stage.e stage2ErrorExtent (G.b + p + 1) ext := by
    unfold RegionsApart
    rcases hEDn with h | h
    · left; omega
    · right; omega
  have herr_c : RegionsApart C.stage.e stage2ErrorExtent (C.stage.c + 1112) 8 := by
    unfold RegionsApart
    rcases hECn with h | h
    · left; omega
    · right; omega
  -- the two lane exclusions: the list ends below the cursor
  have hxj_scan : ∀ k, k < G.nxp →
      G.xp + 4 * k + 4 ≤ G.next0 + 12 ∨ G.next0 + 12 + 8 ≤ G.xp + 4 * k := by
    intro k hk
    left; omega
  have hnext_scan : ∀ k, k < G.nxp →
      G.xp + 4 * k + 4 ≤ s.next ∨ s.next + 8 ≤ G.xp + 4 * k := by
    intro k hk
    left; omega
  refine ⟨C.stage.c, G.b + p + 1, BitVec.ofNat 64 ext, G.dst + A.toNat,
    G.next0 + 20, G.xp, G.next0 + 12, BitVec.ofNat 64 G.nxp, G.b, j0, ps,
    ((G.bs ++ tailbs).take (p + 1 + ext)).drop (p + 1), C.stage.e, rfl, hbase, hj0,
    by simpa only [hnxpv] using hps,
    by simpa only [hlenv] using hbody,
    he,
    by simpa only [hnxpv, hlenv] using hspaced,
    hp_lt, hbase_le,
    by simpa only [hlenv] using hwrap,
    by simpa only [hlenv] using hlen_lt,
    hj0_lt,
    by simpa only [hnxpv] using hnxp_lt,
    houtnP,
    by simpa only [hlenv] using hdst,
    herr,
    hxj_next, hxj_outn,
    by simpa only [hlenv] using hxj_dst,
    hxj_err, hnext_outn,
    by simpa only [hlenv] using hnext_dst,
    hnext_err,
    by simpa only [hlenv] using houtn_dst,
    houtn_err,
    by simpa only [hlenv] using hdst_err,
    by simpa only [hlenv] using hxj_p,
    hxj_c,
    by simpa only [hlenv] using hnext_p,
    hnext_c,
    by simpa only [hlenv] using hdst_p,
    by simpa only [hlenv] using hdst_c,
    by simpa only [hlenv] using houtn_p,
    houtn_c,
    by simpa only [hlenv] using herr_p,
    herr_c,
    by simpa only [hnxpv] using hxj_scan,
    by simpa only [hnxpv] using hnext_scan⟩

end LeanLLVM.Refinement

#print axioms LeanLLVM.Refinement.s2StringBodyPre_of_staging
#print axioms LeanLLVM.Refinement.s2StringBodyFoot_frame_walkWideAt
#print axioms LeanLLVM.Refinement.s2StringBodyPre_spacing
#print axioms LeanLLVM.Refinement.BodyPositionsSpaced_of_reads
#print axioms LeanLLVM.Refinement.s2StringBody_frame_of_form
#print axioms LeanLLVM.Refinement.stage2StringBody_hasBytes
#print axioms LeanLLVM.Refinement.s2StringBodyFoot_presence_walkStaged
#print axioms LeanLLVM.Refinement.readBytes_of_frame
#print axioms LeanLLVM.Refinement.readLanes32_of_frame
#print axioms LeanLLVM.Refinement.readLanes32_of_readBytes
#print axioms LeanLLVM.Refinement.walkWrites_against_abi
#print axioms LeanLLVM.Refinement.walkWideAt_abi_sep
#print axioms LeanLLVM.Refinement.s2StringBodyPre_at_string_call
