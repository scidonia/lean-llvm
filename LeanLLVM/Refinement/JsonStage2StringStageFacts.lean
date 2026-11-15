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
  over `s2StringBodyFoot` is one over the walk's `walkWide` at the carry the link
  builds (`s2StringBodyFoot_frame_walkWide`), and the caller's presence over
  `walkStaged` survives the call (`s2StringBodyFoot_presence_walkStaged`).  The
  second needs no frame at all: every arm of the model is a write nest over the
  caller's memory, and a write adds cells and removes none, so presence is
  monotone through the call whatever the callee wrote.  That is why the staging's
  separation is not consumed here, and the docstrings say so rather than implying
  a use.

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

/-- **The callee's frame is the walk's, at the carry the link builds.**  Every
entry of `s2StringBodyFoot` at the call's argument list lies inside an entry of
`walkWide` at the advanced carry:

| foot entry | covered by | why |
|---|---|---|
| `(%xj.i, 8)` = `(G.next0 + 12, 8)` | `stage2AllocaWrites G.next0` | the alloca's own entry |
| `(%outn.i, 8)` = `(G.next0 + 20, 8)` | `stage2AllocaWrites G.next0` | the alloca's own entry |
| `(dst, len.toNat)` = `(G.dst + A, len.toNat)` | `(G.dst, C.alen + ext)` | `A ≤ C.alen`, `len.toNat ≤ ext` |
| the private `%ei` slot `(next, 8)` | `stage2AllocaWrites G.next0` | `hnext`: the call's cursor is one of the walk's stack slots |
| the error record `(e, stage2ErrorExtent)` | `stage2ReportScratch` | `e` is the staging's `%e` |

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
  address outside every list the frame names.
* **`hAle`** is the log's arena word at most the carried cursor,
  `WalkInv.logArena_le`'s conclusion at the `%ar` read.  It is what places the
  callee's destination window inside the arena's carried prefix: the window
  starts at `G.dst + A` and the frame's arena entry starts at `G.dst`.
* **`hnext`** places the callee's private `%ei` slot at the call's cursor inside
  the walk's stack list.  `s2_string_body` allocates eight bytes at the cursor it
  is called with (`s2StringBodyCall` advances `next` by the slot's width), and the
  slot is a region `walkWide` covers only when the cursor sits in
  `stage2AllocaWrites G.next0`.  No `WalkInv` clause carries `s.next` at all, so
  the placement is the caller's: at the layer's first string-body call the cursor
  is `G.next0 + 28` (the entry's four allocations, and no allocating call since),
  which is the list's fifth entry.  The statement keeps the general placement
  rather than the equality `next = G.next0 + 28`, because it is the region
  containment the frame reads; an equality would be a narrower form of the same
  premise.  Nothing below requires the cursor to be there, and the presence lemma
  is stated without it.

`hlen` is the call's own arithmetic: the extent argument is `%sub260.i`, and the
carry's advance is the same number.  A caller that instantiates `len` as
`BitVec.ofNat 64 ext` has `len.toNat = ext % 2 ^ 64 ≤ ext` by `Nat.mod_le`, which
is the hypothesis at that instantiation. -/
theorem s2StringBodyFoot_frame_walkWide {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {mem : Mem} {next : Nat} {r : CallOutcome} {p A ext : Nat}
    {len nxp : BitVec 64}
    (he : stage2ReadWord mem (C.stage.c + 1112) 8 = some C.stage.e)
    (hAle : A ≤ C.alen)
    (hlen : len.toNat ≤ ext)
    (hnext : ∃ q ∈ stage2AllocaWrites G.next0, q.1 ≤ next ∧ next + 8 ≤ q.1 + q.2)
    (hframe : UnchangedOutside mem r.mem
      (s2StringBodyFoot [.ptr C.stage.c, .ptr (G.b + p + 1), .int 64 len,
        .ptr (G.dst + A), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
        .int 64 nxp] mem next)) :
    UnchangedOutside mem r.mem
      (walkWide G { C with block := "NodeBlock31", alen := C.alen + ext, spans := C.spans ++ [(C.alen, ext)], pending := none }) := by
  let C' : WalkCarry G := { C with block := "NodeBlock31", alen := C.alen + ext, spans := C.spans ++ [(C.alen, ext)], pending := none }
  change UnchangedOutside mem r.mem (walkWide G C')
  have hfoot : s2StringBodyFoot [.ptr C.stage.c, .ptr (G.b + p + 1), .int 64 len,
      .ptr (G.dst + A), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12),
      .int 64 nxp] mem next
      = [(G.next0 + 12, 8), (G.next0 + 20, 8), (G.dst + A, len.toNat),
         (next, 8), (C.stage.e, stage2ErrorExtent)] := by
    simp only [s2StringBodyFoot, he, List.cons_append, List.nil_append]
  obtain ⟨q0, hq0, hq0lo, hq0hi⟩ := hnext
  have hq0w : q0 ∈ walkWide G C' := by
    show q0 ∈ walkPresent G C' ++ stage2AllocaWrites G.next0
    exact List.mem_append_right _ hq0
  have hxj : (G.next0 + 12, 8) ∈ walkWide G C' := by
    show (G.next0 + 12, 8) ∈ walkPresent G C' ++ stage2AllocaWrites G.next0
    exact List.mem_append_right _ (by
      simp only [stage2AllocaWrites]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self)))
  have houtn : (G.next0 + 20, 8) ∈ walkWide G C' := by
    show (G.next0 + 20, 8) ∈ walkPresent G C' ++ stage2AllocaWrites G.next0
    exact List.mem_append_right _ (by
      simp only [stage2AllocaWrites]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self))))
  have hdst : (G.dst, C'.alen) ∈ walkWide G C' := by
    show (G.dst, C'.alen) ∈ walkPresent G C' ++ stage2AllocaWrites G.next0
    exact List.mem_append_left _ (by
      show (G.dst, C'.alen) ∈
        [(G.dst, C'.alen), (G.ev, C'.evlen)] ++
          stage2ReportScratch C'.stage.c C'.stage.ctype C'.stage.cst C'.stage.tok
            C'.stage.s C'.stage.z C'.stage.e C'.stage.d
      exact List.mem_append_left _ (List.mem_cons_self))
  have herr : (C.stage.e, stage2ErrorExtent) ∈ walkWide G C' := by
    show (C.stage.e, stage2ErrorExtent) ∈ walkPresent G C' ++ stage2AllocaWrites G.next0
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
      ∃ q ∈ walkWide G C', q.1 ≤ r.1 ∧ r.1 + r.2 ≤ q.1 + q.2 := by
    intro r hr
    rw [hfoot] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, hxj, le_rfl, le_rfl⟩
    · exact ⟨_, houtn, le_rfl, le_rfl⟩
    · exact ⟨_, hdst, by show G.dst ≤ G.dst + A; omega,
        by show (G.dst + A) + len.toNat ≤ G.dst + (C.alen + ext); omega⟩
    · exact ⟨q0, hq0w, hq0lo, hq0hi⟩
    · exact ⟨_, herr, le_rfl, le_rfl⟩
  refine UnchangedOutside.widen hframe ?_
  intro a ha r hr
  obtain ⟨q, hq, hqlo, hqhi⟩ := hcov r hr
  exact fun hin => ha q hq ⟨le_trans hqlo hin.1, lt_of_lt_of_le hin.2 hqhi⟩

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
and dropping them would drop the call's vocabulary from its own producer. -/

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

/-- **A staged region the walk never writes, against its whole write list.**  The
list's two prefixes are inside their staged extents (`alen` and `evlen` grow inside
them), the seven and `%d.i` are separated from the region by the adapter's
staging (`WalkStage.separate`, `WalkStage.dSep`), and the four `alloca` slots start
at the cursor — so a region staged entirely below `G.next0`, and separated from the
arena's and the event stream's staged extents, is outside every entry.

The two extents are hypotheses rather than `WalkInv`'s projections so the lemma is
about the addresses: `WalkInv.alen_le` and `WalkInv.evlen_le` introduce them. -/
theorem walkWide_abi_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {a n : Nat}
    (ha : (a, n) ∈ stage2Regions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err)
    (harena : G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ a ∨ a + n ≤ G.dst)
    (hevent : G.ev + G.evcap ≤ a ∨ a + n ≤ G.ev)
    (hale : C.alen ≤ G.ndst0 + G.n)
    (hevcap : C.evlen ≤ G.evcap)
    (hwater : a + n ≤ G.next0) :
    ∀ q ∈ walkWide G C, q.1 + q.2 ≤ a ∨ a + n ≤ q.1 := by
  intro q hq
  simp only [walkWide, walkPresent] at hq
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
  · have hstart := stage2AllocaWrites_start hq
    right; omega

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
(`s2StringBodyFoot_frame_walkWide`) needs the upper one: the slot's eight bytes lie
inside the carried stack extent, `s.next + 8 ≤ G.next0 + allocated`.  A future
reader looking for the missing clause should look for **one equality**
(`s.next = G.next0 + nb`, with `nb` the carry's allocated stack bytes), not for two
clauses: it gives both bounds at once, and two separate inequalities would let the
cursor drift out of the extent the frame names. -/
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
  have hsepDoc : ∀ q ∈ walkWide G C,
      q.1 + q.2 ≤ G.b + p + 1 ∨ G.b + p + 1 + ext ≤ q.1 := by
    intro q hq
    have h := walkWide_abi_sep (C := C) (a := G.b) (n := G.n + stage2ReadTail)
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
  have hsepXp : ∀ q ∈ walkWide G C, q.1 + q.2 ≤ G.xp ∨ G.xp + 4 * G.nxp ≤ q.1 :=
    walkWide_abi_sep (C := C) (a := G.xp) (n := 4 * G.nxp) (by simp [stage2Regions])
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
#print axioms LeanLLVM.Refinement.s2StringBodyFoot_frame_walkWide
#print axioms LeanLLVM.Refinement.stage2StringBody_hasBytes
#print axioms LeanLLVM.Refinement.s2StringBodyFoot_presence_walkStaged
#print axioms LeanLLVM.Refinement.readBytes_of_frame
#print axioms LeanLLVM.Refinement.readLanes32_of_frame
#print axioms LeanLLVM.Refinement.readLanes32_of_readBytes
#print axioms LeanLLVM.Refinement.walkWrites_against_abi
#print axioms LeanLLVM.Refinement.walkWide_abi_sep
#print axioms LeanLLVM.Refinement.s2StringBodyPre_at_string_call
