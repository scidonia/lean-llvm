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
  side conditions, and the docstring names which for every one.
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

end LeanLLVM.Refinement

#print axioms LeanLLVM.Refinement.s2StringBodyPre_of_staging
#print axioms LeanLLVM.Refinement.s2StringBodyFoot_frame_walkWide
#print axioms LeanLLVM.Refinement.stage2StringBody_hasBytes
#print axioms LeanLLVM.Refinement.s2StringBodyFoot_presence_walkStaged
