# The refused arm, three fixes from closing

`LeanLLVM.Refinement.s2StringBodyArm_scan_refused` is written and type-checks except
for the goals below.  The module is green at the commit before this note; the arm
itself is not in it.  Everything it calls is committed and proved.

## The declaration

Signature: `(F : the facts below) : s2StringBodyConcludes [.ptr ch, …] mem next 5 x`,
with `set_option maxHeartbeats 4000000 in` — a documented cost, not a trick: five
rewrites each carry a staged `Mem` a level at a time.

```lean
  have hC3 : s2StringBodyRefusedC3 mem ei xj c1 offN k
      = writeBytes
          (writeBytes (writeBytes (s2StringBodyRefusedC0 mem xj c1) ei
            (natToBytes (0#64).toNat 8)) ei Woff) xj Wj := by
    rw [s2StringBodyRefusedC3, s2StringBodyRefusedC2, s2StringBodyRefusedC1,
      ← hWoff, ← hWj]                                   -- ← the goal below
  have hxj8 : readBytes mem xj (wordBytes 8 c1).length ≠ none := by
    intro h
    rw [show (wordBytes 8 c1).length = 8 from natToBytes_length _ _] at h
    rw [readBytes_of_stage2ReadWord hj0] at h
    cases h
  have hC6join := s2StringBodyRefusedC6_join mem hxj8 hei_p
    (by simp [wordBytes, natToBytes_length])            -- ← `simp`, not `simp only`
    (by rcases heixj with h | h
        · exact Or.inr (by simp only [wordBytes, natToBytes_length]; exact h)
        · exact Or.inl (by simp only [wordBytes, natToBytes_length]; exact h))
    (by simp only [wordBytes, natToBytes_length]) hxj8
    (s2StringBodyErr_presence hrec_bs).1
    (s2StringBodyErr_presence hrec_bs).2.1 (s2StringBodyErr_presence hrec_bs).2.2
    (by simp only [wordBytes, natToBytes_length] at h1 ⊢; exact h1)
    … (h2 … h10 the same) …
    -- ← pass the implicits by name: (offN := offN) (k := k) (p := p) (base := base)
  have hM0 : s2StringBodyIfThen11Mem extra e' (BitVec.ofNat 64 offN)
        (BitVec.ofNat 64 (p - base))
      = writeBytes (writeBytes (stage2ErrSetMsg mem e' (p - base + offN) 0) xj
          (wordBytes 8 (c1 + k))) next (wordBytes 8 offN) := by
    rw [hexpMem, ← s2StringBodyRefusedExtra, s2StringBodyIfThen11Mem_staged, hC6join,
      s2StringBodyRefusedModel_reconciles mem hoffN hp0 hsumW, hnext, hWj]
  refine ⟨⟨.int 32 (BitVec.ofNat 32 0),
      s2StringBodyIfThen11Mem extra e' (BitVec.ofNat 64 offN)
        (BitVec.ofNat 64 (p - base)),
      next + 8⟩, ?_, ?_, ?_⟩
  · exact s2StringBodyArm_scan_refused_run (hpc := hpc) (hmem := hmem) (hC0 := hC0)
      (hexpMem := hexpMem.trans hC3) (hWoff := hWoff) (hWj := hWj) …
  · exact ⟨writeBytes (stage2ErrSetMsg mem e' (p - base + offN) 0) xj
      (wordBytes 8 (c1 + k)), 0, wordBytes 8 offN, hmodel, rfl, hM0, rfl⟩
  · rw [hM0]
    simp only [s2StringBodyFoot, hrec]
    exact ((stage2ErrSetMsg_frame (R := [(xj, 8), (outn, 8), (dst, len.toNat),
        (next, 8), (e', stage2ErrorExtent)])
        ⟨(e', stage2ErrorExtent), by simp, le_rfl, by simp [stage2ErrorExtent]⟩).write_le
      (a := xj) (w := 8) ⟨(xj, 8), by simp, le_rfl, le_rfl⟩
      (by simp [natToBytes_length])).write_le (a := next) (w := 8)
      ⟨(next, 8), by simp, le_rfl, le_rfl⟩ (by simp [natToBytes_length])
```

## The goals, verbatim

1. `hC6join`'s implicit parameters (four errors of one shape):
   `don't know how to synthesize implicit argument p` — with `⊢ ℕ` and
   `don't know how to synthesize implicit argument b` with `⊢ Prop`, at the
   `by`-proofs for `h1`/`hdis`.  **Fix**: name them, `(offN := offN) (k := k)
   (p := p) (base := base)`.
2. `(by simp only [wordBytes, natToBytes_length])` for `hlen` left
   `⊢ 8 ≤ 8`.  **Fix**: `simp`, because `le_refl` is not in a `simp only` set.
3. `hxj8`'s order.  The hypothesis is
   `readBytes mem xj (wordBytes 8 c1).length = none`; `readBytes_of_stage2ReadWord`
   is stated at the address `8`, so the **length identity must rewrite the address
   first**, and only then the read; then `cases h`.
4. `hC3` (line 6154 at that revision) still leaves one goal, masked by (1).

## The rules this slice measured

- name the term, and stage what a proof rewrites *inside*;
- keep leaves variable where the consumer unifies structurally, concrete where its
  lemma already carries the word, and cross with one-level rewrites;
- unfold **one level at a time**: a single delta through `C3`, `C2`, `C1` walks the
  `Mem` association list three times and costs 200 000 heartbeats, while three
  one-level rewrites are free;
- `show` is a defeq claim and cannot change a spelling; only `rw` can;
- `simp only` is a closed set: `le_refl`, implicit-argument inference and rewrite
  order are all outside it, and each costs a build to discover.
