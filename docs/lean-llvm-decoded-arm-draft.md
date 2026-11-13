# The decoded arm's `_named` lemma (drafted, untested)

The direct analogue of `s2StringBodyExpand_refused_named`, with `Woff = wordBytes 8
out.length`. It was written but never elaborated; the first step of the next pass is to
test it, **before** writing the decoded arm's proof.

```lean
/-- **The expander's accepting answer at variable leaves**: its memory is the
callee's chain with `Woff`/`Wj` as lists, so a consumer that names the stage unifies
by structure. -/
theorem s2StringBodyExpand_decoded_named {mem xmem : Mem} {p dst xp xj : Nat}
    {len nxp : BitVec 64} {base c1 ei next lane offN k : Nat} {ps : List Nat}
    {body out : List UInt8} {Woff Wj : List UInt8}
    (hmem : xmem = writeBytes mem xj (wordBytes 8 c1))
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (hlane : ps[c1]? = some lane) (hge : p - base ≤ lane)
    (hp0 : p - base < 2 ^ 64) (hc1 : c1 < 2 ^ 64)
    (hWoff : Woff = wordBytes 8 out.length) (hWj : Wj = wordBytes 8 (c1 + k))
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
             (writeBytes (writeBytes (writeBytes xmem ei (natToBytes (0#64).toNat 8))
               dst out) xj Wj) ei Woff,
           next := next } := by
  rw [hWoff, hWj]
  exact s2StringBodyExpand_decoded_at_exit (dst := dst) (next := next)
    (hps := hps) (hbody := hbody) (hlane := hlane) (hge := hge) (hp0 := hp0)
    (hc1 := hc1) (hxjp := hxjp) (heip := heip) (heixj := heixj)
    (heilan := heilan) (hjlan := hjlan) (hmem := hmem) (hdec := hdec)
```

## Why it is shaped this way

`Woff` and `Wj` are **variables**, constrained by two equations, rather than the
concrete words — the leaf rule: *keep the leaves variable where the consumer unifies
structurally, concrete where its lemma already carries the word, and cross with
one-level rewrites only.*
