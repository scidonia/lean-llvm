import LeanLLVM.Refinement.JsonStage2StringBodyBlocks

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The split on `Exited`

The scan leaves either at `if.then` (its second exit) or at `land.lhs.true` (its
first), and the second's two branches are the lane test's bit.  Each wrapper below
reads the composed path at the exit state the scan's instance returns, so `hcont`
in `s2StringBodyScan_run` is one `rcases` away:

* `if.then` — the body-itself arm, answer `1`;
* `land.lhs.true` with the inside test false — the body-itself arm through
  `if.then`, answer `1`;
* `land.lhs.true` with the inside test true and the expander's answer all-ones —
  the refusal, answer `0`;
* `land.lhs.true` with the inside test true and any other answer — the decoded
  length, answer `2`.

`ExitWord` is not consumed here: the outcome's memory is the exit state's own, and
the counter's `∃ c` is what the closing uses to name that memory as the model's. -/

/-- The second exit finishes the body-itself arm. -/
theorem s2StringBodyExit_ifThen {e : State} {len : BitVec 64} {outn : Nat}
    (hpc : e.pc = "if.then")
    (hlen : lookupName e.env "%len" = some (.int 64 len))
    (houtn : lookupName e.env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody e =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes e.mem outn (natToBytes len.toNat 8))) :=
  s2StringBodyIfThen_finishes (env := e.env) (s := e) hpc hlen houtn

/-- The first exit, the lane inside the body: the body-itself arm through
`if.then`. -/
theorem s2StringBodyExit_landLhsTrue_toIfThen {e : State} {sub len conv : BitVec 64}
    {outn : Nat}
    (hpc : e.pc = "land.lhs.true")
    (hsub : lookupName e.env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName e.env "%len" = some (.int 64 len))
    (hconv : lookupName e.env "%conv" = some (.int 64 conv))
    (hbit : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 0#1)
    (houtn : lookupName e.env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 3 s2StringBodyBody e =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes e.mem outn (natToBytes len.toNat 8))) :=
  s2StringBodyLandLhsTrue_toIfThen_finishes (env := e.env) (s := e)
    hpc hsub hlen hconv hbit houtn

/-- The first exit, the expander refusing: the record's path, answer `0`. -/
theorem s2StringBodyExit_refused {e : State} {sub len conv off : BitVec 64}
    {p dst ei xp xj c j : Nat} {nxp : BitVec 64} {extra : Mem} {nx : Nat}
    {call : BitVec 64}
    (hpc : e.pc = "land.lhs.true")
    (hc : lookupName e.env "%c" = some (.ptr c))
    (hsub : lookupName e.env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName e.env "%len" = some (.int 64 len))
    (hconv : lookupName e.env "%conv" = some (.int 64 conv))
    (hbit7 : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1)
    (hp : lookupName e.env "%p" = some (.ptr p))
    (hdst : lookupName e.env "%dst" = some (.ptr dst))
    (hei : lookupName e.env "%ei" = some (.ptr ei))
    (hxp : lookupName e.env "%xp" = some (.ptr xp))
    (hxj : lookupName e.env "%xj" = some (.ptr xj))
    (hnxp : lookupName e.env "%nxp" = some (.int 64 nxp))
    (hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes e.mem ei (natToBytes (0#64).toNat 8)) e.next =
      some { ret := .int 64 call, mem := extra, next := nx })
    (hbit9 : evalICmp .eq call 0xffffffffffffffff#64 = 1#1)
    (hoff : readBytes extra ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes extra (c + (1112#64).toNat) 8 = some (wordBytes 8 j))
    (hj64 : j < 2 ^ 64) :
    runFuel s2StringBodyCalls 5 s2StringBodyBody e =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen11Mem extra j off sub)) :=
  s2StringBodyLandLhsTrue_refused_finishes (env := e.env) (s := e)
    hpc hc hsub hlen hconv hbit7 hp hdst hei hxp hxj hnxp hexp hbit9 hoff hcval hj64

/-- The first exit, the expander decoding: the decoded length's word, answer `2`. -/
theorem s2StringBodyExit_decoded {e : State} {sub len conv : BitVec 64}
    {p dst ei outn xp xj : Nat} {nxp : BitVec 64} {extra : Mem} {nx : Nat}
    {call : BitVec 64}
    (hpc : e.pc = "land.lhs.true")
    (hsub : lookupName e.env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName e.env "%len" = some (.int 64 len))
    (hconv : lookupName e.env "%conv" = some (.int 64 conv))
    (hbit7 : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1)
    (hp : lookupName e.env "%p" = some (.ptr p))
    (hdst : lookupName e.env "%dst" = some (.ptr dst))
    (hei : lookupName e.env "%ei" = some (.ptr ei))
    (hxp : lookupName e.env "%xp" = some (.ptr xp))
    (hxj : lookupName e.env "%xj" = some (.ptr xj))
    (hnxp : lookupName e.env "%nxp" = some (.int 64 nxp))
    (hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes e.mem ei (natToBytes (0#64).toNat 8)) e.next =
      some { ret := .int 64 call, mem := extra, next := nx })
    (hbit9 : evalICmp .eq call 0xffffffffffffffff#64 = 0#1)
    (houtn : lookupName e.env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 5 s2StringBodyBody e =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes extra outn (natToBytes call.toNat 8))) :=
  s2StringBodyLandLhsTrue_decoded_finishes (env := e.env) (s := e)
    hpc hsub hlen hconv hbit7 hp hdst hei hxp hxj hnxp hexp hbit9 houtn


/-! ### The memory term

The post's memory is `r.mem = writeBytes m next slot`, with `m` the model's memory and
`slot` the bytes at the body's own `alloca`.  Reading it per arm shows the three
cases are not alike at all:

* **the body-itself arm writes no slot** — the model's `slot` is `[]` there, so
  `writeBytes m next [] = m` and the term is the identity on the model's memory;
* **the body-itself arm's memory is the model's by definition** — the arm writes
  `natToBytes len 8` at `outn` and the model writes `wordBytes 8 len`, and
  `wordBytes` *is* `natToBytes`, so the two memories are the same term;
* **the two callee arms are not** — the callee writes `dst`, `xj` and the slot `ei`
  in its own order, the model writes `dst`/`xj`/`outn` over `mem` and then the slot
  at `next`; joining those is where the write-order primitives are spent
  (`writeBytes_writeBytes_same` for a region written twice,
  `writeBytes_of_readBytes_self` for one already present), and it is the last
  substantial obligation of the row.

So this section states the two facts that make the first two bullets true and names
the third's shape.  Neither is a `rfl`-convenience: the first says the model's slot
parameter must be a *variable* (it is `[]` on one arm and eight bytes on the others,
and a consumer reading `writeBytes m next slot` must not assume it is populated), and
the second says the arm's memory needs no rewriting at all. -/

/-- The body-itself arm writes no slot: the model's slot is empty, so its slot write
is the identity on the memory.  This is why `slot` has to be a parameter of the
memory term and not a fixed eight-byte region. -/
theorem s2StringBodySlot_of_bodyItself (m : Mem) (next : Nat) :
    writeBytes m next ([] : List UInt8) = m := rfl

/-- The body-itself arm's memory **is** the model's, as one term: the arm writes the
extent's bytes at `outn` and the model writes `wordBytes 8 len`, which is those
bytes. -/
theorem s2StringBodyMemory_of_bodyItself (mem : Mem) (xj outn j1 len : Nat) :
    writeBytes (writeBytes mem xj (wordBytes 8 j1)) outn (natToBytes len 8) =
      writeBytes (writeBytes mem xj (wordBytes 8 j1)) outn (wordBytes 8 len) := rfl

/-- **The decoded arm's memory join**: the body's memory is the model's plus the slot
at the call's allocator.  Two moves: the arm's clear is absorbed by the callee's own
slot write, which spends `dst`'s and `xj`'s presences — the regions the crossings
move into, not the slot's — and then the slot's write crosses `outn`'s, which spends
`outn`'s. -/
theorem s2StringBodyMemory_decoded (mem : Mem) {ei dst xj outn j1 k : Nat}
    {out : List UInt8}
    (hdst : readBytes mem dst out.length ≠ none)
    (hxj : readBytes mem xj 8 ≠ none)
    (houtn : readBytes mem outn 8 ≠ none)
    (hd_ei : ei + 8 ≤ dst ∨ dst + out.length ≤ ei)
    (hx_ei : ei + 8 ≤ xj ∨ xj + 8 ≤ ei)
    (hd_xj : dst + out.length ≤ xj ∨ xj + 8 ≤ dst)
    (ho_ei : ei + 8 ≤ outn ∨ outn + 8 ≤ ei)
    (ho_d : outn + 8 ≤ dst ∨ dst + out.length ≤ outn)
    (ho_x : outn + 8 ≤ xj ∨ xj + 8 ≤ outn) :
    writeBytes
        (writeBytes
          (writeBytes
            (writeBytes
              (writeBytes mem ei (natToBytes (0#64).toNat 8)) dst out)
            xj (wordBytes 8 (j1 + k)))
          ei (wordBytes 8 out.length))
        outn (natToBytes out.length 8)
      = writeBytes
          (writeBytes
            (writeBytes
              (writeBytes mem dst out)
              xj (wordBytes 8 (j1 + k)))
            outn (wordBytes 8 out.length))
          ei (wordBytes 8 out.length) := by
  -- name the arm's word in the model's spelling, so the two sides' only difference
  -- is the clear's presence
  show writeBytes (writeBytes (writeBytes (writeBytes (writeBytes mem ei (natToBytes (0#64).toNat 8)) dst out)
      xj (wordBytes 8 (j1 + k))) ei (wordBytes 8 out.length)) outn (wordBytes 8 out.length)
    = writeBytes (writeBytes (writeBytes (writeBytes mem dst out) xj (wordBytes 8 (j1 + k)))
        outn (wordBytes 8 out.length)) ei (wordBytes 8 out.length)
  -- 1. the arm's clear is absorbed
  rw [writeBytes_absorb_one mem hdst hxj
    (by simp [wordBytes, natToBytes_length]) hd_ei hx_ei hd_xj]
  -- 2. the slot's write crosses `outn`, spending the presence of the region it
  --    crosses into — not of its own
  have hmid_outn : readBytes (writeBytes mem dst out) outn 8 ≠ none := by
    rcases ho_d with h | h
    · rw [readBytes_writeBytes_below mem out 8 outn dst h]; exact houtn
    · rw [s2StringBodyReadBytes_above mem out 8 outn dst h]; exact houtn
  have houtn' : readBytes (writeBytes (writeBytes mem dst out) xj (wordBytes 8 (j1 + k)))
      outn 8 ≠ none := by
    rcases ho_x with h | h
    · rw [readBytes_writeBytes_below (writeBytes mem dst out) (wordBytes 8 (j1 + k))
        8 outn xj h]
      exact hmid_outn
    · rw [s2StringBodyReadBytes_above (writeBytes mem dst out) (wordBytes 8 (j1 + k))
        8 outn xj (by simpa [wordBytes, natToBytes_length] using h)]
      exact hmid_outn
  obtain ⟨O₁, hO₁⟩ := exists_readBytes_of_ne houtn'
  have ho_ei' : ei + (wordBytes 8 out.length).length ≤ outn ∨
      outn + (wordBytes 8 out.length).length ≤ ei := by
    simpa [wordBytes, natToBytes_length] using ho_ei
  rw [writeBytes_comm_of_present_right (writeBytes (writeBytes mem dst out) xj (wordBytes 8 (j1 + k)))
    ei (wordBytes 8 out.length) outn (wordBytes 8 out.length)
    ⟨O₁, hO₁⟩ ho_ei']

/-- **The refusal record's fields are the model's.**  The body writes the record's
three words at `e`, `e + 8`, `e + 16`; the model writes
`writeBytes (writeBytes (writeBytes mem e (wordBytes 4 0)) (e + 8) (wordBytes 8 off))
(e + 16) (wordBytes 8 msg)` with `off = pos0 + off` and `msg = 0`.  The three writes
agree word for word, and the offset's reconciliation is the only arithmetic: the
body's `off + sub` is `off.toNat + pos0` because `sub` is `pos0` at `i64` and the sum
does not wrap. -/
theorem s2StringBodyErrRecord_reconciles (mem : Mem) (e : Nat) (off : BitVec 64)
    (sub : BitVec 64) (pos0 : Nat)
    (hsub : sub = BitVec.ofNat 64 pos0) (hpos0 : pos0 < 2 ^ 64)
    (hsum : off.toNat + pos0 < 2 ^ 64) :
    writeBytes
        (writeBytes
          (writeBytes mem e (natToBytes (0#32).toNat 4))
          (e + (8#64).toNat) (natToBytes (off + sub).toNat 8))
        (e + (16#64).toNat) (natToBytes (0#64).toNat 8)
      = stage2ErrSetMsg mem e (pos0 + off.toNat) 0 := by
  have htoNat : (off + sub).toNat = off.toNat + pos0 := by
    rw [hsub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h0_32 : (0#32).toNat = 0 := by decide
  have h0_64 : (0#64).toNat = 0 := by decide
  have h8 : (8#64).toNat = 8 := by decide
  have h16 : (16#64).toNat = 16 := by decide
  simp only [stage2ErrSetMsg, stage2ErrSet, wordBytes, htoNat, h0_32, h0_64, h8, h16,
    Nat.add_comm]

/-- **The refused arm's memory join.**  The clear is absorbed by the callee's own
`ei` write (adjacent: for the refusal the slot's content *is* that word), then
`scan(xj)` moves right past the record's three words and the `ei` write follows it —
seven crossings over pairwise disjoint regions, each spending one presence.  The
slot's own region is not among them: every crossing moves the slot's write, and a
moved write needs only the region it crosses into to be present. -/
theorem s2StringBodyMemory_refused (mem : Mem) {ei xj e : Nat}
    {Wj R0 R1 R2 Woff : List UInt8}
    (hWoff : Woff.length = 8)
    (hxj : readBytes mem xj Wj.length ≠ none)
    (he0 : readBytes mem e R0.length ≠ none)
    (he1 : readBytes mem (e + (8#64).toNat) R1.length ≠ none)
    (he2 : readBytes mem (e + (16#64).toNat) R2.length ≠ none)
    (h1 : ei + Woff.length ≤ xj ∨ xj + Wj.length ≤ ei)
    (h2 : ei + Woff.length ≤ e ∨ e + R0.length ≤ ei)
    (h3 : ei + Woff.length ≤ e + (8#64).toNat ∨
      e + (8#64).toNat + R1.length ≤ ei)
    (h4 : ei + Woff.length ≤ e + (16#64).toNat ∨
      e + (16#64).toNat + R2.length ≤ ei)
    (h5 : xj + Wj.length ≤ e ∨ e + R0.length ≤ xj)
    (h6 : xj + Wj.length ≤ e + (8#64).toNat ∨
      e + (8#64).toNat + R1.length ≤ xj)
    (h7 : xj + Wj.length ≤ e + (16#64).toNat ∨
      e + (16#64).toNat + R2.length ≤ xj)
    (h8 : e + R0.length ≤ e + (8#64).toNat ∨
      e + (8#64).toNat + R1.length ≤ e)
    (h9 : e + R0.length ≤ e + (16#64).toNat ∨
      e + (16#64).toNat + R2.length ≤ e)
    (h10 : e + (8#64).toNat + R1.length ≤ e + (16#64).toNat ∨
      e + (16#64).toNat + R2.length ≤ e + (8#64).toNat) :
    writeBytes
        (writeBytes
          (writeBytes
            (writeBytes
              (writeBytes
                (writeBytes mem ei (natToBytes (0#64).toNat 8)) ei Woff)
              xj Wj)
            e R0)
          (e + (8#64).toNat) R1)
        (e + (16#64).toNat) R2
      = writeBytes
          (writeBytes
            (writeBytes
              (writeBytes
                (writeBytes mem e R0)
                (e + (8#64).toNat) R1)
              (e + (16#64).toNat) R2)
            xj Wj)
          ei Woff := by
  rw [show writeBytes (writeBytes mem ei (natToBytes (0#64).toNat 8)) ei Woff
      = writeBytes mem ei Woff from
    writeBytes_writeBytes_same mem ei (natToBytes (0#64).toNat 8) Woff
      (by simp [natToBytes_length, hWoff])]
  -- the presences, one per region per hop: the record's and `xj`'s, because the
  -- slot's crossings spend the region they cross into and `xj`'s spend `xj`'s own
  have he0_xj : readBytes (writeBytes mem xj Wj) e R0.length ≠ none := by
    rcases h5 with h | h
    · rw [s2StringBodyReadBytes_above mem Wj R0.length e xj (by omega)]; exact he0
    · rw [readBytes_writeBytes_below mem Wj R0.length e xj (by omega)]; exact he0
  have he1_xj : readBytes (writeBytes mem xj Wj) (e + (8#64).toNat) R1.length ≠ none := by
    rcases h6 with h | h
    · rw [s2StringBodyReadBytes_above mem Wj R1.length (e + (8#64).toNat) xj (by omega)]
      exact he1
    · rw [readBytes_writeBytes_below mem Wj R1.length (e + (8#64).toNat) xj (by omega)]
      exact he1
  have he1_xj0 : readBytes (writeBytes (writeBytes mem xj Wj) e R0)
      (e + (8#64).toNat) R1.length ≠ none := by
    rcases h8 with h | h
    · rw [s2StringBodyReadBytes_above (writeBytes mem xj Wj) R0 R1.length
        (e + (8#64).toNat) e h]
      exact he1_xj
    · rw [readBytes_writeBytes_below (writeBytes mem xj Wj) R0 R1.length
        (e + (8#64).toNat) e h]
      exact he1_xj
  have he2_xj : readBytes (writeBytes mem xj Wj) (e + (16#64).toNat) R2.length ≠ none := by
    rcases h7 with h | h
    · rw [s2StringBodyReadBytes_above mem Wj R2.length (e + (16#64).toNat) xj (by omega)]
      exact he2
    · rw [readBytes_writeBytes_below mem Wj R2.length (e + (16#64).toNat) xj (by omega)]
      exact he2
  have he2_xj0 : readBytes (writeBytes (writeBytes mem xj Wj) e R0)
      (e + (16#64).toNat) R2.length ≠ none := by
    rcases h9 with h | h
    · rw [s2StringBodyReadBytes_above (writeBytes mem xj Wj) R0 R2.length
        (e + (16#64).toNat) e h]
      exact he2_xj
    · rw [readBytes_writeBytes_below (writeBytes mem xj Wj) R0 R2.length
        (e + (16#64).toNat) e h]
      exact he2_xj
  have he2_xj01 : readBytes (writeBytes (writeBytes (writeBytes mem xj Wj) e R0)
      (e + (8#64).toNat) R1) (e + (16#64).toNat) R2.length ≠ none := by
    rcases h10 with h | h
    · rw [s2StringBodyReadBytes_above (writeBytes (writeBytes mem xj Wj) e R0) R1
        R2.length (e + (16#64).toNat) (e + (8#64).toNat) h]
      exact he2_xj0
    · rw [readBytes_writeBytes_below (writeBytes (writeBytes mem xj Wj) e R0) R1
        R2.length (e + (16#64).toNat) (e + (8#64).toNat) h]
      exact he2_xj0
  -- 1. `ei`'s write crosses `xj`
  rw [writeBytes_comm_of_present_right mem ei Woff xj Wj
    (exists_readBytes_of_ne hxj) h1]
  -- 2-4. and the record's three words
  rw [writeBytes_comm_of_present_right (writeBytes mem xj Wj) ei Woff e R0
    (exists_readBytes_of_ne he0_xj) h2]
  rw [writeBytes_comm_of_present_right (writeBytes (writeBytes mem xj Wj) e R0) ei Woff
    (e + (8#64).toNat) R1 (exists_readBytes_of_ne he1_xj0) h3]
  rw [writeBytes_comm_of_present_right (writeBytes (writeBytes (writeBytes mem xj Wj) e R0)
      (e + (8#64).toNat) R1) ei Woff (e + (16#64).toNat) R2
    (exists_readBytes_of_ne he2_xj01) h4]
  -- 5. `xj` past the record's first word
  rw [writeBytes_comm_of_present_left mem xj Wj e R0
    (exists_readBytes_of_ne hxj) h5]
  -- 6-7. and past the next two, which needs `xj`'s presence in what the earlier
  -- crossings left
  have hxj_e0 : readBytes (writeBytes mem e R0) xj Wj.length ≠ none := by
    rcases h5 with h | h
    · rw [readBytes_writeBytes_below mem R0 Wj.length xj e h]; exact hxj
    · rw [s2StringBodyReadBytes_above mem R0 Wj.length xj e h]; exact hxj
  rw [writeBytes_comm_of_present_left (writeBytes mem e R0) xj Wj
    (e + (8#64).toNat) R1 (exists_readBytes_of_ne hxj_e0) h6]
  have hxj_e01 : readBytes (writeBytes (writeBytes mem e R0) (e + (8#64).toNat) R1)
      xj Wj.length ≠ none := by
    rcases h6 with h | h
    · rw [readBytes_writeBytes_below (writeBytes mem e R0) R1 Wj.length xj
        (e + (8#64).toNat) h]
      exact hxj_e0
    · rw [s2StringBodyReadBytes_above (writeBytes mem e R0) R1 Wj.length xj
        (e + (8#64).toNat) h]
      exact hxj_e0
  rw [writeBytes_comm_of_present_left
    (writeBytes (writeBytes mem e R0) (e + (8#64).toNat) R1)
    xj Wj (e + (16#64).toNat) R2 (exists_readBytes_of_ne hxj_e01) h7]

/-- **`%cmp3`'s bit.**  The entry's test is `j0` against the count at `i64`; both
sides are below `2 ^ 63`, so the unsigned comparison is the model's `Nat` one. -/
theorem s2StringBodyBit_cmp3_one {j0 : Nat} {nxp : BitVec 64}
    (hx : j0 < 2 ^ 63) (hy : nxp.toNat < 2 ^ 63) (h : j0 < nxp.toNat) :
    evalICmp .ult (BitVec.ofNat 64 j0) nxp = 1#1 := by
  have h64 : j0 < 2 ^ 64 := by omega
  simp only [evalICmp, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, h, BitVec.ofBool]
  rfl

/-- The same test as `0`: the entry leaves for the body-itself arm. -/
theorem s2StringBodyBit_cmp3_zero {j0 : Nat} {nxp : BitVec 64}
    (hx : j0 < 2 ^ 63) (hy : nxp.toNat < 2 ^ 63) (h : nxp.toNat ≤ j0) :
    evalICmp .ult (BitVec.ofNat 64 j0) nxp = 0#1 := by
  have h64 : j0 < 2 ^ 64 := by omega
  have hlt : ¬ j0 < nxp.toNat := by omega
  simp only [evalICmp, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, hlt,
    BitVec.ofBool]
  rfl

/-- **`takeWhile` is empty exactly when the list is empty or its head fails the
predicate.**  The `true` direction is structural — `takeWhile`'s two equations and the
induction — and the `false` direction is the head's value; that asymmetry is why
stating the `iff` this way needs no arithmetic. -/
theorem takeWhile_isEmpty_iff {α : Type} (p : α → Bool) :
    ∀ (l : List α), (l.takeWhile p).isEmpty = true ↔
      (l = [] ∨ ∃ a t, l = a :: t ∧ ¬ p a = true)
  | [] => by simp
  | a :: t => by
      by_cases h : p a = true
      · rw [List.takeWhile_cons_of_pos (p := p) h]
        simp only [List.isEmpty_cons, Bool.false_eq_true, false_iff]
        rintro (h' | ⟨a', t', heq, hneg⟩)
        · exact absurd h' (by simp)
        · simp only [List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact absurd h hneg
      · rw [List.takeWhile_cons_of_neg (p := p) h]
        exact ⟨fun _ => Or.inr ⟨a, t, rfl, h⟩, fun _ => rfl⟩

set_option maxHeartbeats 1000000 in
/- **The inside test's shape**: the model's window is empty exactly when the lane at
`j1` is past it, or there is none — which is what the body's `%cmp7` reads, its lane's
value being the model's entry at that index. -/
theorem s2StringBodyInBody_empty_iff (ps : List Nat) (j1 pos0 len : Nat) :
    ((ps.drop j1).takeWhile (fun q => decide (q < pos0 + len))).isEmpty = true ↔
      (ps.drop j1 = [] ∨ ∃ a t, ps.drop j1 = a :: t ∧ pos0 + len ≤ a) := by
  rw [takeWhile_isEmpty_iff]
  constructor
  · rintro (h | ⟨a, t, heq, hneg⟩)
    · exact Or.inl h
    · refine Or.inr ⟨a, t, heq, ?_⟩
      have : ¬ a < pos0 + len := by simpa using hneg
      omega
  · rintro (h | ⟨a, t, heq, hle⟩)
    · exact Or.inl h
    · refine Or.inr ⟨a, t, heq, ?_⟩
      have : ¬ a < pos0 + len := by omega
      simpa using this

/-- A lane the list holds at `c` starts the drop at `c`. -/
theorem drop_eq_cons_of_getElem? {ps : List Nat} {c lane : Nat}
    (h : ps[c]? = some lane) : ps.drop c = lane :: ps.drop (c + 1) := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
  rw [← heq]
  exact List.drop_eq_getElem_cons hlt

/-- **`%cmp7`'s case**: a lane at or past the window's end makes the model's window
empty, which is the body-itself arm.  The lane is the one `readLanes32_lane` gives at
the scan's exit counter, and the comparison is the body's `%cmp7`. -/
theorem s2StringBodyWindow_empty_of_lane {ps : List Nat} {c pos0 len lane : Nat}
    (hlane : ps[c]? = some lane) (hle : pos0 + len ≤ lane) :
    ((ps.drop c).takeWhile (fun q => decide (q < pos0 + len))).isEmpty = true := by
  rw [s2StringBodyInBody_empty_iff]
  exact Or.inr ⟨lane, ps.drop (c + 1), drop_eq_cons_of_getElem? hlane, hle⟩

/-- **The expander arm's switch**: a lane below the window's end keeps the window
non-empty, which is the decoded/refused fork.  The dual of
`s2StringBodyWindow_empty_of_lane`, with `false`/`<` in place of `true`/`≤`. -/
theorem s2StringBodyWindow_cons_of_lane {ps : List Nat} {c pos0 len lane : Nat}
    (hlane : ps[c]? = some lane) (hlt : lane < pos0 + len) :
    ((ps.drop c).takeWhile (fun q => decide (q < pos0 + len))).isEmpty = false := by
  rw [drop_eq_cons_of_getElem? hlane]
  rw [List.takeWhile_cons_of_pos (p := fun q => decide (q < pos0 + len)) (by simpa using hlt)]
  rfl

/-! ### `%cmp9`: the call's answer

The expander answers all-ones on refusal and the decoded length otherwise, and the
body tests the returned word against all-ones. -/

/-- The refusal's answer: all-ones is all-ones. -/
theorem s2StringBodyBit_cmp9_refused {call : BitVec 64}
    (h : call = 0xffffffffffffffff#64) :
    evalICmp .eq call 0xffffffffffffffff#64 = 1#1 :=
  evalICmp_eq_one h

/-- The decoded answer: the returned word is not all-ones, so the test is `0`.  The
inequality is the caller's — it follows from the decoded length being a `Nat` below
`2 ^ 64`, which is the staging's fact rather than the bit's. -/
theorem s2StringBodyBit_cmp9_decoded {n : Nat} {call : BitVec 64}
    (hcall : call = BitVec.ofNat 64 n) (hne : call ≠ 0xffffffffffffffff#64) :
    evalICmp .eq call 0xffffffffffffffff#64 = 0#1 := by
  subst hcall
  exact evalICmp_eq_zero hne

/-! ### `%cmp1`: the lane against the body's start

The head's test is `sub` (the body's first position at `i64`) against the lane, and
the lane's value is the model's `ps` entry at the counter. -/

/-- The scan continues: the lane is below the body's start. -/
theorem s2StringBodyBit_cmp1_advance {pos0 q : Nat} (hpos0 : pos0 < 2 ^ 64)
    (hq : q < 2 ^ 32) (h : q < pos0) :
    evalICmpNat .ugt 64 (BitVec.ofNat 64 pos0).toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 q).toNat).toNat = 1#1 := by
  have hconv : (BitVec.ofNat 64 (BitVec.ofNat 32 q).toNat).toNat = q := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq,
      Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos0, hconv]
  exact evalICmpNat_ugt_one hpos0 (by omega) h

/-- The scan leaves: the lane is at or past the body's start. -/
theorem s2StringBodyBit_cmp1_exit {pos0 q : Nat} (hpos0 : pos0 < 2 ^ 64)
    (hq : q < 2 ^ 32) (h : pos0 ≤ q) :
    evalICmpNat .ugt 64 (BitVec.ofNat 64 pos0).toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 q).toNat).toNat = 0#1 := by
  have hconv : (BitVec.ofNat 64 (BitVec.ofNat 32 q).toNat).toNat = q := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq,
      Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos0, hconv]
  exact evalICmpNat_ugt_zero hpos0 (by omega) h

/-! ### The arm correspondence

The window's emptiness and the body's inside test are two readings of one comparison:
the lane at the scan's counter against `pos0 + len`.  The pair below is the bridge in
that direction, and it is where the model's three arms are separated from each other. -/

/-- **Empty window → the lane is past the window's end.**  Read
`s2StringBodyInBody_empty_iff` against the lane the list holds at the counter: the
window is empty only if there is no lane or the lane it starts at is at or past
`pos0 + len`. -/
theorem s2StringBodyWindow_lane_ge {ps : List Nat} {c pos0 len lane : Nat}
    (hlane : ps[c]? = some lane)
    (hempty : ((ps.drop c).takeWhile (fun q => decide (q < pos0 + len))).isEmpty = true) :
    pos0 + len ≤ lane := by
  rw [s2StringBodyInBody_empty_iff] at hempty
  rcases hempty with hnil | ⟨a, t, heq, hle⟩
  · rw [drop_eq_cons_of_getElem? hlane] at hnil
    exact absurd hnil (by simp)
  · rw [drop_eq_cons_of_getElem? hlane] at heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact hle

/-- **Non-empty window → the lane is inside it.**  The dual, by substitution. -/
theorem s2StringBodyWindow_lane_lt {ps : List Nat} {c pos0 len lane : Nat}
    (hlane : ps[c]? = some lane)
    (hcons : ((ps.drop c).takeWhile (fun q => decide (q < pos0 + len))).isEmpty = false) :
    lane < pos0 + len := by
  by_contra hge
  have hempty : ((ps.drop c).takeWhile (fun q => decide (q < pos0 + len))).isEmpty = true :=
    s2StringBodyWindow_empty_of_lane hlane (by omega)
  rw [hempty] at hcons
  exact absurd hcons (by simp)

/-- The scan's head state, named: the entry's output environment over the entry's
output state, cursor advanced by the slot.  Rule four at the level of a *state* — the
five-cell record update is spelled once, here, because the parser will not read it
inside a tuple and because the contract names this state repeatedly. -/
def s2StringBodyHeadState (env : Env) (s : State) (base p j0 : Nat)
    (nxp : BitVec 64) : State :=
  stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
    { s with next := s.next + (Ty.int 64).sizeBytes, pc := "land.rhs", pre := some s.pc }

/-- **The entry, seated**: the body's first control step reaches the named head, and
the invariant holds there.  The prefix and the seat, consumed as one fact. -/
theorem s2StringBodyEntry_seat_landRhs {env : Env} {s : State}
    {c p xj base j0 xp : Nat} {nxp : BitVec 64} {ps : List Nat}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hxpc : lookupName env "%xp" = some (.ptr xp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0)) (hj64 : j0 < 2 ^ 64)
    (hbit : evalICmp .ult (BitVec.ofNat 64 j0) nxp = 1#1)
    (hble : base ≤ p)
    (hword : stage2ReadWord s.mem xj 8 = some j0)
    (hps : readLanes32 s.mem xp nxp.toNat = some ps)
    (hj0N : j0 < nxp.toNat) :
    (∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
        runFuel s2StringBodyCalls k s2StringBodyBody
          (s2StringBodyHeadState env s base p j0 nxp)) ∧
      s2StringBodyScanInv s.mem xj (p - base) xp nxp.toNat ps (nxp.toNat - j0)
        (s2StringBodyHeadState env s base p j0 nxp) j0 :=
  ⟨s2StringBodyEntry_prefix_landRhs hpc hc hp hxj hnxp hbase hb64 hp64 hj0 hj64 hbit,
   s2StringBodyScanInv_seat env s base p xj xp j0 ps nxp hpc hble hp64 hword hps hj0N
     hxpc hxj hnxp⟩

/-- **The contract's statement, checked** — not proved.  It is the module's opening
sentence made into a proposition: at the staging `s2StringBodyPre` states, the body's
run answers with a `CallOutcome` satisfying the post and the footprint.  The budget is
a term of the arguments — the entry's one step, the scan's `(N + 1) * 2`, and the
longest arm's five — so the statement's fuel is computable before any proof is written.

The eight premises are all proved (see the assembly note); what is missing is the
composition.  Checking the statement here, in this module's options, is the point:
the shape is settled, and the proof is the only thing outstanding. -/
example {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2StringBodyPre args mem next)
    (hgoal : ∃ o : CallOutcome,
      runFuel s2StringBodyCalls
          (1 + (2 + 1) * 2 + 5) s2StringBodyBody
          (stagedState s2StringBodyBody args mem next) =
        some (.ret (some o.ret) o.mem) ∧
      s2StringBodyPost args mem next o ∧
      UnchangedOutside mem o.mem (s2StringBodyFoot args mem next)) :
    ∃ o : CallOutcome,
      runFuel s2StringBodyCalls
          (1 + (2 + 1) * 2 + 5) s2StringBodyBody
          (stagedState s2StringBodyBody args mem next) =
        some (.ret (some o.ret) o.mem) ∧
      s2StringBodyPost args mem next o ∧
      UnchangedOutside mem o.mem (s2StringBodyFoot args mem next) :=
  hgoal

/-- **The preamble**: the staged entry of the body carries the eight arguments as its
registers, the caller's memory and allocator, and the entry as its block.  Every arm's
proof starts here, so it is stated once and arm-independently. -/
theorem s2StringBodyStaged_entry (mem : Mem) (next : Nat)
    {c p dst outn xp xj : Nat} {len nxp : BitVec 64} :
    (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).pc = "entry" ∧
    lookupName (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).env "%c" = some (.ptr c) ∧
    lookupName (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).env "%p" = some (.ptr p) ∧
    lookupName (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).env "%len" = some (.int 64 len) ∧
    lookupName (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).env "%dst" = some (.ptr dst) ∧
    lookupName (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).env "%outn" = some (.ptr outn) ∧
    lookupName (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).env "%xp" = some (.ptr xp) ∧
    lookupName (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).env "%xj" = some (.ptr xj) ∧
    lookupName (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).env "%nxp" = some (.int 64 nxp) ∧
    (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).mem = mem ∧
    (stagedState s2StringBodyBody
      [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next).next = next := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩ <;>
    simp [stagedState, initState, s2StringBodyBody, List.zip_cons_cons,
      List.map_cons, lookupName]

/-- **Stage 2: the body-itself arm.**  With the cursor at the count the entry's test
fails; the body-itself arm writes the extent's word at `outn` and answers `1` — three
control steps.  The model's arm names the cursor word too, but the staging already
holds that word, so that write is the memory and the two memories agree. -/
theorem s2StringBodyArm_bodyItself {env : Env} {s : State}
    {c p xj base j0 outn : Nat} {nxp len : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0)) (hj64 : j0 < 2 ^ 64)
    (hbit : evalICmp .ult (BitVec.ofNat 64 j0) nxp = 0#1) :
    runFuel s2StringBodyCalls 3 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) := by
  have h1 := step_entry_ifThen hpc hc hp hxj hnxp hbase hb64 hp64 hj0 hj64 hbit
  have h2 : runFuel s2StringBodyCalls 2 s2StringBodyBody
      (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
        ({ s with next := s.next + (Ty.int 64).sizeBytes, pc := "if.then", pre := some s.pc })) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) :=
    s2StringBodyIfThen_finishes (env := s2StringBodyEntryOut env s.next base p j0 nxp)
      (s := { s with next := s.next + (Ty.int 64).sizeBytes, pc := "if.then", pre := some s.pc })
      rfl (by s2_lk) (by s2_lk)
  exact runFuel_prefix_some (fun k => runFuel_jump_prefix h1 k) h2

/-- **The scan stage**: from the seated head, the scan reaches an exit — the block it
lefts for, the word it leaves, and the prefix of fuel `(N + 1) * 2`.  The existential
form (rather than the outcome form `s2StringBodyScan_run` takes) is what the
composition needs: the exit's *state* is what the arm stages then dispatch on. -/
theorem s2StringBodyScan_reaches_exit (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64)
    (s : State) (c : Nat) (hinv : s2StringBodyScanInv mem0 xj pos0 xp N ps N s c) :
    ∃ (e : State) (j : Nat), j ≤ (N + 1) * 2 ∧ s2StringBodyScanExited e ∧
      s2StringBodyScanExitWord mem0 xj ps pos0 N e ∧
      ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
        runFuel s2StringBodyCalls k s2StringBodyBody e :=
  s2StringBodyScanLoop mem0 xj pos0 xp N ps hps hdisj hN hpos0 |>.run_from N s c hinv

/-! ### The scan's visited prefix

`s2StringBodyScanExitWord` records the counter the scan stopped at and what stopped
it, not the lanes it passed on the way there.  The model's `j1` is the `takeWhile`
length over the lanes below the body's first position, so the counter is that `j1`
only when every lane the scan passed is below it — and a caller of the run sees
only `Exit` and `ExitWord`, so the prefix has to be part of what the exit hands
back.  The instance below carries it as a conjunct of the invariant and of the exit
word, so `scanCounter_eq_takeWhile` applies at the state the run returns rather than
at a state the loop's proof no longer names.

The exit's stop condition is stated as `c = N` rather than the head's
`N ≤ c + 1`: both exits that this instance admits witness it in that form — the
head's exit at a lane inside the body, and `while.body`'s exit at the advanced
counter, which is exactly the count — and it is the form `scanCounter_eq_takeWhile`
consumes. -/

/-- **A name a prefix does not bind reads through it.**  The scan prepends its own
cells to the environment it was given and never rebinds a caller's register, so
each of the caller's cells survives the loop — this is `lookupName_cons_ne` peeled
once per prepended cell, and it is how a continuation reads the entry's registers
at an exit state it did not build. -/
theorem lookupName_append_of_forall {α : Type} {cells : List (String × α)}
    {name : String} {v : α} (env : List (String × α))
    (h : ∀ w, (name, w) ∈ cells → False) (h0 : lookupName env name = some v) :
    lookupName (cells ++ env) name = some v := by
  induction cells with
  | nil => simpa using h0
  | cons c rest ih =>
      obtain ⟨k, w⟩ := c
      rw [List.cons_append, lookupName_cons_ne w (rest ++ env)]
      · exact ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
      · intro hk
        exact h w (by rw [hk]; exact List.mem_cons_self ..)

/-- The lanes the scan has passed are the ones below the body's first position,
and the counter has not gone behind the cursor it started at. -/
def s2StringBodyScanPrefix (ps : List Nat) (pos0 j0 c : Nat) : Prop :=
  j0 ≤ c ∧ ∀ k, j0 ≤ k → k < c → ∃ q, ps[k]? = some q ∧ q < pos0

/-- The names the body's own blocks bind: the entry's seven and the scan's seven.
No caller's register is among them, which is what lets the exit's continuation read
the entry's argument cells through the prepended ones. -/
def s2StringBodyScanNames : List String :=
  ["%ei", "%0", "%sub.ptr.lhs.cast", "%sub.ptr.rhs.cast", "%sub.ptr.sub",
   "%xj.promoted", "%cmp3", "%cmp1", "%conv", "%1", "%arrayidx", "%inc24",
   "%inc", "%exitcond.not"]

/-- **The environment a scan state carries** is the caller's with the body's own
cells in front, and every one of those cells is the body's own name.  This is a
fact about the scan's run — it only ever prepends — rather than something the loop
has to preserve cell by cell. -/
def s2StringBodyScanShape (env0 : Env) (s : State) : Prop :=
  ∃ cells, s.env = cells ++ env0 ∧
    ∀ name w, (name, w) ∈ cells → name ∈ s2StringBodyScanNames

/-- **A caller's cell, read through the scan's own cells**: the shape plus the
name's absence from the body's own names is the pass-through at an exit state the
continuation did not build. -/
theorem s2StringBodyScan_lookup_env0 {env0 : Env} {s : State} {name : String}
    {v : Value} (hshape : s2StringBodyScanShape env0 s)
    (hname : name ∉ s2StringBodyScanNames) (h0 : lookupName env0 name = some v) :
    lookupName s.env name = some v := by
  obtain ⟨cells, hcells, hnames⟩ := hshape
  rw [hcells]
  refine lookupName_append_of_forall env0 (fun w hw => ?_) h0
  exact hname (hnames name w hw)

/-- **The registers a continuation reads, at the head's cells**: five caller
registers fall through the head's own five.  Stated as a bundle because the peel is
one `repeat rw` per goal and a `simp` over the whole environment duplicates the
arithmetic the cells carry — the cost this file records for `s2_lk`. -/
theorem s2StringBodyScan_lookup_landRhs {env : Env} {ei xp xj pos0 N : Nat}
    {inc24 : BitVec 64} {bs : List UInt8} {sub : BitVec 64}
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 (BitVec.ofNat 64 pos0)))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 (BitVec.ofNat 64 N))) :
    lookupName (s2StringBodyLandRhsEnv env inc24 xp bs sub) "%ei" = some (.ptr ei) ∧
    lookupName (s2StringBodyLandRhsEnv env inc24 xp bs sub) "%sub.ptr.sub"
        = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
    lookupName (s2StringBodyLandRhsEnv env inc24 xp bs sub) "%xp" = some (.ptr xp) ∧
    lookupName (s2StringBodyLandRhsEnv env inc24 xp bs sub) "%xj" = some (.ptr xj) ∧
    lookupName (s2StringBodyLandRhsEnv env inc24 xp bs sub) "%nxp"
        = some (.int 64 (BitVec.ofNat 64 N)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [s2StringBodyLandRhsEnv]
     repeat rw [lookupName_cons_ne _ _ (by decide)]
     first | exact hei | exact hsub | exact hxp | exact hxj | exact hnxp)

/-- The same at the counter's two cells over the head's. -/
theorem s2StringBodyScan_lookup_iterate {env : Env} {ei xp xj pos0 N : Nat}
    {inc24 nxp : BitVec 64} {bs : List UInt8} {sub : BitVec 64}
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 (BitVec.ofNat 64 pos0)))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 (BitVec.ofNat 64 N))) :
    lookupName (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
      ("%inc", .int 64 (inc24 + 1#64)) ::
      s2StringBodyLandRhsEnv env inc24 xp bs sub) "%ei" = some (.ptr ei) ∧
    lookupName (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
      ("%inc", .int 64 (inc24 + 1#64)) ::
      s2StringBodyLandRhsEnv env inc24 xp bs sub) "%sub.ptr.sub"
        = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
    lookupName (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
      ("%inc", .int 64 (inc24 + 1#64)) ::
      s2StringBodyLandRhsEnv env inc24 xp bs sub) "%xp" = some (.ptr xp) ∧
    lookupName (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
      ("%inc", .int 64 (inc24 + 1#64)) ::
      s2StringBodyLandRhsEnv env inc24 xp bs sub) "%xj" = some (.ptr xj) ∧
    lookupName (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
      ("%inc", .int 64 (inc24 + 1#64)) ::
      s2StringBodyLandRhsEnv env inc24 xp bs sub) "%nxp"
        = some (.int 64 (BitVec.ofNat 64 N)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (repeat rw [lookupName_cons_ne _ _ (by decide)]
     first | exact hei | exact hsub | exact hxp | exact hxj | exact hnxp)

/-- The scan's invariant with the visited prefix, the environment's shape, and the
body's own slot **by value**.  `%ei` is the one cell that cannot pass through: the
entry's `alloca` shadows the caller's name, so the value the exit's continuation
needs is the one the entry bound, and it has to be stated. -/
def s2StringBodyScanInvP (mem0 : Mem) (xj pos0 xp N j0 : Nat) (ps : List Nat)
    (env0 : Env) (ei : Nat) (r : Nat) (s : State) (c : Nat) : Prop :=
  s2StringBodyScanInv mem0 xj pos0 xp N ps r s c ∧
    s2StringBodyScanPrefix ps pos0 j0 c ∧
    s2StringBodyScanShape env0 s ∧
    lookupName s.env "%ei" = some (.ptr ei)

/-- What the scan leaves behind, with the visited prefix at the counter it stopped
at. -/
def s2StringBodyScanExitWordP (mem0 : Mem) (xj j0 : Nat) (ps : List Nat)
    (pos0 N : Nat) (env0 : Env) (ei xp : Nat) (e : State) : Prop :=
  ∃ c, e.mem = writeBytes mem0 xj (wordBytes 8 c) ∧
    s2StringBodyScanPrefix ps pos0 j0 c ∧ s2StringBodyScanShape env0 e ∧
    lookupName e.env "%ei" = some (.ptr ei) ∧
    lookupName e.env "%sub.ptr.sub" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
    lookupName e.env "%xp" = some (.ptr xp) ∧
    lookupName e.env "%xj" = some (.ptr xj) ∧
    lookupName e.env "%nxp" = some (.int 64 (BitVec.ofNat 64 N)) ∧
    -- the exit's block decides which way the scan stopped, so each arm reads its
    -- own case directly
    (e.pc = "if.then" → c = N) ∧
    (e.pc = "land.lhs.true" → ∃ q conv, ps[c]? = some q ∧ pos0 ≤ q ∧
      lookupName e.env "%conv" = some (.int 64 conv) ∧ conv.toNat = q)

/-- At its own start the scan has passed nothing. -/
theorem s2StringBodyScanPrefix_self (ps : List Nat) (pos0 j0 : Nat) :
    s2StringBodyScanPrefix ps pos0 j0 j0 := by
  refine ⟨le_rfl, ?_⟩
  intro k _ hk
  exact absurd hk (by omega)

/-- The strengthened exit word is the old one: `c = N` is the count reached. -/
theorem s2StringBodyScanExitWordP.toExitWord {mem0 : Mem} {xj j0 : Nat} {ps : List Nat}
    {pos0 N : Nat} {env0 : Env} {ei xp : Nat} {e : State}
    (hexit : s2StringBodyScanExited e)
    (h : s2StringBodyScanExitWordP mem0 xj j0 ps pos0 N env0 ei xp e) :
    s2StringBodyScanExitWord mem0 xj ps pos0 N e := by
  obtain ⟨c, hmem, hfix, hshape, hei, hsub, hxp, hxj, hnxp, hif, hland⟩ := h
  refine ⟨c, hmem, ?_⟩
  rcases hexit with hpc | hpc
  · obtain ⟨q, conv, hq, hge, -, -⟩ := hland hpc
    exact Or.inr ⟨q, hq, hge⟩
  · exact Or.inl (by have := hif hpc; omega)

/-- **The exit's counter is the model's `j1`.**  The prefix the strengthened exit
word carries is `scanCounter_eq_takeWhile`'s visited-prefix hypothesis, and the stop
condition is its stopping hypothesis. -/
theorem s2StringBodyScanExit_j1 {ps : List Nat} {pos0 N j0 c : Nat}
    (hfix : s2StringBodyScanPrefix ps pos0 j0 c)
    (hstop : c = N ∨ ∃ q, ps[c]? = some q ∧ pos0 ≤ q)
    (hlen : ps.length = N) :
    c = j0 + ((ps.drop j0).takeWhile (fun q => decide (q < pos0))).length := by
  refine scanCounter_eq_takeWhile ps pos0 j0 c hfix.1 hfix.2 ?_
  rcases hstop with hN | ⟨q, hq, hge⟩
  · exact Or.inl (List.getElem?_eq_none (by omega))
  · exact Or.inr ⟨q, hq, hge⟩

/-- **The exit arm, with the prefix**: the same two exits as
`s2StringBodyScan_step_exit`, each handing back the lanes it passed. -/
theorem s2StringBodyScan_step_exitP (mem0 : Mem) (xj pos0 xp N j0 : Nat)
    (ps : List Nat) (env0 : Env) (ei : Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64)
    (r c : Nat) (s : State)
    (hinv : s2StringBodyScanInvP mem0 xj pos0 xp N j0 ps env0 ei r s c)
    (hbound : s2StringBodyScanAtBound ps pos0 N s c = true) :
    ∃ (e : State) (j : Nat), j ≤ 2 ∧ s2StringBodyScanExited e ∧
      s2StringBodyScanExitWordP mem0 xj j0 ps pos0 N env0 ei xp e ∧
      ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
        runFuel s2StringBodyCalls k s2StringBodyBody e := by
  obtain ⟨hinv, hfix, hshape, hei⟩ := hinv
  obtain ⟨hpc, hmem, hsum, ⟨p, op, hpre, hinc, hop⟩, hxp, hsub, hxj, hnxp,
    ⟨q, bs, hq, hblen, hval, hlane⟩⟩ := hinv
  have hlen : ps.length = N := (readLanes32_lane hps).1
  have hcN : c < N := by
    have : c < ps.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hq
      cases hq
    omega
  have hb : s2StringBodyScanAtBound ps pos0 N s c = true := hbound
  rw [s2StringBodyScanAtBound_eq] at hbound
  have hN64 : N < 2 ^ 64 := by omega
  have hpos : ((BitVec.ofNat 64 c).signExtend 64).toNat < 2 ^ 63 := by
    rw [signExtend_ofNat c (by omega)]; omega
  have hidx : ((BitVec.ofNat 64 c).signExtend 64).toNat * 4 = 4 * c := by
    rw [signExtend_ofNat c (by omega)]; omega
  have hlane' : readBytes s.mem (xp + ((BitVec.ofNat 64 c).signExtend 64).toNat * 4) 4
      = some bs := by
    rw [hidx]; exact hlane
  have hconv : (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = q := by
    have h32 := bytesToNat_lt_32 hblen
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32,
      Nat.mod_eq_of_lt (by omega), hval]
  by_cases hge : pos0 ≤ q
  · -- the lane is already inside the body: the head's exit, one step
    have hbit : evalICmpNat .ugt 64 (BitVec.ofNat 64 pos0).toNat
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 0#1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos0, hconv]
      exact evalICmpNat_ugt_of_ge hpos0 (by have := bytesToNat_lt_32 hblen; omega) hge
    have hrun := s2StringBodyScanExit (envH := s.env) (s := s) (p := p) (op := op)
      hpc hpre hinc hop hxp hsub hpos hlane' hbit
    let e : State := stateAt (s2StringBodyLandRhsEnv s.env (BitVec.ofNat 64 c) xp bs
        (BitVec.ofNat 64 pos0)) { s with pc := "land.lhs.true", pre := some s.pc }
    have hconv' : lookupName e.env "%conv" =
        some (.int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat)) := by
      simp only [e, stateAt, s2StringBodyLandRhsEnv]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    obtain ⟨hei', hsub', hxp', hxj', hnxp'⟩ := by
      simpa only [e, stateAt] using
        s2StringBodyScan_lookup_landRhs (inc24 := BitVec.ofNat 64 c) (bs := bs)
          (sub := BitVec.ofNat 64 pos0) hei hsub hxp hxj hnxp
    have hshape' : s2StringBodyScanShape env0 e := by
      obtain ⟨cells, hcells, hnames⟩ := hshape
      refine ⟨s2StringBodyLandRhsEnv [] (BitVec.ofNat 64 c) xp bs
        (BitVec.ofNat 64 pos0) ++ cells, ?_, ?_⟩
      · simp only [e, stateAt, s2StringBodyLandRhsEnv, hcells, List.nil_append,
          List.cons_append, List.append_assoc]
      · intro name w hw
        simp only [List.mem_append] at hw
        rcases hw with hw | hw
        · simp only [s2StringBodyLandRhsEnv, List.mem_cons, List.not_mem_nil,
            or_false, Prod.mk.injEq] at hw
          obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ := hw <;> simp [s2StringBodyScanNames]
        · exact hnames name w hw
    refine ⟨e, 1, by decide, Or.inl rfl, ?_, hrun⟩
    refine ⟨c, by simp only [e, stateAt]; exact hmem, hfix, hshape', hei', hsub',
      hxp', hxj', hnxp', ?_, ?_⟩
    · intro h
      simp only [e, stateAt] at h
      exact absurd h (by decide)
    · intro _
      exact ⟨q, BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat, hq, hge,
        hconv', hconv⟩
  · -- the lane is below the body's start, so only the count can have stopped it
    have hlt : q < pos0 := by omega
    have hNle : N ≤ c + 1 := by
      rcases hbound with h | ⟨q', hq', hge'⟩
      · exact h
      · rw [hq] at hq'; cases Option.some.inj hq'; exact absurd hge' hge
    have heqc : c + 1 = N := by omega
    have hbit1 : evalICmpNat .ugt 64 (BitVec.ofNat 64 pos0).toNat
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 1#1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos0, hconv]
      exact evalICmpNat_ugt_one hpos0 (by have := bytesToNat_lt_32 hblen; omega) hlt
    have hbit2 : evalICmp .eq ((BitVec.ofNat 64 c) + 1#64) (BitVec.ofNat 64 N) = 1#1 :=
      evalICmp_eq_of_eq hN64 heqc.symm
    have hrun := s2StringBodyScanIterateExit (envH := s.env) (s := s) (p := p) (op := op)
      hpc hpre hxj hnxp hinc hop hxp hsub hpos hlane' hbit1 hbit2
    let e : State := stateAt
        (("%exitcond.not", .int 1 (evalICmp .eq ((BitVec.ofNat 64 c) + 1#64)
            (BitVec.ofNat 64 N))) ::
          ("%inc", .int 64 ((BitVec.ofNat 64 c) + 1#64)) ::
          s2StringBodyLandRhsEnv s.env (BitVec.ofNat 64 c) xp bs (BitVec.ofNat 64 pos0))
        ({ s with mem := writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8), pc := "if.then", pre := some "while.body" })
    obtain ⟨hei', hsub', hxp', hxj', hnxp'⟩ := by
      simpa only [e, stateAt] using
        s2StringBodyScan_lookup_iterate (inc24 := BitVec.ofNat 64 c)
          (nxp := BitVec.ofNat 64 N) (bs := bs) (sub := BitVec.ofNat 64 pos0)
          hei hsub hxp hxj hnxp
    have hshape' : s2StringBodyScanShape env0 e := by
      obtain ⟨cells, hcells, hnames⟩ := hshape
      refine ⟨("%exitcond.not", .int 1 (evalICmp .eq ((BitVec.ofNat 64 c) + 1#64)
          (BitVec.ofNat 64 N))) ::
        ("%inc", .int 64 ((BitVec.ofNat 64 c) + 1#64)) ::
        (s2StringBodyLandRhsEnv [] (BitVec.ofNat 64 c) xp bs
          (BitVec.ofNat 64 pos0) ++ cells), ?_, ?_⟩
      · simp only [e, stateAt, s2StringBodyLandRhsEnv, hcells, List.nil_append,
          List.cons_append, List.append_assoc]
      · intro name w hw
        simp only [List.mem_cons, List.mem_append] at hw
        obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ | hw | hw := hw
        · simp [s2StringBodyScanNames]
        · simp [s2StringBodyScanNames]
        · simp only [s2StringBodyLandRhsEnv, List.mem_cons, List.not_mem_nil,
            or_false, Prod.mk.injEq] at hw
          obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ := hw <;> simp [s2StringBodyScanNames]
        · exact hnames name w hw
    have hfix' : s2StringBodyScanPrefix ps pos0 j0 (c + 1) := by
      refine ⟨Nat.le_succ_of_le hfix.1, ?_⟩
      intro k hjk hkc
      rcases Nat.lt_or_ge k c with hltc | hgec
      · exact hfix.2 k hjk hltc
      · have hk : k = c := by omega
        subst hk
        exact ⟨q, hq, hlt⟩
    refine ⟨e, 2, le_rfl, Or.inr rfl, ?_, hrun⟩
    refine ⟨c + 1, ?_, hfix', hshape', hei', hsub', hxp', hxj', hnxp', ?_, ?_⟩
    · simp only [e, stateAt]
      rw [show (writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8))
          = writeBytes mem0 xj (wordBytes 8 (c + 1)) from
        s2StringBodyScan_advance mem0 xj c s hmem (by omega)]
    · intro _
      exact heqc
    · intro h
      simp only [e, stateAt] at h
      exact absurd h (by decide)

/-- **The back edge, with the prefix**: one iteration, and the lane it passed joins
the prefix. -/
theorem s2StringBodyScan_step_loopP (mem0 : Mem) (xj pos0 xp N j0 : Nat)
    (ps : List Nat) (env0 : Env) (ei : Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64)
    (r c : Nat) (s : State)
    (hinv : s2StringBodyScanInvP mem0 xj pos0 xp N j0 ps env0 ei (r + 1) s c)
    (hbound : s2StringBodyScanAtBound ps pos0 N s c = false) :
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 2 ∧ e.pc = "land.rhs" ∧ c < c' ∧
      s2StringBodyScanInvP mem0 xj pos0 xp N j0 ps env0 ei r e c' ∧
      ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
        runFuel s2StringBodyCalls k s2StringBodyBody e := by
  obtain ⟨hinv, hfix, hshape, hei⟩ := hinv
  obtain ⟨hpc, hmem, hsum, ⟨p, op, hpre, hinc, hop⟩, hxp, hsub, hxj, hnxp,
    ⟨q, bs, hq, hblen, hval, hlane⟩⟩ := hinv
  have hlen : ps.length = N := (readLanes32_lane hps).1
  have hb : s2StringBodyScanAtBound ps pos0 N s c = false := hbound
  rw [s2StringBodyScanAtBound_false] at hbound
  have hcN : c + 1 < N := by
    by_contra h; exact hbound (Or.inl (by omega))
  have hc : c < N := by omega
  have hltq : q < pos0 := by
    by_contra h
    exact hbound (Or.inr ⟨q, hq, by omega⟩)
  have hN64 : N < 2 ^ 64 := by omega
  have hpos : ((BitVec.ofNat 64 c).signExtend 64).toNat < 2 ^ 63 := by
    rw [signExtend_ofNat c (by omega)]; omega
  obtain ⟨hbit1, hbit2⟩ :=
    s2StringBodyScan_bits_of_not_atBound hb hq hval hblen rfl hpos0 rfl rfl hN64
  have hidx : ((BitVec.ofNat 64 c).signExtend 64).toNat * 4 = 4 * c := by
    rw [signExtend_ofNat c (by omega)]
    omega
  have hlane' : readBytes s.mem (xp + ((BitVec.ofNat 64 c).signExtend 64).toNat * 4) 4
      = some bs := by
    rw [hidx]
    exact hlane
  have hrun := s2StringBodyScanIterate (envH := s.env) (s := s) (p := p) (op := op)
    hpc hpre hxj hnxp hinc hop hxp hsub hpos hlane' hbit1 hbit2
  obtain ⟨laneQ, laneBs, hq', hlaneM, hval'⟩ :=
    (readLanes32_lane hps).2 (c + 1) hcN
  have hblen' : laneBs.length = 4 := readBytes_length_some hlaneM
  have hframe : readBytes (writeBytes mem0 xj (wordBytes 8 (c + 1))) (xp + 4 * (c + 1)) 4
      = some laneBs := by
    rcases hdisj (c + 1) hcN with h | h
    · rw [readBytes_writeBytes_below mem0 (wordBytes 8 (c + 1)) 4 (xp + 4 * (c + 1)) xj
        (by omega)]
      exact hlaneM
    · rw [s2StringBodyReadBytes_above mem0 (wordBytes 8 (c + 1)) 4 (xp + 4 * (c + 1)) xj
        (by simp [wordBytes, natToBytes_length]; omega)]
      exact hlaneM
  let e : State := stateAt
      (("%exitcond.not", .int 1 (evalICmp .eq ((BitVec.ofNat 64 c) + 1#64)
          (BitVec.ofNat 64 N))) ::
        ("%inc", .int 64 ((BitVec.ofNat 64 c) + 1#64)) ::
        s2StringBodyLandRhsEnv s.env (BitVec.ofNat 64 c) xp bs (BitVec.ofNat 64 pos0))
      ({ s with mem := writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8), pc := "land.rhs", pre := some "while.body" })
  have hfix' : s2StringBodyScanPrefix ps pos0 j0 (c + 1) := by
    refine ⟨Nat.le_succ_of_le hfix.1, ?_⟩
    intro k hjk hkc
    rcases Nat.lt_or_ge k c with hltc | hgec
    · exact hfix.2 k hjk hltc
    · have hk : k = c := by omega
      subst hk
      exact ⟨q, hq, hltq⟩
  obtain ⟨hei', -, -, -, -⟩ := by
    simpa only [e, stateAt] using
      s2StringBodyScan_lookup_iterate (inc24 := BitVec.ofNat 64 c)
        (nxp := BitVec.ofNat 64 N) (bs := bs) (sub := BitVec.ofNat 64 pos0)
        hei hsub hxp hxj hnxp
  have hshape' : s2StringBodyScanShape env0 e := by
    obtain ⟨cells, hcells, hnames⟩ := hshape
    refine ⟨("%exitcond.not", .int 1 (evalICmp .eq ((BitVec.ofNat 64 c) + 1#64)
        (BitVec.ofNat 64 N))) ::
      ("%inc", .int 64 ((BitVec.ofNat 64 c) + 1#64)) ::
      (s2StringBodyLandRhsEnv [] (BitVec.ofNat 64 c) xp bs
        (BitVec.ofNat 64 pos0) ++ cells), ?_, ?_⟩
    · simp only [e, stateAt, s2StringBodyLandRhsEnv, hcells, List.nil_append,
        List.cons_append, List.append_assoc]
    · intro name w hw
      simp only [List.mem_cons, List.mem_append] at hw
      obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ | hw | hw := hw
      · simp [s2StringBodyScanNames]
      · simp [s2StringBodyScanNames]
      · simp only [s2StringBodyLandRhsEnv, List.mem_cons, List.not_mem_nil,
          or_false, Prod.mk.injEq] at hw
        obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ := hw <;> simp [s2StringBodyScanNames]
      · exact hnames name w hw
  refine ⟨e, c + 1, 2, le_rfl, rfl, by omega, ⟨?_, hfix', hshape', hei'⟩, ?_⟩
  · refine ⟨rfl, ?_, by omega,
      ⟨"while.body", Operand.reg "%inc", rfl, by simp [phiIncoming], ?_⟩,
      ?_, ?_, ?_, ?_, ⟨laneQ, laneBs, hq', hblen', hval', ?_⟩⟩
    · exact s2StringBodyScan_advance mem0 xj c s hmem (by omega)
    · simp [e, stateAt, evalOperand, lookupName, s2StringBodyLandRhsEnv, ofNat_add_one]
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hxp
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hsub
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hxj
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hnxp
    · simp only [e]
      rw [show (writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8))
          = writeBytes mem0 xj (wordBytes 8 (c + 1)) from
        s2StringBodyScan_advance mem0 xj c s hmem (by omega)]
      exact hframe
  · exact hrun

/-- **The scan, as a `BoundLoop`, handing back the lanes it passed.** -/
def s2StringBodyScanLoopP (mem0 : Mem) (xj pos0 xp N j0 : Nat) (ps : List Nat)
    (env0 : Env) (ei : Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64) :
    BoundLoop s2StringBodyCalls s2StringBodyBody where
  head := "land.rhs"
  exitBlock := "land.lhs.true"
  N := N
  cost := 2
  Inv := s2StringBodyScanInvP mem0 xj pos0 xp N j0 ps env0 ei
  atBound := s2StringBodyScanAtBound ps pos0 N
  Exit := s2StringBodyScanExited
  ExitWord := s2StringBodyScanExitWordP mem0 xj j0 ps pos0 N env0 ei xp
  step_exit := fun r s c =>
    s2StringBodyScan_step_exitP mem0 xj pos0 xp N j0 ps env0 ei hps hdisj hN hpos0 r c s
  step_loop := fun r s c =>
    s2StringBodyScan_step_loopP mem0 xj pos0 xp N j0 ps env0 ei hps hdisj hN hpos0 r c s
  exit_at_zero := by
    intro s c h
    obtain ⟨hb, -⟩ := h
    obtain ⟨_hpc, _hmem, hsum, _⟩ := hb
    rw [s2StringBodyScanAtBound_eq]
    exact Or.inl (by omega)
  budget := by
    intro r s c h
    obtain ⟨hb, -⟩ := h
    obtain ⟨_hpc, _hmem, hsum, _⟩ := hb
    omega

/-- **The scan's run, with the lanes it passed**: from the seated head, the exit at
`(N + 1) * 2` steps carries the model's `j1` as its counter. -/
theorem s2StringBodyScan_runP (mem0 : Mem) (xj pos0 xp N j0 : Nat) (ps : List Nat)
    (env0 : Env) (ei : Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64)
    (s : State) (c : Nat) (k : Nat)
    (hinv : s2StringBodyScanInvP mem0 xj pos0 xp N j0 ps env0 ei N s c) {o : Outcome}
    (hcont : ∀ (e : State), s2StringBodyScanExited e →
      s2StringBodyScanExitWordP mem0 xj j0 ps pos0 N env0 ei xp e →
      runFuel s2StringBodyCalls k s2StringBodyBody e = some o) :
    runFuel s2StringBodyCalls ((N + 1) * 2 + k) s2StringBodyBody s = some o :=
  (s2StringBodyScanLoopP mem0 xj pos0 xp N j0 ps env0 ei hps hdisj hN hpos0).run_at s c hinv k hcont

/-- **The scan's exit, existentially**: the exit's state, the counter, and the word
beside the run's prefix.  The arms dispatch on the state, so this is the form a
composition consumes; `s2StringBodyScan_runP` is the same run with the outcome
fixed in advance. -/
theorem s2StringBodyScan_reaches_exitP (mem0 : Mem) (xj pos0 xp N j0 : Nat)
    (ps : List Nat) (env0 : Env) (ei : Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64)
    (s : State) (c : Nat) (hinv : s2StringBodyScanInvP mem0 xj pos0 xp N j0 ps env0 ei N s c) :
    ∃ (e : State) (j : Nat), j ≤ (N + 1) * 2 ∧ s2StringBodyScanExited e ∧
      s2StringBodyScanExitWordP mem0 xj j0 ps pos0 N env0 ei xp e ∧
      ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
        runFuel s2StringBodyCalls k s2StringBodyBody e :=
  s2StringBodyScanLoopP mem0 xj pos0 xp N j0 ps env0 ei hps hdisj hN hpos0
    |>.run_from N s c hinv

/-- **The seated invariant, with the prefix and the environment's shape**: at the
head the entry leaves, the scan has passed nothing and the body's seven cells are
the entry's, over the caller's environment. -/
theorem s2StringBodyScanInvP_seat (env : Env) (s : State) (base p xj xp j0 : Nat)
    (ps : List Nat) (nxp : BitVec 64)
    (hpc : s.pc = "entry")
    (hbase : base ≤ p) (hp64 : p < 2 ^ 64)
    (hword : stage2ReadWord s.mem xj 8 = some j0)
    (hps : readLanes32 s.mem xp nxp.toNat = some ps)
    (hj0 : j0 < nxp.toNat)
    (hxpc : lookupName env "%xp" = some (.ptr xp))
    (hxjc : lookupName env "%xj" = some (.ptr xj))
    (hnxpc : lookupName env "%nxp" = some (.int 64 nxp)) :
    s2StringBodyScanInvP s.mem xj (p - base) xp nxp.toNat j0 ps env s.next
      (nxp.toNat - j0)
      (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
        { s with next := s.next + (Ty.int 64).sizeBytes, pc := "land.rhs", pre := some s.pc })
      j0 := by
  refine ⟨s2StringBodyScanInv_seat env s base p xj xp j0 ps nxp hpc hbase hp64 hword hps
    hj0 hxpc hxjc hnxpc, s2StringBodyScanPrefix_self ps (p - base) j0, ?_, ?_⟩
  · refine ⟨s2StringBodyEntryOut [] s.next base p j0 nxp, ?_, ?_⟩
    · simp only [stateAt, s2StringBodyEntryOut, s2StringBodyEnv7, s2StringBodyEnv6,
        s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3, s2StringBodyEnv2,
        s2StringBodyEnv1, List.cons_append, List.nil_append]
    · intro name w hw
      simp only [s2StringBodyEntryOut, s2StringBodyEnv7, s2StringBodyEnv6,
        s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3, s2StringBodyEnv2,
        s2StringBodyEnv1, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hw
      obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
        ⟨rfl, -⟩ := hw <;> simp [s2StringBodyScanNames]
  · -- `%ei` is the entry's own cell, over the caller's environment
    simp only [stateAt, s2StringBodyEntryOut, s2StringBodyEnv7, s2StringBodyEnv6,
      s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3, s2StringBodyEnv2,
      s2StringBodyEnv1]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [lookupName_cons_self]

/-- The callee's decoded memory, named. -/
def s2StringBodyExpandMem (mem : Mem) (ei dst xj : Nat) (out outj : List UInt8) : Mem :=
  writeBytes (writeBytes (writeBytes (writeBytes mem ei (natToBytes (0#64).toNat 8)) dst out)
    xj outj) ei (wordBytes 8 out.length)

/-- The decoded arm's memory, named: the model's memory with the slot at the caller's
allocator. -/
def s2StringBodyDecodedMem (mem : Mem) (dst xj outn ei : Nat) (outj out : List UInt8) :
    Mem :=
  writeBytes (writeBytes (writeBytes (writeBytes mem dst out) xj outj) outn
    (wordBytes 8 out.length)) ei (wordBytes 8 out.length)

/-- **The decoded join at the named memories.**  The heavy laminate is unfolded once,
here, so the arm's statement and proof match on identifiers. -/
theorem s2StringBodyMemory_decoded_named (mem : Mem) {ei dst xj outn j1 k : Nat}
    {out : List UInt8}
    (hdst : readBytes mem dst out.length ≠ none)
    (hxj : readBytes mem xj 8 ≠ none)
    (houtn : readBytes mem outn 8 ≠ none)
    (hd_ei : ei + 8 ≤ dst ∨ dst + out.length ≤ ei)
    (hx_ei : ei + 8 ≤ xj ∨ xj + 8 ≤ ei)
    (hd_xj : dst + out.length ≤ xj ∨ xj + 8 ≤ dst)
    (ho_ei : ei + 8 ≤ outn ∨ outn + 8 ≤ ei)
    (ho_d : outn + 8 ≤ dst ∨ dst + out.length ≤ outn)
    (ho_x : outn + 8 ≤ xj ∨ xj + 8 ≤ outn) :
    writeBytes (s2StringBodyExpandMem mem ei dst xj out (wordBytes 8 (j1 + k)))
        outn (natToBytes out.length 8)
      = s2StringBodyDecodedMem mem dst xj outn ei (wordBytes 8 (j1 + k)) out := by
  simp only [s2StringBodyExpandMem, s2StringBodyDecodedMem]
  exact s2StringBodyMemory_decoded mem hdst hxj houtn hd_ei hx_ei hd_xj ho_ei ho_d ho_x

set_option maxHeartbeats 2000000 in
/-- **The decoded terminal at the named memory.**  The laminate `s2StringBodyExit_decoded`
spells in its conclusion is paid once here, so a composition matches on the identifier
and never unfolds it.  The hypotheses are that theorem's, plus the two facts that name
the call's answer and the callee's memory. -/
theorem s2StringBodyExit_decoded_named {e : State} {sub len conv : BitVec 64}
    {p dst ei outn xp xj : Nat} {nxp : BitVec 64} {extra : Mem} {nx : Nat}
    {call : BitVec 64} {outj out : List UInt8}
    (hpc : e.pc = "land.lhs.true")
    (hsub : lookupName e.env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName e.env "%len" = some (.int 64 len))
    (hconv : lookupName e.env "%conv" = some (.int 64 conv))
    (hbit7 : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1)
    (hp : lookupName e.env "%p" = some (.ptr p))
    (hdst : lookupName e.env "%dst" = some (.ptr dst))
    (hei : lookupName e.env "%ei" = some (.ptr ei))
    (hxp : lookupName e.env "%xp" = some (.ptr xp))
    (hxj : lookupName e.env "%xj" = some (.ptr xj))
    (hnxp : lookupName e.env "%nxp" = some (.int 64 nxp))
    (hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes e.mem ei (natToBytes (0#64).toNat 8)) e.next =
      some { ret := .int 64 call, mem := extra, next := nx })
    (hbit9 : evalICmp .eq call 0xffffffffffffffff#64 = 0#1)
    (houtn : lookupName e.env "%outn" = some (.ptr outn))
    (hextra : extra = s2StringBodyExpandMem e.mem ei dst xj out outj)
    (hcall : call = BitVec.ofNat 64 out.length) (hlenOut : out.length < 2 ^ 64) :
    runFuel s2StringBodyCalls 5 s2StringBodyBody e =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes (s2StringBodyExpandMem e.mem ei dst xj out outj) outn
          (natToBytes out.length 8))) := by
  have htoNat : (BitVec.ofNat 64 out.length).toNat = out.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlenOut]
  have hstep := s2StringBodyExit_decoded (e := e) hpc hsub hlen hconv hbit7 hp hdst hei
    hxp hxj hnxp hexp hbit9 houtn
  rw [hcall, htoNat, hextra] at hstep
  exact hstep

/-- The body's own slot is eight bytes, so the run's cursor moves by exactly the
post's `next + 8` — and nothing else in the body moves it: the callee keeps `next`,
and the other blocks allocate nothing. -/
theorem s2StringBodySlot_sizeBytes : (Ty.int 64).sizeBytes = 8 := by decide

/- **The arms are separated by the window, not by the scan's exit.**  Stage 3's plan —
"seat + scan + split + `%cmp9` → decoded" — needs one correction the four-bit work
reveals: the scan's **two** exits both lead onward, and which model arm they reach is
decided by the *window* at the exit counter, not by which exit was taken.  `if.then`
out of `while.body` (the counter reached the count) is the body-itself arm when the
window there is empty, and `land.lhs.true` is the inside test, whose own bit then picks
`if.then` or `if.end`.  So the composition is:

* one **scan stage**: seat → prefix → `s2StringBodyScan_run` → the exit, with the window
  decided by `s2StringBodyWindow_lane_ge`/`_lt` at the exit counter;
* then the **`%cmp9` fork**, shared by the decoded and refused arms, which is the only
  thing that differs between them.

Stating it this way is why stage 2 was three steps: it is the *entry's* `%cmp3` arm, a
different way into the same form. -/

/- **The assembly's content, and it is the control flow, not the memory.**  The
memory was done: both arms' joins, the record reconciliation, the `takeWhile`
bridge.  What the contract needed besides it was the correspondence between the
model's three-way split and the body's four branch bits, each derived from the
model's own data:

* `%cmp3` (entry) is `j0 < nxp.toNat` — the pre's `j0 < 2^63` and the model's
  `readLanes32` give it;
* `%cmp1` (the head) is `pos0 ≤ ps[c]` read backwards: the lane's value is the model's
  entry (`readLanes32_lane`) and `sub` is `pos0` at `i64` (`ofNat_sub`);
* `%cmp7` (the inside test) is `pos0 + len` against that lane — which is where the
  model's `inBody.isEmpty` decides the body-itself arm, and the `takeWhile` bridge
  supplies the `j1` the arm's memory names;
* `%cmp9` (the call's answer) is the expander's own word, which the clause gives
  (`escapeExpand8_decoded`/`_refused`).

So the assembly is **four bit derivations and a composition**, and the composition is
the part the module already has: entry prefix, seat, `s2StringBodyScan_run`, the
`Exited` split, and the arm-correct join.  It is the control flow's correspondence
that was new, and it is the same kind of work as the bridge: a semantic link between
the model's `Nat` data and the body's `i1` tests.  The closing at the end of this
module is that composition, and the four derivations are its `hbit1`, the arms' own
branch bits, `hbit7` and `hbit9`. -/

/- **The contract's prerequisite, now proved.**  The planning estimate was that
`s2StringBodyBody_contract` would assemble seat, run, split and joins — "no crossings,
so the smallest unit" — and a check of this cone said otherwise: the scan's
characterization was missing.  The model's `j1` is
`j0 + ((ps.drop j0).takeWhile (fun q => q < pos0)).length`, while the loop's exit word
gives a counter `c` with `s2StringBodyScanAtBound`'s disjunction at it.  That bridge is
`scanCounter_eq_takeWhile` below, from `takeWhile_length_of_counter`: **a counter whose
every position below it satisfies the predicate, and whose own position does not (or is
past the list), is the `takeWhile` length.**  It is a three-lemma development, not an
assembly step — which is why "no crossings" was the wrong dimension to count, and the
mistake was mine. -/

/-- The cursor word the scan leaves is the model's `j1`: the exit word's counter,
written at the caller's cursor, is the memory the model's `j1` names.  This is where
`ExitWord`'s `∃ c` is consumed — at the memory term, not at the exits. -/
theorem s2StringBodyMemory_cursor {mem0 : Mem} {xj c : Nat} {e : State}
    (h : e.mem = writeBytes mem0 xj (wordBytes 8 c)) :
    writeBytes mem0 xj (wordBytes 8 c) = e.mem := h.symm


end LeanLLVM.Refinement
