/-
The step corpus of the stage-1 mask unit's emitted body, at its measured shape.

`JsonS1MasksIR` holds the fixture, `s1Calls`, the block's lane vocabulary, the
generic `evalInstr_*` lemmas and the lane-to-word bridge.  This module holds the
body's execution: each instruction's step, and the composition that chains them.

## Why the shape is what it is

A step is stated at an **opaque environment** — `withEnv env s`, with the operands
it reads as *hypotheses* — and the composition conses onto a chain that ends in a
variable `env`.  No goal therefore contains a nested `State.bind`, so a lookup is a
head test plus a skip bounded by the instructions since the register was bound,
never a walk down a state chain.

That is not a preference.  Measured, same machine and session, `nix develop -c lake
env lean`, at a fixed `maxHeartbeats 400000`:

* two steps plus their composition elaborate under **20 000** heartbeats — 20×
  inside the budget the `State.bind`-chain shape timed out at;
* **six** steps with five compositions cost **1.60 s** against **1.59 s** for two,
  at the same budget: linear in instructions and independent of depth;
* the same first step stated at the chain shape never completed, at 400k or at 1M.

`s1_chain6` is the shape's own witness: six copies of two of the body's
instructions, deliberately *not* a prefix of the body, kept so the linearity claim
stays checkable rather than remembered.

## Three measured facts to inherit rather than re-derive

* **`BitVec.toNat_shiftLeft` carries the modulus**: `(x <<< n).toNat = x.toNat <<< n % 2 ^ v`.
  The shift the join needs is discharged by `lanesToNat_lt`: `Lhi * 2 ^ 32 < 2 ^ 64`, so the
  modulus is a no-op and `Nat.shiftLeft_eq` + `Nat.mod_eq_of_lt` finish it.
* **The step-scale linearity reproduces**: six steps with five compositions elaborate at
  `maxHeartbeats 20000` in 1.46 s, against 1.59 s for two — the depth-independence claim.
* **Identity scale is a different matter.** `congr` over the `BitVec` chains the words are
  defined from hits a deterministic `whnf` timeout at `maxHeartbeats 800000` — four hundred
  times the step budget. So the identity between a step word (`or14W`) and the specification's
  clean word (`mask64 (pack32 …) (pack32 …)`) is stated at **`toNat` level** and closed by
  `BitVec.toNat_inj` once, not by `congr` over `BitVec`. The steps keep their raw `rfl` forms;
  the reduction lives at this boundary. `Nat.lor_comm` is **not** in this toolchain's core, so
  that route needs either the BitVec-level `BitVec.or_comm` applied *before* `toNat`, or a
  hand-written `Nat.lor` commutativity.

## Which of the two moves a mask needs

The emission computes two different shapes, and which one a mask has decides which
move closes it:

* **The body performs the join** — `%or14.i` is `shl` + `or` over the two halves,
  so the body's own word already has `mask64`'s shape up to operand order.  The
  fix is **one `BitVec.or_comm` on the body's word** (`or14W_comm`), applied before
  any `toNat`; no `Nat.lor` commutativity is needed, which matters because
  `Nat.lor_comm` and `Nat.testBit_lor` are **not** in this toolchain's core.  The
  delimiter and whitespace words are the same shape.
* **The body does not join** — `%or.i` (quote) and `%11` (control) are a single
  sixty-four-lane `icmp` and one `bitcastMask`, so their value is
  `ofNat 64 (lanesToNat …)` with no `|||` in it at all and `…W_comm` has nothing to
  flip.  These need the **packing bridge**: `ofNat 64 (lanesToNat (a ++ b))` against
  `mask64 (ofNat 32 (lanesToNat a)) (ofNat 32 (lanesToNat b))`.

For the bridge, this toolchain has `BitVec.ofNat_or`, `BitVec.ofNat_add`,
`Nat.testBit_add`, `Nat.testBit_two_pow_mul` and `Nat.shiftLeft_eq`, and
`or_ofNat_shift` is exactly the second half of it.  What it does **not** have is the
Nat-level identification `X + 2 ^ 32 * Y = X ||| (Y <<< 32)` (equivalently, a
`Nat.testBit` rule for a sum of disjoint addends) — and the bridge below was closed
without it, over the lane lists (`ofNat_lanesToNat_join`).

## The identities are parametric, so `s1_masks_refines` has no restatement debt

Every mask identity is stated over `k : Ctx` and names a **word**, not a projection:

```lean
theorem s1_backslash_eq (k : Ctx) : (or14W k).toNat = (backslashWord k).toNat
```

`s1_masks_refines` instantiates `k` from its own `(lo, hi, st)` and applies each
identity; none fixes a `Ctx` field, and none is stated at a particular block.  The
six identities are therefore already in the form the terminal theorem consumes.

## Why the later masks are cheaper than the first, and why that will not repeat

The backslash mask took five items — `conv9W_toNat`, `conv12W_toNat`,
`shl13W_toNat`, `or14W_comm` and the identity — while the quote mask needs two.
That drop is **not** because the first mask was done badly.  The first mask paid
for the vocabulary: the `toNat`-level boundary, `or_ofNat_shift`, the packing
bridge, `getElem?_append_left/right` and the `Bool`/`Prop` coercion were all built
there, and it also carried the absence of `Nat.lor_comm`.  The later masks read off
that vocabulary.  A reader seeing "five items, then two" should read it as
*infrastructure, then instances*.

## The gaps here are statement-shaped more often than lemma-shaped

Four items here ended at something absent or awkward in the
toolchain: `Nat.lor_comm`, a `Nat.testBit` rule for sums, `Nat.testBit_two_pow_mul_add`,
and `Bool`/`Prop` coercions under `testBit`.  **Three of the four dissolved by
restating the lemma, not by proving the missing one:**

* `Nat.lor_comm` was never needed once `or14W`'s own operands were flipped, so the
  body's word agreed with `mask64`'s order (`or14W_comm`);
* the `X + 2 ^ 32 * Y = X ||| (Y <<< 32)` sum was never needed once the packing
  bridge was stated over the lane **lists** (`ofNat_lanesToNat_join`);
* the `Bool`/`Prop` coercion was resolved by `Bool.eq_iff_iff.mpr` into `Prop`
  before rewriting with `lanesToNat_testBit`.

So: **try restating before proving.**  The fourth gap — index arithmetic across
`List.getElem?_append` — was bookkeeping, and `getElem?_append_left/right` carry the
subtraction for you.

## Two traps this module exists to avoid

* `simp only [q0…qN, lookupName_bind_ne, …]` **silently does not apply** the
  lemma in that position: the goal stays open and the failure reads as a missing
  lemma.  Do not use it.
* `simp only [q0…qN, State.bind, lookupName]` reaches `maxRecDepth` at about a
  hundred definitions.
* `lookupName_bind_ne` and `lookupName_bind_self` already exist in
  `JsonS1MasksIR`; they are used here, not redefined.

## Migration, completed

`JsonS1MasksIR` used to carry `s1_step0` … `s1_step8` in an older
`State.bind`-chain shape.  This module re-stated the body through step 16
(`%or14.i`), at which point the old steps, their `q0` … `q8` states, their
`s1_peel` macro and the four value abbreviations they used were deleted.  There is
one shape in the tree, and it is the measured one: every value is a step's
consequence, every operand is a hypothesis, and no goal holds a nested state.
-/
import LeanLLVM.Refinement.JsonS1MasksIR
import LeanLLVM.Refinement.QuoteDerive

namespace LeanLLVM.Refinement.JsonS1MasksSteps

open LeanLLVM
open LeanLLVM.JSON (Block32 IsQuoteB IsBackslashB IsSpaceB)
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.BitLanes (pext pdep ctlz)
open LeanLLVM.Refinement.QuoteDerive
open LeanLLVM.Refinement.Pclmul (clmul seedVec specInString64_eq_clmul)

/-- Straight-line composition: an instruction that resolves to a state leaves the
rest of the list to be run from it. -/
theorem denoteCode_cons_of (calls : Calls) (i : Instr) (is : List Instr) (s s' : State)
    (h : evalInstr calls s i = some s')
    (hi : i.isPhi = false := by rfl) :
    denoteCode calls (i :: is) s = denoteCode calls is s' :=
  LeanLLVM.denoteCode_cons_of calls i is s s' h hi

/-- A state seen as its environment: the composition's subject.  Everything a step
does not touch — memory, the allocator cursor, the block, the predecessor — is
carried through unchanged. -/
def withEnv (env : Env) (s : State) : State := { s with env := env }

/-! ### The backslash word's first two steps

The worked pair: an `icmpVec` reading a half's lanes, then the `bitcastMask` that
packs its verdicts into a word.  Its operands are hypotheses, so each proof is a
single unfolding. -/

/-- The low half's backslash lanes: the block's low bytes compared with `\`. -/
def backLo (k : Ctx) : List (BitVec 1) :=
  ((loLanes k).zip (List.replicate 32 (BitVec.ofInt 8 92))).map fun (x, y) => evalICmp .eq x y

/-- The high half's backslash lanes. -/
def backHi (k : Ctx) : List (BitVec 1) :=
  ((hiLanes k).zip (List.replicate 32 (BitVec.ofInt 8 92))).map fun (x, y) => evalICmp .eq x y

theorem backLo_length (k : Ctx) : (backLo k).length = 32 := by
  simp [backLo, loLanes_length]

theorem backHi_length (k : Ctx) : (backHi k).length = 32 := by
  simp [backHi, hiLanes_length]

/-- `%cmp.i54.i = icmp eq <32 x i8> %2, splat (i8 92)`. -/
theorem s1_step9 (env : Env) (s : State) (k : Ctx)
    (h2 : lookupName env "%2" = some (.vec 32 8 (loLanes k))) :
    evalInstr s1Calls (withEnv env s)
        (.icmpVec "%cmp.i54.i" .eq 32 8 (.reg "%2") (splatOf 32 8 92)) =
      some (withEnv (("%cmp.i54.i", .vec 32 1 (backLo k)) :: env) s) := by
  simp only [withEnv, evalInstr, evalOperand, h2, splatOf, Const.toValue, Value.vecLanes,
    loLanes_length, List.length_replicate, and_self, reduceDIte, ite_true, reduceCtorEq,
    State.bind, backLo]

/-- `%7 = bitcast <32 x i1> %cmp.i54.i to i32`. -/
theorem s1_step10 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%cmp.i54.i" = some (.vec 32 1 (backLo k))) :
    evalInstr s1Calls (withEnv env s) (.bitcastMask "%7" 32 (.reg "%cmp.i54.i")) =
      some (withEnv (("%7", .int 32 (BitVec.ofNat 32 (lanesToNat (backLo k)))) :: env) s) := by
  simp only [withEnv, evalInstr, evalOperand, h, backLo_length, and_self, reduceDIte,
    ite_true, State.bind]

/-! ### The shape's witness

Six steps and five compositions, over two of the body's instructions rather than a
prefix of it: what it measures is the composition's cost, not progress through the
body.  Its conclusion is a six-cell environment ending in a variable, which is the
whole of the depth-independence claim. -/

/-- Six compositions of two body instructions: each operand is read through a skip
bounded by the two cells the previous round consed. -/
theorem s1_chain6 (env : Env) (s : State) (k : Ctx)
    (h2 : lookupName env "%2" = some (.vec 32 8 (loLanes k))) :
    denoteCode s1Calls
        [.icmpVec "%cmp.i54.i" .eq 32 8 (.reg "%2") (splatOf 32 8 92),
         .bitcastMask "%7" 32 (.reg "%cmp.i54.i"),
         .icmpVec "%cmp.i54.i" .eq 32 8 (.reg "%2") (splatOf 32 8 92),
         .bitcastMask "%7" 32 (.reg "%cmp.i54.i"),
         .icmpVec "%cmp.i54.i" .eq 32 8 (.reg "%2") (splatOf 32 8 92),
         .bitcastMask "%7" 32 (.reg "%cmp.i54.i")]
        (withEnv env s) =
      some (withEnv (("%7", .int 32 (BitVec.ofNat 32 (lanesToNat (backLo k)))) ::
        ("%cmp.i54.i", .vec 32 1 (backLo k)) ::
        ("%7", .int 32 (BitVec.ofNat 32 (lanesToNat (backLo k)))) ::
        ("%cmp.i54.i", .vec 32 1 (backLo k)) ::
        ("%7", .int 32 (BitVec.ofNat 32 (lanesToNat (backLo k)))) ::
        ("%cmp.i54.i", .vec 32 1 (backLo k)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (s1_step9 env s k h2)]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_step10 _ s k (lookupName_cons_self _ _ _))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_step9 _ s k (by
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), h2]))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_step10 _ s k (lookupName_cons_self _ _ _))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_step9 _ s k (by
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), h2]))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_step10 _ s k (lookupName_cons_self _ _ _))]
  rfl

/-! ### The migration, step by step

The corpus is re-stated here from the body's first instruction.  `JsonS1MasksIR`
keeps the old `State.bind`-chain forms until this module has carried the body through
`%or14.i` (step 16), and they are deleted then — never a red tree in between. -/

/-- `%0 = load <4 x i64>, ptr %p`. -/
theorem s1_load0 (env : Env) (s : State) (k : Ctx)
    (hp : lookupName env "%p" = some (.ptr k.p))
    (hl : readBytes s.mem k.p 32 = some (List.ofFn k.lo)) :
    evalInstr s1Calls (withEnv env s) (.load "%0" (.vec 4 (.int 64)) (.reg "%p")) =
      some (withEnv (("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s) := by
  rw [evalInstr_load (p := .reg "%p") (a := k.p)
    (by simp only [withEnv, evalOperand, hp])
    (loadValue_vec_int (by decide) (by decide) hl)]
  rfl

/-- `%add.ptr = getelementptr i8, ptr %p, i64 32`. -/
theorem s1_ptr (env : Env) (s : State) (k : Ctx)
    (hp : lookupName env "%p" = some (.ptr k.p)) :
    evalInstr s1Calls (withEnv env s) (.gep "%add.ptr" (.int 8) (.reg "%p") (lit 64 32)) =
      some (withEnv (("%add.ptr", .ptr (k.p + 32)) :: env) s) := by
  rw [evalInstr_gep_i8 (base := .reg "%p") (off := lit 64 32) (a := k.p) (w := 64)
    (n := BitVec.ofInt 64 32)
    (hb := by simp only [withEnv, evalOperand, hp])
    (ho := by simp only [withEnv, evalOperand, lit, Const.toValue]) (hpos := by decide)]
  simp only [show (BitVec.signExtend 64 (BitVec.ofInt 64 32)).toNat = 32 from by decide,
    withEnv, State.bind]

/-- `%1 = load <4 x i64>, ptr %add.ptr`, the pair's second load. -/
theorem s1_load1 (env : Env) (s : State) (k : Ctx)
    (hptr : lookupName env "%add.ptr" = some (.ptr (k.p + 32)))
    (hl : readBytes s.mem (k.p + 32) 32 = some (List.ofFn k.hi)) :
    evalInstr s1Calls (withEnv env s) (.load "%1" (.vec 4 (.int 64)) (.reg "%add.ptr")) =
      some (withEnv (("%1", .vec 4 64 (unpackLanes 64 4 (hiWord k))) :: env) s) := by
  rw [evalInstr_load (p := .reg "%add.ptr") (a := k.p + 32)
    (by simp only [withEnv, evalOperand, hptr])
    (loadValue_vec_int (by decide) (by decide) hl)]
  rfl

/-- The first three instructions composed: a bounded skip, then two steps, with no
nested state anywhere. -/
theorem s1_chain3 (env : Env) (s : State) (k : Ctx)
    (hp : lookupName env "%p" = some (.ptr k.p))
    (hl0 : readBytes s.mem k.p 32 = some (List.ofFn k.lo))
    (hl1 : readBytes s.mem (k.p + 32) 32 = some (List.ofFn k.hi)) :
    denoteCode s1Calls
        [.load "%0" (.vec 4 (.int 64)) (.reg "%p"),
         .gep "%add.ptr" (.int 8) (.reg "%p") (lit 64 32),
         .load "%1" (.vec 4 (.int 64)) (.reg "%add.ptr")]
        (withEnv env s) =
      some (withEnv (("%1", .vec 4 64 (unpackLanes 64 4 (hiWord k))) :: ("%add.ptr", .ptr (k.p + 32)) ::
        ("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (s1_load0 env s k hp hl0)]
  rw [denoteCode_cons_of _ _ _ _ _
    (s1_ptr (("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s k
      (by rw [lookupName_cons_ne _ _ (by decide), hp]))]
  rw [denoteCode_cons_of _ _ _ _ _
    (s1_load1 (("%add.ptr", Value.ptr (k.p + 32)) :: ("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s k
      (lookupName_cons_self _ _ _) hl1)]
  rfl


/-! ### The quote word: `%2` … `%or.i`

Each step's operands are hypotheses.  Where a value is a vector, the lane list is
**ascribed at the concrete list** rather than left to inference: `vecLanes_self`
fixes nothing in the expected type, so an un-ascribed use leaves a metavariable. -/

/-- `%2 = bitcast <4 x i64> %0 to <32 x i8>`. -/
theorem s1_bitcast2 (env : Env) (s : State) (k : Ctx)
    (h0 : lookupName env "%0" = some (.vec 4 64 (unpackLanes 64 4 (loWord k)))) :
    evalInstr s1Calls (withEnv env s) (.vecBitcast "%2" 4 64 32 8 (.reg "%0")) =
      some (withEnv (("%2", .vec 32 8 (loLanes k)) :: env) s) := by
  rw [evalInstr_vecBitcast (hv := by simp only [withEnv, evalOperand, h0])
    (hl := vecLanes_self (l := unpackLanes 64 4 (loWord k))
      (unpackLanes_length 64 4 (loWord k))) (hwidth := by decide)]
  simp only [withEnv, State.bind]
  congr 1
  simp only [bitcastVecLanes, packLanes_unpackLanes, show (4 * 64 : Nat) = 256 from rfl,
    show loWord k % 2 ^ 256 = loWord k from Nat.mod_eq_of_lt (loWord_lt k)]
  rw [unpackLanes_lo]

/-- `%3 = bitcast <4 x i64> %1 to <32 x i8>`. -/
theorem s1_bitcast3 (env : Env) (s : State) (k : Ctx)
    (h1 : lookupName env "%1" = some (.vec 4 64 (unpackLanes 64 4 (hiWord k)))) :
    evalInstr s1Calls (withEnv env s) (.vecBitcast "%3" 4 64 32 8 (.reg "%1")) =
      some (withEnv (("%3", .vec 32 8 (hiLanes k)) :: env) s) := by
  rw [evalInstr_vecBitcast (hv := by simp only [withEnv, evalOperand, h1])
    (hl := vecLanes_self (l := unpackLanes 64 4 (hiWord k))
      (unpackLanes_length 64 4 (hiWord k))) (hwidth := by decide)]
  simp only [withEnv, State.bind]
  congr 1
  simp only [bitcastVecLanes, packLanes_unpackLanes, show (4 * 64 : Nat) = 256 from rfl,
    show hiWord k % 2 ^ 256 = hiWord k from Nat.mod_eq_of_lt (hiWord_lt k)]
  rw [unpackLanes_hi]

/-- `%4 = shufflevector <4 x i64> %0, <4 x i64> %1, <8 x i32> <0 … 7>`. -/
theorem s1_shuffle4 (env : Env) (s : State) (k : Ctx)
    (h0 : lookupName env "%0" = some (.vec 4 64 (unpackLanes 64 4 (loWord k))))
    (h1 : lookupName env "%1" = some (.vec 4 64 (unpackLanes 64 4 (hiWord k)))) :
    evalInstr s1Calls (withEnv env s)
        (.shuffleVec "%4" 4 64 (.reg "%0") (.reg "%1") [0, 1, 2, 3, 4, 5, 6, 7]) =
      some (withEnv (("%4", .vec 8 64 (unpackLanes 64 4 (loWord k) ++
        unpackLanes 64 4 (hiWord k))) :: env) s) := by
  rw [evalInstr_shuffleVec
    (ha := by simp only [withEnv, evalOperand, h0])
    (hb := by simp only [withEnv, evalOperand, h1])
    (h1 := vecLanes_self (l := unpackLanes 64 4 (loWord k))
      (unpackLanes_length 64 4 (loWord k)))
    (h2 := vecLanes_self (l := unpackLanes 64 4 (hiWord k))
      (unpackLanes_length 64 4 (hiWord k)))
    (hm := mapM_pick8 (unpackLanes_length 64 4 (loWord k))
      (unpackLanes_length 64 4 (hiWord k)))]
  rfl

/-- `%5 = bitcast <8 x i64> %4 to <64 x i8>`. -/
theorem s1_bitcast5 (env : Env) (s : State) (k : Ctx)
    (h4 : lookupName env "%4" = some (.vec 8 64 (unpackLanes 64 4 (loWord k) ++
      unpackLanes 64 4 (hiWord k)))) :
    evalInstr s1Calls (withEnv env s) (.vecBitcast "%5" 8 64 64 8 (.reg "%4")) =
      some (withEnv (("%5", .vec 64 8 (blockLanes k)) :: env) s) := by
  rw [evalInstr_vecBitcast (hv := by simp only [withEnv, evalOperand, h4])
    (hl := vecLanes_self
      (l := unpackLanes 64 4 (loWord k) ++ unpackLanes 64 4 (hiWord k))
      (by simp [unpackLanes_length])) (hwidth := by decide)]
  simp only [withEnv, State.bind, bitcastVecLanes]
  rw [packLanes_join k]

/-- `%6 = icmp eq <64 x i8> %5, splat (i8 34)`. -/
theorem s1_icmp6 (env : Env) (s : State) (k : Ctx)
    (h5 : lookupName env "%5" = some (.vec 64 8 (blockLanes k))) :
    evalInstr s1Calls (withEnv env s)
        (.icmpVec "%6" .eq 64 8 (.reg "%5") (splatOf 64 8 34)) =
      some (withEnv (("%6", .vec 64 1 (quoteLanes k)) :: env) s) := by
  rw [evalInstr_icmpVec
    (ha := by simp only [withEnv, evalOperand, h5])
    (vb := .vec 64 8 (List.replicate 64 (BitVec.ofInt 8 34)))
    (hb := by simp only [withEnv, evalOperand, splatOf, Const.toValue])
    (h1 := vecLanes_self (l := blockLanes k) (blockLanes_length k))
    (h2 := vecLanes_self (l := List.replicate 64 (BitVec.ofInt 8 34))
      (by simp [List.length_replicate]))]
  rfl

/-- `%or.i = bitcast <64 x i1> %6 to i64`: the raw quote word. -/
theorem s1_quote (env : Env) (s : State) (k : Ctx)
    (h6 : lookupName env "%6" = some (.vec 64 1 (quoteLanes k))) :
    evalInstr s1Calls (withEnv env s) (.bitcastMask "%or.i" 64 (.reg "%6")) =
      some (withEnv (("%or.i", .int 64 (BitVec.ofNat 64 (lanesToNat (quoteLanes k)))) ::
        env) s) := by
  rw [evalInstr_bitcastMask (hv := by simp only [withEnv, evalOperand, h6])
    (hlen := quoteLanes_length k)]
  rfl

/-- The body's first nine instructions composed, `%0` through the raw quote word at
`%or.i`: every operand is read through a skip bounded by the registers consed since
it was bound, and no goal holds a nested state. -/
theorem s1_quoteChain (env : Env) (s : State) (k : Ctx)
    (hp : lookupName env "%p" = some (.ptr k.p))
    (hl0 : readBytes s.mem k.p 32 = some (List.ofFn k.lo))
    (hl1 : readBytes s.mem (k.p + 32) 32 = some (List.ofFn k.hi)) :
    denoteCode s1Calls
        [.load "%0" (.vec 4 (.int 64)) (.reg "%p"),
         .gep "%add.ptr" (.int 8) (.reg "%p") (lit 64 32),
         .load "%1" (.vec 4 (.int 64)) (.reg "%add.ptr"),
         .vecBitcast "%2" 4 64 32 8 (.reg "%0"),
         .vecBitcast "%3" 4 64 32 8 (.reg "%1"),
         .shuffleVec "%4" 4 64 (.reg "%0") (.reg "%1") [0, 1, 2, 3, 4, 5, 6, 7],
         .vecBitcast "%5" 8 64 64 8 (.reg "%4"),
         .icmpVec "%6" .eq 64 8 (.reg "%5") (splatOf 64 8 34),
         .bitcastMask "%or.i" 64 (.reg "%6")]
        (withEnv env s) =
      some (withEnv (("%or.i", .int 64 (BitVec.ofNat 64 (lanesToNat (quoteLanes k)))) ::
        ("%6", .vec 64 1 (quoteLanes k)) ::
        ("%5", .vec 64 8 (blockLanes k)) ::
        ("%4", .vec 8 64 (unpackLanes 64 4 (loWord k) ++ unpackLanes 64 4 (hiWord k))) ::
        ("%3", .vec 32 8 (hiLanes k)) ::
        ("%2", .vec 32 8 (loLanes k)) ::
        ("%1", .vec 4 64 (unpackLanes 64 4 (hiWord k))) ::
        ("%add.ptr", .ptr (k.p + 32)) ::
        ("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (s1_load0 env s k hp hl0)]
  rw [denoteCode_cons_of _ _ _ _ _
    (s1_ptr (("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s k
      (by rw [lookupName_cons_ne _ _ (by decide), hp]))]
  rw [denoteCode_cons_of _ _ _ _ _
    (s1_load1 (("%add.ptr", .ptr (k.p + 32)) :: ("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s k (lookupName_cons_self _ _ _) hl1)]
  rw [denoteCode_cons_of _ _ _ _ _
    (s1_bitcast2 (("%1", .vec 4 64 (unpackLanes 64 4 (hiWord k))) :: ("%add.ptr", .ptr (k.p + 32)) :: ("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s k
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_self _ _ _]))]
  rw [denoteCode_cons_of _ _ _ _ _
    (s1_bitcast3 (("%2", .vec 32 8 (loLanes k)) :: ("%1", .vec 4 64 (unpackLanes 64 4 (hiWord k))) :: ("%add.ptr", .ptr (k.p + 32)) :: ("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s k (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self _ _ _]))]
  rw [denoteCode_cons_of _ _ _ _ _
    (s1_shuffle4 (("%3", .vec 32 8 (hiLanes k)) :: ("%2", .vec 32 8 (loLanes k)) :: ("%1", .vec 4 64 (unpackLanes 64 4 (hiWord k))) :: ("%add.ptr", .ptr (k.p + 32)) :: ("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s k
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), lookupName_cons_self _ _ _])
      (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), lookupName_cons_self _ _ _]))]
  rw [denoteCode_cons_of _ _ _ _ _
    (s1_bitcast5 (("%4", .vec 8 64 (unpackLanes 64 4 (loWord k) ++ unpackLanes 64 4 (hiWord k))) :: ("%3", .vec 32 8 (hiLanes k)) :: ("%2", .vec 32 8 (loLanes k)) :: ("%1", .vec 4 64 (unpackLanes 64 4 (hiWord k))) :: ("%add.ptr", .ptr (k.p + 32)) :: ("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s k (lookupName_cons_self _ _ _))]
  rw [denoteCode_cons_of _ _ _ _ _
    (s1_icmp6 (("%5", .vec 64 8 (blockLanes k)) :: ("%4", .vec 8 64 (unpackLanes 64 4 (loWord k) ++ unpackLanes 64 4 (hiWord k))) :: ("%3", .vec 32 8 (hiLanes k)) :: ("%2", .vec 32 8 (loLanes k)) :: ("%1", .vec 4 64 (unpackLanes 64 4 (hiWord k))) :: ("%add.ptr", .ptr (k.p + 32)) :: ("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s k (lookupName_cons_self _ _ _))]
  rw [denoteCode_cons_of _ _ _ _ _
    (s1_quote (("%6", .vec 64 1 (quoteLanes k)) :: ("%5", .vec 64 8 (blockLanes k)) :: ("%4", .vec 8 64 (unpackLanes 64 4 (loWord k) ++ unpackLanes 64 4 (hiWord k))) :: ("%3", .vec 32 8 (hiLanes k)) :: ("%2", .vec 32 8 (loLanes k)) :: ("%1", .vec 4 64 (unpackLanes 64 4 (hiWord k))) :: ("%add.ptr", .ptr (k.p + 32)) :: ("%0", .vec 4 64 (unpackLanes 64 4 (loWord k))) :: env) s k (lookupName_cons_self _ _ _))]
  rfl

/-! ### The backslash word: `%cmp.i54.i` … `%or14.i`

`backLo`/`backHi` are the halves' lanes.  Each value is bound in the exact form
`evalInstr` produces — `ofNat 64 (ofNat 32 L).toNat` for a zero-extended mask — so
a step closes by `rfl`; the reduction `L % 2 ^ 32 = L` is the identity step's
business, not a step's. -/

/-- `%cmp.i54.i = icmp eq <32 x i8> %2, splat (i8 92)`. -/
theorem s1_backLoCmp (env : Env) (s : State) (k : Ctx)
    (h2 : lookupName env "%2" = some (.vec 32 8 (loLanes k))) :
    evalInstr s1Calls (withEnv env s)
        (.icmpVec "%cmp.i54.i" .eq 32 8 (.reg "%2") (splatOf 32 8 92)) =
      some (withEnv (("%cmp.i54.i", .vec 32 1 (backLo k)) :: env) s) :=
  s1_step9 env s k h2

/-- `%7 = bitcast <32 x i1> %cmp.i54.i to i32`. -/
theorem s1_backLoMask (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%cmp.i54.i" = some (.vec 32 1 (backLo k))) :
    evalInstr s1Calls (withEnv env s) (.bitcastMask "%7" 32 (.reg "%cmp.i54.i")) =
      some (withEnv (("%7", .int 32 (BitVec.ofNat 32 (lanesToNat (backLo k)))) :: env) s) :=
  s1_step10 env s k h

/-- `%conv9.i = zext i32 %7 to i64`. -/
theorem s1_zext9 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%7" = some (.int 32 (BitVec.ofNat 32 (lanesToNat (backLo k))))) :
    evalInstr s1Calls (withEnv env s) (.zext "%conv9.i" 32 64 (.reg "%7")) =
      some (withEnv (("%conv9.i",
        .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 (lanesToNat (backLo k))).toNat)) :: env) s) := by
  rw [evalInstr_zext (x := BitVec.ofNat 32 (lanesToNat (backLo k)))
    (hv := by simp only [withEnv, evalOperand, h])]
  rfl

/-- `%cmp.i52.i = icmp eq <32 x i8> %3, splat (i8 92)`. -/
theorem s1_backHiCmp (env : Env) (s : State) (k : Ctx)
    (h3 : lookupName env "%3" = some (.vec 32 8 (hiLanes k))) :
    evalInstr s1Calls (withEnv env s)
        (.icmpVec "%cmp.i52.i" .eq 32 8 (.reg "%3") (splatOf 32 8 92)) =
      some (withEnv (("%cmp.i52.i", .vec 32 1 (backHi k)) :: env) s) := by
  rw [evalInstr_icmpVec
    (ha := by simp only [withEnv, evalOperand, h3])
    (vb := .vec 32 8 (List.replicate 32 (BitVec.ofInt 8 92)))
    (hb := by simp only [withEnv, evalOperand, splatOf, Const.toValue])
    (h1 := vecLanes_self (l := hiLanes k) (hiLanes_length k))
    (h2 := vecLanes_self (l := List.replicate 32 (BitVec.ofInt 8 92))
      (by simp [List.length_replicate]))]
  rfl

/-- `%8 = bitcast <32 x i1> %cmp.i52.i to i32`. -/
theorem s1_backHiMask (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%cmp.i52.i" = some (.vec 32 1 (backHi k))) :
    evalInstr s1Calls (withEnv env s) (.bitcastMask "%8" 32 (.reg "%cmp.i52.i")) =
      some (withEnv (("%8", .int 32 (BitVec.ofNat 32 (lanesToNat (backHi k)))) :: env) s) := by
  rw [evalInstr_bitcastMask (hv := by simp only [withEnv, evalOperand, h])
    (hlen := backHi_length k)]
  rfl

/-- `%conv12.i = zext i32 %8 to i64`. -/
theorem s1_zext12 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%8" = some (.int 32 (BitVec.ofNat 32 (lanesToNat (backHi k))))) :
    evalInstr s1Calls (withEnv env s) (.zext "%conv12.i" 32 64 (.reg "%8")) =
      some (withEnv (("%conv12.i",
        .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 (lanesToNat (backHi k))).toNat)) :: env) s) := by
  rw [evalInstr_zext (x := BitVec.ofNat 32 (lanesToNat (backHi k)))
    (hv := by simp only [withEnv, evalOperand, h])]
  rfl

/-! ### The join: `%shl13.i` and `%or14.i`

The shift's and the or's raw forms nest `toNat` twice, so each is named as a
definition and the step closes by `rfl` against it — no `simp`, whose `Classical`
dependence is what the pin is there to catch.  The reductions these words need
(`ofNat 64 (ofNat 32 L).toNat = ofNat 64 L` by `L < 2 ^ 32`, and the join's own
equality with `mask64`) belong to the identity, not to the steps. -/

/-- `%conv9.i`'s word. -/
def conv9W (k : Ctx) : BitVec 64 :=
  BitVec.ofNat 64 (BitVec.ofNat 32 (lanesToNat (backLo k))).toNat

/-- `%conv12.i`'s word. -/
def conv12W (k : Ctx) : BitVec 64 :=
  BitVec.ofNat 64 (BitVec.ofNat 32 (lanesToNat (backHi k))).toNat

/-- `%shl13.i`'s word: the high half's backslash mask, above the low half. -/
def shl13W (k : Ctx) : BitVec 64 :=
  BitVec.ofNat 64 (conv12W k).toNat <<< (BitVec.ofNat 64 (BitVec.ofInt 64 32).toNat).toNat

/-- `%or14.i`'s word: the two halves joined. -/
def or14W (k : Ctx) : BitVec 64 :=
  BitVec.ofNat 64 (BitVec.ofNat 64 (shl13W k).toNat).toNat |||
    BitVec.ofNat 64 (conv9W k).toNat

/-- `%shl13.i = shl i64 %conv12.i, 32`. -/
theorem s1_shl13 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%conv12.i" = some (.int 64 (conv12W k))) :
    evalInstr s1Calls (withEnv env s) (.binop "%shl13.i" .shl 64 (.reg "%conv12.i") (lit 64 32)) =
      some (withEnv (("%shl13.i", .int 64 (BitVec.ofNat 64 (shl13W k).toNat)) :: env) s) := by
  rw [evalInstr_binop
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (shl13W k).toNat) (hr := rfl)]
  rfl

/-- `%or14.i = or i64 %shl13.i, %conv9.i`: the raw backslash word. -/
theorem s1_or14 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%shl13.i" = some (.int 64 (BitVec.ofNat 64 (shl13W k).toNat)))
    (h9 : lookupName env "%conv9.i" = some (.int 64 (conv9W k))) :
    evalInstr s1Calls (withEnv env s) (.binop "%or14.i" .or 64 (.reg "%shl13.i") (.reg "%conv9.i")) =
      some (withEnv (("%or14.i", .int 64 (BitVec.ofNat 64 (or14W k).toNat)) :: env) s) := by
  rw [evalInstr_binop
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h9])
    (r := (or14W k).toNat) (hr := rfl)]
  rfl

/-! ### The per-byte test behind the backslash lanes

`backLo`/`backHi` compare each byte with `\`.  The comparison is `IsBackslashB`, and
the proof is `decide` over `BitVec 8` — where `decide` enumerates — transported to
`UInt8`, which `decide` does not enumerate.  No rewrite of a `Prop` under `decide`,
so no ill-typed motive. -/

/-- The lane comparison at a byte, over `BitVec 8`. -/
theorem isBackslashB_lane_bv (x : BitVec 8) :
    BitVec.ofBool (BitVec.ofNat 8 x.toNat = BitVec.ofInt 8 92) =
      BitVec.ofBool (IsBackslashB (UInt8.ofNat x.toNat)) := by
  revert x
  decide

/-- The lane comparison at a byte: `ofNat 8 b.toNat` against `ofInt 8 92` is
`IsBackslashB b`. -/
theorem isBackslashB_lane (b : UInt8) :
    BitVec.ofBool (BitVec.ofNat 8 b.toNat = BitVec.ofInt 8 92) =
      BitVec.ofBool (IsBackslashB b) := by
  have h := isBackslashB_lane_bv b.toBitVec
  rw [show b.toBitVec.toNat = b.toNat from rfl] at h
  rw [show UInt8.ofNat b.toNat = b from UInt8.ofNat_toNat] at h
  exact h

/-- `backLo`'s lanes, as the predicate at each of the low half's bytes. -/
theorem backLo_eq (k : Ctx) :
    backLo k = List.ofFn fun i => BitVec.ofBool (IsBackslashB (k.lo i)) := by
  apply List.ext_getElem
  · simp [backLo, loLanes_length]
  · intro j h1 _
    simp only [backLo, loLanes, List.getElem_map, List.getElem_zip, List.getElem_replicate,
      List.getElem_ofFn]
    exact isBackslashB_lane (k.lo ⟨j, by simpa [backLo_length k] using h1⟩)

/-- `backHi`'s lanes, the same one half up. -/
theorem backHi_eq (k : Ctx) :
    backHi k = List.ofFn fun i => BitVec.ofBool (IsBackslashB (k.hi i)) := by
  apply List.ext_getElem
  · simp [backHi, hiLanes_length]
  · intro j h1 _
    simp only [backHi, hiLanes, List.getElem_map, List.getElem_zip, List.getElem_replicate,
      List.getElem_ofFn]
    exact isBackslashB_lane (k.hi ⟨j, by simpa [backHi_length k] using h1⟩)

/-- The low half's lanes pack to that half's backslash word. -/
theorem backLoW_eq (k : Ctx) :
    lanesToNat (backLo k) = (pack32 IsBackslashB k.lo).toNat := by
  rw [backLo_eq, lanesToNat_ofFn_pack32 IsBackslashB k.lo]

/-- The high half's lanes pack to that half's backslash word. -/
theorem backHiW_eq (k : Ctx) :
    lanesToNat (backHi k) = (pack32 IsBackslashB k.hi).toNat := by
  rw [backHi_eq, lanesToNat_ofFn_pack32 IsBackslashB k.hi]

/-- A packed thirty-two-lane word is below `2 ^ 32`. -/
theorem backLo_lt (k : Ctx) : lanesToNat (backLo k) < 2 ^ 32 := by
  have h := lanesToNat_lt (backLo k)
  simpa [backLo_length k] using h

theorem backHi_lt (k : Ctx) : lanesToNat (backHi k) < 2 ^ 32 := by
  have h := lanesToNat_lt (backHi k)
  simpa [backHi_length k] using h

/-- A thirty-two-bit word read back from its own packing. -/
theorem ofNat32_toNat {L : Nat} (h : L < 2 ^ 32) : (BitVec.ofNat 32 L).toNat = L := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-! ### The backslash word's identity

The body's `%or14.i` word is bound in the raw shape `evalInstr` builds; the
specification's word is `backslashWord`.  The bridge is at **`toNat` level**: the
reduction is arithmetic, and the `BitVec` equality is `toNat`-injective once.
Measured, that boundary is forced rather than preferred: `congr` over the `BitVec`
chains the words are defined from hits a deterministic `whnf` timeout at 800,000
heartbeats, while the steps compose at 20,000, so the identity is stated at `toNat`
and closed once by `BitVec.toNat_inj`. -/

/-- A half's word, doubled into the high thirty-two bits, stays below `2 ^ 64`. -/
theorem mul_pow (L : Nat) (h : L < 2 ^ 32) : L * 2 ^ 32 < 2 ^ 64 := by
  calc L * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right h (by decide)
    _ = 2 ^ 64 := by decide

/-- `%conv9.i`'s word, read back: the low half's packed mask. -/
theorem conv9W_toNat (k : Ctx) : (conv9W k).toNat = lanesToNat (backLo k) := by
  rw [conv9W, BitVec.toNat_ofNat, ofNat32_toNat (backLo_lt k),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (backLo_lt k) (by decide : 2 ^ 32 ≤ 2 ^ 64))]

/-- `%conv12.i`'s word, read back. -/
theorem conv12W_toNat (k : Ctx) : (conv12W k).toNat = lanesToNat (backHi k) := by
  rw [conv12W, BitVec.toNat_ofNat, ofNat32_toNat (backHi_lt k),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (backHi_lt k) (by decide : 2 ^ 32 ≤ 2 ^ 64))]

/-- `%shl13.i`'s word: the high half's mask, above the low half.  `toNat_shiftLeft`
carries `% 2 ^ 64`, and `Lhi * 2 ^ 32 < 2 ^ 64` is what discharges it. -/
theorem shl13W_toNat (k : Ctx) : (shl13W k).toNat = lanesToNat (backHi k) * 2 ^ 32 := by
  rw [shl13W, BitVec.toNat_shiftLeft, conv12W_toNat k]
  rw [show (BitVec.ofNat 64 (BitVec.ofInt 64 32).toNat).toNat = 32 from by
    rw [BitVec.toNat_ofNat, show (BitVec.ofInt 64 32).toNat = 32 from by decide,
      Nat.mod_eq_of_lt (by decide)]]
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (backHi_lt k) (by decide : 2 ^ 32 ≤ 2 ^ 64)),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (mul_pow (lanesToNat (backHi k)) (backHi_lt k))]

/-- `%or14.i` in the join's order: the low half first, as `mask64` writes it.  One
`BitVec.or_comm`, applied before any `toNat`. -/
theorem or14W_comm (k : Ctx) :
    or14W k = (BitVec.ofNat 64 (conv9W k).toNat) |||
      (BitVec.ofNat 64 (BitVec.ofNat 64 (shl13W k).toNat).toNat) := by
  unfold or14W
  exact BitVec.or_comm _ _

/-- **The backslash word's identity.**  The body's `%or14.i` word, read as a
natural, is the specification's clean backslash word. -/
theorem s1_backslash_eq (k : Ctx) :
    (or14W k).toNat = (backslashWord k).toNat := by
  have hlt9 : lanesToNat (backLo k) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (backLo_lt k) (by decide : 2 ^ 32 ≤ 2 ^ 64)
  have hlt12 : lanesToNat (backHi k) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (backHi_lt k) (by decide : 2 ^ 32 ≤ 2 ^ 64)
  have hltSh : lanesToNat (backHi k) * 2 ^ 32 < 2 ^ 64 := mul_pow _ (backHi_lt k)
  have hl : (or14W k).toNat = lanesToNat (backLo k) ||| (lanesToNat (backHi k) * 2 ^ 32) := by
    rw [or14W_comm k, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, conv9W_toNat k, shl13W_toNat k, Nat.mod_eq_of_lt hlt9,
      Nat.mod_eq_of_lt hltSh, Nat.mod_eq_of_lt hltSh]
  have hr : (backslashWord k).toNat =
      lanesToNat (backLo k) ||| (lanesToNat (backHi k) * 2 ^ 32) := by
    rw [backslashWord, mask64, BitVec.toNat_or, BitVec.toNat_setWidth,
      BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
      ← backLoW_eq k, ← backHiW_eq k,
      Nat.mod_eq_of_lt hlt12, Nat.mod_eq_of_lt hltSh, Nat.mod_eq_of_lt hlt9]
  rw [hl, hr]

/-! ### The quote mask's per-byte test

The same shape as the backslash one, at `34` instead of `92`: the enumeration is
`decide` over `BitVec 8`, the transport to `UInt8` is two definitional rewrites. -/

/-- The lane comparison at a byte, over `BitVec 8`. -/
theorem isQuoteB_lane_bv (x : BitVec 8) :
    BitVec.ofBool (BitVec.ofNat 8 x.toNat = BitVec.ofInt 8 34) =
      BitVec.ofBool (IsQuoteB (UInt8.ofNat x.toNat)) := by
  revert x
  decide

/-- The lane comparison at a byte: `ofNat 8 b.toNat` against `ofInt 8 34` is
`IsQuoteB b`. -/
theorem isQuoteB_lane (b : UInt8) :
    BitVec.ofBool (BitVec.ofNat 8 b.toNat = BitVec.ofInt 8 34) =
      BitVec.ofBool (IsQuoteB b) := by
  have h := isQuoteB_lane_bv b.toBitVec
  rw [show b.toBitVec.toNat = b.toNat from rfl] at h
  rw [show UInt8.ofNat b.toNat = b from UInt8.ofNat_toNat] at h
  exact h

/-- The propositional form of the per-byte test, over `BitVec 8`.  The mask
identity's lane step needs **`↔ (IsQuoteB b = true)`** — the `= true` is not
decoration: `pack32_getLsbD` yields a `Bool` coerced to `Prop`, so the right-hand
side of the `ofBool_eq_one` instance is `IsQuoteB b = true` and not `(IsQuoteB b)`.
The two differ by the coercion, and the goal names which it wants. -/
theorem isQuoteB_iff_bv (x : BitVec 8) :
    (BitVec.ofNat 8 x.toNat = BitVec.ofInt 8 34) ↔
      (IsQuoteB (UInt8.ofNat x.toNat) = true) := by
  revert x
  decide

/-- The propositional per-byte test at a byte. -/
theorem isQuoteB_iff (b : UInt8) :
    (BitVec.ofNat 8 b.toNat = BitVec.ofInt 8 34) ↔ (IsQuoteB b = true) := by
  have h := isQuoteB_iff_bv b.toBitVec
  rw [show b.toBitVec.toNat = b.toNat from rfl] at h
  rw [show UInt8.ofNat b.toNat = b from UInt8.ofNat_toNat] at h
  exact h

/-! ### The quote word's identity

`%or.i` is a **single sixty-four-lane comparison** — `icmp eq` over the block's
bytes, then one `bitcastMask` — so its word is `ofNat 64 (lanesToNat (quoteLanes k))`
with no join in it.  It therefore takes the **packing bridge**, not `or14W_comm`.

Two placements are load-bearing and are easy to get wrong:
`hgd` must sit **inside** its branch (it needs `hj32`/`¬hj32` for `omega`), and the
`List.getElem?_ofFn` split is a **`dite`**, so it is discharged by `dif_pos`, not
`ite_eq_left`.  The `List.getElem?_append` split in `hgd` is a plain `ite` and takes
`ite_eq_left`/`ite_eq_right`. -/

/-- **The quote word's identity.**  The body's `%or.i`, read as a natural, is the
specification's `IsQuoteB` mask. -/
theorem s1_quote_eq (k : Ctx) :
    BitVec.ofNat 64 (lanesToNat (quoteLanes k)) = specMask64 IsQuoteB k.lo k.hi := by
  rw [specMask64]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and]
  have hq : (quoteLanes k)[j]? = some (evalICmp .eq ((blockLanes k).getD j 0)
      (BitVec.ofInt 8 34)) := by
    simp only [quoteLanes]
    exact zipReplicate_getElem? (blockLanes k) (BitVec.ofInt 8 34)
      (fun x y => evalICmp .eq x y) (blockLanes_length k) hj
  by_cases hj32 : j < 32
  · have hgd : (blockLanes k).getD j 0 = (loLanes k).getD j 0 := by
      simp only [blockLanes, List.getD, List.getElem?_append, loLanes_length]
      rw [ite_eq_left (by omega : j < 32)]
    rw [mask64_getLsbD_lo _ _ hj32, pack32_getLsbD IsQuoteB k.lo ⟨j, hj32⟩]
    apply Bool.eq_iff_iff.mpr
    rw [lanesToNat_testBit, hq, Option.some.injEq]
    simp only [evalICmp]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.ofBool_eq_one
      (p := ((blockLanes k).getD j 0 = BitVec.ofInt 8 34)), hgd]
    simp only [loLanes, List.getD, List.getElem?_ofFn, Option.getD_some,
      dif_pos (by omega : j < 32)]
    exact isQuoteB_iff _
  · have hgd : (blockLanes k).getD j 0 = (hiLanes k).getD (j - 32) 0 := by
      simp only [blockLanes, List.getD, List.getElem?_append, loLanes_length]
      rw [ite_eq_right (by omega : ¬ j < 32)]
    rw [show j = (j - 32) + 32 from by omega, mask64_getLsbD_hi _ _ (by omega),
      pack32_getLsbD IsQuoteB k.hi ⟨j - 32, by omega⟩]
    apply Bool.eq_iff_iff.mpr
    rw [lanesToNat_testBit, show (j - 32) + 32 = j from by omega, hq, Option.some.injEq]
    simp only [evalICmp]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.ofBool_eq_one
      (p := ((blockLanes k).getD j 0 = BitVec.ofInt 8 34)), hgd]
    simp only [hiLanes, List.getD, List.getElem?_ofFn, Option.getD_some,
      dif_pos (by omega : j - 32 < 32)]
    exact isQuoteB_iff _

/-! ### The control word's identity

`%11 = icmp ult <64 x i8> %10, splat 32` — the emission's `_mm256_min_epu8` fold —
and the fixture stores it as `store <64 x i1> %11, ptr %ctl3`
(`json-s1-masks.candidate.ll:148`).  So its word is a **sixty-four-lane vector**
like the quote word's, not a two-half join, and it takes the **same packing bridge**.

The one difference from quote is the comparison: `ult` hands `ofBool` a `Bool`, not a
`Prop`, so the lane step uses `ofBool_eq_one_bool` rather than `ofBool_eq_one`, and
the per-byte fact is `isControlB_iff` (`b ≤ 0x1F`) rather than `isQuoteB_iff`
(`b = 0x22`). -/

/-- The control per-byte test, over `BitVec 8`. -/
theorem isControlB_iff_bv (x : BitVec 8) :
    BitVec.ult (BitVec.ofNat 8 x.toNat) (BitVec.ofInt 8 32) ↔
      (IsControlB (UInt8.ofNat x.toNat) = true) := by
  revert x
  decide

/-- The control per-byte test at a byte. -/
theorem isControlB_iff (b : UInt8) :
    BitVec.ult (BitVec.ofNat 8 b.toNat) (BitVec.ofInt 8 32) ↔ (IsControlB b = true) := by
  have h := isControlB_iff_bv b.toBitVec
  rw [show b.toBitVec.toNat = b.toNat from rfl] at h
  rw [show UInt8.ofNat b.toNat = b from UInt8.ofNat_toNat] at h
  exact h

/-- **The control word's identity.**  The body's `%11`, packed, is the
specification's `IsControlB` mask. -/
theorem s1_control_eq (k : Ctx) :
    BitVec.ofNat 64 (lanesToNat (controlLanes k)) = specMask64 IsControlB k.lo k.hi := by
  rw [specMask64]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and]
  have hq : (controlLanes k)[j]? = some (evalICmp .ult ((blockLanes k).getD j 0)
      (BitVec.ofInt 8 32)) := by
    simp only [controlLanes]
    exact zipReplicate_getElem? (blockLanes k) (BitVec.ofInt 8 32)
      (fun x y => evalICmp .ult x y) (blockLanes_length k) hj
  by_cases hj32 : j < 32
  · have hgd : (blockLanes k).getD j 0 = (loLanes k).getD j 0 := by
      simp only [blockLanes, List.getD, List.getElem?_append, loLanes_length]
      rw [ite_eq_left (by omega : j < 32)]
    rw [mask64_getLsbD_lo _ _ hj32, pack32_getLsbD IsControlB k.lo ⟨j, hj32⟩]
    apply Bool.eq_iff_iff.mpr
    rw [lanesToNat_testBit, hq, Option.some.injEq]
    simp only [evalICmp]
    rw [ofBool_eq_one_bool (((blockLanes k).getD j 0).ult (BitVec.ofInt 8 32)), hgd]
    simp only [loLanes, List.getD, List.getElem?_ofFn, Option.getD_some,
      dif_pos (by omega : j < 32)]
    exact isControlB_iff _
  · have hgd : (blockLanes k).getD j 0 = (hiLanes k).getD (j - 32) 0 := by
      simp only [blockLanes, List.getD, List.getElem?_append, loLanes_length]
      rw [ite_eq_right (by omega : ¬ j < 32)]
    rw [show j = (j - 32) + 32 from by omega, mask64_getLsbD_hi _ _ (by omega),
      pack32_getLsbD IsControlB k.hi ⟨j - 32, by omega⟩]
    apply Bool.eq_iff_iff.mpr
    rw [lanesToNat_testBit, show (j - 32) + 32 = j from by omega, hq, Option.some.injEq]
    simp only [evalICmp]
    rw [ofBool_eq_one_bool (((blockLanes k).getD j 0).ult (BitVec.ofInt 8 32)), hgd]
    simp only [hiLanes, List.getD, List.getElem?_ofFn, Option.getD_some,
      dif_pos (by omega : j - 32 < 32)]
    exact isControlB_iff _

/-! ### The two-nibble arithmetic: `%12` … `%17`

Each half's structural and whitespace words come from the table path: the byte's low
nibble indexes `s1f_lo_tab`, its high nibble indexes `s1f_hi_tab`, and the two entries
are `&&`ed.  The high nibble is built by the shift the emission writes —
`bitcast <4 x i64> %2 to <16 x i16>`, `lshr <16 x i16> …, 4`, `bitcast … to
<32 x i8>`, `&& 0x0F` — so the lane statement is arithmetic and names no predicate:

lane `i` of `%17` is `ofNat 8 ((V / 2 ^ (8 * i + 4)) % 16)`,

the byte's high nibble.  A predicate first enters at `tabAnd_delim`/`tabAnd_space`,
and the two masks are instances of that.

Two facts the chain needs, and neither is vocabulary:

* the shift is **per sixteen-bit lane**, so the division steps one lane at a time and
  the byte lanes are the `bitcast` reassembly — `bitcastVecLanes_unpackLanes`'s
  `unpackLanes 8 32 (packLanes …)` at two element widths.  Reducing that to
  `V / 2 ^ (8 * i + 4)` is `Nat` arithmetic: `Nat.div_div_eq_div_mul` for the shift's
  own division, `Nat.mod_mul_right_div_self` for the sixteen-bit truncation, and
  `Nat.mod_mod_of_dvd` for the `&& 0x0F`.
* `&&& 0x0F` on a byte is `% 16`, which is `decide` over `BitVec 8` — this file's
  existing idiom for a per-byte fact (`tabAnd_delim_bv`, `and15_eq_mod`).

The lane count `k < 16` in the lane-shift lemma is not decoration: the word is sixteen
`i16` lanes, and the composed division `V / 2 ^ (16 * k + 4)` is the statement's own
sub-goal, so a lane index past the half's sixteen would state something about a lane
the shift never produced. -/

/-- A lane of an `unpackLanes`, as the word it is cut from. -/
theorem unpackLanes_getElem {w n v i : Nat} (hi : i < n) :
    (unpackLanes w n v)[i]'(by rw [unpackLanes_length]; exact hi)
      = BitVec.ofNat w (v / 2 ^ (i * w)) := by
  simp [unpackLanes, List.getElem_range]

/-- The same lane, read as a natural: the cut is truncated to the lane width. -/
theorem unpackLanes_getElem_toNat {w n v i : Nat} (hi : i < n) :
    ((unpackLanes w n v)[i]'(by rw [unpackLanes_length]; exact hi)).toNat
      = (v / 2 ^ (i * w)) % 2 ^ w := by
  rw [unpackLanes_getElem hi, BitVec.toNat_ofNat]

/-- A three-term rotation, so a reordering needs no arithmetic decision procedure. -/
theorem add_rotate (a b c : Nat) : (a + b) + c = (b + c) + a := by
  rw [Nat.add_assoc, Nat.add_comm a (b + c)]

/-- **A modulus's own factor divides out.**  `(A % (n * k)) / n` is `(A / n) % k`, for
positive `n` and `k`.

`Nat.mod_mul_right_div_self` states exactly this and carries `Classical.choice`, which
is past the standard axiom footprint, so the identity is derived here from
`Nat.mod_add_div`, `Nat.add_mul_mod_self_left`, `Nat.add_mul_div_left`,
`Nat.mod_eq_of_lt` and `Nat.div_eq_of_lt`, all of which are `[propext]` or narrower.
The decomposition avoids rewriting `A` under a `/` or `%`: the quotient's own split is
transported by `congrArg`, never by `rw` on the goal. -/
theorem mod_mul_div (A n k : Nat) (hn : 0 < n) (hk : 0 < k) :
    (A % (n * k)) / n = (A / n) % k := by
  have hr : A % n < n := Nat.mod_lt _ hn
  have hr' : A / n % k < k := Nat.mod_lt _ hk
  have hq : A / n = k * (A / n / k) + A / n % k := by
    rw [Nat.add_comm]; exact (Nat.mod_add_div (A / n) k).symm
  have hnq : n * (A / n) = (n * k) * (A / n / k) + n * (A / n % k) := by
    have h := congrArg (fun z => n * z) hq
    rw [Nat.mul_add, ← Nat.mul_assoc] at h
    exact h
  have h1 : A = n * (A / n) + A % n := by
    rw [Nat.add_comm]; exact (Nat.mod_add_div A n).symm
  have h2 : n * (A / n) + A % n
      = (n * (A / n % k) + A % n) + (n * k) * (A / n / k) := by
    rw [hnq]
    exact add_rotate _ _ _
  have hA : A = (n * (A / n % k) + A % n) + (n * k) * (A / n / k) := by
    calc A = n * (A / n) + A % n := h1
      _ = (n * (A / n % k) + A % n) + (n * k) * (A / n / k) := h2
  have hlt : n * (A / n % k) + A % n < n * k := by
    have h3 : n * (A / n % k) ≤ n * (k - 1) := Nat.mul_le_mul_left n (by omega)
    have hk' : n * (k - 1) + n = n * k := by
      rw [← Nat.mul_succ]; congr 1; omega
    calc n * (A / n % k) + A % n ≤ n * (k - 1) + A % n := Nat.add_le_add_right h3 _
      _ < n * (k - 1) + n := Nat.add_lt_add_left hr _
      _ = n * k := hk'
  have hmod : A % (n * k) = n * (A / n % k) + A % n := by
    have hconv : A % (n * k)
        = ((n * (A / n % k) + A % n) + (n * k) * (A / n / k)) % (n * k) :=
      congrArg (fun z => z % (n * k)) hA
    rw [hconv, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hlt
  have hfin : (n * (A / n % k) + A % n) / n = A / n % k := by
    rw [Nat.add_comm (n * (A / n % k)) (A % n),
      Nat.add_mul_div_left (A % n) (A / n % k) hn,
      Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [hmod, hfin]

/-- The sixteen-bit lane's own truncation: `(A % 2 ^ 16) / 16` is `(A / 16) % 2 ^ 12`,
so a shift by four and a cut to the low twelve bits are the same operation.

`Nat.mod_mul_right_div_self` states this in one step and carries `Classical.choice`,
which is past the standard axiom footprint; so the identity is derived here instead
from `Nat.mod_add_div`, `Nat.add_mul_mod_self_left`, `Nat.add_mul_div_left`,
`Nat.mod_eq_of_lt` and `Nat.div_eq_of_lt`, all of which are `[propext]`.
The decomposition is the one that avoids rewriting `A` under a `/` or `%`: the
quotient's own split is transported by `congrArg`, never by `rw` on the goal. -/
theorem mod_pow16_div16 (A : Nat) : (A % 2 ^ 16) / 16 = (A / 16) % 2 ^ 12 := by
  have h : (16 : Nat) * 2 ^ 12 = 2 ^ 16 := by decide
  rw [← h]
  exact mod_mul_div A 16 (2 ^ 12) (by decide) (by decide)

/-- **Lane `k` of the `i16` shift.**  With `k < 16` — the lane count of the half's
sixteen-bit view — lane `k` of `lshr <16 x i16> … 4` is the word's bits from
`16 * k + 4` up, cut to twelve. -/
theorem lane_shr4 (V : Nat) (k : Nat) (hk : k < 16) :
    (((unpackLanes 16 16 V)[k]'(by rw [unpackLanes_length]; exact hk)) >>> 4).toNat
      = (V / 2 ^ (16 * k + 4)) % 2 ^ 12 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, unpackLanes_getElem_toNat hk]
  have hp : (2 : Nat) ^ (k * 16) * 16 = 2 ^ (16 * k + 4) := by
    rw [show (2 : Nat) ^ (k * 16) * 16 = 2 ^ (k * 16) * 2 ^ 4 from by
      rw [show (16 : Nat) = 2 ^ 4 from by decide]]
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [mod_pow16_div16, Nat.div_div_eq_div_mul, hp]

/-- The lane list `%13` binds: each sixteen-bit lane of the word, shifted right four.
`BitVec.ushiftRight` is the `>>>` the semantics' `.lshr` reaches, so the list is the
step's value and not a restatement of it. -/
def shr4Lanes (V : Nat) : List (BitVec 16) :=
  (unpackLanes 16 16 V).map fun (x : BitVec 16) => x >>> 4

theorem shr4Lanes_length (V : Nat) : (shr4Lanes V).length = 16 := by
  simp [shr4Lanes, unpackLanes_length]

/-- Lane `k` of the shifted list, at the index `packLanes_div` reads. -/
theorem shr4Lanes_getD (V k : Nat) (hk : k < 16) :
    (((shr4Lanes V)[k]?).map BitVec.toNat).getD 0 = (V / 2 ^ (16 * k + 4)) % 2 ^ 12 := by
  have hlen : k < (shr4Lanes V).length := by
    rw [shr4Lanes, List.length_map, unpackLanes_length]
    exact hk
  rw [List.getElem?_eq_getElem hlen, Option.map_some, Option.getD_some]
  have hval : ((shr4Lanes V)[k]'hlen)
      = ((unpackLanes 16 16 V)[k]'(by rw [unpackLanes_length]; exact hk)) >>> 4 := by
    simp [shr4Lanes, List.getElem_map]
  rw [hval]
  exact lane_shr4 V k hk

/-- The packed word's bits from `16 * k` up, in the even-byte position: the shifted
lane's low twelve bits survive the `&& 0x0F`, and the nibble is the lane's own. -/
theorem shr4_mod_even (V k : Nat) (hk : k < 16) :
    (packLanes (shr4Lanes V) / 2 ^ (k * 16)) % 16 = (V / 2 ^ (k * 16 + 4)) % 16 := by
  rw [packLanes_div (shr4Lanes V) k, shr4Lanes_getD V k hk,
    show (16 * k + 4) = k * 16 + 4 from by omega,
    show (2 : Nat) ^ 16 * packLanes ((shr4Lanes V).drop (k + 1))
        = 16 * (2 ^ 12 * packLanes ((shr4Lanes V).drop (k + 1))) from by
      rw [show (2 : Nat) ^ 16 = 16 * 2 ^ 12 from by decide, Nat.mul_assoc],
    Nat.add_mul_mod_self_left, Nat.mod_mod_of_dvd _ ⟨256, by decide⟩]

/-- The same lane's high half, at `16 * k + 8`: the odd byte's nibble is the lane's
bits four past its own.  `Nat.add_mul_div_left` is what carries the `2 ^ 16` above the
divisor, so the dropped high nibble of the lane never reaches the result. -/
theorem shr4_mod_odd (V k : Nat) (hk : k < 16) :
    (packLanes (shr4Lanes V) / 2 ^ (k * 16 + 8)) % 16 = (V / 2 ^ (k * 16 + 12)) % 16 := by
  rw [show (2 : Nat) ^ (k * 16 + 8) = 2 ^ (k * 16) * 2 ^ 8 from by rw [← Nat.pow_add]]
  rw [← Nat.div_div_eq_div_mul]
  rw [packLanes_div (shr4Lanes V) k, shr4Lanes_getD V k hk,
    show (16 * k + 4) = k * 16 + 4 from by omega]
  rw [show (2 : Nat) ^ 16 * packLanes ((shr4Lanes V).drop (k + 1))
      = 256 * (256 * packLanes ((shr4Lanes V).drop (k + 1))) from by
    rw [show (2 : Nat) ^ 16 = 256 * 256 from by decide, Nat.mul_assoc]]
  rw [Nat.add_mul_div_left _ _ (by decide)]
  rw [show (2 : Nat) ^ 8 * packLanes ((shr4Lanes V).drop (k + 1))
      = 16 * (16 * packLanes ((shr4Lanes V).drop (k + 1))) from by
    rw [show (2 : Nat) ^ 8 = 16 * 16 from by decide, Nat.mul_assoc]]
  rw [Nat.add_mul_mod_self_left]
  rw [show (2 : Nat) ^ 12 = 256 * 16 from by decide]
  rw [mod_mul_div _ 256 16 (by decide) (by decide),
    Nat.mod_mod_of_dvd _ (Nat.dvd_refl 16)]
  rw [show (256 : Nat) = 2 ^ 8 from by decide]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- **Byte `i` of the packed shift is the high nibble of byte `i`.**  The two cases are
the byte's two nibbles inside one sixteen-bit lane; `i % 2` selects which. -/
theorem packLanes_shr4_mod (V i : Nat) (hi : i < 32) :
    (packLanes (shr4Lanes V) / 2 ^ (8 * i)) % 16 = (V / 2 ^ (8 * i + 4)) % 16 := by
  have hk : i / 2 < 16 := by omega
  rcases (show i % 2 = 0 ∨ i % 2 = 1 by omega) with h | h
  · have h8 : 8 * i = i / 2 * 16 := by omega
    rw [h8]
    exact shr4_mod_even V (i / 2) hk
  · have h8 : 8 * i = i / 2 * 16 + 8 := by omega
    rw [h8]
    exact shr4_mod_odd V (i / 2) hk

/-- `&&& 0x0F` on a byte is `% 16`, enumerated over `BitVec 8` like the table facts. -/
theorem and15_eq_mod (x : BitVec 8) :
    x &&& (0x0F : BitVec 8) = BitVec.ofNat 8 (x.toNat % 16) := by
  revert x
  decide

/-- The high-nibble lanes of a half, in the form the second table reads them. -/
def hiNibbleLanes (V : Nat) : List (BitVec 8) :=
  List.ofFn fun i : Fin 32 => BitVec.ofNat 8 ((V / 2 ^ (8 * i.val + 4)) % 16)

theorem hiNibbleLanes_length (V : Nat) : (hiNibbleLanes V).length = 32 := by
  simp [hiNibbleLanes]

/-- **`%17`'s lanes are the high nibbles.**  The reassembly is
`bitcastVecLanes_unpackLanes`'s `unpackLanes 8 32 (packLanes …)`; the per-lane
reduction is `packLanes_shr4_mod` and `and15_eq_mod`. -/
theorem nibbleLanes_eq (V : Nat) :
    (unpackLanes 8 32 (packLanes (shr4Lanes V))).map (fun x => x &&& 0x0F)
      = hiNibbleLanes V := by
  apply List.ext_getElem
  · simp [hiNibbleLanes, unpackLanes_length]
  · intro i h1 h2
    have hi : i < 32 := by simpa [unpackLanes_length] using h1
    simp only [List.getElem_map, hiNibbleLanes, List.getElem_ofFn]
    rw [unpackLanes_getElem hi, and15_eq_mod, BitVec.toNat_ofNat,
      Nat.mod_mod_of_dvd _ ⟨16, by decide⟩,
      show i * 8 = 8 * i from by omega, packLanes_shr4_mod V i hi]

/-! ### The table region's vocabulary

The eleven instructions from `%12` to `%not.i.i.i` are the low half's structural and
whitespace words, and `%22` to `%not.i8.i.i` are the same eleven for the high half:
the emission writes them twice, and the two differ only in which half's word and
which half's byte lanes they read.  So each step below is stated once, over the
half's two views — the `i16` word the shift reads (`V`) and the byte lane list the
low-nibble table reads (`l`) — and the composition instantiates it twice.  The
register names are parameters for the same reason: `dst` and `r` are the emission's
`%12`/`%0` in one instance and `%22`/`%1` in the other, and a step that fixed them
would have to be written twice with no second content.

The values name lists rather than words, matching `evalInstr_binopVec`'s output, so
the table identity's per-lane reading and the step agree by construction. -/

/-- The low nibble of each byte lane. -/
def nibLanes (l : List (BitVec 8)) : List (BitVec 8) :=
  l.map fun x => x &&& (BitVec.ofInt 8 15)

/-- `s1f_lo_tab` as a lane list, written twice as the emission spells it. -/
def loTabV : List (BitVec 8) := loTab16 ++ loTab16

/-- `s1f_hi_tab` as a lane list, written twice. -/
def hiTabV : List (BitVec 8) := hiTab16 ++ hiTab16

/-- The two tables the emission's `lanesOf` constant spells are those lane lists. -/
theorem loTabV_eq : loTab.map (BitVec.ofInt 8) = loTabV := by decide
theorem hiTabV_eq : hiTab.map (BitVec.ofInt 8) = hiTabV := by decide

/-- The `&&` of two table lookups, lane by lane. -/
def andLanes (a b : List (BitVec 8)) : List (BitVec 8) :=
  a.zip b |>.map fun p => p.1 &&& p.2

/-- `%19`'s lanes: the table pair's structural bits only. -/
def sLanes (l : List (BitVec 8)) : List (BitVec 8) :=
  l.map fun x => x &&& (BitVec.ofInt 8 63)

/-- `%cmp.i25.i.i.i`'s lanes: zero exactly where the structural bits are clear. -/
def eq0Lanes (l : List (BitVec 8)) : List (BitVec 1) :=
  (l.zip (List.replicate 32 (BitVec.ofInt 8 0))).map fun p => evalICmp .eq p.1 p.2

/-- `%cmp.i.i.i.i`'s lanes: the whitespace bits are the top two, so the predicate is
an unsigned comparison against sixty-four rather than a masked equality. -/
def ult64Lanes (l : List (BitVec 8)) : List (BitVec 1) :=
  (l.zip (List.replicate 32 (BitVec.ofInt 8 64))).map fun p => evalICmp .ult p.1 p.2

/-- The complement step's word: `xor i32 …, -1`, in the shape `evalInstr_binop`
leaves it. -/
def complW (x : BitVec 32) : BitVec 32 :=
  (BitVec.ofNat 32 x.toNat) ^^^ (BitVec.ofNat 32 (BitVec.ofInt 32 (-1)).toNat)

/-! ### The eleven steps of one half's table region -/

/-- `%12 = bitcast <4 x i64> %0 to <16 x i16>`. -/
theorem s1_bitcastHalf (env : Env) (s : State) (r dst : String) (V : Nat)
    (hV : V < 2 ^ 256)
    (h : lookupName env r = some (.vec 4 64 (unpackLanes 64 4 V))) :
    evalInstr s1Calls (withEnv env s) (.vecBitcast dst 4 64 16 16 (.reg r)) =
      some (withEnv ((dst, .vec 16 16 (unpackLanes 16 16 V)) :: env) s) := by
  rw [evalInstr_vecBitcast (hv := by simp only [withEnv, evalOperand, h])
    (hl := vecLanes_self (unpackLanes_length 64 4 V)) (hwidth := by decide)]
  simp only [withEnv, State.bind]
  congr 1
  simp only [bitcastVecLanes, packLanes_unpackLanes, show (4 * 64 : Nat) = 256 from rfl,
    Nat.mod_eq_of_lt hV]

/-- `%13 = lshr <16 x i16> %12, splat (i16 4)`. -/
theorem s1_shr4 (env : Env) (s : State) (r dst : String) (V : Nat)
    (h : lookupName env r = some (.vec 16 16 (unpackLanes 16 16 V))) :
    evalInstr s1Calls (withEnv env s) (.binopVec dst .lshr 16 16 (.reg r) (splatOf 16 16 4)) =
      some (withEnv ((dst, .vec 16 16 (shr4Lanes V)) :: env) s) := by
  have h4 : (BitVec.ofInt 16 4).toNat = 4 := by decide
  have hm : ((unpackLanes 16 16 V).zip (List.replicate 16 (BitVec.ofInt 16 4))).mapM
        (fun p => evalBinop .lshr p.1 p.2) = some (shr4Lanes V) := by
    have h' := zipReplicate_mapM (unpackLanes 16 16 V) (BitVec.ofInt 16 4)
      (fun x y => evalBinop .lshr x y) (fun x => x >>> 4)
      (fun x => by simp [evalBinop, h4])
    rw [unpackLanes_length] at h'
    simpa [shr4Lanes] using h'
  rw [evalInstr_binopVec (l1 := unpackLanes 16 16 V)
    (l2 := List.replicate 16 (BitVec.ofInt 16 4)) (ls := shr4Lanes V)
    (h1 := by rw [unpackLanes_length]) (h2 := by simp [List.length_replicate])
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, splatOf, Const.toValue]) hm]
  simp only [withEnv, State.bind]

/-- `%14 = and <32 x i8> %2, splat (i8 15)`: the low nibbles. -/
theorem s1_andNib (env : Env) (s : State) (r dst : String) (l : List (BitVec 8))
    (hl : l.length = 32) (h : lookupName env r = some (.vec 32 8 l)) :
    evalInstr s1Calls (withEnv env s) (.binopVec dst .and 32 8 (.reg r) (splatOf 32 8 15)) =
      some (withEnv ((dst, .vec 32 8 (nibLanes l)) :: env) s) := by
  have hm : (l.zip (List.replicate 32 (BitVec.ofInt 8 15))).mapM
      (fun p => evalBinop .and p.1 p.2) = some (nibLanes l) := by
    have h' := zipReplicate_mapM l (BitVec.ofInt 8 15) (fun x y => evalBinop .and x y)
      (fun x => x &&& (BitVec.ofInt 8 15)) (fun x => rfl)
    rw [hl] at h'
    simpa [nibLanes] using h'
  rw [evalInstr_binopVec (l1 := l) (l2 := List.replicate 32 (BitVec.ofInt 8 15))
    (ls := nibLanes l) (h1 := hl) (h2 := by simp [List.length_replicate])
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, splatOf, Const.toValue]) hm]
  simp only [withEnv, State.bind]

/-- `%15 = call @llvm.x86.avx2.pshuf.b`: the table lookup, at the two-argument
declaration the parser admits. -/
theorem s1_pshufb (env : Env) (s : State) (r dst : String) (tabInt : List Int)
    (tab ctl : List (BitVec 8)) (htabLen : tabInt.length = 32)
    (htab : tabInt.map (BitVec.ofInt 8) = tab)
    (h : lookupName env r = some (.vec 32 8 ctl)) :
    evalInstr s1Calls (withEnv env s)
        (.call dst v32i8 "llvm.x86.avx2.pshuf.b"
          [(v32i8, lanesOf 8 tabInt), (v32i8, .reg r)]) =
      some (withEnv ((dst, .vec 32 8 (pshufbLanes tab ctl)) :: env) s) := by
  have ha : evalOperands (withEnv env s) [(v32i8, lanesOf 8 tabInt), (v32i8, .reg r)]
      = some [.vec 32 8 (tabInt.map (BitVec.ofInt 8)), .vec 32 8 ctl] := by
    rw [evalOperands_cons
      (v := .vec 32 8 (tabInt.map (BitVec.ofInt 8))) (vs := [.vec 32 8 ctl])
      (by simp [evalOperand, lanesOf, Const.toValue, List.length_map, htabLen])
      (evalOperands_cons (by simp only [withEnv, evalOperand, h]) rfl)]
  rw [evalInstr_call ha (s1Calls_pshufb (tabInt.map (BitVec.ofInt 8)) ctl s.mem s.next),
    htab]
  simp only [withEnv, State.bind]

/-- `%16 = bitcast <16 x i16> %13 to <32 x i8>`. -/
theorem s1_bitcast8 (env : Env) (s : State) (r dst : String) (V : Nat)
    (h : lookupName env r = some (.vec 16 16 (shr4Lanes V))) :
    evalInstr s1Calls (withEnv env s) (.vecBitcast dst 16 16 32 8 (.reg r)) =
      some (withEnv ((dst, .vec 32 8 (unpackLanes 8 32 (packLanes (shr4Lanes V)))) ::
        env) s) := by
  rw [evalInstr_vecBitcast (hv := by simp only [withEnv, evalOperand, h])
    (hl := vecLanes_self (shr4Lanes_length V)) (hwidth := by decide)]
  rfl

/-- `%17 = and <32 x i8> %16, splat (i8 15)`: the high nibbles.  `nibbleLanes_eq` is
the whole of the reduction, which is why the step's value is the nibble list and not
the packed shift. -/
theorem s1_andHiNib (env : Env) (s : State) (r dst : String) (V : Nat)
    (h : lookupName env r = some
      (.vec 32 8 (unpackLanes 8 32 (packLanes (shr4Lanes V))))) :
    evalInstr s1Calls (withEnv env s) (.binopVec dst .and 32 8 (.reg r) (splatOf 32 8 15)) =
      some (withEnv ((dst, .vec 32 8 (hiNibbleLanes V)) :: env) s) := by
  have hm : ((unpackLanes 8 32 (packLanes (shr4Lanes V))).zip
      (List.replicate 32 (BitVec.ofInt 8 15))).mapM
        (fun p => evalBinop .and p.1 p.2) = some (hiNibbleLanes V) := by
    have h15 : (BitVec.ofInt 8 15) = (0x0F : BitVec 8) := by decide
    have h' := zipReplicate_mapM (unpackLanes 8 32 (packLanes (shr4Lanes V)))
      (BitVec.ofInt 8 15) (fun x y => evalBinop .and x y)
      (fun x => x &&& (BitVec.ofInt 8 15)) (fun x => rfl)
    rw [unpackLanes_length] at h'
    rw [h', h15, nibbleLanes_eq V]
  rw [evalInstr_binopVec (l1 := unpackLanes 8 32 (packLanes (shr4Lanes V)))
    (l2 := List.replicate 32 (BitVec.ofInt 8 15)) (ls := hiNibbleLanes V)
    (h1 := by rw [unpackLanes_length]) (h2 := by simp [List.length_replicate])
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, splatOf, Const.toValue]) hm]
  simp only [withEnv, State.bind]

/-- `%and.i2831.i.i.i = and <32 x i8> %18, %15`: the two table entries together. -/
theorem s1_andTables (env : Env) (s : State) (ra rb dst : String)
    (a b : List (BitVec 8)) (ha : a.length = 32) (hb : b.length = 32)
    (hra : lookupName env ra = some (.vec 32 8 a))
    (hrb : lookupName env rb = some (.vec 32 8 b)) :
    evalInstr s1Calls (withEnv env s) (.binopVec dst .and 32 8 (.reg ra) (.reg rb)) =
      some (withEnv ((dst, .vec 32 8 (andLanes a b)) :: env) s) := by
  have hm : (a.zip b).mapM (fun p => evalBinop .and p.1 p.2) = some (andLanes a b) := by
    simpa [andLanes, evalBinop] using mapM_some_map (a.zip b) (fun p => p.1 &&& p.2)
  rw [evalInstr_binopVec (l1 := a) (l2 := b) (ls := andLanes a b)
    (h1 := ha) (h2 := hb)
    (ha := by simp only [withEnv, evalOperand, hra])
    (hb := by simp only [withEnv, evalOperand, hrb]) hm]
  simp only [withEnv, State.bind]

/-- `%19 = and <32 x i8> %and.i2831.i.i.i, splat (i8 63)`. -/
theorem s1_and63 (env : Env) (s : State) (r dst : String) (l : List (BitVec 8))
    (hl : l.length = 32) (h : lookupName env r = some (.vec 32 8 l)) :
    evalInstr s1Calls (withEnv env s) (.binopVec dst .and 32 8 (.reg r) (splatOf 32 8 63)) =
      some (withEnv ((dst, .vec 32 8 (sLanes l)) :: env) s) := by
  have hm : (l.zip (List.replicate 32 (BitVec.ofInt 8 63))).mapM
      (fun p => evalBinop .and p.1 p.2) = some (sLanes l) := by
    have h' := zipReplicate_mapM l (BitVec.ofInt 8 63) (fun x y => evalBinop .and x y)
      (fun x => x &&& (BitVec.ofInt 8 63)) (fun x => rfl)
    rw [hl] at h'
    simpa [sLanes] using h'
  rw [evalInstr_binopVec (l1 := l) (l2 := List.replicate 32 (BitVec.ofInt 8 63))
    (ls := sLanes l) (h1 := hl) (h2 := by simp [List.length_replicate])
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, splatOf, Const.toValue]) hm]
  simp only [withEnv, State.bind]

/-- `%cmp.i25.i.i.i = icmp eq <32 x i8> %19, splat (i8 0)`. -/
theorem s1_icmpEq0 (env : Env) (s : State) (r dst : String) (l : List (BitVec 8))
    (hl : l.length = 32) (h : lookupName env r = some (.vec 32 8 l)) :
    evalInstr s1Calls (withEnv env s)
        (.icmpVec dst .eq 32 8 (.reg r) (splatOf 32 8 0)) =
      some (withEnv ((dst, .vec 32 1 (eq0Lanes l)) :: env) s) := by
  rw [evalInstr_icmpVec
    (ha := by simp only [withEnv, evalOperand, h])
    (vb := .vec 32 8 (List.replicate 32 (BitVec.ofInt 8 0)))
    (hb := by simp only [withEnv, evalOperand, splatOf, Const.toValue])
    (h1 := vecLanes_self hl)
    (h2 := vecLanes_self (l := List.replicate 32 (BitVec.ofInt 8 0)) (by simp))]
  simp only [withEnv, State.bind, eq0Lanes]

/-- `%cmp.i.i.i.i = icmp ult <32 x i8> %and.i2831.i.i.i, splat (i8 64)`. -/
theorem s1_icmpUlt64 (env : Env) (s : State) (r dst : String) (l : List (BitVec 8))
    (hl : l.length = 32) (h : lookupName env r = some (.vec 32 8 l)) :
    evalInstr s1Calls (withEnv env s)
        (.icmpVec dst .ult 32 8 (.reg r) (splatOf 32 8 64)) =
      some (withEnv ((dst, .vec 32 1 (ult64Lanes l)) :: env) s) := by
  rw [evalInstr_icmpVec
    (ha := by simp only [withEnv, evalOperand, h])
    (vb := .vec 32 8 (List.replicate 32 (BitVec.ofInt 8 64)))
    (hb := by simp only [withEnv, evalOperand, splatOf, Const.toValue])
    (h1 := vecLanes_self hl)
    (h2 := vecLanes_self (l := List.replicate 32 (BitVec.ofInt 8 64)) (by simp))]
  simp only [withEnv, State.bind, ult64Lanes]

/-- `%20 = bitcast <32 x i1> %cmp.i25.i.i.i to i32`. -/
theorem s1_bitcastMask32 (env : Env) (s : State) (r dst : String) (l : List (BitVec 1))
    (hl : l.length = 32) (h : lookupName env r = some (.vec 32 1 l)) :
    evalInstr s1Calls (withEnv env s) (.bitcastMask dst 32 (.reg r)) =
      some (withEnv ((dst, .int 32 (BitVec.ofNat 32 (lanesToNat l))) :: env) s) := by
  rw [evalInstr_bitcastMask (hv := by simp only [withEnv, evalOperand, h]) hl]
  rfl

/-- `%not = xor i32 %20, -1`. -/
theorem s1_compl (env : Env) (s : State) (r dst : String) (x : BitVec 32)
    (h : lookupName env r = some (.int 32 x)) :
    evalInstr s1Calls (withEnv env s) (.binop dst .xor 32 (.reg r) (lit 32 (-1))) =
      some (withEnv ((dst, .int 32 (BitVec.ofNat 32 (complW x).toNat)) :: env) s) := by
  rw [evalInstr_binop (x := x) (y := BitVec.ofInt 32 (-1))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (complW x).toNat) (hr := rfl)]
  rfl

/-! ### The delimiter word's identity: `%12` … `%not.i.i.i`

The table region's eleven steps produce the low half's delimiter word (`%not.i.i.i`)
and, at `%22` … `%not.i8.i.i`, the high half's.  The identity is one lemma per half
plus the join, and this section is the first half's.

The chain is the same one `s1_quote_eq` and `s1_control_eq` use — `BitVec.ofNat` at
bit `j`, `lanesToNat_testBit`, the lane list's own lookup, and then the per-byte
predicate — with one extra layer: the body's word is a **complement**, so the
per-byte fact enters negated, and `tabAnd_delim` states it in exactly that form
(`tabAnd …, &&& 0x3F ≠ 0`).  `complW_getLsbD` is where the complement's bit is read,
and it is the only place `BitVec.allOnes` appears.

The table read is a `pshufb` over a table written twice, which is
`pshufbLanes_two_copies_lane`; the lane's nibble is `nibbleLanes_eq`'s arithmetic for
the high half and `and15_eq_mod` for the low.  Those three lemmas are the whole of
the difference between this mask and the backslash one. -/

/-- The low half's low-nibble table lookup. -/
def tabLoLanes (k : Ctx) : List (BitVec 8) := pshufbLanes loTabV (nibLanes (loLanes k))

/-- The low half's high-nibble table lookup. -/
def tabHiLanes (k : Ctx) : List (BitVec 8) := pshufbLanes hiTabV (hiNibbleLanes (loWord k))

/-- `%and.i2831.i.i.i`: the two table entries together. -/
def andWordLanes (k : Ctx) : List (BitVec 8) := andLanes (tabHiLanes k) (tabLoLanes k)

/-- `%19`: the structural bits only. -/
def sWordLanes (k : Ctx) : List (BitVec 8) := sLanes (andWordLanes k)

/-- `%cmp.i25.i.i.i`. -/
def cmpWordLanes (k : Ctx) : List (BitVec 1) := eq0Lanes (sWordLanes k)

/-- `%not.i.i.i`: the low half's delimiter word. -/
def delimLoW (k : Ctx) : BitVec 32 :=
  complW (BitVec.ofNat 32 (lanesToNat (cmpWordLanes k)))

theorem ofNat32_toNat' (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem complW_getLsbD (x : BitVec 32) {j : Nat} (hj : j < 32) :
    (complW x).getLsbD j = !(x.getLsbD j) := by
  have hc : complW x = ~~~x := by
    rw [complW, ofNat32_toNat' x,
      show (BitVec.ofNat 32 (BitVec.ofInt 32 (-1)).toNat) = (BitVec.ofInt 32 (-1) : BitVec 32)
        from ofNat32_toNat' _,
      show (BitVec.ofInt 32 (-1) : BitVec 32) = BitVec.allOnes 32 from by decide,
      BitVec.xor_comm]
    rfl
  rw [hc]
  exact LeanLLVM.Refinement.BitLanes.getLsbD_not_of_lt x hj

theorem getD_map {α β : Type} (l : List α) (f : α → β) {d : α} {d' : β}
    (hf : f d = d') (j : Nat) : (l.map f).getD j d' = f (l.getD j d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : l[j]?
  · exact hf.symm
  · simp

theorem zip_getD (a b : List (BitVec 8)) (j : Nat) (hlen : a.length = b.length) :
    (a.zip b).getD j ((0, 0) : BitVec 8 × BitVec 8) = (a.getD j 0, b.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    show a.zip b = a.zipWith Prod.mk b from rfl, List.getElem?_zipWith]
  by_cases hj : j < a.length
  · simp only [List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem (by omega : j < b.length)]
    simp
  · have ha' : a[j]? = none := by rw [List.getElem?_eq_none_iff]; omega
    have hb' : b[j]? = none := by rw [List.getElem?_eq_none_iff]; omega
    simp [ha', hb']

theorem andLanes_getD (a b : List (BitVec 8)) (j : Nat) (hlen : a.length = b.length) :
    (andLanes a b).getD j 0 = (a.getD j 0) &&& (b.getD j 0) := by
  rw [andLanes, getD_map (a.zip b) (fun p : BitVec 8 × BitVec 8 => p.1 &&& p.2)
      (d := ((0, 0) : BitVec 8 × BitVec 8)) (d' := 0) (by decide) j,
    zip_getD a b j hlen]

theorem nibLanes_getD (l : List (BitVec 8)) (j : Nat) :
    (nibLanes l).getD j 0 = (l.getD j 0) &&& (0x0F : BitVec 8) := by
  rw [nibLanes, getD_map l (fun x => x &&& (BitVec.ofInt 8 15)) (d := (0 : BitVec 8)) (d' := 0)
      (by decide) j,
    show BitVec.ofInt 8 15 = (0x0F : BitVec 8) from by decide]

theorem sLanes_getD (l : List (BitVec 8)) (j : Nat) :
    (sLanes l).getD j 0 = (l.getD j 0) &&& (0x3F : BitVec 8) := by
  rw [sLanes, getD_map l (fun x => x &&& (BitVec.ofInt 8 63)) (d := (0 : BitVec 8)) (d' := 0)
      (by decide) j,
    show BitVec.ofInt 8 63 = (0x3F : BitVec 8) from by decide]

theorem nibLanes_length (l : List (BitVec 8)) : (nibLanes l).length = l.length := by
  simp [nibLanes]

theorem sLanes_length (l : List (BitVec 8)) : (sLanes l).length = l.length := by
  simp [sLanes]

theorem pshufbLanes_length (t control : List (BitVec 8)) :
    (pshufbLanes t control).length = control.length := by
  simp [pshufbLanes]

theorem andLanes_length (a b : List (BitVec 8)) :
    (andLanes a b).length = min a.length b.length := by
  simp [andLanes, List.length_zip]

theorem getLsbD7_of_lt16 {x : BitVec 8} (h : x.toNat < 16) : x.getLsbD 7 = false := by
  show x.toNat.testBit 7 = false
  exact Nat.testBit_lt_two_pow (by omega)

theorem hiNibbleLanes_getD (V : Nat) {j : Nat} (hj : j < 32) :
    (hiNibbleLanes V).getD j 0 = BitVec.ofNat 8 ((V / 2 ^ (8 * j + 4)) % 16) := by
  rw [hiNibbleLanes, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dif_pos (by simpa using hj), Option.getD_some]

theorem loLanes_getD_eq (k : Ctx) {j : Nat} (hj : j < 32) :
    (loLanes k).getD j 0 = BitVec.ofNat 8 (k.lo ⟨j, hj⟩).toNat := by
  rw [loLanes, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dif_pos (by simpa using hj), Option.getD_some]

theorem loLanes_getD_loWord (k : Ctx) {j : Nat} (hj : j < 32) :
    (loLanes k).getD j 0 = BitVec.ofNat 8 (loWord k / 2 ^ (j * 8)) := by
  rw [← unpackLanes_lo k, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [unpackLanes_length]; exact hj), Option.getD_some]
  exact unpackLanes_getElem hj

theorem loLanes_hiNibble (k : Ctx) {j : Nat} (hj : j < 32) :
    ((loLanes k).getD j 0 >>> 4).toNat = (loWord k / 2 ^ (8 * j + 4)) % 16 := by
  rw [loLanes_getD_loWord k hj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 4 = 16 from by decide, BitVec.toNat_ofNat]
  have h : ((loWord k / 2 ^ (j * 8)) % 256) / 16
      = ((loWord k / 2 ^ (j * 8)) / 16) % 16 := by
    rw [show (256 : Nat) = 16 * 16 from by decide]
    exact mod_mul_div _ 16 16 (by decide) (by decide)
  rw [h, Nat.div_div_eq_div_mul]
  have hp : (2 : Nat) ^ (j * 8) * 16 = 2 ^ (8 * j + 4) := by
    rw [show (16 : Nat) = 2 ^ 4 from by decide, ← Nat.pow_add]
    congr 1
    omega
  rw [hp]

theorem tabLoLanes_getD (k : Ctx) {j : Nat} (hj : j < 32) :
    (tabLoLanes k).getD j 0
      = loTab16.getD (((loLanes k).getD j 0) &&& (0x0F : BitVec 8)).toNat 0 := by
  have hlt : ((loLanes k).getD j 0 &&& (0x0F : BitVec 8)).toNat < 16 := by
    rw [and15_eq_mod, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide))
        (by decide : (16 : Nat) ≤ 2 ^ 8))]
    exact Nat.mod_lt _ (by decide)
  have h7 : ((loLanes k).getD j 0 &&& (0x0F : BitVec 8)).getLsbD 7 = false :=
    getLsbD7_of_lt16 hlt
  rw [tabLoLanes, show loTabV = loTab16 ++ loTab16 from rfl,
    pshufbLanes_two_copies_lane loTab16 (by decide) (nibLanes (loLanes k)) hj
      (by simp [nibLanes_length, loLanes_length]),
    nibLanes_getD, h7, if_neg (by simp), Nat.mod_eq_of_lt hlt]

theorem tabHiLanes_getD (k : Ctx) {j : Nat} (hj : j < 32) :
    (tabHiLanes k).getD j 0
      = hiTab16.getD ((hiNibbleLanes (loWord k)).getD j 0).toNat 0 := by
  have hlt : ((hiNibbleLanes (loWord k)).getD j 0).toNat < 16 := by
    rw [hiNibbleLanes_getD (loWord k) hj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide))
        (by decide : (16 : Nat) ≤ 2 ^ 8))]
    exact Nat.mod_lt _ (by decide)
  have h7 : ((hiNibbleLanes (loWord k)).getD j 0).getLsbD 7 = false :=
    getLsbD7_of_lt16 hlt
  rw [tabHiLanes, show hiTabV = hiTab16 ++ hiTab16 from rfl,
    pshufbLanes_two_copies_lane hiTab16 (by decide) (hiNibbleLanes (loWord k)) hj
      (by simp [hiNibbleLanes_length]),
    h7, if_neg (by simp), Nat.mod_eq_of_lt hlt]

theorem tabLanes_length (k : Ctx) : (tabHiLanes k).length = (tabLoLanes k).length := by
  simp [tabHiLanes, tabLoLanes, pshufbLanes_length, nibLanes_length, hiNibbleLanes_length,
    loLanes_length]

theorem andWordLanes_getD (k : Ctx) {j : Nat} (hj : j < 32) :
    (andWordLanes k).getD j 0
      = loTab16.getD (((loLanes k).getD j 0) &&& (0x0F : BitVec 8)).toNat 0
        &&& hiTab16.getD ((hiNibbleLanes (loWord k)).getD j 0).toNat 0 := by
  rw [andWordLanes, andLanes_getD _ _ j (tabLanes_length k),
    tabHiLanes_getD k hj, tabLoLanes_getD k hj, BitVec.and_comm]

theorem hiNibbleLanes_toNat_eq (k : Ctx) {j : Nat} (hj : j < 32) :
    ((hiNibbleLanes (loWord k)).getD j 0).toNat = ((loLanes k).getD j 0 >>> 4).toNat := by
  rw [hiNibbleLanes_getD (loWord k) hj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)),
    loLanes_hiNibble k hj]

theorem sWordLanes_getD (k : Ctx) {j : Nat} (hj : j < 32) :
    (sWordLanes k).getD j 0 = tabAnd ((loLanes k).getD j 0) &&& (0x3F : BitVec 8) := by
  rw [sWordLanes, sLanes_getD, andWordLanes_getD k hj,
    tabAnd, hiNibbleLanes_toNat_eq k hj]

theorem sWordLanes_length (k : Ctx) : (sWordLanes k).length = 32 := by
  simp [sWordLanes, sLanes_length, andWordLanes, andLanes_length, tabLanes_length,
    tabHiLanes, tabLoLanes, pshufbLanes_length, nibLanes_length, hiNibbleLanes_length,
    loLanes_length]

theorem cmpWordLanes_getElem? (k : Ctx) {j : Nat} (hj : j < 32) :
    (cmpWordLanes k)[j]? = some (BitVec.ofBool ((sWordLanes k).getD j 0 = 0)) := by
  rw [cmpWordLanes, eq0Lanes,
    show List.replicate 32 (BitVec.ofInt 8 0)
        = List.replicate (sWordLanes k).length (BitVec.ofInt 8 0) from by
      rw [sWordLanes_length],
    zipReplicate_getElem?_len (sWordLanes k) (BitVec.ofInt 8 0)
      (fun x y => evalICmp .eq x y) (by rw [sWordLanes_length]; exact hj)]
  rfl

theorem bool_not_decide (q : Prop) [Decidable q] : (!(decide q)) = decide (¬ q) := by
  by_cases hq : q <;> simp [hq]

theorem lanesToNat_testBit_bool (l : List (BitVec 1)) (j : Nat) {b : Bool}
    (h : l[j]? = some (BitVec.ofBool b)) : (lanesToNat l).testBit j = b := by
  apply Bool.eq_iff_iff.mpr
  rw [lanesToNat_testBit, h, Option.some.injEq]
  cases b <;> simp

theorem loToBitVec (b : UInt8) : b.toBitVec = BitVec.ofNat 8 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using b.toBitVec.isLt)]
  rfl

theorem delimLoW_eq (k : Ctx) : delimLoW k = pack32 IsDelimB k.lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [delimLoW, complW_getLsbD _ hj, pack32_getLsbD IsDelimB k.lo ⟨j, hj⟩,
    BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and,
    lanesToNat_testBit_bool (cmpWordLanes k) j
      (b := decide ((sWordLanes k).getD j 0 = 0)) (cmpWordLanes_getElem? k hj)]
  rw [bool_not_decide, sWordLanes_getD k hj, loLanes_getD_eq k hj,
    show BitVec.ofNat 8 (k.lo ⟨j, hj⟩).toNat = (k.lo ⟨j, hj⟩).toBitVec from
      (loToBitVec _).symm]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact tabAnd_delim _

/-! ### The high half's table region and the delimiter word

The emission writes the eleven table instructions twice; the steps above are already
parametric in the half, so only the lane vocabulary and the word are separate here.
Each lemma is its low-half counterpart at `hiWord`/`hiLanes`, and the proofs are the
same because every fact they use — `nibLanes_getD`, `sLanes_getD`, `andLanes_getD`,
`pshufbLanes_two_copies_lane`, `nibbleLanes_eq` — is already stated over a half's two
views rather than over `k.lo`. -/

/-- The high half's low-nibble table lookup. -/
def tabLoLanesHi (k : Ctx) : List (BitVec 8) := pshufbLanes loTabV (nibLanes (hiLanes k))

/-- The high half's high-nibble table lookup. -/
def tabHiLanesHi (k : Ctx) : List (BitVec 8) := pshufbLanes hiTabV (hiNibbleLanes (hiWord k))

/-- `%and.i2831.i6.i.i`. -/
def andWordLanesHi (k : Ctx) : List (BitVec 8) := andLanes (tabHiLanesHi k) (tabLoLanesHi k)

/-- `%29`. -/
def sWordLanesHi (k : Ctx) : List (BitVec 8) := sLanes (andWordLanesHi k)

/-- `%cmp.i25.i7.i.i`. -/
def cmpWordLanesHi (k : Ctx) : List (BitVec 1) := eq0Lanes (sWordLanesHi k)

/-- `%not.i8.i.i`: the high half's delimiter word. -/
def delimHiW (k : Ctx) : BitVec 32 :=
  complW (BitVec.ofNat 32 (lanesToNat (cmpWordLanesHi k)))

theorem hiLanes_getD_eq (k : Ctx) {j : Nat} (hj : j < 32) :
    (hiLanes k).getD j 0 = BitVec.ofNat 8 (k.hi ⟨j, hj⟩).toNat := by
  rw [hiLanes, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dif_pos (by simpa using hj), Option.getD_some]

theorem hiLanes_getD_hiWord (k : Ctx) {j : Nat} (hj : j < 32) :
    (hiLanes k).getD j 0 = BitVec.ofNat 8 (hiWord k / 2 ^ (j * 8)) := by
  rw [← unpackLanes_hi k, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [unpackLanes_length]; exact hj), Option.getD_some]
  exact unpackLanes_getElem hj

theorem hiLanes_hiNibble (k : Ctx) {j : Nat} (hj : j < 32) :
    ((hiLanes k).getD j 0 >>> 4).toNat = (hiWord k / 2 ^ (8 * j + 4)) % 16 := by
  rw [hiLanes_getD_hiWord k hj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 4 = 16 from by decide, BitVec.toNat_ofNat]
  have h : ((hiWord k / 2 ^ (j * 8)) % 256) / 16
      = ((hiWord k / 2 ^ (j * 8)) / 16) % 16 := by
    rw [show (256 : Nat) = 16 * 16 from by decide]
    exact mod_mul_div _ 16 16 (by decide) (by decide)
  rw [h, Nat.div_div_eq_div_mul]
  have hp : (2 : Nat) ^ (j * 8) * 16 = 2 ^ (8 * j + 4) := by
    rw [show (16 : Nat) = 2 ^ 4 from by decide, ← Nat.pow_add]
    congr 1
    omega
  rw [hp]

theorem tabLoLanesHi_getD (k : Ctx) {j : Nat} (hj : j < 32) :
    (tabLoLanesHi k).getD j 0
      = loTab16.getD (((hiLanes k).getD j 0) &&& (0x0F : BitVec 8)).toNat 0 := by
  have hlt : ((hiLanes k).getD j 0 &&& (0x0F : BitVec 8)).toNat < 16 := by
    rw [and15_eq_mod, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide))
        (by decide : (16 : Nat) ≤ 2 ^ 8))]
    exact Nat.mod_lt _ (by decide)
  have h7 : ((hiLanes k).getD j 0 &&& (0x0F : BitVec 8)).getLsbD 7 = false :=
    getLsbD7_of_lt16 hlt
  rw [tabLoLanesHi, show loTabV = loTab16 ++ loTab16 from rfl,
    pshufbLanes_two_copies_lane loTab16 (by decide) (nibLanes (hiLanes k)) hj
      (by simp [nibLanes_length, hiLanes_length]),
    nibLanes_getD, h7, if_neg (by simp), Nat.mod_eq_of_lt hlt]

theorem tabHiLanesHi_getD (k : Ctx) {j : Nat} (hj : j < 32) :
    (tabHiLanesHi k).getD j 0
      = hiTab16.getD ((hiNibbleLanes (hiWord k)).getD j 0).toNat 0 := by
  have hlt : ((hiNibbleLanes (hiWord k)).getD j 0).toNat < 16 := by
    rw [hiNibbleLanes_getD (hiWord k) hj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide))
        (by decide : (16 : Nat) ≤ 2 ^ 8))]
    exact Nat.mod_lt _ (by decide)
  have h7 : ((hiNibbleLanes (hiWord k)).getD j 0).getLsbD 7 = false :=
    getLsbD7_of_lt16 hlt
  rw [tabHiLanesHi, show hiTabV = hiTab16 ++ hiTab16 from rfl,
    pshufbLanes_two_copies_lane hiTab16 (by decide) (hiNibbleLanes (hiWord k)) hj
      (by simp [hiNibbleLanes_length]),
    h7, if_neg (by simp), Nat.mod_eq_of_lt hlt]

theorem tabLanesHi_length (k : Ctx) : (tabHiLanesHi k).length = (tabLoLanesHi k).length := by
  simp [tabHiLanesHi, tabLoLanesHi, pshufbLanes_length, nibLanes_length, hiNibbleLanes_length,
    hiLanes_length]

theorem andWordLanesHi_getD (k : Ctx) {j : Nat} (hj : j < 32) :
    (andWordLanesHi k).getD j 0
      = loTab16.getD (((hiLanes k).getD j 0) &&& (0x0F : BitVec 8)).toNat 0
        &&& hiTab16.getD ((hiNibbleLanes (hiWord k)).getD j 0).toNat 0 := by
  rw [andWordLanesHi, andLanes_getD _ _ j (tabLanesHi_length k),
    tabHiLanesHi_getD k hj, tabLoLanesHi_getD k hj, BitVec.and_comm]

theorem hiNibbleLanes_toNat_eq_hi (k : Ctx) {j : Nat} (hj : j < 32) :
    ((hiNibbleLanes (hiWord k)).getD j 0).toNat = ((hiLanes k).getD j 0 >>> 4).toNat := by
  rw [hiNibbleLanes_getD (hiWord k) hj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)),
    hiLanes_hiNibble k hj]

theorem sWordLanesHi_getD (k : Ctx) {j : Nat} (hj : j < 32) :
    (sWordLanesHi k).getD j 0 = tabAnd ((hiLanes k).getD j 0) &&& (0x3F : BitVec 8) := by
  rw [sWordLanesHi, sLanes_getD, andWordLanesHi_getD k hj,
    tabAnd, hiNibbleLanes_toNat_eq_hi k hj]

theorem sWordLanesHi_length (k : Ctx) : (sWordLanesHi k).length = 32 := by
  simp [sWordLanesHi, sLanes_length, andWordLanesHi, andLanes_length, tabLanesHi_length,
    tabHiLanesHi, tabLoLanesHi, pshufbLanes_length, nibLanes_length, hiNibbleLanes_length,
    hiLanes_length]

theorem cmpWordLanesHi_getElem? (k : Ctx) {j : Nat} (hj : j < 32) :
    (cmpWordLanesHi k)[j]? = some (BitVec.ofBool ((sWordLanesHi k).getD j 0 = 0)) := by
  rw [cmpWordLanesHi, eq0Lanes,
    show List.replicate 32 (BitVec.ofInt 8 0)
        = List.replicate (sWordLanesHi k).length (BitVec.ofInt 8 0) from by
      rw [sWordLanesHi_length],
    zipReplicate_getElem?_len (sWordLanesHi k) (BitVec.ofInt 8 0)
      (fun x y => evalICmp .eq x y) (by rw [sWordLanesHi_length]; exact hj)]
  rfl

theorem delimHiW_eq (k : Ctx) : delimHiW k = pack32 IsDelimB k.hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [delimHiW, complW_getLsbD _ hj, pack32_getLsbD IsDelimB k.hi ⟨j, hj⟩,
    BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and,
    lanesToNat_testBit_bool (cmpWordLanesHi k) j
      (b := decide ((sWordLanesHi k).getD j 0 = 0)) (cmpWordLanesHi_getElem? k hj)]
  rw [bool_not_decide, sWordLanesHi_getD k hj, hiLanes_getD_eq k hj,
    show BitVec.ofNat 8 (k.hi ⟨j, hj⟩).toNat = (k.hi ⟨j, hj⟩).toBitVec from
      (loToBitVec _).symm]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact tabAnd_delim _

/-! ### The join: `%conv2.i.i` … `%or5.i.i`, and the delimiter identity

The body widens each half's word with `zext`, shifts the high one above the low one by
thirty-two, and `or`s them — the same three steps the backslash word's `%conv9.i` …
`%or14.i` take, which is why the word is stated once, generically, and both masks are
instances of it.

`joinW_toNat` is where the operand order matters.  `mask64` writes the low word first,
the emission writes the high word first, and this core has no `Nat.lor` commutativity;
so the order is settled at the **`BitVec`** level — one `BitVec.or_comm` on `joinW`
before any `toNat`, which is exactly the move `or14W_comm` makes for the backslash
word.  Neither side then needs `Nat.lor` reordered. -/

/-- `zext i32 … to i64`. -/
def zext64W (x : BitVec 32) : BitVec 64 := BitVec.ofNat 64 x.toNat

/-- `shl i64 …, 32`. -/
def shlUpW (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (x.toNat <<< (BitVec.ofNat 64 (BitVec.ofInt 64 32).toNat).toNat)

/-- The join of two half words in the emission's shape. -/
def joinW (lo hi : BitVec 32) : BitVec 64 :=
  BitVec.ofNat 64 (shlUpW (zext64W hi)).toNat ||| BitVec.ofNat 64 (zext64W lo).toNat

theorem joinW_toNat (lo hi : BitVec 32) :
    (joinW lo hi).toNat = (mask64 lo hi).toNat := by
  have hltLo : lo.toNat < 2 ^ 32 := lo.isLt
  have hltHi : hi.toNat < 2 ^ 32 := hi.isLt
  have hltSh : hi.toNat * 2 ^ 32 < 2 ^ 64 := mul_pow hi.toNat hltHi
  have hlt9 : lo.toNat < 2 ^ 64 := by omega
  have hlt12 : hi.toNat < 2 ^ 64 := by omega
  have h32 : (BitVec.ofNat 64 (BitVec.ofInt 64 32).toNat).toNat = 32 := by
    rw [BitVec.toNat_ofNat, show (BitVec.ofInt 64 32).toNat = 32 from by decide,
      Nat.mod_eq_of_lt (by decide)]
  have hz : (zext64W hi).toNat = hi.toNat := by
    rw [zext64W, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt12]
  have hsh : (shlUpW (zext64W hi)).toNat = hi.toNat * 2 ^ 32 := by
    rw [shlUpW, BitVec.toNat_ofNat, hz, h32, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hltSh]
  have hl : (joinW lo hi).toNat = lo.toNat ||| (hi.toNat * 2 ^ 32) := by
    rw [joinW, BitVec.or_comm, BitVec.toNat_or, BitVec.toNat_ofNat, hsh,
      zext64W, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt9,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hltSh, Nat.mod_eq_of_lt hlt9]
  have hr : (mask64 lo hi).toNat = lo.toNat ||| (hi.toNat * 2 ^ 32) := by
    rw [mask64, BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt hlt12, Nat.mod_eq_of_lt hltSh, Nat.mod_eq_of_lt hlt9]
  rw [hl, hr]


theorem s1_delimiter_eq (k : Ctx) :
    (joinW (delimLoW k) (delimHiW k)).toNat = (specMask64 IsDelimB k.lo k.hi).toNat := by
  rw [joinW_toNat, delimLoW_eq, delimHiW_eq, specMask64]


/-! ### The whitespace word: `%cmp.i.i.i.i` … `%not18.i.i.i`

The whitespace word is the delimiter word's skeleton with a different comparison: the
body tests `icmp ult <32 x i8> %and.i2831.i.i.i, splat 64` — the table pair's bits six
and seven — rather than masking with `63` and testing equality.  So the lane is
`BitVec.ofBool (BitVec.ult x 64)` with **no `decide`** in it: `evalICmp .ult` hands
`ofBool` a `Bool`, where `evalICmp .eq` hands it a `Prop`.  That is why this identity
uses `lanesToNat_testBit_bool` directly and never `bool_not_decide`, and why the
per-byte link is stated as the `Bool` equation `not_ult64_bv` rather than as an `iff`.

The `&& 0x3F` of the delimiter word is absent here, so the lane fact is
`andWordLanes_eq_tabAnd` — `tabAnd` at the byte, unmasked — and `tabAnd_space` reads it
in exactly that form. -/

/-- `%not18.i.i.i`: the low half's whitespace word. -/
def wsLoW (k : Ctx) : BitVec 32 :=
  complW (BitVec.ofNat 32 (lanesToNat (ult64Lanes (andWordLanes k))))

theorem andWordLanes_length (k : Ctx) : (andWordLanes k).length = 32 := by
  simp [andWordLanes, andLanes_length, tabHiLanes, tabLoLanes, pshufbLanes_length,
    nibLanes_length, hiNibbleLanes_length, loLanes_length]

theorem ult64Lanes_getElem? (l : List (BitVec 8)) (hlen : l.length = 32) {j : Nat}
    (hj : j < l.length) :
    (ult64Lanes l)[j]? =
      some (BitVec.ofBool (BitVec.ult (l.getD j 0) (BitVec.ofInt 8 64))) := by
  rw [ult64Lanes, ← hlen,
    zipReplicate_getElem?_len l (BitVec.ofInt 8 64) (fun x y => evalICmp .ult x y) hj]
  rfl

theorem andWordLanes_eq_tabAnd (k : Ctx) {j : Nat} (hj : j < 32) :
    (andWordLanes k).getD j 0 = tabAnd ((loLanes k).getD j 0) := by
  rw [andWordLanes_getD k hj, hiNibbleLanes_toNat_eq k hj]
  rfl

theorem not_ult64_bv (x : BitVec 8) :
    (!(BitVec.ult x (BitVec.ofInt 8 64))) = decide (x &&& (0xC0 : BitVec 8) ≠ 0) := by
  revert x
  decide

theorem wsLoW_eq (k : Ctx) : wsLoW k = pack32 LeanLLVM.JSON.IsSpaceB k.lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [wsLoW, complW_getLsbD _ hj, pack32_getLsbD LeanLLVM.JSON.IsSpaceB k.lo ⟨j, hj⟩,
    BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and,
    lanesToNat_testBit_bool (ult64Lanes (andWordLanes k)) j
      (b := BitVec.ult ((andWordLanes k).getD j 0) (BitVec.ofInt 8 64))
      (ult64Lanes_getElem? _ (andWordLanes_length k) (by rw [andWordLanes_length]; omega)),
    not_ult64_bv, andWordLanes_eq_tabAnd k hj, loLanes_getD_eq k hj,
    show BitVec.ofNat 8 (k.lo ⟨j, hj⟩).toNat = (k.lo ⟨j, hj⟩).toBitVec from
      (loToBitVec _).symm]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact LeanLLVM.Refinement.JsonS1MasksIR.tabAnd_space (k.lo ⟨j, hj⟩)


/-- `%not18.i10.i.i`: the high half's whitespace word. -/
def wsHiW (k : Ctx) : BitVec 32 :=
  complW (BitVec.ofNat 32 (lanesToNat (ult64Lanes (andWordLanesHi k))))

theorem andWordLanesHi_length (k : Ctx) : (andWordLanesHi k).length = 32 := by
  simp [andWordLanesHi, andLanes_length, tabHiLanesHi, tabLoLanesHi, pshufbLanes_length,
    nibLanes_length, hiNibbleLanes_length, hiLanes_length]

theorem andWordLanesHi_eq_tabAnd (k : Ctx) {j : Nat} (hj : j < 32) :
    (andWordLanesHi k).getD j 0 = tabAnd ((hiLanes k).getD j 0) := by
  rw [andWordLanesHi_getD k hj, hiNibbleLanes_toNat_eq_hi k hj]
  rfl

theorem wsHiW_eq (k : Ctx) : wsHiW k = pack32 LeanLLVM.JSON.IsSpaceB k.hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [wsHiW, complW_getLsbD _ hj, pack32_getLsbD LeanLLVM.JSON.IsSpaceB k.hi ⟨j, hj⟩,
    BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and,
    lanesToNat_testBit_bool (ult64Lanes (andWordLanesHi k)) j
      (b := BitVec.ult ((andWordLanesHi k).getD j 0) (BitVec.ofInt 8 64))
      (ult64Lanes_getElem? _ (andWordLanesHi_length k)
        (by rw [andWordLanesHi_length]; omega)),
    not_ult64_bv, andWordLanesHi_eq_tabAnd k hj, hiLanes_getD_eq k hj,
    show BitVec.ofNat 8 (k.hi ⟨j, hj⟩).toNat = (k.hi ⟨j, hj⟩).toBitVec from
      (loToBitVec _).symm]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact LeanLLVM.Refinement.JsonS1MasksIR.tabAnd_space (k.hi ⟨j, hj⟩)

/-- **The whitespace word's identity.**  The body's `%or.i.i`, read as a natural, is
the specification's `IsSpaceB` mask over the block. -/
theorem s1_whitespace_eq (k : Ctx) :
    (joinW (wsLoW k) (wsHiW k)).toNat
      = (specMask64 LeanLLVM.JSON.IsSpaceB k.lo k.hi).toNat := by
  rw [joinW_toNat, wsLoW_eq, wsHiW_eq, specMask64]

/-! ### The escape region: `%esc_ppar.i` … `%or15.i.i` -/

/-- The shape `evalInstr` binds a computed word in: the sixty-four-bit truncation
of the natural its operation produced. -/
def bv (x : BitVec 64) : BitVec 64 := BitVec.ofNat 64 x.toNat

theorem bv_eq (x : BitVec 64) : bv x = x := by
  apply BitVec.eq_of_toNat_eq
  rw [bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem bv_toNat (x : BitVec 64) : (bv x).toNat = x.toNat := by
  rw [bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_toNat {w : Nat} (x : BitVec w) : (BitVec.ofNat w x.toNat) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem xor_allOnes_eq_not (x : BitVec 64) : x ^^^ BitVec.allOnes 64 = ~~~x := by
  rw [BitVec.xor_comm]
  rfl

theorem oneLane_and (a b : Bool) : oneLane 64 a &&& oneLane 64 b = oneLane 64 (a && b) := by
  cases a <;> cases b <;> decide

theorem and_oneLane (x : BitVec 64) (b : Bool) :
    x &&& oneLane 64 b = oneLane 64 (x.getLsbD 0 && b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_and, oneLane_getLsbD _ hk, oneLane_getLsbD _ hk]
  by_cases h : k = 0
  · subst h
    simp
  · have hd : decide (k = 0) = false := by simp [h]
    simp [hd]

theorem oneLane_and_not (a b : Bool) :
    oneLane 64 a &&& ~~~(oneLane 64 b) = oneLane 64 (a && !b) := by
  cases a <;> cases b <;>
    simp only [oneLane, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
      Bool.false_and, Bool.false_eq_true]
  all_goals (
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [BitVec.getLsbD_and, LeanLLVM.Refinement.BitLanes.getLsbD_not_of_lt _ hk]
    simp [oneLane_getLsbD _ hk])


/-- The backslash word, as the escape arithmetic reads it. -/
def bsW (k : Ctx) : BitVec 64 := bv (or14W k)

/-- The run-open bit, as the carry slot holds it. -/
def openW (k : Ctx) : BitVec 64 := oneLane 64 k.opened

/-- The run parity, as the carry slot holds it. -/
def pparW (k : Ctx) : BitVec 64 := oneLane 64 k.ppar

/-- The constant `1`, as the emission writes it. -/
def oneW : BitVec 64 := BitVec.ofInt 64 1

/-- The even-lanes constant, as the emission writes it. -/
def evenC : BitVec 64 := BitVec.ofInt 64 0x5555555555555555

def escShlW (k : Ctx) : BitVec 64 := bv (bsW k <<< 1)
def escOr62W (k : Ctx) : BitVec 64 := bv (escShlW k ||| openW k)
def escNotW (k : Ctx) : BitVec 64 := bv (escOr62W k ^^^ BitVec.allOnes 64)
def escAndStartsW (k : Ctx) : BitVec 64 := bv (bsW k &&& escNotW k)
def escAnd1W (k : Ctx) : BitVec 64 := bv (conv9W k &&& oneW)
def escAnd2W (k : Ctx) : BitVec 64 := bv (openW k &&& escAnd1W k)
def escOr3W (k : Ctx) : BitVec 64 := bv (escAndStartsW k ||| escAnd2W k)
def escShrW (k : Ctx) : BitVec 64 := bv (bsW k >>> 1)
def escNot4W (k : Ctx) : BitVec 64 := bv (escShrW k ^^^ BitVec.allOnes 64)
def escAnd5W (k : Ctx) : BitVec 64 := bv (bsW k &&& escNot4W k)
def escShl6W (k : Ctx) : BitVec 64 := bv (escAnd5W k <<< 1)
def escAnd7W (k : Ctx) : BitVec 64 := bv (pparW k &&& openW k)
def escXorEvenW (k : Ctx) : BitVec 64 := bv (escAnd7W k ^^^ evenC)
def escPext1W (k : Ctx) : BitVec 64 := bv (pext (escXorEvenW k) (escOr3W k))
def escPext2W (k : Ctx) : BitVec 64 := bv (pext evenC (escAnd5W k))
def escXor36W (k : Ctx) : BitVec 64 := bv (escPext1W k ^^^ escPext2W k)
def escNot10W (k : Ctx) : BitVec 64 := bv (escXor36W k ^^^ BitVec.allOnes 64)
def escPdepW (k : Ctx) : BitVec 64 := bv (pdep (escNot10W k) (escShl6W k))
def escCmp63L (k : Ctx) : BitVec 1 := evalICmp .ne (bsW k) (BitVec.ofInt 64 (-1))
def escToboolL (k : Ctx) : BitVec 1 := evalICmp .eq (openW k) (BitVec.ofInt 64 0)
def selBit (c a b : BitVec 1) : BitVec 1 := if c = 1 then a else b
def escOrCondL (k : Ctx) : BitVec 1 := selBit (escCmp63L k) 1 (escToboolL k)
def sel64 (c : BitVec 1) (a b : BitVec 64) : BitVec 64 := if c = 1 then a else b
def escCond24W (k : Ctx) : BitVec 64 := sel64 (escOrCondL k) 0 (pparW k)
def escNot17W (k : Ctx) : BitVec 64 := bv (bsW k ^^^ BitVec.allOnes 64)
def escCtlzW (k : Ctx) : BitVec 64 := BitVec.ofNat 64 (ctlz (escNot17W k))
def escShr16W (k : Ctx) : BitVec 64 := bv (conv12W k >>> 31)
def escNot12W (k : Ctx) : BitVec 64 := bv (escAnd1W k ^^^ BitVec.allOnes 64)
def escAnd39W (k : Ctx) : BitVec 64 := bv (openW k &&& escNot12W k)
def escAnd14W (k : Ctx) : BitVec 64 := bv (escAnd39W k &&& pparW k)
def escXor25W (k : Ctx) : BitVec 64 := bv (escCond24W k ^^^ escCtlzW k)
def escAnd26W (k : Ctx) : BitVec 64 := bv (escXor25W k &&& escShr16W k)

/-- `s1f_escaped`'s return: `%or15.i.i`. -/
def escapedWord (k : Ctx) : BitVec 64 := bv (escPdepW k ||| escAnd14W k)

theorem oneW_eq : oneW = oneLane 64 true := by
  unfold oneW
  rfl

theorem and_oneW (x : BitVec 64) : x &&& oneW = oneLane 64 (x.getLsbD 0) := by
  rw [oneW_eq, and_oneLane]
  simp

theorem evenLanes_literal : evenLanes 64 = (0x5555555555555555 : BitVec 64) := by decide

theorem evenC_eq : evenLanes 64 = evenC := by
  rw [evenLanes_literal]
  decide

/-! The words without the truncation `evalInstr` binds them in. -/

theorem bsW_eq (k : Ctx) : bsW k = or14W k := by rw [bsW, bv_eq]
theorem escShlW_eq (k : Ctx) : escShlW k = bsW k <<< 1 := by rw [escShlW, bv_eq]
theorem escOr62W_eq (k : Ctx) : escOr62W k = escShlW k ||| openW k := by
  rw [escOr62W, bv_eq]
theorem escNotW_eq (k : Ctx) : escNotW k = escOr62W k ^^^ BitVec.allOnes 64 := by
  rw [escNotW, bv_eq]
theorem escAndStartsW_eq (k : Ctx) : escAndStartsW k = bsW k &&& escNotW k := by
  rw [escAndStartsW, bv_eq]
theorem escAnd1W_eq (k : Ctx) : escAnd1W k = conv9W k &&& oneW := by rw [escAnd1W, bv_eq]
theorem escAnd2W_eq (k : Ctx) : escAnd2W k = openW k &&& escAnd1W k := by
  rw [escAnd2W, bv_eq]
theorem escOr3W_eq (k : Ctx) : escOr3W k = escAndStartsW k ||| escAnd2W k := by
  rw [escOr3W, bv_eq]
theorem escShrW_eq (k : Ctx) : escShrW k = bsW k >>> 1 := by rw [escShrW, bv_eq]
theorem escNot4W_eq (k : Ctx) : escNot4W k = escShrW k ^^^ BitVec.allOnes 64 := by
  rw [escNot4W, bv_eq]
theorem escAnd5W_eq (k : Ctx) : escAnd5W k = bsW k &&& escNot4W k := by
  rw [escAnd5W, bv_eq]
theorem escShl6W_eq (k : Ctx) : escShl6W k = escAnd5W k <<< 1 := by rw [escShl6W, bv_eq]
theorem escAnd7W_eq (k : Ctx) : escAnd7W k = pparW k &&& openW k := by
  rw [escAnd7W, bv_eq]
theorem escXorEvenW_eq (k : Ctx) : escXorEvenW k = escAnd7W k ^^^ evenC := by
  rw [escXorEvenW, bv_eq]
theorem escPext1W_eq (k : Ctx) : escPext1W k = pext (escXorEvenW k) (escOr3W k) := by
  rw [escPext1W, bv_eq]
theorem escPext2W_eq (k : Ctx) : escPext2W k = pext evenC (escAnd5W k) := by
  rw [escPext2W, bv_eq]
theorem escXor36W_eq (k : Ctx) : escXor36W k = escPext1W k ^^^ escPext2W k := by
  rw [escXor36W, bv_eq]
theorem escNot10W_eq (k : Ctx) : escNot10W k = escXor36W k ^^^ BitVec.allOnes 64 := by
  rw [escNot10W, bv_eq]
theorem escPdepW_eq (k : Ctx) : escPdepW k = pdep (escNot10W k) (escShl6W k) := by
  rw [escPdepW, bv_eq]
theorem escNot12W_eq (k : Ctx) : escNot12W k = escAnd1W k ^^^ BitVec.allOnes 64 := by
  rw [escNot12W, bv_eq]
theorem escAnd39W_eq (k : Ctx) : escAnd39W k = openW k &&& escNot12W k := by
  rw [escAnd39W, bv_eq]
theorem escAnd14W_eq (k : Ctx) : escAnd14W k = escAnd39W k &&& pparW k := by
  rw [escAnd14W, bv_eq]
theorem escapedWord_eq (k : Ctx) : escapedWord k = escPdepW k ||| escAnd14W k := by
  rw [escapedWord, bv_eq]
theorem escXor25W_eq (k : Ctx) : escXor25W k = escCond24W k ^^^ escCtlzW k := by
  rw [escXor25W, bv_eq]
theorem escAnd26W_eq (k : Ctx) : escAnd26W k = escXor25W k &&& escShr16W k := by
  rw [escAnd26W, bv_eq]

/-! ### The step lemmas -/

theorem s1_escGep (env : Env) (s : State) (k : Ctx)
    (hc : lookupName env "%c" = some (.ptr k.c)) :
    evalInstr s1Calls (withEnv env s) (.gep "%esc_ppar.i" (.int 8) (.reg "%c") (lit 64 8)) =
      some (withEnv (("%esc_ppar.i", .ptr (k.c + 8)) :: env) s) := by
  rw [evalInstr_gep_i8 (base := .reg "%c") (off := lit 64 8) (a := k.c) (w := 64)
    (n := BitVec.ofInt 64 8)
    (hb := by simp only [withEnv, evalOperand, hc])
    (ho := by simp only [withEnv, evalOperand, lit, Const.toValue]) (hpos := by decide)]
  simp only [show (BitVec.signExtend 64 (BitVec.ofInt 64 8)).toNat = 8 from by decide,
    withEnv, State.bind]

theorem s1_escShl (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or14.i" = some (.int 64 (bsW k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%shl.i61.i" .shl 64 (.reg "%or14.i") (lit 64 1)) =
      some (withEnv (("%shl.i61.i", .int 64 (escShlW k)) :: env) s) := by
  rw [evalInstr_binop (x := bsW k) (y := (BitVec.ofInt 64 1))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (escShlW k).toNat) (hr := by
      show (some ((BitVec.ofNat 64 (bsW k).toNat).shiftLeft
        (BitVec.ofNat 64 (BitVec.ofInt 64 1).toNat).toNat)).map BitVec.toNat
        = some (escShlW k).toNat
      rw [show (BitVec.ofNat 64 (BitVec.ofInt 64 1).toNat) = (1 : BitVec 64) from by decide,
        show (1 : BitVec 64).toNat = 1 from by decide,
        show (BitVec.ofNat 64 (bsW k).toNat) = bsW k from bv_eq _]
      unfold escShlW
      rw [bv_toNat]
      rfl)]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem loadValue_int64 {m : Mem} {addr : Nat} {bs : List UInt8}
    (hr : readBytes m addr 8 = some bs) :
    loadValue m (.int 64) addr = some (.int 64 (BitVec.ofNat 64 (bytesToNat bs))) := by
  simp only [loadValue, show (64 = 0) = False from by decide, ite_false, hr]

theorem openW_eq (k : Ctx) : openW k = BitVec.ofNat 64 (if k.opened then 1 else 0) := by
  unfold openW oneLane
  cases hb : k.opened <;> simp [hb]

theorem pparW_eq (k : Ctx) : pparW k = BitVec.ofNat 64 (if k.ppar then 1 else 0) := by
  unfold pparW oneLane
  cases hb : k.ppar <;> simp [hb]

theorem natToBytes_bit (b : Bool) :
    bytesToNat (natToBytes (if b then 1 else 0) 8) = if b then 1 else 0 := by
  cases b <;> decide

theorem s1_escOpenLoad (env : Env) (s : State) (k : Ctx)
    (hc : lookupName env "%c" = some (.ptr k.c))
    (hr : readBytes s.mem k.c 8 = some (natToBytes (if k.opened then 1 else 0) 8)) :
    evalInstr s1Calls (withEnv env s) (.load "%32" (.int 64) (.reg "%c")) =
      some (withEnv (("%32", .int 64 (openW k)) :: env) s) := by
  rw [evalInstr_load (p := .reg "%c") (a := k.c)
    (by simp only [withEnv, evalOperand, hc])
    (by show loadValue s.mem (.int 64) k.c = some (.int 64 (openW k))
        rw [loadValue_int64 hr, natToBytes_bit, openW_eq])]
  rfl

theorem s1_escOr62 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%shl.i61.i" = some (.int 64 (escShlW k)))
    (h2 : lookupName env "%32" = some (.int 64 (openW k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%or.i62.i" .or 64 (.reg "%shl.i61.i") (.reg "%32")) =
      some (withEnv (("%or.i62.i", .int 64 (escOr62W k)) :: env) s) := by
  rw [evalInstr_binop (x := escShlW k) (y := openW k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escOr62W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escOr62W])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escNot (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or.i62.i" = some (.int 64 (escOr62W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%not.i.i" .xor 64 (.reg "%or.i62.i") (lit 64 (-1))) =
      some (withEnv (("%not.i.i", .int 64 (escNotW k)) :: env) s) := by
  rw [evalInstr_binop (x := escOr62W k) (y := (BitVec.ofInt 64 (-1)))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (escNotW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escNotW,
        show (BitVec.ofInt 64 (-1)) = BitVec.allOnes 64 from by decide])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escAndStarts (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or14.i" = some (.int 64 (bsW k)))
    (h2 : lookupName env "%not.i.i" = some (.int 64 (escNotW k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%and.i.i" .and 64 (.reg "%or14.i") (.reg "%not.i.i")) =
      some (withEnv (("%and.i.i", .int 64 (escAndStartsW k)) :: env) s) := by
  rw [evalInstr_binop (x := bsW k) (y := escNotW k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escAndStartsW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAndStartsW])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escAnd1 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%conv9.i" = some (.int 64 (conv9W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%and1.i.i" .and 64 (.reg "%conv9.i") (lit 64 1)) =
      some (withEnv (("%and1.i.i", .int 64 (escAnd1W k)) :: env) s) := by
  rw [evalInstr_binop (x := conv9W k) (y := (BitVec.ofInt 64 1))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (escAnd1W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAnd1W, oneW])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escAnd2 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%32" = some (.int 64 (openW k)))
    (h2 : lookupName env "%and1.i.i" = some (.int 64 (escAnd1W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%and2.i.i" .and 64 (.reg "%32") (.reg "%and1.i.i")) =
      some (withEnv (("%and2.i.i", .int 64 (escAnd2W k)) :: env) s) := by
  rw [evalInstr_binop (x := openW k) (y := escAnd1W k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escAnd2W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAnd2W])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escOr3 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and.i.i" = some (.int 64 (escAndStartsW k)))
    (h2 : lookupName env "%and2.i.i" = some (.int 64 (escAnd2W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%or3.i.i" .or 64 (.reg "%and.i.i") (.reg "%and2.i.i")) =
      some (withEnv (("%or3.i.i", .int 64 (escOr3W k)) :: env) s) := by
  rw [evalInstr_binop (x := escAndStartsW k) (y := escAnd2W k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escOr3W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escOr3W])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escShr (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or14.i" = some (.int 64 (bsW k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%shr.i.i" .lshr 64 (.reg "%or14.i") (lit 64 1)) =
      some (withEnv (("%shr.i.i", .int 64 (escShrW k)) :: env) s) := by
  rw [evalInstr_binop (x := bsW k) (y := (BitVec.ofInt 64 1))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (escShrW k).toNat) (hr := by
      show (some ((BitVec.ofNat 64 (bsW k).toNat).ushiftRight
        (BitVec.ofNat 64 (BitVec.ofInt 64 1).toNat).toNat)).map BitVec.toNat
        = some (escShrW k).toNat
      rw [show (BitVec.ofNat 64 (BitVec.ofInt 64 1).toNat) = (1 : BitVec 64) from by decide,
        show (1 : BitVec 64).toNat = 1 from by decide,
        show (BitVec.ofNat 64 (bsW k).toNat) = bsW k from bv_eq _]
      unfold escShrW
      rw [bv_toNat]
      rfl)]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escNot4 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%shr.i.i" = some (.int 64 (escShrW k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%not4.i.i" .xor 64 (.reg "%shr.i.i") (lit 64 (-1))) =
      some (withEnv (("%not4.i.i", .int 64 (escNot4W k)) :: env) s) := by
  rw [evalInstr_binop (x := escShrW k) (y := (BitVec.ofInt 64 (-1)))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (escNot4W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escNot4W,
        show (BitVec.ofInt 64 (-1)) = BitVec.allOnes 64 from by decide])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escAnd5 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or14.i" = some (.int 64 (bsW k)))
    (h2 : lookupName env "%not4.i.i" = some (.int 64 (escNot4W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%and5.i.i" .and 64 (.reg "%or14.i") (.reg "%not4.i.i")) =
      some (withEnv (("%and5.i.i", .int 64 (escAnd5W k)) :: env) s) := by
  rw [evalInstr_binop (x := bsW k) (y := escNot4W k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escAnd5W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAnd5W])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escShl6 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and5.i.i" = some (.int 64 (escAnd5W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%shl6.i.i" .shl 64 (.reg "%and5.i.i") (lit 64 1)) =
      some (withEnv (("%shl6.i.i", .int 64 (escShl6W k)) :: env) s) := by
  rw [evalInstr_binop (x := escAnd5W k) (y := (BitVec.ofInt 64 1))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (escShl6W k).toNat) (hr := by
      show (some ((BitVec.ofNat 64 (escAnd5W k).toNat).shiftLeft
        (BitVec.ofNat 64 (BitVec.ofInt 64 1).toNat).toNat)).map BitVec.toNat
        = some (escShl6W k).toNat
      rw [show (BitVec.ofNat 64 (BitVec.ofInt 64 1).toNat) = (1 : BitVec 64) from by decide,
        show (1 : BitVec 64).toNat = 1 from by decide,
        show (BitVec.ofNat 64 (escAnd5W k).toNat) = escAnd5W k from bv_eq _]
      unfold escShl6W
      rw [bv_toNat]
      rfl)]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escPparLoad (env : Env) (s : State) (k : Ctx)
    (hp : lookupName env "%esc_ppar.i" = some (.ptr (k.c + 8)))
    (hr : readBytes s.mem (k.c + 8) 8 = some (natToBytes (if k.ppar then 1 else 0) 8)) :
    evalInstr s1Calls (withEnv env s) (.load "%33" (.int 64) (.reg "%esc_ppar.i")) =
      some (withEnv (("%33", .int 64 (pparW k)) :: env) s) := by
  rw [evalInstr_load (p := .reg "%esc_ppar.i") (a := k.c + 8)
    (by simp only [withEnv, evalOperand, hp])
    (by show loadValue s.mem (.int 64) (k.c + 8) = some (.int 64 (pparW k))
        rw [loadValue_int64 hr, natToBytes_bit, pparW_eq])]
  rfl

theorem s1_escAnd7 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%33" = some (.int 64 (pparW k)))
    (h2 : lookupName env "%32" = some (.int 64 (openW k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%and7.i.i" .and 64 (.reg "%33") (.reg "%32")) =
      some (withEnv (("%and7.i.i", .int 64 (escAnd7W k)) :: env) s) := by
  rw [evalInstr_binop (x := pparW k) (y := openW k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escAnd7W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAnd7W])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escXorEven (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and7.i.i" = some (.int 64 (escAnd7W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%xor.i.i" .xor 64 (.reg "%and7.i.i") (lit 64 0x5555555555555555)) =
      some (withEnv (("%xor.i.i", .int 64 (escXorEvenW k)) :: env) s) := by
  rw [evalInstr_binop (x := escAnd7W k) (y := (BitVec.ofInt 64 0x5555555555555555))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (escXorEvenW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escXorEvenW,
        evenC])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escPext1 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%xor.i.i" = some (.int 64 (escXorEvenW k)))
    (h2 : lookupName env "%or3.i.i" = some (.int 64 (escOr3W k))) :
    evalInstr s1Calls (withEnv env s)
        (.call "%34" (.int 64) "llvm.x86.bmi.pext.64"
          [(.int 64, .reg "%xor.i.i"), (.int 64, .reg "%or3.i.i")]) =
      some (withEnv (("%34", .int 64 (escPext1W k)) :: env) s) := by
  have ha : evalOperands (withEnv env s)
      [(.int 64, .reg "%xor.i.i"), (.int 64, .reg "%or3.i.i")]
      = some [.int 64 (escXorEvenW k), .int 64 (escOr3W k)] := by
    rw [evalOperands_cons (v := .int 64 (escXorEvenW k)) (vs := [.int 64 (escOr3W k)])
      (by simp only [withEnv, evalOperand, h])
      (evalOperands_cons (by simp only [withEnv, evalOperand, h2]) rfl)]
  rw [evalInstr_call ha (s1Calls_pext (escXorEvenW k) (escOr3W k) s.mem s.next)]
  simp only [withEnv, State.bind]
  rw [escPext1W_eq]

theorem s1_escPext2 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and5.i.i" = some (.int 64 (escAnd5W k))) :
    evalInstr s1Calls (withEnv env s)
        (.call "%35" (.int 64) "llvm.x86.bmi.pext.64"
          [(.int 64, lit 64 0x5555555555555555), (.int 64, .reg "%and5.i.i")]) =
      some (withEnv (("%35", .int 64 (escPext2W k)) :: env) s) := by
  have ha : evalOperands (withEnv env s)
      [(.int 64, lit 64 0x5555555555555555), (.int 64, .reg "%and5.i.i")]
      = some [.int 64 (BitVec.ofInt 64 0x5555555555555555), .int 64 (escAnd5W k)] := by
    rw [evalOperands_cons (v := .int 64 (BitVec.ofInt 64 0x5555555555555555))
      (vs := [.int 64 (escAnd5W k)])
      (by simp only [withEnv, evalOperand, lit, Const.toValue])
      (evalOperands_cons (by simp only [withEnv, evalOperand, h]) rfl)]
  rw [evalInstr_call ha (s1Calls_pext (BitVec.ofInt 64 0x5555555555555555) (escAnd5W k)
    s.mem s.next)]
  simp only [withEnv, State.bind]
  rw [escPext2W_eq]
  rfl

theorem s1_escXor36 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%34" = some (.int 64 (escPext1W k)))
    (h2 : lookupName env "%35" = some (.int 64 (escPext2W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%36" .xor 64 (.reg "%34") (.reg "%35")) =
      some (withEnv (("%36", .int 64 (escXor36W k)) :: env) s) := by
  rw [evalInstr_binop (x := escPext1W k) (y := escPext2W k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escXor36W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escXor36W])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escNot10 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%36" = some (.int 64 (escXor36W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%not10.i.i" .xor 64 (.reg "%36") (lit 64 (-1))) =
      some (withEnv (("%not10.i.i", .int 64 (escNot10W k)) :: env) s) := by
  rw [evalInstr_binop (x := escXor36W k) (y := (BitVec.ofInt 64 (-1)))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (escNot10W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escNot10W,
        show (BitVec.ofInt 64 (-1)) = BitVec.allOnes 64 from by decide])]
  simp only [withEnv, State.bind, ofNat_toNat]

theorem s1_escPdep (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%not10.i.i" = some (.int 64 (escNot10W k)))
    (h2 : lookupName env "%shl6.i.i" = some (.int 64 (escShl6W k))) :
    evalInstr s1Calls (withEnv env s)
        (.call "%37" (.int 64) "llvm.x86.bmi.pdep.64"
          [(.int 64, .reg "%not10.i.i"), (.int 64, .reg "%shl6.i.i")]) =
      some (withEnv (("%37", .int 64 (escPdepW k)) :: env) s) := by
  have ha : evalOperands (withEnv env s)
      [(.int 64, .reg "%not10.i.i"), (.int 64, .reg "%shl6.i.i")]
      = some [.int 64 (escNot10W k), .int 64 (escShl6W k)] := by
    rw [evalOperands_cons (v := .int 64 (escNot10W k)) (vs := [.int 64 (escShl6W k)])
      (by simp only [withEnv, evalOperand, h])
      (evalOperands_cons (by simp only [withEnv, evalOperand, h2]) rfl)]
  rw [evalInstr_call ha (s1Calls_pdep (escNot10W k) (escShl6W k) s.mem s.next)]
  simp only [withEnv, State.bind]
  rw [escPdepW_eq]

theorem s1_escCmp63 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or14.i" = some (.int 64 (bsW k))) :
    evalInstr s1Calls (withEnv env s)
        (.icmp "%cmp.i63.i" .ne 64 (.reg "%or14.i") (lit 64 (-1))) =
      some (withEnv (("%cmp.i63.i", .int 1 (escCmp63L k)) :: env) s) := by
  rw [evalInstr_icmp (x := bsW k) (y := (BitVec.ofInt 64 (-1)))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])]
  simp only [withEnv, State.bind, escCmp63L]

theorem s1_escTobool (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%32" = some (.int 64 (openW k))) :
    evalInstr s1Calls (withEnv env s)
        (.icmp "%tobool.not.i.i" .eq 64 (.reg "%32") (lit 64 0)) =
      some (withEnv (("%tobool.not.i.i", .int 1 (escToboolL k)) :: env) s) := by
  rw [evalInstr_icmp (x := openW k) (y := (BitVec.ofInt 64 0))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])]
  simp only [withEnv, State.bind, escToboolL]

/-- A one-bit word is `1` or `0`: the comparison lanes are always one of the two,
which is what `select` requires of its condition. -/
theorem bv1_zero_one (x : BitVec 1) : x = 1 ∨ x = 0 := by
  rcases Nat.eq_zero_or_pos x.toNat with h | h
  · right
    apply BitVec.eq_of_toNat_eq
    rw [h]
    rfl
  · left
    apply BitVec.eq_of_toNat_eq
    rw [show x.toNat = 1 from by have := x.isLt; omega]
    rfl

theorem s1_escOrCond (env : Env) (s : State) (k : Ctx) (c : BitVec 1)
    (hc : c = 1 ∨ c = 0)
    (h : lookupName env "%cmp.i63.i" = some (.int 1 c))
    (h2 : lookupName env "%tobool.not.i.i" = some (.int 1 (escToboolL k))) :
    evalInstr s1Calls (withEnv env s)
        (.select "%or.cond.i.i" (.int 1) (.reg "%cmp.i63.i") (lit 1 1)
          (.reg "%tobool.not.i.i")) =
      some (withEnv (("%or.cond.i.i", .int 1 (selBit c 1 (escToboolL k))) :: env) s) := by
  rcases hc with hc | hc
  · rw [evalInstr_select_true (va := .int 1 (1 : BitVec 1)) (vb := .int 1 (escToboolL k))
      (hc := by simp only [withEnv, evalOperand, h, hc])
      (ha := by simp only [withEnv, evalOperand, lit, Const.toValue]; rfl)
      (hb := by simp only [withEnv, evalOperand, h2])]
    simp [withEnv, State.bind, selBit, hc]
  · rw [evalInstr_select_false (va := .int 1 (1 : BitVec 1)) (vb := .int 1 (escToboolL k))
      (hc := by simp only [withEnv, evalOperand, h, hc])
      (ha := by simp only [withEnv, evalOperand, lit, Const.toValue]; rfl)
      (hb := by simp only [withEnv, evalOperand, h2])]
    simp [withEnv, State.bind, selBit, hc]

theorem s1_escCond24 (env : Env) (s : State) (k : Ctx) (c : BitVec 1)
    (hc : c = 1 ∨ c = 0)
    (h : lookupName env "%or.cond.i.i" = some (.int 1 c))
    (h2 : lookupName env "%33" = some (.int 64 (pparW k))) :
    evalInstr s1Calls (withEnv env s)
        (.select "%cond24.i.i" (.int 64) (.reg "%or.cond.i.i") (lit 64 0) (.reg "%33")) =
      some (withEnv (("%cond24.i.i", .int 64 (sel64 c 0 (pparW k))) :: env) s) := by
  rcases hc with hc | hc
  · have h0 : (BitVec.ofInt 64 0) = (0 : BitVec 64) := by decide
    rw [evalInstr_select_true (va := .int 64 0) (vb := .int 64 (pparW k))
      (hc := by simp only [withEnv, evalOperand, h, hc])
      (ha := by simp only [withEnv, evalOperand, lit, Const.toValue, h0])
      (hb := by simp only [withEnv, evalOperand, h2])]
    simp [withEnv, State.bind, sel64, hc]
  · have h0 : (BitVec.ofInt 64 0) = (0 : BitVec 64) := by decide
    rw [evalInstr_select_false (va := .int 64 0) (vb := .int 64 (pparW k))
      (hc := by simp only [withEnv, evalOperand, h, hc])
      (ha := by simp only [withEnv, evalOperand, lit, Const.toValue, h0])
      (hb := by simp only [withEnv, evalOperand, h2])]
    simp [withEnv, State.bind, sel64, hc]

/-- `%not17.i.i = xor i64 %or14.i, -1`. -/
theorem s1_escNot17 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or14.i" = some (.int 64 (bsW k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%not17.i.i" .xor 64 (.reg "%or14.i") (lit 64 (-1))) =
      some (withEnv (("%not17.i.i", .int 64 (escNot17W k)) :: env) s) := by
  rw [evalInstr_binop (x := bsW k) (y := (BitVec.ofInt 64 (-1)))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (escNot17W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escNot17W,
        show (BitVec.ofInt 64 (-1)) = BitVec.allOnes 64 from by decide])]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- `%38 = call llvm.ctlz.i64(%not17.i.i, false)`. -/
theorem s1_escCtlz (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%not17.i.i" = some (.int 64 (escNot17W k))) :
    evalInstr s1Calls (withEnv env s)
        (.call "%38" (.int 64) "llvm.ctlz.i64"
          [(.int 64, .reg "%not17.i.i"), (.int 1, lit 1 0)]) =
      some (withEnv (("%38", .int 64 (escCtlzW k)) :: env) s) := by
  have h0 : (BitVec.ofInt 1 0) = (0 : BitVec 1) := by decide
  have ha : evalOperands (withEnv env s)
      [(.int 64, .reg "%not17.i.i"), (.int 1, lit 1 0)]
      = some [.int 64 (escNot17W k), .int 1 (0 : BitVec 1)] := by
    rw [evalOperands_cons (v := .int 64 (escNot17W k)) (vs := [.int 1 (0 : BitVec 1)])
      (by simp only [withEnv, evalOperand, h])
      (evalOperands_cons (by simp only [withEnv, evalOperand, lit, Const.toValue, h0]) rfl)]
  rw [evalInstr_call ha (s1Calls_ctlz (escNot17W k) s.mem s.next)]
  simp only [withEnv, State.bind, escCtlzW]

/-- `%shr16.i.i = lshr i64 %conv12.i, 31`: the block's top lane. -/
theorem s1_escShr16 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%conv12.i" = some (.int 64 (conv12W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%shr16.i.i" .lshr 64 (.reg "%conv12.i") (lit 64 31)) =
      some (withEnv (("%shr16.i.i", .int 64 (escShr16W k)) :: env) s) := by
  rw [evalInstr_binop (x := conv12W k) (y := (BitVec.ofInt 64 31))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (escShr16W k).toNat) (hr := by
      show (some ((BitVec.ofNat 64 (conv12W k).toNat).ushiftRight
        (BitVec.ofNat 64 (BitVec.ofInt 64 31).toNat).toNat)).map BitVec.toNat
        = some (escShr16W k).toNat
      rw [show (BitVec.ofNat 64 (BitVec.ofInt 64 31).toNat) = (31 : BitVec 64) from by decide,
        show (31 : BitVec 64).toNat = 31 from by decide,
        show (BitVec.ofNat 64 (conv12W k).toNat) = conv12W k from bv_eq _]
      unfold escShr16W
      rw [bv_toNat]
      rfl)]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- `%not12.i.i = xor i64 %and1.i.i, -1`. -/
theorem s1_escNot12 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and1.i.i" = some (.int 64 (escAnd1W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%not12.i.i" .xor 64 (.reg "%and1.i.i") (lit 64 (-1))) =
      some (withEnv (("%not12.i.i", .int 64 (escNot12W k)) :: env) s) := by
  rw [evalInstr_binop (x := escAnd1W k) (y := (BitVec.ofInt 64 (-1)))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (escNot12W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escNot12W,
        show (BitVec.ofInt 64 (-1)) = BitVec.allOnes 64 from by decide])]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- `%39 = and i64 %32, %not12.i.i`. -/
theorem s1_escAnd39 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%32" = some (.int 64 (openW k)))
    (h2 : lookupName env "%not12.i.i" = some (.int 64 (escNot12W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%39" .and 64 (.reg "%32") (.reg "%not12.i.i")) =
      some (withEnv (("%39", .int 64 (escAnd39W k)) :: env) s) := by
  rw [evalInstr_binop (x := openW k) (y := escNot12W k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escAnd39W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAnd39W])]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- `%and14.i.i = and i64 %39, %33`. -/
theorem s1_escAnd14 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%39" = some (.int 64 (escAnd39W k)))
    (h2 : lookupName env "%33" = some (.int 64 (pparW k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%and14.i.i" .and 64 (.reg "%39") (.reg "%33")) =
      some (withEnv (("%and14.i.i", .int 64 (escAnd14W k)) :: env) s) := by
  rw [evalInstr_binop (x := escAnd39W k) (y := pparW k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escAnd14W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAnd14W])]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- `%or15.i.i = or i64 %37, %and14.i.i`: `s1f_escaped`'s return. -/
theorem s1_escOr15 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%37" = some (.int 64 (escPdepW k)))
    (h2 : lookupName env "%and14.i.i" = some (.int 64 (escAnd14W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%or15.i.i" .or 64 (.reg "%37") (.reg "%and14.i.i")) =
      some (withEnv (("%or15.i.i", .int 64 (escapedWord k)) :: env) s) := by
  rw [evalInstr_binop (x := escPdepW k) (y := escAnd14W k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escapedWord k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escapedWord])]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- `%xor25.i.i = xor i64 %cond24.i.i, %38`: the outgoing run parity. -/
theorem s1_escXor25 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%cond24.i.i" = some (.int 64 (escCond24W k)))
    (h2 : lookupName env "%38" = some (.int 64 (escCtlzW k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%xor25.i.i" .xor 64 (.reg "%cond24.i.i") (.reg "%38")) =
      some (withEnv (("%xor25.i.i", .int 64 (escXor25W k)) :: env) s) := by
  rw [evalInstr_binop (x := escCond24W k) (y := escCtlzW k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escXor25W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escXor25W])]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- `%and26.i.i = and i64 %xor25.i.i, %shr16.i.i`: the parity the carry slot takes. -/
theorem s1_escAnd26 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%xor25.i.i" = some (.int 64 (escXor25W k)))
    (h2 : lookupName env "%shr16.i.i" = some (.int 64 (escShr16W k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%and26.i.i" .and 64 (.reg "%xor25.i.i") (.reg "%shr16.i.i")) =
      some (withEnv (("%and26.i.i", .int 64 (escAnd26W k)) :: env) s) := by
  rw [evalInstr_binop (x := escXor25W k) (y := escShr16W k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (escAnd26W k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, escAnd26W])]
  simp only [withEnv, State.bind, ofNat_toNat]

/-! ### The escape word's identity

`%or15.i.i` is `s1f_escaped`'s return, and `QuoteDerive`'s `kernelEscape` is the
same arithmetic named after the registers.  The chain below reads each stage of the
body into that name — the run starts, the run ends and the lane after them, the
parity alternate, the run parity, the scatter, and the boundary lane — and then the
identity is the disjunction `kernelEscape` is defined as. -/

theorem nat32 : (BitVec.ofNat 64 (BitVec.ofInt 64 32).toNat).toNat = 32 := by decide

/-- The `i16`-view shift's word has lane zero clear: its first twelve bits are the
low half's low nibble, and the shift carries it above lane zero. -/
theorem shl13_lane0 (k : Ctx) : (shl13W k).getLsbD 0 = false := by
  rw [shl13W, nat32, BitVec.getLsbD_shiftLeft]
  rfl

theorem ofNat_conv9 (k : Ctx) : (BitVec.ofNat 64 (conv9W k).toNat) = conv9W k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (conv9W k).isLt]

theorem ofNat_shl13 (k : Ctx) :
    (BitVec.ofNat 64 (BitVec.ofNat 64 (shl13W k).toNat).toNat) = shl13W k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show (BitVec.ofNat 64 (shl13W k).toNat).toNat < 2 ^ 64 from
      (BitVec.ofNat 64 (shl13W k).toNat).isLt),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (shl13W k).isLt]

/-- Lane zero of the backslash word: the low half's lane zero. -/
theorem or14W_lane0 (k : Ctx) : (or14W k).getLsbD 0 = (conv9W k).getLsbD 0 := by
  rw [or14W_comm]
  rw [BitVec.getLsbD_or, ofNat_conv9 k, ofNat_shl13 k, shl13_lane0, Bool.or_false]

/-- `%and1.i.i`'s word, at its only possible set lane. -/
theorem escAnd1W_lane (k : Ctx) : escAnd1W k = oneLane 64 ((bsW k).getLsbD 0) := by
  rw [escAnd1W_eq, and_oneW, bsW_eq, or14W_lane0]

/-- `%and2.i.i`'s word is the block's own lane zero, masked with the run-open bit. -/
theorem escAnd2W_lane (k : Ctx) : escAnd2W k = bsW k &&& oneLane 64 k.opened := by
  rw [escAnd2W_eq, escAnd1W_lane]
  simp only [openW]
  rw [oneLane_and, and_oneLane,
    show (k.opened && (bsW k).getLsbD 0) = ((bsW k).getLsbD 0 && k.opened) from
      Bool.and_comm _ _]

/-- `%or3.i.i` is the kernel's run-start mask. -/
theorem escRunStarts (k : Ctx) : escOr3W k = runStarts (bsW k) k.opened := by
  rw [escOr3W_eq, escAndStartsW_eq, escNotW_eq, escOr62W_eq, escShlW_eq,
    xor_allOnes_eq_not, escAnd2W_lane, runStarts, openedBackslashes]
  simp only [openW]

/-- `%and5.i.i` is the kernel's run-end mask. -/
theorem escRunEnds (k : Ctx) : escAnd5W k = runEnds (bsW k) := by
  rw [escAnd5W_eq, escNot4W_eq, escShrW_eq, xor_allOnes_eq_not, runEnds]

/-- `%shl6.i.i` is the lane after each run's end. -/
theorem escAfterRuns (k : Ctx) : escShl6W k = afterRuns (bsW k) := by
  rw [escShl6W_eq, escRunEnds, afterRuns]

/-- `%xor.i.i` is the kernel's parity alternate. -/
theorem escAlt (k : Ctx) : escXorEvenW k = altLanes 64 k.opened k.ppar := by
  rw [escXorEvenW_eq, escAnd7W_eq, altLanes, evenC_eq]
  simp only [openW, pparW]
  rw [oneLane_and, BitVec.xor_comm,
    show (k.ppar && k.opened) = (k.opened && k.ppar) from Bool.and_comm _ _]

/-- `%not10.i.i` is the kernel's odd-run mask. -/
theorem escOddRuns (k : Ctx) :
    escNot10W k = oddRuns (bsW k) k.opened k.ppar := by
  rw [escNot10W_eq, escXor36W_eq, xor_allOnes_eq_not, escPext1W_eq, escPext2W_eq,
    escAlt, escRunStarts, escRunEnds, oddRuns, startPara, endPara, ← evenC_eq]

/-- `%37` is the kernel's scattered run parity. -/
theorem escEscapedRuns (k : Ctx) :
    escPdepW k = escapedRuns (bsW k) k.opened k.ppar := by
  rw [escPdepW_eq, escOddRuns, escAfterRuns, escapedRuns]

/-- `%and14.i.i` is the kernel's boundary lane: lane zero escaped when the block
enters in the middle of an odd run. -/
theorem escBoundary (k : Ctx) :
    escAnd14W k = boundaryEscape (bsW k) k.opened k.ppar := by
  rw [escAnd14W_eq, escAnd39W_eq, escNot12W_eq, escAnd1W_lane, xor_allOnes_eq_not,
    boundaryEscape]
  simp only [openW, pparW]
  rw [oneLane_and_not, oneLane_and]

/-- `%or15.i.i` is `kernelEscape`: the scatter of the odd runs' parity onto the
lanes after their ends, or the boundary lane. -/
theorem escapedWord_eq_kernelEscape (k : Ctx) :
    escapedWord k = kernelEscape (bsW k) k.opened k.ppar := by
  rw [escapedWord_eq, escEscapedRuns, escBoundary, kernelEscape]

/-- The block's backslash word is the specification's sixty-four-lane
`IsBackslashB` mask. -/
theorem bsW_eq_spec (k : Ctx) : bsW k = specMask64 IsBackslashB k.lo k.hi := by
  rw [bsW_eq]
  apply BitVec.eq_of_toNat_eq
  rw [s1_backslash_eq]
  rfl

/-- **The escape word's identity.**  `s1f_escaped`'s return — the body's
`%or15.i.i` — is the specification's `kernelEscape` over the block's backslash mask
and the carry slot's two bits. -/
theorem s1_escaped_eq (k : Ctx) :
    (escapedWord k).toNat =
      (kernelEscape (specMask64 IsBackslashB k.lo k.hi) k.opened k.ppar).toNat := by
  rw [escapedWord_eq_kernelEscape, bsW_eq_spec]


/-! ### The unescaped-quote word: `%not.i` … `%and.i`, and the block-level identity -/

theorem isUnescapedQuote_and_isEscapedQuote (st : ClassState) (b : UInt8) :
    (isUnescapedQuote st b && isEscapedQuote st b) = false := by
  unfold isUnescapedQuote isEscapedQuote
  cases hq : IsQuoteB b <;> cases ho : st.oddRun <;> simp

theorem quote_and_not_escaped_lane (p q e : Bool) (h : (q || e) = p) (hd : (q && e) = false) :
    (p && !e) = q := by
  rw [← h, show ((q || e) && !e) = (q && !e) from by cases q <;> cases e <;> rfl]
  cases q <;> cases e <;> simp_all

/-- **The window's unescaped-quote field is its raw quote mask without the
escapes.**  The classifier splits each quote lane by the escape state and loses
none, so subtracting the escaped half from the raw mask returns the field the fold
records.  This is the `classWindow`-level algebra `s1_and_eq` is the block-level
instance of. -/
theorem quoteMask_and_not_escaped (bs : List UInt8) (st : ClassState)
    (hlen : 32 ≤ bs.length) :
    LeanLLVM.JSON.maskOfListWith IsQuoteB bs &&& ~~~(escapedQuoteMask bs st) = quoteMask bs st := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hklen : k < bs.length := by omega
  obtain ⟨b, hb⟩ : ∃ b, bs[k]? = some b := by
    cases h : bs[k]?
    · exact absurd h (by simp [List.getElem?_eq_none_iff, hklen])
    · exact ⟨_, rfl⟩
  rw [BitVec.getLsbD_and, LeanLLVM.Refinement.BitLanes.getLsbD_not_of_lt _ hk,
    LeanLLVM.JSON.maskOfListWith_getLsbD hk hb,
    escapedQuoteMask_getLsbD hk hb,
    quoteMask_getLsbD hk hb]
  exact quote_and_not_escaped_lane _ _ _ (quote_or_escaped _ _)
    (isUnescapedQuote_and_isEscapedQuote _ _)

/-- `%or.i`: the raw quote word. -/
def qrawW (k : Ctx) : BitVec 64 := BitVec.ofNat 64 (lanesToNat (quoteLanes k))

/-- `%not.i`: the escape word's complement. -/
def notEscW (k : Ctx) : BitVec 64 := bv (escapedWord k ^^^ BitVec.allOnes 64)

/-- `%and.i`: the unescaped-quote word, `%or.i & ~%not.i`. -/
def andQuoteW (k : Ctx) : BitVec 64 := bv (qrawW k &&& notEscW k)

theorem qrawW_eq (k : Ctx) : qrawW k = specMask64 IsQuoteB k.lo k.hi :=
  s1_quote_eq k

theorem notEscW_eq (k : Ctx) : notEscW k = ~~~(escapedWord k) := by
  rw [notEscW, bv_eq, xor_allOnes_eq_not]

theorem andQuoteW_eq (k : Ctx) :
    andQuoteW k = specMask64 IsQuoteB k.lo k.hi &&& ~~~(escapedWord k) := by
  rw [andQuoteW, bv_eq, qrawW_eq, notEscW_eq]

/-- **The unescaped-quote word is the specification's.**  The body's `%and.i` —
`%or.i & ~%not.i`, the raw quote mask without the escapes — is `specQuote64`, the
`kernelQuote64` derivation read at the body's own registers. -/
theorem s1_and_eq (k : Ctx) (hst : k.st.oddRun = (k.opened && k.ppar)) :
    specMask64 IsQuoteB k.lo k.hi &&& ~~~(escapedWord k) = specQuote64 k.lo k.hi k.st := by
  rw [escapedWord_eq_kernelEscape, bsW_eq_spec]
  exact kernelQuote64 k.lo k.hi k.st k.opened k.ppar hst

theorem andQuoteW_spec (k : Ctx) (hst : k.st.oddRun = (k.opened && k.ppar)) :
    andQuoteW k = specQuote64 k.lo k.hi k.st := by
  rw [andQuoteW_eq, s1_and_eq k hst]

/-! ### The in-string word: `%vecinit1.i.i.i` … `%xor.i` -/

/-- `%vecinit1.i.i.i`'s lanes: the quote word in lane zero of a two-lane vector. -/
def vecInitLanes (k : Ctx) : List (BitVec 64) := [andQuoteW k, 0]

/-- `%40`'s lanes: the carry-less product at immediate zero, lane one clear. -/
def pclmulLanes (k : Ctx) : List (BitVec 64) :=
  [clmul (andQuoteW k) (BitVec.allOnes 64), 0]

/-- `%vecext.i.i.i`: lane zero of the product. -/
def vecextW (k : Ctx) : BitVec 64 := clmul (andQuoteW k) (BitVec.allOnes 64)

/-- `%41`: the carry slot's in-string word. -/
def seedW (k : Ctx) : BitVec 64 := seedVec 64 k.st.inside

/-- `%xor.i`: the in-string word. -/
def inStringWord (k : Ctx) : BitVec 64 := bv (vecextW k ^^^ seedW k)

/-- `%shr.i`: the word the carry slot takes, the in-string word's sign. -/
def imSignW (k : Ctx) : BitVec 64 := bv (BitVec.sshiftRight (inStringWord k) 63)

/-! ### The step lemmas -/

/-- `%not.i = xor i64 %or15.i.i, -1`. -/
theorem s1_andNotEsc (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or15.i.i" = some (.int 64 (escapedWord k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%not.i" .xor 64 (.reg "%or15.i.i") (lit 64 (-1))) =
      some (withEnv (("%not.i", .int 64 (notEscW k)) :: env) s) := by
  rw [evalInstr_binop (x := escapedWord k) (y := (BitVec.ofInt 64 (-1)))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (notEscW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, notEscW,
        show (BitVec.ofInt 64 (-1)) = BitVec.allOnes 64 from by decide])]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- `%and.i = and i64 %or.i, %not.i`. -/
theorem s1_andQuote (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or.i" = some (.int 64 (qrawW k)))
    (h2 : lookupName env "%not.i" = some (.int 64 (notEscW k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%and.i" .and 64 (.reg "%or.i") (.reg "%not.i")) =
      some (withEnv (("%and.i", .int 64 (andQuoteW k)) :: env) s) := by
  rw [evalInstr_binop (x := qrawW k) (y := notEscW k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (andQuoteW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, andQuoteW])]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- `%vecinit1.i.i.i = insertelement <2 x i64> zeroinitializer, i64 %and.i, i64 0`. -/
theorem s1_vecInit (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and.i" = some (.int 64 (andQuoteW k))) :
    evalInstr s1Calls (withEnv env s)
        (.insertelement "%vecinit1.i.i.i" 2 64 (.imm (.splat 2 64 (BitVec.ofNat 64 0)))
          (.reg "%and.i") (lit 64 0)) =
      some (withEnv (("%vecinit1.i.i.i", .vec 2 64 (vecInitLanes k)) :: env) s) := by
  rw [evalInstr_insertelement
    (vv := .vec 2 64 (List.replicate 2 (BitVec.ofNat 64 0)))
    (lanes := List.replicate 2 (BitVec.ofNat 64 0))
    (ev := .int 64 (andQuoteW k)) (x := (andQuoteW k).toNat)
    (k := (BitVec.ofInt 64 0))
    (hv := by simp only [withEnv, evalOperand, Const.toValue])
    (hl := vecLanes_self (by simp))
    (he := by simp only [withEnv, evalOperand, h])
    (hx := by simp [Value.intToNat])
    (hi := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (hk := by simp [List.length_replicate])]
  simp only [withEnv, State.bind, vecInitLanes]
  rw [show (BitVec.ofNat 64 (andQuoteW k).toNat) = andQuoteW k from ofNat_toNat (andQuoteW k),
    show (BitVec.ofInt 64 0).toNat = 0 from by decide]
  rfl

/-- `%40 = call @llvm.x86.pclmulqdq(%vecinit1.i.i.i, <2 x i64> <-1, 0>, i8 0)`. -/
theorem s1_pclmul (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%vecinit1.i.i.i" = some (.vec 2 64 (vecInitLanes k))) :
    evalInstr s1Calls (withEnv env s)
        (.call "%40" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
          [(.vec 2 (.int 64), .reg "%vecinit1.i.i.i"),
           (.vec 2 (.int 64), lanesOf 64 [-1, 0]), (.int 8, lit 8 0)]) =
      some (withEnv (("%40", .vec 2 64 (pclmulLanes k)) :: env) s) := by
  have hneg : (BitVec.ofInt 64 (-1) : BitVec 64) = BitVec.allOnes 64 := by decide
  have ha : evalOperands (withEnv env s)
      [(.vec 2 (.int 64), .reg "%vecinit1.i.i.i"),
       (.vec 2 (.int 64), lanesOf 64 [-1, 0]), (.int 8, lit 8 0)]
      = some [.vec 2 64 (vecInitLanes k),
          .vec 2 64 [BitVec.ofInt 64 (-1), BitVec.ofInt 64 0], .int 8 0] := by
    rw [evalOperands_cons (v := .vec 2 64 (vecInitLanes k))
      (vs := [.vec 2 64 [BitVec.ofInt 64 (-1), BitVec.ofInt 64 0], .int 8 0])
      (by simp only [withEnv, evalOperand, h])
      (evalOperands_cons (v := .vec 2 64 [BitVec.ofInt 64 (-1), BitVec.ofInt 64 0])
        (vs := [.int 8 0])
        (by simp [withEnv, evalOperand, lanesOf, Const.toValue]) rfl)]
  rw [evalInstr_call ha
    (s1Calls_pclmulqdq (andQuoteW k) 0 (BitVec.ofInt 64 (-1)) (BitVec.ofInt 64 0)
      s.mem s.next)]
  simp only [withEnv, State.bind, pclmulLanes, vecInitLanes, hneg]

/-- `%vecext.i.i.i = extractelement <2 x i64> %40, i64 0`. -/
theorem s1_vecext (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%40" = some (.vec 2 64 (pclmulLanes k))) :
    evalInstr s1Calls (withEnv env s)
        (.extractelement "%vecext.i.i.i" 2 64 (.reg "%40") (lit 64 0)) =
      some (withEnv (("%vecext.i.i.i", .int 64 (vecextW k)) :: env) s) := by
  rw [evalInstr_extractelement
    (vv := .vec 2 64 (pclmulLanes k)) (lanes := pclmulLanes k)
    (x := clmul (andQuoteW k) (BitVec.allOnes 64)) (wi := 64) (k := (BitVec.ofInt 64 0))
    (hv := by simp only [withEnv, evalOperand, h])
    (hl := vecLanes_self (by simp [pclmulLanes]))
    (hi := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (hx := by simp [pclmulLanes, vecextW])]
  simp only [withEnv, State.bind, vecextW]

/-- `%im_carry.i = getelementptr i8, ptr %c, i64 16`. -/
theorem s1_imGep (env : Env) (s : State) (k : Ctx)
    (hc : lookupName env "%c" = some (.ptr k.c)) :
    evalInstr s1Calls (withEnv env s) (.gep "%im_carry.i" (.int 8) (.reg "%c") (lit 64 16)) =
      some (withEnv (("%im_carry.i", .ptr (k.c + 16)) :: env) s) := by
  rw [evalInstr_gep_i8 (base := .reg "%c") (off := lit 64 16) (a := k.c) (w := 64)
    (n := BitVec.ofInt 64 16)
    (hb := by simp only [withEnv, evalOperand, hc])
    (ho := by simp only [withEnv, evalOperand, lit, Const.toValue]) (hpos := by decide)]
  simp only [show (BitVec.signExtend 64 (BitVec.ofInt 64 16)).toNat = 16 from by decide,
    withEnv, State.bind]

theorem seedBytes (b : Bool) :
    bytesToNat (natToBytes (if b then 0xFFFFFFFFFFFFFFFF else 0) 8) = (seedVec 64 b).toNat := by
  cases b <;> decide

/-- `%41 = load i64, ptr %im_carry.i`. -/
theorem s1_imLoad (env : Env) (s : State) (k : Ctx)
    (hp : lookupName env "%im_carry.i" = some (.ptr (k.c + 16)))
    (hr : readBytes s.mem (k.c + 16) 8
      = some (natToBytes (if k.st.inside then 0xFFFFFFFFFFFFFFFF else 0) 8)) :
    evalInstr s1Calls (withEnv env s) (.load "%41" (.int 64) (.reg "%im_carry.i")) =
      some (withEnv (("%41", .int 64 (seedW k)) :: env) s) := by
  rw [evalInstr_load (p := .reg "%im_carry.i") (a := k.c + 16)
    (by simp only [withEnv, evalOperand, hp])
    (by show loadValue s.mem (.int 64) (k.c + 16) = some (.int 64 (seedW k))
        rw [loadValue_int64 hr, seedBytes, seedW,
          show (BitVec.ofNat 64 (seedVec 64 k.st.inside).toNat) = seedVec 64 k.st.inside
            from ofNat_toNat (seedVec 64 k.st.inside)])]
  rfl

/-- `%xor.i = xor i64 %vecext.i.i.i, %41`: the in-string word. -/
theorem s1_inString (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%vecext.i.i.i" = some (.int 64 (vecextW k)))
    (h2 : lookupName env "%41" = some (.int 64 (seedW k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%xor.i" .xor 64 (.reg "%vecext.i.i.i") (.reg "%41")) =
      some (withEnv (("%xor.i", .int 64 (inStringWord k)) :: env) s) := by
  rw [evalInstr_binop (x := vecextW k) (y := seedW k)
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, h2])
    (r := (inStringWord k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, inStringWord])]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- `%shr.i = ashr i64 %xor.i, 63`. -/
theorem s1_imSign (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%xor.i" = some (.int 64 (inStringWord k))) :
    evalInstr s1Calls (withEnv env s)
        (.binop "%shr.i" .ashr 64 (.reg "%xor.i") (lit 64 63)) =
      some (withEnv (("%shr.i", .int 64 (imSignW k)) :: env) s) := by
  rw [evalInstr_binop (x := inStringWord k) (y := (BitVec.ofInt 64 63))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (imSignW k).toNat) (hr := by
      show (some ((BitVec.ofNat 64 (inStringWord k).toNat).sshiftRight
        (BitVec.ofNat 64 (BitVec.ofInt 64 63).toNat).toNat)).map BitVec.toNat
        = some (imSignW k).toNat
      rw [show (BitVec.ofNat 64 (BitVec.ofInt 64 63).toNat) = (63 : BitVec 64) from by decide,
        show (63 : BitVec 64).toNat = 63 from by decide,
        show (BitVec.ofNat 64 (inStringWord k).toNat) = inStringWord k from
          ofNat_toNat (inStringWord k)]
      unfold imSignW
      rw [bv_toNat]
      rfl)]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- **The in-string word's identity.**  `%xor.i` — the block's carry-less product
XOR the carry slot's word — is the specification's in-string mask, through
`specInString64_eq_clmul` and the unescaped-quote identity `s1_and_eq`. -/
theorem s1_instring_eq (k : Ctx) (hst : k.st.oddRun = (k.opened && k.ppar)) :
    (inStringWord k).toNat = (specInString64 k.lo k.hi k.st).toNat := by
  rw [specInString64_eq_clmul]
  congr 1
  rw [inStringWord, bv_eq, vecextW, seedW, andQuoteW_spec k hst]


/-! ### The two joins: `%conv.i.i` … `%or.i.i`, `%conv2.i.i` … `%or5.i.i`

The emission writes the same four instructions twice — `zext` the low half's word,
`zext` the high half's, shift the high one above the low one by thirty-two, and
`or` them — so each step is stated once, parametrically in the destination and the
word, and the composition instantiates it twice.  The join's value is `joinW`, the
word the delimiter and whitespace identities are stated over. -/

/-- A thirty-two-bit computed word, in the shape `evalInstr` binds it. -/
def bv32 (x : BitVec 32) : BitVec 32 := BitVec.ofNat 32 x.toNat

theorem bv32_eq (x : BitVec 32) : bv32 x = x := by
  apply BitVec.eq_of_toNat_eq
  rw [bv32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-- A shift's own `toNat`: `x <<< n` read back as the wrapped natural. -/
theorem shiftLeft_toNat (x : BitVec 64) (n : Nat) :
    (x.shiftLeft n).toNat = (BitVec.ofNat 64 (x.toNat <<< n)).toNat := by
  rw [show x.shiftLeft n = (x <<< n) from rfl, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]

/-- The `shl` step's arithmetic. -/
theorem shlJoin_hr (x : BitVec 64) :
    evalBinopNat .shl 64 x.toNat (BitVec.ofInt 64 32).toNat
      = some ((bv (shlUpW x))).toNat := by
  simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, shlUpW]
  rw [show (BitVec.ofInt 64 32).toNat = 32 from by decide]
  exact congrArg some (shiftLeft_toNat x 32)

/-- A join of two truncated words is the join of the words. -/
theorem or_bv (x y : BitVec 64) : (bv x ||| bv y) = (x ||| y) := by
  rw [bv_eq, bv_eq]

/-- The `or` step's arithmetic. -/
theorem orJoin_hr (x y : BitVec 64) :
    evalBinopNat .or 64 x.toNat y.toNat = some ((bv (bv x ||| bv y))).toNat := by
  simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat]
  rw [or_bv]

/-- `zext i32 … to i64`, parametric in the destination and the source word. -/
theorem s1_zextJoin (env : Env) (s : State) (r dst : String) (x : BitVec 32)
    (h : lookupName env r = some (.int 32 x)) :
    evalInstr s1Calls (withEnv env s) (.zext dst 32 64 (.reg r)) =
      some (withEnv ((dst, .int 64 (zext64W x)) :: env) s) := by
  rw [evalInstr_zext (x := x) (hv := by simp only [withEnv, evalOperand, h])]
  simp only [withEnv, State.bind, zext64W]

/-- `shl i64 …, 32`, parametric in the destination and the source word. -/
theorem s1_shlJoin (env : Env) (s : State) (r dst : String) (x : BitVec 64)
    (h : lookupName env r = some (.int 64 x)) :
    evalInstr s1Calls (withEnv env s) (.binop dst .shl 64 (.reg r) (lit 64 32)) =
      some (withEnv ((dst, .int 64 (bv (shlUpW x))) :: env) s) := by
  rw [evalInstr_binop (x := x) (y := (BitVec.ofInt 64 32))
    (ha := by simp only [withEnv, evalOperand, h])
    (hb := by simp only [withEnv, evalOperand, lit, Const.toValue])
    (r := (bv (shlUpW x)).toNat) (hr := shlJoin_hr x)]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- `or i64 …, …`, parametric in the destination and the two words. -/
theorem s1_orJoin (env : Env) (s : State) (ra rb dst : String) (x y : BitVec 64)
    (ha : lookupName env ra = some (.int 64 x))
    (hb : lookupName env rb = some (.int 64 y)) :
    evalInstr s1Calls (withEnv env s) (.binop dst .or 64 (.reg ra) (.reg rb)) =
      some (withEnv ((dst, .int 64 (bv (bv x ||| bv y))) :: env) s) := by
  rw [evalInstr_binop (x := x) (y := y)
    (ha := by simp only [withEnv, evalOperand, ha])
    (hb := by simp only [withEnv, evalOperand, hb])
    (r := (bv (bv x ||| bv y)).toNat) (hr := orJoin_hr x y)]
  simp only [withEnv, State.bind, ofNat_toNat]

/-- The join's own word: the two `bv` layers the `or` step produces are
`joinW`'s operands. -/
theorem joinBody_eq (lo hi : BitVec 32) :
    bv (bv (bv (shlUpW (zext64W hi))) ||| bv (zext64W lo)) = joinW lo hi := by
  have h2 : bv (bv (bv (shlUpW (zext64W hi))) ||| bv (zext64W lo))
      = (bv (bv (shlUpW (zext64W hi))) ||| bv (zext64W lo)) := bv_eq _
  have h1 : bv (bv (shlUpW (zext64W hi))) = bv (shlUpW (zext64W hi)) := bv_eq _
  rw [h2, h1]
  rfl

/-- **The whitespace join is the body's.**  `%or.i.i` — the high half's word
shifted above the low half's and `or`ed in — is `joinW`, the shape the whitespace
identity reads. -/
theorem s1_wsJoin (k : Ctx) :
    bv (bv (bv (shlUpW (zext64W (bv32 (wsHiW k))))) ||| bv (zext64W (bv32 (wsLoW k))))
      = joinW (wsLoW k) (wsHiW k) := by
  rw [bv32_eq, bv32_eq]
  exact joinBody_eq _ _

/-- **The delimiter join is the body's**, the same theorem one word pair over. -/
theorem s1_delimJoin (k : Ctx) :
    bv (bv (bv (shlUpW (zext64W (bv32 (delimHiW k))))) ||| bv (zext64W (bv32 (delimLoW k))))
      = joinW (delimLoW k) (delimHiW k) := by
  rw [bv32_eq, bv32_eq]
  exact joinBody_eq _ _


/-! ### The control word and the six stores

The control word is the raw quote word's shape at `ult … 0x20`: a second
`shufflevector`/`bitcast` pair over the same two loads, then a sixty-four-lane
`icmp`.  The stores are the five `i64` words and the one `<64 x i1>` mask, each
stated at the slot the emission writes. -/

/-- `%9 = shufflevector <4 x i64> %0, <4 x i64> %1, <8 x i32> <0 … 7>`. -/
theorem s1_shuffle9 (env : Env) (s : State) (k : Ctx)
    (h0 : lookupName env "%0" = some (.vec 4 64 (unpackLanes 64 4 (loWord k))))
    (h1 : lookupName env "%1" = some (.vec 4 64 (unpackLanes 64 4 (hiWord k)))) :
    evalInstr s1Calls (withEnv env s)
        (.shuffleVec "%9" 4 64 (.reg "%0") (.reg "%1") [0, 1, 2, 3, 4, 5, 6, 7]) =
      some (withEnv (("%9", .vec 8 64 (unpackLanes 64 4 (loWord k) ++
        unpackLanes 64 4 (hiWord k))) :: env) s) := by
  rw [evalInstr_shuffleVec
    (ha := by simp only [withEnv, evalOperand, h0])
    (hb := by simp only [withEnv, evalOperand, h1])
    (h1 := vecLanes_self (unpackLanes_length 64 4 (loWord k)))
    (h2 := vecLanes_self (unpackLanes_length 64 4 (hiWord k)))
    (hm := mapM_pick8 (unpackLanes_length 64 4 (loWord k))
      (unpackLanes_length 64 4 (hiWord k)))]
  rfl

/-- `%10 = bitcast <8 x i64> %9 to <64 x i8>`. -/
theorem s1_bitcast10 (env : Env) (s : State) (k : Ctx)
    (h9 : lookupName env "%9" = some (.vec 8 64 (unpackLanes 64 4 (loWord k) ++
      unpackLanes 64 4 (hiWord k)))) :
    evalInstr s1Calls (withEnv env s) (.vecBitcast "%10" 8 64 64 8 (.reg "%9")) =
      some (withEnv (("%10", .vec 64 8 (blockLanes k)) :: env) s) := by
  rw [evalInstr_vecBitcast (hv := by simp only [withEnv, evalOperand, h9])
    (hl := vecLanes_self
      (l := unpackLanes 64 4 (loWord k) ++ unpackLanes 64 4 (hiWord k))
      (by simp [unpackLanes_length])) (hwidth := by decide)]
  simp only [withEnv, State.bind, bitcastVecLanes]
  rw [packLanes_join k]

/-- `%11 = icmp ult <64 x i8> %10, splat (i8 32)`. -/
theorem s1_icmp11 (env : Env) (s : State) (k : Ctx)
    (h10 : lookupName env "%10" = some (.vec 64 8 (blockLanes k))) :
    evalInstr s1Calls (withEnv env s)
        (.icmpVec "%11" .ult 64 8 (.reg "%10") (splatOf 64 8 32)) =
      some (withEnv (("%11", .vec 64 1 (controlLanes k)) :: env) s) := by
  rw [evalInstr_icmpVec
    (ha := by simp only [withEnv, evalOperand, h10])
    (vb := .vec 64 8 (List.replicate 64 (BitVec.ofInt 8 32)))
    (hb := by simp only [withEnv, evalOperand, splatOf, Const.toValue])
    (h1 := vecLanes_self (blockLanes_length k))
    (h2 := vecLanes_self (l := List.replicate 64 (BitVec.ofInt 8 32))
      (by simp [List.length_replicate]))]
  rfl

/-- `store i64 %r, ptr %p`: an eight-byte write at the slot, parametric in the
source word and the slot. -/
theorem s1_storeInt64 (env : Env) (s : State) (r p : String) (x : BitVec 64) (a : Nat)
    (hv : lookupName env r = some (.int 64 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr s1Calls (withEnv env s) (.store (.int 64) (.reg r) (.reg p)) =
      some (withEnv env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  rw [evalInstr_store (vv := .int 64 x) (a := a)
    (s' := withEnv env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) })
    (hv := by simp only [withEnv, evalOperand, hv])
    (hp := by simp only [withEnv, evalOperand, hp])
    (hs := by simp [storeValue, withEnv])]

/-- `store <64 x i1> %r, ptr %p`: the control mask's own eight-byte write. -/
theorem s1_storeVec1 (env : Env) (s : State) (r p : String) (lanes : List (BitVec 1))
    (a : Nat) (hlen : lanes.length = 64)
    (hv : lookupName env r = some (.vec 64 1 lanes))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr s1Calls (withEnv env s) (.store (.vec 64 (.int 1)) (.reg r) (.reg p)) =
      some (withEnv env
        { s with mem := writeBytes s.mem a (natToBytes (packLanes lanes) 8) }) := by
  rw [evalInstr_store (vv := .vec 64 1 lanes) (a := a)
    (s' := withEnv env { s with mem := writeBytes s.mem a (natToBytes (packLanes lanes) 8) })
    (hv := by simp only [withEnv, evalOperand, hv])
    (hp := by simp only [withEnv, evalOperand, hp])
    (hs := by simp [storeValue, withEnv, hlen])]


/-- `%ws2 = getelementptr i8, ptr %o, i64 24`. -/
theorem s1_wsGep (env : Env) (s : State) (k : Ctx)
    (ho : lookupName env "%o" = some (.ptr k.o)) :
    evalInstr s1Calls (withEnv env s) (.gep "%ws2" (.int 8) (.reg "%o") (lit 64 24)) =
      some (withEnv (("%ws2", .ptr (k.o + 24)) :: env) s) := by
  rw [evalInstr_gep_i8 (base := .reg "%o") (off := lit 64 24) (a := k.o) (w := 64)
    (n := BitVec.ofInt 64 24)
    (hb := by simp only [withEnv, evalOperand, ho])
    (ho := by simp only [withEnv, evalOperand, lit, Const.toValue]) (hpos := by decide)]
  simp only [show (BitVec.signExtend 64 (BitVec.ofInt 64 24)).toNat = 24 from by decide,
    withEnv, State.bind]

/-- `%ctl3 = getelementptr i8, ptr %o, i64 40`. -/
theorem s1_ctlGep (env : Env) (s : State) (k : Ctx)
    (ho : lookupName env "%o" = some (.ptr k.o)) :
    evalInstr s1Calls (withEnv env s) (.gep "%ctl3" (.int 8) (.reg "%o") (lit 64 40)) =
      some (withEnv (("%ctl3", .ptr (k.o + 40)) :: env) s) := by
  rw [evalInstr_gep_i8 (base := .reg "%o") (off := lit 64 40) (a := k.o) (w := 64)
    (n := BitVec.ofInt 64 40)
    (hb := by simp only [withEnv, evalOperand, ho])
    (ho := by simp only [withEnv, evalOperand, lit, Const.toValue]) (hpos := by decide)]
  simp only [show (BitVec.signExtend 64 (BitVec.ofInt 64 40)).toNat = 40 from by decide,
    withEnv, State.bind]

/-! ### The remaining slot addresses, and the memory facts the readback needs -/

/-- `%delim = getelementptr i8, ptr %o, i64 8`. -/
theorem s1_delimGep (env : Env) (s : State) (k : Ctx)
    (ho : lookupName env "%o" = some (.ptr k.o)) :
    evalInstr s1Calls (withEnv env s) (.gep "%delim" (.int 8) (.reg "%o") (lit 64 8)) =
      some (withEnv (("%delim", .ptr (k.o + 8)) :: env) s) := by
  rw [evalInstr_gep_i8 (base := .reg "%o") (off := lit 64 8) (a := k.o) (w := 64)
    (n := BitVec.ofInt 64 8)
    (hb := by simp only [withEnv, evalOperand, ho])
    (ho := by simp only [evalOperand, lit, Const.toValue]) (hpos := by decide)]
  simp only [show (BitVec.signExtend 64 (BitVec.ofInt 64 8)).toNat = 8 from by decide,
    withEnv, State.bind]

/-- `%in_string = getelementptr i8, ptr %o, i64 16`. -/
theorem s1_inStringGep (env : Env) (s : State) (k : Ctx)
    (ho : lookupName env "%o" = some (.ptr k.o)) :
    evalInstr s1Calls (withEnv env s) (.gep "%in_string" (.int 8) (.reg "%o") (lit 64 16)) =
      some (withEnv (("%in_string", .ptr (k.o + 16)) :: env) s) := by
  rw [evalInstr_gep_i8 (base := .reg "%o") (off := lit 64 16) (a := k.o) (w := 64)
    (n := BitVec.ofInt 64 16)
    (hb := by simp only [withEnv, evalOperand, ho])
    (ho := by simp only [evalOperand, lit, Const.toValue]) (hpos := by decide)]
  simp only [show (BitVec.signExtend 64 (BitVec.ofInt 64 16)).toNat = 16 from by decide,
    withEnv, State.bind]

/-- `%backslash = getelementptr i8, ptr %o, i64 32`. -/
theorem s1_backslashGep (env : Env) (s : State) (k : Ctx)
    (ho : lookupName env "%o" = some (.ptr k.o)) :
    evalInstr s1Calls (withEnv env s) (.gep "%backslash" (.int 8) (.reg "%o") (lit 64 32)) =
      some (withEnv (("%backslash", .ptr (k.o + 32)) :: env) s) := by
  rw [evalInstr_gep_i8 (base := .reg "%o") (off := lit 64 32) (a := k.o) (w := 64)
    (n := BitVec.ofInt 64 32)
    (hb := by simp only [withEnv, evalOperand, ho])
    (ho := by simp only [evalOperand, lit, Const.toValue]) (hpos := by decide)]
  simp only [show (BitVec.signExtend 64 (BitVec.ofInt 64 32)).toNat = 32 from by decide,
    withEnv, State.bind]

/-- A write that ends at or below an address does not disturb it. -/
theorem readByte_writeBytes_above (m : Mem) :
    ∀ (bs : List UInt8) {start addr : Nat}, start + bs.length ≤ addr →
      readByte (writeBytes m start bs) addr = readByte m addr
  | [], _, _, _ => by simp only [writeBytes]
  | b :: bs, start, addr, h => by
      simp only [writeBytes]
      have h' : (start + 1) + bs.length ≤ addr := by
        simp only [List.length_cons] at h; omega
      rw [readByte_writeBytes_above (writeByte m start b) bs h']
      exact readByte_writeByte_other m b (by omega)

/-- A sequence read entirely above a written range is unaffected by it. -/
theorem readBytes_writeBytes_above (m : Mem) :
    ∀ (bs : List UInt8) (n addr start : Nat), start + bs.length ≤ addr →
      readBytes (writeBytes m start bs) addr n = readBytes m addr n
  | bs, 0, _, _, _ => by simp only [readBytes]
  | bs, n + 1, addr, start, h => by
      simp only [readBytes]
      rw [readByte_writeBytes_above m bs h]
      cases hr : readByte m addr with
      | none => rfl
      | some b =>
          rw [readBytes_writeBytes_above m bs n (addr + 1) start (by omega)]

/-- Two consecutive reads compose: the bytes of the two together are the bytes of
the range.  This is `readBytes_split` read in the other direction. -/
theorem readBytes_app (m : Mem) :
    ∀ (n k addr : Nat) {a b : List UInt8}, readBytes m addr n = some a →
      readBytes m (addr + n) k = some b → readBytes m addr (n + k) = some (a ++ b)
  | 0, k, addr, a, b, ha, hb => by
      simp only [readBytes, Option.some.injEq] at ha
      subst ha
      simpa using hb
  | n + 1, k, addr, a, b, ha, hb => by
      rw [show addr + (n + 1) = (addr + 1) + n from by omega] at hb
      rw [show n + 1 + k = (n + k) + 1 from by omega]
      simp only [readBytes] at ha ⊢
      cases hr : readByte m addr with
      | none => rw [hr] at ha; simp at ha
      | some b0 =>
          cases hrest : readBytes m (addr + 1) n with
          | none => rw [hr, hrest] at ha; simp at ha
          | some rest =>
              rw [hr, hrest] at ha
              simp only [Option.some.injEq] at ha
              subst ha
              have ih := readBytes_app m n k (addr + 1) hrest hb
              rw [ih]
              rfl

/-- A `32 + 32` read that is absent, whose first half reads back, is absent at
its second half: the two halves compose, so a readable second half would make the
whole range readable. -/
theorem readBytes_second_none {m : Mem} {addr : Nat} {a : List UInt8}
    (h1 : readBytes m addr 32 = some a) (h : readBytes m addr 64 = none) :
    readBytes m (addr + 32) 32 = none := by
  cases h2 : readBytes m (addr + 32) 32 with
  | none => rfl
  | some b =>
      have hboth := readBytes_app m 32 32 addr h1 h2
      rw [show (32 : Nat) + 32 = 64 from rfl, h] at hboth
      exact absurd hboth (by simp)


/-- A `denoteCode` step whose instruction is undefined is undefined. -/
theorem denoteCode_cons_none (calls : Calls) (i : Instr) (is : List Instr) (s : State)
    (h : evalInstr calls s i = none) (hi : i.isPhi = false := by rfl) :
    denoteCode calls (i :: is) s = none :=
  LeanLLVM.denoteCode_cons_none calls i is s h hi

/-- The unit's instruction list, at its first three instructions: the two block
loads and the address between them, split off the rest. -/
theorem s1MasksInstrs_three :
    s1MasksInstrs =
      .load "%0" (.vec 4 (.int 64)) (.reg "%p") ::
      .gep "%add.ptr" (.int 8) (.reg "%p") (lit 64 32) ::
      .load "%1" (.vec 4 (.int 64)) (.reg "%add.ptr") ::
      s1MasksInstrs.tail.tail.tail := rfl

/-- The block's first load is undefined when the block is unreadable. -/
theorem s1_load0_none (env : Env) (s : State) (k : Ctx)
    (hp : lookupName env "%p" = some (.ptr k.p))
    (hl0 : readBytes s.mem k.p 32 = none) :
    evalInstr s1Calls (withEnv env s) (.load "%0" (.vec 4 (.int 64)) (.reg "%p")) = none := by
  have hload : loadValue s.mem (.vec 4 (.int 64)) k.p = none :=
    loadValue_vec_int_of_readBytes_none (by decide) (by decide) hl0
  simp only [evalInstr, evalOperand, withEnv, hp, hload]

/-- The block's first load, with the bytes as read rather than a named half: what
the widening below needs, since a readable first half is not known to be a `Block32`
before the read's length is known. -/
theorem s1_load0_bytes (env : Env) (s : State) (p : Nat) {bs : List UInt8}
    (hp : lookupName env "%p" = some (.ptr p))
    (hl : readBytes s.mem p 32 = some bs) :
    evalInstr s1Calls (withEnv env s) (.load "%0" (.vec 4 (.int 64)) (.reg "%p")) =
      some (withEnv (("%0", .vec 4 64 (unpackLanes 64 4 (bytesToNat bs))) :: env) s) := by
  rw [evalInstr_load (p := .reg "%p") (a := p)
    (by simp only [withEnv, evalOperand, hp])
    (loadValue_vec_int (by decide) (by decide) hl)]
  rfl

/-- The block's second load is undefined when the block's second half is
unreadable. -/
theorem s1_load1_none (env : Env) (s : State) (k : Ctx)
    (hptr : lookupName env "%add.ptr" = some (.ptr (k.p + 32)))
    (hl1 : readBytes s.mem (k.p + 32) 32 = none) :
    evalInstr s1Calls (withEnv env s) (.load "%1" (.vec 4 (.int 64)) (.reg "%add.ptr")) = none := by
  have hload : loadValue s.mem (.vec 4 (.int 64)) (k.p + 32) = none :=
    loadValue_vec_int_of_readBytes_none (by decide) (by decide) hl1
  simp only [evalInstr, evalOperand, withEnv, hptr, hload]

/-- The entry block is the only block, so one step is the body and its terminator. -/
theorem step_s1Masks (s : State) (hpc : s.pc = "entry") :
    step s1Calls s1MasksFunction s =
      (match denoteCode s1Calls s1MasksInstrs s with
       | none => .ub
       | some s' => .ret none s') := by
  unfold step
  rw [hpc]
  rfl

/-- **The unit is undefined when the block is unreadable**, through whichever of
the body's two block loads is the one whose bytes are absent: a load whose bytes
are absent is `ub`, not a word of zeroes.

The hypothesis is the whole window the body reads.  The body performs both 32-byte
loads unconditionally, so an absent second half is not a case it survives: when the
first half reads back and the second does not, the second load is the `ub`.

This is what makes `s1_masks_refines`'s premise mean something — without it the
refinement could hold vacuously on an unreadable block. -/
theorem s1_masks_undefined_of_no_read (env : Env) (s : State) (k : Ctx)
    (hpc : s.pc = "entry")
    (hp : lookupName env "%p" = some (.ptr k.p))
    (h64 : readBytes s.mem k.p 64 = none) :
    runFuel s1Calls 1 s1MasksFunction (withEnv env s) = some .ub := by
  have hden : denoteCode s1Calls s1MasksInstrs (withEnv env s) = none := by
    rw [s1MasksInstrs_three]
    rcases h32 : readBytes s.mem k.p 32 with _ | bs
    · exact denoteCode_cons_none _ _ _ _ (s1_load0_none env s k hp h32)
    · have hl1 : readBytes s.mem (k.p + 32) 32 = none := readBytes_second_none h32 h64
      have hl0 : readBytes s.mem k.p 32 = some bs := h32
      rw [denoteCode_cons_of _ _ _ _ _ (s1_load0_bytes env s k.p hp hl0)]
      rw [denoteCode_cons_of _ _ _ _ _
        (s1_ptr (("%0", .vec 4 64 (unpackLanes 64 4 (bytesToNat bs))) :: env) s k
          (lookupName_cons_ne _ _ (by decide) |>.trans hp))]
      exact denoteCode_cons_none _ _ _ _
        (s1_load1_none _ s k (lookupName_cons_self _ _ _) hl1)
  have hstep : step s1Calls s1MasksFunction (withEnv env s) = .ub := by
    rw [step_s1Masks _ (by rw [withEnv]; exact hpc), hden]
  unfold runFuel
  rw [hstep]


/-! ### The body's run

The composition of the whole body: one `denoteCode_cons_of` per instruction, each
step's operand lookups resolved by `s1_lk` — peel the cells bound after the
register, then take the cell, or the caller's environment for `%p`, `%c` and `%o`.

The conclusion is about the **memory** and nothing else: the environment the run
leaves is 115 cells of intermediate values, and no later clause reads it.

The list is **115** instructions, not 114: the count is the pinned list's own, and
one `denoteCode_cons_of` per entry is what closes.

The projection is measured rather than preferred.  Stated with the environment
existential — `∃ env', denoteCode … = some (withEnv env' …)` — the closing `rfl` has
to compare two 115-deep record-update stacks field by field, and
`set_option diagnostics true` attributed **604 256 `State.mem` unfoldings** to that
one check: 400 k heartbeats and 16 s, and 2 M heartbeats and 64 s, both still timing
out.  At the memory level the writes are syntactic: the same file composes and
compares in 9 s at the **default** heartbeat budget, and each of the nine writes is
read back by its own clause below. -/

/-- Resolve a register in the run's environment: peel the cells bound after it, then
take the cell it is, or the caller's environment when it is a parameter. -/
macro "s1_lk " h:term : tactic =>
  `(tactic| ((repeat rw [lookupName_cons_ne _ _ (by decide)]); (first
      | exact lookupName_cons_self _ _ _
      | exact $h)))

/-- The environment of a run is not observed by `State.mem`. -/
theorem withEnv_mem (env : Env) (s : State) : (withEnv env s).mem = s.mem := rfl

/-- `%or5.i.i`'s word, the delimiter join. -/
def or5W (k : Ctx) : BitVec 64 :=
  bv (bv (bv (shlUpW (zext64W (bv32 (delimHiW k))))) ||| bv (zext64W (bv32 (delimLoW k))))

/-- `%or.i.i`'s word, the whitespace join. -/
def orWsW (k : Ctx) : BitVec 64 :=
  bv (bv (bv (shlUpW (zext64W (bv32 (wsHiW k))))) ||| bv (zext64W (bv32 (wsLoW k))))

theorem or5W_eq (k : Ctx) : or5W k = joinW (delimLoW k) (delimHiW k) := s1_delimJoin k

theorem orWsW_eq (k : Ctx) : orWsW k = joinW (wsLoW k) (wsHiW k) := s1_wsJoin k

/-- The control mask is sixty-four lanes: `%11` is `<64 x i1>`, so its store is one
eight-byte write. -/
theorem controlLanes_length (k : Ctx) : (controlLanes k).length = 64 := by
  simp only [controlLanes, List.length_map, List.length_zip, blockLanes_length,
    List.length_replicate, Nat.min_self]

/-- The `%41` load still sees the carry slot's in-string word: the two carry
words the body has already written are below it. -/
theorem readImCarry_after_stores (k : Ctx) (m : Mem) :
    readBytes (writeBytes (writeBytes m (k.c + 8) (natToBytes (escAnd26W k).toNat 8))
        k.c (natToBytes (escShr16W k).toNat 8)) (k.c + 16) 8
      = readBytes m (k.c + 16) 8 :=
  (readBytes_writeBytes_above (writeBytes m (k.c + 8) (natToBytes (escAnd26W k).toNat 8))
      (natToBytes (escShr16W k).toNat 8) 8 (k.c + 16) k.c
      (by rw [natToBytes_length]; omega)).trans
    (readBytes_writeBytes_above m (natToBytes (escAnd26W k).toNat 8) 8 (k.c + 16) (k.c + 8)
      (by rw [natToBytes_length]; omega))

/-- The memory the unit leaves: the two carry words and the in-string word at the
carry slot, then the six output words, each an eight-byte write at the slot it is
stored to. -/
def s1SlotMem (k : Ctx) (m : Mem) : Mem :=
  writeBytes
    (writeBytes
      (writeBytes
        (writeBytes
          (writeBytes
            (writeBytes
              (writeBytes
                (writeBytes
                  (writeBytes m (k.c + 8) (natToBytes (escAnd26W k).toNat 8))
                  k.c (natToBytes (escShr16W k).toNat 8))
                (k.c + 16) (natToBytes (imSignW k).toNat 8))
              k.o (natToBytes (andQuoteW k).toNat 8))
            (k.o + 8) (natToBytes (or5W k).toNat 8))
          (k.o + 16) (natToBytes (inStringWord k).toNat 8))
        (k.o + 24) (natToBytes (orWsW k).toNat 8))
      (k.o + 32) (natToBytes (bsW k).toNat 8))
    (k.o + 40) (natToBytes (packLanes (controlLanes k)) 8)

/-- **The body's run, composed.**  Every instruction of the pinned list executed in
order; the memory it leaves is `s1SlotMem`, the two carry words, the in-string word
and the six output words. -/
theorem s1_run (env : Env) (s : State) (k : Ctx)
    (hp : lookupName env "%p" = some (.ptr k.p))
    (hc : lookupName env "%c" = some (.ptr k.c))
    (ho : lookupName env "%o" = some (.ptr k.o))
    (hl0 : readBytes s.mem k.p 32 = some (List.ofFn k.lo))
    (hl1 : readBytes s.mem (k.p + 32) 32 = some (List.ofFn k.hi))
    (hd0 : readBytes s.mem k.c 8 = some (natToBytes (if k.opened then 1 else 0) 8))
    (hd1 : readBytes s.mem (k.c + 8) 8 = some (natToBytes (if k.ppar then 1 else 0) 8))
    (hd2 : readBytes s.mem (k.c + 16) 8
      = some (natToBytes (if k.st.inside then 0xFFFFFFFFFFFFFFFF else 0) 8)) :
    Option.map State.mem (denoteCode s1Calls s1MasksInstrs (withEnv env s))
      = some (s1SlotMem k s.mem) := by
  simp only [s1MasksInstrs, shuffle64, pshufb]

  rw [denoteCode_cons_of _ _ _ _ _ (s1_load0 _ _ k (by s1_lk hp) hl0)]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_ptr _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_load1 _ _ k (by s1_lk hp) hl1)]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcast2 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcast3 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_shuffle4 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcast5 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_icmp6 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_quote _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_backLoCmp _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_backLoMask _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_zext9 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_backHiCmp _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_backHiMask _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_zext12 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_shl13 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_or14 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_shuffle9 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcast10 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_icmp11 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcastHalf _ _ "%0" "%12" (loWord k) (loWord_lt k) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_shr4 _ _ "%12" "%13" (loWord k) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_andNib _ _ "%2" "%14" (loLanes k) (loLanes_length k) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_pshufb _ _ "%14" "%15" loTab loTabV (nibLanes (loLanes k)) (by decide) loTabV_eq (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcast8 _ _ "%13" "%16" (loWord k) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_andHiNib _ _ "%16" "%17" (loWord k) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_pshufb _ _ "%17" "%18" hiTab hiTabV (hiNibbleLanes (loWord k)) (by decide) hiTabV_eq (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_andTables _ _ "%18" "%15" "%and.i2831.i.i.i" (tabHiLanes k) (tabLoLanes k) (by simp [tabHiLanes, pshufbLanes_length, hiNibbleLanes_length]) (by simp [tabLoLanes, pshufbLanes_length, nibLanes_length, loLanes_length]) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_and63 _ _ "%and.i2831.i.i.i" "%19" (andWordLanes k) (by rw [andWordLanes_length]) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_icmpEq0 _ _ "%19" "%cmp.i25.i.i.i" (sWordLanes k) (by rw [sWordLanes_length]) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcastMask32 _ _ "%cmp.i25.i.i.i" "%20" (cmpWordLanes k) (by simp [cmpWordLanes, eq0Lanes, sWordLanes_length]) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_compl _ _ "%20" "%not.i.i.i" (BitVec.ofNat 32 (lanesToNat (cmpWordLanes k))) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_icmpUlt64 _ _ "%and.i2831.i.i.i" "%cmp.i.i.i.i" (andWordLanes k) (by rw [andWordLanes_length]) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcastMask32 _ _ "%cmp.i.i.i.i" "%21" (ult64Lanes (andWordLanes k)) (by simp [ult64Lanes, andWordLanes_length]) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_compl _ _ "%21" "%not18.i.i.i" (BitVec.ofNat 32 (lanesToNat (ult64Lanes (andWordLanes k)))) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcastHalf _ _ "%1" "%22" (hiWord k) (hiWord_lt k) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_shr4 _ _ "%22" "%23" (hiWord k) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_andNib _ _ "%3" "%24" (hiLanes k) (hiLanes_length k) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_pshufb _ _ "%24" "%25" loTab loTabV (nibLanes (hiLanes k)) (by decide) loTabV_eq (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcast8 _ _ "%23" "%26" (hiWord k) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_andHiNib _ _ "%26" "%27" (hiWord k) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_pshufb _ _ "%27" "%28" hiTab hiTabV (hiNibbleLanes (hiWord k)) (by decide) hiTabV_eq (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_andTables _ _ "%28" "%25" "%and.i2831.i6.i.i" (tabHiLanesHi k) (tabLoLanesHi k) (by simp [tabHiLanesHi, pshufbLanes_length, hiNibbleLanes_length]) (by simp [tabLoLanesHi, pshufbLanes_length, nibLanes_length, hiLanes_length]) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_and63 _ _ "%and.i2831.i6.i.i" "%29" (andWordLanesHi k) (by rw [andWordLanesHi_length]) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_icmpEq0 _ _ "%29" "%cmp.i25.i7.i.i" (sWordLanesHi k) (by rw [sWordLanesHi_length]) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcastMask32 _ _ "%cmp.i25.i7.i.i" "%30" (cmpWordLanesHi k) (by simp [cmpWordLanesHi, eq0Lanes, sWordLanesHi_length]) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_compl _ _ "%30" "%not.i8.i.i" (BitVec.ofNat 32 (lanesToNat (cmpWordLanesHi k))) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_icmpUlt64 _ _ "%and.i2831.i6.i.i" "%cmp.i.i9.i.i" (andWordLanesHi k) (by rw [andWordLanesHi_length]) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_bitcastMask32 _ _ "%cmp.i.i9.i.i" "%31" (ult64Lanes (andWordLanesHi k)) (by simp [ult64Lanes, andWordLanesHi_length]) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_compl _ _ "%31" "%not18.i10.i.i" (BitVec.ofNat 32 (lanesToNat (ult64Lanes (andWordLanesHi k)))) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_zextJoin _ _ "%not18.i.i.i" "%conv.i.i" (bv32 (wsLoW k)) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_zextJoin _ _ "%not18.i10.i.i" "%conv1.i.i" (bv32 (wsHiW k)) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_shlJoin _ _ "%conv1.i.i" "%shl.i.i" (zext64W (bv32 (wsHiW k))) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_orJoin _ _ "%shl.i.i" "%conv.i.i" "%or.i.i" (bv (shlUpW (zext64W (bv32 (wsHiW k))))) (zext64W (bv32 (wsLoW k))) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_zextJoin _ _ "%not.i.i.i" "%conv2.i.i" (bv32 (delimLoW k)) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_zextJoin _ _ "%not.i8.i.i" "%conv3.i.i" (bv32 (delimHiW k)) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_shlJoin _ _ "%conv3.i.i" "%shl4.i.i" (zext64W (bv32 (delimHiW k))) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_orJoin _ _ "%shl4.i.i" "%conv2.i.i" "%or5.i.i" (bv (shlUpW (zext64W (bv32 (delimHiW k))))) (zext64W (bv32 (delimLoW k))) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escGep _ _ k (by s1_lk hc))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escShl _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escOpenLoad _ _ k (by s1_lk hc) hd0)]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escOr62 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escNot _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escAndStarts _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escAnd1 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escAnd2 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escOr3 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escShr _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escNot4 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escAnd5 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escShl6 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escPparLoad _ _ k (by s1_lk hp) hd1)]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escAnd7 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escXorEven _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escPext1 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escPext2 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escXor36 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escNot10 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escPdep _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escCmp63 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escTobool _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escOrCond _ _ k (escCmp63L k) (bv1_zero_one _) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escCond24 _ _ k (escOrCondL k) (bv1_zero_one _) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escNot17 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escCtlz _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escShr16 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escNot12 _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escAnd39 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escAnd14 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escOr15 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escXor25 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_escAnd26 _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_storeInt64 _ _ "%and26.i.i" "%esc_ppar.i" (escAnd26W k) (k.c + 8) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_storeInt64 _ _ "%shr16.i.i" "%c" (escShr16W k) k.c (by s1_lk hp) (by s1_lk hc))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_andNotEsc _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_andQuote _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_vecInit _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_pclmul _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_vecext _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_imGep _ _ k (by s1_lk hc))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_imLoad _ _ k (by s1_lk hp) (by rw [readImCarry_after_stores k]; exact hd2))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_inString _ _ k (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_imSign _ _ k (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_storeInt64 _ _ "%shr.i" "%im_carry.i" (imSignW k) (k.c + 16) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_storeInt64 _ _ "%and.i" "%o" (andQuoteW k) k.o (by s1_lk hp) (by s1_lk ho))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_delimGep _ _ k (by s1_lk ho))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_storeInt64 _ _ "%or5.i.i" "%delim" (or5W k) (k.o + 8) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_inStringGep _ _ k (by s1_lk ho))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_storeInt64 _ _ "%xor.i" "%in_string" (inStringWord k) (k.o + 16) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_wsGep _ _ k (by s1_lk ho))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_storeInt64 _ _ "%or.i.i" "%ws2" (orWsW k) (k.o + 24) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_backslashGep _ _ k (by s1_lk ho))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_storeInt64 _ _ "%or14.i" "%backslash" (bsW k) (k.o + 32) (by s1_lk hp) (by s1_lk hp))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_ctlGep _ _ k (by s1_lk ho))]
  rw [denoteCode_cons_of _ _ _ _ _ (s1_storeVec1 _ _ "%11" "%ctl3" (controlLanes k) (k.o + 40) (controlLanes_length k) (by s1_lk hp) (by s1_lk hp))]
  rw [show ∀ (x : State), denoteCode s1Calls [] x = some x from fun x => rfl]
  simp only [Option.map_some, withEnv_mem, s1SlotMem]

/-! ### The slot readback

`s1SlotMem` is nine eight-byte writes: the two carry words and the in-string word at
the carry slot, then the six output words.  Each was written at exactly the address
read below, so the read either meets its own write or misses a write on one side of
it, and three lemmas peel the stack without unfolding any write's contents. -/

/-- A read at the address just written returns the written bytes. -/
theorem readBytes_slot_same (m : Mem) (addr : Nat) (v : Nat) :
    readBytes (writeBytes m addr (natToBytes v 8)) addr 8 = some (natToBytes v 8) := by
  show readBytes (writeBytes m addr (natToBytes v 8)) addr (natToBytes v 8).length
      = some (natToBytes v 8)
  exact readBytes_writeBytes_same m (natToBytes v 8)

/-- A read entirely below a write is unaffected by it. -/
theorem readBytes_slot_below (m : Mem) (start addr : Nat) (v : Nat)
    (h : addr + 8 ≤ start) :
    readBytes (writeBytes m start (natToBytes v 8)) addr 8 = readBytes m addr 8 :=
  readBytes_writeBytes_below m (natToBytes v 8) 8 addr start h

/-- A read entirely above a write is unaffected by it. -/
theorem readBytes_slot_above (m : Mem) (start addr : Nat) (v : Nat)
    (h : start + 8 ≤ addr) :
    readBytes (writeBytes m start (natToBytes v 8)) addr 8 = readBytes m addr 8 :=
  readBytes_writeBytes_above m (natToBytes v 8) 8 addr start h

/-- A single byte outside a write's range is unaffected by it. -/
theorem readByte_slot_outside (m : Mem) (start addr : Nat) (v : Nat)
    (h : addr < start ∨ start + 8 ≤ addr) :
    readByte (writeBytes m start (natToBytes v 8)) addr = readByte m addr := by
  rcases h with h | h
  · exact readByte_writeBytes_below m (natToBytes v 8) h
  · exact readByte_writeBytes_above m (natToBytes v 8) h

/-- `%and.i`'s word at `%o`. -/
theorem s1Slot_quote (k : Ctx) (m : Mem) :
    readBytes (s1SlotMem k m) k.o 8 = some (natToBytes (andQuoteW k).toNat 8) := by
  simp only [s1SlotMem]
  rw [readBytes_slot_below _ (k.o + 40) k.o _ (by omega),
    readBytes_slot_below _ (k.o + 32) k.o _ (by omega),
    readBytes_slot_below _ (k.o + 24) k.o _ (by omega),
    readBytes_slot_below _ (k.o + 16) k.o _ (by omega),
    readBytes_slot_below _ (k.o + 8) k.o _ (by omega)]
  exact readBytes_slot_same _ k.o _

/-- `%or5.i.i`'s word at `%delim`. -/
theorem s1Slot_delim (k : Ctx) (m : Mem) :
    readBytes (s1SlotMem k m) (k.o + 8) 8 = some (natToBytes (or5W k).toNat 8) := by
  simp only [s1SlotMem]
  rw [readBytes_slot_below _ (k.o + 40) (k.o + 8) _ (by omega),
    readBytes_slot_below _ (k.o + 32) (k.o + 8) _ (by omega),
    readBytes_slot_below _ (k.o + 24) (k.o + 8) _ (by omega),
    readBytes_slot_below _ (k.o + 16) (k.o + 8) _ (by omega)]
  exact readBytes_slot_same _ (k.o + 8) _

/-- `%xor.i`'s word at `%in_string`. -/
theorem s1Slot_instring (k : Ctx) (m : Mem) :
    readBytes (s1SlotMem k m) (k.o + 16) 8 =
      some (natToBytes (inStringWord k).toNat 8) := by
  simp only [s1SlotMem]
  rw [readBytes_slot_below _ (k.o + 40) (k.o + 16) _ (by omega),
    readBytes_slot_below _ (k.o + 32) (k.o + 16) _ (by omega),
    readBytes_slot_below _ (k.o + 24) (k.o + 16) _ (by omega)]
  exact readBytes_slot_same _ (k.o + 16) _

/-- `%or.i.i`'s word at `%ws2`. -/
theorem s1Slot_space (k : Ctx) (m : Mem) :
    readBytes (s1SlotMem k m) (k.o + 24) 8 = some (natToBytes (orWsW k).toNat 8) := by
  simp only [s1SlotMem]
  rw [readBytes_slot_below _ (k.o + 40) (k.o + 24) _ (by omega),
    readBytes_slot_below _ (k.o + 32) (k.o + 24) _ (by omega)]
  exact readBytes_slot_same _ (k.o + 24) _

/-- `%or14.i`'s word at `%backslash`. -/
theorem s1Slot_backslash (k : Ctx) (m : Mem) :
    readBytes (s1SlotMem k m) (k.o + 32) 8 = some (natToBytes (bsW k).toNat 8) := by
  simp only [s1SlotMem]
  rw [readBytes_slot_below _ (k.o + 40) (k.o + 32) _ (by omega)]
  exact readBytes_slot_same _ (k.o + 32) _

/-- `%11`'s control mask at `%ctl3`. -/
theorem s1Slot_control (k : Ctx) (m : Mem) :
    readBytes (s1SlotMem k m) (k.o + 40) 8 =
      some (natToBytes (packLanes (controlLanes k)) 8) := by
  simp only [s1SlotMem]
  exact readBytes_slot_same _ (k.o + 40) _

/-- `%shr16.i.i`'s word at `%c`, the outgoing run-open bit. -/
theorem s1Slot_open (k : Ctx) (m : Mem) (hdisj : k.c + 24 ≤ k.o) :
    readBytes (s1SlotMem k m) k.c 8 = some (natToBytes (escShr16W k).toNat 8) := by
  simp only [s1SlotMem]
  rw [readBytes_slot_below _ (k.o + 40) k.c _ (by omega),
    readBytes_slot_below _ (k.o + 32) k.c _ (by omega),
    readBytes_slot_below _ (k.o + 24) k.c _ (by omega),
    readBytes_slot_below _ (k.o + 16) k.c _ (by omega),
    readBytes_slot_below _ (k.o + 8) k.c _ (by omega),
    readBytes_slot_below _ k.o k.c _ (by omega),
    readBytes_slot_below _ (k.c + 16) k.c _ (by omega)]
  exact readBytes_slot_same _ k.c _

/-- `%and26.i.i`'s word at `%esc_ppar.i`, the outgoing run parity. -/
theorem s1Slot_ppar (k : Ctx) (m : Mem) (hdisj : k.c + 24 ≤ k.o) :
    readBytes (s1SlotMem k m) (k.c + 8) 8 = some (natToBytes (escAnd26W k).toNat 8) := by
  simp only [s1SlotMem]
  rw [readBytes_slot_below _ (k.o + 40) (k.c + 8) _ (by omega),
    readBytes_slot_below _ (k.o + 32) (k.c + 8) _ (by omega),
    readBytes_slot_below _ (k.o + 24) (k.c + 8) _ (by omega),
    readBytes_slot_below _ (k.o + 16) (k.c + 8) _ (by omega),
    readBytes_slot_below _ (k.o + 8) (k.c + 8) _ (by omega),
    readBytes_slot_below _ k.o (k.c + 8) _ (by omega),
    readBytes_slot_below _ (k.c + 16) (k.c + 8) _ (by omega),
    readBytes_slot_above _ k.c (k.c + 8) _ (by omega)]
  exact readBytes_slot_same _ (k.c + 8) _

/-- `%shr.i`'s word at `%im_carry.i`, the outgoing in-string word. -/
theorem s1Slot_im (k : Ctx) (m : Mem) (hdisj : k.c + 24 ≤ k.o) :
    readBytes (s1SlotMem k m) (k.c + 16) 8 = some (natToBytes (imSignW k).toNat 8) := by
  simp only [s1SlotMem]
  rw [readBytes_slot_below _ (k.o + 40) (k.c + 16) _ (by omega),
    readBytes_slot_below _ (k.o + 32) (k.c + 16) _ (by omega),
    readBytes_slot_below _ (k.o + 24) (k.c + 16) _ (by omega),
    readBytes_slot_below _ (k.o + 16) (k.c + 16) _ (by omega),
    readBytes_slot_below _ (k.o + 8) (k.c + 16) _ (by omega),
    readBytes_slot_below _ k.o (k.c + 16) _ (by omega)]
  exact readBytes_slot_same _ (k.c + 16) _

/-- The carry slot, read back: the three words the body leaves there. -/
theorem s1Slot_carry (k : Ctx) (m : Mem) (hdisj : k.c + 24 ≤ k.o) :
    readBytes (s1SlotMem k m) k.c 24
      = some (natToBytes (escShr16W k).toNat 8 ++
          (natToBytes (escAnd26W k).toNat 8 ++ natToBytes (imSignW k).toNat 8)) := by
  have h16 : readBytes (s1SlotMem k m) (k.c + 8) 16
      = some (natToBytes (escAnd26W k).toNat 8 ++ natToBytes (imSignW k).toNat 8) := by
    rw [show (16 : Nat) = 8 + 8 from by decide]
    rw [readBytes_app _ 8 8 (k.c + 8) (s1Slot_ppar k m hdisj)]
    rw [show (k.c + 8) + 8 = k.c + 16 from by omega]
    exact s1Slot_im k m hdisj
  rw [show (24 : Nat) = 8 + 16 from by decide]
  rw [readBytes_app _ 8 16 k.c (s1Slot_open k m hdisj) h16]

/-! ### The stored words are the specification's

Each clause is one identity: the word the body leaves at a slot, read back, is
`specMask64`'s packing of that slot's predicate, and the six sixty-four-lane
specification masks are those packings joined. -/

/-- The delimiter mask reads no carry: `classWindow`'s `delim` is the packing. -/
theorem specDelimiter64_eq (k : Ctx) :
    specDelimiter64 k.lo k.hi k.st = specMask64 IsDelimB k.lo k.hi := by
  unfold specDelimiter64 classMask64 specMask64
  rw [delimiterMask_eq_maskOfListWith (List.ofFn k.lo) k.st (by simp),
    delimiterMask_eq_maskOfListWith (List.ofFn k.hi) _ (by simp)]
  rfl

/-- The backslash mask reads no carry. -/
theorem specBackslash64_eq (k : Ctx) :
    specBackslash64 k.lo k.hi k.st = specMask64 IsBackslashB k.lo k.hi := by
  unfold specBackslash64 classMask64 specMask64
  rw [backslashMask_eq_maskOfListWith (List.ofFn k.lo) k.st (by simp),
    backslashMask_eq_maskOfListWith (List.ofFn k.hi) _ (by simp)]
  rfl

theorem specSpace64_eq (k : Ctx) :
    specSpace64 k.lo k.hi k.st = specMask64 IsSpaceB k.lo k.hi := rfl

theorem specControl64_eq (k : Ctx) :
    specControl64 k.lo k.hi k.st = specMask64 IsControlB k.lo k.hi := rfl

/-- The control mask's packed word, read as a natural. -/
theorem packLanes_control (k : Ctx) :
    packLanes (controlLanes k) = (specMask64 IsControlB k.lo k.hi).toNat := by
  have hlt : lanesToNat (controlLanes k) < 2 ^ 64 := by
    have h := lanesToNat_lt (controlLanes k)
    simpa [controlLanes_length k] using h
  have h := congrArg BitVec.toNat (s1_control_eq k)
  rw [packLanes_eq_lanesToNat, ← h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The quote word's slot. -/
theorem s1Slot_quote_spec (k : Ctx) (m : Mem)
    (hst : k.st.oddRun = (k.opened && k.ppar)) :
    readBytes (s1SlotMem k m) k.o 8 =
      some (natToBytes (specQuote64 k.lo k.hi k.st).toNat 8) := by
  rw [s1Slot_quote k m, andQuoteW_spec k hst]

/-- The delimiter word's slot. -/
theorem s1Slot_delim_spec (k : Ctx) (m : Mem) :
    readBytes (s1SlotMem k m) (k.o + 8) 8 =
      some (natToBytes (specDelimiter64 k.lo k.hi k.st).toNat 8) := by
  rw [s1Slot_delim k m, or5W_eq k, s1_delimiter_eq k, ← specDelimiter64_eq k]

/-- The in-string word's slot. -/
theorem s1Slot_instring_spec (k : Ctx) (m : Mem)
    (hst : k.st.oddRun = (k.opened && k.ppar)) :
    readBytes (s1SlotMem k m) (k.o + 16) 8 =
      some (natToBytes (specInString64 k.lo k.hi k.st).toNat 8) := by
  rw [s1Slot_instring k m, s1_instring_eq k hst]

/-- The whitespace word's slot. -/
theorem s1Slot_space_spec (k : Ctx) (m : Mem) :
    readBytes (s1SlotMem k m) (k.o + 24) 8 =
      some (natToBytes (specSpace64 k.lo k.hi k.st).toNat 8) := by
  rw [s1Slot_space k m, orWsW_eq k, s1_whitespace_eq k, ← specSpace64_eq k]

/-- The backslash word's slot. -/
theorem s1Slot_backslash_spec (k : Ctx) (m : Mem) :
    readBytes (s1SlotMem k m) (k.o + 32) 8 =
      some (natToBytes (specBackslash64 k.lo k.hi k.st).toNat 8) := by
  rw [s1Slot_backslash k m, bsW_eq_spec k, ← specBackslash64_eq k]

/-- The control mask's slot. -/
theorem s1Slot_control_spec (k : Ctx) (m : Mem) :
    readBytes (s1SlotMem k m) (k.o + 40) 8 =
      some (natToBytes (specControl64 k.lo k.hi k.st).toNat 8) := by
  rw [s1Slot_control k m, packLanes_control k, ← specControl64_eq k]

/-! ### Outside the two slots

Nine eight-byte writes, and a byte in neither slot misses every one of them: below
the write, or at or above its end. -/

/-- A byte outside both slots is not touched by the body. -/
theorem s1Slot_outside (k : Ctx) (m : Mem) (a : Nat)
    (h1 : a < k.c ∨ k.c + 24 ≤ a) (h2 : a < k.o ∨ k.o + 48 ≤ a) :
    readByte (s1SlotMem k m) a = readByte m a := by
  simp only [s1SlotMem]
  rw [readByte_slot_outside _ (k.o + 40) a _ (by omega),
    readByte_slot_outside _ (k.o + 32) a _ (by omega),
    readByte_slot_outside _ (k.o + 24) a _ (by omega),
    readByte_slot_outside _ (k.o + 16) a _ (by omega),
    readByte_slot_outside _ (k.o + 8) a _ (by omega),
    readByte_slot_outside _ k.o a _ (by omega),
    readByte_slot_outside _ (k.c + 16) a _ (by omega),
    readByte_slot_outside _ k.c a _ (by omega),
    readByte_slot_outside _ (k.c + 8) a _ (by omega)]

/-! ### The run, as an outcome

`step_s1Masks` turns the composed body into the single control step, and `runFuel`
at fuel one is that step's `.ret`. -/

/-- **The unit's run leaves `s1SlotMem`.**  One control step, whose memory is the
slot write stack. -/
theorem s1_runFuel (env : Env) (s : State) (k : Ctx)
    (hpc : s.pc = "entry")
    (hp : lookupName env "%p" = some (.ptr k.p))
    (hc : lookupName env "%c" = some (.ptr k.c))
    (ho : lookupName env "%o" = some (.ptr k.o))
    (hl0 : readBytes s.mem k.p 32 = some (List.ofFn k.lo))
    (hl1 : readBytes s.mem (k.p + 32) 32 = some (List.ofFn k.hi))
    (hd0 : readBytes s.mem k.c 8 = some (natToBytes (if k.opened then 1 else 0) 8))
    (hd1 : readBytes s.mem (k.c + 8) 8 = some (natToBytes (if k.ppar then 1 else 0) 8))
    (hd2 : readBytes s.mem (k.c + 16) 8
      = some (natToBytes (if k.st.inside then 0xFFFFFFFFFFFFFFFF else 0) 8)) :
    runFuel s1Calls 1 s1MasksFunction (withEnv env s)
      = some (.ret none (s1SlotMem k s.mem)) := by
  obtain ⟨s', hs', hm⟩ :=
    Option.map_eq_some_iff.mp (s1_run env s k hp hc ho hl0 hl1 hd0 hd1 hd2)
  have hstep : step s1Calls s1MasksFunction (withEnv env s) = .ret none s' := by
    rw [step_s1Masks _ (by simpa [withEnv] using hpc), hs']
  unfold runFuel
  rw [hstep]
  show some (Outcome.ret none s'.mem) = some (Outcome.ret none (s1SlotMem k s.mem))
  rw [hm]

/-! ### The specification's outgoing carry, at 64 lanes -/

/-- The carry the next block inherits, as the lane recursion read at 64. -/
theorem carry64_oddRun_eq (k : Ctx) (hst : k.st.oddRun = (k.opened && k.ppar)) :
    (carry64 k.lo k.hi k.st).oddRun
      = runParityBefore (specMask64 IsBackslashB k.lo k.hi) k.opened k.ppar 64 := by
  unfold carry64
  rw [classWindow_carry (List.ofFn k.hi) ((classWindow (List.ofFn k.lo) k.st).carry)]
  exact oddRun_hi hst 32 (by omega)

/-- The carry the next block inherits, as bit 63 of the body's in-string product. -/
theorem carry64_inside_eq (k : Ctx) (hst : k.st.oddRun = (k.opened && k.ppar)) :
    (carry64 k.lo k.hi k.st).inside
      = (clmul (andQuoteW k) (BitVec.allOnes 64) ^^^ seedVec 64 k.st.inside).getLsbD 63 := by
  unfold carry64
  rw [LeanLLVM.Refinement.Pclmul.specInString64_outgoing_carry_pclmul, ← andQuoteW_spec k hst]

/-! ### Bit `j` of a packed lane list, and the run-open bit -/

/-- The `j`-th bit of a natural, read back as the digit it is. -/
theorem div_pow_two_mod_two (n j : Nat) : n / 2 ^ j % 2 = if n.testBit j then 1 else 0 := by
  have h := Nat.testBit_div_two_pow (n := j) (x := n) (i := 0)
  rw [Nat.zero_add] at h
  rw [← h, Nat.testBit_zero]
  by_cases hc : n / 2 ^ j % 2 = 1
  · simp [hc]
  · have h0 : n / 2 ^ j % 2 = 0 := by
      have := Nat.mod_lt (n / 2 ^ j) (by decide : 0 < 2)
      omega
    simp [h0]

/-- `%shr16.i.i`: the outgoing run-open bit is the high half's top backslash lane. -/
theorem s1_open_spec (k : Ctx) :
    (escShr16W k).toNat = (if IsBackslashB (k.hi ⟨31, by decide⟩) then 1 else 0) := by
  have hbit : (lanesToNat (backHi k)).testBit 31 = IsBackslashB (k.hi ⟨31, by decide⟩) := by
    apply lanesToNat_testBit_bool
    rw [backHi_eq, List.getElem?_ofFn]
    exact dite_eq_left (by decide)
  have hlen : (backHi k).length = 32 := backHi_length k
  have hlt : lanesToNat (backHi k) < 2 ^ 32 := by
    have h := lanesToNat_lt (backHi k)
    rwa [hlen] at h
  have hdiv : lanesToNat (backHi k) / 2 ^ 31 < 2 := by
    have h : (2 : Nat) ^ 32 = 2 ^ 31 * 2 := by
      rw [show (32 : Nat) = 31 + 1 from by decide, Nat.pow_succ]
    omega
  have hlt64 : lanesToNat (backHi k) / 2 ^ 31 < 2 ^ 64 := by omega
  rw [escShr16W, bv_toNat, BitVec.toNat_ushiftRight, conv12W_toNat k,
    Nat.shiftRight_eq_div_pow, ← Nat.mod_eq_of_lt hdiv, div_pow_two_mod_two, hbit]


/-! ### The closed form of the lane recursion -/

/-- `k` flips of a bit: the parity the run recursion accumulates. -/
def flipBits (k : Nat) (b : Bool) : Bool := if k % 2 = 0 then b else !b

theorem flipBits_succ (k : Nat) (b : Bool) : flipBits (k + 1) b = !(flipBits k b) := by
  unfold flipBits
  by_cases h : k % 2 = 0
  · have h1 : (k + 1) % 2 = 1 := by omega
    simp [h, h1]
  · have h1 : (k + 1) % 2 = 0 := by
      have := Nat.mod_lt k (by decide : 0 < 2)
      omega
    simp [h, h1]

/-- The parity test one count up. -/
theorem succ_mod_two_test (n : Nat) : ((n + 1) % 2 == 1) = !(n % 2 == 1) := by
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by
    have := Nat.mod_lt n (by decide : 0 < 2)
    omega
  rcases hn with h0 | h1
  · have h : (n + 1) % 2 = 1 := by omega
    rw [h, h0]; rfl
  · have h : (n + 1) % 2 = 0 := by omega
    rw [h, h1]; rfl

/-- **The lane recursion, in closed form.**  `runParityBefore` at `k` is the parity of
the run of set lanes ending at lane `k - 1`, and the incoming parity survives only
when that run is the whole prefix. -/
theorem runParityBefore_eq {w : Nat} (bs : BitVec w) (o p : Bool) :
    ∀ k, runParityBefore bs o p k
      = if BitLanes.suffixRun bs k = k then flipBits k (o && p)
        else (BitLanes.suffixRun bs k % 2 == 1)
  | 0 => by
      show (o && p) = _
      rw [show BitLanes.suffixRun bs 0 = 0 from rfl]
      simp [flipBits]
  | k + 1 => by
      have ih := runParityBefore_eq bs o p k
      rw [runParityBefore, ih]
      show (if bs.getLsbD k then
          !(if BitLanes.suffixRun bs k = k then flipBits k (o && p)
            else (BitLanes.suffixRun bs k % 2 == 1)) else false) = _
      rw [BitLanes.suffixRun]
      by_cases hb : bs.getLsbD k
      · rw [ite_eq_left hb, ite_eq_left hb]
        by_cases hk : BitLanes.suffixRun bs k = k
        · rw [ite_eq_left hk, ite_eq_left (by omega), flipBits_succ]
        · rw [ite_eq_right hk]
          have hne : BitLanes.suffixRun bs k + 1 ≠ k + 1 := by omega
          rw [ite_eq_right hne, succ_mod_two_test]
      · rw [ite_eq_right hb, ite_eq_right hb]
        have hne : (0 : Nat) ≠ k + 1 := by omega
        rw [ite_eq_right hne]
        rfl


/-- `ashr` by the sign bit is one of two constants: the sign word.

`Classical.choice` enters this module here and at `s1_inside_spec`, and nowhere
else: both carry it, and every theorem whose footprint is wider than
`[propext, Quot.sound]` above them — `s1_masks_refines` included — inherits it
through one of these two.  The carrier is this core's
*bit-to-magnitude* bridge — `BitVec.msb_eq_true_iff_two_mul_ge`,
`msb_eq_false_iff_two_mul_lt` and `le_toNat_iff_getLsbD_eq_true` all carry it — and
the other route (`BitVec.getLsbD_sshiftRight`, `toNat_sshiftRight`,
`sshiftRight_eq_of_msb_false`) carries it too, so no route reaches the sign word
without it.  The lemmas that *are* clean, and are what these rest on: `sshiftRight_eq`,
`BitVec.toNat_ushiftRight` with `Nat.shiftRight_eq_div_pow`, `BitVec.toInt`'s
definition, and `Int.negSucc 0 = -1`. -/
theorem sshiftRight_63 (x : BitVec 64) :
    x.sshiftRight 63 = seedVec 64 (x.getLsbD 63) := by
  rw [BitVec.sshiftRight_eq]
  by_cases hb : x.getLsbD 63 = true
  · have hmsb : x.msb = true := by rw [BitVec.msb_eq_getLsbD_last]; exact hb
    have hge : 2 ^ 63 ≤ x.toNat := by
      have := (BitVec.msb_eq_true_iff_two_mul_ge (x := x)).mp hmsb
      omega
    have hti : x.toInt = Int.negSucc (2 ^ 64 - 1 - x.toNat) := by
      rw [show BitVec.toInt x
          = if 2 * x.toNat < 2 ^ 64 then (x.toNat : Int)
            else (x.toNat : Int) - ((2 ^ 64 : Nat) : Int) from rfl]
      rw [ite_eq_right (by omega)]
      omega
    rw [show seedVec 64 (x.getLsbD 63) = BitVec.allOnes 64 from by rw [hb]; rfl, hti]
    rw [show (Int.negSucc (2 ^ 64 - 1 - x.toNat) >>> 63)
        = Int.negSucc ((2 ^ 64 - 1 - x.toNat) >>> 63) from rfl]
    rw [show (2 ^ 64 - 1 - x.toNat) >>> 63 = 0 from by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (by omega)]
    decide
  · have hf : x.getLsbD 63 = false := by
      cases h : x.getLsbD 63 <;> simp_all
    have hmsbf : x.msb = false := by rw [BitVec.msb_eq_getLsbD_last]; exact hf
    have hlt : 2 * x.toNat < 2 ^ 64 :=
      (BitVec.msb_eq_false_iff_two_mul_lt (x := x)).mp hmsbf
    have hlt63 : x.toNat < 2 ^ 63 := by omega
    have hti : x.toInt = (x.toNat : Int) := by
      rw [show BitVec.toInt x
          = if 2 * x.toNat < 2 ^ 64 then (x.toNat : Int)
            else (x.toNat : Int) - ((2 ^ 64 : Nat) : Int) from rfl]
      rw [ite_eq_left hlt]
    rw [show seedVec 64 (x.getLsbD 63) = (0 : BitVec 64) from by rw [hf]; rfl, hti]
    rw [show ((x.toNat : Int) >>> 63) = ((x.toNat >>> 63 : Nat) : Int) from rfl]
    rw [show x.toNat >>> 63 = 0 from by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt hlt63]
    rfl

/-- `%shr.i`: the outgoing in-string word is the carry the next block inherits. -/
theorem s1_inside_spec (k : Ctx) (hst : k.st.oddRun = (k.opened && k.ppar)) :
    (imSignW k).toNat =
      (if (carry64 k.lo k.hi k.st).inside then 0xFFFFFFFFFFFFFFFF else 0) := by
  rw [carry64_inside_eq k hst]
  unfold imSignW inStringWord vecextW seedW
  rw [bv_toNat, bv_eq, sshiftRight_63]
  by_cases hb : (clmul (andQuoteW k) (BitVec.allOnes 64) ^^^ seedVec 64 k.st.inside).getLsbD 63 = true
  · rw [hb]
    decide
  · have hg : (clmul (andQuoteW k) (BitVec.allOnes 64) ^^^ seedVec 64 k.st.inside).getLsbD 63 = false := by
      cases h : (clmul (andQuoteW k) (BitVec.allOnes 64) ^^^ seedVec 64 k.st.inside).getLsbD 63 <;> simp_all
    rw [hg]
    rfl

/-- `%38`: the trailing run of the backslash mask. -/
theorem escCtlz_toNat (k : Ctx) : (escCtlzW k).toNat = BitLanes.trailingRun (bsW k) := by
  have hb : BitLanes.trailingRun (bsW k) < 2 ^ 64 := by
    have := BitLanes.trailingRun_le (bsW k)
    omega
  rw [escCtlzW, BitVec.toNat_ofNat,
    show escNot17W k = ~~~(bsW k) from by rw [escNot17W, bv_eq, xor_allOnes_eq_not],
    BitLanes.ctlz_not_eq_trailingRun, Nat.mod_eq_of_lt hb]

/-- `%shr16.i.i`: bit 63 of the backslash mask. -/
theorem escShr16_toNat (k : Ctx) :
    (escShr16W k).toNat = (if (bsW k).getLsbD 63 then 1 else 0) := by
  rw [s1_open_spec k, bsW_eq_spec k, show (63 : Nat) = 31 + 32 from by decide]
  rw [specMask64_getLsbD_hi IsBackslashB k.lo k.hi (by decide)]

theorem oneLane_toNat (b : Bool) : (oneLane 64 b).toNat = (if b then 1 else 0) := by
  cases b <;> rfl

theorem oneLane_eq_zero (b : Bool) : oneLane 64 b = (0 : BitVec 64) ↔ ¬ b := by
  cases b <;> simp [oneLane]

theorem escCmp63L_one (k : Ctx) :
    escCmp63L k = 1 ↔ bsW k ≠ BitVec.ofInt 64 (-1) := by
  rw [escCmp63L, evalICmp]
  exact ofBool_eq_one

theorem escToboolL_one (k : Ctx) : escToboolL k = 1 ↔ ¬ k.opened := by
  rw [escToboolL, evalICmp, ofBool_eq_one, show BitVec.ofInt 64 0 = (0 : BitVec 64) from rfl,
    openW, oneLane_eq_zero]

theorem escOrCondL_one (k : Ctx) :
    escOrCondL k = 1 ↔ (bsW k ≠ BitVec.ofInt 64 (-1) ∨ ¬ k.opened) := by
  unfold escOrCondL selBit
  by_cases h : escCmp63L k = 1
  · rw [ite_eq_left h]
    exact ⟨fun _ => Or.inl ((escCmp63L_one k).mp h), fun _ => rfl⟩
  · rw [ite_eq_right h]
    constructor
    · intro hb
      right
      exact (escToboolL_one k).mp hb
    · intro hb
      rcases hb with hb | hb
      · exact absurd ((escCmp63L_one k).mpr hb) h
      · exact (escToboolL_one k).mpr hb

theorem escCond24_toNat (k : Ctx) :
    (escCond24W k).toNat =
      (if (bsW k = BitVec.ofInt 64 (-1) ∧ k.opened) then (if k.ppar then 1 else 0) else 0) := by
  unfold escCond24W sel64 pparW
  by_cases h : escOrCondL k = 1
  · rw [ite_eq_left h, show (0 : BitVec 64).toNat = 0 from rfl]
    have hb : ¬ (bsW k = BitVec.ofInt 64 (-1) ∧ k.opened) := by
      rintro ⟨h1, h2⟩
      rcases (escOrCondL_one k).mp h with h' | h'
      · exact h' h1
      · exact h' h2
    rw [ite_eq_right hb]
  · rw [ite_eq_right h]
    rw [oneLane_toNat]
    have hb : bsW k = BitVec.ofInt 64 (-1) ∧ k.opened := by
      by_cases h1 : bsW k = BitVec.ofInt 64 (-1)
      · by_cases h2 : k.opened
        · exact ⟨h1, h2⟩
        · exact absurd ((escOrCondL_one k).mpr (Or.inr h2)) h
      · exact absurd ((escOrCondL_one k).mpr (Or.inl h1)) h
    rw [ite_eq_left hb]


/-- A suffix run that reaches the lane count is every lane set. -/
theorem suffixRun_full {w : Nat} (m : BitVec w) :
    ∀ n, BitLanes.suffixRun m n = n ↔ ∀ i, i < n → m.getLsbD i = true
  | 0 => by
      rw [show BitLanes.suffixRun m 0 = 0 from rfl]
      exact ⟨fun _ i hi => absurd hi (by omega), fun _ => rfl⟩
  | n + 1 => by
      rw [BitLanes.suffixRun]
      by_cases h : m.getLsbD n
      · rw [ite_eq_left h]
        constructor
        · intro hs i hi
          by_cases hin : i = n
          · subst hin; exact h
          · exact (suffixRun_full m n).mp (by omega) i (by omega)
        · intro hall
          exact congrArg (· + 1) ((suffixRun_full m n).mpr (fun i hi => hall i (by omega)))
      · rw [ite_eq_right h]
        constructor
        · intro hs
          exact absurd hs (by omega)
        · intro hall
          have hf : m.getLsbD n = false := by
            cases hh : m.getLsbD n <;> simp_all
          exact absurd (hall n (by omega)) (by rw [hf]; simp)

theorem eq_allOnes_iff (m : BitVec 64) :
    m = BitVec.allOnes 64 ↔ ∀ i, i < 64 → m.getLsbD i = true := by
  constructor
  · intro h
    subst h
    intro i hi
    exact LeanLLVM.Refinement.BitLanes.allOnes_getLsbD_of_lt hi
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [LeanLLVM.Refinement.BitLanes.allOnes_getLsbD_of_lt hi]
    exact h i hi

/-- The trailing run reaches the lane count exactly on an all-backslash block. -/
theorem trailingRun_eq_64_iff (m : BitVec 64) :
    BitLanes.trailingRun m = 64 ↔ m = BitVec.ofInt 64 (-1) := by
  rw [show BitVec.ofInt 64 (-1) = BitVec.allOnes 64 from rfl, eq_allOnes_iff,
    show BitLanes.trailingRun m = BitLanes.suffixRun m 64 from rfl]
  exact ⟨fun h i hi => (suffixRun_full m 64).mp h i hi,
    fun h => (suffixRun_full m 64).mpr h⟩

/-- A clear top lane leaves no trailing run. -/
theorem trailingRun_eq_zero (m : BitVec 64) (h : m.getLsbD 63 = false) :
    BitLanes.trailingRun m = 0 := by
  show BitLanes.suffixRun m (63 + 1) = 0
  rw [BitLanes.suffixRun, h]
  rfl


/-- `flipBits` at the sixty-four-lane count is the bit itself. -/
theorem flipBits_64 (b : Bool) : flipBits 64 b = b := by
  unfold flipBits
  rw [show (64 : Nat) % 2 = 0 from by decide, ite_eq_left rfl]

/-- **The outgoing run parity.**  `%and26.i.i` — the trailing backslash run's parity
across the block boundary — is the carry the next block is entered with. -/
theorem s1_ppar_spec (k : Ctx) (hst : k.st.oddRun = (k.opened && k.ppar)) :
    (escAnd26W k).toNat = (if (carry64 k.lo k.hi k.st).oddRun then 1 else 0) := by
  -- the specification's carry, in closed form
  have hR : (if (carry64 k.lo k.hi k.st).oddRun then 1 else 0)
      = (if BitLanes.trailingRun (bsW k) = 64
          then (if k.opened then (if k.ppar then 1 else 0) else 0)
          else BitLanes.trailingRun (bsW k) % 2) := by
    show (if (carry64 k.lo k.hi k.st).oddRun then 1 else 0)
      = (if BitLanes.suffixRun (bsW k) 64 = 64
          then (if k.opened then (if k.ppar then 1 else 0) else 0)
          else BitLanes.suffixRun (bsW k) 64 % 2)
    rw [carry64_oddRun_eq k hst, runParityBefore_eq, ← bsW_eq_spec k, flipBits_64]
    by_cases h : BitLanes.suffixRun (bsW k) 64 = 64
    · rw [ite_eq_left h, ite_eq_left h]
      cases k.opened <;> cases k.ppar <;> rfl
    · rw [ite_eq_right h, ite_eq_right h]
      have := Nat.mod_lt (BitLanes.suffixRun (bsW k) 64) (by decide : 0 < 2)
      cases hh : BitLanes.suffixRun (bsW k) 64 % 2 with
      | zero => simp_all
      | succ n =>
          have hn : n = 0 := by omega
          subst hn
          rfl
  rw [hR]
  rw [escAnd26W_eq, BitVec.toNat_and, escXor25W_eq, BitVec.toNat_xor,
    escCond24_toNat k, escCtlz_toNat k, escShr16_toNat k]
  -- the two cases the carry boundary has: a trailing run, or none
  by_cases hb : (bsW k).getLsbD 63 = true
  · rw [ite_eq_left hb]
    by_cases hT : BitLanes.trailingRun (bsW k) = 64
    · -- all backslashes: every lane is set, so the incoming parity survives
      have h1 : bsW k = BitVec.ofInt 64 (-1) := (trailingRun_eq_64_iff (bsW k)).mp hT
      rw [ite_eq_left hT]
      simp only [h1, true_and]
      cases k.opened <;> cases k.ppar <;> decide
    · have hH : ¬ (bsW k = BitVec.ofInt 64 (-1) ∧ k.opened) := by
        rintro ⟨h1, _⟩
        exact hT ((trailingRun_eq_64_iff (bsW k)).mpr h1)
      rw [ite_eq_right hT, ite_eq_right hH, Nat.zero_xor, Nat.and_one_is_mod]
  · have hg : (bsW k).getLsbD 63 = false := by
      cases h : (bsW k).getLsbD 63 <;> simp_all
    rw [ite_eq_right hb]
    have hzero := trailingRun_eq_zero (bsW k) hg
    rw [hzero, ite_eq_right (by decide : ¬ ((0 : Nat) = 64)), Nat.and_zero]

theorem s1Slot_open_below (k : Ctx) (m : Mem) (hdisj : k.o + 48 ≤ k.c) :
    readBytes (s1SlotMem k m) k.c 8 = some (natToBytes (escShr16W k).toNat 8) := by
  simp only [s1SlotMem]
  rw [readBytes_slot_above _ (k.o + 40) k.c _ (by omega),
    readBytes_slot_above _ (k.o + 32) k.c _ (by omega),
    readBytes_slot_above _ (k.o + 24) k.c _ (by omega),
    readBytes_slot_above _ (k.o + 16) k.c _ (by omega),
    readBytes_slot_above _ (k.o + 8) k.c _ (by omega),
    readBytes_slot_above _ k.o k.c _ (by omega),
    readBytes_slot_below _ (k.c + 16) k.c _ (by omega)]
  exact readBytes_slot_same _ k.c _

theorem s1Slot_ppar_below (k : Ctx) (m : Mem) (hdisj : k.o + 48 ≤ k.c) :
    readBytes (s1SlotMem k m) (k.c + 8) 8 = some (natToBytes (escAnd26W k).toNat 8) := by
  simp only [s1SlotMem]
  rw [readBytes_slot_above _ (k.o + 40) (k.c + 8) _ (by omega),
    readBytes_slot_above _ (k.o + 32) (k.c + 8) _ (by omega),
    readBytes_slot_above _ (k.o + 24) (k.c + 8) _ (by omega),
    readBytes_slot_above _ (k.o + 16) (k.c + 8) _ (by omega),
    readBytes_slot_above _ (k.o + 8) (k.c + 8) _ (by omega),
    readBytes_slot_above _ k.o (k.c + 8) _ (by omega),
    readBytes_slot_below _ (k.c + 16) (k.c + 8) _ (by omega),
    readBytes_slot_above _ k.c (k.c + 8) _ (by omega)]
  exact readBytes_slot_same _ (k.c + 8) _

theorem s1Slot_im_below (k : Ctx) (m : Mem) (hdisj : k.o + 48 ≤ k.c) :
    readBytes (s1SlotMem k m) (k.c + 16) 8 = some (natToBytes (imSignW k).toNat 8) := by
  simp only [s1SlotMem]
  rw [readBytes_slot_above _ (k.o + 40) (k.c + 16) _ (by omega),
    readBytes_slot_above _ (k.o + 32) (k.c + 16) _ (by omega),
    readBytes_slot_above _ (k.o + 24) (k.c + 16) _ (by omega),
    readBytes_slot_above _ (k.o + 16) (k.c + 16) _ (by omega),
    readBytes_slot_above _ (k.o + 8) (k.c + 16) _ (by omega),
    readBytes_slot_above _ k.o (k.c + 16) _ (by omega)]
  exact readBytes_slot_same _ (k.c + 16) _

theorem s1Slot_carry_below (k : Ctx) (m : Mem) (hdisj : k.o + 48 ≤ k.c) :
    readBytes (s1SlotMem k m) k.c 24
      = some (natToBytes (escShr16W k).toNat 8 ++
          (natToBytes (escAnd26W k).toNat 8 ++ natToBytes (imSignW k).toNat 8)) := by
  have h16 : readBytes (s1SlotMem k m) (k.c + 8) 16
      = some (natToBytes (escAnd26W k).toNat 8 ++ natToBytes (imSignW k).toNat 8) := by
    rw [show (16 : Nat) = 8 + 8 from by decide]
    rw [readBytes_app _ 8 8 (k.c + 8) (s1Slot_ppar_below k m hdisj)]
    rw [show (k.c + 8) + 8 = k.c + 16 from by omega]
    exact s1Slot_im_below k m hdisj
  rw [show (24 : Nat) = 8 + 16 from by decide]
  rw [readBytes_app _ 8 16 k.c (s1Slot_open_below k m hdisj) h16]

/-- The first eight-byte word of a slot, read back. -/
theorem slotTake (v : Nat) (rest : List UInt8) :
    (natToBytes v 8 ++ rest).take 8 = natToBytes v 8 := by
  show (natToBytes v 8 ++ rest).take (natToBytes v 8).length = natToBytes v 8
  exact List.take_left

/-- The bytes after a slot's first word. -/
theorem slotDrop (v : Nat) (rest : List UInt8) :
    (natToBytes v 8 ++ rest).drop 8 = rest := by
  show (natToBytes v 8 ++ rest).drop (natToBytes v 8).length = rest
  exact List.drop_left

theorem blockTake (lo hi : Block32) :
    (List.ofFn lo ++ List.ofFn hi).take 32 = List.ofFn lo := by
  show (List.ofFn lo ++ List.ofFn hi).take (List.ofFn lo).length = List.ofFn lo
  exact List.take_left

theorem blockDrop (lo hi : Block32) :
    (List.ofFn lo ++ List.ofFn hi).drop 32 = List.ofFn hi := by
  show (List.ofFn lo ++ List.ofFn hi).drop (List.ofFn lo).length = List.ofFn hi
  exact List.drop_left

set_option linter.unusedVariables false in
/-- **The stage-1 block classifier refines the kernel's six masks and its carry.**

Under `s1Calls`, from a readable sixty-four-byte block at `%p` and a twenty-four-byte
carry slot at `%c` holding `(opened, ppar, in-string)` with `oddRun = (opened && ppar)`,
one control step leaves the six specification masks at `%o` — quote, delimiter,
in-string, whitespace, backslash, control — the outgoing carry at `%c`, and every byte
outside the two slots unchanged.  The carry slot's three words are the identities
`s1_open_spec`, `s1_ppar_spec` and `s1_inside_spec`.

Footprint: `[propext, Classical.choice, Quot.sound]`.  The carrier is
`s1_inside_spec`'s bit-to-magnitude bridge (see `sshiftRight_63`); every other
clause is `[propext, Quot.sound]` or narrower, and `s1_ppar_spec` — the parity the
carry slot holds — is narrower, since `BitLanes.allOnes_getLsbD_of_lt` supplies the
extensionality this core's `BitVec.getLsbD_allOnes` does not.

The two premises about `%p` are not consumed by any clause: the body writes only to
the two output slots, so the sweep for bytes outside them never needs the block's
disjointness.  They stay in the statement because `%p` is an input like the other
two, and a caller whose block overlapped a slot would be describing another ABI. -/
theorem s1_masks_refines (lo hi : Block32) (st : ClassState) (opened ppar : Bool)
    (hodd : st.oddRun = (opened && ppar))
    (mem : Mem) (p c o : Nat)
    (hblock : readBytes mem p 64 = some (block64 lo hi))
    (hcarry : readBytes mem c 24 = some (carrySlot opened ppar st.inside))
    (hdisj : p + 64 ≤ c ∨ c + 24 ≤ p) (hdisj' : p + 64 ≤ o ∨ o + 48 ≤ p)
    (hdisj'' : c + 24 ≤ o ∨ o + 48 ≤ c) :
    ∃ mem', runFuel s1Calls 1 s1MasksFunction
              { (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]) with mem := mem }
              = some (.ret none mem') ∧
      readBytes mem' o 8 = some (natToBytes (specQuote64 lo hi st).toNat 8) ∧
      readBytes mem' (o + 8) 8 = some (natToBytes (specDelimiter64 lo hi st).toNat 8) ∧
      readBytes mem' (o + 16) 8 = some (natToBytes (specInString64 lo hi st).toNat 8) ∧
      readBytes mem' (o + 24) 8 = some (natToBytes (specSpace64 lo hi st).toNat 8) ∧
      readBytes mem' (o + 32) 8 = some (natToBytes (specBackslash64 lo hi st).toNat 8) ∧
      readBytes mem' (o + 40) 8 = some (natToBytes (specControl64 lo hi st).toNat 8) ∧
      readBytes mem' c 24 = some (carrySlot (IsBackslashB (hi ⟨31, by decide⟩))
        (carry64 lo hi st).oddRun (carry64 lo hi st).inside) ∧
      (∀ a, (a < p ∨ p + 64 ≤ a) → (a < c ∨ c + 24 ≤ a) → (a < o ∨ o + 48 ≤ a) →
        readByte mem' a = readByte mem a) := by
  let k : Ctx := ⟨p, c, o, lo, hi, opened, ppar, st⟩
  have hst : k.st.oddRun = (k.opened && k.ppar) := hodd
  -- the entry environment
  have hp : lookupName (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]).env "%p"
      = some (.ptr p) := by
    simp only [initState, s1MasksFunction, List.map, List.zip, List.zipWith, lookupName,
      ite_true]
  have hc : lookupName (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]).env "%c"
      = some (.ptr c) := by
    simp only [initState, s1MasksFunction, List.map, List.zip, List.zipWith, lookupName,
      ite_true]
    rfl
  have ho : lookupName (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]).env "%o"
      = some (.ptr o) := by
    simp only [initState, s1MasksFunction, List.map, List.zip, List.zipWith, lookupName,
      ite_true]
    rfl
  -- the block, split at the half
  have hl0 : readBytes mem p 32 = some (List.ofFn lo) := by
    obtain ⟨h1, _⟩ := readBytes_split mem p 32 32 hblock
    rw [block64, blockTake lo hi] at h1
    exact h1
  have hl1 : readBytes mem (p + 32) 32 = some (List.ofFn hi) := by
    obtain ⟨_, h2⟩ := readBytes_split mem p 32 32 hblock
    rw [block64, blockDrop lo hi] at h2
    exact h2
  -- the carry slot, split at its three words
  have hd0 : readBytes mem c 8 = some (natToBytes (if opened then 1 else 0) 8) := by
    obtain ⟨h1, _⟩ := readBytes_split mem c 8 16 hcarry
    rw [carrySlot, List.append_assoc, slotTake] at h1
    exact h1
  have hdrest : readBytes mem (c + 8) 16
      = some (natToBytes (if ppar then 1 else 0) 8 ++
          natToBytes (if st.inside then 0xFFFFFFFFFFFFFFFF else 0) 8) := by
    obtain ⟨_, h2⟩ := readBytes_split mem c 8 16 hcarry
    rw [carrySlot, List.append_assoc, slotDrop] at h2
    exact h2
  have hd1 : readBytes mem (c + 8) 8 = some (natToBytes (if ppar then 1 else 0) 8) := by
    obtain ⟨h1, _⟩ := readBytes_split mem (c + 8) 8 8 hdrest
    rw [slotTake] at h1
    exact h1
  have hd2 : readBytes mem (c + 16) 8
      = some (natToBytes (if st.inside then 0xFFFFFFFFFFFFFFFF else 0) 8) := by
    obtain ⟨_, h2⟩ := readBytes_split mem (c + 8) 8 8 hdrest
    rw [show c + 8 + 8 = c + 16 from by omega, slotDrop] at h2
    exact h2
  refine ⟨s1SlotMem k mem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the run
    have hrun := s1_runFuel (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]).env
      { (initState s1MasksFunction [.ptr p, .ptr c, .ptr o]) with mem := mem } k
      rfl hp hc ho hl0 hl1 hd0 hd1 hd2
    exact hrun
  · exact s1Slot_quote_spec k mem hst
  · exact s1Slot_delim_spec k mem
  · exact s1Slot_instring_spec k mem hst
  · exact s1Slot_space_spec k mem
  · exact s1Slot_backslash_spec k mem
  · exact s1Slot_control_spec k mem
  · -- the carry slot
    have hc24 : readBytes (s1SlotMem k mem) k.c 24
        = some (natToBytes (escShr16W k).toNat 8 ++
            (natToBytes (escAnd26W k).toNat 8 ++ natToBytes (imSignW k).toNat 8)) := by
      rcases hdisj'' with h | h
      · exact s1Slot_carry k mem h
      · exact s1Slot_carry_below k mem h
    rw [hc24, s1_open_spec k, s1_ppar_spec k hst, s1_inside_spec k hst]
    rw [← List.append_assoc]
    rfl
  · intro a h1 h2 h3
    exact s1Slot_outside k mem a h2 h3



end LeanLLVM.Refinement.JsonS1MasksSteps
