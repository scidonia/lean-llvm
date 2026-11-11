/-
An emitted-IR bridge for the JSON block classifier.

`probes/install/ir/json-classify.candidate.ll` is the emission of the classifier
probe; `probes/install/ir/capture-json.sh` records the clang and `opt`
invocations and every piece of textual syntax removed before the parser sees
it.  This module

1. parses the file;
2. pins the parsed AST against the literal below (`#guard`, because the parser
   runs on `String` primitives, which the kernel does not reduce, so a
   proposition about a `parseModule` result cannot be closed by `rfl`);
3. proves, against the semantics in `LeanLLVM.Semantics`, that the parsed
   function returns the block layer's mask, `JSON.maskOf`, on every block
   readable at its argument, and reaches `ub` when it is not --
   `scannerLLVM_refines`, `classify32_undefined_of_no_read`;
4. shows the result does not depend on the allocator state the run is seeded
   with -- `classify32_next_independent` -- which is the bridge a seeded
   environment needs.

The body is emitted at `-O2`, so the ten `eq` comparisons and the tab/newline
range test are present as separate vector operations rather than as a scalar
chain; the per-lane reading is what links them to `IsStructOrSpaceB`, and the
pack's bit-level reading is `lanesToNat_testBit` in `Semantics.lean`.
-/
import LeanLLVM.Parser
import LeanLLVM.Semantics
import LeanLLVM.JSON.ScanBlock

namespace LeanLLVM.Refinement.JsonClassifyIR

open LeanLLVM
open LeanLLVM.JSON

/-! ### The fixture -/

/-- The classifier as emitted and committed. -/
def classifySrc : String := include_str "../../probes/install/ir/json-classify.candidate.ll"

/-- Parse a fixture and take its single function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-- An eight-bit constant, in the form `parseConst` produces for a literal. -/
def c8 (v : Int) : BitVec 8 := BitVec.ofInt 8 v

/-- A `splat` operand of thirty-two `i8` lanes. -/
def splat8 (v : Int) : Operand := .imm (.splat 32 8 (c8 v))

/-- `%arg` is the parameter name the fixture uses. -/
abbrev argName : String := "%arg"

/-- The classifier body, register by register, in the order the instructions
appear in the fixture. -/
def classify32Instrs : List Instr := [
  .load "%i" (.vec 32 (.int 8)) (.reg argName),
  .icmpVec "%i1" .eq 32 8 (.reg "%i") (splat8 34),
  .icmpVec "%i2" .eq 32 8 (.reg "%i") (splat8 92),
  .binopVec "%i3" .or 32 1 (.reg "%i1") (.reg "%i2"),
  .icmpVec "%i4" .eq 32 8 (.reg "%i") (splat8 58),
  .binopVec "%i5" .or 32 1 (.reg "%i4") (.reg "%i3"),
  .icmpVec "%i6" .eq 32 8 (.reg "%i") (splat8 44),
  .binopVec "%i7" .or 32 1 (.reg "%i6") (.reg "%i5"),
  .icmpVec "%i8" .eq 32 8 (.reg "%i") (splat8 123),
  .binopVec "%i9" .or 32 1 (.reg "%i8") (.reg "%i7"),
  .icmpVec "%i10" .eq 32 8 (.reg "%i") (splat8 125),
  .binopVec "%i11" .or 32 1 (.reg "%i10") (.reg "%i9"),
  .icmpVec "%i12" .eq 32 8 (.reg "%i") (splat8 91),
  .binopVec "%i13" .or 32 1 (.reg "%i12") (.reg "%i11"),
  .icmpVec "%i14" .eq 32 8 (.reg "%i") (splat8 93),
  .binopVec "%i15" .or 32 1 (.reg "%i14") (.reg "%i13"),
  .icmpVec "%i16" .eq 32 8 (.reg "%i") (splat8 32),
  .binopVec "%i17" .or 32 1 (.reg "%i16") (.reg "%i15"),
  .binopVec "%i18" .add 32 8 (.reg "%i") (splat8 (-9)),
  .icmpVec "%i19" .ult 32 8 (.reg "%i18") (splat8 2),
  .binopVec "%i20" .or 32 1 (.reg "%i19") (.reg "%i17"),
  .icmpVec "%i21" .eq 32 8 (.reg "%i") (splat8 13),
  .binopVec "%i22" .or 32 1 (.reg "%i21") (.reg "%i20"),
  .bitcastMask "%i23" 32 (.reg "%i22")]

/-- The classifier's single block: the body above, returning the packed mask. -/
def classify32Body : Block :=
  { name := "bb", instrs := classify32Instrs,
    term := .ret (.int 32) (some (.reg "%i23")) }

/-- `probes/install/ir/json-classify.candidate.ll`, as an AST. -/
def classify32Function : Function :=
  { name := "leanllvm_json_classify32", retTy := .int 32, params := [(argName, .ptr)],
    blocks := [classify32Body] }

#guard decide (firstFunction classifySrc = some classify32Function)

/-- The negative control's body: the same instructions, then the mask
complemented before the return (`%w = xor i32 %i23, -1`; `ret i32 %w`), built
from the list above rather than from a second fixture. -/
def wrongMaskFunction : Function :=
  { classify32Function with
    blocks := [{ name := "bb",
                 instrs := classify32Instrs ++
                   [.binop "%w" .xor 32 (.reg "%i23")
                      (.imm (.int 32 (BitVec.ofInt 32 (-1))))],
                 term := .ret (.int 32) (some (.reg "%w")) }] }

/-! ### The block's lanes, register by register

The load binds lane `k` to byte `k`; each comparison binds the lane test on that
byte; each `or` binds the lane-wise disjunction.  The values below are what each
register holds, with the lane list kept as a `List.ofFn` so a lane reading is
`List.getElem?_ofFn`. -/

/-- Byte `k` of the block, as the lane the load binds.  `loadValue` builds the
lane with `BitVec.ofNat 8 b.toNat`, which is `b.toBitVec`. -/
def laneByte (block : Block32) (k : Fin 32) : BitVec 8 := (block k).toBitVec

/-- The lanes the load binds: `loadValue` maps the thirty-two bytes. -/
def loadedLanes (block : Block32) : List (BitVec 8) :=
  (List.ofFn block).map (fun b => b.toBitVec)

theorem loadedLanes_eq (block : Block32) :
    loadedLanes block = List.ofFn (laneByte block) := by
  rw [loadedLanes, List.map_ofFn]
  rfl

/-- `%i1`: byte equals `"`. -/
def lane1 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => BitVec.ofBool (laneByte block k = c8 34)

/-- `%i2`: byte equals `\`. -/
def lane2 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => BitVec.ofBool (laneByte block k = c8 92)

/-- `%i3`. -/
def lane3 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => lane1 block k ||| lane2 block k

/-- `%i4`: byte equals `:`. -/
def lane4 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => BitVec.ofBool (laneByte block k = c8 58)

/-- `%i5`. -/
def lane5 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => lane4 block k ||| lane3 block k

/-- `%i6`: byte equals `,`. -/
def lane6 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => BitVec.ofBool (laneByte block k = c8 44)

/-- `%i7`. -/
def lane7 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => lane6 block k ||| lane5 block k

/-- `%i8`: byte equals `{`. -/
def lane8 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => BitVec.ofBool (laneByte block k = c8 123)

/-- `%i9`. -/
def lane9 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => lane8 block k ||| lane7 block k

/-- `%i10`: byte equals `}`. -/
def lane10 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => BitVec.ofBool (laneByte block k = c8 125)

/-- `%i11`. -/
def lane11 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => lane10 block k ||| lane9 block k

/-- `%i12`: byte equals `[`. -/
def lane12 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => BitVec.ofBool (laneByte block k = c8 91)

/-- `%i13`. -/
def lane13 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => lane12 block k ||| lane11 block k

/-- `%i14`: byte equals `]`. -/
def lane14 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => BitVec.ofBool (laneByte block k = c8 93)

/-- `%i15`. -/
def lane15 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => lane14 block k ||| lane13 block k

/-- `%i16`: byte equals space. -/
def lane16 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => BitVec.ofBool (laneByte block k = c8 32)

/-- `%i17`. -/
def lane17 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => lane16 block k ||| lane15 block k

/-- `%i18`: the range test's biased byte, `byte + (-9)`. -/
def lane18 (block : Block32) : Fin 32 → BitVec 8 :=
  fun k => laneByte block k + c8 (-9)

/-- `%i19`: the unsigned comparison with `2`, which is "tab or newline". -/
def lane19 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => BitVec.ofBool (lane18 block k < c8 2)

/-- `%i20`. -/
def lane20 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => lane19 block k ||| lane17 block k

/-- `%i21`: byte equals carriage return. -/
def lane21 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => BitVec.ofBool (laneByte block k = c8 13)

/-- `%i22`: the mask lanes. -/
def lane22 (block : Block32) : Fin 32 → BitVec 1 :=
  fun k => lane21 block k ||| lane20 block k

/-- The value `%i23` holds: the packed mask. -/
def packed (block : Block32) : BitVec 32 :=
  BitVec.ofNat 32 (lanesToNat (List.ofFn (lane22 block)))

/-- The body's per-byte decision, in the shape the lane chain has. -/
def laneExpr (x : BitVec 8) : BitVec 1 :=
  BitVec.ofBool (x = c8 13) |||
    (BitVec.ofBool (x + c8 (-9) < c8 2) |||
      (BitVec.ofBool (x = c8 32) |||
        (BitVec.ofBool (x = c8 93) |||
          (BitVec.ofBool (x = c8 91) |||
            (BitVec.ofBool (x = c8 125) |||
              (BitVec.ofBool (x = c8 123) |||
                (BitVec.ofBool (x = c8 44) |||
                  (BitVec.ofBool (x = c8 58) |||
                    (BitVec.ofBool (x = c8 34) |||
                      BitVec.ofBool (x = c8 92))))))))))

/-- The per-byte decision is the scalar transition's: the ten comparisons plus
the tab/newline range test, against the eight structural bytes and the four
whitespace bytes.  Proved by exhausting the byte. -/
theorem laneDecision (x : BitVec 8) :
    laneExpr x = 1 ↔ IsStructOrSpaceB (UInt8.ofBitVec x) = true := by
  revert x
  decide

/-- Lane `k` of the mask is the scalar decision on byte `k`. -/
theorem lane22_eq_one (block : Block32) (k : Fin 32) :
    lane22 block k = 1 ↔ IsStructOrSpaceB (block k) = true := by
  have h : lane22 block k = laneExpr (laneByte block k) := rfl
  rw [h, laneDecision]
  simp [laneByte]

/-- The packed lanes are the block mask, read bit by bit. -/
theorem packed_eq_maskOf (block : Block32) : packed block = maskOf block := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  unfold packed
  rw [BitVec.getLsbD_ofNat]
  have hk' : decide (k < 32) = true := decide_eq_true hk
  rw [hk', Bool.true_and]
  rw [maskOf_eq_maskOfList]
  have hlookup : (List.ofFn block)[k]? = some (block ⟨k, hk⟩) := by
    rw [List.getElem?_ofFn]
    simp [hk]
  rw [maskOfList_getLsbD hk hlookup]
  rw [Bool.eq_iff_iff]
  rw [lanesToNat_testBit, List.getElem?_ofFn, dite_eq_left hk, Option.some.injEq]
  exact lane22_eq_one block ⟨k, hk⟩

/-! ### Reading each instruction shape -/

/-- A `vecLanes` read at the value's own shape. -/
theorem vecLanes_vec (n w : Nat) (l : List (BitVec w)) (h : l.length = n) :
    Value.vecLanes n w (.vec n w l) = some l := by
  simp [Value.vecLanes, h]

/-- Zipping with a replicate of the matching length pairs every element with
the replicated one. -/
theorem zip_replicate_right {α β : Type} (l : List α) (b : β) :
    ∀ {n : Nat}, l.length = n → l.zip (List.replicate n b) = l.map (fun a => (a, b))
  | 0, h => by simp at h; subst h; simp
  | n + 1, h => by
      cases l with
      | nil => simp at h
      | cons a as =>
          simp only [List.length_cons] at h
          have has : as.length = n := by omega
          simp only [List.replicate_succ, List.map_cons, List.zip_cons_cons]
          rw [zip_replicate_right as b has]

/-- Zipping two `List.ofFn`s pairs the two functions at the same index. -/
theorem zip_ofFn_ofFn {α β : Type} {n : Nat} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun k => (f k, g k)) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_ofFn]
  split
  · rename_i hi
    rw [List.getElem?_zip_eq_some]
    simp [hi]
  · rename_i hi
    rw [List.getElem?_eq_none_iff, List.length_zip, List.length_ofFn, List.length_ofFn]
    omega

/-- Mapping over a `List.ofFn` is `List.ofFn` of the composite. -/
theorem map_ofFn_apply {α β : Type} {n : Nat} (f : Fin n → α) (g : α → β) :
    (List.ofFn f).map g = List.ofFn (fun k => g (f k)) := by
  rw [List.map_ofFn]
  rfl

/-- A `mapM` that always succeeds is the mapped list. -/
theorem mapM_some_map {α β : Type} (l : List α) (f : α → β) :
    l.mapM (fun a => some (f a)) = some (l.map f) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.mapM_cons, ih]

/-- The load reads thirty-two bytes as thirty-two lanes. -/
theorem evalInstr_load (calls : Calls) (s : State) (d r : String) (p : Nat)
    (block : Block32)
    (harg : lookupName s.env r = some (.ptr p))
    (hread : readBytes s.mem p 32 = some (List.ofFn block)) :
    evalInstr calls s (.load d (.vec 32 (.int 8)) (.reg r)) =
      some (s.bind d (.vec 32 8 (loadedLanes block))) := by
  simp [evalInstr, evalOperand, harg, loadValue, hread, loadedLanes]

/-- A lane-wise `eq` against a splat. -/
theorem evalInstr_icmpVec_eq_splat (calls : Calls) (s : State) (d r : String) (v : BitVec 8)
    (f : Fin 32 → BitVec 8)
    (hreg : lookupName s.env r = some (.vec 32 8 (List.ofFn f))) :
    evalInstr calls s (.icmpVec d .eq 32 8 (.reg r) (.imm (.splat 32 8 v))) =
      some (s.bind d (.vec 32 1 (List.ofFn (fun k => BitVec.ofBool (f k = v))))) := by
  simp only [evalInstr, evalOperand, Const.toValue, hreg, vecLanes_vec, List.length_ofFn,
    List.length_replicate, zip_replicate_right, map_ofFn_apply, evalICmp]

/-- A lane-wise unsigned `ult` against a splat. -/
theorem evalInstr_icmpVec_ult_splat (calls : Calls) (s : State) (d r : String) (v : BitVec 8)
    (f : Fin 32 → BitVec 8)
    (hreg : lookupName s.env r = some (.vec 32 8 (List.ofFn f))) :
    evalInstr calls s (.icmpVec d .ult 32 8 (.reg r) (.imm (.splat 32 8 v))) =
      some (s.bind d (.vec 32 1 (List.ofFn (fun k => BitVec.ofBool ((f k).ult v))))) := by
  simp only [evalInstr, evalOperand, Const.toValue, hreg, vecLanes_vec, List.length_ofFn,
    List.length_replicate, zip_replicate_right, map_ofFn_apply, evalICmp]

/-- A lane-wise `or` of two registers. -/
theorem evalInstr_binopVec_or (calls : Calls) (s : State) (d r₁ r₂ : String)
    (f g : Fin 32 → BitVec 1)
    (h₁ : lookupName s.env r₁ = some (.vec 32 1 (List.ofFn f)))
    (h₂ : lookupName s.env r₂ = some (.vec 32 1 (List.ofFn g))) :
    evalInstr calls s (.binopVec d .or 32 1 (.reg r₁) (.reg r₂)) =
      some (s.bind d (.vec 32 1 (List.ofFn (fun k => f k ||| g k)))) := by
  simp only [evalInstr, evalOperand, h₁, h₂, vecLanes_vec, List.length_ofFn,
    zip_ofFn_ofFn, mapM_some_map, map_ofFn_apply, evalBinop]

/-- A lane-wise `add` against a splat. -/
theorem evalInstr_binopVec_add_splat (calls : Calls) (s : State) (d r : String) (v : BitVec 8)
    (f : Fin 32 → BitVec 8)
    (hreg : lookupName s.env r = some (.vec 32 8 (List.ofFn f))) :
    evalInstr calls s (.binopVec d .add 32 8 (.reg r) (.imm (.splat 32 8 v))) =
      some (s.bind d (.vec 32 8 (List.ofFn (fun k => f k + v)))) := by
  simp only [evalInstr, evalOperand, Const.toValue, hreg, vecLanes_vec, List.length_ofFn,
    List.length_replicate, zip_replicate_right, mapM_some_map, map_ofFn_apply, evalBinop]

/-- The mask pack. -/
theorem evalInstr_bitcastMask (calls : Calls) (s : State) (d r : String)
    (f : Fin 32 → BitVec 1)
    (hreg : lookupName s.env r = some (.vec 32 1 (List.ofFn f))) :
    evalInstr calls s (.bitcastMask d 32 (.reg r)) =
      some (s.bind d (.int 32 (BitVec.ofNat 32 (lanesToNat (List.ofFn f))))) := by
  simp [evalInstr, evalOperand, hreg]

/-! ### The body, stage by stage -/

/-- Peel one instruction from a straight-line block whose effect is known. -/
theorem denoteCode_cons_of (calls : Calls) (i : Instr) (is : List Instr) (s s' : State)
    (h : evalInstr calls s i = some s') :
    denoteCode calls (i :: is) s = denoteCode calls is s' := by
  simp only [denoteCode, h]

/-- The state after the load. -/
def q0 (s : State) (block : Block32) : State :=
  s.bind "%i" (.vec 32 8 (List.ofFn (laneByte block)))

/-- The state after `%i1`. -/
def q1 (s : State) (block : Block32) : State :=
  (q0 s block).bind "%i1" (.vec 32 1 (List.ofFn (lane1 block)))

/-- The state after `%i2`. -/
def q2 (s : State) (block : Block32) : State :=
  (q1 s block).bind "%i2" (.vec 32 1 (List.ofFn (lane2 block)))

/-- The state after `%i3`. -/
def q3 (s : State) (block : Block32) : State :=
  (q2 s block).bind "%i3" (.vec 32 1 (List.ofFn (lane3 block)))

/-- The state after `%i4`. -/
def q4 (s : State) (block : Block32) : State :=
  (q3 s block).bind "%i4" (.vec 32 1 (List.ofFn (lane4 block)))

/-- The state after `%i5`. -/
def q5 (s : State) (block : Block32) : State :=
  (q4 s block).bind "%i5" (.vec 32 1 (List.ofFn (lane5 block)))

/-- The state after `%i6`. -/
def q6 (s : State) (block : Block32) : State :=
  (q5 s block).bind "%i6" (.vec 32 1 (List.ofFn (lane6 block)))

/-- The state after `%i7`. -/
def q7 (s : State) (block : Block32) : State :=
  (q6 s block).bind "%i7" (.vec 32 1 (List.ofFn (lane7 block)))

/-- The state after `%i8`. -/
def q8 (s : State) (block : Block32) : State :=
  (q7 s block).bind "%i8" (.vec 32 1 (List.ofFn (lane8 block)))

/-- The state after `%i9`. -/
def q9 (s : State) (block : Block32) : State :=
  (q8 s block).bind "%i9" (.vec 32 1 (List.ofFn (lane9 block)))

/-- The state after `%i10`. -/
def q10 (s : State) (block : Block32) : State :=
  (q9 s block).bind "%i10" (.vec 32 1 (List.ofFn (lane10 block)))

/-- The state after `%i11`. -/
def q11 (s : State) (block : Block32) : State :=
  (q10 s block).bind "%i11" (.vec 32 1 (List.ofFn (lane11 block)))

/-- The state after `%i12`. -/
def q12 (s : State) (block : Block32) : State :=
  (q11 s block).bind "%i12" (.vec 32 1 (List.ofFn (lane12 block)))

/-- The state after `%i13`. -/
def q13 (s : State) (block : Block32) : State :=
  (q12 s block).bind "%i13" (.vec 32 1 (List.ofFn (lane13 block)))

/-- The state after `%i14`. -/
def q14 (s : State) (block : Block32) : State :=
  (q13 s block).bind "%i14" (.vec 32 1 (List.ofFn (lane14 block)))

/-- The state after `%i15`. -/
def q15 (s : State) (block : Block32) : State :=
  (q14 s block).bind "%i15" (.vec 32 1 (List.ofFn (lane15 block)))

/-- The state after `%i16`. -/
def q16 (s : State) (block : Block32) : State :=
  (q15 s block).bind "%i16" (.vec 32 1 (List.ofFn (lane16 block)))

/-- The state after `%i17`. -/
def q17 (s : State) (block : Block32) : State :=
  (q16 s block).bind "%i17" (.vec 32 1 (List.ofFn (lane17 block)))

/-- The state after `%i18`. -/
def q18 (s : State) (block : Block32) : State :=
  (q17 s block).bind "%i18" (.vec 32 8 (List.ofFn (lane18 block)))

/-- The state after `%i19`. -/
def q19 (s : State) (block : Block32) : State :=
  (q18 s block).bind "%i19" (.vec 32 1 (List.ofFn (lane19 block)))

/-- The state after `%i20`. -/
def q20 (s : State) (block : Block32) : State :=
  (q19 s block).bind "%i20" (.vec 32 1 (List.ofFn (lane20 block)))

/-- The state after `%i21`. -/
def q21 (s : State) (block : Block32) : State :=
  (q20 s block).bind "%i21" (.vec 32 1 (List.ofFn (lane21 block)))

/-- The state after `%i22`. -/
def q22 (s : State) (block : Block32) : State :=
  (q21 s block).bind "%i22" (.vec 32 1 (List.ofFn (lane22 block)))

/-- The state after `%i23`. -/
def q23 (s : State) (block : Block32) : State :=
  (q22 s block).bind "%i23" (.int 32 (packed block))

/-- The state the body reaches from `s`, register by register. -/
def classifyRun (s : State) (block : Block32) : State := q23 s block

/-- The load stage. -/
theorem step1 (calls : Calls) (s : State) (p : Nat) (block : Block32)
    (harg : lookupName s.env argName = some (.ptr p))
    (hread : readBytes s.mem p 32 = some (List.ofFn block)) :
    evalInstr calls s (.load "%i" (.vec 32 (.int 8)) (.reg argName)) = some (q0 s block) := by
  rw [evalInstr_load calls s "%i" argName p block harg hread, loadedLanes_eq]
  rfl

/-- `%i1`. -/
theorem step2 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q0 s block) (.icmpVec "%i1" .eq 32 8 (.reg "%i") (splat8 34)) =
      some (q1 s block) := by
  simp only [splat8]
  rw [evalInstr_icmpVec_eq_splat calls (q0 s block) "%i1" "%i" (c8 34) (laneByte block)
    (by simp only [q0, State.bind]; rfl)]
  rfl

/-- `%i2`. -/
theorem step3 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q1 s block) (.icmpVec "%i2" .eq 32 8 (.reg "%i") (splat8 92)) =
      some (q2 s block) := by
  simp only [splat8]
  rw [evalInstr_icmpVec_eq_splat calls (q1 s block) "%i2" "%i" (c8 92) (laneByte block)
    (by simp only [q1, q0, State.bind]; rfl)]
  rfl

/-- `%i3`. -/
theorem step4 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q2 s block) (.binopVec "%i3" .or 32 1 (.reg "%i1") (.reg "%i2")) =
      some (q3 s block) := by
  rw [evalInstr_binopVec_or calls (q2 s block) "%i3" "%i1" "%i2" (lane1 block) (lane2 block)
    (by simp only [q2, q1, q0, State.bind]; rfl)
    (by simp only [q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i4`. -/
theorem step5 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q3 s block) (.icmpVec "%i4" .eq 32 8 (.reg "%i") (splat8 58)) =
      some (q4 s block) := by
  simp only [splat8]
  rw [evalInstr_icmpVec_eq_splat calls (q3 s block) "%i4" "%i" (c8 58) (laneByte block)
    (by simp only [q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i5`. -/
theorem step6 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q4 s block) (.binopVec "%i5" .or 32 1 (.reg "%i4") (.reg "%i3")) =
      some (q5 s block) := by
  rw [evalInstr_binopVec_or calls (q4 s block) "%i5" "%i4" "%i3" (lane4 block) (lane3 block)
    (by simp only [q4, q3, q2, q1, q0, State.bind]; rfl)
    (by simp only [q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i6`. -/
theorem step7 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q5 s block) (.icmpVec "%i6" .eq 32 8 (.reg "%i") (splat8 44)) =
      some (q6 s block) := by
  simp only [splat8]
  rw [evalInstr_icmpVec_eq_splat calls (q5 s block) "%i6" "%i" (c8 44) (laneByte block)
    (by simp only [q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i7`. -/
theorem step8 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q6 s block) (.binopVec "%i7" .or 32 1 (.reg "%i6") (.reg "%i5")) =
      some (q7 s block) := by
  rw [evalInstr_binopVec_or calls (q6 s block) "%i7" "%i6" "%i5" (lane6 block) (lane5 block)
    (by simp only [q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)
    (by simp only [q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i8`. -/
theorem step9 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q7 s block) (.icmpVec "%i8" .eq 32 8 (.reg "%i") (splat8 123)) =
      some (q8 s block) := by
  simp only [splat8]
  rw [evalInstr_icmpVec_eq_splat calls (q7 s block) "%i8" "%i" (c8 123) (laneByte block)
    (by simp only [q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i9`. -/
theorem step10 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q8 s block) (.binopVec "%i9" .or 32 1 (.reg "%i8") (.reg "%i7")) =
      some (q9 s block) := by
  rw [evalInstr_binopVec_or calls (q8 s block) "%i9" "%i8" "%i7" (lane8 block) (lane7 block)
    (by simp only [q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)
    (by simp only [q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i10`. -/
theorem step11 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q9 s block) (.icmpVec "%i10" .eq 32 8 (.reg "%i") (splat8 125)) =
      some (q10 s block) := by
  simp only [splat8]
  rw [evalInstr_icmpVec_eq_splat calls (q9 s block) "%i10" "%i" (c8 125) (laneByte block)
    (by simp only [q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i11`. -/
theorem step12 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q10 s block) (.binopVec "%i11" .or 32 1 (.reg "%i10") (.reg "%i9")) =
      some (q11 s block) := by
  rw [evalInstr_binopVec_or calls (q10 s block) "%i11" "%i10" "%i9" (lane10 block) (lane9 block)
    (by simp only [q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)
    (by simp only [q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i12`. -/
theorem step13 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q11 s block) (.icmpVec "%i12" .eq 32 8 (.reg "%i") (splat8 91)) =
      some (q12 s block) := by
  simp only [splat8]
  rw [evalInstr_icmpVec_eq_splat calls (q11 s block) "%i12" "%i" (c8 91) (laneByte block)
    (by simp only [q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i13`. -/
theorem step14 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q12 s block) (.binopVec "%i13" .or 32 1 (.reg "%i12") (.reg "%i11")) =
      some (q13 s block) := by
  rw [evalInstr_binopVec_or calls (q12 s block) "%i13" "%i12" "%i11" (lane12 block)
    (lane11 block)
    (by simp only [q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)
    (by simp only [q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i14`. -/
theorem step15 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q13 s block) (.icmpVec "%i14" .eq 32 8 (.reg "%i") (splat8 93)) =
      some (q14 s block) := by
  simp only [splat8]
  rw [evalInstr_icmpVec_eq_splat calls (q13 s block) "%i14" "%i" (c8 93) (laneByte block)
    (by simp only [q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i15`. -/
theorem step16 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q14 s block) (.binopVec "%i15" .or 32 1 (.reg "%i14") (.reg "%i13")) =
      some (q15 s block) := by
  rw [evalInstr_binopVec_or calls (q14 s block) "%i15" "%i14" "%i13" (lane14 block)
    (lane13 block)
    (by simp only [q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)
    (by simp only [q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i16`. -/
theorem step17 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q15 s block) (.icmpVec "%i16" .eq 32 8 (.reg "%i") (splat8 32)) =
      some (q16 s block) := by
  simp only [splat8]
  rw [evalInstr_icmpVec_eq_splat calls (q15 s block) "%i16" "%i" (c8 32) (laneByte block)
    (by simp only [q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i17`. -/
theorem step18 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q16 s block) (.binopVec "%i17" .or 32 1 (.reg "%i16") (.reg "%i15")) =
      some (q17 s block) := by
  rw [evalInstr_binopVec_or calls (q16 s block) "%i17" "%i16" "%i15" (lane16 block)
    (lane15 block)
    (by simp only [q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)
    (by simp only [q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i18`. -/
theorem step19 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q17 s block) (.binopVec "%i18" .add 32 8 (.reg "%i") (splat8 (-9))) =
      some (q18 s block) := by
  simp only [splat8]
  rw [evalInstr_binopVec_add_splat calls (q17 s block) "%i18" "%i" (c8 (-9)) (laneByte block)
    (by simp only [q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i19`. -/
theorem step20 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q18 s block) (.icmpVec "%i19" .ult 32 8 (.reg "%i18") (splat8 2)) =
      some (q19 s block) := by
  simp only [splat8]
  rw [evalInstr_icmpVec_ult_splat calls (q18 s block) "%i19" "%i18" (c8 2) (lane18 block)
    (by simp only [q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i20`. -/
theorem step21 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q19 s block) (.binopVec "%i20" .or 32 1 (.reg "%i19") (.reg "%i17")) =
      some (q20 s block) := by
  rw [evalInstr_binopVec_or calls (q19 s block) "%i20" "%i19" "%i17" (lane19 block)
    (lane17 block)
    (by simp only [q19, q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)
    (by simp only [q19, q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i21`. -/
theorem step22 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q20 s block) (.icmpVec "%i21" .eq 32 8 (.reg "%i") (splat8 13)) =
      some (q21 s block) := by
  simp only [splat8]
  rw [evalInstr_icmpVec_eq_splat calls (q20 s block) "%i21" "%i" (c8 13) (laneByte block)
    (by simp only [q20, q19, q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i22`. -/
theorem step23 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q21 s block) (.binopVec "%i22" .or 32 1 (.reg "%i21") (.reg "%i20")) =
      some (q22 s block) := by
  rw [evalInstr_binopVec_or calls (q21 s block) "%i22" "%i21" "%i20" (lane21 block)
    (lane20 block)
    (by simp only [q21, q20, q19, q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)
    (by simp only [q21, q20, q19, q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- `%i23`. -/
theorem step24 (calls : Calls) (s : State) (block : Block32) :
    evalInstr calls (q22 s block) (.bitcastMask "%i23" 32 (.reg "%i22")) = some (q23 s block) := by
  rw [evalInstr_bitcastMask calls (q22 s block) "%i23" "%i22" (lane22 block)
    (by simp only [q22, q21, q20, q19, q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]; rfl)]
  rfl

/-- The body, stage by stage. -/
theorem classify32_block (calls : Calls) (s : State) (block : Block32) (p : Nat)
    (harg : lookupName s.env argName = some (.ptr p))
    (hread : readBytes s.mem p 32 = some (List.ofFn block)) :
    denoteCode calls classify32Instrs s = some (classifyRun s block) := by
  have h1 := step1 calls s p block harg hread
  have h2 := step2 calls s block
  have h3 := step3 calls s block
  have h4 := step4 calls s block
  have h5 := step5 calls s block
  have h6 := step6 calls s block
  have h7 := step7 calls s block
  have h8 := step8 calls s block
  have h9 := step9 calls s block
  have h10 := step10 calls s block
  have h11 := step11 calls s block
  have h12 := step12 calls s block
  have h13 := step13 calls s block
  have h14 := step14 calls s block
  have h15 := step15 calls s block
  have h16 := step16 calls s block
  have h17 := step17 calls s block
  have h18 := step18 calls s block
  have h19 := step19 calls s block
  have h20 := step20 calls s block
  have h21 := step21 calls s block
  have h22 := step22 calls s block
  have h23 := step23 calls s block
  have h24 := step24 calls s block
  rw [show classify32Instrs =
      [.load "%i" (.vec 32 (.int 8)) (.reg argName),
       .icmpVec "%i1" .eq 32 8 (.reg "%i") (splat8 34),
       .icmpVec "%i2" .eq 32 8 (.reg "%i") (splat8 92),
       .binopVec "%i3" .or 32 1 (.reg "%i1") (.reg "%i2"),
       .icmpVec "%i4" .eq 32 8 (.reg "%i") (splat8 58),
       .binopVec "%i5" .or 32 1 (.reg "%i4") (.reg "%i3"),
       .icmpVec "%i6" .eq 32 8 (.reg "%i") (splat8 44),
       .binopVec "%i7" .or 32 1 (.reg "%i6") (.reg "%i5"),
       .icmpVec "%i8" .eq 32 8 (.reg "%i") (splat8 123),
       .binopVec "%i9" .or 32 1 (.reg "%i8") (.reg "%i7"),
       .icmpVec "%i10" .eq 32 8 (.reg "%i") (splat8 125),
       .binopVec "%i11" .or 32 1 (.reg "%i10") (.reg "%i9"),
       .icmpVec "%i12" .eq 32 8 (.reg "%i") (splat8 91),
       .binopVec "%i13" .or 32 1 (.reg "%i12") (.reg "%i11"),
       .icmpVec "%i14" .eq 32 8 (.reg "%i") (splat8 93),
       .binopVec "%i15" .or 32 1 (.reg "%i14") (.reg "%i13"),
       .icmpVec "%i16" .eq 32 8 (.reg "%i") (splat8 32),
       .binopVec "%i17" .or 32 1 (.reg "%i16") (.reg "%i15"),
       .binopVec "%i18" .add 32 8 (.reg "%i") (splat8 (-9)),
       .icmpVec "%i19" .ult 32 8 (.reg "%i18") (splat8 2),
       .binopVec "%i20" .or 32 1 (.reg "%i19") (.reg "%i17"),
       .icmpVec "%i21" .eq 32 8 (.reg "%i") (splat8 13),
       .binopVec "%i22" .or 32 1 (.reg "%i21") (.reg "%i20"),
       .bitcastMask "%i23" 32 (.reg "%i22")] from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ h1]
  rw [denoteCode_cons_of _ _ _ _ _ h2]
  rw [denoteCode_cons_of _ _ _ _ _ h3]
  rw [denoteCode_cons_of _ _ _ _ _ h4]
  rw [denoteCode_cons_of _ _ _ _ _ h5]
  rw [denoteCode_cons_of _ _ _ _ _ h6]
  rw [denoteCode_cons_of _ _ _ _ _ h7]
  rw [denoteCode_cons_of _ _ _ _ _ h8]
  rw [denoteCode_cons_of _ _ _ _ _ h9]
  rw [denoteCode_cons_of _ _ _ _ _ h10]
  rw [denoteCode_cons_of _ _ _ _ _ h11]
  rw [denoteCode_cons_of _ _ _ _ _ h12]
  rw [denoteCode_cons_of _ _ _ _ _ h13]
  rw [denoteCode_cons_of _ _ _ _ _ h14]
  rw [denoteCode_cons_of _ _ _ _ _ h15]
  rw [denoteCode_cons_of _ _ _ _ _ h16]
  rw [denoteCode_cons_of _ _ _ _ _ h17]
  rw [denoteCode_cons_of _ _ _ _ _ h18]
  rw [denoteCode_cons_of _ _ _ _ _ h19]
  rw [denoteCode_cons_of _ _ _ _ _ h20]
  rw [denoteCode_cons_of _ _ _ _ _ h21]
  rw [denoteCode_cons_of _ _ _ _ _ h22]
  rw [denoteCode_cons_of _ _ _ _ _ h23]
  rw [denoteCode_cons_of _ _ _ _ _ h24]
  rfl

/-- The body's last register holds the packed mask. -/
theorem lookupName_classifyRun (s : State) (block : Block32) :
    lookupName (classifyRun s block).env "%i23" = some (.int 32 (packed block)) := by
  simp [classifyRun, q23, q22, q21, q20, q19, q18, q17, q16, q15, q14, q13, q12, q11, q10,
    q9, q8, q7, q6, q5, q4, q3, q2, q1, q0, State.bind]

/-- The body leaves the caller's memory alone. -/
theorem classifyRun_mem (s : State) (block : Block32) :
    (classifyRun s block).mem = s.mem := rfl

/-- One control step of the body, from a state whose argument is `p` and whose
memory holds the block there. -/
theorem classify32_step (calls : Calls) (s : State) (block : Block32) (p : Nat)
    (harg : lookupName s.env argName = some (.ptr p))
    (hread : readBytes s.mem p 32 = some (List.ofFn block)) (hpc : s.pc = "bb") :
    step calls classify32Function s =
      .ret (some (.int 32 (maskOf block))) (classifyRun s block) := by
  have hfind : classify32Function.findBlock s.pc = some classify32Body := by
    simp [hpc, classify32Function, classify32Body, Function.findBlock, findBlockList]
  simp only [step, hfind, classify32Body]
  rw [classify32_block calls s block p harg hread]
  simp only [execTerm, evalOperand, lookupName_classifyRun, packed_eq_maskOf]

/-- The body's first instruction does not resolve when the block is not
readable, so the whole run is `ub`. -/
theorem classify32_step_ub (calls : Calls) (s : State) (p : Nat)
    (harg : lookupName s.env argName = some (.ptr p))
    (hnone : readBytes s.mem p 32 = none) (hpc : s.pc = "bb") :
    step calls classify32Function s = .ub := by
  have hfind : classify32Function.findBlock s.pc = some classify32Body := by
    simp [hpc, classify32Function, classify32Body, Function.findBlock, findBlockList]
  simp only [step, hfind, classify32Body, classify32Instrs, denoteCode, evalInstr,
    evalOperand, harg, loadValue, hnone]

/-! ### The theorems -/

/-- The body's memory and outcome do not depend on the allocator state it is
seeded with: the body executes no `alloca` and no store.  This is the bridge
between `envForBodySym` (which seeds an arbitrary `next`) and the run below
(which starts at `initState`'s `next := 1`). -/
theorem classify32_next_independent (block : Block32) (mem : Mem) (p n m : Nat)
    (hread : readBytes mem p 32 = some (List.ofFn block)) :
    runFuel noCalls 10000 classify32Function
        { (initState classify32Function [.ptr p]) with mem := mem, next := n } =
      runFuel noCalls 10000 classify32Function
        { (initState classify32Function [.ptr p]) with mem := mem, next := m } := by
  have hstate : ∀ next,
      runFuel noCalls 10000 classify32Function
          { (initState classify32Function [.ptr p]) with mem := mem, next := next } =
        some (.ret (some (.int 32 (maskOf block))) mem) := by
    intro next
    have harg : lookupName
        ({ (initState classify32Function [.ptr p]) with mem := mem, next := next }).env
          argName = some (.ptr p) := by
      simp [initState, classify32Function, argName, List.map, List.zip, List.zipWith]
    have hpc :
        ({ (initState classify32Function [.ptr p]) with mem := mem, next := next }).pc =
          "bb" := rfl
    simp only [runFuel,
      classify32_step noCalls _ block p harg hread hpc, classifyRun_mem]
  rw [hstate n, hstate m]

/-- `scannerLLVM_refines`: the imported candidate body, run under this
repository's semantics from a memory holding the block at `%arg`, returns the
scalar transition's mask and leaves the caller's memory exactly as it found it.
The memory hypothesis is the body's entire precondition: `%arg` is readable for
32 bytes, which is what `load <32 x i8>` needs on the machine. -/
theorem scannerLLVM_refines (block : Block32) (mem : Mem) (p : Nat)
    (hread : readBytes mem p 32 = some (List.ofFn block)) :
    runFuel noCalls 10000 classify32Function
        { (initState classify32Function [.ptr p]) with mem := mem } =
      some (.ret (some (.int 32 (maskOf block))) mem) := by
  have harg : lookupName
      { (initState classify32Function [.ptr p]) with mem := mem }.env argName =
        some (.ptr p) := by
    simp [initState, classify32Function, argName, List.map, List.zip, List.zipWith]
  have hpc : { (initState classify32Function [.ptr p]) with mem := mem }.pc = "bb" := rfl
  simp only [runFuel, classify32_step noCalls _ block p harg hread hpc, classifyRun_mem]

/-- Where the block is not readable, the body is undefined — the same place the
reference is undefined, which is what keeps the seam relation from having to
pretend the candidate fails where it succeeds. -/
theorem classify32_undefined_of_no_read (mem : Mem) (p : Nat)
    (h : readBytes mem p 32 = none) :
    runFuel noCalls 10000 classify32Function
        { (initState classify32Function [.ptr p]) with mem := mem } = some .ub := by
  have harg : lookupName
      { (initState classify32Function [.ptr p]) with mem := mem }.env argName =
        some (.ptr p) := by
    simp [initState, classify32Function, argName, List.map, List.zip, List.zipWith]
  have hpc : { (initState classify32Function [.ptr p]) with mem := mem }.pc = "bb" := rfl
  simp only [runFuel, classify32_step_ub noCalls _ p harg h hpc]

end LeanLLVM.Refinement.JsonClassifyIR
