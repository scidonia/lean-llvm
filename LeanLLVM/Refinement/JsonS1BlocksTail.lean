/-
The peeled tail's block traces.

The body's peel is four blocks: `if.then103` classifies the last whole block and
writes its DFA word, `if.then144` classifies the partial tail's two window pairs
and joins them into the accumulator, `if.then150` runs the escape list on the
arm the peel's own masks selected, and `if.then164` reads the document's last
byte and folds the partial-byte test into the verdict.  Each run is one
`denoteCode` equation at the block's own instruction list, closed by the block
tactic, so the register values are the block's computation rather than a
re-derivation.

Every block's run is stated at the environment it is entered with: the two
`<4 x i64>` words the loop's last page left, the peel's byte pointer and index,
the DFA state, the emission cursor and the accumulator.  A block whose run
writes memory or calls the escape list hands its caller the state that write or
call leaves, so the trace is parameterized by the bytes it read and the call's
outcome rather than deciding them.

`if.then164`'s trace is the document's last byte: the forward `getelementptr`
to `b + n`, the backward one to `b + n - 1`, the byte load, and the two tests
`(b % 256) & 0xfe = 0xc0` and `b % 256 > 0xf4` joined with the ASCII verdict.
-/
import LeanLLVM.Refinement.JsonS1BlocksRefine

namespace LeanLLVM.Refinement.JsonS1BlocksTail

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.BitLanes (ptestz)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- The tail's steps: the block battery plus the `i1` register `select`, which
the tail's own verdict word composes. -/
macro "tail_step" : tactic => `(tactic|
  (first
   | rw [denoteCode_select_bit_reg_imm_w _ _ _ _ _ _ _ ?_ ?_ _]
   | block_step_b))

/-- A tail block's chain, closed by the block's own close. -/
macro "tail_eval" : tactic => `(tactic|
  (repeat tail_step
   block_close_v))

/-! ### `if.then164` — the document's last byte

The block addresses `b + n`, steps back one byte, and tests the byte twice: its
high seven bits against `0xc0` and the whole byte against `0xf4`.  The two bits
are ORed into the verdict the phi hands on. -/

/-- The byte's two tests, as the block's own arithmetic reads them: the mask
drops the low bit, and the second test is the whole byte's unsigned compare. -/
def lastByteBits (last : BitVec 8) : BitVec 1 :=
  evalICmp .ugt last 0xf4#8 ||| evalICmp .eq (last &&& 0xfe#8) 0xc0#8

/-- `if.then164`'s environment: the two pointers, the byte, its mask and the
three bits, ending at the phi's verdict. -/
def ifThen164Env (env : Env) (p : Nat) (last : BitVec 8) (err : BitVec 1) : Env :=
  cells [("%or169500", .int 1 (err ||| lastByteBits last)),
         ("%204", .int 1 (lastByteBits last)),
         ("%cmp3.i", .int 1 (evalICmp .ugt last 0xf4#8)),
         ("%cmp.i", .int 1 (evalICmp .eq (last &&& 0xfe#8) 0xc0#8)),
         ("%203", .int 8 (last &&& 0xfe#8)),
         ("%202", .int 8 last),
         ("%arrayidx166", .ptr (p - 1)),
         ("%201", .ptr p)] env

theorem if_then164_denote (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (last : UInt8) (err : BitVec 1)
    (hn : lookupName env "%n" = some (.int 64 n))
    (hb : lookupName env "%b" = some (.ptr b))
    (herr : lookupName env "%cmp155" = some (.int 1 err))
    (hpos : (n.signExtend 64).toNat < 2 ^ 63)
    (hp : 1 ≤ b + (n.signExtend 64).toNat)
    (hr : readBytes s.mem (b + (n.signExtend 64).toNat - 1) 1 = some [last]) :
    denoteCode s1BlocksCalls if_then164Instrs (stateAt env s) =
      some (stateAt (ifThen164Env env (b + (n.signExtend 64).toNat) (BitVec.ofNat 8 last.toNat) err)
        s) := by
  unfold if_then164Instrs ifThen164Env
  tail_eval

theorem if_then164_step (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (last : UInt8) (err : BitVec 1)
    (hpc : s.pc = "if.then164")
    (hn : lookupName env "%n" = some (.int 64 n))
    (hb : lookupName env "%b" = some (.ptr b))
    (herr : lookupName env "%cmp155" = some (.int 1 err))
    (hpos : (n.signExtend 64).toNat < 2 ^ 63)
    (hp : 1 ≤ b + (n.signExtend 64).toNat)
    (hr : readBytes s.mem (b + (n.signExtend 64).toNat - 1) 1 = some [last]) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifThen164Env env (b + (n.signExtend 64).toNat) (BitVec.ofNat 8 last.toNat) err)
        { s with pc := "if.end170", pre := some "if.then164" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_then164Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then164
  rw [step_at hfind (if_then164_denote env s n b last err hn hb herr hpos hp hr)]
  rw [show if_then164Block.term = if_then164Term from rfl]
  simp only [if_then164Term, execTerm]
  simp only [stateAt, hpc]

/-! ### `if.then150` — the peel's escape call

The block joins the peel's two words, reads their bytes as the arm's mask and
runs the escape list at the caller's own selection: the call's outcome is the
caller's, so the run is the block's computation plus one `hc`. -/

/-- The arm's packed mask word: the bytes below `0x20`, in the shuffle's order. -/
def ifThen150QuoteWord (w136 w137 : List (BitVec 64)) : BitVec 64 :=
  BitVec.ofNat 64 (lanesToNat
    (icmpLanes .ult (bitcastVecLanes 8 64 (w136 ++ w137))
      (List.replicate 64 0x20#8)))

/-- `if.then150`'s environment: the join, its byte view, the arm's mask and the
packed word the call passes. -/
def ifThen150Env (env : Env) (w136 w137 : List (BitVec 64)) : Env :=
  cells [("%or.i467", .int 64 (ifThen150QuoteWord w136 w137)),
         ("%198", .vec 64 1
           (icmpLanes .ult (bitcastVecLanes 8 64 (w136 ++ w137))
             (List.replicate 64 0x20#8))),
         ("%197", .vec 64 8 (bitcastVecLanes 8 64 (w136 ++ w137))),
         ("%196", .vec 8 64 (w136 ++ w137))] env

theorem if_then150_denote (env : Env) (s : State)
    (w136 w137 : List (BitVec 64)) (h136 : w136.length = 4) (h137 : w137.length = 4)
    (or14 xs shr : BitVec 64) (xp nxp xcarry : Nat) (r : CallOutcome)
    (h136v : lookupName env "%136" = some (.vec 4 64 w136))
    (h137v : lookupName env "%137" = some (.vec 4 64 w137))
    (hor : lookupName env "%or14.i391" = some (.int 64 or14))
    (hxs : lookupName env "%xor.i435" = some (.int 64 xs))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hc : s1BlocksCalls "leanllvm_json_escape_list"
      [.int 64 or14, .int 64 (ifThen150QuoteWord w136 w137), .int 64 xs, .int 64 shr,
       .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next = some r) :
    denoteCode s1BlocksCalls if_then150Instrs (stateAt env s) =
      some (stateAt (ifThen150Env env w136 w137)
        { s with mem := r.mem, next := r.next }) := by
  unfold if_then150Instrs ifThen150Env
  -- the join: the shuffle's eight lanes are the two words, in operand order
  rw [denoteCode_shuffleVec (calls := s1BlocksCalls) (env := env) (s := s)
    (d := "%196") (n := 4) (w := 64) (a := .reg "%136") (b := .reg "%137")
    (mask := [0, 1, 2, 3, 4, 5, 6, 7]) (l1 := w136) (l2 := w137)
    (ls := w136 ++ w137)
    (ha := BlockEval.evalOperand_reg_of env s "%136" (.vec 4 64 w136) h136v)
    (hb := BlockEval.evalOperand_reg_of env s "%137" (.vec 4 64 w137) h137v)
    (h1 := vecLanes_self h136) (h2 := vecLanes_self h137)
    (hm := mapM_pick8 h136 h137)]
  tail_eval

theorem if_then150_step (env : Env) (s : State)
    (w136 w137 : List (BitVec 64)) (h136 : w136.length = 4) (h137 : w137.length = 4)
    (or14 xs shr : BitVec 64) (xp nxp xcarry : Nat) (r : CallOutcome)
    (hpc : s.pc = "if.then150")
    (h136v : lookupName env "%136" = some (.vec 4 64 w136))
    (h137v : lookupName env "%137" = some (.vec 4 64 w137))
    (hor : lookupName env "%or14.i391" = some (.int 64 or14))
    (hxs : lookupName env "%xor.i435" = some (.int 64 xs))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hc : s1BlocksCalls "leanllvm_json_escape_list"
      [.int 64 or14, .int 64 (ifThen150QuoteWord w136 w137), .int 64 xs, .int 64 shr,
       .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next = some r) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifThen150Env env w136 w137)
        { s with pc := "if.end153.thread", pre := some "if.then150",
                 mem := r.mem, next := r.next }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_then150Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then150
  rw [step_at hfind (if_then150_denote env s w136 w137 h136 h137 or14 xs shr xp nxp
    xcarry r h136v h137v hor hxs hshr hxp hnxp hxcarry hc)]
  rw [show if_then150Block.term = if_then150Term from rfl]
  simp only [if_then150Term, execTerm]
  simp only [stateAt, hpc]

/-! ### `if.then144` — the partial tail

The block reads three windows below the peel's pointer (the word at `-1`, the
bytes at `-2` and `-3`), classifies them with the two table lookups and the
carried low-nibble control, and repeats at `+31`, `+30` and `+29`.  The two
byte windows are each put through `usub.sat` against `0x60` and `0x70`; their
high bits are the state mask, and the two state words join into the
accumulator. -/

/-- The values `if.then144` binds, one field per destination, in binding order.
The first three are inputs: the peel's pointer and the two low-nibble controls
the classify block left. -/
structure IfThen144Values where
  addPtr171 : Nat
  w171 : List (BitVec 64)
  addPtr172 : Nat
  byte172 : List (BitVec 8)
  addPtr173 : Nat
  byte173 : List (BitVec 8)
  byte174 : List (BitVec 8)
  low175 : List (BitVec 8)
  shuf176 : List (BitVec 8)
  half177 : List (BitVec 16)
  shr178 : List (BitVec 16)
  byte179 : List (BitVec 8)
  low180 : List (BitVec 8)
  shuf181 : List (BitVec 8)
  and440 : List (BitVec 8)
  shuf182 : List (BitVec 8)
  and441 : List (BitVec 8)
  andHi442 : List (BitVec 64)
  sat443 : List (BitVec 8)
  sat444 : List (BitVec 8)
  or445 : List (BitVec 8)
  orVec446 : List (BitVec 64)
  andMask447 : List (BitVec 64)
  xor448 : List (BitVec 64)
  addPtr183 : Nat
  w183 : List (BitVec 64)
  addPtr184 : Nat
  byte184 : List (BitVec 8)
  addPtr185 : Nat
  byte185 : List (BitVec 8)
  byte186 : List (BitVec 8)
  low187 : List (BitVec 8)
  shuf188 : List (BitVec 8)
  half189 : List (BitVec 16)
  shr190 : List (BitVec 16)
  byte191 : List (BitVec 8)
  low192 : List (BitVec 8)
  shuf193 : List (BitVec 8)
  and452 : List (BitVec 8)
  shuf194 : List (BitVec 8)
  and453 : List (BitVec 8)
  andHi454 : List (BitVec 64)
  sat455 : List (BitVec 8)
  sat456 : List (BitVec 8)
  or457 : List (BitVec 8)
  orVec458 : List (BitVec 64)
  andMask459 : List (BitVec 64)
  xor460 : List (BitVec 64)
  v195 : List (BitVec 64)
  orI : List (BitVec 64)

/-- The block's computation, from the peel's pointer, the two low-nibble
controls the classify block left, the carried accumulator, and the six loaded
windows. -/
def ifThen144Values (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8) :
    IfThen144Values :=
  let addPtr171 := a - 1
  let w171 := unpackLanes 64 4 (bytesToNat bs171)
  let addPtr172 := a - 2
  let byte172 := bs172.map fun b => BitVec.ofNat 8 b.toNat
  let addPtr173 := a - 3
  let byte173 := bs173.map fun b => BitVec.ofNat 8 b.toNat
  let byte174 := bitcastVecLanes 8 32 w171
  let low175 := byte174.map fun x => x &&& 0x0f#8
  let shuf176 := pshufbLanes ifThen38TableHi low175
  let half177 := bitcastVecLanes 16 16 w171
  let shr178 := half177.map fun x : BitVec 16 => x >>> (0x0004#16).toNat
  let byte179 := bitcastVecLanes 8 32 shr178
  let low180 := byte179.map fun x => x &&& 0x0f#8
  let shuf181 := pshufbLanes ifThen38TableMid low180
  let and440 := List.zipWith (fun x y => x &&& y) shuf181 shuf176
  let shuf182 := pshufbLanes ifThen38TableLo lo103
  let and441 := List.zipWith (fun x y => x &&& y) and440 shuf182
  let andHi442 := bitcastVecLanes 64 4 and441
  let sat443 := List.zipWith BitLanes.subsSat byte172 (List.replicate 32 0x60#8)
  let sat444 := List.zipWith BitLanes.subsSat byte173 (List.replicate 32 0x70#8)
  let or445 := List.zipWith (fun x y => x ||| y) sat444 sat443
  let orVec446 := bitcastVecLanes 64 4 or445
  let andMask447 := orVec446.map fun x => x &&& 0x8080808080808080#64
  let xor448 := List.zipWith (fun x y => x ^^^ y) andMask447 andHi442
  let addPtr183 := a + ((0x000000000000001f#64).signExtend 64).toNat
  let w183 := unpackLanes 64 4 (bytesToNat bs183)
  let addPtr184 := a + ((0x000000000000001e#64).signExtend 64).toNat
  let byte184 := bs184.map fun b => BitVec.ofNat 8 b.toNat
  let addPtr185 := a + ((0x000000000000001d#64).signExtend 64).toNat
  let byte185 := bs185.map fun b => BitVec.ofNat 8 b.toNat
  let byte186 := bitcastVecLanes 8 32 w183
  let low187 := byte186.map fun x => x &&& 0x0f#8
  let shuf188 := pshufbLanes ifThen38TableHi low187
  let half189 := bitcastVecLanes 16 16 w183
  let shr190 := half189.map fun x : BitVec 16 => x >>> (0x0004#16).toNat
  let byte191 := bitcastVecLanes 8 32 shr190
  let low192 := byte191.map fun x => x &&& 0x0f#8
  let shuf193 := pshufbLanes ifThen38TableMid low192
  let and452 := List.zipWith (fun x y => x &&& y) shuf193 shuf188
  let shuf194 := pshufbLanes ifThen38TableLo lo161
  let and453 := List.zipWith (fun x y => x &&& y) and452 shuf194
  let andHi454 := bitcastVecLanes 64 4 and453
  let sat455 := List.zipWith BitLanes.subsSat byte184 (List.replicate 32 0x60#8)
  let sat456 := List.zipWith BitLanes.subsSat byte185 (List.replicate 32 0x70#8)
  let or457 := List.zipWith (fun x y => x ||| y) sat456 sat455
  let orVec458 := bitcastVecLanes 64 4 or457
  let andMask459 := orVec458.map fun x => x &&& 0x8080808080808080#64
  let xor460 := List.zipWith (fun x y => x ^^^ y) andMask459 andHi454
  let v195 := List.zipWith (fun x y => x ||| y) xor448 xor460
  let orI := List.zipWith (fun x y => x ||| y) v195 u8k
  { addPtr171, w171, addPtr172, byte172, addPtr173, byte173, byte174, low175,
    shuf176, half177, shr178, byte179, low180, shuf181, and440, shuf182, and441,
    andHi442, sat443, sat444, or445, orVec446, andMask447, xor448, addPtr183,
    w183, addPtr184, byte184, addPtr185, byte185, byte186, low187, shuf188,
    half189, shr190, byte191, low192, shuf193, and452, shuf194, and453, andHi454,
    sat455, sat456, or457, orVec458, andMask459, xor460, v195, orI }

/-- The environment after the three windows below the pointer. -/
def ift144Env1 (env : Env) (v : IfThen144Values) : Env :=
  cells [("%173", .vec 32 8 v.byte173),
         ("%add.ptr5.i.i439", .ptr v.addPtr173),
         ("%172", .vec 32 8 v.byte172),
         ("%add.ptr3.i.i438", .ptr v.addPtr172),
         ("%171", .vec 4 64 v.w171),
         ("%add.ptr.i.i437", .ptr v.addPtr171)] env

/-- The environment after the first window's two table lookups and their join. -/
def ift144Env2 (env : Env) (v : IfThen144Values) : Env :=
  cells [("%and.i3741.i.i440", .vec 32 8 v.and440),
         ("%181", .vec 32 8 v.shuf181),
         ("%180", .vec 32 8 v.low180),
         ("%179", .vec 32 8 v.byte179),
         ("%178", .vec 16 16 v.shr178),
         ("%177", .vec 16 16 v.half177),
         ("%176", .vec 32 8 v.shuf176),
         ("%175", .vec 32 8 v.low175),
         ("%174", .vec 32 8 v.byte174)] (ift144Env1 env v)

/-- The environment after the first low-table join, the first window's
subtracts and their high-bit mask. -/
def ift144Env3 (env : Env) (v : IfThen144Values) : Env :=
  cells [("%xor.i.i.i448", .vec 4 64 v.xor448),
         ("%and.i.i.i447", .vec 4 64 v.andMask447),
         ("%or.i.i.i446", .vec 4 64 v.orVec446),
         ("%or.i43.i.i445", .vec 32 8 v.or445),
         ("%elt.sat.i.i.i444", .vec 32 8 v.sat444),
         ("%elt.sat.i40.i.i443", .vec 32 8 v.sat443),
         ("%and.i35.i.i442", .vec 4 64 v.andHi442),
         ("%and.i3542.i.i441", .vec 32 8 v.and441),
         ("%182", .vec 32 8 v.shuf182)] (ift144Env2 env v)

/-- The environment after the three windows above the pointer are loaded. -/
def ift144Env4 (env : Env) (v : IfThen144Values) : Env :=
  cells [("%185", .vec 32 8 v.byte185),
         ("%add.ptr5.i6.i451", .ptr v.addPtr185),
         ("%184", .vec 32 8 v.byte184),
         ("%add.ptr3.i5.i450", .ptr v.addPtr184),
         ("%183", .vec 4 64 v.w183),
         ("%add.ptr.i4.i449", .ptr v.addPtr183)] (ift144Env3 env v)

/-- The environment after the second window's two table lookups and their
join. -/
def ift144Env5 (env : Env) (v : IfThen144Values) : Env :=
  cells [("%and.i3741.i7.i452", .vec 32 8 v.and452),
         ("%193", .vec 32 8 v.shuf193),
         ("%192", .vec 32 8 v.low192),
         ("%191", .vec 32 8 v.byte191),
         ("%190", .vec 16 16 v.shr190),
         ("%189", .vec 16 16 v.half189),
         ("%188", .vec 32 8 v.shuf188),
         ("%187", .vec 32 8 v.low187),
         ("%186", .vec 32 8 v.byte186)] (ift144Env4 env v)

/-- The environment after the second low-table join, the second window's
subtracts, the two state masks and the accumulator's join. -/
def ift144Env6 (env : Env) (v : IfThen144Values) : Env :=
  cells [("%or.i", .vec 4 64 v.orI),
         ("%195", .vec 4 64 v.v195),
         ("%xor.i.i15.i460", .vec 4 64 v.xor460),
         ("%and.i.i14.i459", .vec 4 64 v.andMask459),
         ("%or.i.i13.i458", .vec 4 64 v.orVec458),
         ("%or.i43.i12.i457", .vec 32 8 v.or457),
         ("%elt.sat.i.i11.i456", .vec 32 8 v.sat456),
         ("%elt.sat.i40.i10.i455", .vec 32 8 v.sat455),
         ("%and.i35.i9.i454", .vec 4 64 v.andHi454),
         ("%and.i3542.i8.i453", .vec 32 8 v.and453),
         ("%194", .vec 32 8 v.shuf194)] (ift144Env5 env v)

/-- `if.then144`'s environment: everything the block binds. -/
def ifThen144Out (env : Env) (v : IfThen144Values) : Env := ift144Env6 env v

/-- `if.then144`'s run at its six segment boundaries. -/
def ifThen144Seg1 : List Instr := if_then144Instrs.take 6
def ifThen144Seg2 : List Instr := (if_then144Instrs.drop 6).take 9
def ifThen144Seg3 : List Instr := (if_then144Instrs.drop 15).take 9
def ifThen144Seg4 : List Instr := (if_then144Instrs.drop 24).take 6
def ifThen144Seg5 : List Instr := (if_then144Instrs.drop 30).take 9
def ifThen144Seg6 : List Instr := (if_then144Instrs.drop 39).take 11

/-! ### `if.then144`'s lane-list lengths

Each stored vector's lane count is structural from the loaded window or the two
nibble tables it was shuffled with, so these projections close from the loaded
windows' and the controls' lengths. -/

theorem ifThen144Values_and440_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).and440.length
      = 32 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length,
    JsonS1MasksSteps.pshufbLanes_length, List.length_zipWith, List.length_map]

theorem ifThen144Values_and441_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h103len : lo103.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).and441.length
      = 32 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length,
    JsonS1MasksSteps.pshufbLanes_length, List.length_zipWith, List.length_map, h103len]

theorem ifThen144Values_andHi442_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h103len : lo103.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).andHi442.length
      = 4 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length,
    JsonS1MasksSteps.pshufbLanes_length, List.length_zipWith, List.length_map, h103len]

theorem ifThen144Values_sat443_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h172len : bs172.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).sat443.length
      = 32 := by
  simp [ifThen144Values, List.length_zipWith, List.length_map, h172len]

theorem ifThen144Values_sat444_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h173len : bs173.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).sat444.length
      = 32 := by
  simp [ifThen144Values, List.length_zipWith, List.length_map, h173len]

theorem ifThen144Values_or445_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h172len : bs172.length = 32) (h173len : bs173.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).or445.length
      = 32 := by
  simp [ifThen144Values, List.length_zipWith, List.length_map, h172len, h173len]

theorem ifThen144Values_orVec446_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h172len : bs172.length = 32) (h173len : bs173.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).orVec446.length
      = 4 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length, List.length_zipWith,
    List.length_map, List.length_replicate, h172len, h173len]

theorem ifThen144Values_andMask447_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h172len : bs172.length = 32) (h173len : bs173.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).andMask447.length
      = 4 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length, List.length_zipWith,
    List.length_map, List.length_replicate, h172len, h173len]

theorem ifThen144Values_xor448_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h172len : bs172.length = 32) (h173len : bs173.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).xor448.length
      = 4 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length, List.length_zipWith,
    List.length_map, List.length_replicate, h172len, h173len]

theorem ifThen144Values_and452_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).and452.length
      = 32 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length,
    JsonS1MasksSteps.pshufbLanes_length, List.length_zipWith, List.length_map]

theorem ifThen144Values_and453_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h161len : lo161.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).and453.length
      = 32 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length,
    JsonS1MasksSteps.pshufbLanes_length, List.length_zipWith, List.length_map, h161len]

theorem ifThen144Values_andHi454_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h161len : lo161.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).andHi454.length
      = 4 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length,
    JsonS1MasksSteps.pshufbLanes_length, List.length_zipWith, List.length_map, h161len]

theorem ifThen144Values_sat455_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h184len : bs184.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).sat455.length
      = 32 := by
  simp [ifThen144Values, List.length_zipWith, List.length_map, h184len]

theorem ifThen144Values_sat456_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h185len : bs185.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).sat456.length
      = 32 := by
  simp [ifThen144Values, List.length_zipWith, List.length_map, h185len]

theorem ifThen144Values_or457_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h184len : bs184.length = 32) (h185len : bs185.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).or457.length
      = 32 := by
  simp [ifThen144Values, List.length_zipWith, List.length_map, h184len, h185len]

theorem ifThen144Values_orVec458_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h184len : bs184.length = 32) (h185len : bs185.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).orVec458.length
      = 4 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length, List.length_zipWith,
    List.length_map, List.length_replicate, h184len, h185len]

theorem ifThen144Values_andMask459_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h184len : bs184.length = 32) (h185len : bs185.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).andMask459.length
      = 4 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length, List.length_zipWith,
    List.length_map, List.length_replicate, h184len, h185len]

theorem ifThen144Values_xor460_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h184len : bs184.length = 32) (h185len : bs185.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).xor460.length
      = 4 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length, List.length_zipWith,
    List.length_map, List.length_replicate, h184len, h185len]

theorem ifThen144Values_v195_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h172len : bs172.length = 32) (h173len : bs173.length = 32)
    (h184len : bs184.length = 32) (h185len : bs185.length = 32) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).v195.length
      = 4 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length, List.length_zipWith,
    List.length_map, List.length_replicate, h172len, h173len, h184len, h185len]

theorem ifThen144Values_orI_length (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h172len : bs172.length = 32) (h173len : bs173.length = 32)
    (h184len : bs184.length = 32) (h185len : bs185.length = 32)
    (huk : u8k.length = 4) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).orI.length
      = 4 := by
  simp [ifThen144Values, bitcastVecLanes, unpackLanes_length, List.length_zipWith,
    List.length_map, List.length_replicate, h172len, h173len, h184len, h185len, huk]

/-- **`if.then144`'s first segment.**  The `-1` word and the `-2` and `-3` byte
windows, the backward `getelementptr`s the peel's pointer carries. -/
theorem if_then144_seg1 (env : Env) (s : State) (a : Nat)
    (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (hadd : lookupName env "%add.ptr106" = some (.ptr a))
    (h1 : 1 ≤ a) (h171 : readBytes s.mem (a - 1) 32 = some bs171)
    (h2 : 2 ≤ a) (h172 : readBytes s.mem (a - 2) 32 = some bs172)
    (h3 : 3 ≤ a) (h173 : readBytes s.mem (a - 3) 32 = some bs173) :
    let v := ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
    denoteCode s1BlocksCalls ifThen144Seg1 (stateAt env s) =
      some (stateAt (ift144Env1 env v) s) := by
  intro v
  unfold ifThen144Seg1 ift144Env1
  simp only [if_then144Instrs, List.take, List.drop]
  block_eval_b

/-- **`if.then144`'s second segment.**  The first window's two table lookups and
their join. -/
theorem if_then144_seg2 (env : Env) (s : State) (a : Nat)
    (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8) :
    let v := ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
    denoteCode s1BlocksCalls ifThen144Seg2 (stateAt (ift144Env1 env v) s) =
      some (stateAt (ift144Env2 env v) s) := by
  intro v
  unfold ifThen144Seg2 ift144Env1 ift144Env2
  simp only [if_then144Instrs, List.take, List.drop]
  block_eval_b

/-- **`if.then144`'s third segment.**  The first control's low-table lookup,
its join with the class masks, and the first window's two subtracts and state
mask. -/
theorem if_then144_seg3 (env : Env) (s : State) (a : Nat)
    (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h103 : lookupName env "%152" = some (.vec 32 8 lo103))
    (h103len : lo103.length = 32)
    (h172len : bs172.length = 32) (h173len : bs173.length = 32) :
    let v := ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
    denoteCode s1BlocksCalls ifThen144Seg3 (stateAt (ift144Env2 env v) s) =
      some (stateAt (ift144Env3 env v) s) := by
  intro v
  have htabFold : ifThen38TableLo =
      [0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8,
       0xe6#8, 0xae#8, 0xba#8, 0xba#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8,
       0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8,
       0xe6#8, 0xae#8, 0xba#8, 0xba#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8] := rfl
  unfold ifThen144Seg3
  simp only [if_then144Instrs, List.take, List.drop]
  rw [← htabFold]
  block_step_b
  rw [denoteCode_binopVec s1BlocksCalls _ s "%and.i3542.i.i441" .and 32 8
        (.reg "%and.i3741.i.i440") (.reg "%182")
        (va := .vec 32 8 v.and440)
        (vb := .vec 32 8 (pshufbLanes ifThen38TableLo lo103))
        (l1 := v.and440) (l2 := pshufbLanes ifThen38TableLo lo103) (ls := v.and441)
        (BlockEval.evalOperand_reg_of _ _ "%and.i3741.i.i440" (.vec 32 8 v.and440)
          (by simp only [ift144Env2, ift144Env1, cells]; block_lk_cons))
        (BlockEval.evalOperand_reg_of _ _ "%182"
          (.vec 32 8 (pshufbLanes ifThen38TableLo lo103))
          (lookupName_cons_self _ _ _))
        (vecLanes_self
          (ifThen144Values_and440_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185))
        (vecLanes_self (by rw [JsonS1MasksSteps.pshufbLanes_length]; omega))
        (by rw [binopLanes_zipWith .and (fun x y => x &&& y) (fun x y => rfl)
              v.and440 (pshufbLanes ifThen38TableLo lo103) (by
                rw [ifThen144Values_and440_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185,
                  JsonS1MasksSteps.pshufbLanes_length]
                omega)]
            rfl)]
  rw [denoteCode_vecBitcast s1BlocksCalls _ s "%and.i35.i.i442" 32 8 4 64
        (.reg "%and.i3542.i.i441")
        (BlockEval.evalOperand_reg_of _ _ "%and.i3542.i.i441" (.vec 32 8 v.and441)
          (lookupName_cons_self _ _ _))
        (vecLanes_self
          (ifThen144Values_and441_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
            h103len))
        (by decide)]
  rw [denoteCode_usubSat_b _ s "%elt.sat.i40.i.i443" (.reg "%172")
        (.imm (.splat 32 8 0x60#8))
        (a := v.byte172) (b := List.replicate 32 0x60#8)
        (BlockEval.evalOperand_reg_of _ _ "%172" (.vec 32 8 v.byte172)
          (by simp only [ift144Env2, ift144Env1, cells]; block_lk_cons))
        (by simp only [evalOperand, Const.toValue, lanesOf, splatOf])]
  rw [denoteCode_usubSat_b _ s "%elt.sat.i.i.i444" (.reg "%173")
        (.imm (.splat 32 8 0x70#8))
        (a := v.byte173) (b := List.replicate 32 0x70#8)
        (BlockEval.evalOperand_reg_of _ _ "%173" (.vec 32 8 v.byte173)
          (by simp only [ift144Env2, ift144Env1, cells]; block_lk_cons))
        (by simp only [evalOperand, Const.toValue, lanesOf, splatOf])]
  rw [denoteCode_binopVec s1BlocksCalls _ s "%or.i43.i.i445" .or 32 8
        (.reg "%elt.sat.i.i.i444") (.reg "%elt.sat.i40.i.i443")
        (va := .vec 32 8 (List.zipWith BitLanes.subsSat v.byte173 (List.replicate 32 0x70#8)))
        (vb := .vec 32 8 (List.zipWith BitLanes.subsSat v.byte172 (List.replicate 32 0x60#8)))
        (l1 := List.zipWith BitLanes.subsSat v.byte173 (List.replicate 32 0x70#8))
        (l2 := List.zipWith BitLanes.subsSat v.byte172 (List.replicate 32 0x60#8))
        (ls := v.or445)
        (BlockEval.evalOperand_reg_of _ _ "%elt.sat.i.i.i444"
          (.vec 32 8 (List.zipWith BitLanes.subsSat v.byte173 (List.replicate 32 0x70#8)))
          (lookupName_cons_self _ _ _))
        (BlockEval.evalOperand_reg_of _ _ "%elt.sat.i40.i.i443"
          (.vec 32 8 (List.zipWith BitLanes.subsSat v.byte172 (List.replicate 32 0x60#8)))
          (by block_lk_cons))
        (vecLanes_self
          (by simp (config := { zetaDelta := true }) only [ifThen144Values, List.length_zipWith,
                List.length_map, List.length_replicate, h173len]; decide))
        (vecLanes_self
          (by simp (config := { zetaDelta := true }) only [ifThen144Values, List.length_zipWith,
                List.length_map, List.length_replicate, h172len]; decide))
        (by rw [binopLanes_zipWith .or (fun x y => x ||| y) (fun x y => rfl)
              (List.zipWith BitLanes.subsSat v.byte173 (List.replicate 32 0x70#8))
              (List.zipWith BitLanes.subsSat v.byte172 (List.replicate 32 0x60#8))
              (by simp (config := { zetaDelta := true }) only [ifThen144Values,
                    List.length_zipWith, List.length_map, List.length_replicate, h172len, h173len])]
            rfl)]
  rw [denoteCode_vecBitcast s1BlocksCalls _ s "%or.i.i.i446" 32 8 4 64
        (.reg "%or.i43.i.i445")
        (BlockEval.evalOperand_reg_of _ _ "%or.i43.i.i445" (.vec 32 8 v.or445)
          (lookupName_cons_self _ _ _))
        (vecLanes_self
          (ifThen144Values_or445_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
            h172len h173len))
        (by decide)]
  rw [denoteCode_binopVec s1BlocksCalls _ s "%and.i.i.i447" .and 4 64
        (.reg "%or.i.i.i446") (.imm (.splat 4 64 0x8080808080808080#64))
        (va := .vec 4 64 (bitcastVecLanes 64 4 v.or445))
        (vb := .vec 4 64 (List.replicate 4 0x8080808080808080#64))
        (l1 := bitcastVecLanes 64 4 v.or445)
        (l2 := List.replicate 4 0x8080808080808080#64)
        (ls := v.andMask447)
        (BlockEval.evalOperand_reg_of _ _ "%or.i.i.i446"
          (.vec 4 64 (bitcastVecLanes 64 4 v.or445))
          (lookupName_cons_self _ _ _))
        (by simp only [evalOperand, Const.toValue, lanesOf, splatOf])
        (vecLanes_self (by simp [bitcastVecLanes, unpackLanes_length]))
        (vecLanes_self (by decide))
        (by rw [binopLanes_replicate .and (fun x y => x &&& y) (fun x y => rfl)
              (bitcastVecLanes 64 4 v.or445) 4
              (by simp [bitcastVecLanes, unpackLanes_length])
              0x8080808080808080#64]
            rfl)]
  rw [denoteCode_binopVec s1BlocksCalls _ s "%xor.i.i.i448" .xor 4 64
        (.reg "%and.i.i.i447") (.reg "%and.i35.i.i442")
        (va := .vec 4 64 v.andMask447)
        (vb := .vec 4 64 (bitcastVecLanes 64 4 v.and441))
        (l1 := v.andMask447) (l2 := bitcastVecLanes 64 4 v.and441) (ls := v.xor448)
        (BlockEval.evalOperand_reg_of _ _ "%and.i.i.i447" (.vec 4 64 v.andMask447)
          (lookupName_cons_self _ _ _))
        (BlockEval.evalOperand_reg_of _ _ "%and.i35.i.i442"
          (.vec 4 64 (bitcastVecLanes 64 4 v.and441))
          (by block_lk_cons))
        (vecLanes_self
          (ifThen144Values_andMask447_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
            h172len h173len))
        (vecLanes_self (by simp [bitcastVecLanes, unpackLanes_length]))
        (by rw [binopLanes_zipWith .xor (fun x y => x ^^^ y) (fun x y => rfl)
              v.andMask447 (bitcastVecLanes 64 4 v.and441) (by
                rw [ifThen144Values_andMask447_length a lo103 lo161 u8k bs171 bs172 bs173
                  bs183 bs184 bs185 h172len h173len]
                simp [bitcastVecLanes, unpackLanes_length])]
            rfl)]
  rfl
  all_goals (first
    | exact BlockEval.evalOperand_reg_of _ _ "%152" (.vec 32 8 lo103) h103
    | decide)

/-- **`if.then144`'s fourth segment.**  The word and the two byte windows above
the pointer. -/
theorem if_then144_seg4 (env : Env) (s : State) (a : Nat)
    (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h183 : readBytes s.mem
      (a + ((0x000000000000001f#64).signExtend 64).toNat) 32 = some bs183)
    (h184 : readBytes s.mem
      (a + ((0x000000000000001e#64).signExtend 64).toNat) 32 = some bs184)
    (h185 : readBytes s.mem
      (a + ((0x000000000000001d#64).signExtend 64).toNat) 32 = some bs185) :
    let v := ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
    lookupName (ift144Env3 env v) "%add.ptr106" = some (.ptr a) →
    denoteCode s1BlocksCalls ifThen144Seg4 (stateAt (ift144Env3 env v) s) =
      some (stateAt (ift144Env4 env v) s) := by
  intro v hadd
  unfold ifThen144Seg4 ift144Env3 ift144Env4
  simp only [if_then144Instrs, List.take, List.drop]
  block_eval_b

/-- **`if.then144`'s fifth segment.**  The second window's two table lookups
and their join. -/
theorem if_then144_seg5 (env : Env) (s : State) (a : Nat)
    (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8) :
    let v := ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
    denoteCode s1BlocksCalls ifThen144Seg5 (stateAt (ift144Env4 env v) s) =
      some (stateAt (ift144Env5 env v) s) := by
  intro v
  unfold ifThen144Seg5 ift144Env4 ift144Env5
  simp only [if_then144Instrs, List.take, List.drop]
  block_eval_b

/-- **`if.then144`'s sixth segment.**  The second control's low-table lookup,
its joins, and the accumulator's join through the carried word. -/
theorem if_then144_seg6 (env : Env) (s : State) (a : Nat)
    (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (h161 : lookupName env "%161" = some (.vec 32 8 lo161))
    (hu : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (h161len : lo161.length = 32)
    (h172len : bs172.length = 32) (h173len : bs173.length = 32)
    (h184len : bs184.length = 32) (h185len : bs185.length = 32)
    (huk : u8k.length = 4) :
    let v := ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
    denoteCode s1BlocksCalls ifThen144Seg6 (stateAt (ift144Env5 env v) s) =
      some (stateAt (ift144Env6 env v) s) := by
  intro v
  have htabFold : ifThen38TableLo =
      [0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8,
       0xe6#8, 0xae#8, 0xba#8, 0xba#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8,
       0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8,
       0xe6#8, 0xae#8, 0xba#8, 0xba#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8] := rfl
  unfold ifThen144Seg6
  simp only [if_then144Instrs, List.take, List.drop]
  rw [← htabFold]
  block_step_b
  rw [denoteCode_binopVec s1BlocksCalls _ s "%and.i3542.i8.i453" .and 32 8
        (.reg "%and.i3741.i7.i452") (.reg "%194")
        (va := .vec 32 8 v.and452)
        (vb := .vec 32 8 (pshufbLanes ifThen38TableLo lo161))
        (l1 := v.and452) (l2 := pshufbLanes ifThen38TableLo lo161) (ls := v.and453)
        (BlockEval.evalOperand_reg_of _ _ "%and.i3741.i7.i452" (.vec 32 8 v.and452)
          (by simp only [ift144Env5, ift144Env4, ift144Env3, ift144Env2, ift144Env1, cells];
              block_lk_cons))
        (BlockEval.evalOperand_reg_of _ _ "%194"
          (.vec 32 8 (pshufbLanes ifThen38TableLo lo161))
          (lookupName_cons_self _ _ _))
        (vecLanes_self
          (ifThen144Values_and452_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185))
        (vecLanes_self (by rw [JsonS1MasksSteps.pshufbLanes_length]; omega))
        (by rw [binopLanes_zipWith .and (fun x y => x &&& y) (fun x y => rfl)
              v.and452 (pshufbLanes ifThen38TableLo lo161) (by
                rw [ifThen144Values_and452_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185,
                  JsonS1MasksSteps.pshufbLanes_length]
                omega)]
            rfl)]
  rw [denoteCode_vecBitcast s1BlocksCalls _ s "%and.i35.i9.i454" 32 8 4 64
        (.reg "%and.i3542.i8.i453")
        (BlockEval.evalOperand_reg_of _ _ "%and.i3542.i8.i453" (.vec 32 8 v.and453)
          (lookupName_cons_self _ _ _))
        (vecLanes_self
          (ifThen144Values_and453_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
            h161len))
        (by decide)]
  rw [denoteCode_usubSat_b _ s "%elt.sat.i40.i10.i455" (.reg "%184")
        (.imm (.splat 32 8 0x60#8))
        (a := v.byte184) (b := List.replicate 32 0x60#8)
        (BlockEval.evalOperand_reg_of _ _ "%184" (.vec 32 8 v.byte184)
          (by simp only [ift144Env5, ift144Env4, ift144Env3, ift144Env2, ift144Env1, cells];
              block_lk_cons))
        (by simp only [evalOperand, Const.toValue, lanesOf, splatOf])]
  rw [denoteCode_usubSat_b _ s "%elt.sat.i.i11.i456" (.reg "%185")
        (.imm (.splat 32 8 0x70#8))
        (a := v.byte185) (b := List.replicate 32 0x70#8)
        (BlockEval.evalOperand_reg_of _ _ "%185" (.vec 32 8 v.byte185)
          (by simp only [ift144Env5, ift144Env4, ift144Env3, ift144Env2, ift144Env1, cells];
              block_lk_cons))
        (by simp only [evalOperand, Const.toValue, lanesOf, splatOf])]
  rw [denoteCode_binopVec s1BlocksCalls _ s "%or.i43.i12.i457" .or 32 8
        (.reg "%elt.sat.i.i11.i456") (.reg "%elt.sat.i40.i10.i455")
        (va := .vec 32 8 (List.zipWith BitLanes.subsSat v.byte185 (List.replicate 32 0x70#8)))
        (vb := .vec 32 8 (List.zipWith BitLanes.subsSat v.byte184 (List.replicate 32 0x60#8)))
        (l1 := List.zipWith BitLanes.subsSat v.byte185 (List.replicate 32 0x70#8))
        (l2 := List.zipWith BitLanes.subsSat v.byte184 (List.replicate 32 0x60#8))
        (ls := v.or457)
        (BlockEval.evalOperand_reg_of _ _ "%elt.sat.i.i11.i456"
          (.vec 32 8 (List.zipWith BitLanes.subsSat v.byte185 (List.replicate 32 0x70#8)))
          (lookupName_cons_self _ _ _))
        (BlockEval.evalOperand_reg_of _ _ "%elt.sat.i40.i10.i455"
          (.vec 32 8 (List.zipWith BitLanes.subsSat v.byte184 (List.replicate 32 0x60#8)))
          (by block_lk_cons))
        (vecLanes_self
          (by simp (config := { zetaDelta := true }) only [ifThen144Values, List.length_zipWith,
                List.length_map, List.length_replicate, h185len]; decide))
        (vecLanes_self
          (by simp (config := { zetaDelta := true }) only [ifThen144Values, List.length_zipWith,
                List.length_map, List.length_replicate, h184len]; decide))
        (by rw [binopLanes_zipWith .or (fun x y => x ||| y) (fun x y => rfl)
              (List.zipWith BitLanes.subsSat v.byte185 (List.replicate 32 0x70#8))
              (List.zipWith BitLanes.subsSat v.byte184 (List.replicate 32 0x60#8))
              (by simp (config := { zetaDelta := true }) only [ifThen144Values,
                    List.length_zipWith, List.length_map, List.length_replicate, h184len, h185len])]
            rfl)]
  rw [denoteCode_vecBitcast s1BlocksCalls _ s "%or.i.i13.i458" 32 8 4 64
        (.reg "%or.i43.i12.i457")
        (BlockEval.evalOperand_reg_of _ _ "%or.i43.i12.i457" (.vec 32 8 v.or457)
          (lookupName_cons_self _ _ _))
        (vecLanes_self
          (ifThen144Values_or457_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
            h184len h185len))
        (by decide)]
  rw [denoteCode_binopVec s1BlocksCalls _ s "%and.i.i14.i459" .and 4 64
        (.reg "%or.i.i13.i458") (.imm (.splat 4 64 0x8080808080808080#64))
        (va := .vec 4 64 (bitcastVecLanes 64 4 v.or457))
        (vb := .vec 4 64 (List.replicate 4 0x8080808080808080#64))
        (l1 := bitcastVecLanes 64 4 v.or457)
        (l2 := List.replicate 4 0x8080808080808080#64)
        (ls := v.andMask459)
        (BlockEval.evalOperand_reg_of _ _ "%or.i.i13.i458"
          (.vec 4 64 (bitcastVecLanes 64 4 v.or457))
          (lookupName_cons_self _ _ _))
        (by simp only [evalOperand, Const.toValue, lanesOf, splatOf])
        (vecLanes_self (by simp [bitcastVecLanes, unpackLanes_length]))
        (vecLanes_self (by decide))
        (by rw [binopLanes_replicate .and (fun x y => x &&& y) (fun x y => rfl)
              (bitcastVecLanes 64 4 v.or457) 4
              (by simp [bitcastVecLanes, unpackLanes_length])
              0x8080808080808080#64]
            rfl)]
  rw [denoteCode_binopVec s1BlocksCalls _ s "%xor.i.i15.i460" .xor 4 64
        (.reg "%and.i.i14.i459") (.reg "%and.i35.i9.i454")
        (va := .vec 4 64 v.andMask459)
        (vb := .vec 4 64 (bitcastVecLanes 64 4 v.and453))
        (l1 := v.andMask459) (l2 := bitcastVecLanes 64 4 v.and453) (ls := v.xor460)
        (BlockEval.evalOperand_reg_of _ _ "%and.i.i14.i459" (.vec 4 64 v.andMask459)
          (lookupName_cons_self _ _ _))
        (BlockEval.evalOperand_reg_of _ _ "%and.i35.i9.i454"
          (.vec 4 64 (bitcastVecLanes 64 4 v.and453))
          (by block_lk_cons))
        (vecLanes_self
          (ifThen144Values_andMask459_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
            h184len h185len))
        (vecLanes_self (by simp [bitcastVecLanes, unpackLanes_length]))
        (by rw [binopLanes_zipWith .xor (fun x y => x ^^^ y) (fun x y => rfl)
              v.andMask459 (bitcastVecLanes 64 4 v.and453) (by
                rw [ifThen144Values_andMask459_length a lo103 lo161 u8k bs171 bs172 bs173
                  bs183 bs184 bs185 h184len h185len]
                simp [bitcastVecLanes, unpackLanes_length])]
            rfl)]
  rw [denoteCode_binopVec s1BlocksCalls _ s "%195" .or 4 64
        (.reg "%xor.i.i.i448") (.reg "%xor.i.i15.i460")
        (va := .vec 4 64 v.xor448) (vb := .vec 4 64 v.xor460)
        (l1 := v.xor448) (l2 := v.xor460) (ls := v.v195)
        (BlockEval.evalOperand_reg_of _ _ "%xor.i.i.i448" (.vec 4 64 v.xor448)
          (by simp only [ift144Env5, ift144Env4, ift144Env3, ift144Env2, ift144Env1, cells];
              block_lk_cons))
        (BlockEval.evalOperand_reg_of _ _ "%xor.i.i15.i460" (.vec 4 64 v.xor460)
          (lookupName_cons_self _ _ _))
        (vecLanes_self
          (ifThen144Values_xor448_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
            h172len h173len))
        (vecLanes_self
          (ifThen144Values_xor460_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
            h184len h185len))
        (by rw [binopLanes_zipWith .or (fun x y => x ||| y) (fun x y => rfl)
              v.xor448 v.xor460 (by
                rw [ifThen144Values_xor448_length a lo103 lo161 u8k bs171 bs172 bs173 bs183
                  bs184 bs185 h172len h173len,
                  ifThen144Values_xor460_length a lo103 lo161 u8k bs171 bs172 bs173 bs183
                  bs184 bs185 h184len h185len])]
            rfl)]
  have h195 : v.v195.length = 4 :=
    ifThen144Values_v195_length a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
      h172len h173len h184len h185len
  have hm : binopLanes .or v.v195 u8k =
      some (List.zipWith (fun x y => x ||| y) v.v195 u8k) :=
    binopLanes_zipWith .or (fun x y => x ||| y) (fun x y => rfl) v.v195 u8k
      (by rw [ifThen144Values_v195_length a lo103 lo161 u8k bs171 bs172 bs173 bs183
        bs184 bs185 h172len h173len h184len h185len, huk])
  block_step_b
  block_close_v
  all_goals (try (exact hm))

/-- `if.then144`'s six segments, in order. -/
theorem if_then144Instrs_split :
    if_then144Instrs =
      ifThen144Seg1 ++ (ifThen144Seg2 ++ (ifThen144Seg3 ++
        (ifThen144Seg4 ++ (ifThen144Seg5 ++ ifThen144Seg6)))) := rfl

/-- The peel's pointer is not a cell the block binds, so the fourth segment
still reaches it through the three environments before it. -/
theorem lookupName_ift144Env3_addptr (env : Env) (v : IfThen144Values) {a : Nat}
    (h : lookupName env "%add.ptr106" = some (.ptr a)) :
    lookupName (ift144Env3 env v) "%add.ptr106" = some (.ptr a) := by
  unfold ift144Env3 ift144Env2 ift144Env1
  simp only [cells]
  block_lk_cons

/-- **`if.then144`'s run.**  The three windows below the pointer and the first
window's class masks hand their environment to the three windows above the
pointer, whose class masks and the classify block's second control leave the
accumulator's word. -/
theorem if_then144_denote (env : Env) (s : State) (a : Nat)
    (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (hadd : lookupName env "%add.ptr106" = some (.ptr a))
    (h1 : 1 ≤ a) (h171 : readBytes s.mem (a - 1) 32 = some bs171)
    (h2 : 2 ≤ a) (h172 : readBytes s.mem (a - 2) 32 = some bs172)
    (h3 : 3 ≤ a) (h173 : readBytes s.mem (a - 3) 32 = some bs173)
    (h103 : lookupName env "%152" = some (.vec 32 8 lo103))
    (h103len : lo103.length = 32)
    (h161 : lookupName env "%161" = some (.vec 32 8 lo161))
    (h161len : lo161.length = 32)
    (hu : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (huk : u8k.length = 4)
    (h183 : readBytes s.mem
      (a + ((0x000000000000001f#64).signExtend 64).toNat) 32 = some bs183)
    (h184 : readBytes s.mem
      (a + ((0x000000000000001e#64).signExtend 64).toNat) 32 = some bs184)
    (h185 : readBytes s.mem
      (a + ((0x000000000000001d#64).signExtend 64).toNat) 32 = some bs185) :
    let v := ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
    denoteCode s1BlocksCalls if_then144Instrs (stateAt env s) =
      some (stateAt (ifThen144Out env v) s) := by
  intro v
  have h172len : bs172.length = 32 :=
    LeanLLVM.Refinement.JsonEntrySteps.readBytes_length s.mem (a - 2) 32 h172
  have h173len : bs173.length = 32 :=
    LeanLLVM.Refinement.JsonEntrySteps.readBytes_length s.mem (a - 3) 32 h173
  have h184len : bs184.length = 32 :=
    LeanLLVM.Refinement.JsonEntrySteps.readBytes_length s.mem
      (a + ((0x000000000000001e#64).signExtend 64).toNat) 32 h184
  have h185len : bs185.length = 32 :=
    LeanLLVM.Refinement.JsonEntrySteps.readBytes_length s.mem
      (a + ((0x000000000000001d#64).signExtend 64).toNat) 32 h185
  have hs1 := if_then144_seg1 env s a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
    hadd h1 h171 h2 h172 h3 h173
  have hs2 := if_then144_seg2 env s a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
  have hs3 := if_then144_seg3 env s a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
    h103 h103len h172len h173len
  have hs4 := if_then144_seg4 env s a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
    h183 h184 h185 (lookupName_ift144Env3_addptr env v hadd)
  have hs5 := if_then144_seg5 env s a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
  have hs6 := if_then144_seg6 env s a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185
    h161 hu h161len h172len h173len h184len h185len huk
  calc denoteCode s1BlocksCalls if_then144Instrs (stateAt env s)
      = denoteCode s1BlocksCalls
          (ifThen144Seg1 ++ (ifThen144Seg2 ++ (ifThen144Seg3 ++
            (ifThen144Seg4 ++ (ifThen144Seg5 ++ ifThen144Seg6)))))
          (stateAt env s) := by rw [if_then144Instrs_split]
    _ = denoteCode s1BlocksCalls
          (ifThen144Seg2 ++ (ifThen144Seg3 ++ (ifThen144Seg4 ++
            (ifThen144Seg5 ++ ifThen144Seg6))))
          (stateAt (ift144Env1 env v) s) := denoteCode_append_apply hs1 (by rfl)
    _ = denoteCode s1BlocksCalls
          (ifThen144Seg3 ++ (ifThen144Seg4 ++ (ifThen144Seg5 ++ ifThen144Seg6)))
          (stateAt (ift144Env2 env v) s) := denoteCode_append_apply hs2 (by rfl)
    _ = denoteCode s1BlocksCalls (ifThen144Seg4 ++ (ifThen144Seg5 ++ ifThen144Seg6))
          (stateAt (ift144Env3 env v) s) := denoteCode_append_apply hs3 (by rfl)
    _ = denoteCode s1BlocksCalls (ifThen144Seg5 ++ ifThen144Seg6)
          (stateAt (ift144Env4 env v) s) := denoteCode_append_apply hs4 (by rfl)
    _ = denoteCode s1BlocksCalls ifThen144Seg6
          (stateAt (ift144Env5 env v) s) := denoteCode_append_apply hs5 (by rfl)
    _ = some (stateAt (ifThen144Out env v) s) := hs6

/-- **`if.then144`'s step.**  The block's terminator is an unconditional branch
to the accumulator merge. -/
theorem if_then144_step (env : Env) (s : State) (a : Nat)
    (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8)
    (hpc : s.pc = "if.then144")
    (hadd : lookupName env "%add.ptr106" = some (.ptr a))
    (h1 : 1 ≤ a) (h171 : readBytes s.mem (a - 1) 32 = some bs171)
    (h2 : 2 ≤ a) (h172 : readBytes s.mem (a - 2) 32 = some bs172)
    (h3 : 3 ≤ a) (h173 : readBytes s.mem (a - 3) 32 = some bs173)
    (h103 : lookupName env "%152" = some (.vec 32 8 lo103))
    (h103len : lo103.length = 32)
    (h161 : lookupName env "%161" = some (.vec 32 8 lo161))
    (h161len : lo161.length = 32)
    (hu : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (huk : u8k.length = 4)
    (h183 : readBytes s.mem
      (a + ((0x000000000000001f#64).signExtend 64).toNat) 32 = some bs183)
    (h184 : readBytes s.mem
      (a + ((0x000000000000001e#64).signExtend 64).toNat) 32 = some bs184)
    (h185 : readBytes s.mem
      (a + ((0x000000000000001d#64).signExtend 64).toNat) 32 = some bs185) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt
        (ifThen144Out env
          (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185))
        { s with pc := "if.end147", pre := some "if.then144" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_then144Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then144
  rw [step_at hfind (if_then144_denote env s a lo103 lo161 u8k bs171 bs172 bs173
    bs183 bs184 bs185 hadd h1 h171 h2 h172 h3 h173 h103 h103len h161 h161len hu huk
    h183 h184 h185)]
  rw [show if_then144Block.term = if_then144Term from rfl]
  simp only [if_then144Term, execTerm]
  simp only [stateAt, hpc]

/-! ### `if.then103` — the peeled whole block

The peel classifies the last whole block.  The block reads the block's two
`<4 x i64>` words at `b + (n & -64)`, zero-tests their high bits against the
accumulator's word, runs the classifier's two table lookups on the low nibbles,
and folds the row's state through the carry-less product and the entry block's
`%and` shift.  The stored word is the DFA row; the two verdict bits the phi reads
are the entry test and the peel's high-bit test.

The values are stated once, `IfThen103Values`; the run is split at twelve
boundaries, each one `denoteCode` equation at an explicit environment. -/

/-- The values `if.then103` binds, one field per destination, in binding order.
The inputs are the document's pointer and index, the loop's two carried words,
the DFA state's three words, the ASCII probe's word and the emission cursor's two
cells. -/
structure IfThen103Values where
  shl105 : BitVec 64
  addPtr106 : Nat
  w136 : List (BitVec 64)
  addPtr110 : Nat
  w137 : List (BitVec 64)
  or280 : List (BitVec 64)
  ptz138 : BitVec 32
  or279 : List (BitVec 64)
  byte139 : List (BitVec 8)
  byte140 : List (BitVec 8)
  join141 : List (BitVec 64)
  join142 : List (BitVec 8)
  cmp143 : List (BitVec 1)
  mask385 : BitVec 64
  join144 : List (BitVec 64)
  join145 : List (BitVec 8)
  cmp146 : List (BitVec 1)
  mask391 : BitVec 64
  andII : BitVec 64
  shlII : BitVec 64
  notII : BitVec 64
  and1II : BitVec 64
  xorII : BitVec 64
  and2II : BitVec 64
  xor3II : BitVec 64
  not4II : BitVec 64
  addII : BitVec 64
  add5II : BitVec 64
  and6II : BitVec 64
  and7II : BitVec 64
  and8II : BitVec 64
  and9II : BitVec 64
  and11II : BitVec 64
  orII : BitVec 64
  or12II : BitVec 64
  notI : BitVec 64
  andI : BitVec 64
  half147 : List (BitVec 16)
  shr148 : List (BitVec 16)
  low149 : List (BitVec 8)
  shuf150 : List (BitVec 8)
  byte151 : List (BitVec 8)
  low152 : List (BitVec 8)
  shuf153 : List (BitVec 8)
  and416 : List (BitVec 8)
  and154 : List (BitVec 8)
  cmp417 : List (BitVec 1)
  mask155 : BitVec 32
  not418 : BitVec 32
  half156 : List (BitVec 16)
  shr157 : List (BitVec 16)
  low158 : List (BitVec 8)
  shuf159 : List (BitVec 8)
  byte160 : List (BitVec 8)
  low161 : List (BitVec 8)
  shuf162 : List (BitVec 8)
  and420 : List (BitVec 8)
  and163 : List (BitVec 8)
  cmp421 : List (BitVec 1)
  mask164 : BitVec 32
  not422 : BitVec 32
  conv16 : BitVec 64
  conv17 : BitVec 64
  shl18 : BitVec 64
  or19 : BitVec 64
  join165 : List (BitVec 8)
  cmp166 : List (BitVec 1)
  mask431 : BitVec 64
  vecinit : List (BitVec 64)
  pclmul : List (BitVec 64)
  vecext : BitVec 64
  xorI : BitVec 64
  not125 : BitVec 64
  v168 : BitVec 64
  v169 : BitVec 64
  and126 : BitVec 64
  and129 : BitVec 64
  shl131 : BitVec 64
  or132 : BitVec 64
  not133 : BitVec 64
  and134 : BitVec 64
  v170 : BitVec 64
  or135 : BitVec 64
  notmask : BitVec 64
  sub : BitVec 64
  and137 : BitVec 64
  arrayidx : Nat
  tobool139 : BitVec 1
  tobool141 : BitVec 1
  cond190 : BitVec 1
  tobool143 : BitVec 1
  cond191 : BitVec 1

/-- The block's computation, from the peel's index and pointer, the loop's
carried words, the ASCII word, the DFA state, the emission cursor and the entry
block's `%and`. -/
def ifThen103Values (n : BitVec 64) (b : Nat) (bs136 bs137 : List UInt8)
    (ascii : List (BitVec 64)) (st0 st9 st15 prevS andv shr : BitVec 64)
    (ent : Nat) (conv prevAscii : BitVec 32) : IfThen103Values :=
  let shl105 := n &&& 0xffffffffffffffc0#64
  let addPtr106 := b + (shl105.signExtend 64).toNat
  let w136 := unpackLanes 64 4 (bytesToNat bs136)
  let addPtr110 := addPtr106 + ((0x0000000000000020#64).signExtend 64).toNat
  let w137 := unpackLanes 64 4 (bytesToNat bs137)
  let or280 := List.zipWith (fun x y => x ||| y) w137 w136
  let ptz138 := ptestz (BitVec.ofNat 256 (packLanes or280))
    (BitVec.ofNat 256 (packLanes highMaskLanes))
  let or279 := List.zipWith (fun x y => x ||| y) or280 ascii
  let byte139 := bitcastVecLanes 8 32 w136
  let byte140 := bitcastVecLanes 8 32 w137
  let join141 := w136 ++ w137
  let join142 := bitcastVecLanes 8 64 join141
  let cmp143 := icmpLanes .eq join142 (List.replicate 64 0x22#8)
  let mask385 := BitVec.ofNat 64 (lanesToNat cmp143)
  let join144 := w136 ++ w137
  let join145 := bitcastVecLanes 8 64 join144
  let cmp146 := icmpLanes .eq join145 (List.replicate 64 0x5c#8)
  let mask391 := BitVec.ofNat 64 (lanesToNat cmp146)
  let andII := st0 &&& st9
  let shlII := mask391 <<< (0x0000000000000001#64).toNat
  let notII := shlII ^^^ 0xffffffffffffffff#64
  let and1II := mask391 &&& notII
  let xorII := andII ^^^ 0x5555555555555555#64
  let and2II := and1II &&& xorII
  let xor3II := and2II ^^^ and1II
  let not4II := mask391 ^^^ 0xffffffffffffffff#64
  let addII := and2II + mask391
  let add5II := xor3II + mask391
  let and6II := not4II &&& 0xaaaaaaaaaaaaaaaa#64
  let and7II := and6II &&& addII
  let and8II := not4II &&& 0x5555555555555555#64
  let and9II := and8II &&& add5II
  let and11II := andII &&& not4II
  let orII := and7II ||| and11II
  let or12II := orII ||| and9II
  let notI := or12II ^^^ 0xffffffffffffffff#64
  let andI := mask385 &&& notI
  let half147 := bitcastVecLanes 16 16 w136
  let shr148 := half147.map fun x : BitVec 16 => x >>> (0x0004#16).toNat
  let low149 := byte139.map fun x => x &&& 0x0f#8
  let shuf150 := pshufbLanes forBodyTableA low149
  let byte151 := bitcastVecLanes 8 32 shr148
  let low152 := byte151.map fun x => x &&& 0x0f#8
  let shuf153 := pshufbLanes forBodyTableB low152
  let and416 := List.zipWith (fun x y => x &&& y) shuf153 shuf150
  let and154 := and416.map fun x => x &&& 0x3f#8
  let cmp417 := icmpLanes .eq and154 (List.replicate 32 0x00#8)
  let mask155 := BitVec.ofNat 32 (lanesToNat cmp417)
  let not418 := mask155 ^^^ 0xffffffff#32
  let half156 := bitcastVecLanes 16 16 w137
  let shr157 := half156.map fun x : BitVec 16 => x >>> (0x0004#16).toNat
  let low158 := byte140.map fun x => x &&& 0x0f#8
  let shuf159 := pshufbLanes forBodyTableA low158
  let byte160 := bitcastVecLanes 8 32 shr157
  let low161 := byte160.map fun x => x &&& 0x0f#8
  let shuf162 := pshufbLanes forBodyTableB low161
  let and420 := List.zipWith (fun x y => x &&& y) shuf162 shuf159
  let and163 := and420.map fun x => x &&& 0x3f#8
  let cmp421 := icmpLanes .eq and163 (List.replicate 32 0x00#8)
  let mask164 := BitVec.ofNat 32 (lanesToNat cmp421)
  let not422 := mask164 ^^^ 0xffffffff#32
  let conv16 := BitVec.ofNat 64 not418.toNat
  let conv17 := BitVec.ofNat 64 not422.toNat
  let shl18 := conv17 <<< (0x0000000000000020#64).toNat
  let or19 := shl18 ||| conv16
  let join165 := and416 ++ and420
  let cmp166 := icmpLanes .eq join165 (List.replicate 64 0x00#8)
  let mask431 := BitVec.ofNat 64 (lanesToNat cmp166)
  let vecinit := [BitVec.ofNat 64 andI.toNat, 0x0000000000000000#64]
  let pclmul := [Pclmul.clmul (BitVec.ofNat 64 andI.toNat) (BitVec.allOnes 64),
    0x0000000000000000#64]
  let vecext := Pclmul.clmul (BitVec.ofNat 64 andI.toNat) (BitVec.allOnes 64)
  let xorI := vecext ^^^ st15
  let not125 := xorI ^^^ 0xffffffffffffffff#64
  let v168 := andI ||| xorI
  let v169 := v168 ^^^ 0xffffffffffffffff#64
  let and126 := mask431 &&& v169
  let and129 := or19 &&& not125
  let shl131 := and126 <<< (0x0000000000000001#64).toNat
  let or132 := shl131 ||| prevS
  let not133 := or132 ^^^ 0xffffffffffffffff#64
  let and134 := and126 &&& not133
  let v170 := and129 ||| and134
  let or135 := v170 ||| andI
  let notmask := 0xffffffffffffffff#64 <<< andv.toNat
  let sub := notmask ^^^ 0xffffffffffffffff#64
  let and137 := or135 &&& sub
  let arrayidx := ent + (shr.signExtend 64).toNat * (Ty.int 64).sizeBytes
  let tobool139 := evalICmp .eq conv 0x00000000#32
  let tobool141 := evalICmp .ne ptz138 0x00000000#32
  let cond190 := if tobool139 = 1 then tobool141 else 0x0#1
  let tobool143 := evalICmp .ne prevAscii 0x00000000#32
  let cond191 := if cond190 = 1 then tobool143 else 0x0#1
  { shl105, addPtr106, w136, addPtr110, w137, or280, ptz138, or279, byte139,
    byte140, join141, join142, cmp143, mask385, join144, join145, cmp146,
    mask391, andII, shlII, notII, and1II, xorII, and2II, xor3II, not4II, addII,
    add5II, and6II, and7II, and8II, and9II, and11II, orII, or12II, notI, andI,
    half147, shr148, low149, shuf150, byte151, low152, shuf153, and416, and154,
    cmp417, mask155, not418, half156, shr157, low158, shuf159, byte160, low161,
    shuf162, and420, and163, cmp421, mask164, not422, conv16, conv17, shl18,
    or19, join165, cmp166, mask431, vecinit, pclmul, vecext, xorI, not125, v168,
    v169, and126, and129, shl131, or132, not133, and134, v170, or135, notmask,
    sub, and137, arrayidx, tobool139, tobool141, cond190, tobool143, cond191 }

/-- The environment after the peeled block's two window loads and their join. -/
def ift103Env1 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%or.i279", .vec 4 64 v.or279),
         ("%138", .int 32 v.ptz138),
         ("%or.i280", .vec 4 64 v.or280),
         ("%137", .vec 4 64 v.w137),
         ("%add.ptr110", .ptr v.addPtr110),
         ("%136", .vec 4 64 v.w136),
         ("%add.ptr106", .ptr v.addPtr106),
         ("%shl105", .int 64 v.shl105)] env

/-- The environment after the two byte views of the loaded words. -/
def ift103Env2 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%140", .vec 32 8 v.byte140),
         ("%139", .vec 32 8 v.byte139)] (ift103Env1 env v)

/-- The environment after the first join's byte compare and packed mask. -/
def ift103Env3 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%or.i385", .int 64 v.mask385),
         ("%143", .vec 64 1 v.cmp143),
         ("%142", .vec 64 8 v.join142),
         ("%141", .vec 8 64 v.join141)] (ift103Env2 env v)

/-- The environment after the second join's byte compare and packed mask. -/
def ift103Env4 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%or14.i391", .int 64 v.mask391),
         ("%146", .vec 64 1 v.cmp146),
         ("%145", .vec 64 8 v.join145),
         ("%144", .vec 8 64 v.join144)] (ift103Env3 env v)

/-- The environment after the carried state's bit arithmetic. -/
def ift103Env5 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%and.i415", .int 64 v.andI),
         ("%not.i414", .int 64 v.notI),
         ("%or12.i.i410", .int 64 v.or12II),
         ("%or.i.i409", .int 64 v.orII),
         ("%and11.i.i408", .int 64 v.and11II),
         ("%and9.i.i406", .int 64 v.and9II),
         ("%and8.i.i405", .int 64 v.and8II),
         ("%and7.i.i404", .int 64 v.and7II),
         ("%and6.i.i403", .int 64 v.and6II),
         ("%add5.i.i402", .int 64 v.add5II),
         ("%add.i.i401", .int 64 v.addII),
         ("%not4.i.i400", .int 64 v.not4II),
         ("%xor3.i.i399", .int 64 v.xor3II),
         ("%and2.i.i398", .int 64 v.and2II),
         ("%xor.i.i397", .int 64 v.xorII),
         ("%and1.i.i396", .int 64 v.and1II),
         ("%not.i.i395", .int 64 v.notII),
         ("%shl.i.i394", .int 64 v.shlII),
         ("%and.i.i393", .int 64 v.andII)] (ift103Env4 env v)

/-- The environment after the first word's two table lookups and their class
mask. -/
def ift103Env6 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%not.i46.i418", .int 32 v.not418),
         ("%155", .int 32 v.mask155),
         ("%cmp.i21.i.i417", .vec 32 1 v.cmp417),
         ("%154", .vec 32 8 v.and154),
         ("%and.i2326.i.i416", .vec 32 8 v.and416),
         ("%153", .vec 32 8 v.shuf153),
         ("%152", .vec 32 8 v.low152),
         ("%151", .vec 32 8 v.byte151),
         ("%150", .vec 32 8 v.shuf150),
         ("%149", .vec 32 8 v.low149),
         ("%148", .vec 16 16 v.shr148),
         ("%147", .vec 16 16 v.half147)] (ift103Env5 env v)

/-- The environment after the second word's two table lookups and their class
mask. -/
def ift103Env7 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%not.i49.i422", .int 32 v.not422),
         ("%164", .int 32 v.mask164),
         ("%cmp.i21.i48.i421", .vec 32 1 v.cmp421),
         ("%163", .vec 32 8 v.and163),
         ("%and.i2326.i47.i420", .vec 32 8 v.and420),
         ("%162", .vec 32 8 v.shuf162),
         ("%161", .vec 32 8 v.low161),
         ("%160", .vec 32 8 v.byte160),
         ("%159", .vec 32 8 v.shuf159),
         ("%158", .vec 32 8 v.low158),
         ("%157", .vec 16 16 v.shr157),
         ("%156", .vec 16 16 v.half156)] (ift103Env6 env v)

/-- The environment after the two class words' packed join. -/
def ift103Env8 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%or19.i427", .int 64 v.or19),
         ("%shl18.i426", .int 64 v.shl18),
         ("%conv17.i425", .int 64 v.conv17),
         ("%conv16.i424", .int 64 v.conv16)] (ift103Env7 env v)

/-- The environment after the sixty-four-lane join and its zero mask. -/
def ift103Env9 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%or23.i431", .int 64 v.mask431),
         ("%166", .vec 64 1 v.cmp166),
         ("%165", .vec 64 8 v.join165)] (ift103Env8 env v)

/-- The environment after the written lane and the carry-less product. -/
def ift103Env10 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%167", .vec 2 64 v.pclmul),
         ("%vecinit1.i.i.i432", .vec 2 64 v.vecinit)] (ift103Env9 env v)

/-- The environment after the state update and the emit word's mask. -/
def ift103Env11 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%and137", .int 64 v.and137),
         ("%sub", .int 64 v.sub),
         ("%notmask", .int 64 v.notmask),
         ("%or135", .int 64 v.or135),
         ("%170", .int 64 v.v170),
         ("%and134", .int 64 v.and134),
         ("%not133", .int 64 v.not133),
         ("%or132", .int 64 v.or132),
         ("%shl131", .int 64 v.shl131),
         ("%and129", .int 64 v.and129),
         ("%and126", .int 64 v.and126),
         ("%169", .int 64 v.v169),
         ("%168", .int 64 v.v168),
         ("%not125", .int 64 v.not125),
         ("%xor.i435", .int 64 v.xorI),
         ("%vecext.i.i.i433", .int 64 v.vecext)] (ift103Env10 env v)

/-- The environment after the emit store and the two verdict bits. -/
def ift103Env12 (env : Env) (v : IfThen103Values) : Env :=
  cells [("%or.cond191", .int 1 v.cond191),
         ("%tobool143", .int 1 v.tobool143),
         ("%or.cond190", .int 1 v.cond190),
         ("%tobool141", .int 1 v.tobool141),
         ("%tobool139", .int 1 v.tobool139),
         ("%arrayidx138", .ptr v.arrayidx)] (ift103Env11 env v)

/-- `if.then103`'s environment: everything the block binds. -/
def ifThen103Out (env : Env) (v : IfThen103Values) : Env := ift103Env12 env v

/-- `if.then103`'s run at its twelve segment boundaries: the two window loads
and their join, the two byte views, each join's compare, the carried state's bit
arithmetic, the first word's class words, the second word's class words, the two
class words' packed join, the sixty-four-lane join, the written lane, the state
update, and the store with the verdict bits. -/
def ifThen103Seg1 : List Instr := if_then103Instrs.take 8
def ifThen103Seg2 : List Instr := (if_then103Instrs.drop 8).take 2
def ifThen103Seg3 : List Instr := (if_then103Instrs.drop 10).take 4
def ifThen103Seg4 : List Instr := (if_then103Instrs.drop 14).take 4
def ifThen103Seg5 : List Instr := (if_then103Instrs.drop 18).take 19
def ifThen103Seg6 : List Instr := (if_then103Instrs.drop 37).take 12
def ifThen103Seg7 : List Instr := (if_then103Instrs.drop 49).take 12
def ifThen103Seg8 : List Instr := (if_then103Instrs.drop 61).take 4
def ifThen103Seg9 : List Instr := (if_then103Instrs.drop 65).take 3
def ifThen103Seg10 : List Instr := (if_then103Instrs.drop 68).take 2
def ifThen103Seg11 : List Instr := (if_then103Instrs.drop 70).take 16
def ifThen103Seg12 : List Instr := (if_then103Instrs.drop 86).take 7

/-- The first class mask's join: two thirty-two-lane table lookups. -/
theorem ifThen103Values_and416_length (n : BitVec 64) (b : Nat) (bs136 bs137 : List UInt8)
    (ascii : List (BitVec 64)) (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
      prevAscii).and416.length = 32 := by
  simp [ifThen103Values, bitcastVecLanes, unpackLanes_length,
    JsonS1MasksSteps.pshufbLanes_length, List.length_zipWith, List.length_map]

/-- The second class mask's join. -/
theorem ifThen103Values_and420_length (n : BitVec 64) (b : Nat) (bs136 bs137 : List UInt8)
    (ascii : List (BitVec 64)) (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
      prevAscii).and420.length = 32 := by
  simp [ifThen103Values, bitcastVecLanes, unpackLanes_length,
    JsonS1MasksSteps.pshufbLanes_length, List.length_zipWith, List.length_map]

/-- `%vecinit1.i.i.i432`: lane zero of a two-lane zero vector takes `%and.i415`. -/
theorem ifThen103_vecinit (env : Env) (s : State) (x : BitVec 64)
    (h : lookupName env "%and.i415" = some (.int 64 x)) (is : List Instr) :
    denoteCode s1BlocksCalls
        (.insertelement "%vecinit1.i.i.i432" 2 64
          (.imm (.splat 2 64 0x0000000000000000#64)) (.reg "%and.i415")
          (.imm (.int 64 0x0000000000000000#64)) :: is) (stateAt env s) =
      denoteCode s1BlocksCalls is
        (stateAt (("%vecinit1.i.i.i432",
          .vec 2 64 [BitVec.ofNat 64 x.toNat, 0x0000000000000000#64]) :: env) s) := by
  rw [denoteCode_insertelement (calls := s1BlocksCalls) (env := env) (s := s)
    (d := "%vecinit1.i.i.i432") (n := 2) (w := 64)
    (v := .imm (.splat 2 64 0x0000000000000000#64)) (elt := .reg "%and.i415")
    (idx := .imm (.int 64 0x0000000000000000#64))
    (vv := .vec 2 64 (List.replicate 2 0x0000000000000000#64))
    (lanes := List.replicate 2 0x0000000000000000#64)
    (ev := .int 64 x) (x := x.toNat) (wi := 64) (k := 0x0000000000000000#64)
    (hv := by simp [evalOperand, Const.toValue])
    (hl := vecLanes_self (by simp))
    (helt := evalOperand_reg_of env s "%and.i415" (.int 64 x) h)
    (hx := rfl) (hi := rfl) (hk := by decide)]
  rfl

/-- `%167`: the carry-less product of the written lane against all ones. -/
theorem ifThen103_pclmul (env : Env) (s : State) (a : BitVec 64)
    (h : lookupName env "%vecinit1.i.i.i432" =
      some (.vec 2 64 [a, 0x0000000000000000#64])) (is : List Instr) :
    denoteCode s1BlocksCalls
        (.call "%167" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
          [(.vec 2 (.int 64), .reg "%vecinit1.i.i.i432"),
           (.vec 2 (.int 64),
             .imm (.vector 64 [0xffffffffffffffff#64, 0x0000000000000000#64])),
           (.int 8, .imm (.int 8 0x00#8))] :: is) (stateAt env s) =
      denoteCode s1BlocksCalls is
        (stateAt (("%167",
          .vec 2 64 [Pclmul.clmul a (BitVec.allOnes 64), 0x0000000000000000#64]) :: env) s) := by
  exact denoteCode_pclmul_b env s "%vecinit1.i.i.i432" "%167"
    (a0 := a) (a1 := 0x0000000000000000#64)
    (evalOperand_reg_of env s "%vecinit1.i.i.i432"
      (.vec 2 64 [a, 0x0000000000000000#64]) h) is

/-- `%vecext.i.i.i433`: lane zero of the product, which is the product itself. -/
theorem ifThen103_vecext (env : Env) (s : State) (a : BitVec 64)
    (h : lookupName env "%167" = some (.vec 2 64 [a, 0x0000000000000000#64]))
    (is : List Instr) :
    denoteCode s1BlocksCalls
        (.extractelement "%vecext.i.i.i433" 2 64 (.reg "%167")
          (.imm (.int 64 0x0000000000000000#64)) :: is) (stateAt env s) =
      denoteCode s1BlocksCalls is
        (stateAt (("%vecext.i.i.i433", .int 64 a) :: env) s) := by
  exact denoteCode_extractelement (calls := s1BlocksCalls) (env := env) (s := s)
    (d := "%vecext.i.i.i433") (n := 2) (w := 64) (v := .reg "%167")
    (idx := .imm (.int 64 0x0000000000000000#64))
    (vv := .vec 2 64 [a, 0x0000000000000000#64])
    (lanes := [a, 0x0000000000000000#64]) (wi := 64)
    (k := 0x0000000000000000#64) (x := a)
    (hv := evalOperand_reg_of env s "%167" (.vec 2 64 [a, 0x0000000000000000#64]) h)
    (hl := vecLanes_self (by simp)) (hi := rfl) (hx := by simp) is

/-- The peel's steps: the block battery, the written lane, its product and its
lane read, and the `i1` verdict `select`. -/
macro "t103_step" : tactic => `(tactic|
  (first
   | rw [ifThen103_vecinit _ _ _ ?_ _]
   | rw [ifThen103_pclmul _ _ _ ?_ _]
   | rw [ifThen103_vecext _ _ _ ?_ _]
   | rw [denoteCode_select_bit_reg_imm_w _ _ _ _ _ _ _ ?_ ?_ _]
   | block_step_b))

macro "t103_eval" : tactic => `(tactic|
  (repeat t103_step
   block_close_v))

/-- **`if.then103`'s first segment.**  The mask, the block's address, its two
`<4 x i64>` loads, their join and the join's zero test. -/
theorem if_then103_seg1 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32)
    (hn : lookupName env "%n" = some (.int 64 n))
    (hb : lookupName env "%b" = some (.ptr b))
    (hascii : lookupName env "%ascii.1.lcssa" = some (.vec 4 64 ascii))
    (hasciilen : ascii.length = 4)
    (hpos : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat < 2 ^ 63)
    (h136 : readBytes s.mem
      (b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat) 32 = some bs136)
    (h137 : readBytes s.mem
      ((b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs137) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg1 (stateAt env s) =
      some (stateAt (ift103Env1 env v) s) := by
  intro v
  have h280 : v.or280.length = 4 := by
    simp (config := { zetaDelta := true }) only [ifThen103Values, unpackLanes_length,
      List.length_zipWith]
    omega
  have hm : binopLanes .or v.or280 ascii =
      some (List.zipWith (fun x y => x ||| y) v.or280 ascii) :=
    binopLanes_zipWith .or (fun x y => x ||| y) (fun x y => rfl) v.or280 ascii
      (by rw [h280, hasciilen])
  unfold ifThen103Seg1 ift103Env1
  simp only [if_then103Instrs, List.take, List.drop]
  t103_eval
  all_goals (try (exact hm))

/-- **`if.then103`'s second segment.**  The two `<4 x i64>` words' byte views. -/
theorem if_then103_seg2 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg2 (stateAt (ift103Env1 env v) s) =
      some (stateAt (ift103Env2 env v) s) := by
  intro v
  unfold ifThen103Seg2 ift103Env1 ift103Env2
  simp only [if_then103Instrs, List.take, List.drop]
  t103_eval

/-- **`if.then103`'s third segment.**  The first join's byte view, its `0x22`
compare and the packed mask. -/
theorem if_then103_seg3 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg3 (stateAt (ift103Env2 env v) s) =
      some (stateAt (ift103Env3 env v) s) := by
  intro v
  unfold ifThen103Seg3
  simp only [if_then103Instrs, List.take, List.drop]
  rw [denoteCode_shuffleVec (calls := s1BlocksCalls) (env := ift103Env2 env v) (s := s)
    (d := "%141") (n := 4) (w := 64) (a := .reg "%136") (b := .reg "%137")
    (mask := [0, 1, 2, 3, 4, 5, 6, 7]) (l1 := v.w136) (l2 := v.w137)
    (ls := v.w136 ++ v.w137)
    (ha := BlockEval.evalOperand_reg_of _ _ "%136" (.vec 4 64 v.w136)
      (by simp only [ift103Env2, ift103Env1, cells]; block_lk_cons))
    (hb := BlockEval.evalOperand_reg_of _ _ "%137" (.vec 4 64 v.w137)
      (by simp only [ift103Env2, ift103Env1, cells]; block_lk_cons))
    (h1 := vecLanes_self (by simp (config := { zetaDelta := true }) only [ifThen103Values, unpackLanes_length]))
    (h2 := vecLanes_self (by simp (config := { zetaDelta := true }) only [ifThen103Values, unpackLanes_length]))
    (hm := mapM_pick8 (by simp (config := { zetaDelta := true }) only [ifThen103Values, unpackLanes_length])
      (by simp (config := { zetaDelta := true }) only [ifThen103Values, unpackLanes_length]))]
  unfold ift103Env2 ift103Env3
  t103_eval

/-- **`if.then103`'s fourth segment.**  The second join's byte view, its `0x5c`
compare and the packed mask. -/
theorem if_then103_seg4 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg4 (stateAt (ift103Env3 env v) s) =
      some (stateAt (ift103Env4 env v) s) := by
  intro v
  unfold ifThen103Seg4
  simp only [if_then103Instrs, List.take, List.drop]
  rw [denoteCode_shuffleVec (calls := s1BlocksCalls) (env := ift103Env3 env v) (s := s)
    (d := "%144") (n := 4) (w := 64) (a := .reg "%136") (b := .reg "%137")
    (mask := [0, 1, 2, 3, 4, 5, 6, 7]) (l1 := v.w136) (l2 := v.w137)
    (ls := v.w136 ++ v.w137)
    (ha := BlockEval.evalOperand_reg_of _ _ "%136" (.vec 4 64 v.w136)
      (by simp only [ift103Env3, ift103Env2, ift103Env1, cells]; block_lk_cons))
    (hb := BlockEval.evalOperand_reg_of _ _ "%137" (.vec 4 64 v.w137)
      (by simp only [ift103Env3, ift103Env2, ift103Env1, cells]; block_lk_cons))
    (h1 := vecLanes_self (by simp (config := { zetaDelta := true }) only [ifThen103Values, unpackLanes_length]))
    (h2 := vecLanes_self (by simp (config := { zetaDelta := true }) only [ifThen103Values, unpackLanes_length]))
    (hm := mapM_pick8 (by simp (config := { zetaDelta := true }) only [ifThen103Values, unpackLanes_length])
      (by simp (config := { zetaDelta := true }) only [ifThen103Values, unpackLanes_length]))]
  unfold ift103Env3 ift103Env4
  t103_eval

/-- **`if.then103`'s fifth segment.**  The carried state's bit arithmetic: the
odd-byte mask, the two shifted masks and the ASCII word's join. -/
theorem if_then103_seg5 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32)
    (hst0 : lookupName env "%st.sroa.0.2.lcssa" = some (.int 64 st0))
    (hst9 : lookupName env "%st.sroa.9.2.lcssa" = some (.int 64 st9)) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg5 (stateAt (ift103Env4 env v) s) =
      some (stateAt (ift103Env5 env v) s) := by
  intro v
  unfold ifThen103Seg5 ift103Env4 ift103Env5
  simp only [if_then103Instrs, List.take, List.drop]
  t103_eval

/-- **`if.then103`'s sixth segment.**  The first word's two table lookups and
their class mask. -/
theorem if_then103_seg6 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg6 (stateAt (ift103Env5 env v) s) =
      some (stateAt (ift103Env6 env v) s) := by
  intro v
  unfold ifThen103Seg6 ift103Env5 ift103Env6
  simp only [if_then103Instrs, List.take, List.drop]
  t103_eval

/-- **`if.then103`'s seventh segment.**  The second word's two table lookups and
their class mask. -/
theorem if_then103_seg7 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg7 (stateAt (ift103Env6 env v) s) =
      some (stateAt (ift103Env7 env v) s) := by
  intro v
  unfold ifThen103Seg7 ift103Env6 ift103Env7
  simp only [if_then103Instrs, List.take, List.drop]
  t103_eval

/-- **`if.then103`'s eighth segment.**  The two class words' widen and packed
join. -/
theorem if_then103_seg8 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg8 (stateAt (ift103Env7 env v) s) =
      some (stateAt (ift103Env8 env v) s) := by
  intro v
  unfold ifThen103Seg8 ift103Env7 ift103Env8
  simp only [if_then103Instrs, List.take, List.drop]
  t103_eval

/-- **`if.then103`'s ninth segment.**  The sixty-four-lane join of the two class
words and its zero mask. -/
theorem if_then103_seg9 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg9 (stateAt (ift103Env8 env v) s) =
      some (stateAt (ift103Env9 env v) s) := by
  intro v
  unfold ifThen103Seg9
  simp only [if_then103Instrs, List.take, List.drop]
  rw [denoteCode_shuffleVec (calls := s1BlocksCalls) (env := ift103Env8 env v) (s := s)
    (d := "%165") (n := 32) (w := 8)
    (a := .reg "%and.i2326.i.i416") (b := .reg "%and.i2326.i47.i420")
    (mask := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
      22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
      44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63])
    (l1 := v.and416) (l2 := v.and420) (ls := v.and416 ++ v.and420)
    (ha := BlockEval.evalOperand_reg_of _ _ "%and.i2326.i.i416" (.vec 32 8 v.and416)
      (by simp only [ift103Env8, ift103Env7, ift103Env6, ift103Env5, ift103Env4,
        ift103Env3, ift103Env2, ift103Env1, cells]; block_lk_cons))
    (hb := BlockEval.evalOperand_reg_of _ _ "%and.i2326.i47.i420" (.vec 32 8 v.and420)
      (by simp only [ift103Env8, ift103Env7, ift103Env6, ift103Env5, ift103Env4,
        ift103Env3, ift103Env2, ift103Env1, cells]; block_lk_cons))
    (h1 := vecLanes_self
      (ifThen103Values_and416_length n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
        ent conv prevAscii))
    (h2 := vecLanes_self
      (ifThen103Values_and420_length n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
        ent conv prevAscii))
    (hm := mapM_pick32
      (ifThen103Values_and416_length n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
        ent conv prevAscii)
      (ifThen103Values_and420_length n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
        ent conv prevAscii))]
  unfold ift103Env8 ift103Env9
  t103_eval

/-- **`if.then103`'s tenth segment.**  The written lane and the carry-less
product. -/
theorem if_then103_seg10 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg10 (stateAt (ift103Env9 env v) s) =
      some (stateAt (ift103Env10 env v) s) := by
  intro v
  unfold ifThen103Seg10 ift103Env9 ift103Env10
  simp only [if_then103Instrs, List.take, List.drop]
  t103_eval

/-- **`if.then103`'s eleventh segment.**  The product's lane read, the state
update, the carry's join and the emit word's mask. -/
theorem if_then103_seg11 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32)
    (hst15 : lookupName env "%st.sroa.15.2.lcssa" = some (.int 64 st15))
    (hprevS : lookupName env "%prevS.2.lcssa" = some (.int 64 prevS))
    (hand : lookupName env "%and" = some (.int 64 andv)) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg11 (stateAt (ift103Env10 env v) s) =
      some (stateAt (ift103Env11 env v) s) := by
  intro v
  unfold ifThen103Seg11 ift103Env10 ift103Env11
  simp only [if_then103Instrs, List.take, List.drop]
  t103_eval

/-- **`if.then103`'s twelfth segment.**  The emit store and the two verdict bits
the phi reads. -/
theorem if_then103_seg12 (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32)
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hpos : (shr.signExtend 64).toNat < 2 ^ 63)
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (hprev : lookupName env "%prev_ascii.1.lcssa" = some (.int 32 prevAscii)) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls ifThen103Seg12 (stateAt (ift103Env11 env v) s) =
      some (stateAt (ifThen103Out env v)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8) }) := by
  intro v
  unfold ifThen103Seg12 ift103Env11 ifThen103Out
  simp only [if_then103Instrs, List.take, List.drop]
  t103_eval

/-- `if.then103`'s twelve segments, in order. -/
theorem if_then103Instrs_split :
    if_then103Instrs =
      ifThen103Seg1 ++ (ifThen103Seg2 ++ (ifThen103Seg3 ++ (ifThen103Seg4 ++
        (ifThen103Seg5 ++ (ifThen103Seg6 ++ (ifThen103Seg7 ++ (ifThen103Seg8 ++
          (ifThen103Seg9 ++ (ifThen103Seg10 ++ (ifThen103Seg11 ++
            ifThen103Seg12)))))))))) := rfl

/-- **`if.then103`'s run.**  The twelve segments compose: the peel's mask and
window loads hand their environment to the two byte views and their compares,
whose masks are the carried state's input; the state's bit arithmetic and the
two words' class masks hand their class words to the packed join, whose zero mask
is the written lane; the product's lane and the emit word's mask are the store's
inputs, and the store leaves the two verdict bits the phi reads. -/
theorem if_then103_denote (env : Env) (s : State) (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32)
    (hn : lookupName env "%n" = some (.int 64 n))
    (hb : lookupName env "%b" = some (.ptr b))
    (hascii : lookupName env "%ascii.1.lcssa" = some (.vec 4 64 ascii))
    (hasciilen : ascii.length = 4)
    (hpos : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat < 2 ^ 63)
    (h136 : readBytes s.mem
      (b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat) 32 = some bs136)
    (h137 : readBytes s.mem
      ((b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs137)
    (hst0 : lookupName env "%st.sroa.0.2.lcssa" = some (.int 64 st0))
    (hst9 : lookupName env "%st.sroa.9.2.lcssa" = some (.int 64 st9))
    (hst15 : lookupName env "%st.sroa.15.2.lcssa" = some (.int 64 st15))
    (hprevS : lookupName env "%prevS.2.lcssa" = some (.int 64 prevS))
    (hand : lookupName env "%and" = some (.int 64 andv))
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hshrPos : (shr.signExtend 64).toNat < 2 ^ 63)
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (hprev : lookupName env "%prev_ascii.1.lcssa" = some (.int 32 prevAscii)) :
    let v := ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii
    denoteCode s1BlocksCalls if_then103Instrs (stateAt env s) =
      some (stateAt (ifThen103Out env v)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8) }) := by
  intro v
  have hs1 := if_then103_seg1 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii hn hb hascii hasciilen hpos h136 h137
  have hs2 := if_then103_seg2 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii
  have hs3 := if_then103_seg3 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii
  have hs4 := if_then103_seg4 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii
  have hs5 := if_then103_seg5 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii hst0 hst9
  have hs6 := if_then103_seg6 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii
  have hs7 := if_then103_seg7 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii
  have hs8 := if_then103_seg8 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii
  have hs9 := if_then103_seg9 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii
  have hs10 := if_then103_seg10 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii
  have hs11 := if_then103_seg11 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii hst15 hprevS hand
  have hs12 := if_then103_seg12 env s n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
    ent conv prevAscii hent hshr hshrPos hconv hprev
  calc denoteCode s1BlocksCalls if_then103Instrs (stateAt env s)
      = denoteCode s1BlocksCalls
          (ifThen103Seg1 ++ (ifThen103Seg2 ++ (ifThen103Seg3 ++ (ifThen103Seg4 ++
            (ifThen103Seg5 ++ (ifThen103Seg6 ++ (ifThen103Seg7 ++ (ifThen103Seg8 ++
              (ifThen103Seg9 ++ (ifThen103Seg10 ++ (ifThen103Seg11 ++
                ifThen103Seg12)))))))))))
          (stateAt env s) := by rw [if_then103Instrs_split]
    _ = denoteCode s1BlocksCalls
          (ifThen103Seg2 ++ (ifThen103Seg3 ++ (ifThen103Seg4 ++
            (ifThen103Seg5 ++ (ifThen103Seg6 ++ (ifThen103Seg7 ++ (ifThen103Seg8 ++
              (ifThen103Seg9 ++ (ifThen103Seg10 ++ (ifThen103Seg11 ++
                ifThen103Seg12))))))))))
          (stateAt (ift103Env1 env v) s) := denoteCode_append_apply hs1 (by rfl)
    _ = denoteCode s1BlocksCalls
          (ifThen103Seg3 ++ (ifThen103Seg4 ++ (ifThen103Seg5 ++
            (ifThen103Seg6 ++ (ifThen103Seg7 ++ (ifThen103Seg8 ++
              (ifThen103Seg9 ++ (ifThen103Seg10 ++ (ifThen103Seg11 ++
                ifThen103Seg12)))))))))
          (stateAt (ift103Env2 env v) s) := denoteCode_append_apply hs2 (by rfl)
    _ = denoteCode s1BlocksCalls
          (ifThen103Seg4 ++ (ifThen103Seg5 ++ (ifThen103Seg6 ++
            (ifThen103Seg7 ++ (ifThen103Seg8 ++ (ifThen103Seg9 ++
              (ifThen103Seg10 ++ (ifThen103Seg11 ++ ifThen103Seg12))))))))
          (stateAt (ift103Env3 env v) s) := denoteCode_append_apply hs3 (by rfl)
    _ = denoteCode s1BlocksCalls
          (ifThen103Seg5 ++ (ifThen103Seg6 ++ (ifThen103Seg7 ++
            (ifThen103Seg8 ++ (ifThen103Seg9 ++ (ifThen103Seg10 ++
              (ifThen103Seg11 ++ ifThen103Seg12)))))))
          (stateAt (ift103Env4 env v) s) := denoteCode_append_apply hs4 (by rfl)
    _ = denoteCode s1BlocksCalls
          (ifThen103Seg6 ++ (ifThen103Seg7 ++ (ifThen103Seg8 ++
            (ifThen103Seg9 ++ (ifThen103Seg10 ++ (ifThen103Seg11 ++
              ifThen103Seg12))))))
          (stateAt (ift103Env5 env v) s) := denoteCode_append_apply hs5 (by rfl)
    _ = denoteCode s1BlocksCalls
          (ifThen103Seg7 ++ (ifThen103Seg8 ++ (ifThen103Seg9 ++
            (ifThen103Seg10 ++ (ifThen103Seg11 ++ ifThen103Seg12)))))
          (stateAt (ift103Env6 env v) s) := denoteCode_append_apply hs6 (by rfl)
    _ = denoteCode s1BlocksCalls
          (ifThen103Seg8 ++ (ifThen103Seg9 ++ (ifThen103Seg10 ++
            (ifThen103Seg11 ++ ifThen103Seg12))))
          (stateAt (ift103Env7 env v) s) := denoteCode_append_apply hs7 (by rfl)
    _ = denoteCode s1BlocksCalls
          (ifThen103Seg9 ++ (ifThen103Seg10 ++ (ifThen103Seg11 ++ ifThen103Seg12)))
          (stateAt (ift103Env8 env v) s) := denoteCode_append_apply hs8 (by rfl)
    _ = denoteCode s1BlocksCalls (ifThen103Seg10 ++ (ifThen103Seg11 ++ ifThen103Seg12))
          (stateAt (ift103Env9 env v) s) := denoteCode_append_apply hs9 (by rfl)
    _ = denoteCode s1BlocksCalls (ifThen103Seg11 ++ ifThen103Seg12)
          (stateAt (ift103Env10 env v) s) := denoteCode_append_apply hs10 (by rfl)
    _ = denoteCode s1BlocksCalls ifThen103Seg12
          (stateAt (ift103Env11 env v) s) := denoteCode_append_apply hs11 (by rfl)
    _ = some (stateAt (ifThen103Out env v)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8) }) := hs12

/-- **`if.then103`'s step to the accumulator merge.**  The peel's verdict is set:
the entry test and the high-bit test both hold, so the phi reads
`if.then103`'s accumulator. -/
theorem if_then103_step_end147 (env : Env) (s : State) (v : IfThen103Values)
    (hpc : s.pc = "if.then103")
    (hbit : lookupName (ifThen103Out env v) "%or.cond191" = some (.int 1 1))
    (hout : denoteCode s1BlocksCalls if_then103Instrs (stateAt env s) =
      some (stateAt (ifThen103Out env v)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8) })) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifThen103Out env v)
        { s with
          pc := "if.end147",
          pre := some "if.then103",
          mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8) }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_then103Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then103
  rw [step_at hfind hout]
  rw [show if_then103Block.term = if_then103Term from rfl]
  simp only [if_then103Term]
  rw [LeanLLVM.Refinement.JsonS1BlocksRefine.execTerm_condbr_true
    (BlockEval.evalOperand_reg_of _ _ _ _ hbit) rfl]
  simp only [stateAt, hpc]

/-- **`if.then103`'s step to the partial tail.**  The peel's verdict is clear:
the last block is ASCII, and the partial tail's own windows are the next armour. -/
theorem if_then103_step_then144 (env : Env) (s : State) (v : IfThen103Values)
    (hpc : s.pc = "if.then103")
    (hbit : lookupName (ifThen103Out env v) "%or.cond191" = some (.int 1 0))
    (hout : denoteCode s1BlocksCalls if_then103Instrs (stateAt env s) =
      some (stateAt (ifThen103Out env v)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8) })) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifThen103Out env v)
        { s with
          pc := "if.then144",
          pre := some "if.then103",
          mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8) }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_then103Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then103
  rw [step_at hfind hout]
  rw [show if_then103Block.term = if_then103Term from rfl]
  simp only [if_then103Term]
  rw [LeanLLVM.Refinement.JsonS1BlocksRefine.execTerm_condbr_false
    (BlockEval.evalOperand_reg_of _ _ _ _ hbit) rfl]
  simp only [stateAt, hpc]

#print axioms if_then164_denote
#print axioms if_then164_step
#print axioms if_then150_denote
#print axioms if_then150_step
#print axioms if_then144_denote
#print axioms if_then144_step
#print axioms if_then103_denote
#print axioms if_then103_step_end147
#print axioms if_then103_step_then144

/-! ### What the module does not compose

The four runs stop at their blocks' own terminators.  The composition that ties
them into the unit is not here: the peel arm's entry from `for.end101` and the
phi merge at `if.end147`, the escape record that discharges the tail call's
`hc` at `if.then150`, and the tail's model-side identities — the DFA word the
peel writes and the two verdict bits it hands `if.end170`.  Those are the
caller's, as `if_then`'s escape arm already is in the unit's refinement. -/

end LeanLLVM.Refinement.JsonS1BlocksTail
