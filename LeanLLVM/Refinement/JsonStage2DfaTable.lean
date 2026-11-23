/-
The table-driven stage-2 dispatch, its encoding in Lean, and the first
soundness lemmas: the 8-symbol classifier, the 10-state transition table, the
parent-resume table, and the abstraction by which each row is a certified
value/container rule.

## What is here

`stage2_dfa.c` replaces the certified walk's per-byte `switch` and its chain of
value-rule branches with one byte classifier (`sd_cls`), one packed
`(action, next state)` load (`sd_tr`), and one parent-resume byte
(`sd_restore`).  This module states those three arrays as `sdCls`, `sdTr` and
`sdRestore`, and proves:

* `sdCls_correct` — the classifier is exactly the partition the certified
  walk's `switch` induces: the seven structural bytes map to their own symbol
  and every other byte is the scalar arm, over all 256 bytes;
* `Abs_total`, `Abs_injective`, `Abs_mem_reachable` — `Abs` is defined on all
  ten states, no two states are the same configuration, and each state's
  configuration is in the ten-entry reachable list;
* `sdRestore_sound` — on the three states whose push writes a resume byte, it
  is `Abs` of the state `s2_after_value` leaves the parent in;
* `sdTr_sound` — on all 80 rows, the table's action and next state are the
  certified rule's, read through `Abs`;
* `sdA_err_iff_refusal` — `A_ERR` is exactly where the certified rules refuse.

The two helper models are `stage2ValuePos` and `stage2AfterValue`
(`JsonStage2Body`), whose C calls are `s2_value_pos` and `s2_after_value`.
`s2ValuePos_reply` and `s2AfterValue_reply` (`JsonStage2Helpers`) are the
equations from the emitted call to those models; the bridge lemmas at the end
restate the table's tests at the calls' argument lists, so this module never
re-reads `Mem` for a rule and never proves a helper body.

## The C pin

The three arrays are a captured copy in
`probes/install/ir/stage2-dfa-tables.c`; compiling it and redirecting its
output gives `probes/install/ir/stage2-dfa.tables.txt`, which is the text
included below.  The `#guard`s compare that text with this module's encoding,
so a change to either table without the other fails elaboration.  A perturbed
row is rejected by the guard beside the equality.

## What this pass does not state

The walk-level statements are the next pass: that the DFA's stack byte
`stk[i]` is `Abs` of the parent's resumed state, that the abstract state and
the output cursors equal the certified run's at every entry, and that a
document the certified walk accepts never *meets* an `A_ERR` row (the row-level
fact proved here is only that `A_ERR` is the certified refusal).  No body,
fixture or bridge theorem is proved here.
-/
import LeanLLVM.Refinement.JsonStage2Helpers

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The alphabet, the states, and the actions -/

/-- The eight symbols the DFA classifies a byte into.  C order: `sd_cls` values
0..7. -/
inductive Sym where
  | lbrace    -- '{'
  | lbracket  -- '['
  | rbrace    -- '}'
  | rbracket  -- ']'
  | comma     -- ','
  | colon     -- ':'
  | quote     -- '"'
  | scalar    -- every other byte
  deriving DecidableEq, Repr

/-- The ten states, in `sd_tr`'s row order. -/
inductive St where
  | root       -- expecting the document's single root value
  | rootEnd    -- root done; nothing more is legal
  | objFirst   -- after '{': a key or '}'
  | objKey     -- after ',': a key, and not '}'
  | objColon   -- after a key: ':'
  | objVal     -- after ':': a value
  | objComma   -- after a value: ',' or '}'
  | arrFirst   -- after '[': a value or ']'
  | arrVal     -- after ',': a value, and not ']'
  | arrComma   -- after a value: ',' or ']'
  deriving DecidableEq, Repr

/-- The eight actions, in `sd_tr`'s packed order (`action << 4 | next`). -/
inductive Act where
  | none      -- comma or colon: state change only
  | openObj
  | openArr
  | closeObj
  | closeArr
  | quote     -- a key or a string, decided by the previous state
  | scalar
  | err       -- the entry is not legal in this state
  deriving DecidableEq, Repr

/-- The classifier: the seven structural bytes, everything else scalar.  The
byte literals are `'{'`, `'['`, `'}'`, `']'`, `','`, `':'` and `'"'`. -/
def sdCls (b : UInt8) : Sym :=
  if b = 123 then .lbrace
  else if b = 91 then .lbracket
  else if b = 125 then .rbrace
  else if b = 93 then .rbracket
  else if b = 44 then .comma
  else if b = 58 then .colon
  else if b = 34 then .quote
  else .scalar

/-- The transition table.  A close's next-state field is the stack's restore
value and is unused; the table writes `0` there, as the C does. -/
def sdTr : St → Sym → Act × St
  | .root, .lbrace => (.openObj, .objFirst)
  | .root, .lbracket => (.openArr, .arrFirst)
  | .root, .rbrace => (.err, .root)
  | .root, .rbracket => (.err, .root)
  | .root, .comma => (.err, .root)
  | .root, .colon => (.err, .root)
  | .root, .quote => (.quote, .rootEnd)
  | .root, .scalar => (.scalar, .rootEnd)
  | .rootEnd, .lbrace => (.err, .root)
  | .rootEnd, .lbracket => (.err, .root)
  | .rootEnd, .rbrace => (.err, .root)
  | .rootEnd, .rbracket => (.err, .root)
  | .rootEnd, .comma => (.err, .root)
  | .rootEnd, .colon => (.err, .root)
  | .rootEnd, .quote => (.err, .root)
  | .rootEnd, .scalar => (.err, .root)
  | .objFirst, .lbrace => (.err, .root)
  | .objFirst, .lbracket => (.err, .root)
  | .objFirst, .rbrace => (.closeObj, .root)
  | .objFirst, .rbracket => (.err, .root)
  | .objFirst, .comma => (.err, .root)
  | .objFirst, .colon => (.err, .root)
  | .objFirst, .quote => (.quote, .objColon)
  | .objFirst, .scalar => (.err, .root)
  | .objKey, .lbrace => (.err, .root)
  | .objKey, .lbracket => (.err, .root)
  | .objKey, .rbrace => (.err, .root)
  | .objKey, .rbracket => (.err, .root)
  | .objKey, .comma => (.err, .root)
  | .objKey, .colon => (.err, .root)
  | .objKey, .quote => (.quote, .objColon)
  | .objKey, .scalar => (.err, .root)
  | .objColon, .lbrace => (.err, .root)
  | .objColon, .lbracket => (.err, .root)
  | .objColon, .rbrace => (.err, .root)
  | .objColon, .rbracket => (.err, .root)
  | .objColon, .comma => (.err, .root)
  | .objColon, .colon => (.none, .objVal)
  | .objColon, .quote => (.err, .root)
  | .objColon, .scalar => (.err, .root)
  | .objVal, .lbrace => (.openObj, .objFirst)
  | .objVal, .lbracket => (.openArr, .arrFirst)
  | .objVal, .rbrace => (.err, .root)
  | .objVal, .rbracket => (.err, .root)
  | .objVal, .comma => (.err, .root)
  | .objVal, .colon => (.err, .root)
  | .objVal, .quote => (.quote, .objComma)
  | .objVal, .scalar => (.scalar, .objComma)
  | .objComma, .lbrace => (.err, .root)
  | .objComma, .lbracket => (.err, .root)
  | .objComma, .rbrace => (.closeObj, .root)
  | .objComma, .rbracket => (.err, .root)
  | .objComma, .comma => (.none, .objKey)
  | .objComma, .colon => (.err, .root)
  | .objComma, .quote => (.err, .root)
  | .objComma, .scalar => (.err, .root)
  | .arrFirst, .lbrace => (.openObj, .objFirst)
  | .arrFirst, .lbracket => (.openArr, .arrFirst)
  | .arrFirst, .rbrace => (.err, .root)
  | .arrFirst, .rbracket => (.closeArr, .root)
  | .arrFirst, .comma => (.err, .root)
  | .arrFirst, .colon => (.err, .root)
  | .arrFirst, .quote => (.quote, .arrComma)
  | .arrFirst, .scalar => (.scalar, .arrComma)
  | .arrVal, .lbrace => (.openObj, .objFirst)
  | .arrVal, .lbracket => (.openArr, .arrFirst)
  | .arrVal, .rbrace => (.err, .root)
  | .arrVal, .rbracket => (.err, .root)
  | .arrVal, .comma => (.err, .root)
  | .arrVal, .colon => (.err, .root)
  | .arrVal, .quote => (.quote, .arrComma)
  | .arrVal, .scalar => (.scalar, .arrComma)
  | .arrComma, .lbrace => (.err, .root)
  | .arrComma, .lbracket => (.err, .root)
  | .arrComma, .rbrace => (.err, .root)
  | .arrComma, .rbracket => (.closeArr, .root)
  | .arrComma, .comma => (.none, .arrVal)
  | .arrComma, .colon => (.err, .root)
  | .arrComma, .quote => (.err, .root)
  | .arrComma, .scalar => (.err, .root)

/-- The parent-resume table: the state a frame resumes in once its child
closes.  Unspecified entries are `0` (`root`), as in the C array. -/
def sdRestore : St → St
  | .objVal => .objComma
  | .arrFirst => .arrComma
  | .arrVal => .arrComma
  | _ => .root

/-! ### The C pin -/

/-- The captured C arrays, printed as three decimal rows. -/
def dfaTablesText : String :=
  include_str "../../probes/install/ir/stage2-dfa.tables.txt"

/-- One printed line: a tag and its decimal entries. -/
def parseTableLine (line : String) : Option (String × List Nat) :=
  match line.splitOn " " with
  | tag :: rest => some (tag, rest.filterMap String.toNat?)
  | [] => none

/-- The three arrays the captured text carries. -/
structure Tables where
  cls : List Nat
  tr : List Nat
  restore : List Nat
  deriving DecidableEq, Repr

def parseTables (src : String) : Option Tables :=
  let rows := (src.splitOn "\n").filter (fun l => !l.isEmpty) |>.filterMap parseTableLine
  match rows with
  | [("sd_cls", c), ("sd_tr", t), ("sd_restore", r)] => some ⟨c, t, r⟩
  | _ => none

def Sym.toNat : Sym → Nat
  | .lbrace => 0
  | .lbracket => 1
  | .rbrace => 2
  | .rbracket => 3
  | .comma => 4
  | .colon => 5
  | .quote => 6
  | .scalar => 7

def St.toNat : St → Nat
  | .root => 0
  | .rootEnd => 1
  | .objFirst => 2
  | .objKey => 3
  | .objColon => 4
  | .objVal => 5
  | .objComma => 6
  | .arrFirst => 7
  | .arrVal => 8
  | .arrComma => 9

def Act.toNat : Act → Nat
  | .none => 0
  | .openObj => 1
  | .openArr => 2
  | .closeObj => 3
  | .closeArr => 4
  | .quote => 5
  | .scalar => 6
  | .err => 7

def allSt : List St :=
  [.root, .rootEnd, .objFirst, .objKey, .objColon, .objVal, .objComma,
   .arrFirst, .arrVal, .arrComma]

def allSym : List Sym :=
  [.lbrace, .lbracket, .rbrace, .rbracket, .comma, .colon, .quote, .scalar]

/-- The classifier's 256 bytes in ascending byte order. -/
def sdClsRow : List Nat :=
  (List.range 256).map fun n => (sdCls (UInt8.ofNat n)).toNat

/-- The transition table's 80 packed bytes in `sd_tr[state][symbol]` order. -/
def sdTrRow : List Nat :=
  allSt.flatMap fun st =>
    allSym.map fun sym =>
      let t := sdTr st sym
      t.1.toNat * 16 + t.2.toNat

/-- The resume table's 10 bytes in state order. -/
def sdRestoreRow : List Nat :=
  allSt.map fun st => (sdRestore st).toNat

/- The captured text is exactly this module's three tables. -/
#guard decide (parseTables dfaTablesText = some ⟨sdClsRow, sdTrRow, sdRestoreRow⟩)

/- The pin is about the content: byte 0 of the captured classifier is scalar
(`7`), and a captured row that called it `lbrace` (`0`) is not this module's
row. -/
#guard decide (parseTables dfaTablesText ≠
  some ⟨(sdClsRow.tail.headD 0) :: (0 :: sdClsRow.tail.tail), sdTrRow, sdRestoreRow⟩)

#guard decide (sdClsRow.length = 256)
#guard decide (sdTrRow.length = 80)
#guard decide (sdRestoreRow.length = 10)

/-! ### The classifier over all 256 bytes -/

/-- `b` is none of the seven structural bytes. -/
def isScalarByte (b : UInt8) : Bool :=
  b ≠ 123 && b ≠ 91 && b ≠ 125 && b ≠ 93 && b ≠ 44 && b ≠ 58 && b ≠ 34

/-- The classifier's partition: each symbol names its byte, and `scalar` is
exactly the complement of the seven. -/
abbrev sdClsProp (b : UInt8) : Prop :=
  (sdCls b = .lbrace ↔ b = 123) ∧
  (sdCls b = .lbracket ↔ b = 91) ∧
  (sdCls b = .rbrace ↔ b = 125) ∧
  (sdCls b = .rbracket ↔ b = 93) ∧
  (sdCls b = .comma ↔ b = 44) ∧
  (sdCls b = .colon ↔ b = 58) ∧
  (sdCls b = .quote ↔ b = 34) ∧
  (sdCls b = .scalar ↔ isScalarByte b = true)

/- **The classifier is the certified `switch`'s partition**, for all 256
bytes.  The proof is 256 ground instances, decided together; `b.toNat` is the
enumeration index and `UInt8.ofNat_toNat` closes it. -/
set_option maxRecDepth 10000 in
theorem sdCls_correct (b : UInt8) : sdClsProp b := by
  have hcheck : (List.range 256).all
      (fun n => decide (sdClsProp (UInt8.ofNat n))) = true := by
    decide
  have hn : b.toNat ∈ List.range 256 := List.mem_range.mpr (UInt8.toNat_lt b)
  have hb := List.all_eq_true.mp hcheck b.toNat hn
  have hprop : sdClsProp (UInt8.ofNat b.toNat) := of_decide_eq_true hb
  rwa [UInt8.ofNat_toNat] at hprop

/-! ### The configurations the ten states name -/

/-- The certified walk's configuration: the root and its done flag, or one
container's `cst` phase.  `obj` has five phases (0 key-or-close, 1 colon,
2 value, 3 comma-or-close, 4 key), `arr` three (0 value-or-close, 1
comma-or-close, 2 value). -/
inductive Cfg where
  | root (done : Bool)
  | obj (cst : Fin 5)
  | arr (cst : Fin 3)
  deriving DecidableEq, Repr

/-- The state abstraction. -/
def Abs : St → Cfg
  | .root => .root false
  | .rootEnd => .root true
  | .objFirst => .obj 0
  | .objKey => .obj 4
  | .objColon => .obj 1
  | .objVal => .obj 2
  | .objComma => .obj 3
  | .arrFirst => .arr 0
  | .arrVal => .arr 2
  | .arrComma => .arr 1

/-- `Abs` is defined on every state. -/
theorem Abs_total (st : St) : ∃ c : Cfg, Abs st = c := ⟨Abs st, rfl⟩

/-- **`Abs` is injective**: distinct states are distinct configurations, so no
two table rows are the same rule. -/
theorem Abs_injective : Function.Injective Abs := by
  intro a b h
  cases a <;> cases b <;> simp_all [Abs]

/-- The ten configurations the ten states reach, in `St` order. -/
def reachableCfgs : List Cfg :=
  [.root false, .root true, .obj 0, .obj 4, .obj 1, .obj 2, .obj 3,
   .arr 0, .arr 2, .arr 1]

/-- Every state's configuration is one of the ten. -/
theorem Abs_mem_reachable (st : St) : Abs st ∈ reachableCfgs := by
  cases st <;> decide

/-- The list has no duplicates, so injectivity makes the ten states and the
ten configurations correspond one to one. -/
theorem reachableCfgs_nodup : reachableCfgs.Nodup := by decide

/-! ### The certified rules, as predicates on `Cfg` -/

def Cfg.depth : Cfg → Nat
  | .root _ => 0
  | _ => 1

def Cfg.rootDone : Cfg → Nat
  | .root false => 0
  | .root true => 1
  | _ => 0

/-- The container's `ctype` byte: `C_OBJ = 1`, `C_ARR = 2`, `0` at the root. -/
def Cfg.tyByte : Cfg → UInt8
  | .root _ => 0
  | .obj _ => 1
  | .arr _ => 2

/-- The container's `cst` byte, `0` at the root. -/
def Cfg.cstByte : Cfg → UInt8
  | .root _ => 0
  | .obj i => UInt8.ofNat i.val
  | .arr i => UInt8.ofNat i.val

/-- `s2_value_pos`'s test over a container's two bytes: object state 2, or
array state 0 or 2. -/
def valuePosOf (ty cst : UInt8) : Bool :=
  if ty.toNat = 1 then (if cst.toNat = 2 then true else false)
  else (if cst.toNat = 0 ∨ cst.toNat = 2 then true else false)

/-- A value is legal here: the still-open root, object state 2, or array state
0 or 2. -/
def valuePos : Cfg → Bool
  | .root false => true
  | .root true => false
  | c => valuePosOf c.tyByte c.cstByte

/-- A key is legal here: object state 0 (first member) or 4 (after a comma). -/
def keyPos : Cfg → Bool
  | .obj i => i.val = 0 ∨ i.val = 4
  | _ => false

/-- The object close test: state 0 (empty) or 3 (after a value). -/
def closeOkObj : Cfg → Bool
  | .obj i => i.val = 0 ∨ i.val = 3
  | _ => false

/-- The array close test: state 0 (empty) or 1 (after a value). -/
def closeOkArr : Cfg → Bool
  | .arr i => i.val = 0 ∨ i.val = 1
  | _ => false

/-- The object comma test: state 3. -/
def commaOkObj : Cfg → Bool
  | .obj i => i.val = 3
  | _ => false

/-- The array comma test: state 1. -/
def commaOkArr : Cfg → Bool
  | .arr i => i.val = 1
  | _ => false

/-- The colon test: object state 1 (after a key). -/
def colonOk : Cfg → Bool
  | .obj i => i.val = 1
  | _ => false

/-- `s2_after_value`: the root is done, an object goes to state 3, an array to
state 1. -/
def afterValue : Cfg → Cfg
  | .root _ => .root true
  | .obj _ => .obj ⟨3, by decide⟩
  | .arr _ => .arr ⟨1, by decide⟩

/-- The certified rule at a configuration and a symbol, in the table's own
shape: the action, and the resulting configuration when the action does not
close (a close resumes the parent, which the stack holds). -/
def certStep (c : Cfg) (sym : Sym) : Option (Act × Option Cfg) :=
  match sym with
  | .lbrace =>
      if valuePos c then some (.openObj, some (.obj 0)) else none
  | .lbracket =>
      if valuePos c then some (.openArr, some (.arr 0)) else none
  | .rbrace =>
      if closeOkObj c then some (.closeObj, none) else none
  | .rbracket =>
      if closeOkArr c then some (.closeArr, none) else none
  | .comma =>
      match c with
      | .obj _ => if commaOkObj c then some (.none, some (.obj 4)) else none
      | .arr _ => if commaOkArr c then some (.none, some (.arr 2)) else none
      | _ => none
  | .colon =>
      match c with
      | .obj _ => if colonOk c then some (.none, some (.obj 2)) else none
      | _ => none
  | .quote =>
      if keyPos c then some (.quote, some (.obj 1))
      else if valuePos c then some (.quote, some (afterValue c)) else none
  | .scalar =>
      if valuePos c then some (.scalar, some (afterValue c)) else none

/-- The table's rule in the same shape: the packed action, with the
next-state field dropped for a close. -/
def isClose : Act → Bool
  | .closeObj => true
  | .closeArr => true
  | _ => false

def tableStep (st : St) (sym : Sym) : Option (Act × Option St) :=
  let t := sdTr st sym
  if t.1 = .err then none
  else some (t.1, if isClose t.1 then none else some t.2)

/-- **The transition table is the certified value/container rule**: on all 80
rows the action and the resulting configuration agree, with `Abs` read through
the next state and a close's resume left to the stack. -/
theorem sdTr_sound (st : St) (sym : Sym) :
    (tableStep st sym).map (fun p => (p.1, p.2.map Abs)) = certStep (Abs st) sym := by
  cases st <;> cases sym <;> decide

/-- **The resume table is `s2_after_value` at the parent**: on the three states
whose push writes a resume byte (`objVal`, `arrFirst`, `arrVal` — the root's
push writes none because the stack is empty), the byte is `Abs` of the state
the parent takes after its child's value.  The other seven rows are the C
array's default `0` and are never read as a resume value. -/
theorem sdRestore_sound (st : St) :
    (st = .objVal ∨ st = .arrFirst ∨ st = .arrVal) →
      Abs (sdRestore st) = afterValue (Abs st) := by
  cases st <;> decide

/-- **`A_ERR` is exactly the certified refusal**: a row the table marks `err`
is a row the certified rule refuses, and every other row is accepted.  (That
an accepted document never *meets* an `A_ERR` row is the walk invariant, not a
row-level statement.) -/
theorem sdA_err_iff_refusal (st : St) (sym : Sym) :
    (sdTr st sym).1 = .err ↔ certStep (Abs st) sym = none := by
  cases st <;> cases sym <;> decide

/-! ### The bridges to the emitted calls' models -/

/-- **`s2_value_pos`'s model at the configuration `Abs` names.**  The reply
theorem that turns the emitted call into this model is `s2ValuePos_reply`. -/
theorem stage2ValuePos_cfg (mem : Mem) (c : Cfg) (ct cs : Nat)
    (hct : readByte mem ct = some c.tyByte)
    (hcs : readByte mem cs = some c.cstByte) :
    stage2ValuePos mem c.depth c.rootDone ct cs =
      some (if valuePos c then 1 else 0) := by
  cases c with
  | root done =>
      cases done <;> simp [stage2ValuePos, Cfg.depth, Cfg.rootDone, valuePos]
  | obj i =>
      simp [stage2ValuePos, Cfg.depth, Cfg.tyByte, Cfg.cstByte,
        valuePos, valuePosOf, hct, hcs]
  | arr i =>
      simp [stage2ValuePos, Cfg.depth, Cfg.tyByte, Cfg.cstByte,
        valuePos, valuePosOf, hct, hcs]

/-- **`s2_after_value`'s model at the root**: it sets the done slot. -/
theorem stage2AfterValue_root (mem : Mem) (done : Bool) (ct cs : Nat) :
    stage2AfterValue mem 0 (if done then 1 else 0) ct cs =
      some (writeBytes mem (if done then 1 else 0) (wordBytes 4 1)) := by
  simp [stage2AfterValue]

/-- **`s2_after_value`'s model at a container**: it writes the phase byte the
table's `afterValue` names — `3` after an object member, `1` after an array
element. -/
theorem stage2AfterValue_container (mem : Mem) (c : Cfg) (ct cs : Nat)
    (hd : c.depth = 1) (hct : readByte mem ct = some c.tyByte) :
    stage2AfterValue mem c.depth c.rootDone ct cs =
      some (writeBytes mem cs
        [UInt8.ofNat (if c.tyByte.toNat = 1 then 3 else 1)]) := by
  cases c <;> simp_all [stage2AfterValue, Cfg.depth, Cfg.tyByte]

end LeanLLVM.Refinement
