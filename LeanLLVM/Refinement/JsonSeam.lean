/-
The JSON seam: the reference selection, the installed candidate's selection, the
staging caller, and the contextual replacement theorem.

`LeanLLVM/Refinement/JsonClassifyIR.lean` proves the emitted classifier body returns
the block layer's mask on every block readable at its argument.  This module
lifts that body to a call environment (`envForBodySym`) and states the
reference selection beside it (`envForMask`), relates the two at every symbol
(`classifySeam_refines`), and carries the relation through a caller that stages
its own block (`scanCaller`): `replaceScanner_sound` is the framed replacement,
`replaceScanner_ret` its one behaviour for four words, and
`wrongMask_not_refines` the negative control.

The reference selection is the verified scalar transition, run on the block the
caller's memory holds: there is no baseline LLVM body, because the fragment has
no pointer arithmetic, so no scalar byte-walking body can be written in it.
Both selections allocate nothing and return the caller's memory unchanged, which
is why the caller's frame is empty.

`probes/install/ir/json-caller.ll` is printed from `scanCaller` by
`lake exe leanllvm-json-emit` through the framework's printer, verified with
`opt -passes=verify`, and parsed back and pinned below with `#guard`.
-/
import LeanLLVM.Parser
import LeanLLVM.Semantics
import LeanLLVM.Memory
import LeanLLVM.Frames
import LeanLLVM.CallRefinement
import LeanLLVM.Refinement.JsonClassifyIR
import LeanLLVM.Refinement.ModuleRefinement

namespace LeanLLVM.Refinement.JsonSeam

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.SeamContext (seamSymbol envForBody)
open LeanLLVM.Refinement.JsonClassifyIR (classify32Function classify32Instrs classify32Body
  classifyRun classifyRun_mem lookupName_classifyRun packed packed_eq_maskOf
  classify32_block classify32_step classify32_step_ub classify32_next_independent
  scannerLLVM_refines classify32_undefined_of_no_read wrongMaskFunction argName)

/-! ### The selections -/

/-- The JSON seam's symbol, as the linker and the call environment name it. -/
def jsonSeamSymbol : String := "leanllvm_json_classify32"

/-- The reference selection: the verified scalar transition, run on the block the
caller's memory holds at the pointer.  This is the source side of the pair — not
an LLVM body, because the fragment has no pointer arithmetic, so no scalar
byte-walking body can be written in it.  It allocates nothing and returns the
caller's memory unchanged. -/
def envForMask : Calls :=
  fun callee args mem next =>
    if callee = jsonSeamSymbol then
      match args with
      | [.ptr p] =>
          match readBytes mem p 32 with
          | some bs => some { ret := .int 32 (maskOfList bs), mem := mem, next := next }
          | none => none
      | _ => none
    else none

/-- The environment an installed body provides, generalised over the symbol the
selection resolves.  `SeamContext.envForBody` is this at `seamSymbol`, and
`envForBodySym_comma` records the identity.  The seam runs `f` from the caller's
memory and from an allocator whose next free address is the caller's `next`, with
the parameters bound to the arguments; the caller resumes from `next + reserve`,
the frame the selection reserves for the body.  A run that reaches `ub`, or that
does not return a value within `fuel`, is an unresolved call. -/
def envForBodySym (sym : String) (fuel reserve : Nat) (f : Function) : Calls :=
  fun callee args mem next =>
    if callee = sym then
      let s : State :=
        { env := (f.params.zip args).map fun p => (p.1.1, p.2)
          mem := mem, next := next, pc := f.entry?.getD "", pre := none }
      match runFuel noCalls fuel f s with
      | some (.ret (some v) m) => some { ret := v, mem := m, next := next + reserve }
      | _ => none
    else none

/-- The JSON selection is `SeamContext.envForBody` generalised over the symbol:
at the comma-mask symbol the two are the same function.  A change to either
breaks this `rfl`, so the two cannot drift. -/
theorem envForBodySym_comma (fuel reserve : Nat) (f : Function) :
    envForBodySym seamSymbol fuel reserve f = envForBody fuel reserve f := rfl

/-! ### The caller fixture -/

/-- The staging caller as emitted (`probes/install/ir/json-caller.ll`).  The pin
below compares the whole module, declaration included: the fixture carries the
seam's `declare` line because `opt -passes=verify` refuses a call to an
undeclared symbol, and a pin over the functions alone would leave those bytes
unobserved while the file is claimed as the printer's output whole.  A
parse-equality pins every token the parser models, not comments or formatting;
the emitter's round-trip check and `opt -passes=verify` cover those. -/
def scanCallerSrc : String := include_str "../../probes/install/ir/json-caller.ll"

/-- The caller: four `i64` words, staged into four locals from address `1`, then
the seam called on the first local's address.  The staging is what `Beh`
requires: it runs a caller from `initState`, whose memory is empty, so a caller
that only calls would hand the callee nothing to read.  `initState` starts the allocator at
`1`, so the locals are at `1, 9, 17, 25` and the callee reads the 32 bytes of the
four words little-endian. -/
def scanCaller : Function :=
  { name := "leanllvm_json_scan_caller", retTy := .int 32,
    params := [("%w0", .int 64), ("%w1", .int 64), ("%w2", .int 64), ("%w3", .int 64)],
    blocks := [
      { name := "entry",
        instrs := [
          .alloca "%b0" (.int 64) 8,
          .alloca "%b1" (.int 64) 8,
          .alloca "%b2" (.int 64) 8,
          .alloca "%b3" (.int 64) 8,
          .store (.int 64) (.reg "%w0") (.reg "%b0"),
          .store (.int 64) (.reg "%w1") (.reg "%b1"),
          .store (.int 64) (.reg "%w2") (.reg "%b2"),
          .store (.int 64) (.reg "%w3") (.reg "%b3"),
          .call "%m" (.int 32) jsonSeamSymbol [(.ptr, .reg "%b0")] ],
        term := .ret (.int 32) (some (.reg "%m")) } ] }

-- The whole module, declaration included: `parseModule` returns
-- `Except String Module`, so a successful parse is read through `toOption` and
-- an error is `none`, which fails the pin.  A parse-equality pins every token
-- the parser models, not comments or formatting; the emitter's round-trip check
-- and `opt -passes=verify` cover those.
#guard decide ((parseModule scanCallerSrc).toOption =
  some (⟨[⟨"leanllvm_json_classify32", .int 32, [.ptr]⟩], [scanCaller]⟩ : Module))

/-- The 32 bytes the four words stage, in the order the callee reads them. -/
def blockOf (w0 w1 w2 w3 : BitVec 64) : List UInt8 :=
  natToBytes w0.toNat 8 ++ natToBytes w1.toNat 8 ++
  natToBytes w2.toNat 8 ++ natToBytes w3.toNat 8

/-- The caller's memory after its four stores: empty memory with each word's
eight little-endian bytes written at the address its `alloca` handed out
(`1`, `9`, `17`, `25`).  A `Mem` is a byte list and carries no allocator state —
the caller's allocator reaches `33` in its *state*, which is not part of an
`Outcome` (`Semantics.lean:246-251`). -/
def stagedMem (w0 w1 w2 w3 : BitVec 64) : Mem :=
  writeBytes
    (writeBytes
      (writeBytes
        (writeBytes [] 1 (natToBytes w0.toNat 8))
        9 (natToBytes w1.toNat 8))
      17 (natToBytes w2.toNat 8))
    25 (natToBytes w3.toNat 8)

/-! ### Reading the staged block -/

/-- A successful read of `n` bytes returns `n` bytes. -/
theorem readBytes_length {m : Mem} {addr n : Nat} {bs : List UInt8}
    (h : readBytes m addr n = some bs) : bs.length = n := by
  induction n generalizing addr bs with
  | zero =>
      simp only [readBytes, Option.some.injEq] at h
      subst h
      rfl
  | succ k ih =>
      simp only [readBytes] at h
      cases hb : readByte m addr with
      | none =>
          rw [hb] at h
          cases h
      | some b =>
          rw [hb] at h
          cases hr : readBytes m (addr + 1) k with
          | none =>
              rw [hr] at h
              cases h
          | some cs =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              simp only [List.length_cons, ih hr]

/-- A write of a concatenation is the two writes in order: the second starts
where the first ended. -/
theorem writeBytes_append (m : Mem) (start : Nat) :
    ∀ (bs cs : List UInt8),
      writeBytes m start (bs ++ cs) =
        writeBytes (writeBytes m start bs) (start + bs.length) cs
  | [], cs => by simp [writeBytes]
  | b :: bs, cs => by
      simp only [List.cons_append, writeBytes, List.length_cons]
      rw [show start + (bs.length + 1) = start + 1 + bs.length from by omega]
      exact writeBytes_append (writeByte m start b) (start + 1) bs cs

/-- The four staged writes are one write of the 32 staged bytes at address `1`. -/
theorem stagedMem_eq (w0 w1 w2 w3 : BitVec 64) :
    stagedMem w0 w1 w2 w3 = writeBytes [] 1 (blockOf w0 w1 w2 w3) := by
  rw [blockOf, stagedMem]
  rw [writeBytes_append [] 1 (natToBytes w0.toNat 8 ++ natToBytes w1.toNat 8 ++
        natToBytes w2.toNat 8) (natToBytes w3.toNat 8)]
  rw [show 1 + (natToBytes w0.toNat 8 ++ natToBytes w1.toNat 8 ++
        natToBytes w2.toNat 8).length = 25 from by simp [natToBytes_length]]
  rw [writeBytes_append [] 1 (natToBytes w0.toNat 8 ++ natToBytes w1.toNat 8)
        (natToBytes w2.toNat 8)]
  rw [show 1 + (natToBytes w0.toNat 8 ++ natToBytes w1.toNat 8).length = 17
        from by simp [natToBytes_length]]
  rw [writeBytes_append [] 1 (natToBytes w0.toNat 8) (natToBytes w1.toNat 8)]
  rw [show 1 + (natToBytes w0.toNat 8).length = 9 from by rw [natToBytes_length]]

/-- The staged block is 32 bytes, which is what `List.ofFn` needs. -/
theorem blockOf_length (w0 w1 w2 w3 : BitVec 64) : (blockOf w0 w1 w2 w3).length = 32 := by
  simp [blockOf, natToBytes_length]

/-- The callee's 32-byte read: the four staged words as `blockOf` concatenates
them. -/
theorem readBytes_staged (w0 w1 w2 w3 : BitVec 64) :
    readBytes (stagedMem w0 w1 w2 w3) 1 32 = some (blockOf w0 w1 w2 w3) := by
  rw [stagedMem_eq, ← blockOf_length w0 w1 w2 w3]
  exact readBytes_writeBytes_same [] (blockOf w0 w1 w2 w3)

/-- A 32-byte list is the `List.ofFn` of its own indexing, bundled with the
function that indexes it. -/
theorem exists_block_of_length {bs : List UInt8} (h : bs.length = 32) :
    ∃ block : Block32, List.ofFn block = bs :=
  ⟨fun i => bs[i.val]'(by omega), ofFn_of_length h⟩

/-- The mask of the block a byte list indexes is the list's mask. -/
theorem maskOf_block_eq {bs : List UInt8} {block : Block32} (h : List.ofFn block = bs) :
    maskOf block = maskOfList bs := by
  rw [maskOf, h]

/-! ### The body at a seeded allocator

`envForBodySym` seeds the body at the caller's `next`, so the statements below
read `classify32_step` directly rather than going through `initState`; the body
allocates nothing, so the allocator state is inert. -/

/-- The classified body from a state whose argument is a readable pointer, at
any allocator state. -/
theorem classify32_seed_run (block : Block32) (mem : Mem) (p next : Nat)
    (hread : readBytes mem p 32 = some (List.ofFn block)) :
    runFuel noCalls 10000 classify32Function
        { env := (classify32Function.params.zip [.ptr p]).map fun q => (q.1.1, q.2)
          mem := mem, next := next, pc := classify32Function.entry?.getD "", pre := none } =
      some (.ret (some (.int 32 (maskOf block))) mem) := by
  let s : State :=
    { env := (classify32Function.params.zip [.ptr p]).map fun q => (q.1.1, q.2)
      mem := mem, next := next, pc := classify32Function.entry?.getD "", pre := none }
  change runFuel noCalls 10000 classify32Function s =
    some (.ret (some (.int 32 (maskOf block))) mem)
  have harg : lookupName s.env argName = some (.ptr p) := by
    simp [s, classify32Function, argName, List.map, List.zip, List.zipWith]
  have hpc : s.pc = "bb" := rfl
  simp only [runFuel, classify32_step noCalls s block p harg hread hpc, classifyRun_mem,
    s]

/-- The classified body from a state whose argument pointer is not readable, at
any allocator state. -/
theorem classify32_seed_run_ub (mem : Mem) (p next : Nat)
    (hread : readBytes mem p 32 = none) :
    runFuel noCalls 10000 classify32Function
        { env := (classify32Function.params.zip [.ptr p]).map fun q => (q.1.1, q.2)
          mem := mem, next := next, pc := classify32Function.entry?.getD "", pre := none } =
      some .ub := by
  let s : State :=
    { env := (classify32Function.params.zip [.ptr p]).map fun q => (q.1.1, q.2)
      mem := mem, next := next, pc := classify32Function.entry?.getD "", pre := none }
  change runFuel noCalls 10000 classify32Function s = some .ub
  have harg : lookupName s.env argName = some (.ptr p) := by
    simp [s, classify32Function, argName, List.map, List.zip, List.zipWith]
  have hpc : s.pc = "bb" := rfl
  simp only [runFuel, classify32_step_ub noCalls s p harg hread hpc]

/-- The classifier's first instruction reads `%arg` as a pointer, so a
non-pointer argument leaves the step unresolved. -/
theorem classify32_step_nonptr (calls : Calls) (s : State) (v : Value)
    (harg : lookupName s.env argName = some v) (hne : ∀ p, v ≠ .ptr p)
    (hpc : s.pc = "bb") :
    step calls classify32Function s = .ub := by
  have hfind : classify32Function.findBlock s.pc = some classify32Body := by
    simp [hpc, classify32Function, classify32Body, Function.findBlock, findBlockList]
  cases v with
  | int w x =>
      simp only [step, hfind, classify32Body, classify32Instrs, denoteCode, denoteRun, State.bindAll, evalInstr,
        evalOperand, harg]
  | ptr p => exact absurd rfl (hne p)
  | vec n w l =>
      simp only [step, hfind, classify32Body, classify32Instrs, denoteCode, denoteRun, State.bindAll, evalInstr,
        evalOperand, harg]
  | float b =>
      simp only [step, hfind, classify32Body, classify32Instrs, denoteCode, denoteRun, State.bindAll, evalInstr,
        evalOperand, harg]

/-- The classifier body run from a state whose argument is not a pointer is
undefined. -/
theorem classify32_run_ub_of_head (v : Value) (rest : List Value) (mem : Mem)
    (next : Nat) (hne : ∀ p, v ≠ .ptr p) :
    runFuel noCalls 10000 classify32Function
        { env := (classify32Function.params.zip (v :: rest)).map fun q => (q.1.1, q.2)
          mem := mem, next := next, pc := classify32Function.entry?.getD "", pre := none } = some .ub := by
  let s : State :=
    { env := (classify32Function.params.zip (v :: rest)).map fun q => (q.1.1, q.2)
      mem := mem, next := next, pc := classify32Function.entry?.getD "", pre := none }
  change runFuel noCalls 10000 classify32Function s = some .ub
  have harg : lookupName s.env argName = some v := by
    simp [s, classify32Function, argName, List.map, List.zip, List.zipWith]
  have hstep : step noCalls classify32Function s = .ub :=
    classify32_step_nonptr noCalls s v harg hne rfl
  simp only [runFuel, hstep]

/-! ### The selections agree at one pointer argument -/

/-- The candidate's selection at a single pointer argument is the reference
selection at the same argument.  This is the bridge the caller-level theorems
consume: the caller's one call passes exactly one argument. -/
theorem envForBodySym_eq_envForMask (v : Value) (mem : Mem) (next : Nat) :
    envForBodySym jsonSeamSymbol 10000 0 classify32Function jsonSeamSymbol [v] mem next =
      envForMask jsonSeamSymbol [v] mem next := by
  cases v with
  | ptr p =>
      cases hread : readBytes mem p 32 with
      | none =>
          simp only [envForBodySym, classify32_seed_run_ub mem p next hread, ↓reduceIte,
            envForMask, hread]
      | some bs =>
          have hlen : bs.length = 32 := readBytes_length hread
          obtain ⟨block, hblock⟩ := exists_block_of_length hlen
          have hreadBlock : readBytes mem p 32 = some (List.ofFn block) := by
            rw [hblock]
            exact hread
          have hmask : maskOf block = maskOfList bs := maskOf_block_eq hblock
          simp only [envForBodySym, classify32_seed_run block mem p next hreadBlock,
            ↓reduceIte, envForMask, hread, hmask, Nat.add_zero]
  | int w x =>
      simp only [envForBodySym, classify32_run_ub_of_head (.int w x) [] mem next
        (by intro p h; cases h), ↓reduceIte, envForMask]
  | vec n w l =>
      simp only [envForBodySym, classify32_run_ub_of_head (.vec n w l) [] mem next
        (by intro p h; cases h), ↓reduceIte, envForMask]
  | float b =>
      simp only [envForBodySym, classify32_run_ub_of_head (.float b) [] mem next
        (by intro p h; cases h), ↓reduceIte, envForMask]

/-- `classifySeam_refines`: the installed candidate refines the reference
selection at every symbol, outside an empty frame.  `replaceScanner_sound`
consumes this at the caller's one call, which is where the relation is
exercised. -/
theorem classifySeam_refines :
    ∀ sym, CallRefinesWithin (envForBodySym jsonSeamSymbol 10000 0 classify32Function)
      envForMask sym (ReserveFrame 0) := by
  intro sym args mem next
  by_cases hs : sym = jsonSeamSymbol
  · subst hs
    match args with
    | [] => exact Or.inl (by simp [envForMask])
    | [.ptr p] =>
        cases hread : readBytes mem p 32 with
        | none => exact Or.inl (by simp [envForMask, hread])
        | some bs =>
            have hlen : bs.length = 32 := readBytes_length hread
            obtain ⟨block, hblock⟩ := exists_block_of_length hlen
            have hreadBlock : readBytes mem p 32 = some (List.ofFn block) := by
              rw [hblock]
              exact hread
            have hmask : maskOf block = maskOfList bs := maskOf_block_eq hblock
            refine Or.inr ⟨{ ret := .int 32 (maskOf block), mem := mem, next := next + 0 },
              { ret := .int 32 (maskOfList bs), mem := mem, next := next }, ?_, ?_, ?_,
              Nat.le_refl next, ?_, AgreesOutsideMem.refl mem (ReserveFrame 0 next)⟩
            · simp only [envForBodySym, classify32_seed_run block mem p next hreadBlock,
                ↓reduceIte]
            · simp only [envForMask, hread, ↓reduceIte]
            · simp [hmask]
            · show next + 0 = next
              omega
    | .ptr p :: _ :: _ => exact Or.inl (by simp [envForMask])
    | .int w x :: _ => exact Or.inl (by simp [envForMask])
    | .vec n w l :: _ => exact Or.inl (by simp [envForMask])
    | .float b :: _ => exact Or.inl (by simp [envForMask])
  · exact Or.inl (by simp [envForMask, hs])

/-! ### The caller's step equivalence -/

/-- The two selections agree at the caller's one call: it passes a single
argument, and the candidate and the reference agree at every single-argument
list. -/
theorem evalInstr_call_eq (s : State) (d : String) (retTy : Ty) :
    evalInstr (envForBodySym jsonSeamSymbol 10000 0 classify32Function) s
        (.call d retTy jsonSeamSymbol [(.ptr, .reg "%b0")]) =
      evalInstr envForMask s (.call d retTy jsonSeamSymbol [(.ptr, .reg "%b0")]) := by
  simp only [evalInstr, evalOperands, evalOperand]
  cases hb : lookupName s.env "%b0" with
  | none => rfl
  | some v => simp only [envForBodySym_eq_envForMask v s.mem s.next]

/-- The caller's control step is the same under the two selections.  The call is
the only environment-dependent instruction, and the two selections agree on the
argument list the caller produces. -/
theorem scanCaller_step_eq (s : State) :
    step (envForBodySym jsonSeamSymbol 10000 0 classify32Function) scanCaller s =
      step envForMask scanCaller s := by
  by_cases hpc : s.pc = "entry"
  · have hfind : scanCaller.findBlock s.pc =
        some { name := "entry",
               instrs := [
                 .alloca "%b0" (.int 64) 8,
                 .alloca "%b1" (.int 64) 8,
                 .alloca "%b2" (.int 64) 8,
                 .alloca "%b3" (.int 64) 8,
                 .store (.int 64) (.reg "%w0") (.reg "%b0"),
                 .store (.int 64) (.reg "%w1") (.reg "%b1"),
                 .store (.int 64) (.reg "%w2") (.reg "%b2"),
                 .store (.int 64) (.reg "%w3") (.reg "%b3"),
                 .call "%m" (.int 32) jsonSeamSymbol [(.ptr, .reg "%b0")]],
               term := .ret (.int 32) (some (.reg "%m")) } := by
      simp [hpc, scanCaller, Function.findBlock, findBlockList]
    simp only [step, hfind]
    simp only [denoteCode, denoteRun, State.bindAll, evalInstr_call_eq]
    simp only [evalInstr]
  · have hnone : scanCaller.findBlock s.pc = none := by
      simp [scanCaller, Function.findBlock, findBlockList]
      exact fun h => hpc h.symm
    simp only [step, hnone]

/-- The caller's run is the same under the two selections, at every fuel and
from every state. -/
theorem scanCaller_runFuel_eq (n : Nat) (s : State) :
    runFuel (envForBodySym jsonSeamSymbol 10000 0 classify32Function) n scanCaller s =
      runFuel envForMask n scanCaller s := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
      simp only [runFuel, scanCaller_step_eq s]
      cases hs : step envForMask scanCaller s with
      | ub => rfl
      | ret v s' => rfl
      | jump s' => exact ih s'

/-- The caller's behaviours are the same under the two selections.
`replaceScanner_ret` consumes this to state the caller's unique outcome under the
installed body, and `replaceScanner_sound` consumes it off the one call: an
argument list that does not stage four words leaves both selections undefined
before the call. -/
theorem scanCaller_beh_eq (args : List Value) (o : Outcome) :
    Beh (envForBodySym jsonSeamSymbol 10000 0 classify32Function) scanCaller args o ↔
      Beh envForMask scanCaller args o := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact Or.inl ⟨n, by
        rw [← scanCaller_runFuel_eq n (initState scanCaller args)]; exact hn⟩
    · exact Or.inr ⟨n, by
        rw [← scanCaller_runFuel_eq n (initState scanCaller args)]; exact hn⟩
  · intro h
    rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact Or.inl ⟨n, by
        rw [scanCaller_runFuel_eq n (initState scanCaller args)]; exact hn⟩
    · exact Or.inr ⟨n, by
        rw [scanCaller_runFuel_eq n (initState scanCaller args)]; exact hn⟩

/-! ### The caller under the reference selection -/

/-- The reference selection resolves the caller's call at address `1` with the
staged memory and the allocator at `33`. -/
theorem envForMask_scanCaller_call (w0 w1 w2 w3 : BitVec 64) :
    envForMask jsonSeamSymbol [.ptr 1] (stagedMem w0 w1 w2 w3) 33 =
      some { ret := .int 32 (maskOfList (blockOf w0 w1 w2 w3)),
             mem := stagedMem w0 w1 w2 w3, next := 33 } := by
  simp only [envForMask, jsonSeamSymbol, readBytes_staged, ↓reduceIte]

/-- The caller's one control step under any selection that resolves its call at
address `1` with the staged memory and the allocator at `33`: four allocations at
`1, 9, 17, 25`, four stores of the words, the call, and the return of what the
call gave back.  The selection and the call's outcome are parameters, because
`replaceScanner_sound` reads the caller's run off the relation's two call
outcomes. -/
theorem scanCaller_step_of_call (calls : Calls) (w0 w1 w2 w3 : BitVec 64)
    (v : Value) (m : Mem) (next : Nat)
    (h : calls jsonSeamSymbol [.ptr 1] (stagedMem w0 w1 w2 w3) 33 = some ⟨v, m, next⟩) :
    step calls scanCaller
        (initState scanCaller [.int 64 w0, .int 64 w1, .int 64 w2, .int 64 w3]) =
      .ret (some v)
        { env := [("%m", v), ("%b3", .ptr 25), ("%b2", .ptr 17), ("%b1", .ptr 9),
                  ("%b0", .ptr 1), ("%w0", .int 64 w0), ("%w1", .int 64 w1),
                  ("%w2", .int 64 w2), ("%w3", .int 64 w3)]
          mem := m, next := next, pc := "entry", pre := none } := by
  have h' : calls jsonSeamSymbol [.ptr 1]
      (writeBytes (writeBytes (writeBytes (writeBytes [] 1 (natToBytes w0.toNat 8))
        9 (natToBytes w1.toNat 8)) 17 (natToBytes w2.toNat 8)) 25
        (natToBytes w3.toNat 8)) 33 = some ⟨v, m, next⟩ := by
    simpa only [stagedMem] using h
  simp [step, scanCaller, Function.findBlock, findBlockList, Function.entry?, List.head?,
    Option.getD, Option.map, initState, List.map, List.zip, List.zipWith, denoteCode, denoteRun, State.bindAll,
    evalInstr, evalOperands, evalOperand, execTerm, Ty.sizeBytes, lookupName,
    storeValue, h']

/-- The caller's run under a selection that resolves its call completes in one
step, for any fuel. -/
theorem scanCaller_runFuel_succ_of_call (calls : Calls) (w0 w1 w2 w3 : BitVec 64)
    (v : Value) (m : Mem) (next : Nat)
    (h : calls jsonSeamSymbol [.ptr 1] (stagedMem w0 w1 w2 w3) 33 = some ⟨v, m, next⟩)
    (n : Nat) :
    runFuel calls (n + 1) scanCaller
        (initState scanCaller [.int 64 w0, .int 64 w1, .int 64 w2, .int 64 w3]) =
      some (.ret (some v) m) := by
  simp only [runFuel, scanCaller_step_of_call calls w0 w1 w2 w3 v m next h]

/-- The caller has exactly one behaviour under any selection that resolves its
call: the call's value, with the call's memory.  `replaceScanner_sound` consumes
this at the two call outcomes the relation relates, and `scanCaller_beh` is its
reference-selection instance. -/
theorem scanCaller_beh_of_call (calls : Calls) (w0 w1 w2 w3 : BitVec 64)
    (v : Value) (m : Mem) (next : Nat)
    (h : calls jsonSeamSymbol [.ptr 1] (stagedMem w0 w1 w2 w3) 33 = some ⟨v, m, next⟩)
    (o : Outcome) :
    Beh calls scanCaller [.int 64 w0, .int 64 w1, .int 64 w2, .int 64 w3] o ↔
      o = .ret (some v) m := by
  constructor
  · intro hb
    rcases hb with ⟨n, hn⟩ | ⟨n, hn⟩
    · cases n with
      | zero => simp [runFuel] at hn
      | succ k =>
          rw [scanCaller_runFuel_succ_of_call calls w0 w1 w2 w3 v m next h k] at hn
          simp at hn
    · cases n with
      | zero => simp [runFuel] at hn
      | succ k =>
          rw [scanCaller_runFuel_succ_of_call calls w0 w1 w2 w3 v m next h k] at hn
          exact (Option.some.inj hn).symm
  · intro ho
    subst ho
    exact Or.inr ⟨1, scanCaller_runFuel_succ_of_call calls w0 w1 w2 w3 v m next h 0⟩

/-- The caller has exactly one behaviour under the reference selection, for any
four words: the mask of the bytes they stage, with the caller's memory intact.
`replaceScanner_ret` consumes this: it is how the caller's unique outcome under
the installed body is stated, through `scanCaller_beh_eq`. -/
theorem scanCaller_beh (w0 w1 w2 w3 : BitVec 64) (o : Outcome) :
    Beh envForMask scanCaller [.int 64 w0, .int 64 w1, .int 64 w2, .int 64 w3] o ↔
      o = .ret (some (.int 32 (maskOfList (blockOf w0 w1 w2 w3))))
        (stagedMem w0 w1 w2 w3) :=
  scanCaller_beh_of_call envForMask w0 w1 w2 w3
    (.int 32 (maskOfList (blockOf w0 w1 w2 w3))) (stagedMem w0 w1 w2 w3) 33
    (envForMask_scanCaller_call w0 w1 w2 w3) o

/-! ### The contextual replacement -/

/-- The caller's four parameters are bound by the first four arguments, so a
longer argument list runs from the same initial state. -/
theorem initState_scanCaller_cons (w0 w1 w2 w3 : BitVec 64) (rest : List Value) :
    initState scanCaller
        (.int 64 w0 :: .int 64 w1 :: .int 64 w2 :: .int 64 w3 :: rest) =
      initState scanCaller [.int 64 w0, .int 64 w1, .int 64 w2, .int 64 w3] := rfl

/-- `replaceScanner_sound`.  The caller's behaviour under the installed
candidate's selection is matched by its behaviour under the reference selection,
outside an empty footprint.  The frame is `Nat → Prop` here — one predicate,
because the caller-level relation has no allocator base to index — and
`fun _ => False` is what `ReserveFrame 0 base` is at every base.

The proof consults `classifySeam_refines` at the caller's one call: the relation
supplies the two call outcomes, and its value and memory clauses are the target
outcome's `Outcome.AgreesOutside` at the empty frame.  Where the four stores do
not stage the call at all — anything but four `i64` words — both selections are
undefined before the call, which `scanCaller_beh_eq` states. -/
theorem replaceScanner_sound :
    RefinesWithinAcross (envForBodySym jsonSeamSymbol 10000 0 classify32Function)
      envForMask scanCaller scanCaller (fun _ => False) := by
  intro args o ho
  match args with
  | .int 64 w0 :: .int 64 w1 :: .int 64 w2 :: .int 64 w3 :: rest =>
      have hresolved : envForMask jsonSeamSymbol [.ptr 1] (stagedMem w0 w1 w2 w3) 33 ≠
          none := by
        simp [envForMask_scanCaller_call w0 w1 w2 w3]
      rcases classifySeam_refines jsonSeamSymbol [.ptr 1] (stagedMem w0 w1 w2 w3) 33 with
        hunresolved | ⟨r', r, hr', hr, hret, _hle, _hnext, hmem⟩
      · exact absurd hunresolved hresolved
      · have ho4 : Beh (envForBodySym jsonSeamSymbol 10000 0 classify32Function)
            scanCaller [.int 64 w0, .int 64 w1, .int 64 w2, .int 64 w3] o := by
          simpa only [Beh, initState_scanCaller_cons w0 w1 w2 w3 rest] using ho
        have hot : o = .ret (some r'.ret) r'.mem :=
          (scanCaller_beh_of_call (envForBodySym jsonSeamSymbol 10000 0 classify32Function)
            w0 w1 w2 w3 r'.ret r'.mem r'.next hr' o).1 ho4
        refine ⟨.ret (some r.ret) r.mem, ?hsource, ?hagree⟩
        · have hsource' : Beh envForMask scanCaller
              [.int 64 w0, .int 64 w1, .int 64 w2, .int 64 w3]
              (.ret (some r.ret) r.mem) :=
            (scanCaller_beh_of_call envForMask w0 w1 w2 w3 r.ret r.mem r.next hr
              (.ret (some r.ret) r.mem)).2 rfl
          simpa only [Beh, initState_scanCaller_cons w0 w1 w2 w3 rest] using hsource'
        · rw [hot]
          refine ⟨congrArg some hret, ?hmem⟩
          intro a _
          exact hmem a (by
            simp only [ReserveFrame]
            omega)
  | _ =>
      exact ⟨o, (scanCaller_beh_eq _ o).1 ho, Outcome.agreesOutside_refl o _⟩

/-- The informative instance: for every four words, the caller's one outcome
under both selections is the mask of the bytes they stage, with the caller's
memory intact. -/
theorem replaceScanner_ret (w0 w1 w2 w3 : BitVec 64) :
    ∀ o, Beh (envForBodySym jsonSeamSymbol 10000 0 classify32Function)
        scanCaller [.int 64 w0, .int 64 w1, .int 64 w2, .int 64 w3] o ↔
      o = .ret (some (.int 32 (maskOfList (blockOf w0 w1 w2 w3))))
        (stagedMem w0 w1 w2 w3) := by
  intro o
  rw [scanCaller_beh_eq]
  exact scanCaller_beh w0 w1 w2 w3 o

/-! ### The negative control -/

/-- A straight-line run splits at a block boundary: a point whose second half
does not begin with a `phi`, so no leading run is cut in two.  The pending
bindings of the first half are installed at the split. -/
theorem denoteRun_append (calls : Calls) :
    ∀ (is js : List Instr) (pend : List (String × Value)) (s : State),
      startsWithPhi js = false →
      denoteRun calls pend (is ++ js) s =
        (denoteRun calls pend is s).bind (denoteCode calls js)
  | [], js, pend, s, hb => by
      simp only [List.nil_append, denoteRun, Option.bind_some]
      exact denoteRun_nil_pend hb
  | i :: is, js, pend, s, hb => by
      simp only [List.cons_append]
      by_cases hphi : i.isPhi = true
      · obtain ⟨d, ty, inc, rfl⟩ : ∃ d ty inc, i = .phi d ty inc := by
          cases i with
          | phi d ty inc => exact ⟨d, ty, inc, rfl⟩
          | _ => simp_all [Instr.isPhi]
        simp only [denoteRun]
        cases hsel : phiSelect s inc with
        | none => rfl
        | some v =>
            simp only [hsel]
            exact denoteRun_append calls is js (pend ++ [(d, v)]) s hb
      · have hi : i.isPhi = false := by
          cases i <;> simp_all [Instr.isPhi]
        simp only [denoteRun_cons_of hi]
        cases he : evalInstr calls (s.bindAll pend) i with
        | none => rfl
        | some s' => simp only []; exact denoteRun_append calls is js [] s' hb

/-- A straight-line sequence's effect composes. -/
theorem denoteCode_append (calls : Calls) (is js : List Instr) (s : State)
    (hb : startsWithPhi js = false) :
    denoteCode calls (is ++ js) s = (denoteCode calls is s).bind (denoteCode calls js) :=
  denoteRun_append calls is js [] s hb

/-- The complemented body's instruction, added after the classifier's. -/
def wrongMaskInstr : Instr :=
  .binop "%w" .xor 32 (.reg "%i23") (.imm (.int 32 (BitVec.ofInt 32 (-1))))

/-- The complemented body's state after its extra instruction. -/
def wrongMaskRun (s : State) (block : Block32) : State :=
  (classifyRun s block).bind "%w" (.int 32 (packed block ^^^ BitVec.ofInt 32 (-1)))

/-- The complemented body's instructions: the classifier's, then the
complement. -/
def wrongMaskInstrs : List Instr := classify32Instrs ++ [wrongMaskInstr]

/-- The complemented body's block. -/
def wrongMaskBody : Block :=
  { name := "bb", instrs := wrongMaskInstrs,
    term := .ret (.int 32) (some (.reg "%w")) }

/-- A non-void return evaluates its operand. -/
theorem execTerm_ret_int (s : State) (w : Nat) (v : Operand) :
    execTerm s (.ret (.int w) (some v)) =
      (match evalOperand s v with | some x => .ret (some x) s | none => .ub) := rfl

/-- The complemented body's one control step: the classifier's instructions,
then the complement, then the return. -/
theorem wrongMask_step (s : State) (block : Block32) (p : Nat)
    (harg : lookupName s.env argName = some (.ptr p))
    (hread : readBytes s.mem p 32 = some (List.ofFn block)) (hpc : s.pc = "bb") :
    step noCalls wrongMaskFunction s =
      .ret (some (.int 32 (packed block ^^^ BitVec.ofInt 32 (-1)))) (wrongMaskRun s block) := by
  have hfind : wrongMaskFunction.findBlock s.pc = some wrongMaskBody := by
    rw [hpc]
    show findBlockList wrongMaskFunction.blocks "bb" = some wrongMaskBody
    rw [show wrongMaskFunction.blocks = [wrongMaskBody] from rfl]
    simp [findBlockList, wrongMaskBody]
  have hsplit : wrongMaskInstrs = classify32Instrs ++ [wrongMaskInstr] := rfl
  have hbody : denoteCode noCalls wrongMaskInstrs s = some (wrongMaskRun s block) := by
    rw [hsplit, denoteCode_append]
    · rw [classify32_block noCalls s block p harg hread]
      simp only [wrongMaskInstr, wrongMaskRun, denoteCode, denoteRun, State.bindAll, evalInstr,
        evalOperand, lookupName_classifyRun, Const.toValue, Value.intToNat, evalBinopNat,
        evalBinop, Option.bind, State.bind]
      simp
    · rfl
  have hterm : execTerm (wrongMaskRun s block) wrongMaskBody.term =
      .ret (some (.int 32 (packed block ^^^ BitVec.ofInt 32 (-1)))) (wrongMaskRun s block) := by
    rw [show wrongMaskBody.term = .ret (.int 32) (some (.reg "%w")) from rfl]
    rw [execTerm_ret_int]
    simp [wrongMaskRun, State.bind, evalOperand]
  simp only [step, hfind]
  rw [show wrongMaskBody.instrs = wrongMaskInstrs from rfl]
  rw [hbody]
  exact hterm

/-- The complemented body's run from a state seeded with an arbitrary allocator:
it reads the block, returns the complement of the mask, and leaves the memory as
it found it. -/
theorem wrongMask_run (block : Block32) (mem : Mem) (p next : Nat)
    (hread : readBytes mem p 32 = some (List.ofFn block)) :
    runFuel noCalls 10000 wrongMaskFunction
        { env := (wrongMaskFunction.params.zip [.ptr p]).map fun q => (q.1.1, q.2)
          mem := mem, next := next, pc := wrongMaskFunction.entry?.getD "", pre := none } =
      some (.ret (some (.int 32 (packed block ^^^ BitVec.ofInt 32 (-1)))) mem) := by
  let s : State :=
    { env := (wrongMaskFunction.params.zip [.ptr p]).map fun q => (q.1.1, q.2)
      mem := mem, next := next, pc := wrongMaskFunction.entry?.getD "", pre := none }
  change runFuel noCalls 10000 wrongMaskFunction s =
    some (.ret (some (.int 32 (packed block ^^^ BitVec.ofInt 32 (-1)))) mem)
  have harg : lookupName s.env argName = some (.ptr p) := by
    simp [s, wrongMaskFunction, classify32Function, argName, List.map, List.zip, List.zipWith]
  have hpc : s.pc = "bb" := rfl
  simp only [runFuel, wrongMask_step s block p harg hread hpc]
  simp only [wrongMaskRun, State.bind, classifyRun]
  rfl

/-- A successful read of a written byte list at its own length. -/
theorem readBytes_writeBytes_same_of_length {m : Mem} {addr n : Nat} {bs : List UInt8}
    (h : bs.length = n) :
    readBytes (writeBytes m addr bs) addr n = some bs := by
  rw [← h]
  exact readBytes_writeBytes_same m bs

/-- A candidate that returns the complement of the reference mask is **not**
related to it: the relation's value clause is what refuses it. -/
theorem wrongMask_not_refines :
    ¬ CallRefinesWithin (envForBodySym jsonSeamSymbol 10000 0 wrongMaskFunction)
        envForMask jsonSeamSymbol (ReserveFrame 0) := by
  intro h
  let bs : List UInt8 := List.replicate 32 (0 : UInt8)
  let mem : Mem := writeBytes [] 0 bs
  have hlen : bs.length = 32 := by simp [bs]
  obtain ⟨block, hblock⟩ := exists_block_of_length hlen
  have hread : readBytes mem 0 32 = some bs :=
    readBytes_writeBytes_same_of_length (m := ([] : Mem)) (addr := 0) hlen
  have hreadBlock : readBytes mem 0 32 = some (List.ofFn block) := by
    rw [hread]
    rw [hblock]
  have hsrc : envForMask jsonSeamSymbol [.ptr 0] mem 1 =
      some { ret := .int 32 (maskOfList bs), mem := mem, next := 1 } := by
    simp only [envForMask, jsonSeamSymbol, hread, ↓reduceIte]
  have hcand : envForBodySym jsonSeamSymbol 10000 0 wrongMaskFunction jsonSeamSymbol
      [.ptr 0] mem 1 =
      some { ret := .int 32 (packed block ^^^ BitVec.ofInt 32 (-1)),
             mem := mem, next := 1 + 0 } := by
    simp only [envForBodySym, wrongMask_run block mem 0 1 hreadBlock, ↓reduceIte]
  rcases h [.ptr 0] mem 1 with hnone | ⟨r', r, hr', hr, hret, _hle, _hnext, _hmem⟩
  · rw [hsrc] at hnone
    cases hnone
  · have hr'val : r'.ret = (.int 32 (packed block ^^^ BitVec.ofInt 32 (-1)) : Value) := by
      have hh := congrArg (Option.map CallOutcome.ret) (hr'.symm.trans hcand)
      simpa using hh
    have hrval : r.ret = (.int 32 (maskOfList bs) : Value) := by
      have hh := congrArg (Option.map CallOutcome.ret) (hr.symm.trans hsrc)
      simpa using hh
    have e : (.int 32 (packed block ^^^ BitVec.ofInt 32 (-1)) : Value) =
        .int 32 (maskOfList bs) := by
      rw [← hr'val, ← hrval]
      exact hret
    injection e with _ hw
    rw [packed_eq_maskOf, maskOf, hblock] at hw
    have hzero : maskOfList bs = (0 : BitVec 32) := by decide
    rw [hzero] at hw
    exact absurd hw (by decide)

end LeanLLVM.Refinement.JsonSeam
