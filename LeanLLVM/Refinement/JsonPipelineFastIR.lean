/-
The fused mask passes as emitted, pinned.

`probes/install/ir/pipeline_fast.candidate.ll` is the emission of
`kernel/json/pipeline_fast.c` at the measured compiler line
(`-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
-falign-functions=64 -fno-discard-value-names`) plus `-fno-inline-functions`:
the two passes and their helpers are out of line, where the measured object
inlines them.  `capture-pipeline-fast.sh` records the derivation and the tokens
the normalisation removed; the body's instructions are the source's.

The two functions the fixture defines are the list-free pass (`pf_mask_core`,
three parameters after clang elides the unused `xp`/`nxp`/`xc`) and the list
pass (`pf_mask_list`, six parameters).  Each is thirteen blocks: the entry's
frame and carry clear, the full-block loop, the document-end ASCII/partial-block
tail, and the return.  The carry is the `%struct.s1_carry` alloca the parser
resolves through the declared layout `("s1_carry", 24)`; the fixture carries no
`%struct` definition.

## What the pin is

The parser runs on `String` primitives, which the kernel does not reduce, so the
pin is a set of `#guard`s on the parsed module: the function names in order, the
parameter registers, the block names, every allocation's type in text order, and
the call census (each helper's occurrence count and the list-only calls).  A
change to the fixture that the pins do not carry fails elaboration; a change to
a pin that the fixture does not carry fails too.

## The refinement, and where its rows are

The body statement is a `runFuel` refinement of `pf_mask_core`/`pf_mask_list`
against `JsonPipelineFastStage1`'s `passRun` at the same block list: the body's
`%ent` words are `specWords`, its returned word is the fused gate's verdict, and
the carry/`u8k` cells it keeps in its frame are `passRun`'s state.  The helper
calls the body makes (`s1f_escaped`, `pf_sw32_dn`, `s1f_prefix_xor`,
`kl_err_vec_ld`, `kl_tail_byte`, `leanllvm_json_escape_list`) are the rows'
callees: each must be bound in a `Calls` environment to the model
`JsonPipelineFastStage1` states.  The entry row is the frame and carry clear;
the loop rows are the per-block `passBlock` steps; the tail rows are the partial
block's `limMask` clamp and the document-end rule.
-/
import LeanLLVM.Parser

namespace LeanLLVM.Refinement.JsonPipelineFastIR

open LeanLLVM

/-- The fixture: the two passes, as committed. -/
def pfSrc : String :=
  include_str "../../probes/install/ir/pipeline_fast.candidate.ll"

/-- The parsed fixture, at the declared `%struct.s1_carry` extent. -/
def pfModule : Option Module :=
  match parseModuleWith [("s1_carry", 24)] pfSrc with
  | .ok m => some m
  | .error _ => none

/-- The list-free pass. -/
def pfCore : Option Function := pfModule.bind fun m => m.functions[0]?

/-- The list pass. -/
def pfList : Option Function := pfModule.bind fun m => m.functions[1]?

/-- The call targets a function names, in text order: both a bound `call` and a
`call void` are calls, because the census is the callee. -/
def pfCallTargets (f : Function) : List String :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .call _ _ callee _ => some callee
    | .callVoid callee _ => some callee
    | _ => none

/-- Every allocation instruction's type, in text order. -/
def pfAllocaTypes (f : Function) : List Ty :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .alloca _ ty _ => some ty
    | _ => none

/-- The number of calls to a symbol. -/
def pfCallCount (f : Function) (sym : String) : Nat :=
  (pfCallTargets f).count sym

/-! ### The pins -/

#guard pfModule.isSome

#guard (pfCore.map (·.name)) = some "pf_mask_core"
#guard (pfList.map (·.name)) = some "pf_mask_list"

#guard (pfCore.map (fun f => f.params.map (fun p => p.1)))
  = some ["%b", "%n", "%ent"]
#guard (pfList.map (fun f => f.params.map (fun p => p.1)))
  = some ["%b", "%n", "%ent", "%xp", "%nxp", "%xc"]

#guard (pfCore.map (fun f => f.blocks.map (fun b => b.name))) = some
  ["entry", "for.body.lr.ph", "for.cond.cleanup.loopexit", "for.cond.cleanup",
   "for.body", "if.then", "if.end", "if.then22", "if.then59", "if.end63.thread",
   "if.end63", "if.then70", "if.end76"]
#guard (pfList.map (fun f => f.blocks.map (fun b => b.name))) = some
  ["entry", "for.body.lr.ph", "for.cond.cleanup.loopexit", "for.cond.cleanup",
   "for.body", "if.then", "if.end", "if.then23", "if.then61", "if.end65.thread",
   "if.end65", "if.then72", "if.end78"]

#guard (pfCore.map pfAllocaTypes) = some
  [.int 32, .int 32, .int 32, .int 32, .int 32, .int 32, .int 32, .int 32,
   .struct "s1_carry" 24]
#guard (pfList.map pfAllocaTypes) = some
  [.int 32, .int 32, .int 32, .int 32, .int 32, .int 32, .int 32, .int 32,
   .struct "s1_carry" 24]

#guard (pfCore.map (·.retTy)) = some (.int 64)
#guard (pfList.map (·.retTy)) = some (.int 64)

-- The helper census, per pass.  `pf_sw32_dn` is called twice (one per 32-byte
-- half), `s1f_escaped` and `s1f_prefix_xor` once per mask block, `kl_err_vec_ld`
-- once per block the gate takes, and `kl_tail_byte` once at the document end.
#guard pfCore.map (fun f => pfCallCount f "pf_sw32_dn") = some 4
#guard pfCore.map (fun f => pfCallCount f "s1f_escaped") = some 2
#guard pfCore.map (fun f => pfCallCount f "s1f_prefix_xor") = some 2
#guard pfCore.map (fun f => pfCallCount f "kl_err_vec_ld") = some 2
#guard pfCore.map (fun f => pfCallCount f "kl_tail_byte") = some 1
#guard pfCore.map (fun f => pfCallCount f "leanllvm_json_escape_list") = some 0

#guard pfList.map (fun f => pfCallCount f "pf_sw32_dn") = some 4
#guard pfList.map (fun f => pfCallCount f "pf_ctl") = some 2
#guard pfList.map (fun f => pfCallCount f "leanllvm_json_escape_list") = some 2

-- The intrinsics both passes read, and nothing else: the ASCII probe and the
-- gate's two intrinsics per taken block, with the classifier's shuffles inlined
-- into the helpers.
#guard pfCore.map (fun f => pfCallCount f "llvm.x86.avx.ptestz.256") = some 4
#guard pfList.map (fun f => pfCallCount f "llvm.x86.avx.ptestz.256") = some 4

-- The frame is cleared to zero at the entry: one `memset` of the carry slot.
#guard pfCore.map (fun f => pfCallCount f "llvm.memset.p0.i64") = some 1
#guard pfList.map (fun f => pfCallCount f "llvm.memset.p0.i64") = some 1

end LeanLLVM.Refinement.JsonPipelineFastIR
