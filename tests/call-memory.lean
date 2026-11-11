/-
The call-memory scenarios: a callee's writes reach its caller, a pure callee
leaves the caller's state alone, and a module replacement is related only
outside the callee's footprint.

The programs are built here; the selection is the library's own installed
environment where one exists — `envFor` for CM2, `envForBody` for CM4 — and
scenario-built where the scenario needs a body the library does not provide:
`cmStore` for CM1, `envA` and `envB` for CM3.  The caller text is a `Function`
value, so each run is in process and deterministic; no compiler, proof checker,
service or network is reached.  A positive refinement is a theorem, and so is a
negative one: the relation quantifies over every argument list, memory and
allocator state, so a `#guard` can decide only a closed case.

Elaborated by `lake env lean tests/call-memory.lean`.
-/
import LeanLLVM

namespace CallMemory

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.SeamContext
open LeanLLVM.Refinement.CommaMaskLoop
open LeanLLVM.Refinement.CommaMaskIR

/-! ### The programs the scenarios run -/

/-- `%p = call ptr @seam(i64 %arg)`, `%v = load i64, ptr %p`, `ret i64 %v`. -/
def cmObserve : Function :=
  { name := "cm_observe", retTy := .int 64, params := [("%arg", .int 64)],
    blocks := [
      { name := "entry",
        instrs := [
          .call "%p" .ptr seamSymbol [(.int 64, .reg "%arg")],
          .load "%v" (.int 64) (.reg "%p") ],
        term := .ret (.int 64) (some (.reg "%v")) } ] }

/-- `alloca %buf i64`, `store %arg -> %buf`, `call %r = @seam(%arg)`,
`%out = load i64 %buf`, `ret %out`, with no store after the call. -/
def cmKeep : Function :=
  { name := "cm_keep", retTy := .int 64, params := [("%arg", .int 64)],
    blocks := [
      { name := "entry",
        instrs := [
          .alloca "%buf" (.int 64) 8,
          .store (.int 64) (.reg "%arg") (.reg "%buf"),
          .call "%r" (.int 64) seamSymbol [(.int 64, .reg "%arg")],
          .load "%out" (.int 64) (.reg "%buf") ],
        term := .ret (.int 64) (some (.reg "%out")) } ] }

/-- `cmKeep` with a second local allocated after the call: `alloca %tmp i64`,
store `0` at `%tmp`, then load `%buf`.  A callee that reset the allocator would
hand `%tmp` the address `%buf` occupies, and the store would change the value
the caller returns. -/
def cmKeepAlloc : Function :=
  { name := "cm_keep_alloc", retTy := .int 64, params := [("%arg", .int 64)],
    blocks := [
      { name := "entry",
        instrs := [
          .alloca "%buf" (.int 64) 8,
          .store (.int 64) (.reg "%arg") (.reg "%buf"),
          .call "%r" (.int 64) seamSymbol [(.int 64, .reg "%arg")],
          .alloca "%tmp" (.int 64) 8,
          .store (.int 64) (.imm (.int 64 0)) (.reg "%tmp"),
          .load "%out" (.int 64) (.reg "%buf") ],
        term := .ret (.int 64) (some (.reg "%out")) } ] }

/-! ### CM1 — a caller observes the store its callee left

The selection writes the eight little-endian bytes of `42` at address `1`,
advances the allocator to `9`, and returns the pointer to them. -/

def cmStore : Calls :=
  fun callee args mem _next =>
    if callee = seamSymbol then
      match args with
      | [.int 64 _] =>
          some { ret := .ptr 1, mem := writeBytes mem 1 (natToBytes 42 8), next := 9 }
      | _ => none
    else none

-- The caller returns the value it loaded through its callee's pointer, and the
-- memory it returns holds the bytes the callee stored there.
#guard
  match run cmStore cmObserve [.int 64 0] with
  | some (.ret (some (.int 64 v)) m) =>
      v = 42 ∧ readByte m 1 = some 42 ∧ readBytes m 1 8 = some (natToBytes 42 8)
  | _ => false

/-! ### CM2 — a pure callee leaves the caller's memory and allocator untouched

The identity selection is the library's `envFor`, which returns its argument and
leaves the caller's memory and allocator exactly as it found them.  Each caller
reads a slot it wrote before the call and nothing rewrites it, so the value it
returns is evidence about the call; the second caller allocates after the call,
so a callee that reset the allocator would alias its local onto the first. -/

-- The caller's own byte survives the call, at the address it stored it.
#guard
  match run (envFor (fun x => x)) cmKeep [.int 64 0x2A] with
  | some (.ret (some (.int 64 v)) m) => v = 0x2A ∧ readByte m 1 = some 0x2A
  | _ => false

-- The post-call allocation lands above the caller's byte, so the byte survives
-- and the caller returns it.
#guard
  match run (envFor (fun x => x)) cmKeepAlloc [.int 64 0x2A] with
  | some (.ret (some (.int 64 v)) _) => v = 0x2A
  | _ => false

/-! ### CM3 — the relation is sensitive to memory outside the frame

Each selection writes a different byte at the same address and resumes the
caller eight bytes above the base it was handed, so both reserve from the
caller's own allocator and the only difference between them is the byte at
`1`. -/

def envA : Calls :=
  fun callee args mem next =>
    if callee = seamSymbol then
      match args with
      | [.int 64 _] =>
          some { ret := .int 64 0, mem := writeBytes mem 1 (natToBytes 42 1), next := next + 8 }
      | _ => none
    else none

def envB : Calls :=
  fun callee args mem next =>
    if callee = seamSymbol then
      match args with
      | [.int 64 _] =>
          some { ret := .int 64 0, mem := writeBytes mem 1 (natToBytes 43 1), next := next + 8 }
      | _ => none
    else none

/-- `Band` is decidable: an application is decided by the arithmetic it
expands to. -/
instance bandDecidable (lo hi a : Nat) : Decidable (Band lo hi a) := by
  unfold Band
  infer_instance

/-- The two selections are related at `Band 1 3`: the same returned value, the
same allocator advance, and the only differing byte is at address `1`, inside
the band. -/
theorem cm3_relation :
    CallRefinesWithin envB envA seamSymbol (fun _ => Band 1 3) := by
  intro args mem next
  by_cases hargs : ∃ x : BitVec 64, args = [.int 64 x]
  · obtain ⟨x, rfl⟩ := hargs
    right
    refine
      ⟨{ ret := .int 64 0, mem := writeBytes mem 1 (natToBytes 43 1), next := next + 8 },
       { ret := .int 64 0, mem := writeBytes mem 1 (natToBytes 42 1), next := next + 8 },
       ?_, ?_, rfl, show next ≤ next + 8 from by omega, rfl, ?_⟩
    · simp [envB]
    · simp [envA]
    · intro a ha
      have hlt : a < 1 ∨ 1 + 1 ≤ a := by
        have hne : ¬ (1 ≤ a ∧ a < 3) := ha
        omega
      have h43 : readByte (writeBytes mem 1 (natToBytes 43 1)) a = readByte mem a :=
        readByte_writeBytes_outside mem (natToBytes 43 1)
          (by simpa [natToBytes_length] using hlt)
      have h42 : readByte (writeBytes mem 1 (natToBytes 42 1)) a = readByte mem a :=
        readByte_writeBytes_outside mem (natToBytes 42 1)
          (by simpa [natToBytes_length] using hlt)
      change readByte (writeBytes mem 1 (natToBytes 43 1)) a =
        readByte (writeBytes mem 1 (natToBytes 42 1)) a
      rw [h43, h42]
  · left
    cases args with
    | nil => simp [envA]
    | cons v rest =>
      cases rest with
      | cons w rest => simp [envA]
      | nil =>
        cases v with
        | int width bits =>
          by_cases hw : width = 64
          · subst hw
            exfalso
            exact hargs ⟨bits, rfl⟩
          · simp [envA, hw]
        | ptr addr => simp [envA]
        | vec n w lanes => simp [envA]

-- The separating address is `1`, which `Band 2 3` excludes, and the two
-- memories really do differ there.
#guard
  match envA seamSymbol [.int 64 0] [] 1, envB seamSymbol [.int 64 0] [] 1 with
  | some rA, some rB => ¬ Band 2 3 1 ∧ readByte rA.mem 1 ≠ readByte rB.mem 1
  | _, _ => false

/-! ### CM4 — the frame is load-bearing in both directions

`callerFunction` makes one call and returns its value: it executes no load, so
the two selections are related at the band the loop's two locals occupy and
refused below it. -/

/-- The caller is related at `Band 1 17`, the band `loopFunction`'s allocations
cover at base `1`. -/
theorem cm4_admitted (x : BitVec 64) :
    RefinesWithinAcross (envForBody 10000 16 loopFunction)
      (envForBody 10000 16 candidateFunction)
      callerFunction callerFunction (Band 1 17) := by
  simpa [loopFrame_eq] using caller_replaces_loop_within x

/-- The caller is refused at `Band 17 25`: the loop leaves a byte at address `1`
and the candidate leaves the incoming memory unchanged, so agreement outside a
band that excludes address `1` is false.  The proof names the inequality
`readByte memL 1 ≠ none` and pins no byte value. -/
theorem cm4_refused (x : BitVec 64) :
    ¬ RefinesWithinAcross (envForBody 10000 16 loopFunction)
      (envForBody 10000 16 candidateFunction)
      callerFunction callerFunction (Band 17 25) := by
  intro h
  obtain ⟨memL, _hband, hL19⟩ := loop_run_at_base x 1 []
  have hL : runFuel noCalls 10000 loopFunction (initState loopFunction [.int 64 x]) =
      some (.ret (some (.int 64 (spec x))) memL) := by
    simpa [initState] using (runFuel_mono_le (by decide : 19 ≤ 10000) hL19)
  obtain ⟨memC, hC, hCnil⟩ := candidate_run_mem_eq x [] 1
  have hLrun : runFuel noCalls 10000 loopFunction
      { env := (loopFunction.params.zip [.int 64 x]).map fun p => (p.1.1, p.2)
        mem := [], next := 1, pc := loopFunction.entry?.getD "", pre := none } =
      some (.ret (some (.int 64 (spec x))) memL) := by
    simpa [initState, loopFunction] using hL
  have hLe : envForBody 10000 16 loopFunction seamSymbol [.int 64 x] [] 1 =
      some { ret := .int 64 (spec x), mem := memL, next := 17 } := by
    simp [envForBody, hLrun]
  have hCrun : runFuel noCalls 10000 candidateFunction
      { env := (candidateFunction.params.zip [.int 64 x]).map fun p => (p.1.1, p.2)
        mem := [], next := 1, pc := candidateFunction.entry?.getD "", pre := none } =
      some (.ret (some (.int 64 (byteLoop x))) memC) := by
    simpa [initState, candidateFunction] using hC
  have hCe : envForBody 10000 16 candidateFunction seamSymbol [.int 64 x] [] 1 =
      some { ret := .int 64 (byteLoop x), mem := memC, next := 17 } := by
    simp [envForBody, hCrun]
  have hLbeh : Beh (envForBody 10000 16 loopFunction) callerFunction [.int 64 x]
      (.ret (some (.int 64 (spec x))) memL) :=
    (caller_beh_body 10000 16 loopFunction x hLe _).mpr rfl
  obtain ⟨o', ho', hagree⟩ := h [.int 64 x] _ hLbeh
  have ho'eq : o' = .ret (some (.int 64 (byteLoop x))) memC :=
    (caller_beh_body 10000 16 candidateFunction x hCe o').mp ho'
  subst ho'eq
  have hmem : AgreesOutsideMem memL memC (Band 17 25) := hagree.2
  have h1 : readByte memL 1 = readByte memC 1 := hmem 1 (by decide)
  subst hCnil
  obtain ⟨mem1, hrun1, hbyte1⟩ := loop_mem_at_one x
  have hr : runFuel noCalls 10000 loopFunction (initState loopFunction [.int 64 x]) =
      some (.ret (some (.int 64 (spec x))) mem1) := by
    simpa [run] using hrun1
  have hmems : mem1 = memL := by
    have ho := Option.some.inj (hr.symm.trans hL)
    injection ho with _ hmemEq
  subst hmems
  rw [h1] at hbyte1
  exact hbyte1 rfl

/-! ### CM5 — the caller theorem consumes the loop's framed statement

Each proof term is printed one level deep, which is the depth at which the
consumed constant is visible. -/

#print loop_seam_within_refines

#print caller_replaces_loop_within

end CallMemory
