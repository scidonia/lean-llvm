# lean-llvm

Lean 4 development of a certified LLVM transformation and refinement framework.
`DESIGN.md` states the refinement relation and the modelling choices; this file
records how to build and what a change must prove.

## Toolchain

Lean `v4.35.0` and LLVM tools come from the flake.  Run every toolchain
command through the dev shell so the environment belongs to this checkout:

```bash
nix develop -c lake build
nix develop -c lake build LeanLLVMTest
nix develop -c lake exe leanllvm tests/constfold.ll
```

`llvm-as`, `llvm-dis`, `opt`, `llc` and `clang` are provided by the shell.

Run Lean and Lake under a **memory ceiling**, so a runaway elaboration dies
inside its own cgroup instead of taking the session or the machine with it:

```bash
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c lake build
```

The ceiling is per invocation and inherited by everything the shell starts.
A build killed by it is a signal that the file it was elaborating needs
splitting or its `maxHeartbeats` raising — not a reason to run the same
command without the ceiling.

The default targets are the `leanllvm` executable and the `ITree` library, so
`lake build` covers `LeanLLVM` (through the executable) and the generic tree
library.  The generic library depends on `leanprover-community/mathlib4` at the
revision pinned in `lakefile.toml`, resolved into `.lake/packages`; mathlib's
oleans must be present before the tree modules elaborate, so a cold checkout pays
for a mathlib build unless its prebuilt cache is already in place.  The mathlib
revision, `lean-toolchain` and the flake's Lean source are one unit: moving one
needs the other two to match.

## Layout

- `LeanLLVM/` is the library: syntax, semantics, parser, printer, refinement,
  the pass framework, and the passes.
- `LeanLLVM/Vellum/` is the refinement layer: `Contract`, `Refines` /
  `SemRefines`, `Correct`, the contextual theorems, the comma-mask instance,
  the emitted-IR bridge (`CommaMaskIR`), the IR-level caller (`SeamContext`),
  the two-environment contextual replacement (`ModuleRefinement`:
  `RefinesWithinAcross`, `replaceFunction_sound`, `memCaller_replaces_loop`),
  the stage-1 depth counter (`DepthCountRefine`: `depth_count_refines` for the
  emitted `@depth_count`, over its stripped text in `tests/v16/depth_count.ll`),
  and the JSON classifier's three: `JsonScanSpec` writes the classifier's
  interface in the model's vocabulary — the delimiter predicate, the packed words,
  the in-string and candidate masks, and the carry — with the candidate mask's
  unescaped-quote reading recorded as the specification decision, the bridges to
  `ScanBlock`'s fold and to `ScanBody`'s byte rule's `inside` field proved, the
  identification with `ScanWindow`'s `windowOf`/`carryAt` proved **at the projection**
  `BodyState.classPart := ⟨inside, oddRun⟩` (the classifier has no UTF-8 field, so the
  theorem is about those two fields, not about `BodyState` equality) on a full window
  with no stop — the quote, backslash and structural mask equalities there, the
  closing lane empty on both sides exactly when the window stops nowhere, the same bit
  at a closing stop's own lane, and the carry — the closing-lane comparison under
  `NoBackslashOutside` and the carry under `ContinuesBefore` and
  `NoBackslashOutside`, each with its counterexample,
  and the post-stop divergence stated as a divergence (`classCarryAt_succ_of_stop`,
  `classCarryAt_succ_closed`) rather than a caveat — and the identification with
  the kernel's registers proved for the extracted mask unit and owed for any other
  emission; `JsonClassifyIR` relates the emitted
  classifier body to the block layer's mask (`scannerLLVM_refines`, over
  `probes/install/ir/json-classify.candidate.ll`); and `JsonSeam` states the
  reference selection, the installed body's selection, and the framed
  replacement through a staging caller (`classifySeam_refines`,
  `replaceScanner_sound`, `replaceScanner_ret`, over
  `probes/install/ir/json-caller.ll`); and the stage-1 mask unit's own bridge:
  `JsonS1MasksIR` pins `probes/install/ir/json-s1-masks.candidate.ll` by
  `#guard`, and `JsonS1MasksSteps` proves `s1_masks_refines` over that body — the
  six masks `JsonScanSpec` specifies and the outgoing carry, at the body's own
  registers, under an environment binding its five intrinsic calls — with the six
  per-mask identities and the totality companion `s1_masks_undefined_of_no_read`
  (a block absent across the 64 bytes the body reads is `ub`).  `Pclmul` is the
  classifier's arithmetic
  underneath those three: `clmul` as the truncated GF(2) polynomial product
  written as a fold of shifted XORs, the all-ones instance as the prefix parity
  (`clmul_allOnes_self`) and its uniqueness (`clmul_allOnes_unique`), and the two
  mask identities — `inStringMask_eq_clmul` over a window and
  `specInString64_eq_clmul` over a sixty-four-byte block — with the outgoing carry
  `specInString64_outgoing_carry`, all stated over `JsonScanSpec`'s own masks.
  `BitLanes` models the bit intrinsics the two units' kernels use besides
  `pclmulqdq` — `pext`, `pdep` and `ctlz`, and `ctpop`/`cttz` for the entry
  kernels, five lane definitions over six intrinsic spellings — in lane
  vocabulary, with `rank` and the two alignment facts that pair a mask's set
  lanes with their positions (`rank_setLanes_getElem`,
  `setLanes_getElem?_rank`), the Galois connection `pdep_pext`/`pext_pdep`,
  `ctlz (~~~m) = trailingRun m`, and the `ctpop`/`cttz` readings of a mask's set
  lanes a position emitter uses.  `QuoteDerive`
  proves the kernel's escape arithmetic: `kernelEscape_eq` — the kernel's
  `pext`/`pdep` scatter is the parity mask on the lanes that are not backslashes —
  `kernelQuote64` — the kernel's `%qmc2 = %qrawc2 & ~%escc2` over a sixty-four-lane
  block *is* `JsonScanSpec`'s `specQuote64` — and `ppn64`, the same for the outgoing
  parity `%ppnc2` against the `classStep` fold's `oddRun`.  That derivation carries
  `st.oddRun = (runOpen && ppar)` as a hypothesis, and both sides keep it rather
  than being restricted by it: `nextParity_and_not_top` and
  `nextParity_ne_zero_imp_open` confine the kernel's parity to its top lane, while
  `classStep_oddRun_gated`, `specCarry_hypothesis` and `classState_self_open` read
  the specification's parity as its own run-open bit.  Its docstring records what it
  does not prove: the sequence is a **hand transcription** of `tests/v16/ci2.ll`, no
  fixture of that file is `include_str`'d and no AST is pinned, so no theorem reaches
  `@ci2`; the `i1`-vector bitcast and the low-then-high join are the conventions the
  transcription reads, not theorems about the instructions; and any relation to the
  emitted IR is owed here for `@ci2` — as it is in `Pclmul` — while the extracted
  stage-1 mask unit's body is related to these definitions by `JsonS1MasksSteps`.
  The entry positions unit is the second unit's chain: `JsonEntSpec` writes the
  entry stream's specification out of `JsonScanSpec`'s masks — `specScalar64` as
  the complement of four of them, its run starts `scalarStarts64`, the joined
  `entryMask64`, `structuralOnly64` for the `S1F_GRAIN=1` granularity the measured
  build does not select, the `lim` tail `limMask`, the positions read
  `positionsOf`, and the `pos8Row` table row; `JsonEntryIR` pins both bodies of
  `probes/install/ir/json-entry.candidate.ll` by `#guard`, binds their intrinsics
  in `entryCalls`, gives the rewritten table read an address so no clause depends
  on a global, and proves the tail statement `entry_tail_eq`; `JsonEntrySteps`
  proves `entry_pos8_refines` — the returned cursor, the words below it read as
  the model's positions, and every byte outside the span the body's stores reach
  unchanged — and `JsonB8Steps` proves `entry_b8_refines`, the two kernels'
  agreement `entry_pos8_b8_agree` and B8's totality companion
  `entry_b8_undefined_of_no_read`, which are the statements the block layer asks
  for.
  The theorems the refinement claims rest on are pinned in
  `LeanLLVMTest/Vellum.lean`, each at the ceiling `[propext, Quot.sound]` or with a
  `Classical.choice` carrier the pin names — the three `private` numeral lemmas of
  `BitLanes` cannot be named from another file — each choice-carrying `BitVec`/`List`
  lemma replaced by a local proof.  The pins are the instrument and not a formality:
  **a proof term that picks up a carrier no pin names** shows in no build, no warning
  and no diff.  `JsonScanSpec`'s bridge had exactly one,
  closed by `simp` deciding a concrete `UInt8` comparison inside a proposition-valued
  definition; it was caught by `#print axioms` on the declaration and fixed by
  `unfold`/`decide` and re-probing every theorem in the module.
- `LeanLLVM/JSON/` is the byte-level JSON development: the independent
  semantics (`Spec`), scanner (`Scan`), parser (`Parse`), tape (`Tape`) and
  their correctness modules; the block layer `ScanBlock` — `maskOfList`,
  `maskOf`, `scanBlock` and `scanBlock_correct`, which reads the mask per lane
  against the scalar transition and confines `ok` to a full 32-byte block; and
  the stateful scanner model above both chains: `ScanBody` is the single
  `BodyState` carry (in-string flag, escape-run parity and pending UTF-8) and
  the byte rule, `ScanWindow` the window fold and the masks it reports,
  `ScanString` the window-driven scan and the tail, and `ScanBlocks`
  `scan_simd_refines_scalar`, the whole-scan statement relating that scan to
  the parser's own string scanner.  The parser imports none of the four:
  outside the model modules themselves, `LeanLLVM/JSON.lean` is the only
  importer, and it imports all four.
- `ITree.lean` and `ITree/` are a second Lake library, `ITree`: the generic
  interaction tree.  `ITree/Core` is the public tree API, `ITree/Coinduction`
  the parameterised-fixpoint layer, `ITree/IEq` exact equality,
  `ITree/Monad` the lawful functor/monad instances, `ITree/TauClosure` the
  finite/infinite delay object, `ITree/MonadIter` the ported iterator and the
  seeded guarded recursion `mfix` with its equations and positive-delay
  witnesses, and
  `ITree/EffectAlgebra` the tree-valued handler with its directly guarded
  interpreter; `ITree/Effect` is the separate one-step handler with a computable
  fold.  No module here imports a `LeanLLVM` module.  `ITree/README.md` records
  the public surface, both interpreters, the single mathlib adapter and the
  upstream provenance.
- `LeanLLVM/ITree/` is the LLVM instantiation of that library: `Interpret` is
  the fuel semantics as an `Ev` tree, `MemoryEffect` folds `Ev` into an
  `ObsEv` handler so memory becomes an effect, `Simtt` the directed relation on
  the resulting bare handled trees, `LoopRule` the framed loop rule with its
  postcondition weakening, handler jump-delay and decreasing-measure facts,
  `Bridge` the correspondence and elimination against a completed run, and
  `LoopInstance` the rule's two instances: a visibly recurring call tree and the
  comma-mask loop/candidate pair.  `LeanLLVM.lean` imports it after the Vellum
  modules, so `LeanLLVMTest/` reaches it through the same entrypoint as the rest
  of `LeanLLVM`.  `LeanLLVM/ITree/README.md` records the handler, the relation,
  the rule and the open obligations.
- `LeanLLVMTest/` is the check library.  It imports `LeanLLVM` from outside, so
  it sees exactly the public interface, and holds `#guard` checks,
  `#guard_msgs` pins, and small theorems.
- `reference/vellvm/` is vendored VeLLVM source for study.  It is not built,
  linted or edited.
- `tests/` holds textual IR exercised by the driver, and executable scenarios of
  user-facing routes: `m4-loop-gate.sh` drives the installer selector with a
  manifest that binds no loop theorem and no loop certificate, and asserts that
  such a request fails closed and that the baseline is installed instead;
  `m4-loop-install-gate.sh` drives the same selector against a manifest that
  does bind the loop's theorem and certificate, and asserts that a matching one
  installs the loop, that a certificate naming another unit's theorem or another
  unit's object hash is refused, and that a non-strict mismatch falls back to
  the baseline; `m4-depth-install-gate.sh` does the same for the depth counter,
  adding another unit's contract to the wrong-name refusals, and
  `depth-count/check.sh` compares the installed depth object, rebuilt from
  `tests/v16/depth_count.ll`, against `depthSpec` over an index-array corpus
  with a tampered expectation and a defect object as controls;
  `m3-certificate-gate.sh` drives the same
  selector against a certificate with one changed field, an absent certificate
  and a structurally malformed one, and asserts strict refusal and non-strict
  baseline fallback; `m4-loop-emission.sh` drives the fixture-capture
  route and the driver's command line, and asserts that the loop fixture is
  regenerated from the Lean emission and that a function header carrying an
  unmodelled attribute is refused.  The installer scenarios build their
  manifest and tool shims in a private temporary directory: they reach no
  compiler, proof checker, network or external service.  Three further routes
  exercise the JSON parser: `json-api.lean` and `json-tape.lean` are `#guard`
  programs over the public entry point -- accepted documents with their decoded
  values and their tape's input, refusals naming their reason, limit outcomes
  reported as themselves, and tapes whose spans do and do not name their
  tokens -- while `tests/json/check.sh` runs the built `leanllvm-json` over
  `tests/json/corpus` against the hand-written `tests/json/manifest.tsv` and
  asserts that a tampered expectation is a mismatch.  The JSON classifier
  has its own two: `tests/json-classify.lean` with
  `tests/json-classify.contract.md` exercises the block layer, the emitted body
  and the seam under the semantics, and `tests/json-classify/check.sh` compares
  the installed object — rebuilt from the committed fixture, `sha256` recorded
  in its transcript — against `leanllvm-json-classify` over every 32-byte
  window of the corpus and a mixed block, with a defect object and a tampered
  expectation as its controls.  Its object arm stages each window in a
  32-byte-aligned buffer, so it claims agreement on aligned windows only.
  The stage-1 mask unit has two routes of its own: `tests/json-s1-masks.lean`
  asserts the six masks and the carry of a mixed block under three carry states,
  that no byte outside the two slots moved, and the three clause witnesses; and
  `tests/json-s1-masks/check.sh` compares the installed object — compiled from
  `kernel/json/s1_block.c` and called through `probes/json/s1_masks_driver.c`,
  every window staged at offset 1 of a 96-byte buffer so the object is called
  misaligned — against the Lean body over the corpus and the three generated arms
  (byte, class alphabet, fixed-seed random), with a defect object and a tampered
  expectation as its controls.  It also regenerates the fixture from that source
  and byte-compares it; a difference is a setup failure, not an assertion result.
  The entry positions unit has two routes of its own: `tests/json-entry.lean`
  holds the fixture pin, the positions and two-stream assertions over a mixed
  block, and the clause witnesses, every observation a `#guard`; and
  `tests/json-entry/check.sh` makes two actors agree row for row — the pinned
  ASTs, run by `leanllvm-json-entry` under the semantics, and the installed
  object, compiled from `kernel/json/entry.c` and called through
  `probes/json/entry_driver.c` — over a corpus whose mask streams are derived from
  committed JSON documents' block bytes and six generated arms (one-lane,
  one-byte, fixed-seed random, empty, full, and one stream longer than a caller
  chunk), asserting the word at the cursor plus eight on every row as the
  body's stop sentinel, with a defect object per kernel and a tampered
  expectation as its controls.
  One more check sits beside those routes: `tests/json-import-boundary.sh`
  filters the actual `import` declarations of `LeanLLVM/JSON/*.lean` and
  asserts that `Parse.lean` imports exactly `Spec`, `Scan` and `Tape`, that
  `ScanBlock.lean` imports `Bytes` alone, that no module of the parser's chain
  names the block layer or the model in an `import` line, and that the four
  model modules are imported only by each other and by `LeanLLVM/JSON.lean`.
  Every detector runs on an in-memory sample it must catch — and, where the
  corpus allows, on a file it must catch — before any absence is asserted.
  Run it with `nix develop -c bash tests/json-import-boundary.sh`.
  `probes/install/ir/capture-json.sh` regenerates the classifier fixture and
  records its invocation and stripped items, and `lake exe leanllvm-json-emit`
  prints the caller fixture.  Each route carries a
  staged cut recorded in `docs/json-route-evidence.md`: the cut is a runtime
  override in a throwaway copy, never an edit to a definition that carries a
  proof, because such an edit falsifies the proof and the route then stops at
  import rather than at an assertion.  The tape route's red is a reachability
  red: it shows the scenario's accept path depends on the decoder's positions,
  not that the span refusals are sensitive — their sensitivity rests on their
  pairing with the affirmative controls and on `tape_valid`, and is not
  claimed by a cut.
- `kernel/json/` holds the two extracted units of the measured SIMD JSON
  stage 1 — `s1_block.c`, the classification mask unit, and `entry.c`, the entry
  positions unit — each with its own ABI, its own specification in
  `LeanLLVM/Vellum/`, its own identity arms and its own route.  Neither is the
  pipeline, and `kernel/json/measured/` is read-only reference that the identity
  and bench scripts read and no `lake` target builds.  `kernel/json/README.md`
  records each unit's entity list, deletion list, boundary and limits.
- `docs/` holds the design notes and evidence records: `contract.md` and
  `capabilities.md` for the trust ledger, `json-route-evidence.md` for the
  staged cuts, and `json-pipeline-performance.md`, which records the measured
  performance of a native SIMD JSON pipeline against simdjson.  The measured
  pipeline is a scratch implementation **not in this tree**: the note records
  observed ratios and the shapes refuted at measured cost, and no theorem,
  contract or axiom pin covers the code those numbers came from.  Two units of
  that pipeline are here — the classification mask unit and the entry positions
  unit named above — each pinned and proved (`s1_masks_refines`,
  `entry_pos8_refines`, `entry_b8_refines`); the note's ratios are measurements
  of the scratch build and are not claims about those units.

## What a change must satisfy

- No `sorry`, no `admit`, no `native_decide`.
- A transformation is not done until it has a `Pass.Sound` theorem.  The build
  enforces that the theorem typechecks; a test is not a substitute.
- Every theorem that claims soundness should have its axiom footprint pinned in
  `LeanLLVMTest/` with `#guard_msgs in #print axioms ...` once it is stable.
  The generic layer pins the same way in `tests/itree-import.lean`; its ceiling
  is the carrier's own footprint (`PFunctor.M.dest` already carries
  `Classical.choice`), so a generic `rfl` lemma may report it too.
- The parser and printer are part of the contract: round-trip checks in
  `LeanLLVMTest/Core.lean` must pass, and emitted IR must assemble with
  `llvm-as`.  A fixture read through `include_str` is not a `lake build` input,
  so elaborate its proof module from source after changing it; keep the mutation
  that shows the pin bites (`probes/install/check.sh` does this for the candidate
  and loop fixtures).  A fixture whose portable form is produced by the
  optimiser is emitted at `-O2` with its flags and target recorded:
  `json-classify.candidate.ll` is `-O2 -mavx2`, because instcombine folds the
  tab and newline comparisons into a range test and that form is what the proof
  analyses, and `probes/install/ir/capture-json.sh` records the invocation and
  every piece of syntax stripped before the parser sees it.
- `phi` is part of the modelled fragment: `Instr.phi` carries its type and its
  labelled incoming list, `State` carries the predecessor a jump writes, and a
  `phi` whose list omits the actual predecessor is `ub`.  The additive claim is
  a theorem, not an assertion: `runFuel_init_setPre` (and its step and relational
  forms) says a `phi`-free function's run is unchanged whatever predecessor the
  state carries, pinned in `LeanLLVMTest/Core.lean` with the rest of the
  footprint.  Its conformance evidence is `tests/phi-fragment.lean` (the paired
  edge-timing evaluation, three predecessors, an entry-block `phi`, a missing
  predecessor and the exercised non-interference instance) and its differential
  observation is `tests/phi-differential.sh`, which compares `clang`'s answers
  with the model's on the same files and is an observation, not a proof.
- The parser refuses the surfaces it checks, with a message naming the
  construct: unmodelled instructions, block structure, and a function
  definition's header -- a return attribute before the return type and a
  function attribute after the parameter list are refused
  (`tests/m4-loop-emission.sh --return-attr`, `--function-attr`).  Do not
  silently approximate an unmodelled construct on those surfaces.  A `declare`
  header is not checked: its parameter list is read up to the closing `)` and
  the rest of the line is ignored, so unmodelled declaration tokens can be
  accepted and dropped.  Do not claim total attribute rejection.
- Five surfaces are accepted rather than refused, and each has its paired check
  in `LeanLLVMTest/Core.lean`.  Four are dropped because the model has nothing
  for them to affect: a definition's linkage, visibility and calling convention
  (no linkage or calling-convention semantics — the `Calls` environment decides
  which definition answers and how the call is made), `icmp`'s `samesign` (the
  modelled predicate is the plain one and the flag can only exclude inputs, so
  dropping it widens), a call's `tail` marker (no ABI, stack or frame), and a
  call written without a destination (it binds nothing).  The fifth, a call's
  written callee function type, is read and checked positionally against the
  argument list (a final `...` admits further arguments; a disagreement, a
  non-final `...` or an unreadable type is refused by name) and then dropped,
  because the callee is a symbol the environment resolves and the AST has no
  field for a type.  For the four dropped surfaces the pair is: the construct
  parses to the AST the same program without it parses to, and the program runs
  to the same answer.  For the written callee type the pair is the same AST and
  the same run, plus the refusal of a disagreeing type.  A new accepted surface
  needs the same pair and the reason written where the decision is made.
- A vector constant has one accepted spelling beside its literals:
  `zeroinitializer` at a vector type is the splat of zero, which is that value
  exactly, so it parses to the AST the splat spelling does and runs to the same
  answer (`zeroInitializerSample`/`zeroSplatSample` in
  `LeanLLVMTest/Core.lean`, and the run pair in `tests/vector-lanes.lean`).  The
  lane-list literal and the lane accesses `extractelement`/`insertelement` are
  modelled, not accepted-and-dropped.  An index outside the vector's lane range
  is `ub`: LLVM calls it poison, and the model has no poison — the same reading
  `Const.toValue` gives a `poison` literal — so the accepting case and the
  refusal are stated as theorems (`evalInstr_extractelement`,
  `evalInstr_extractelement_out_of_range`, and the `insertelement` pair) and
  pinned in `LeanLLVMTest/Core.lean`.  `tests/vector-lanes.lean` is the scenario:
  a lane read returns that lane and an out-of-range index is `ub`, with the lane
  values chosen so a read of another lane, or of zero, fails one of the pair.
- A vector form is modelled only where a body uses it, and each is admitted
  beside its nearest unmodelled neighbour, refused by name: `shufflevector` with
  a defined mask naming lanes below `2n` (a mask entry at or past `2n`, or one
  written `undef`/`poison`, is refused); a vector `store` at integer lanes —
  `store <n x iW>` whose total width is whole bytes (`n * w % 8 = 0`, the mask
  store being that rule at `w = 1`) — where `store <5 x i1>` and `store
  <3 x i2>` are refused, and a value operand the function defines at another
  type than the written one is refused by name while an undefined register has
  no type, stays accepted and is `ub` when read; a non-mask vector `bitcast` at
  equal total width, where an unequal width is refused; vector `lshr`, which the stage-1
  fixture emits twice (`lshr <16 x i16> …, splat (i16 4)` reading `%12` and
  `%22`, the high-nibble extraction), and vector `shl` with it — the two
  directions are one operation, and no tracked `.ll` emits a vector `shl`, so
  that side is exercised as an accepted control in `tests/vector-s1.lean`
  (accepted, printed, re-parsed and evaluated) and in `tests/json-s1-parser.lean`
  — where a vector `ashr` is refused; a vector `load` at integer lanes whose
  total width is whole bytes; and the eight intrinsic spellings the two units
  call —
  `llvm.x86.avx2.pshuf.b` at two arguments, `llvm.x86.pclmulqdq` at immediate 0,
  `llvm.x86.bmi.pext.64`, `llvm.x86.bmi.pdep.64`, `llvm.ctlz.i64` with the
  non-poison flag, `llvm.ctpop.i32`, `llvm.ctpop.i64`, and `llvm.cttz.i64` at
  both flag values — each validated at symbol, arity, type and immediate, with
  its neighbouring spelling refused.  The two `cttz` flags are not symmetric:
  `i1 false` is exact at the zero word, and `i1 true` is admitted because the
  entry claims read no lane the poison can reach, the bound stated once in
  `LeanLLVM/Vellum/BitLanes.lean`; `ctlz … i1 true` has no such bound and stays
  refused.  `umin`/`umax` stay refused: the emission
  contains none.  `tests/vector-s1.lean` checks every acceptance and its refusal
  in one run, `tests/vector-entry.lean` does the same for the widened store and
  the entry intrinsics, and `probes/install/ir/json-s1-masks.candidate.ll` is the
  fixture that uses every stage-1 form except a vector `shl`, which appears in no
  tracked `.ll`; `probes/install/ir/json-entry.candidate.ll` is the entry
  kernels' fixture.
- An installation certificate is data, not source.
  `probes/install/InstallCertificate.lean` derives it from the imported proof
  graph rebuilt from current project source, from a freshly source-elaborated
  `CommaMaskIR` (and, for the loop, a `CommaMaskLoop` re-elaborated after it,
  since it imports `CommaMaskIR`, and for the depth counter a
  `DepthCountRefine` re-elaborated from source), and from the object, fixture
  and marker paths
  the manifest names; it checks the statement of the theorem covering the
  requested unit — `IR_refines` for the candidate and the baseline,
  `loop_refines_candidate_within` for the loop, which the loop's certificate
  names in place of `IR_refines`, and `depth_count_refines` for the depth
  counter, whose certificate names the propositional boundary `depthContract`
  (the theorem's own hypothesis set and conclusion) instead of the pure
  `commaContract` — the contract link and
  the axiom footprint in the loaded environment and refuses a stale proof
  module whose pinned fixtures differ from the files it hashes.
  `probes/install/select.sh` parses the certificate with a closed grammar,
  compares each field with the input it names, and reproduces the certificate
  byte for byte before linking. The depth unit is built from
  `tests/v16/depth_count.ll` at the same `clang -c` flags as the other units,
  and its caller is the corpus driver `probes/install/depth_driver.c` rather
  than the one-word comma seam. Never `source` a certificate, never accept a
  supplied theorem, axiom set or target as proof, and keep certificate files
  out of compiled units.
- `probes/install/build.sh`, the app build and the selector serialize the
  proof-module rebuilds and the certificate producers under the
  `.lake/install-certificate.lock` directory, created atomically by `mkdir`.
  The install and app builders hold it through their
  final manifest publication, and the selector holds it from before the
  manifest is sourced through the link and selection record.  Not obtaining the
  lock refuses before source elaboration or any published-input read; a lock
  directory
  left behind by a crashed run is removed only after verifying that no owner is
  running. Lake warm-up builds and the fixture emitter are writers too: run them
  through `probes/install/lake-locked.sh` rather than a bare `lake build` or
  `lake exe`, which take the same lock for that command only. Do not run a
  concurrent `lake build` that bypasses the wrapper. `probes/install/check.sh`
  and `probes/app/check.sh` are the end-to-end routes;
  `probes/install/build.sh` must run before reading the manifest or the
  certificates it publishes.
- The 64-bit seam identities are kernel-checked in
  `LeanLLVM/Vellum/CommaMaskKernel.lean` by a byte-lane argument.  Do not
  reintroduce `bv_decide`, `native_decide`, `sorry` or `admit`; the pins in
  `LeanLLVMTest/Vellum.lean` must stay at the standard axiom footprint.
- Checks are behavioural where behaviour is observable: parse a program, run it,
  run the pass, compare.  Avoid tests that merely restate a definition.
- A mathematical obligation — a refinement, a framing law, a loop rule — is
  discharged by a theorem, its axiom pin, and an adversarial example that fails
  (`LeanLLVMTest/Vellum.lean` has both the loop's framed statement and a write
  outside the frame that it refuses).  A user-facing route gets an executable
  scenario instead: `tests/m4-loop-gate.sh` drives `probes/install/select.sh`
  with no loop theorem or certificate bound and asserts refusal and fallback,
  and `tests/m4-loop-install-gate.sh` drives it with both bound and asserts the
  loop install, the wrong-theorem and wrong-hash refusals, and the fallback.
- The tree relation (`LeanLLVM/ITree/Simtt.lean`) is a second, finer statement
  beside `Refines` and `RefinesWithin`, not a replacement for them.  Those
  keep their definitions and their proofs, and no pass or route reasons
  through the tree layer yet; do not describe it as the semantics' refinement
  relation.  It relates **bare handled trees**: memory is an effect, folded by
  `MemoryEffect.handle`, so the relation has no memory index and no frame
  parameter, and a private access is silent because the handler inserted a
  `tau`.  Its own statements follow the same discipline: a positive theorem, a
  negative example the same detector rejects, and an axiom pin no wider than
  `[propext, Classical.choice, Quot.sound]` in `LeanLLVMTest/Vellum.lean`.  The
  congruence theorems (`simtt_bind`, `simtt_interp`) are conditional, and their
  refused witnesses are part of the statement: do not drop a hypothesis to make
  a congruence easier.  The tree layer describes **`PureEnv` environments only**:
  its call event carries a value and no memory, so `handled_runFuel` and the
  fifteen declarations that gain a `PureEnv` hypothesis carry one (sixteen
  change; `HandledExec.vis_call_inv` gains `retAt` only).  A `Calls` entry
  returns the callee's value, memory and allocator state for the semantics, and
  nothing in the tree layer may be described as covering a callee that writes.
  `Classical.choice` is budgeted there for the arbitrary-`Prop` frame the host
  handler decides with `Classical.propDecidable`; that handler is
  proof-facing, `runFuel` and the routes are untouched, and making it
  computable needs a decidable frame contract rather than a silent narrowing.
  The loop rule (`LeanLLVM/ITree/LoopRule.lean`) is conditional too: `simtt_loop`
  does not assert that any pair of loops satisfies its premise, and it says
  nothing about `Refines`/`RefinesWithin`.  Its frame is expressed at the return
  (`oT.AgreesOutside frame oS`), which is why postcondition weakening
  (`simtt_post_mono`), not definitional equality, recovers the plain framed post.
  The loop instance is one pair at fixed budgets and one allocator-derived frame;
  a wider frame, a bigger budget or a rule at the executable refinement relation
  is new work, not a variation on that theorem.
- Keep mathlib behind its adapter.  A new module anywhere in the package
  imports `ITree.Core`/`ITree.Coinduction` (or a module above them), never
  `Mathlib.*`, and clients name trees through `ITree.Core` rather than
  `PFunctor.M`, `MIntl` or `CofixA`.  Only `ITree/Internal/PFunctor.lean` may
  import mathlib directly: `Mathlib.*` may not appear in any other file.  No
  module under `ITree/` or `ITree.lean` may import a `LeanLLVM` module, so
  `lake build ITree` builds without the instantiation.
- The generic library has two focused checks beside the builds:
  `tests/itree-import.lean` elaborates a client that imports `ITree` only, and
  `tests/itree-boundary.sh` checks the import inventory against the actual
  `import` declarations — with a positive control on the same detector before
  each absence claim.  Run them with
  `nix develop -c lake env lean tests/itree-import.lean` and
  `nix develop -c bash tests/itree-boundary.sh`.
- `ITree.mfix` is the seeded reading of the ported `iter`, not a second
  corecursor: its equations and guards are the iterator's.  Do not add a fixed
  point for an arbitrary function-argument body — such a body can choose an
  unguarded recursive seed — and keep each recursive operation's `FiniteLater`
  witness positive: a `now` witness is refused by `not_finiteLater_now`, and the
  import test pins both the witness and that refusal.

## Adding a pass

1. Write `Function → Function` in `LeanLLVM/Transform/`.
2. Prove the local effect lemma for each rewritten instruction/terminator.
3. Lift to `runFuel` by induction, then state the `Beh` result and derive
   `Refines`.
4. Package it as a `Pass` with a `Sound` theorem; add it to
   `LeanLLVM/Pipeline.lean` only if it is ready.
5. Add a `#guard` check showing the pass fires on a concrete program and that
   observable behaviour is unchanged.

## Style

- Keep passes block-local until dominance is modelled; cross-block rewrites
  need an explicit statement of what makes a substitution valid.
- Document a modelling simplification where it is made, not only in this file.
- The driver's output is a toolchain artifact: canonical syntax, one instruction
  per line, block labels preserved.
