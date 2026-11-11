# Call memory

A call's environment is the linker's selection for an external symbol.  What it
leaves behind — the returned value, the memory after its writes, and the
allocator state the caller resumes from — is what a caller can then observe, and
what a module replacement may ignore only outside the callee's footprint.

These scenarios drive the semantics and the two-environment relation.  The
programs are built here; the selection is the library's own installed
environment where one exists — `envFor` for CM2, `envForBody` for CM4 — and
scenario-built where the scenario needs a body the library does not provide:
`cmStore` for CM1, `envA` and `envB` for CM3.  The caller text is a `Function`
value, so the run is in process and deterministic; no compiler, service or
network is reached.  The negative claims are theorems, because the relation
quantifies over every argument list, memory and allocator state, and a `#guard`
can decide only a closed instance; where a negative rests on an unpinned byte,
the scenario asserts the inequality (`≠ none`) rather than a value.

    nix develop -c lake env lean tests/call-memory.lean

### CM1 — a caller observes the store its callee left

- **Actor:** the installed selection for the seam.
- **Given:** `cmObserve`, `%p = call ptr @seam(i64 %arg)`, `%v = load i64, ptr %p`,
  `ret i64 %v`; and a selection whose seam entry writes the eight little-endian
  bytes of `42` at address `1`, advances the allocator to `9`, and returns
  `Value.ptr 1`.
- **When:** the caller is run on `[.int 64 0]` under that selection.
- **Then:** it returns `.int 64 42`, and the memory it returns reads `42` at
  address `1` and `natToBytes 42 8` at `1` for eight bytes — the returned value
  and the bytes are asserted separately, so the value is bound to what the callee
  stored rather than to the load's own arithmetic.
- **Why:** the memory a callee writes is the caller's state after the call; a
  model that carries only the returned value leaves the caller's load undefined.
- **Not claimed:** that the caller may read an address it was not handed.

### CM2 — a pure callee leaves the caller's memory and allocator untouched

- **Actor:** the installed selection — the library's `envFor`, which returns its
  argument and leaves the caller's memory and allocator exactly as it found
  them.
- **Given:** `cmKeep`, `alloca %buf i64`, `store %arg -> %buf`,
  `call %r = @seam(%arg)`, `%out = load i64 %buf`, `ret %out`, with no store
  after the call; and `cmKeepAlloc`, which additionally allocates `%tmp` after
  the call, stores `0` at `%tmp`, and then loads `%buf` — so a callee that reset
  the allocator would hand `%tmp` the address `1` of `%buf`, clobber it, and
  change the value the caller returns.
- **When:** each caller is run on `[.int 64 0x2A]` under `envFor (fun x => x)`.
- **Then:** the first returns `0x2A` and the memory it returns reads `0x2A` at
  address `1`; the second returns `0x2A` too, because `%tmp` is at `9` and the
  store there leaves `%buf` alone.
- **Why:** the caller adopts the callee's memory wholesale and resumes from the
  callee's allocator state, so a selection that returns a fresh memory erases
  what the caller had stored, and one that resets the allocator aliases the
  caller's later locals onto its earlier ones.  Both halves are observable: the
  second only through the allocation `cmKeepAlloc` makes after the call.
- **Not claimed:** that `envFor` is the only pure selection.

### CM3 — the relation is sensitive to memory outside the frame

- **Actor:** the module-replacement relation, over two selections.
- **Given:** `envA` writes the byte `42` at address `1`, returns `.int 64 0`, and
  resumes the caller at `next + 8`; `envB` writes the byte `43` at address `1`,
  returns `.int 64 0`, and resumes at `next + 8`.  Each selection therefore
  reserves eight bytes from whatever base the caller hands it, which satisfies
  the relation's `next ≤ r.next` at every base, while the differing byte is at
  the absolute address `1`, which the caller's frame hides.
- **When:** the relation is stated over the two selections, and each selection's
  result is read at the reserved state.
- **Then:** two assertions hold in one run.
  - The relation holds at `Band 1 3`: the returned value and the allocator
    advance are equal, and the memories agree outside a band that contains the
    only differing byte.
  - The separating address is `1`, which `Band 2 3` excludes, and the two
    memories really do differ there — asserted as a byte read by a `#guard`.
- **Why:** a relation that ignored memory outside the frame would accept these
  two selections; the positive half shows the band is enough, and the witness
  shows the bytes at a named address are what tell the two apart, at an address
  the band excludes.
- **Not claimed:** that the two selections are related at a frame that excludes
  address `1`.

### CM4 — the frame is load-bearing in both directions

- **Actor:** the module-replacement relation, over a caller that does not read a
  callee band.
- **Given:** `callerFunction`, one `.call` and one `ret`, which returns the
  callee's value and executes no load; and the two installed selections
  `envForBody 10000 16 loopFunction` and `envForBody 10000 16 candidateFunction`
  at allocation base `1`.
- **When:** the caller is related to itself across the two selections.
- **Then:** the relation holds at `Band 1 17`, the band the loop's two locals
  occupy, and it is refused at `Band 17 25`: the loop leaves a byte at address
  `1`, the candidate leaves the incoming memory unchanged, and address `1` lies
  outside `Band 17 25`, so no frame that excludes the callee's band can relate
  them.  The refusal is a proved negation; the proof uses `readByte memL 1 ≠
  none` as an inequality and pins no byte value.
- **Why:** a frame that is named but never consulted accepts a replacement whose
  writes escape it.  A caller that does not load the band is related at the band
  and refused below it, which is what makes the frame, rather than the caller's
  text, the load-bearing part.
- **Not claimed:** anything about a caller that loads inside the callee's band;
  such a caller distinguishes the two selections by value, and the outcome
  relation compares returned values before memory.

### CM5 — the caller theorem consumes the loop's framed statement

- **Actor:** the module theorem, as elaborated.
- **Given:** `caller_replaces_loop_within` and `loop_seam_within_refines`.
- **When:** each theorem's proof term is printed one level deep.
- **Then:** `loop_seam_within_refines`'s print names
  `LeanLLVM.Refinement.CommaMaskLoop.loop_refines_candidate_within`, and
  `caller_replaces_loop_within`'s print names
  `LeanLLVM.Refinement.loop_seam_within_refines`.
- **Why:** the caller theorem reaches the loop's selection through the framed
  statement rather than re-deriving the base-one agreement; one level of print
  shows the consumed constant, and the two prints together exhibit the chain
  `caller_replaces_loop_within → loop_seam_within_refines →
  loop_refines_candidate_within` at the depth the printer reaches.
- **Not claimed:** that a one-level print shows the transitive constant, or that
  the loop's framed statement is the only route to the caller theorem.
