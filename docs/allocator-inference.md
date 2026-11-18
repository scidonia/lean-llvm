# Why "allocator and collector carry-over" is an inference, not a measurement

**The fact being inferred:** the staging row's spread at a single size is 41.9–164.5 µs on *identical buffer arithmetic*. That is a large spread for the same bytes and the same operations, and it has a shape: the same work, different costs.

**Why it is an inference, not a measurement:** the harness measures **time**, not allocator or collector events. It does not observe allocations, frees, or GC pauses. So the cause of that spread cannot be read off the harness: it could be allocator/collector carry-over, or it could be something else — the admission/depth scan's content dependence, page faults on a fresh buffer, cache behaviour, or another process. The doc names allocator/collector carry-over as an *inference from the spread's shape*, not as a measured cause, because the instrument does not measure the thing being claimed.

**Why that matters for the measures:** reusing the workspace is the measure that would *test* the inference directly. If the spread collapses when the workspace is reused, the inference is confirmed; if it does not, it is not. Until that measurement exists, the honest statement is that the spread is *consistent with* allocator/collector carry-over, not that it is caused by it.

**The rule this comes from:** a result belongs to the instrument that measured it. A time measurement cannot establish a cause about allocator or collector behaviour, and the doc says so rather than presenting the inference as a finding.
