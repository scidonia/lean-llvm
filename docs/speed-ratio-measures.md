# Moving the speed ratio in our favour

**The measured constraint:** admission plus staging is **0.76–7.3× the native call** on the P core. Most of the composed route's cost is not in the pipeline at all. So the first measure is staging, not the units.

## The measures, in order of leverage

**1. Reuse the workspace instead of rebuilding it per document.**
The admission and staging rows are per-document costs: a native admission/depth scan and building the caller's buffers in the pipeline record's shape. If the workspace (arena, event records, the fixed workspace) is allocated once and only the *changed* regions are updated per document, the admission/staging rows collapse to the update cost. That is the highest-leverage measure, because those rows are the dominant cost. The doc names allocator/collector carry-over as an inference, so this is also the measure that tests that inference directly.

**2. Avoid the copy where the caller can hand over its buffer.**
Staging copies the document into the pipeline record's shape. If the caller can hand over its own buffer (zero-copy), the staging row is the copy cost only. That is an ABI change, not a speed tweak, and it changes what the wrapper has to prove (presence, capacities, padding, separation, lifetimes) — but it is the right shape for a caller that already owns its document bytes.

**3. Fuse the three units into one pass.**
simdjson fuses classification, the string/escape state and UTF-8 into one pass that writes a structural-index array. The units are three calls reading a mask stream: classification masks, entry positions, UTF-8 validity. Fusing them into a single pass over the document removes the mask-stream staging and the three-call overhead. That is the largest structural lever for the pipeline itself, and it is what makes the units' stage-1 numbers meaningful for a composed route.

**4. Use the units' measured fast paths where they win.**
On strings and UTF-8 the units are faster than simdjson's stage 1 (0.49–0.79 of it). On route-like documents the composed route's staging dominates, so the win is in staging, not in the units. Any optimisation effort should go where the measured cost is: staging, not the units' already-competitive classification.

**5. Measure the pipeline alone, after the workspace is reused.**
The current split includes admission and staging. Reusing the workspace isolates the pipeline's own cost and shows whether the pipeline itself is competitive with simdjson's stage 1. That is the measurement that decides whether further optimisation should target the pipeline or the staging.

## What not to do

Do not optimise the units' classification for route-like documents: it is already in the range of a SIMD stage 1 (13.4–13.9 GB/s), and the composed route's loss is in staging, not in the units. And do not compare the composed route to simdjson's stage 1 as a stage ratio: the route includes stage 2, so the honest comparison is `native ÷ parse`, with `native ÷ stage1` as an upper bound.

## The one-line answer

**Reuse the workspace, and fuse the three units into one pass.** Those are the two measures that move the ratio, because the measured cost is staging and three separate calls, not the pipeline's speed.
