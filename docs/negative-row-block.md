# The negative row block

**The negative row block** is the division-by-a-power-of-ten block in the emitted `num_fast` conversion — `t3_divBody`, at `while.body232.i.i`.

The emitted starting approximation is computed by scaling the decimal value by powers of ten in both directions: the **positive row block** (`t3_mulBody`, `while.body206.i.i`) multiplies by a power of ten, and the **negative row block** (`t3_divBody`, `while.body232.i.i`) divides by one. The two directions are the two arms of the emitted starting approximation's ladder.

Concretely, the negative row block computes the residual exponent by `ashr` after multiplying by `-2^32` (recovering the index `k` for `k < 2^31`), and tests against `-22`, so the emitted clamp is `min k 22`. Its composition and terminator step are the remaining obligations before the division loop's arms and exit can be proved, and then `NumFastBodyArm`.

The positive row block's step and the `t3Rows` splits are already proved; the negative row block's composition and terminator step are what remains.
