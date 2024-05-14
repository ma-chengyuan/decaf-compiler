This folder contains demonstrations/test cases of optimizations we implemented.

- `rgae/`: Redundant global & array access elimination
- `unrolling/`: Constant-trip-count loop unrolling (with constant folding)
- `dase/`: Dead array store elimination
- `gvnpre/`: Global value numbering-partial redundancy elimination
- `psr/`: Polynomial strength reduction
- `indvar/`: Polynomial induction variable strength reduction
- `fuse-bc/`: Bounds check fusion
- `const-div-mod/`: Constant divisor/modulo strength reduction
- `licm/`: Loop invariant code motion
- `nm-arr/`: Array index offset nonmaterializer
- `peephole/`: Peephole assembly optimizations
- `omit-frame-pointer/`: Use `%rbp` as a general purpose use register

More optimizations are documented in our design doc with examples attached.
