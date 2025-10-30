# JIT Shift Algorithm Verification

Formal verification of 64-bit shift operations implemented using 32-bit registers, using SMT solving via the Camada library.

## Overview

This project uses SMT (Satisfiability Modulo Theories) solvers to prove the correctness of three JIT shift algorithms:
- **Left Shift**: 64-bit left shift using two 32-bit registers
- **Arithmetic Right Shift**: Sign-extending right shift
- **Logical Right Shift**: Zero-filling right shift

Each algorithm is tested in three scenarios:
1. No register aliasing (all operands use separate registers)
2. In-place on left operand (lhs = result)
3. Result overwrites shift register (rhs = result)

## Dependencies

- **[Camada](https://github.com/mikhailramalho/camada)**: Unified C++ interface for multiple SMT solvers
- **CMake** 3.11 or higher
- **Ninja** build system
- At least one SMT solver backend (Z3, MathSAT, STP, CVC4, Yices, or Boolector)

## Building

```bash
mkdir build && cd build
cmake -G Ninja -DSOLVER_CAMADA_DIR=/path/to/camada ..
ninja
```

## Running

```bash
./Hello
```

Expected output:
```
✓ Left Shift (no aliasing) - PASSED
✓ Left Shift (lhs = result) - PASSED
✓ Left Shift (rhs = result) - PASSED
✓ Arithmetic Right Shift (no aliasing) - PASSED
✓ Arithmetic Right Shift (lhs = result) - PASSED
✓ Arithmetic Right Shift (rhs = result) - PASSED
✓ Logical Right Shift (no aliasing) - PASSED
✓ Logical Right Shift (lhs = result) - PASSED
✓ Logical Right Shift (rhs = result) - PASSED
```

## How It Works

For each shift operation:
1. **Expected behavior**: Computed using native 64-bit SMT operations
2. **Actual behavior**: Step-by-step translation of JIT algorithm to SMT constraints
3. **Verification**: SMT solver checks if `expected ≠ actual` is satisfiable
   - **UNSAT** = algorithms are equivalent (proof of correctness)
   - **SAT** = counterexample found (algorithm has a bug)

The verification also ensures that non-aliased operands preserve their original values during in-place operations.

## Sanitizer Support

Build with sanitizers for debugging:

```bash
cmake -G Ninja -DCMAKE_BUILD_TYPE=Sanitizer -DSANITIZER_TYPE=ASAN ..
```

Available sanitizers: ASAN, TSAN, LSAN, MSAN, UBSAN
