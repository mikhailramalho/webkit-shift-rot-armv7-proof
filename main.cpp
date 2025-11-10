#include "camada/camada.h"

#include <algorithm>
#include <bitset>
#include <cassert>
#include <functional>
#include <iostream>

#include <camada/boolectorsolver.h>
#include <camada/z3solver.h>

#define REQUIRE assert

enum class ShiftOp { LEFT_SHIFT, RIGHT_SHIFT_LOGICAL, RIGHT_SHIFT_ARITHMETIC };

struct ShiftContext {
  camada::SMTSolverRef solver;
  camada::SMTExprRef lhsHi;
  camada::SMTExprRef lhsLo;
  camada::SMTExprRef shift;
  camada::SMTExprRef rhsLo; // shiftReg
  camada::SMTExprRef resultHi;
  camada::SMTExprRef resultLo;
};

camada::SMTExprRef computeExpected(const ShiftContext &ctx, ShiftOp op) {
  // Set up expected result computation
  auto lhs64 = ctx.solver->mkSymbol("lhs64", ctx.solver->mkBVSort(64));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(lhs64, ctx.solver->mkBVConcat(ctx.lhsHi, ctx.lhsLo)));

  auto mask63 = ctx.solver->mkBVFromDec(63, 32);
  auto shift32 = ctx.solver->mkSymbol("shift32", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(shift32, ctx.solver->mkBVAnd(ctx.rhsLo, mask63)));
  auto shift64 = ctx.solver->mkSymbol("shift64", ctx.solver->mkBVSort(64));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(shift64, ctx.solver->mkBVZeroExt(32, shift32)));

  // Compute expected result based on operation type
  auto expected64 =
      ctx.solver->mkSymbol("expected64", ctx.solver->mkBVSort(64));
  switch (op) {
  case ShiftOp::LEFT_SHIFT:
    ctx.solver->addConstraint(
        ctx.solver->mkEqual(expected64, ctx.solver->mkBVShl(lhs64, shift64)));
    break;
  case ShiftOp::RIGHT_SHIFT_LOGICAL:
    ctx.solver->addConstraint(
        ctx.solver->mkEqual(expected64, ctx.solver->mkBVLshr(lhs64, shift64)));
    break;
  case ShiftOp::RIGHT_SHIFT_ARITHMETIC:
    ctx.solver->addConstraint(
        ctx.solver->mkEqual(expected64, ctx.solver->mkBVAshr(lhs64, shift64)));
    break;
  }

  return expected64;
}

camada::SMTExprRef computeActualRightShiftArithmetic(const ShiftContext &ctx) {
  // m_jit.and32(TrustedImm32(63), rhsLo, shift);
  auto shift_computed =
      ctx.solver->mkBVAnd(ctx.solver->mkBVFromDec(63, 32), ctx.rhsLo);
  ctx.solver->addConstraint(ctx.solver->mkEqual(ctx.shift, shift_computed));

  // m_jit.urshift256(lhsLo, shift, resultLo);
  auto resultLo1 = ctx.solver->mkSymbol("resultLo1", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      resultLo1, ctx.solver->mkBVLshr(ctx.lhsLo, ctx.shift)));

  // m_jit.move(TrustedImm32(32), tmp);
  // m_jit.sub32(shift, tmp);  // tmp = tmp - shift
  auto tmp1 = ctx.solver->mkSymbol("tmp1", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(tmp1, ctx.solver->mkBVFromDec(32, 32)));

  auto tmp2 = ctx.solver->mkSymbol("tmp2", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(tmp2, ctx.solver->mkBVSub(tmp1, ctx.shift)));

  // m_jit.lshift256(lhsHi, tmp, tmp);
  auto tmp3 = ctx.solver->mkSymbol("tmp3", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(tmp3, ctx.solver->mkBVShl(ctx.lhsHi, tmp2)));

  // m_jit.or32(tmp, resultLo);
  auto resultLo2 = ctx.solver->mkSymbol("resultLo2", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(resultLo2, ctx.solver->mkBVOr(tmp3, resultLo1)));

  // m_jit.move(shift, tmp);
  // m_jit.sub32(TrustedImm32(32), tmp);  // tmp = tmp - 32
  auto tmp4 = ctx.solver->mkSymbol("tmp4", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(tmp4, ctx.shift));

  auto tmp5 = ctx.solver->mkSymbol("tmp5", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      tmp5, ctx.solver->mkBVSub(tmp4, ctx.solver->mkBVFromDec(32, 32))));

  // m_jit.rshift256(lhsHi, tmp, tmp);
  auto tmp6 = ctx.solver->mkSymbol("tmp6", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(tmp6, ctx.solver->mkBVAshr(ctx.lhsHi, tmp5)));

  // m_jit.or32(resultLo, tmp, tmp);
  auto tmp7 = ctx.solver->mkSymbol("tmp7", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(tmp7, ctx.solver->mkBVOr(resultLo2, tmp6)));

  // m_jit.moveConditionally32(RelationalCondition::AboveOrEqual, shift,
  // TrustedImm32(32), tmp, resultLo, resultLo); if (shift >= 32) then resultLo
  // = tmp7 else resultLo = resultLo2
  auto condition =
      ctx.solver->mkBVUge(ctx.shift, ctx.solver->mkBVFromDec(32, 32));
  auto resultLo_final =
      ctx.solver->mkSymbol("resultLo_final", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      resultLo_final, ctx.solver->mkIte(condition, tmp7, resultLo2)));

  // m_jit.rshift256(lhsHi, shift, resultHi);
  auto resultHi_final =
      ctx.solver->mkSymbol("resultHi_final", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      resultHi_final, ctx.solver->mkBVAshr(ctx.lhsHi, ctx.shift)));

  // Concatenate resultHi:resultLo to form the 64-bit result
  auto actual64 = ctx.solver->mkSymbol("actual64", ctx.solver->mkBVSort(64));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      actual64, ctx.solver->mkBVConcat(resultHi_final, resultLo_final)));

  return actual64;
}

camada::SMTExprRef computeActualRightShiftLogical(const ShiftContext &ctx) {
  // m_jit.and32(TrustedImm32(63), rhsLo, shift);
  auto shift_computed =
      ctx.solver->mkBVAnd(ctx.solver->mkBVFromDec(63, 32), ctx.rhsLo);
  ctx.solver->addConstraint(ctx.solver->mkEqual(ctx.shift, shift_computed));

  // m_jit.urshift256(lhsLo, shift, resultLo);
  auto resultLo1 = ctx.solver->mkSymbol("resultLo1", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      resultLo1, ctx.solver->mkBVLshr(ctx.lhsLo, ctx.shift)));

  // m_jit.move(TrustedImm32(32), tmp);
  // m_jit.sub32(shift, tmp);  // tmp = tmp - shift
  auto tmp1 = ctx.solver->mkSymbol("tmp1", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(tmp1, ctx.solver->mkBVFromDec(32, 32)));

  auto tmp2 = ctx.solver->mkSymbol("tmp2", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(tmp2, ctx.solver->mkBVSub(tmp1, ctx.shift)));

  // m_jit.lshift256(lhsHi, tmp, tmp);
  auto tmp3 = ctx.solver->mkSymbol("tmp3", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(tmp3, ctx.solver->mkBVShl(ctx.lhsHi, tmp2)));

  // m_jit.or32(tmp, resultLo);
  auto resultLo2 = ctx.solver->mkSymbol("resultLo2", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(resultLo2, ctx.solver->mkBVOr(tmp3, resultLo1)));

  // m_jit.move(shift, tmp);
  // m_jit.sub32(TrustedImm32(32), tmp);  // tmp = tmp - 32
  auto tmp4 = ctx.solver->mkSymbol("tmp4", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(tmp4, ctx.shift));

  auto tmp5 = ctx.solver->mkSymbol("tmp5", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      tmp5, ctx.solver->mkBVSub(tmp4, ctx.solver->mkBVFromDec(32, 32))));

  // m_jit.urshift256(lhsHi, tmp, tmp);
  auto tmp6 = ctx.solver->mkSymbol("tmp6", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(tmp6, ctx.solver->mkBVLshr(ctx.lhsHi, tmp5)));

  // m_jit.or32(tmp, resultLo);
  auto resultLo_final =
      ctx.solver->mkSymbol("resultLo_final", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      resultLo_final, ctx.solver->mkBVOr(tmp6, resultLo2)));

  // m_jit.urshift256(lhsHi, shift, resultHi);
  auto resultHi_final =
      ctx.solver->mkSymbol("resultHi_final", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      resultHi_final, ctx.solver->mkBVLshr(ctx.lhsHi, ctx.shift)));

  // Concatenate resultHi:resultLo to form the 64-bit result
  auto actual64 = ctx.solver->mkSymbol("actual64", ctx.solver->mkBVSort(64));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      actual64, ctx.solver->mkBVConcat(resultHi_final, resultLo_final)));

  return actual64;
}

camada::SMTExprRef computeActualLeftShift(const ShiftContext &ctx) {
  // m_jit.and32(TrustedImm32(63), shiftReg, shift);
  auto shift_computed =
      ctx.solver->mkBVAnd(ctx.solver->mkBVFromDec(63, 32), ctx.rhsLo);
  ctx.solver->addConstraint(ctx.solver->mkEqual(ctx.shift, shift_computed));

  // m_jit.sub32(shift, TrustedImm32(32), tmp);
  auto tmp1 = ctx.solver->mkSymbol("tmp1", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      tmp1, ctx.solver->mkBVSub(ctx.shift, ctx.solver->mkBVFromDec(32, 32))));

  // m_jit.lshiftUnchecked(lhsHi, shift, resultHi);
  auto resultHi1 = ctx.solver->mkSymbol("resultHi1", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      resultHi1, ctx.solver->mkBVShl(ctx.lhsHi, ctx.shift)));

  // m_jit.lshiftUnchecked(lhsLo, tmp, tmp);
  auto tmp2 = ctx.solver->mkSymbol("tmp2", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(tmp2, ctx.solver->mkBVShl(ctx.lhsLo, tmp1)));

  // m_jit.or32(resultHi, tmp, resultHi);
  auto resultHi2 = ctx.solver->mkSymbol("resultHi2", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(resultHi2, ctx.solver->mkBVOr(resultHi1, tmp2)));

  // m_jit.sub32(TrustedImm32(32), shift, tmp);
  auto tmp3 = ctx.solver->mkSymbol("tmp3", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      tmp3, ctx.solver->mkBVSub(ctx.solver->mkBVFromDec(32, 32), ctx.shift)));

  // m_jit.urshiftUnchecked(lhsLo, tmp, tmp);
  auto tmp4 = ctx.solver->mkSymbol("tmp4", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(tmp4, ctx.solver->mkBVLshr(ctx.lhsLo, tmp3)));

  // m_jit.or32(resultHi, tmp, resultHi);
  auto resultHi_final =
      ctx.solver->mkSymbol("resultHi_final", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(
      ctx.solver->mkEqual(resultHi_final, ctx.solver->mkBVOr(resultHi2, tmp4)));

  // m_jit.lshiftUnchecked(lhsLo, shift, resultLo);
  auto resultLo_final =
      ctx.solver->mkSymbol("resultLo_final", ctx.solver->mkBVSort(32));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      resultLo_final, ctx.solver->mkBVShl(ctx.lhsLo, ctx.shift)));

  // Concatenate resultHi:resultLo to form the 64-bit result
  auto actual64 = ctx.solver->mkSymbol("actual64", ctx.solver->mkBVSort(64));
  ctx.solver->addConstraint(ctx.solver->mkEqual(
      actual64, ctx.solver->mkBVConcat(resultHi_final, resultLo_final)));

  return actual64;
}

void proveShiftCorrectness(const ShiftContext &ctx,
                           const std::string &algorithmName, ShiftOp op,
                           camada::SMTExprRef actual64) {
  auto expected64 = computeExpected(ctx, op);

  // Prove equivalence by checking if they can differ (should be UNSAT)
  auto neq = ctx.solver->mkNot(ctx.solver->mkEqual(expected64, actual64));
  ctx.solver->addConstraint(neq);

  // Check and report results
  auto result = ctx.solver->check();
  if (result == camada::checkResult::UNSAT) {
    std::cerr << "✓ " << algorithmName << " - PASSED\n";
  } else if (result == camada::checkResult::SAT) {
    std::cerr << "\n=== COUNTEREXAMPLE FOUND: " << algorithmName << " ===\n";
    std::cerr << "The algorithms differ for these values:\n";
    ctx.solver->dump();
    ctx.solver->dumpModel();
  } else {
    std::cerr << "\n=== UNKNOWN: " << algorithmName << " ===\n";
    std::cerr << "Solver could not determine satisfiability.\n";
    ctx.solver->dump();
  }
}

void testShift(const std::string &testName, ShiftOp op,
               camada::SMTExprRef lhsHi, camada::SMTExprRef lhsLo,
               camada::SMTExprRef rhsHi, camada::SMTExprRef rhsLo,
               camada::SMTExprRef resultHi, camada::SMTExprRef resultLo,
               camada::SMTSolverRef solver, bool checkLhsPreserved = false,
               bool checkRhsPreserved = false) {
  auto shift = solver->mkSymbol("shift", solver->mkBVSort(32));

  // If we need to check that lhs/rhs are preserved, save their original values
  camada::SMTExprRef origLhsHi, origLhsLo, origRhsHi, origRhsLo;

  if (checkLhsPreserved) {
    origLhsHi = solver->mkSymbol("origLhsHi", solver->mkBVSort(32));
    origLhsLo = solver->mkSymbol("origLhsLo", solver->mkBVSort(32));
    solver->addConstraint(solver->mkEqual(origLhsHi, lhsHi));
    solver->addConstraint(solver->mkEqual(origLhsLo, lhsLo));
  }

  if (checkRhsPreserved) {
    origRhsHi = solver->mkSymbol("origRhsHi", solver->mkBVSort(32));
    origRhsLo = solver->mkSymbol("origRhsLo", solver->mkBVSort(32));
    solver->addConstraint(solver->mkEqual(origRhsHi, rhsHi));
    solver->addConstraint(solver->mkEqual(origRhsLo, rhsLo));
  }

  // Create context struct
  ShiftContext ctx{solver, lhsHi, lhsLo, shift, rhsLo, resultHi, resultLo};

  // Compute actual result based on operation type
  camada::SMTExprRef actualResult;
  switch (op) {
  case ShiftOp::LEFT_SHIFT:
    actualResult = computeActualLeftShift(ctx);
    break;
  case ShiftOp::RIGHT_SHIFT_LOGICAL:
    actualResult = computeActualRightShiftLogical(ctx);
    break;
  case ShiftOp::RIGHT_SHIFT_ARITHMETIC:
    actualResult = computeActualRightShiftArithmetic(ctx);
    break;
  }

  proveShiftCorrectness(ctx, testName, op, actualResult);

  // After the algorithm runs, check that non-aliased operands are preserved
  if (checkLhsPreserved) {
    // Verify lhs still holds original value
    solver->addConstraint(solver->mkEqual(lhsHi, origLhsHi));
    solver->addConstraint(solver->mkEqual(lhsLo, origLhsLo));
  }

  if (checkRhsPreserved) {
    // Verify rhs still holds original value
    solver->addConstraint(solver->mkEqual(rhsHi, origRhsHi));
    solver->addConstraint(solver->mkEqual(rhsLo, origRhsLo));
  }
}

int main() {
  // Test 1: No aliasing - all separate symbols
  {
    auto solver = camada::createZ3Solver();
    auto lhsLo = solver->mkSymbol("lhsLo", solver->mkBVSort(32));
    auto lhsHi = solver->mkSymbol("lhsHi", solver->mkBVSort(32));
    auto rhsLo = solver->mkSymbol("rhsLo", solver->mkBVSort(32));
    auto rhsHi = solver->mkSymbol("rhsHi", solver->mkBVSort(32));
    auto resultLo = solver->mkSymbol("resultLo", solver->mkBVSort(32));
    auto resultHi = solver->mkSymbol("resultHi", solver->mkBVSort(32));

    testShift("Left Shift (no aliasing)", ShiftOp::LEFT_SHIFT, lhsHi, lhsLo,
              rhsHi, rhsLo, resultHi, resultLo, solver);
  }

  // Test 2: lhs and result share same symbols (in-place operation)
  {
    auto solver = camada::createZ3Solver();
    auto lhsLo = solver->mkSymbol("lhsLo", solver->mkBVSort(32));
    auto lhsHi = solver->mkSymbol("lhsHi", solver->mkBVSort(32));
    auto rhsLo = solver->mkSymbol("rhsLo", solver->mkBVSort(32));
    auto rhsHi = solver->mkSymbol("rhsHi", solver->mkBVSort(32));

    // Result aliases lhs - should hold correct result at the end
    // rhs should be preserved (not modified)
    testShift("Left Shift (lhs = result)", ShiftOp::LEFT_SHIFT, lhsHi, lhsLo,
              rhsHi, rhsLo, lhsHi, lhsLo, solver,
              /*checkLhsPreserved=*/false, /*checkRhsPreserved=*/true);
  }

  // Test 3: rhs and result share same symbols
  {
    auto solver = camada::createZ3Solver();
    auto lhsLo = solver->mkSymbol("lhsLo", solver->mkBVSort(32));
    auto lhsHi = solver->mkSymbol("lhsHi", solver->mkBVSort(32));
    auto rhsLo = solver->mkSymbol("rhsLo", solver->mkBVSort(32));
    auto rhsHi = solver->mkSymbol("rhsHi", solver->mkBVSort(32));

    // Result aliases rhs - should hold correct result at the end
    // lhs should be preserved (not modified)
    testShift("Left Shift (rhs = result)", ShiftOp::LEFT_SHIFT, lhsHi, lhsLo,
              rhsHi, rhsLo, rhsHi, rhsLo, solver,
              /*checkLhsPreserved=*/true, /*checkRhsPreserved=*/false);
  }

  // Test 4-6: Arithmetic right shift tests
  // Test 4: No aliasing
  {
    auto solver = camada::createZ3Solver();
    auto lhsLo = solver->mkSymbol("lhsLo", solver->mkBVSort(32));
    auto lhsHi = solver->mkSymbol("lhsHi", solver->mkBVSort(32));
    auto rhsLo = solver->mkSymbol("rhsLo", solver->mkBVSort(32));
    auto rhsHi = solver->mkSymbol("rhsHi", solver->mkBVSort(32));
    auto resultLo = solver->mkSymbol("resultLo", solver->mkBVSort(32));
    auto resultHi = solver->mkSymbol("resultHi", solver->mkBVSort(32));

    testShift("Arithmetic Right Shift (no aliasing)",
              ShiftOp::RIGHT_SHIFT_ARITHMETIC, lhsHi, lhsLo, rhsHi, rhsLo,
              resultHi, resultLo, solver);
  }

  // Test 5: lhs and result share same symbols
  {
    auto solver = camada::createZ3Solver();
    auto lhsLo = solver->mkSymbol("lhsLo", solver->mkBVSort(32));
    auto lhsHi = solver->mkSymbol("lhsHi", solver->mkBVSort(32));
    auto rhsLo = solver->mkSymbol("rhsLo", solver->mkBVSort(32));
    auto rhsHi = solver->mkSymbol("rhsHi", solver->mkBVSort(32));

    testShift("Arithmetic Right Shift (lhs = result)",
              ShiftOp::RIGHT_SHIFT_ARITHMETIC, lhsHi, lhsLo, rhsHi, rhsLo,
              lhsHi, lhsLo, solver,
              /*checkLhsPreserved=*/false, /*checkRhsPreserved=*/true);
  }

  // Test 6: rhs and result share same symbols
  {
    auto solver = camada::createZ3Solver();
    auto lhsLo = solver->mkSymbol("lhsLo", solver->mkBVSort(32));
    auto lhsHi = solver->mkSymbol("lhsHi", solver->mkBVSort(32));
    auto rhsLo = solver->mkSymbol("rhsLo", solver->mkBVSort(32));
    auto rhsHi = solver->mkSymbol("rhsHi", solver->mkBVSort(32));

    testShift("Arithmetic Right Shift (rhs = result)",
              ShiftOp::RIGHT_SHIFT_ARITHMETIC, lhsHi, lhsLo, rhsHi, rhsLo,
              rhsHi, rhsLo, solver,
              /*checkLhsPreserved=*/true, /*checkRhsPreserved=*/false);
  }

  // Test 7-9: Logical right shift tests
  // Test 7: No aliasing
  {
    auto solver = camada::createZ3Solver();
    auto lhsLo = solver->mkSymbol("lhsLo", solver->mkBVSort(32));
    auto lhsHi = solver->mkSymbol("lhsHi", solver->mkBVSort(32));
    auto rhsLo = solver->mkSymbol("rhsLo", solver->mkBVSort(32));
    auto rhsHi = solver->mkSymbol("rhsHi", solver->mkBVSort(32));
    auto resultLo = solver->mkSymbol("resultLo", solver->mkBVSort(32));
    auto resultHi = solver->mkSymbol("resultHi", solver->mkBVSort(32));

    testShift("Logical Right Shift (no aliasing)",
              ShiftOp::RIGHT_SHIFT_LOGICAL, lhsHi, lhsLo, rhsHi, rhsLo,
              resultHi, resultLo, solver);
  }

  // Test 8: lhs and result share same symbols
  {
    auto solver = camada::createZ3Solver();
    auto lhsLo = solver->mkSymbol("lhsLo", solver->mkBVSort(32));
    auto lhsHi = solver->mkSymbol("lhsHi", solver->mkBVSort(32));
    auto rhsLo = solver->mkSymbol("rhsLo", solver->mkBVSort(32));
    auto rhsHi = solver->mkSymbol("rhsHi", solver->mkBVSort(32));

    testShift("Logical Right Shift (lhs = result)",
              ShiftOp::RIGHT_SHIFT_LOGICAL, lhsHi, lhsLo, rhsHi, rhsLo, lhsHi,
              lhsLo, solver,
              /*checkLhsPreserved=*/false, /*checkRhsPreserved=*/true);
  }

  // Test 9: rhs and result share same symbols
  {
    auto solver = camada::createZ3Solver();
    auto lhsLo = solver->mkSymbol("lhsLo", solver->mkBVSort(32));
    auto lhsHi = solver->mkSymbol("lhsHi", solver->mkBVSort(32));
    auto rhsLo = solver->mkSymbol("rhsLo", solver->mkBVSort(32));
    auto rhsHi = solver->mkSymbol("rhsHi", solver->mkBVSort(32));

    testShift("Logical Right Shift (rhs = result)",
              ShiftOp::RIGHT_SHIFT_LOGICAL, lhsHi, lhsLo, rhsHi, rhsLo, rhsHi,
              rhsLo, solver,
              /*checkLhsPreserved=*/true, /*checkRhsPreserved=*/false);
  }
}
