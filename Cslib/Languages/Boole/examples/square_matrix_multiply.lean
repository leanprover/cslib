import StrataBoole.MetaVerifier
import Smt

namespace Strata

/-
Verification example for the textbook square-matrix-multiply algorithm, using direct nested
`for ... to` loops to exercise their lowering end to end.
-/

private def squareMatrixMult :=
#strata
program Boole;

var A : (Map int (Map int int));
var B : (Map int (Map int int));
var C : (Map int (Map int int));

procedure SquareMatrixMultiply(n: int) returns ()
spec
{
  requires n >= 1;
  modifies C;
}
{
  for i:int := 1 to n
    invariant 1 <= i
    invariant i <= n + 1
  {
    for j:int := 1 to n
      invariant 1 <= j
      invariant j <= n + 1
    {
      C[i][j] := 0;
      for k:int := 1 to n
        invariant 1 <= k
        invariant k <= n + 1
      {
        C[i][j] := (C[i])[j] + ((A[i])[k] * (B[k])[j]);
      }
    }
  }
};

#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_2_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_2_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_2_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_2_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" squareMatrixMult (options := .quiet)

theorem squareMatrixMult_smtVCsCorrect : Strata.smtVCsCorrectBoole squareMatrixMult := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
