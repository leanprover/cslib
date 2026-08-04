import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for recursive-index map assignment (`arr[i][j]... := v`):
lowering recursively nests map `select`/`update`, so any index depth works.
Demonstrated via matrix transpose, with a real postcondition (every entry of
the result is the corresponding transposed entry of the input) rather than a
syntax-only check.
-/

private def matrixTransposeSeed : StrataDDM.Program :=
#strata
program Boole;

type Matrix := Map int (Map int int);

procedure matrix_transpose (A: Matrix, m: int, n: int) returns (B: Matrix)
spec {
  ensures ∀ i: int, j: int . 0 <= i && i < m && 0 <= j && j < n ==> B[i][j] == A[j][i];
}
{
  var j: int;

  for i: int := 0 to (m - 1)
    invariant ∀ p: int, q: int . 0 <= p && p < i && 0 <= q && q < n ==> B[p][q] == A[q][p]
  {
    j := 0;
    while (j < n)
      invariant ∀ p: int, q: int . 0 <= p && p < i && 0 <= q && q < n ==> B[p][q] == A[q][p]
      invariant ∀ q: int . 0 <= q && q < j ==> B[i][q] == A[q][i]
    {
      B[i][j] := A[j][i];
      j := j + 1;
    }
  }
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_1
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

Obligation: matrix_transpose_ensures_0_594
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" matrixTransposeSeed (options := .quiet)

theorem matrixTransposeSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole matrixTransposeSeed := by
  gen_smt_vcs_boole
  all_goals (first | smt | smt +mono | omega | trivial | grind)
