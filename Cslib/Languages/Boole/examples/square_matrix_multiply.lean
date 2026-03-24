import Strata.MetaVerifier
import Smt

namespace Strata

-- CLRS Chapter 4: SQUARE-MATRIX-MULTIPLY
-- page 75

--SQUARE-MATRIX-MULTIPLY (A, B)
-- n = A.rows
-- let C be a new n x n matrix
-- for i = 1 to n
--   for j = 1 to n
--     c_{ij} = 0
--     for k = 1 to n
--       cij = c_{ij} + a_{ik} * b_{kj}
--return C

private def squareMatrixMult :=
#strata
program Boole;

var A : (Map int (Map int int));
var B : (Map int (Map int int));
var C : (Map int (Map int int));

// Iterative version
// Do we want the recursive version described in the book?

procedure SquareMatrixMultiply(n: int) returns ()
spec
{
  requires n >= 1;
  modifies C;
}
{
  var j: int;
  var k: int;

  for i:int := 1 to n
    invariant 1 <= i
    invariant i <= n + 1
  { // [FEUTURE REQUEST]: add support for nested for-loops to Boole, which would allow us to write this more cleanly
    j := 1;
    while (j <= n)
      invariant 1 <= j
      invariant j <= n + 1
    {
      C[i][j] := 0;
      k := 1;
      while (k <= n)
        invariant 1 <= k
        invariant k <= n + 1
      {
        C[i][j] := (C[i])[j] + ((A[i])[k] * (B[k])[j]);
        k := k + 1;
      }
      j := j + 1;
    }
  }
};

#end

#eval Strata.Boole.verify "cvc5" squareMatrixMult

example : Strata.smtVCsCorrect squareMatrixMult := by
  gen_smt_vcs
  all_goals smt
