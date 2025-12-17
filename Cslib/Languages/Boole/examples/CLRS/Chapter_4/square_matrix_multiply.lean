import Strata.MetaVerifier

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

// [FEATURE_REQUEST] the definitions below
// could have a better representation
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
  var i: int;
  var j: int;
  var k: int;

  i := 1;
  while (i <= n)
    invariant 1 <= i && i <= n + 1;
  {
    j := 1;
    while (j <= n)
      invariant 1 <= j && j <= n + 1;
    {
      C := (C[i := C[i][j := 0]]);
      k := 1;
      while (k <= n)
        invariant 1 <= k && k <= n + 1;
      {
        C := (C[i := C[i][j := (C[i][j] + (A[i][k] * B[k][j]))]]);
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
};

#end

#eval verify "cvc5" squareMatrixMult
