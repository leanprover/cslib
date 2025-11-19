import Strata.Languages.Boogie.Verifier

------------------------------------------------------------
namespace Strata

-- CLRS Exercise 2-4: Inversions
--
-- An inversion in an array A[1..n] is a pair (i, j) such that
--   i < j  and  A[i] > A[j].
--
-- A straightforward Θ(n^2) algorithm:
--
-- INV-COUNT(A)
-- 1  inv = 0
-- 2  for i = 1 to A.length
-- 3      for j = i + 1 to A.length
-- 4          if A[i] > A[j]
-- 5              inv = inv + 1
-- 6  return inv

private def inversionCountPgm :=
#strata
program Boogie;

// Represent an "array of ints" as a map int -> int
type Array := Map int int;

// Global array and its length
var A : Array;
var n : int;

// A proper spec could be:
// inv = |{ (i,j) | 0 <= i < j < n and A[i] > A[j] }|
// but we keep it informal for now.

procedure InversionCount() returns (inv : int)
spec
{
  requires n >= 0;
  ensures inv >= 0;
  // [FEATURE REQUEST]
  // Introducing summation for writing specs.
  // ensures inv ==
  //   (sum k:int ::
  //      (exists i:int, j:int ::
  //         0 <= i && i < j && j < n &&
  //         A[i] > A[j] && k == 1));
}
{
  var i : int;
  var j : int;

  inv := 0;

  // Convert CLRS 1-based loops to 0-based:
  // for i = 0 to n-1:
  i := 0;
  while (i < n)
    invariant (0 <= i && i <= n && inv >= 0);
  {
    // for j = i+1 to n-1:
    j := i + 1;
    while (j < n)
      //invariant (i + 1 <= j && j <= n);
      //invariant (0 <= i && i < n + 1);
      invariant (inv >= 0);
      // [FEATURE REQUEST] Support for multiple invariants
    {
      if (A[i] > A[j]) {
        inv := inv + 1;
      }

      j := j + 1;
    }

    i := i + 1;
  }
};
#end

#eval verify "cvc5" inversionCountPgm
