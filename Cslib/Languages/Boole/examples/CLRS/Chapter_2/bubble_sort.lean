import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- CLRS Chapter 2: Bubble Sort
-- Exercise 2.2
-- BUBBLESORT(A)
-- 1  for i = 1 to A.length − 1
-- 2      for j = A.length downto i + 1
-- 3          if A[j] < A[j − 1]
-- 4              exchange A[j] with A[j − 1]

private def bubbleSortPgm :=
#strata
program Boole;

type Array := Map int int;

var A : Array;
var n : int;

// function array_length(a: Array) : int { n }
// axiom (array_length(A) == n);

procedure BubbleSort() returns ()
spec
{
  modifies A;
  modifies n;

  ensures forall i:int, j:int ::
    0 <= i && i <= j && j < n ==> A[i] <= A[j];
}
{
  var i : int;
  var j : int;
  var tmp : int;

  // Convert CLRS 1-based loops to 0-based:
  // for i = 0 to n-2
  i := 0;

  while (i < n - 1)
    // invariant (0 <= i && i <= n - 1);
    // [FEATURE REQUEST] Support for multiple invariants
    invariant (
      forall p:int, q:int ::
        (n - (i)) <= p && p <= q && q < n ==> A[p] <= A[q]
    );
  {
    // inner loop: j = n-1 downto i+1
    j := n - 1;

    while (j > i)
      //invariant (i < j && j < n);
      //invariant (0 <= i && i <= n - 1);
      invariant (
        forall p:int, q:int ::
          (n - (i)) <= p && p <= q && q < n ==> A[p] <= A[q]
      );
    {
      if (A[j] < A[j - 1])
      {
        tmp := A[j];
        A := A[j := A[j - 1]];
        A := A[j - 1 := tmp];
      }

      j := j - 1;
    }

    i := i + 1;
  }
};
#end

#eval verify "cvc5" bubbleSortPgm
