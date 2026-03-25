import Strata.MetaVerifier
import Smt

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

procedure BubbleSort() returns ()
spec
{
  modifies A;
  modifies n;

  ensures ∀ i:int, j:int .
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
    // After each outer pass, A[0..i-1] is sorted and <= all of A[i..n-1].
    // Combined into one quantifier: ∀ p≤q<n, p<i ⇒ A[p]≤A[q].
    invariant 0 <= i
    invariant ∀ p:int, q:int .
      0 <= p && p <= q && q < n && p < i ==> A[p] <= A[q]
  {
    // inner loop: j = n-1 downto i+1
    j := n - 1;

    while (j > i)
      // A[j] is the running minimum of A[j..n-1], bubbling leftward.
      invariant i <= j && j < n
      invariant ∀ k:int . j <= k && k < n ==> A[j] <= A[k]
      invariant ∀ p:int, q:int .
        0 <= p && p <= q && q < n && p < i ==> A[p] <= A[q]
    {
      if (A[j] < A[j - 1])
      {
        tmp := A[j];
        A[j] := A[j - 1];
        A[j - 1] := tmp;
      }

      j := j - 1;
    }

    i := i + 1;
  }
};
#end

#eval Strata.Boole.verify "cvc5" bubbleSortPgm

example : Strata.smtVCsCorrect bubbleSortPgm := by
  gen_smt_vcs
  all_goals (smt +mono)
