import Strata.MetaVerifier

---------------------------------------------------------------------
namespace Strata

-- CLRS Chapter 1: Insertion Sort
-- Pseudo-code adapted from CLRS book (3rd edition), page 18

-- Pseudo-code:
-- INSERTION-SORT(A)
-- 1  for j = 2 to A.length
-- 2      key = A[j]
-- 3      // Insert A[j] into the sorted sequence A[1..j-1]
-- 4      i = j - 1
-- 5      while i > 0 and A[i] > key
-- 6          A[i + 1] = A[i]
-- 7          i = i - 1
-- 8      A[i + 1] = key

private def insertionSortPgm :=
#strata
program Boole;

// An "array of ints" is a map from int to int
type Array := Map int int;

// Global array we'll sort
var A : Array;
var n : int; // length of A

// Add axiom for length of A
// function array_length(a: Array) : int { n }
// axiom (array_length(A) == n);
// [FEATURE REQUEST] Support native arrays


procedure InsertionSort() returns ()
spec
{
  modifies A;
  modifies n;
  ensures forall i:int, j: int ::
  0 <= i && i <= j && j < n ==> A[i] <= A[j];
  // [FEATURE REQUEST] Support for Lean 4-style quantifiers
  // -- ∀ i, j: int, 0 ≤ i ∧ i ≤ j ∧ j < n → A[i] ≤ A[j]
}
{
  var i : int;
  var j : int;
  var key : int;

  // CLRS-style insertion sort (0-based):
  // for i = 1 to n-1
  // [FEATURE REQUEST] For loop construct
  i := 1;
  while (i < n) {
    key := A[i];
    j := i - 1;

    while (j >= 0 && A[j] > key)
     invariant (
      forall p:int, q:int ::
        0 <= p && p <= q && q < i ==> A[p] <= A[q]
     );
    {
      // map update: A[j+1] := A[j]
      A := A[j + 1 := A[j]];
      // [FEATURE REQUEST] Support for array updates
      // like A[j+1] := A[j]
      j := j - 1;
    }

    // A[j+1] := key
    A := A[j + 1 := key];

    i := i + 1;
  }
};
#end

#eval verify "cvc5" insertionSortPgm
