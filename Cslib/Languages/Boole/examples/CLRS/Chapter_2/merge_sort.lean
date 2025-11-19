import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

-- CLRS Chapter 1: Merge Sort
-- Pseudo-code adapted from CLRS book (3rd edition), page 31
-- Note: This implementation uses 0-based indexing for arrays.
-- Pseudo-code:
-- MERGE(A, p, q, r)
-- 1  n1 = q - p + 1
-- 2  n2 = r - q
-- 3  let L[1..n1 + 1] and R[1..n2 + 1] be new arrays
-- 4  for i = 1 to n1
-- 5      L[i] = A[p + i - 1]
-- 6  for j = 1 to n2
-- 7      R[j] = A[q + j]
-- 8  L[n1 + 1] = ∞
-- 9  R[n2 + 1] = ∞
-- 10 i = 1
-- 11 j = 1
-- 12 for k = p to r
-- 13     if L[i] ≤ R[j]
-- 14         A[k] = L[i]
-- 15         i = i + 1
-- 16     else
-- 17         A[k] = R[j]
-- 18         j = j + 1

-- MERGE-SORT(A, p, r)
-- 1  if p < r
-- 2      q = ⌊(p + r) / 2⌋
-- 3      MERGE-SORT(A, p, q)
-- 4      MERGE-SORT(A, q + 1, r)
-- 5      MERGE(A, p, q, r)

private def mergeSortPgm :=
#strata
program Boogie;

// An "array of ints" is a map from int to int
type Array := Map int int;

// Global array we’ll sort, and its length
var A : Array;
var n : int;

// Top-level MergeSort: sorts A[0..n-1]
procedure MergeSort() returns ()
spec
{
  modifies A;
  modifies n;
  requires n >= 0;

  // Postcondition: A[0..n-1] is non-decreasing
  ensures forall i:int, j:int ::
    0 <= i && i <= j && j < n ==> A[i] <= A[j];
}
{
  if (n > 1) {
    // Nothing to do for arrays of length 0 or 1
    // Sort the range [0 .. n-1]
    call MergeSortRange(0, n - 1);
  }
};

// Recursive merge sort on subarray A[l..r]
procedure MergeSortRange(l : int, r : int) returns ()
spec
{
  modifies A;
  // We assume the range is inside [0..n-1] and non-empty
  requires 0 <= l && l <= r && r < n;
}
{
  var m : int;

  if (l < r) {
    // m = floor((l + r) / 2)
    m := (l + r) div 2;
    //[FEATURE REQUEST] Support for `/` division operator

    // Recursively sort A[l..m] and A[m+1..r]
    call MergeSortRange(l, m);
    call MergeSortRange(m + 1, r);

    // Merge the two sorted halves
    call Merge(l, m, r);
  }
};

// Merge sorted subarrays A[l..m] and A[m+1..r] back into A[l..r]
procedure Merge(l : int, m : int, r : int) returns ()
spec
{
  modifies A;
  // Basic shape constraints for the subranges
  requires 0 <= l && l <= m && m < r && r < n;

  // Want to specify that A[l..m] and A[m+1..r] are sorted
  // [FEATURE REQUEST] Support for preconditions involving sortedness
  // requires forall i:int, j:int :: l <= i && i <= j && j <= m ==> A[i] <= A[j];
  // requires forall i:int, j:int :: m+1 <= i && i <= j && j <= r ==> A[i] <= A[j];
}
{
  var i : int;
  var j : int;
  var k : int;
  var temp : Array;

  // Copy A[l..r] into temp[l..r]
  k := l;
  while (k <= r) {
    temp := temp[k := A[k]];
    k := k + 1;
  }

  i := l;
  j := m + 1;
  k := l;

  // Merge while both halves are non-empty
  while (i <= m && j <= r) {
    if (temp[i] <= temp[j]) {
      A := A[k := temp[i]];
      i := i + 1;
    } else {
      A := A[k := temp[j]];
      j := j + 1;
    }
    k := k + 1;
  }

  // Copy any remaining elements from the left half
  while (i <= m) {
    A := A[k := temp[i]];
    i := i + 1;
    k := k + 1;
  }

  // Copy any remaining elements from the right half
  while (j <= r) {
    A := A[k := temp[j]];
    j := j + 1;
    k := k + 1;
  }
};
#end

#eval verify "cvc5" mergeSortPgm
