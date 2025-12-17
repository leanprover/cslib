import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- CLRS Exercise 2-4 (Inversions) with merge sort:
--
-- COUNT-INVERSIONS(A, p, r)
--   if p < r
--     q = floor((p + r) / 2)
--     inv_left  = COUNT-INVERSIONS(A, p, q)
--     inv_right = COUNT-INVERSIONS(A, q+1, r)
--     inv_split = MERGE-AND-COUNT(A, p, q, r)
--     return inv_left + inv_right + inv_split
--   else
--     return 0
--
-- MERGE-AND-COUNT merges the two sorted halves and
-- counts split inversions while merging.

private def inversionCountMergeSortPgm :=
#strata
program Boole;

// Arrays as maps from int to int
type Array := Map int int;

// Global array and length
var A : Array;
var n : int;

// Merge two sorted subarrays A[l..m] and A[m+1..r]
// and count split inversions.
procedure MergeAndCount(l : int, m : int, r : int) returns (inv : int)
spec
{
  requires 0 <= l && l <= m && m < r && r < n;
  modifies A;
  ensures inv >= 0;
}
{
  var nL : int;
  var nR : int;
  var i  : int;
  var j  : int;
  var k  : int;
  var L  : Array;
  var R  : Array;

  inv := 0;

  // lengths of left and right halves
  nL := m - l + 1;
  nR := r - m;

  // copy A[l .. m] into L[0 .. nL-1]
  i := 0;
  while (i < nL)
    invariant (0 <= i && i <= nL);
  {
    L := L[i := A[l + i]];
    // [FEATURE REQUEST] Support for simple indexing
    // like L[i] := A[l + i]
    // This is hard to read specially when
    // assigning from a different array.
    i := i + 1;
  }

  // copy A[m+1 .. r] into R[0 .. nR-1]
  j := 0;
  while (j < nR)
    invariant (0 <= j && j <= nR);
  {
    R := R[j := A[m + 1 + j]];
    // [FEATURE REQUEST] Support for simple indexing
    // [Style] like R[j] := A[m + 1 + j]
    j := j + 1;
  }

  // merge L and R back into A[l..r], counting inversions
  i := 0;
  j := 0;
  k := l;

  while (i < nL && j < nR)
    // invariant (0 <= i && i <= nL);
    // invariant (0 <= j && j <= nR);
    // invariant (l <= k && k <= r + 1);
    invariant (inv >= 0);
    // [FEATURE REQUEST]
    // [Style] Support for multiple invariants
  {
    if (L[i] <= R[j]) {
      A := A[k := L[i]];
      i := i + 1;
    } else {
      A := A[k := R[j]];
      j := j + 1;
      // all remaining elements in L[i..nL-1] form inversions with R[j-1]
      inv := inv + (nL - i);
    }
    k := k + 1;
  }

  // copy any remaining L
  while (i < nL)
    //invariant (0 <= i && i <= nL);
    invariant (l <= k && k <= r + 1);
  {
    A := A[k := L[i]];
    i := i + 1;
    k := k + 1;
  }

  // copy any remaining R
  while (j < nR)
    //invariant (0 <= j && j <= nR);
    invariant (l <= k && k <= r + 1);
  {
    A := A[k := R[j]];
    j := j + 1;
    k := k + 1;
  }
};

// Recursive merge-sort + inversion count on A[l..r]
procedure MergeSortInv(l : int, r : int) returns (inv : int)
spec
{
  requires 0 <= l && l <= r && r < n;
  modifies A;
  ensures inv >= 0;
}
{
  var m      : int;
  var invL   : int;
  var invR   : int;
  var invSpl : int;

  if (l >= r) {
    inv := 0;
  } else {
    m := (l + r) div 2;
    // [FEATURE REQUEST]
    // [Style] Support for a simple division operator

    call invL := MergeSortInv(l, m);
    // [FEATURE REQUEST]
    // [Style] Support for a simple function  call syntax
    // like invL := MergeSortInv(l, m)
    call invR := MergeSortInv(m + 1, r);
    call invSpl := MergeAndCount(l, m, r);

    inv := invL + invR + invSpl;
  }
};

// Top-level procedure: sorts A[0..n-1] and returns inversion count
procedure InversionCountMergeSort() returns (inv : int)
spec
{
  requires n >= 0;
  modifies A;
  ensures inv >= 0;
  ensures forall i:int, j:int ::
    0 <= i && i <= j && j < n ==> A[i] <= A[j];
}
{
  if (n <= 1) {
    inv := 0;
  } else {
    call inv := MergeSortInv(0, n - 1);
  }
};
#end

#eval verify "cvc5" inversionCountMergeSortPgm
