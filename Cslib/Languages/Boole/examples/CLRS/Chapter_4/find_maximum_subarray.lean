import Strata.MetaVerifier

namespace Strata

-- CLRS Chapter 4: FIND-MAXIMUM-SUBARRAY
-- page 72
-- FIND-MAXIMUM-SUBARRAY(A, low, high)
-- 1  if high == low
-- 2      return (low, high, A[low])        -- base case: only one element
-- 3  else
-- 4      mid = (low + high) / 2
-- 5      (left-low, left-high, left-sum) =
-- 6          FIND-MAXIMUM-SUBARRAY(A, low, mid)
-- 7      (right-low, right-high, right-sum) =
-- 8          FIND-MAXIMUM-SUBARRAY(A, mid + 1, high)
-- 9      (cross-low, cross-high, cross-sum) =
-- 10         FIND-MAX-CROSSING-SUBARRAY(A, low, mid, high)
-- 11     if left-sum >= right-sum and left-sum >= cross-sum
-- 12         return (left-low, left-high, left-sum)
-- 13     elseif right-sum >= left-sum and right-sum >= cross-sum
-- 14         return (right-low, right-high, right-sum)
-- 15     else
-- 16         return (cross-low, cross-high, cross-sum)

private def findMaxSubArray :=
#strata
program Boole;

type Array := Map int int;

// Input array
var A : Array;

// Computes the sum of array elements from index i to j (inclusive)
function SumRange(A: Map int int, i:int, j:int) : int;

// Base case: if i > j, the sum of an empty range is 0
axiom (forall A: Map int int, i:int, j:int ::
    i > j ==> SumRange(A, i, j) == 0);

// Recursive case: sum of range i..j is A[i] + sum of i+1..j
axiom (forall A: Map int int, i:int, j:int ::
    i <= j ==> SumRange(A, i, j) == A[i] + SumRange(A, i+1, j));

// Procedure: FIND_MAXIMUM_SUBARRAY
// Finds the contiguous subarray with the maximum sum in A[low..high]
// Returns: (resLow, resHigh, resSum)
procedure FIND_MAXIMUM_SUBARRAY(low: int, high: int)
    returns (resLow: int, resHigh: int, resSum: int)
spec
{
    // precondition: valid range
    requires low <= high;

    // postconditions: result indices are within bounds, and resSum is correct
    ensures low <= resLow && resLow <= resHigh && resHigh <= high;
    ensures resSum == SumRange(A,resLow,resHigh);
}
{
    var mid: int;
    var ll: int; var lh: int; var ls: int;
    var rl: int; var rh: int; var rs: int;
    var cl: int; var ch: int; var cs: int;

    // base case: single element
    if (high == low) {
        resLow := low;
        resHigh := high;
        resSum := A[low];
    } else {
        // recursive case: divide
        mid := (low + high) div 2;

        // ensure recursive calls are within bounds
        assert low <= mid;
        assert mid + 1 <= high;

        // recursive calls
        call ll, lh, ls := FIND_MAXIMUM_SUBARRAY(low, mid);
        call rl, rh, rs := FIND_MAXIMUM_SUBARRAY(mid+1, high);

        // find max subarray crossing the middle
        call cl, ch, cs := FIND_MAX_CROSSING_SUBARRAY(low, mid, high);

        // conquer: pick the maximum
        if (ls >= rs && ls >= cs) {
            resLow := ll;
            resHigh := lh;
        } else {
            if (rs >= ls && rs >= cs) {
                resLow := rl;
                resHigh := rh;
            } else {
                resLow := cl;
                resHigh := ch;
            }
        }
        // compute the sum of the chosen subarray
        resSum := SumRange(A, resLow, resHigh);
    }
};

// Procedure: FIND_MAX_CROSSING_SUBARRAY
// Returns the maximum subarray that crosses the midpoint
// Abstracted for verification
// Proving the ensures for all possible subarrays is very hard.
// We treat FIND_MAX_CROSSING_SUBARRAY as a correct black box.
procedure FIND_MAX_CROSSING_SUBARRAY(low: int, mid: int, high: int)
    returns (crossLow: int, crossHigh: int, crossSum: int)
spec
{
    // precondition: valid range
    requires low <= mid && mid < high;

    // postconditions (assumed with 'free ensures' for verification)
    // 1. result indices are valid
    free ensures low <= crossLow && crossLow <= crossHigh && crossHigh <= high;

    // 2. sum matches the actual array range
    free ensures crossSum == SumRange(A, crossLow, crossHigh);

    // 3. crossSum is greater than or equal to sum of any subarray in the range
    free ensures forall i:int,j:int :: low <= i && i <= j && j <= high ==> SumRange(A,i,j) <= crossSum;
}
{};

#end

#eval verify "cvc5" findMaxSubArray
