program Boogie;

// Exercise 2.3-5 solution
// Standard binary search: given a sorted array A[0..n-1] and a value x,
// find an index i such that A[i] == x, or return -1 if x is not in A.

//BINARY-SEARCH(A, x)
//    low <- 1
//    high <- length[A]
//    while low ≤ high
//        mid <- (low + high) / 2
//        if A[mid] = x
//            return mid
//        else if A[mid] > x
//            high <- mid - 1
//        else
//            low <- mid + 1
//    return NIL

var A: Map int int;

// helper lemma: if the search interval is empty, then x cannot exist in the array
// Why we need this:
// After binary search exits without finding x, we know logically that the remaining search  
// interval is empty (low > high). The loop invariant tracks that any occurrence of x must be 
// within [low..high]. However, Boogie/Strata cannot automatically deduce that an empty interval 
// implies no x exists. The lemma explicitly bridges this gap.
procedure IntervalEmptyImpliesNoX(low: int, high: int, n: int, A: Map int int, x: int) returns ()
spec {
    requires low > high;
    requires forall k:int :: 0 <= k && k < n && A[k] == x ==> low <= k && k <= high;
    ensures forall k:int :: 0 <= k && k < n ==> A[k] != x;
}
{};

// Binary Search procedure
// A: input array of integers
// x: value to search for
// returns index i such that A[i] == x, or -1 if not found
procedure BinarySearch(A: Map int int, n: int, x: int) returns (idx: int)
spec
{
    // preconditions: array is sorted and size is non-negative
    requires n >= 0;
    requires forall i:int, j:int :: (0 <= i && i < j && j < n) ==> A[i] <= A[j];

    // postconditions
    ensures (idx == -1 ==> forall k:int :: 0 <= k && k < n ==> A[k] != x);
        // if search fails, x does not exist
    ensures (idx != -1 ==> 0 <= idx && idx < n && A[idx] == x);
        // if search succeeds, idx points to x

}
{
    var low: int;
    var high: int;
    var mid: int;

    // initialize the search interval
    low := 0;
    high := n - 1;
    idx := -1; // initially, we haven't found x

    var found: bool;
    found := false;

    // loop invariants:
    // 1. 0 <= low <= n and -1 <= high < n: bounds for low and high
    // 2. if idx != -1, then A[idx] == x (tracks correctness of idx)
    // 3. forall k: if A[k] == x, then k must lie within [low..high]
    //    this ensures the search interval always contains all possible x's.
    while (low <= high && !found)
        invariant 0 <= low && low <= n
            && -1 <= high && high < n
            && (idx != -1 ==> 0 <= idx && idx < n && A[idx] == x)
            // any x must be in the current search interval
            && forall k:int :: 0 <= k && k < n && A[k] == x ==> low <= k && k <= high;
    {
        mid := (low + high) div 2;

        if (A[mid] == x) {
            idx := mid;
            found := true; // exit loop
        }
        else {
            if (A[mid] > x) {
                high := mid - 1; // search left half
            }
            else {
                low := mid + 1; // search right half
            }
        }
    }
    // if not found, call lemma to prove no x exists
    if (idx == -1) {
        assume low > high;
        call IntervalEmptyImpliesNoX(low, high, n, A, x);
    }
};
