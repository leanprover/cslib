import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- Selection sort.
--
-- This example uses a lightweight sortedness spec:
--   `∀ k, 0 ≤ k ∧ k < n-1 → A[k] ≤ A[k+1]`
-- instead of `∀ i j, i ≤ j → A[i] ≤ A[j]`, because it tends to generate
-- simpler verification conditions.
private def selectionSortPgm : Strata.Program :=
#strata
program Boole;

type Array := Map int int;

var A : Array;
var n : int;

procedure SelectionSort() returns ()
spec
{
  modifies A;
  // Adjacent-order sortedness.
  ensures forall k:int :: 0 <= k && k < n - 1 ==> A[k] <= A[k + 1];
}
{
  var i : int;
  var j : int;
  var m : int;
  var tmp : int;

  if (n > 1) {
    i := 0;

    while (i < n - 1)
      invariant 0 <= i && i <= n - 1
      // Prefix `A[0..i]` is sorted.
      invariant forall k:int :: 0 <= k && k < i ==> A[k] <= A[k + 1]
      // Every element already placed in the prefix is <= every element remaining in the suffix.
      invariant forall p:int, q:int :: 0 <= p && p < i && i <= q && q < n ==> A[p] <= A[q]
    {
      m := i;
      j := i + 1;

      // Find an index `m` holding a minimum of `A[i..n-1]`.
      while (j < n)
        invariant i <= m && m < n
        invariant i < j && j <= n
        invariant forall k:int :: i <= k && k < j ==> A[m] <= A[k]
      {
        if (A[j] < A[m]) {
          m := j;
        }
        j := j + 1;
      }

      if (m != i) {
        tmp := A[i];
        A := A[i := A[m]];
        A := A[m := tmp];
      }

      i := i + 1;
    }
  }
};
#end

set_option maxHeartbeats 1000000 in
example : Strata.smtVCsCorrect selectionSortPgm := by
  gen_smt_vcs
  all_goals grind

end Strata
