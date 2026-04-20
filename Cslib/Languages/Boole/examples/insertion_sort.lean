import Strata.MetaVerifier

------------------------------------------------------------
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
  // Adjacent-order formulation of sortedness (simpler VCs than ∀ i j, ...).
  ensures forall k:int ::
    0 <= k && k < n - 1 ==> A[k] <= A[k + 1];
  // [FEATURE REQUEST] Support for Lean 4-style quantifiers
  // -- ∀ k: int, 0 ≤ k ∧ k < n - 1 → A[k] ≤ A[k + 1]
}
{
  var i : int;
  var j : int;
  var key : int;

  if (n > 1) {
    // CLRS-style insertion sort (0-based):
    // for i = 1 to n-1
    // [FEATURE REQUEST] For loop construct
    i := 1;
    while (i < n)
      invariant 1 <= i && i <= n
      invariant (
        forall k:int ::
          0 <= k && k < i - 1 ==> A[k] <= A[k + 1]
      )
    {
      key := A[i];
      j := i - 1;

      // We do one shift outside the loop so that, inside the loop,
      // the prefix `A[0..i]` is sorted (with `key` stored separately).
      if (A[j] > key) {
        A := A[j + 1 := A[j]];
        j := j - 1;

        while (j >= 0 && A[j] > key)
          invariant -1 <= j && j < i
          invariant (
            forall k:int ::
              0 <= k && k < i ==> A[k] <= A[k + 1]
          )
          invariant (
            forall k:int :: j < k && k <= i ==> A[k] > key
          )
        {
          A := A[j + 1 := A[j]];
          j := j - 1;
        }
      }

      A := A[j + 1 := key];
      i := i + 1;
    }
  }
};
#end

-- Optional: run the SMT-based pipeline if `cvc5` is on your `PATH`.
-- Note: use `#eval!` if your dependency graph contains `sorry`.
-- #eval! Strata.Boole.verify "cvc5" insertionSortPgm

set_option maxHeartbeats 1000000 in
example : Strata.smtVCsCorrect insertionSortPgm := by
  gen_smt_vcs
  all_goals grind (config := { splits := 20, gen := 10 })

end Strata
