import StrataBoole.MetaVerifier
import Smt

open Strata

-- Selection sort.
--
-- This example uses a lightweight sortedness spec:
--   `∀ k, 0 ≤ k ∧ k < n-1 → A[k] ≤ A[k+1]`
-- instead of `∀ i j, i ≤ j → A[i] ≤ A[j]`, because it tends to generate
-- simpler verification conditions.
private def selectionSortPgm : StrataDDM.Program :=
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

/-- info:
Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_2
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_1_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_1_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_1_2
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_2
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_2
Property: assert
Result: ✅ pass

Obligation: SelectionSort_ensures_0_527
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" selectionSortPgm (options := .quiet)

-- `smt`/`smt +mono` don't fail fast on these swap-invariant goals (they hang for many
-- minutes rather than erroring), so they're deliberately excluded here.
set_option maxHeartbeats 1000000 in
theorem selectionSortPgm_smtVCsCorrect : Strata.smtVCsCorrectBoole selectionSortPgm := by
  gen_smt_vcs_boole
  all_goals (try (first | omega | trivial | grind))
  -- The outer loop condition `i < n - 1` makes the inner loop's guard `i + 1 < n` true, so
  -- every `if i + 1 < n` in these two swap goals reduces; unfolding `select`/`store` then
  -- lets `grind` split on whether the queried index is one of the two swapped positions.
  case insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1 |
      insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_2 =>
    intro n A1 i A4 j3 m3 j4 m4
    intros
    have hc : i + 1 < n := by omega
    simp only [hc, ↓reduceIte, SmtArray.select, SmtArray.store] at *
    grind
