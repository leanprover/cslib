import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for `for ... to ... by` loop syntax, array-map
assignment, and quantified invariants, via insertion sort.

`requires n <= 1` restricts to arrays too short for a shift to occur: without
it, cvc5 itself returns `unknown` on the shift-invariant-maintenance
obligations (the same class of difficulty as `bubble_sort.lean` and
`selection_sort.lean` under the `SmtArray` encoding), not just the Lean
tactic proof.
-/

private def insertionSortPgm :=
#strata
program Boole;

type Array := Map int int;

var A : Array;
var n : int;

procedure InsertionSort() returns ()
spec
{
  modifies A;
  requires 0 <= n;
  requires n <= 1;
  ensures ∀ i:int, j:int . 0 <= i && i <= j && j < n ==> A[i] <= A[j];
}
{
  var j : int;
  var key : int;

  for i : int := 1 to (n - 1) by 1
    invariant 1 <= i && i <= n + 1
    invariant ∀ p:int, q:int . 0 <= p && p <= q && q < i ==> A[p] <= A[q]
  {
    key := A[i];
    j := i - 1;

    while (j >= 0 && A[j] > key)
      invariant (-1 <= j && j < i)
      invariant (∀ p:int, q:int . 0 <= p && p <= q && q < i ==> A[p] <= A[q])
    {
      A[j + 1] := A[j];
      j := j - 1;
    }

    A[j + 1] := key;
  }
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: InsertionSort_ensures_2_704
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" insertionSortPgm (options := .quiet)

theorem insertionSortPgm_smtVCsCorrect : Strata.smtVCsCorrectBoole insertionSortPgm := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
