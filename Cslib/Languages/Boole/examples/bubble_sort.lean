import StrataBoole.MetaVerifier
import Smt

open Strata

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

/-- info:
Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_1
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

Obligation: BubbleSort_ensures_0_461
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" bubbleSortPgm (options := .quiet)

-- `omega`/`trivial` close the goals that are pure arithmetic or a direct restatement of a
-- hypothesis; the five named cases below are the genuine swap-invariant-maintenance goals, each
-- closed by case-splitting on whether the conditional swap fired and, for the inner loop, on how
-- the queried index relates to the two swapped positions `j-1`/`j`, then reading off the
-- resulting array value via `SmtArray.select_store_self`/`select_store_of_ne`.
set_option maxHeartbeats 1000000 in
theorem bubbleSortPgm_smtVCsCorrect : Strata.smtVCsCorrectBoole bubbleSortPgm := by
  gen_smt_vcs_boole
  all_goals (try (first | omega | trivial))
  case insertLoopInvAssert_entry_invariant_loop_1_1 =>
    intro A1 n1 i1 A4 _ _ _ _ _ x hx
    have hxeq : x = n1 - 1 := by omega
    rw [hxeq]
    omega
  case insertLoopInvAssert_entry_invariant_loop_1_2 =>
    intro A1 n1 i1 A4 _ _ _ _ H
    exact H
  case insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_2 =>
    intro A1 n1 i1 A4 j3 A6 _ _ _ _ _ _ _ _ _ _ _ _ H5 _ _ x y hxy
    by_cases hcond : A6.select j3 < A6.select (j3 - 1)
    · simp only [if_pos hcond]
      simp (discharger := omega) only [SmtArray.select_store_of_ne]
      by_cases hy1 : y = j3 - 1
      · subst hy1
        simp only [SmtArray.select_store_self]
        exact H5 x j3 (by omega)
      · by_cases hy2 : y = j3
        · subst hy2
          simp (discharger := omega) only [SmtArray.select_store_of_ne, SmtArray.select_store_self]
          exact H5 x (y - 1) (by omega)
        · simp (discharger := omega) only [SmtArray.select_store_of_ne]
          exact H5 x y hxy
    · rw [if_neg hcond]
      exact H5 x y hxy
  case insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_1 =>
    intro A1 n1 i1 A4 j3 A6 _ _ _ _ _ _ _ _ _ _ _ H4 _ _ _ bv10 hbv10
    by_cases hcond : A6.select j3 < A6.select (j3 - 1)
    · simp only [if_pos hcond]
      simp (discharger := omega) only [SmtArray.select_store_self]
      by_cases hb1 : bv10 = j3 - 1
      · subst hb1
        simp (discharger := omega) only [SmtArray.select_store_self]
        omega
      · by_cases hb2 : bv10 = j3
        · subst hb2
          simp (discharger := omega) only [SmtArray.select_store_of_ne, SmtArray.select_store_self]
          omega
        · simp (discharger := omega) only [SmtArray.select_store_of_ne]
          exact H4 bv10 (by omega)
    · rw [if_neg hcond]
      by_cases hb1 : bv10 = j3 - 1
      · subst hb1; omega
      · have := H4 bv10 (by omega)
        omega
  case insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1 =>
    intro A1 n1 i1 A4 j3 A6 j4 A8
    intros
    rename_i hJ Hmin Hsorted hnJ b0 b1 hb
    have hc : n1 - 1 > i1 := by omega
    simp only [hc, ↓reduceIte] at hJ Hmin Hsorted hnJ ⊢
    by_cases hlt : b0 < i1
    · exact Hsorted b0 b1 ⟨hb.1, hlt⟩
    · have hb0 : b0 = j4 := by omega
      rw [hb0]
      exact Hmin b1 (by omega)
  case BubbleSort_ensures_0_461 =>
    intro A1 n1 i1 A4 j3 A6 j4 A8 i2 A10
    intros
    rename_i Hfinal hnI b0 b1 hb
    by_cases houter : 0 < n1 - 1 <;> simp only [houter, ↓reduceIte] at Hfinal hnI ⊢
    · by_cases hlt : b0 < i2
      · exact Hfinal b0 b1 ⟨hb, hlt⟩
      · have heq : b0 = b1 := by omega
        rw [heq]
        exact Int.le_refl _
    · have heq : b0 = b1 := by omega
      rw [heq]
      exact Int.le_refl _
