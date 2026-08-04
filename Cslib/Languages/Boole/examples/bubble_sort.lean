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

Obligation: entry_invariant_1_2
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_2
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
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
  case entry_invariant_1_1 =>
    intro A1 n1 i1 A4 _ _ _ _ _ x hx
    have hxeq : x = n1 - 1 := by omega
    rw [hxeq]
    omega
  case entry_invariant_1_2 =>
    intro A1 n1 i1 A4 _ _ _ _ H
    exact H
  case arbitrary_iter_maintain_invariant_1_2 =>
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
  case arbitrary_iter_maintain_invariant_1_1 =>
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
  case arbitrary_iter_maintain_invariant_0_1 =>
    intro A1 n1 i1 A4 j3 A6 j4 A8 _ h1 h2 h3 H_A4pre h4 H_entry2 H5'
    have hc : n1 - 1 > i1 := by omega
    simp only [if_pos hc] at *
    intro _ _ _ _ _ _ _ _ _ Hj4run Hj4pre _ bv13 bv14 hbv
    by_cases hb : bv13 < i1
    · exact Hj4pre bv13 bv14 ⟨hbv.1, hb⟩
    · have hbeq : bv13 = i1 := by omega
      have hj4eq : j4 = i1 := by omega
      rw [hbeq, ← hj4eq]
      exact Hj4run bv14 (by omega)
  case BubbleSort_ensures_0_461 =>
    intro A1 n1 i1 A4 j3 A6 j4 A8
    by_cases houter : 0 < n1 - 1
    · simp only [if_pos houter] at *
      intro i2 A10 _ _ h2 h3
      have hc2 : n1 - 1 > i1 := by omega
      simp only [if_pos hc2] at *
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi2a hi2b Hfinal _ bv15 bv16 hbv
      by_cases hb : bv15 < i2
      · exact Hfinal bv15 bv16 ⟨hbv, hb⟩
      · have heq : bv15 = i2 := by omega
        have heq2 : bv16 = i2 := by omega
        rw [heq, heq2]
        omega
    · simp only [if_neg houter, true_implies] at *
      intro i2 A10 _ _ bv15 bv16 hbv
      have heq : bv15 = bv16 := by omega
      rw [heq]
      omega
