/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Separation.Defs
import Mathlib.Data.Int.Interval

set_option linter.style.emptyLine false

/-!
# Integer-Specific Helper Lemmas for Separation

Provides integer-arithmetic lemmas needed by the separation proof:
- Finite intervals in Z
- Well-ordering arguments for finding first failure points
- Direct witness constructions for Until/Since

## References

- GHR94, Chapter 10.2: These lemmas support the key Z-dependent steps
  (particularly Lemma 10.2.2, the negation equivalence)
-/

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Finite Interval Properties -/

/-- In Z, bounded open intervals (t, s) with t < s are finite. -/
theorem Int.Ioo_finite' (t s : Int) (_h : t < s) :
    Set.Finite (Set.Ioo t s) :=
  Set.Finite.ofFinset (Finset.Ioo t s) (fun x => by
    simp [Finset.mem_Ioo, Set.mem_Ioo])

/-- In Z, the interval (t, t+1) is empty (discreteness). -/
theorem Int.Ioo_succ_empty (t : Int) :
    Set.Ioo t (t + 1) = ∅ := by
  ext x; simp [Set.mem_Ioo]; omega

/-- In Z, if t < s then t + 1 ≤ s. -/
theorem Int.succ_least (t s : Int) (h : t < s) :
    t + 1 ≤ s := by omega

/-- In Z, every non-empty set bounded below has an infimum.
    If P holds for some n > t, then there is a least such n.
    This is the KEY INTEGER-SPECIFIC lemma used in
    Lemma 10.2.2. -/
theorem Int.exists_least_above
    {pred : Int → Prop} {t : Int}
    (hex : ∃ n, t < n ∧ pred n) [DecidablePred pred] :
    ∃ m, t < m ∧ pred m ∧
      ∀ k, t < k → k < m → ¬pred k := by
  obtain ⟨n, htn, hpn⟩ := hex
  let Q : ℕ → Prop := fun k => pred (t + 1 + ↑k)
  have hQ_dec : DecidablePred Q :=
    fun k => inferInstanceAs (Decidable (pred (t + 1 + ↑k)))
  have hQ_ex : ∃ k : ℕ, Q k := by
    refine ⟨(n - t - 1).toNat, ?_⟩
    change pred (t + 1 + ↑((n - t - 1).toNat))
    convert hpn using 1; omega
  let m_nat := @Nat.find Q hQ_dec hQ_ex
  have hm_spec := @Nat.find_spec Q hQ_dec hQ_ex
  have hm_min := @Nat.find_min Q hQ_dec hQ_ex
  refine ⟨t + 1 + ↑m_nat, by omega, hm_spec, ?_⟩
  intro k htk hkm
  have hk_idx : (k - t - 1).toNat < m_nat := by omega
  exact fun hpk => hm_min hk_idx (by
    change pred (t + 1 + ↑((k - t - 1).toNat))
    convert hpk using 1; omega)

/-- Dual: If P holds for some n < t, then there is a greatest
    such n. -/
theorem Int.exists_greatest_below
    {pred : Int → Prop} {t : Int}
    (hex : ∃ n, n < t ∧ pred n) [DecidablePred pred] :
    ∃ m, m < t ∧ pred m ∧
      ∀ k, m < k → k < t → ¬pred k := by
  obtain ⟨n, hnt, hpn⟩ := hex
  let Q : ℕ → Prop := fun k => pred (t - 1 - ↑k)
  have hQ_dec : DecidablePred Q :=
    fun k => inferInstanceAs (Decidable (pred (t - 1 - ↑k)))
  have hQ_ex : ∃ k : ℕ, Q k := by
    refine ⟨(t - n - 1).toNat, ?_⟩
    change pred (t - 1 - ↑((t - n - 1).toNat))
    convert hpn using 1; omega
  let m_nat := @Nat.find Q hQ_dec hQ_ex
  have hm_spec := @Nat.find_spec Q hQ_dec hQ_ex
  have hm_min := @Nat.find_min Q hQ_dec hQ_ex
  refine ⟨t - 1 - ↑m_nat, by omega, hm_spec, ?_⟩
  intro k hmk hkt
  have hk_idx : (t - k - 1).toNat < m_nat := by omega
  intro hpk
  have : ¬Q (t - k - 1).toNat := hm_min hk_idx
  exact this (by
    change pred (t - 1 - ↑((t - k - 1).toNat))
    convert hpk using 1; omega)

/-- Non-decidable version of exists_least_above.
    Uses classical logic. -/
theorem Int.exists_least_above'
    {pred : Int → Prop} {t : Int}
    (hex : ∃ n, t < n ∧ pred n) :
    ∃ m, t < m ∧ pred m ∧
      ∀ k, t < k → k < m → ¬pred k := by
  haveI : DecidablePred pred := Classical.decPred pred
  exact Int.exists_least_above hex

/-! ## Direct Witness Constructions -/

/-- Key property: if phi holds at s and psi holds on (t,s),
    then U(phi, psi) holds at t. -/
theorem until_witness_construction
    (M : IntStructure Atom) (t s : Int) (hts : t < s)
    (phi psi : Formula Atom)
    (hphi : int_truth M s phi)
    (hpsi : ∀ r : Int,
      t < r → r < s → int_truth M r psi) :
    int_truth M t (.untl phi psi) :=
  ⟨s, hts, hphi, hpsi⟩

/-- Dual: if phi holds at s and psi holds on (s,t),
    then S(phi, psi) holds at t. -/
theorem since_witness_construction
    (M : IntStructure Atom) (t s : Int) (hst : s < t)
    (phi psi : Formula Atom)
    (hphi : int_truth M s phi)
    (hpsi : ∀ r : Int,
      s < r → r < t → int_truth M r psi) :
    int_truth M t (.snce phi psi) :=
  ⟨s, hst, hphi, hpsi⟩

/-! ## Top/True Equivalences -/

/-- neg bot is always true in int_truth. -/
theorem neg_bot_true
    (M : IntStructure Atom) (t : Int) :
    int_truth M t (Formula.neg (Atom := Atom) .bot) := by
  simp [int_truth]

/-- S(a, neg bot) iff some_past a. -/
theorem since_top_is_past (a : Formula Atom) :
    int_equiv (.snce a (Formula.neg .bot))
      (Formula.some_past a) :=
  int_equiv_refl _

/-- U(a, neg bot) iff some_future a. -/
theorem until_top_is_future (a : Formula Atom) :
    int_equiv (.untl a (Formula.neg .bot))
      (Formula.some_future a) :=
  int_equiv_refl _

end Cslib.Logic.Bimodal.Metalogic.Separation
