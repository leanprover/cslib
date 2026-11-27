/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.CycleCount
public import Cslib.Foundations.RelationAlgebra.IsoClass
public import Cslib.Foundations.RelationAlgebra.SymmetricCycles

/-!
# Asymptotic enumeration of finite relation algebras

The enumeration is indexed by the total number of Boolean atoms and counts isomorphism classes.
The nonintegral classes have at most `k - 2` diversity atoms. Burnside's lemma bounds the number
of their diversity cycle orbits by `k.choose 3`. For the lower bound on all classes, a symmetric
integral table has `(k + 1).choose 3` possible diversity cycles. At least half of these tables
eventually satisfy associativity, and a class has at most `k ^ k` labellings. The gap of
`k.choose 2` in the two exponents absorbs the cost of labelling and choosing the identity data.

See [James Koussas, *Finite Relation Algebras*](https://arxiv.org/pdf/2202.01959), §4.
-/

@[expose] public section

namespace Cslib.RelationAlgebra
namespace IsoClass

private theorem card_le_of_fiber_bound {X Y : Type*} [Finite X] [Finite Y] (f : X → Y) (m : ℕ)
    (h : ∀ y, Nat.card {x // f x = y} ≤ m) : Nat.card X ≤ Nat.card Y * m := by
  classical
  let _ := Fintype.ofFinite Y
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun y _ => h y)

private abbrev Bad (k : ℕ) := {q : ofAtoms k // ¬ IsIntegral q}

private noncomputable def signature {k : ℕ} (q : Bad k) :=
  let S := q.val.out.val
  (S.conv, S.id, S.rightId)

private theorem card_signature_fiber_le {k : ℕ} (hk : 0 < k)
    (s : (Fin k → Fin k) × Set (Fin k) × (Fin k → Fin k)) :
    Nat.card {q : Bad k // signature q = s} ≤ 2 ^ (k.choose 3) := by
  classical
  let X := {q : Bad k // signature q = s}
  rcases isEmpty_or_nonempty X with hempty | hnonempty
  · exact (Nat.card_of_isEmpty (α := X)).le.trans (Nat.zero_le _)
  let q₀ := hnonempty.some
  let S (x : X) := x.val.val.out.val
  have he (x y : X) := x.prop.trans y.prop.symm
  have hf (x y : X) : (S x).conv = (S y).conv := congrArg Prod.fst (he x y)
  have hi (x y : X) : (S x).id = (S y).id := congrArg (fun t => t.2.1) (he x y)
  have hr (x y : X) : (S x).rightId = (S y).rightId := congrArg (fun t => t.2.2) (he x y)
  let I := (S q₀).id
  let D := ↥(Iᶜ : Set (Fin k))
  let f (x : D) : D := ⟨(S q₀).conv x.val, fun hx => x.prop <| by
    have h := (S q₀).conv_eq_self_of_mem_id hx
    rw [(S q₀).conv_conv] at h
    exact h.symm ▸ hx⟩
  have hinv : Function.Involutive f := fun x => Subtype.ext ((S q₀).conv_conv x)
  have hj (x : X) (a : D) : (f a).val = (S x).conv a := congrFun (hf q₀ x) a
  let encode (x : X) := (S x).orbitCycles hinv Subtype.val (hj x)
  have inj : Function.Injective encode := by
    intro x y hxy
    have hS : S x = S y := (S x).ext_of_diversity (hf x y) (hi x y) (hr x y) <| by
      intro a ha b hb c hc
      rw [hi x q₀] at ha hb hc
      let t : AtomStructure.Triangle f := ⟨![⟨a, ha⟩, ⟨b, hb⟩, f ⟨c, hc⟩]⟩
      let _ := AtomStructure.Triangle.action hinv
      have h := Set.ext_iff.mp hxy (Quotient.mk (MulAction.orbitRel _ _) t)
      change (a, b, (S x).conv ((f ⟨c, hc⟩).val)) ∈ (S x).cycles ↔
        (a, b, (S y).conv ((f ⟨c, hc⟩).val)) ∈ (S y).cycles at h
      simpa only [← hj, hinv _] using h
    apply Subtype.ext
    apply Subtype.ext
    exact x.val.val.out_eq.symm.trans ((congrArg (Quotient.mk _) (Subtype.ext hS)).trans
      y.val.val.out_eq)
  have hI : 2 ≤ I.ncard := by
    have hbad := q₀.val.prop
    rw [← q₀.val.val.out_eq] at hbad
    change ¬ RelationAlgebra.IsIntegral (ComplexAlgebra (S q₀)) at hbad
    have hn : I.ncard ≠ 1 := fun h => hbad ((ComplexAlgebra.isIntegral_iff _).mpr
      (Set.ncard_eq_one.mp h))
    obtain ⟨e, he, _⟩ := (S q₀).exists_id_cycle_right ⟨0, hk⟩
    have hp : 0 < I.ncard := Finite.card_pos_iff.mpr ⟨⟨e, he⟩⟩
    omega
  have hD : Nat.card D + 2 ≤ k := by
    have h := I.ncard_add_ncard_compl
    rw [Nat.card_fin] at h
    change I.ncard + Nat.card D = k at h
    omega
  calc
    Nat.card X ≤ Nat.card (Set (AtomStructure.Triangle.Orbit hinv)) :=
      Nat.card_le_card_of_injective _ inj
    _ = 2 ^ Nat.card (AtomStructure.Triangle.Orbit hinv) := by
      let _ := Fintype.ofFinite (AtomStructure.Triangle.Orbit hinv)
      simp [Nat.card_eq_fintype_card]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) <|
      (AtomStructure.Triangle.card_orbit_le_choose hinv).trans (Nat.choose_le_choose _ hD)

/-- A nonintegral algebra has at most `k - 2` diversity atoms. Its identity cycles are
determined by its right identity map. The remaining cycles form a set of triangle orbits. -/
theorem card_nonintegral_le {k : ℕ} (hk : 0 < k) :
    Nat.card {q : ofAtoms k // ¬ IsIntegral q} ≤
      k ^ k * (2 ^ k * k ^ k) * 2 ^ (k.choose 3) := by
  classical
  have h := card_le_of_fiber_bound (@signature k) _ (card_signature_fiber_le hk)
  simpa [Nat.card_prod, Nat.card_eq_fintype_card] using h

open Filter
open scoped Topology

private abbrev Good (n : ℕ) := {T : SymmetricCycles.Table (Fin n) // SymmetricCycles.HasWitnesses T}

private noncomputable def classOfTable {n : ℕ} (T : Good n) : ofAtoms (n + 1) :=
  letI := SymmetricCycles.lawful_of_hasWitnesses T.prop
  ofAlgebra (A := ComplexAlgebra (SymmetricCycles.atomStructure T.val)) <| by
    rw [ComplexAlgebra.card_atoms]
    simp [Nat.card_eq_fintype_card]

private theorem card_good_le (n : ℕ) :
    Nat.card (Good n) ≤ Nat.card (ofAtoms (n + 1)) * (n + 1) ^ (n + 1) := by
  apply card_le_of_fiber_bound classOfTable
  intro q
  let X := {T : Good n // classOfTable T = q}
  rcases isEmpty_or_nonempty X with hempty | hnonempty
  · exact (Nat.card_of_isEmpty (α := X)).le.trans (Nat.zero_le _)
  let S (x : X) := SymmetricCycles.atomStructure x.val.val
  let inst (x : X) : LawfulAtomStructure (S x) := SymmetricCycles.lawful_of_hasWitnesses x.val.prop
  let y := hnonempty.some
  have he (x : X) : Nonempty (RelationAlgebraEquiv (ComplexAlgebra (S x)) (ComplexAlgebra (S y))) :=
    (ofAlgebra_eq_iff ..).mp (x.prop.trans y.prop.symm)
  let f (x : X) : Option (Fin n) → Option (Fin n) := ComplexAlgebra.atomEquiv (S x) (he x).some
  have hf (x : X) (a b c : Option (Fin n)) :
      (a, b, c) ∈ (S x).cycles ↔ (f x a, f x b, f x c) ∈ (S y).cycles :=
    (ComplexAlgebra.atomEquiv_mem_cycles (S x) (he x).some a b c).symm
  have hinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    ext t
    obtain ⟨a, t, rfl⟩ := t.exists_eq_cons_of_succ
    obtain ⟨b, t, rfl⟩ := t.exists_eq_cons_of_succ
    obtain ⟨c, t, rfl⟩ := t.exists_eq_cons_of_succ
    rw [Sym.eq_nil_of_card_zero t]
    exact (hf u (some b) (some c) (some a)).trans
      (huv ▸ (hf v (some b) (some c) (some a)).symm)
  have h := Nat.card_le_card_of_injective f hinj
  simpa [Nat.card_fun, Nat.card_eq_fintype_card] using h

/-- There are at least half as many classes as symmetric labelled tables divided by
the number of possible relabellings (bounded here by all functions on the atoms). -/
theorem eventually_le_card_mul_relabellings :
    ∀ᶠ k : ℕ in atTop, (2 : ℝ) ^ ((k + 1).choose 3) / 2 ≤
      Nat.card (ofAtoms k) * (k : ℝ) ^ k := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp SymmetricCycles.eventually_half_le_card_hasWitnesses
  filter_upwards [eventually_ge_atTop (N + 1)] with k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  exact (hN n (by omega)).trans (by exact_mod_cast card_good_le n)

private theorem eventually_pow_le_choose :
    ∀ᶠ k : ℕ in atTop, (4 * k ^ 3) ^ k ≤ 2 ^ k.choose 2 := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 6 (r := (2 : ℝ)) (by norm_num)
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 32)]
    with k hk h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  let k := n + 1
  change (k : ℝ) ^ 6 / 2 ^ k ≤ _ at h
  have h' := (div_le_iff₀ (by positivity)).mp h
  have hs : 2 * (4 * k ^ 3) ^ 2 ≤ 2 ^ k := by
    exact_mod_cast (show 2 * (4 * (k : ℝ) ^ 3) ^ 2 ≤ 2 ^ k by linarith only [h'])
  change 2 * _ ≤ 2 ^ (n + 1) at hs
  rw [pow_succ 2 n] at hs
  have hbase : (4 * k ^ 3) ^ 2 ≤ 2 ^ n := by omega
  have hc : k * n = k.choose 2 * 2 := by
    simpa [k] using Nat.add_one_mul_choose_eq n 1
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Nat.zero_le _)
  calc
    ((4 * k ^ 3) ^ k) ^ 2 = ((4 * k ^ 3) ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
    _ ≤ (2 ^ n) ^ k := Nat.pow_le_pow_left hbase k
    _ = (2 ^ k.choose 2) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n k, hc]

/-- Eventually the proportion of nonintegral classes is at most `2 / 2^k`. -/
theorem eventually_two_pow_mul_card_nonintegral_le :
    ∀ᶠ k : ℕ in atTop, 2 ^ k * Nat.card {q : ofAtoms k // ¬ IsIntegral q} ≤
      2 * Nat.card (ofAtoms k) := by
  filter_upwards [eventually_gt_atTop 0, eventually_le_card_mul_relabellings,
    eventually_pow_le_choose]
    with k hk htotal hpow
  have ht : 2 ^ ((k + 1).choose 3) ≤ 2 * Nat.card (ofAtoms k) * k ^ k := by
    exact_mod_cast (show (2 : ℝ) ^ ((k + 1).choose 3) ≤ 2 * Nat.card (ofAtoms k) * (k : ℝ) ^ k by
      linarith only [htotal])
  apply Nat.le_of_mul_le_mul_right _ (Nat.pow_pos hk (n := k))
  calc
    2 ^ k * Nat.card {q : ofAtoms k // ¬ IsIntegral q} * k ^ k ≤
        2 ^ k * (k ^ k * (2 ^ k * k ^ k) * 2 ^ k.choose 3) * k ^ k := by
      gcongr
      exact card_nonintegral_le hk
    _ = (4 * k ^ 3) ^ k * 2 ^ k.choose 3 := by
      rw [show 4 = 2 * 2 by decide, mul_pow, mul_pow, ← pow_mul, Nat.mul_comm 3 k, pow_mul]
      ring
    _ ≤ 2 ^ k.choose 2 * 2 ^ k.choose 3 := Nat.mul_le_mul_right _ hpow
    _ = 2 ^ ((k + 1).choose 3) := by rw [← pow_add, Nat.choose_succ_succ' k 2]
    _ ≤ _ := ht

/-- Among isomorphism classes of finite relation algebras on `k` atoms, the proportion
that are integral tends to one. See Koussas, *Finite Relation Algebras*, Corollary 24. -/
theorem tendsto_integral_div_all :
    Tendsto (fun k => (Nat.card (IntegralAtom.IsoClass.ofAtoms k) : ℝ) / Nat.card (ofAtoms k))
      atTop (𝓝 1) := by
  have hbad : Tendsto (fun k => (Nat.card {q : ofAtoms k // ¬ IsIntegral q} : ℝ) /
      Nat.card (ofAtoms k)) atTop (𝓝 0) := by
    have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 2
    rw [mul_zero] at hlim
    apply squeeze_zero' (.of_forall fun _ => by positivity) _ hlim
    filter_upwards [eventually_two_pow_mul_card_nonintegral_le] with k h
    have hp : (0 : ℝ) < Nat.card (ofAtoms k) := by exact_mod_cast card_ofAtoms_pos k
    rw [div_le_iff₀ hp, one_div, inv_pow]
    have h' : (2 : ℝ) ^ k * Nat.card {q : ofAtoms k // ¬ IsIntegral q} ≤
        2 * Nat.card (ofAtoms k) := by exact_mod_cast h
    calc
      _ ≤ (2 * Nat.card (ofAtoms k) : ℝ) / 2 ^ k := (le_div_iff₀ (by positivity)).mpr
        (by simpa only [mul_comm] using h')
      _ = _ := by ring
  have h := tendsto_const_nhds (x := (1 : ℝ)) |>.sub hbad
  rw [sub_zero] at h
  apply h.congr fun k => ?_
  have hp : (Nat.card (ofAtoms k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (card_ofAtoms_pos k).ne'
  have hc : (Nat.card (IntegralAtom.IsoClass.ofAtoms k) : ℝ) +
      Nat.card {q : ofAtoms k // ¬ IsIntegral q} = Nat.card (ofAtoms k) := by
    exact_mod_cast card_integral_add_card_nonintegral k
  field_simp
  linarith

end IsoClass

end Cslib.RelationAlgebra
