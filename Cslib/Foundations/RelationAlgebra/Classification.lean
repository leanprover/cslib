/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.GeneralLemmas
public import Cslib.Foundations.RelationAlgebra.Hom

/-!
# Classification of finite relation algebras

Finite Boolean algebras are determined by their atoms. The initial classification results
identify relation algebras with one identity atom and no diversity atoms.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {A B : Type*} [RelationAlgebra A] [RelationAlgebra B]

/-- In a finite Boolean algebra, an element above exactly one atom is itself an atom. -/
theorem isAtom_of_card_atoms_below_eq_one [Finite A] {a : A}
    (h : Nat.card {b : A // IsAtom b ∧ b ≤ a} = 1) : IsAtom a := by
  obtain ⟨b, hb⟩ := Nat.card_eq_one_iff_exists.mp h
  have he : a = b := by
    apply le_antisymm _ b.property.2
    apply BooleanAlgebra.le_iff_atom_le_imp.mpr
    intro c hc hca
    exact (congrArg Subtype.val (hb ⟨c, hc, hca⟩)).le
  exact he ▸ b.property.1

/-- Exactly one identity atom makes a finite relation algebra integral. -/
theorem integral_of_hasSignature_one {j k : ℕ} (h : HasSignature A 1 j k) : Integral A := by
  let : Finite A := h.1
  exact isAtom_of_card_atoms_below_eq_one h.2.1

/-- In signature `⟨1, 1, 0⟩`, the complement of identity is a symmetric atom. -/
theorem diversity_atom_of_hasSignature_one_one (h : HasSignature A 1 1 0) :
    IsAtom (1 : A)ᶜ ∧ star (1 : A)ᶜ = (1 : A)ᶜ := by
  let : Finite A := h.1
  have hs (a : A) (ha : IsAtom a) (ha1 : a ≤ (1 : A)ᶜ) : star a = a := by
    by_contra hne
    have hn : Nonempty {a : A // IsAtom a ∧ a ≤ (1 : A)ᶜ ∧ star a ≠ a} :=
      ⟨⟨a, ha, ha1, hne⟩⟩
    have hp := Nat.card_pos_iff.mpr ⟨hn, inferInstance⟩
    have hz := h.2.2.2
    omega
  obtain ⟨a, ha⟩ := Nat.card_eq_one_iff_exists.mp h.2.2.1
  have he : (1 : A)ᶜ = a := by
    apply le_antisymm _ a.property.2.1
    apply BooleanAlgebra.le_iff_atom_le_imp.mpr
    intro b hb hb1
    exact (congrArg Subtype.val (ha ⟨b, hb, hb1, hs b hb hb1⟩)).le
  rw [he]
  exact ⟨a.property.1, a.property.2.2⟩

/-- Complementary atoms give the four possible Boolean elements. -/
theorem eq_bot_or_eq_one_or_eq_compl_or_eq_top (h1 : IsAtom (1 : A))
    (hd : IsAtom (1 : A)ᶜ) (a : A) : a = ⊥ ∨ a = 1 ∨ a = (1 : A)ᶜ ∨ a = ⊤ := by
  have he : a = (a ⊓ 1) ⊔ (a ⊓ (1 : A)ᶜ) := by
    rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
  rcases h1.le_iff.mp (inf_le_right : a ⊓ 1 ≤ (1 : A)) with h | h <;>
    rcases hd.le_iff.mp (inf_le_right : a ⊓ (1 : A)ᶜ ≤ (1 : A)ᶜ) with h' | h' <;>
    simp only [h, h', bot_sup_eq, sup_bot_eq, sup_compl_eq_top] at he
  · exact Or.inl he
  · exact Or.inr (Or.inr (Or.inl he))
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (Or.inr he))

/-- In signature `⟨1, 1, 0⟩`, the diversity square has exactly two possible values. -/
theorem diversity_sq_eq_one_or_top (h : HasSignature A 1 1 0) :
    (1 : A)ᶜ * (1 : A)ᶜ = 1 ∨ (1 : A)ᶜ * (1 : A)ᶜ = ⊤ := by
  have h1 : IsAtom (1 : A) := integral_of_hasSignature_one h
  obtain ⟨hd, hs⟩ := diversity_atom_of_hasSignature_one_one h
  have hnot : ¬ (1 : A)ᶜ ≤ 1 := by
    intro hle
    apply hd.ne_bot
    exact le_antisymm (by simpa using le_inf hle le_rfl) bot_le
  rcases eq_bot_or_eq_one_or_eq_compl_or_eq_top h1 hd ((1 : A)ᶜ * (1 : A)ᶜ) with
    hm | hm | hm | hm
  · have ht := tarski (1 : A)ᶜ (1 : A)ᶜ
    rw [hs, hm, compl_bot, compl_compl] at ht
    have hl : (1 : A)ᶜ ≤ (1 : A)ᶜ * ⊤ := by
      simpa using mul_le_mul_left (le_top : (1 : A) ≤ ⊤) (1 : A)ᶜ
    exact (hnot (hl.trans ht)).elim
  · exact Or.inl hm
  · have ht := tarski (1 : A)ᶜ (1 : A)ᶜ
    rw [hs, hm, compl_compl, mul_one] at ht
    exact (hnot ht).elim
  · exact Or.inr hm

open scoped Classical in
/-- The Boolean map matching identity and diversity in two-atom algebras. -/
noncomputable def twoAtomMap (B : Type*) [RelationAlgebra B] (a : A) : B :=
  (if 1 ≤ a then 1 else ⊥) ⊔ (if (1 : A)ᶜ ≤ a then (1 : B)ᶜ else ⊥)

/-- The Boolean map sends the four distinguished elements to their counterparts. -/
theorem twoAtomMap_values (h1 : IsAtom (1 : A)) (hd : IsAtom (1 : A)ᶜ) :
    twoAtomMap B (⊥ : A) = ⊥ ∧ twoAtomMap B (1 : A) = 1 ∧
      twoAtomMap B (1 : A)ᶜ = (1 : B)ᶜ ∧ twoAtomMap B (⊤ : A) = ⊤ := by
  have htop : (1 : A) ≠ ⊤ := by
    intro he
    exact hd.ne_bot (by rw [he, compl_top])
  simp [twoAtomMap, h1.ne_bot, hd.ne_bot, htop]

/-- Two algebras of signature `⟨1, 1, 0⟩` have a canonical Boolean order isomorphism. -/
noncomputable def orderIsoOfHasSignatureOneOne (hA : HasSignature A 1 1 0)
    (hB : HasSignature B 1 1 0) : A ≃o B := by
  have hA1 : IsAtom (1 : A) := integral_of_hasSignature_one hA
  have hAd := (diversity_atom_of_hasSignature_one_one hA).1
  have hB1 : IsAtom (1 : B) := integral_of_hasSignature_one hB
  have hBd := (diversity_atom_of_hasSignature_one_one hB).1
  letI : Nontrivial A := ⟨⟨1, ⊥, hA1.ne_bot⟩⟩
  letI : Nontrivial B := ⟨⟨1, ⊥, hB1.ne_bot⟩⟩
  have hAtop : (1 : A) ≠ ⊤ := by
    intro he
    exact hAd.ne_bot (by rw [he, compl_top])
  have hBtop : (1 : B) ≠ ⊤ := by
    intro he
    exact hBd.ne_bot (by rw [he, compl_top])
  obtain ⟨hf0, hf1, hfd, hft⟩ := twoAtomMap_values (B := B) hA1 hAd
  obtain ⟨hg0, hg1, hgd, hgt⟩ := twoAtomMap_values (B := A) hB1 hBd
  refine
    { toFun := twoAtomMap B
      invFun := twoAtomMap A
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · intro a
    rcases eq_bot_or_eq_one_or_eq_compl_or_eq_top hA1 hAd a with rfl | rfl | rfl | rfl <;>
      simp only [hf0, hf1, hfd, hft, hg0, hg1, hgd, hgt]
  · intro b
    rcases eq_bot_or_eq_one_or_eq_compl_or_eq_top hB1 hBd b with rfl | rfl | rfl | rfl <;>
      simp only [hf0, hf1, hfd, hft, hg0, hg1, hgd, hgt]
  · intro a b
    change twoAtomMap B a ≤ twoAtomMap B b ↔ a ≤ b
    rcases eq_bot_or_eq_one_or_eq_compl_or_eq_top hA1 hAd a with rfl | rfl | rfl | rfl <;>
      rcases eq_bot_or_eq_one_or_eq_compl_or_eq_top hA1 hAd b with rfl | rfl | rfl | rfl <;>
      simp only [hf0, hf1, hfd, hft, bot_le, le_top, le_refl, le_bot_iff, top_le_iff,
        compl_le_self, le_compl_self, compl_eq_top, hA1.ne_bot, hAd.ne_bot, hB1.ne_bot,
        hBd.ne_bot, hAtop, hBtop, top_ne_bot]

/-- The diversity-square equation is invariant under relation-algebra isomorphism. -/
theorem diversity_sq_eq_one_iff (e : RelationAlgebraEquiv A B) :
    (1 : A)ᶜ * (1 : A)ᶜ = 1 ↔ (1 : B)ᶜ * (1 : B)ᶜ = 1 := by
  constructor
  · intro h
    simpa only [map_mul, map_compl', map_one] using congrArg e h
  · intro h
    apply e.injective
    change e ((1 : A)ᶜ * (1 : A)ᶜ) = e 1
    simpa only [map_mul, map_compl', map_one] using h

/-- In signature `⟨1, 1, 0⟩`, the diversity square determines the relation algebra. -/
noncomputable def equivOfHasSignatureOneOne (hA : HasSignature A 1 1 0)
    (hB : HasSignature B 1 1 0)
    (hsq : (1 : A)ᶜ * (1 : A)ᶜ = 1 ↔ (1 : B)ᶜ * (1 : B)ᶜ = 1) :
    RelationAlgebraEquiv A B := by
  let f := orderIsoOfHasSignatureOneOne hA hB
  have hA1 : IsAtom (1 : A) := integral_of_hasSignature_one hA
  obtain ⟨hAd, hsA⟩ := diversity_atom_of_hasSignature_one_one hA
  have hB1 : IsAtom (1 : B) := integral_of_hasSignature_one hB
  obtain ⟨hBd, hsB⟩ := diversity_atom_of_hasSignature_one_one hB
  have hf0 : f ⊥ = ⊥ := f.map_bot
  have hf1 : f 1 = 1 := (twoAtomMap_values (B := B) hA1 hAd).2.1
  have hfd : f (1 : A)ᶜ = (1 : B)ᶜ := (twoAtomMap_values (B := B) hA1 hAd).2.2.1
  have hfdd : f ((1 : A)ᶜ * (1 : A)ᶜ) = (1 : B)ᶜ * (1 : B)ᶜ := by
    rcases diversity_sq_eq_one_or_top hA with ha | ha
    · rw [ha, hf1, hsq.mp ha]
    · rcases diversity_sq_eq_one_or_top hB with hb | hb
      · have he : (1 : A) = ⊤ := (hsq.mpr hb).symm.trans ha
        exact (hAd.ne_bot (by rw [he, compl_top])).elim
      · rw [ha, hb, f.map_top]
  refine { f with map_mul' := ?_, map_star' := ?_ }
  · intro a b
    change f (a * b) = f a * f b
    rcases eq_bot_or_eq_one_or_eq_compl_or_eq_top hA1 hAd a with rfl | rfl | rfl | rfl <;>
      rcases eq_bot_or_eq_one_or_eq_compl_or_eq_top hA1 hAd b with rfl | rfl | rfl | rfl <;>
      simp only [← sup_compl_eq_top (x := (1 : A)), sup_mul, mul_sup, mul_one, one_mul,
        mul_bot, bot_mul, map_sup, hf0, hf1, hfd, hfdd]
  · intro a
    change f (star a) = star (f a)
    rcases eq_bot_or_eq_one_or_eq_compl_or_eq_top hA1 hAd a with rfl | rfl | rfl | rfl <;>
      simp only [star_bot, star_one, star_top, hsA, hsB, hf0, hf1, hfd, map_top]

/-- With no diversity atoms, the identity is the Boolean top. -/
theorem one_eq_top_of_hasSignature_zero {i : ℕ} (h : HasSignature A i 0 0) :
    (1 : A) = ⊤ := by
  let : Finite A := h.1
  have hno : ¬ ∃ a : A, IsAtom a ∧ a ≤ (1 : A)ᶜ := by
    rintro ⟨a, ha, ha1⟩
    by_cases hs : star a = a
    · have hn : Nonempty {a : A // IsAtom a ∧ a ≤ (1 : A)ᶜ ∧ star a = a} :=
        ⟨⟨a, ha, ha1, hs⟩⟩
      have hp := Nat.card_pos_iff.mpr ⟨hn, inferInstance⟩
      have hz := h.2.2.1
      omega
    · have hn : Nonempty {a : A // IsAtom a ∧ a ≤ (1 : A)ᶜ ∧ star a ≠ a} :=
        ⟨⟨a, ha, ha1, hs⟩⟩
      have hp := Nat.card_pos_iff.mpr ⟨hn, inferInstance⟩
      have hz := h.2.2.2
      omega
  have hc : (1 : A)ᶜ = ⊥ := (eq_bot_or_exists_atom_le _).resolve_right hno
  simpa only [compl_compl, compl_bot] using congrArg compl hc

/-- A relation algebra of signature `⟨1, 0, 0⟩` has exactly the two Boolean elements. -/
theorem isSimpleOrder_of_hasSignature_one (h : HasSignature A 1 0 0) : IsSimpleOrder A := by
  let : Finite A := h.1
  have h1 := one_eq_top_of_hasSignature_zero h
  obtain ⟨a, ha⟩ := Nat.card_eq_one_iff_exists.mp h.2.1
  have hatop : (a : A) = ⊤ := by
    apply le_antisymm le_top
    apply BooleanAlgebra.le_iff_atom_le_imp.mpr
    intro b hb _
    have he := congrArg Subtype.val (ha ⟨b, hb, by simp [h1]⟩)
    exact he.le
  exact isSimpleOrder_iff_isAtom_top.mpr (hatop ▸ a.property.1)

/-- Any two relation algebras of signature `⟨1, 0, 0⟩` are isomorphic. -/
noncomputable def equivOfHasSignatureOne (hA : HasSignature A 1 0 0)
    (hB : HasSignature B 1 0 0) : RelationAlgebraEquiv A B := by
  classical
  letI : IsSimpleOrder A := isSimpleOrder_of_hasSignature_one hA
  letI : IsSimpleOrder B := isSimpleOrder_of_hasSignature_one hB
  let f : A ≃o B := IsSimpleOrder.orderIsoBool.trans IsSimpleOrder.orderIsoBool.symm
  have hA1 := one_eq_top_of_hasSignature_zero hA
  have hB1 := one_eq_top_of_hasSignature_zero hB
  have hf1 : f 1 = 1 := by rw [hA1, hB1, f.map_top]
  refine { f with map_mul' := ?_, map_star' := ?_ }
  · intro a b
    change f (a * b) = f a * f b
    rcases eq_bot_or_eq_top a with rfl | rfl <;>
      rcases eq_bot_or_eq_top b with rfl | rfl <;>
      simp only [← hA1, mul_bot, mul_one, map_bot, hf1]
  · intro a
    change f (star a) = star (f a)
    rcases eq_bot_or_eq_top a with rfl | rfl <;>
      simp only [star_bot, star_top, map_bot, map_top]

end Cslib.RelationAlgebra
