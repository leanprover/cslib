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
