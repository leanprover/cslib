/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.RelationAlgebra.SpecialElements

/-! # Integral relation algebras -/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {α : Type*} [RelationAlgebra α] {a b : α}

lemma IsIntegral.relDom_eq_one (h : IsIntegral α) (ha : a ≠ ⊥) : relDom a = 1 := by
  have := h.le_iff.mp (le_one_of_corefl <| relDom a)
  grind [relDom_eq_bot_iff]

/-- A relation algebra is integral iff it is nontrivial, and every non-bot element has full
domain. -/
theorem isIntegral_iff_forall_relDom :
    IsIntegral α ↔ Nontrivial α ∧ ∀ a : α, a ≠ ⊥ → relDom a = 1 := by
  refine ⟨fun h ↦ ⟨h.nontrivial, fun a ha ↦ h.relDom_eq_one ha⟩, ?_⟩
  intro ⟨hnt, h⟩
  rw [IsIntegral, isAtom_iff_le_of_ge]
  constructor
  · simp [one_eq_bot_iff, not_subsingleton]
  · intro a hbot hle
    rw [← @relDom_of_isRelCorefl _ _ _ ⟨hle⟩, h a hbot]

lemma IsIntegral.relCod_eq_one (h : IsIntegral α) (ha : a ≠ ⊥) : relCod a = 1 := by
  have := h.le_iff.mp (le_one_of_corefl <| relCod a)
  grind [relCod_eq_bot_iff]

/-- A relation algebra is integral iff it is nontrivial, and every non-bot element has full
codomain. -/
theorem isIntegral_iff_forall_relCod :
    IsIntegral α ↔ Nontrivial α ∧ ∀ a : α, a ≠ ⊥ → relCod a = 1 := by
  refine ⟨fun h ↦ ⟨h.nontrivial, fun a ha ↦ h.relCod_eq_one ha⟩, ?_⟩
  simp_rw [isIntegral_iff_forall_relDom, and_imp, ← relCod_star]
  refine fun hnt h ↦ ⟨hnt, fun a hbot ↦ ?_⟩
  grind [star_inj, star_bot]

lemma IsIntegral.mul_eq_bot_iff (h : IsIntegral α) : a * b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by
  constructor
  · intro hab
    obtain (hb | hb) := h.le_iff.mp (le_one_of_corefl <| relDom b)
    · exact Or.inr <| relDom_eq_bot_iff.mp hb
    · refine Or.inl <| eq_bot_iff.mpr ?_
      grw [← mul_one a, ← hb, relDom, inf_le_left, ← mul_assoc, hab, bot_mul]
  · rintro (rfl | rfl)
    all_goals simp

theorem isIntegral_tfae (α : Type*) [RelationAlgebra α] [Nontrivial α] :
    [IsIntegral α, ∀ a b : α, a * b = ⊥ → a = ⊥ ∨ b = ⊥,
      ∀ a : α, a ≠ ⊥ → relDom a = 1, ∀ a : α, a ≠ ⊥ → relCod a = 1,
      ∀ a : α, a ≠ ⊥ → a * ⊤ = ⊤, ∀ a : α, a ≠ ⊥ → ⊤ * a = ⊤].TFAE := by
  tfae_have 2 → 5 := fun h a hbot ↦ by
    rw [← compl_inj_iff, compl_top]
    apply h (star a) (a * ⊤)ᶜ (by grw [eq_bot_iff, tarski, compl_top]) |>.resolve_left
    rwa [← star_bot, star_inj, ← ne_eq]
  tfae_have 1 → 2 := fun h a b ↦ h.mul_eq_bot_iff.mp
  tfae_have 1 ↔ 3 := by simp_all [isIntegral_iff_forall_relDom]
  tfae_have 1 ↔ 4 := by simp_all [isIntegral_iff_forall_relCod]
  tfae_have 3 ↔ 5 := by simp [relDom_eq_one_iff]
  tfae_have 4 ↔ 6 := by simp [relCod_eq_one_iff]
  tfae_finish

end Cslib.RelationAlgebra
