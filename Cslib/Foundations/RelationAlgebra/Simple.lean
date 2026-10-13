/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Hom

/-!
# Simple relation algebras

Following the equivalent criterion in [Givant2017, Theorem 9.2(ii)][Givant2017], a relation
algebra is simple if it is nontrivial and `⊤ * a * ⊤ = ⊤` for every nonzero `a`.
Givant's Boolean unit `1` is written `⊤` here; his identity element `1′` is written `1`.

We prove the ideal-element characterization (Lemma 9.1), the other two criteria in the
Simplicity Theorem (Theorem 9.2), and consequences for homomorphisms and integral algebras.

## References

* [Steven Givant, *Introduction to Relation Algebras*, Chapter 9][Givant2017]
-/

@[expose] public section

namespace Cslib.RelationAlgebra

/-- A relation algebra is simple when it is nontrivial and every nonzero element generates
Boolean top under multiplication by top on both sides. This is the criterion in
[Givant2017, Theorem 9.2(ii)][Givant2017]. -/
def Simple (α : Type*) [RelationAlgebra α] : Prop :=
  Nontrivial α ∧ ∀ a : α, a ≠ ⊥ → (⊤ : α) * a * ⊤ = ⊤

variable {α : Type*} [RelationAlgebra α]

/-- Simplicity excludes the degenerate relation algebra. -/
theorem Simple.nontrivial (h : Simple α) : Nontrivial α := h.1

/-- Every nonzero element of a simple algebra generates Boolean top. -/
theorem Simple.top_mul_top (h : Simple α) {a : α} (ha : a ≠ ⊥) :
    (⊤ : α) * a * ⊤ = ⊤ := h.2 a ha

/-- A simple algebra has exactly two ideal elements, the distinct bottom and top.
An ideal element is a fixed point of `a ↦ ⊤ * a * ⊤`.
This is [Givant2017, Lemma 9.1][Givant2017]. -/
theorem simple_iff_ideal_elements :
    Simple α ↔ Nontrivial α ∧ ∀ a : α, ⊤ * a * ⊤ = a → a = ⊥ ∨ a = ⊤ := by
  constructor
  · intro h
    refine ⟨h.nontrivial, fun a ha => ?_⟩
    by_cases hbot : a = ⊥
    · exact Or.inl hbot
    · exact Or.inr (ha.symm.trans (h.top_mul_top hbot))
  · rintro ⟨hnt, h⟩
    refine ⟨hnt, fun a ha => ?_⟩
    have hfixed : ⊤ * (⊤ * a * ⊤) * ⊤ = ⊤ * a * ⊤ := by
      calc
        ⊤ * (⊤ * a * ⊤) * ⊤ = (⊤ * ⊤) * a * (⊤ * ⊤) := by simp only [mul_assoc]
        _ = ⊤ * a * ⊤ := by rw [top_mul_top]
    rcases h (⊤ * a * ⊤) hfixed with hbot | htop
    · exact (ha (bot_unique ((le_top_mul a).trans
        ((le_mul_top (⊤ * a)).trans (le_of_eq hbot))))).elim
    · exact htop

/-- The one-sided alternative characterization of simplicity from
[Givant2017, Theorem 9.2(iii)][Givant2017]. -/
theorem simple_iff_mul_top_or_top_mul_compl :
    Simple α ↔ Nontrivial α ∧ ∀ a : α, a * ⊤ = ⊤ ∨ ⊤ * aᶜ = ⊤ := by
  constructor
  · intro h
    refine ⟨h.nontrivial, fun a => ?_⟩
    by_cases ha : a * ⊤ = ⊤
    · exact Or.inl ha
    · right
      have hne : (a * ⊤)ᶜ ≠ ⊥ := fun hbot => ha (compl_eq_bot.mp hbot)
      apply top_unique
      calc
        ⊤ = ⊤ * (a * ⊤)ᶜ * ⊤ := (h.top_mul_top hne).symm
        _ = ⊤ * ((a * ⊤)ᶜ * ⊤) := mul_assoc _ _ _
        _ ≤ ⊤ * aᶜ := mul_le_mul_left (by
          simpa only [star_top] using right_tarski a (⊤ : α)) ⊤
  · rintro ⟨hnt, h⟩
    refine ⟨hnt, fun a ha => ?_⟩
    rcases h (⊤ * a) with htop | hcompl
    · exact htop
    · have hle : (⊤ : α) ≤ aᶜ := by
        simpa only [star_top, hcompl] using tarski (⊤ : α) a
      exact (ha (compl_eq_top.mp (top_unique hle))).elim

/-- A rectangle in a simple algebra is bottom only when one of its sides is bottom.
This is [Givant2017, Theorem 9.2(iv)][Givant2017]. -/
theorem simple_iff_mul_top_mul_eq_bot :
    Simple α ↔ Nontrivial α ∧
      ∀ a b : α, a * ⊤ * b = ⊥ → a = ⊥ ∨ b = ⊥ := by
  constructor
  · intro h
    refine ⟨h.nontrivial, fun a b hab => ?_⟩
    by_cases ha : a = ⊥
    · exact Or.inl ha
    · right
      apply bot_unique
      calc
        b ≤ ⊤ * b := le_top_mul b
        _ = (⊤ * a * ⊤) * b := by rw [h.top_mul_top ha]
        _ = ⊤ * (a * ⊤ * b) := by simp only [mul_assoc]
        _ = ⊥ := by rw [hab, mul_bot]
  · rintro ⟨hnt, h⟩
    refine ⟨hnt, fun a ha => ?_⟩
    have hz : star a * ⊤ * (⊤ * a * ⊤)ᶜ = ⊥ := by
      apply bot_unique
      simpa only [star_mul, star_top, compl_top] using tarski ((⊤ : α) * a) (⊤ : α)
    rcases h (star a) (⊤ * a * ⊤)ᶜ hz with hstar | hcompl
    · exact (ha (by simpa only [star_star, star_bot] using congrArg star hstar)).elim
    · exact compl_eq_bot.mp hcompl

/-- In an integral relation algebra, left multiplication of a nonzero element by top gives top.
This is [Givant2017, Theorem 9.7(iii)][Givant2017]. -/
theorem Integral.top_mul_eq_top (h : Integral (α := α)) {a : α} (ha : a ≠ ⊥) :
    ⊤ * a = ⊤ := by
  have he : 1 ⊓ star a * a ≠ ⊥ := by
    intro he
    have hle := left_modular a 1 a
    rw [mul_one, inf_idem, he, mul_bot] at hle
    exact ha (eq_bot_iff.mpr hle)
  have he_one : 1 ⊓ star a * a = 1 := (h.le_iff.mp inf_le_left).resolve_left he
  have hone : 1 ≤ star a * a := by
    rw [← he_one]
    exact inf_le_right
  apply top_unique
  calc
    ⊤ = (⊤ : α) * 1 := (mul_one _).symm
    _ ≤ ⊤ * (star a * a) := mul_le_mul_left hone _
    _ = (⊤ * star a) * a := (mul_assoc _ _ _).symm
    _ ≤ ⊤ * a := mul_le_mul_right le_top _

/-- In an integral relation algebra, right multiplication of a nonzero element by top gives top.
This is [Givant2017, Theorem 9.7(ii)][Givant2017]. -/
theorem Integral.mul_top_eq_top (h : Integral (α := α)) {a : α} (ha : a ≠ ⊥) :
    a * ⊤ = ⊤ := by
  have hstar : star a ≠ ⊥ := by
    intro hstar
    apply ha
    simpa only [star_star, star_bot] using congrArg star hstar
  simpa only [star_mul, star_star, star_top] using congrArg star (h.top_mul_eq_top hstar)

/-- Every integral relation algebra is simple.
This is [Givant2017, Corollary 9.10][Givant2017]. -/
theorem Integral.simple (h : Integral (α := α)) : Simple α := by
  refine ⟨nontrivial_of_ne (1 : α) ⊥ h.ne_bot, fun a ha => ?_⟩
  rw [h.top_mul_eq_top ha, top_mul_top]

/-- Integral relation algebras have no zero divisors.
This is part of [Givant2017, Theorem 9.7][Givant2017]. -/
theorem Integral.mul_eq_bot_iff (h : Integral (α := α)) {a b : α} :
    a * b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by
  constructor
  · intro hab
    by_cases ha : a = ⊥
    · exact Or.inl ha
    · right
      by_contra hb
      let : Nontrivial α := nontrivial_of_ne (1 : α) ⊥ h.ne_bot
      apply top_ne_bot (α := α)
      calc
        ⊤ = (⊤ : α) * b := (h.top_mul_eq_top hb).symm
        _ = (⊤ * a) * b := by rw [h.top_mul_eq_top ha]
        _ = ⊤ * (a * b) := mul_assoc _ _ _
        _ = ⊥ := by rw [hab, mul_bot]
  · rintro (rfl | rfl)
    · exact bot_mul _
    · exact mul_bot _

/-- Atomicity of identity is equivalent to nontriviality and absence of zero divisors.
This is [Givant2017, Theorem 9.7(i), (vii)][Givant2017]. -/
theorem integral_iff_mul_eq_bot :
    Integral (α := α) ↔
      Nontrivial α ∧ ∀ a b : α, a * b = ⊥ → a = ⊥ ∨ b = ⊥ := by
  constructor
  · intro h
    exact ⟨nontrivial_of_ne (1 : α) ⊥ h.ne_bot, fun _ _ => h.mul_eq_bot_iff.mp⟩
  · rintro ⟨hα, h⟩
    let : Nontrivial α := hα
    refine ⟨?_, ?_⟩
    · intro hone
      apply top_ne_bot (α := α)
      calc
        ⊤ = (⊤ : α) * 1 := (mul_one _).symm
        _ = ⊥ := by rw [hone, mul_bot]
    · intro a ha
      have hab : a * (1 ⊓ aᶜ) = ⊥ := by
        apply eq_bot_iff.mpr
        calc
          a * (1 ⊓ aᶜ) ≤ a ⊓ aᶜ := le_inf
            (by simpa only [mul_one] using mul_le_mul_left (inf_le_left : (1 : α) ⊓ aᶜ ≤ 1) a)
            (by
              calc
                a * (1 ⊓ aᶜ) ≤ 1 * (1 ⊓ aᶜ) := mul_le_mul_right ha.le _
                _ = 1 ⊓ aᶜ := one_mul _
                _ ≤ aᶜ := inf_le_right)
          _ = ⊥ := inf_compl_eq_bot
      rcases h _ _ hab with ha_bot | hcompl
      · exact ha_bot
      · exfalso
        apply ha.not_ge
        simpa only [compl_compl] using
          le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hcompl)

variable {β : Type*} [RelationAlgebra β]

/-- Every homomorphism from a simple algebra to a nontrivial algebra is injective, as in
Givant's definition of simplicity [Givant2017, Section 9.1, p. 386][Givant2017]. -/
theorem Simple.injective (h : Simple α) [Nontrivial β]
    (f : RelationAlgebraHom α β) : Function.Injective f := by
  have hbot : ∀ a, f a = ⊥ → a = ⊥ := by
    intro a ha
    by_contra hne
    have ht := congrArg f (h.top_mul_top hne)
    simp only [map_mul, map_top, ha, mul_bot, bot_mul] at ht
    exact bot_ne_top ht
  intro a b hab
  apply le_antisymm
  · apply sdiff_eq_bot_iff.mp
    apply hbot
    rw [map_sdiff', hab, sdiff_self]
  · apply sdiff_eq_bot_iff.mp
    apply hbot
    rw [map_sdiff', hab, sdiff_self]

/-- Every homomorphism from a simple algebra is injective or has a degenerate target, as in
[Givant2017, Section 9.1, p. 386][Givant2017]. -/
theorem Simple.injective_or_subsingleton (h : Simple α) (f : RelationAlgebraHom α β) :
    Function.Injective f ∨ Subsingleton β := by
  rcases subsingleton_or_nontrivial β with hβ | hβ
  · exact Or.inr hβ
  · exact Or.inl (h.injective f)

/-- Simplicity passes to subalgebras, expressed using an injective homomorphism.
This is [Givant2017, Corollary 9.3][Givant2017]. -/
theorem Simple.of_injective (h : Simple β) (f : RelationAlgebraHom α β)
    (hf : Function.Injective f) : Simple α := by
  let := h.nontrivial
  constructor
  · apply nontrivial_of_ne (⊥ : α) ⊤
    intro heq
    have := congrArg f heq
    rw [map_bot, map_top] at this
    exact bot_ne_top this
  · intro a ha
    apply hf
    rw [map_mul, map_mul, map_top]
    apply h.top_mul_top
    intro heq
    exact ha (hf (heq.trans (map_bot f).symm))

/-- Simplicity is invariant under isomorphism. -/
theorem simple_iff_of_equiv (e : RelationAlgebraEquiv α β) :
    Simple α ↔ Simple β :=
  ⟨fun h => h.of_injective e.symm.toHom e.symm.injective,
    fun h => h.of_injective e.toHom e.injective⟩

end Cslib.RelationAlgebra
