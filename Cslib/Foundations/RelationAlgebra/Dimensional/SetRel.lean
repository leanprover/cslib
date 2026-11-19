/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.RelationalBasis
public import Cslib.Foundations.RelationAlgebra.Representation

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

namespace PiSetRel

variable {ι : Type u} {γ : ι → Type w} {κ : Type v}

section pt

variable [DecidableEq ι] {i j : ι} {x y z : γ i}

def pt (i : ι) (x y : γ i) : ∀ i, SetRel (γ i) (γ i) :=
  Function.update ⊥ i {(x, y)}

@[simp]
theorem pt_apply_self : pt i x y i = {(x, y)} :=
  Function.update_self ..

@[simp]
theorem pt_apply_of_ne (h : j ≠ i) : pt i x y j = ⊥ :=
  Function.update_of_ne h ..

theorem isAtom_pt : IsAtom (pt i x y) :=
  Pi.isAtom_single (Set.isAtom_singleton _)

theorem exists_eq_pt {a : ∀ i, SetRel (γ i) (γ i)} (ha : IsAtom a) : ∃ i x y, a = pt i x y := by
  obtain ⟨i, s, hs, rfl⟩ := Pi.isAtom_iff_eq_single.mp ha
  obtain ⟨⟨x, y⟩, rfl⟩ := Set.isAtom_iff.mp hs
  exact ⟨i, x, y, rfl⟩

theorem pt_le_iff {b : ∀ i, SetRel (γ i) (γ i)} : pt i x y ≤ b ↔ (x, y) ∈ b i := by
  simp [pt, update_le_iff]

theorem pt_le_one : pt i x x ≤ 1 :=
  pt_le_iff.mpr rfl

theorem star_pt : star (pt i x y) = pt i y x := by
  funext j
  obtain rfl | h := eq_or_ne j i
  · ext ⟨u, v⟩
    simp [Pi.star_apply, and_comm]
  · simp [Pi.star_apply, h, SetRel.star_eq_inv]

theorem pt_le_mul : pt i x z ≤ pt i x y * pt i y z :=
  pt_le_iff.mpr <| by simp [Pi.mul_apply]

theorem exists_eq_pt_of_pt_le_mul {i₁ i₂ : ι} {x₁ y₁ : γ i₁} {x₂ y₂ : γ i₂}
    (h : pt i x y ≤ pt i₁ x₁ y₁ * pt i₂ x₂ y₂) :
    ∃ z, pt i₁ x₁ y₁ = pt i x z ∧ pt i₂ x₂ y₂ = pt i z y := by
  rw [pt_le_iff, Pi.mul_apply] at h
  obtain rfl | h₁ := eq_or_ne i i₁
  · obtain rfl | h₂ := eq_or_ne i i₂
    · obtain ⟨z, hz₁, hz₂⟩ := SetRel.mem_mul.mp h
      simp only [pt_apply_self, Set.mem_singleton_iff, Prod.mk.injEq] at hz₁ hz₂
      obtain ⟨rfl, rfl⟩ := hz₁
      obtain ⟨rfl, rfl⟩ := hz₂
      exact ⟨z, rfl, rfl⟩
    · obtain ⟨z, -, hz⟩ := SetRel.mem_mul.mp h
      simp [h₂] at hz
  · obtain ⟨z, hz, -⟩ := SetRel.mem_mul.mp h
    simp [h₁] at hz

end pt

open Classical in
def basis (γ : ι → Type w) (κ : Type v) : Set (κ → κ → ∀ i, SetRel (γ i) (γ i)) :=
  {m | ∃ i, ∃ s : κ → γ i, ∀ p q, m p q = pt i (s p) (s q)}

theorem isRelationalBasis_basis {i₀ i₁ : κ} (hne : i₀ ≠ i₁) :
    IsRelationalBasis (basis γ κ) where
  isBasicMatrix := by
    classical
    rintro m ⟨i, s, hm⟩
    refine ⟨fun p q => ?_, fun p => ?_, fun p q => ?_, fun p q r => ?_⟩
    · rw [hm]
      exact isAtom_pt
    · rw [hm]
      exact pt_le_one
    · rw [hm, hm, star_pt]
    · rw [hm, hm, hm]
      exact pt_le_mul
  exists_apply_eq := by
    classical
    intro a ha
    obtain ⟨i, x, y, rfl⟩ := exists_eq_pt ha
    refine ⟨fun p q => pt i (if p = i₀ then x else y) (if q = i₀ then x else y),
      ⟨i, fun p => if p = i₀ then x else y, fun _ _ => rfl⟩, i₀, i₁, hne, ?_⟩
    simp [hne.symm]
  exists_apply_eq_apply_eq := by
    classical
    rintro m p q k a b ⟨i, s, hm⟩ hpk hqk ha hb hab
    obtain ⟨i₁, x₁, y₁, rfl⟩ := exists_eq_pt ha
    obtain ⟨i₂, x₂, y₂, rfl⟩ := exists_eq_pt hb
    rw [hm] at hab
    obtain ⟨z, h₁, h₂⟩ := exists_eq_pt_of_pt_le_mul hab
    refine ⟨fun l h => pt i (Function.update s k z l) (Function.update s k z h),
      ⟨i, Function.update s k z, fun _ _ => rfl⟩, ?_, ?_, fun l h hl hh => ?_⟩
    · simp [h₁, hpk]
    · simp [h₂, hqk]
    · simp [hm, hl.symm, hh.symm]

end PiSetRel

theorem Representable.dimensional_of_ne {α : Type u} [RelationAlgebra α] (h : Representable α)
    {κ : Type v} {i₀ i₁ : κ} (hne : i₀ ≠ i₁) : Dimensional α κ :=
  let ⟨_, _, ⟨r⟩⟩ := h
  ⟨_, inferInstance, r.hom, r.injective, inferInstance, _, PiSetRel.isRelationalBasis_basis hne⟩

theorem Representable.dimensional {α : Type u} [RelationAlgebra α] (h : Representable α) :
    Dimensional α ℕ :=
  h.dimensional_of_ne zero_ne_one

end Cslib.RelationAlgebra
