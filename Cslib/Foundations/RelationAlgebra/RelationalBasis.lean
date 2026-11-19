/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Hom
public import Mathlib.Data.ENat.Basic

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

variable {α : Type u} [NonAssocRelationAlgebra α] {ι : Type v}

structure IsBasicMatrix (m : ι → ι → α) : Prop where
  isAtom (i j : ι) : IsAtom (m i j)
  le_one (i : ι) : m i i ≤ 1
  star_apply (i j : ι) : star (m i j) = m j i
  le_mul (i j k : ι) : m i k ≤ m i j * m j k

structure IsRelationalBasis (B : Set (ι → ι → α)) : Prop where
  isBasicMatrix {m : ι → ι → α} : m ∈ B → IsBasicMatrix m
  exists_apply_eq {a : α} : IsAtom a → ∃ m ∈ B, ∃ i j, i ≠ j ∧ m i j = a
  exists_apply_eq_apply_eq {m : ι → ι → α} {i j k : ι} {a b : α} :
    m ∈ B → i ≠ k → j ≠ k → IsAtom a → IsAtom b → m i j ≤ a * b →
      ∃ m' ∈ B, m' i k = a ∧ m' k j = b ∧ ∀ l h, k ≠ l → k ≠ h → m l h = m' l h

def Dimensional (α : Type u) [NonAssocRelationAlgebra α] (ι : Type v) : Prop :=
  ∃ (β : Type u) (_ : SemiAssocRelationAlgebra β) (f : RelationAlgebraHom α β),
    Function.Injective f ∧ IsAtomic β ∧ ∃ B : Set (ι → ι → β), IsRelationalBasis B

def RA (α : Type u) [NonAssocRelationAlgebra α] (n : ℕ∞) : Prop :=
  Dimensional α {i : ℕ // (i : ℕ∞) < n}

variable {ι' : Type w}

theorem IsBasicMatrix.comp {m : ι → ι → α} (hm : IsBasicMatrix m) (f : ι' → ι) :
    IsBasicMatrix fun p q => m (f p) (f q) where
  isAtom _ _ := hm.isAtom _ _
  le_one _ := hm.le_one _
  star_apply _ _ := hm.star_apply _ _
  le_mul _ _ _ := hm.le_mul _ _ _

namespace IsRelationalBasis

variable {B : Set (ι → ι → α)}

private theorem exists_apply_right (hB : IsRelationalBasis B) {m : ι → ι → α} (hm : m ∈ B)
    {p q k : ι} (hp : p ≠ k) (hq : q ≠ k) : ∃ m' ∈ B, m' p k = m p q := by
  obtain ⟨m', hm', h, -, -⟩ := hB.exists_apply_eq_apply_eq hm hp hq
    ((hB.isBasicMatrix hm).isAtom p q) ((hB.isBasicMatrix hm).isAtom q q)
    ((hB.isBasicMatrix hm).le_mul p q q)
  exact ⟨m', hm', h⟩

private theorem exists_apply_left (hB : IsRelationalBasis B) {m : ι → ι → α} (hm : m ∈ B)
    {p q k : ι} (hp : p ≠ k) (hq : q ≠ k) : ∃ m' ∈ B, m' k q = m p q := by
  obtain ⟨m', hm', -, h, -⟩ := hB.exists_apply_eq_apply_eq hm hp hq
    ((hB.isBasicMatrix hm).isAtom p p) ((hB.isBasicMatrix hm).isAtom p q)
    ((hB.isBasicMatrix hm).le_mul p p q)
  exact ⟨m', hm', h⟩

theorem exists_apply_eq_of_ne (hB : IsRelationalBasis B) {t i j : ι} (hij : i ≠ j)
    (hti : t ≠ i) (htj : t ≠ j) {a : α} (ha : IsAtom a) : ∃ m ∈ B, m i j = a := by
  obtain ⟨m, hm, p, q, hpq, rfl⟩ := hB.exists_apply_eq ha
  -- a position whose column is already `j` only needs its row moved
  have key : ∀ (p : ι) (m : ι → ι → α), m ∈ B → p ≠ j → ∃ m' ∈ B, m' i j = m p j := by
    intro p m hm hpj
    by_cases hpi : p = i
    · exact ⟨m, hm, by rw [hpi]⟩
    · exact hB.exists_apply_left hm hpi hij.symm
  by_cases hqj : q = j
  · subst hqj
    exact key p m hm hpq
  by_cases hjp : j = p
  · subst hjp
    by_cases hiq : i = q
    · subst hiq
      obtain ⟨m₁, hm₁, h₁⟩ := hB.exists_apply_left hm (k := t) htj.symm hti.symm
      obtain ⟨m₂, hm₂, h₂⟩ := hB.exists_apply_right hm₁ (p := t) (q := i) (k := j) htj hij
      obtain ⟨m₃, hm₃, h₃⟩ := key t m₂ hm₂ htj
      exact ⟨m₃, hm₃, by rw [h₃, h₂, h₁]⟩
    · obtain ⟨m₁, hm₁, h₁⟩ := hB.exists_apply_left hm (k := i) hij.symm (Ne.symm hiq)
      obtain ⟨m₂, hm₂, h₂⟩ := hB.exists_apply_right hm₁ (p := i) (q := q) (k := j) hij hqj
      exact ⟨m₂, hm₂, by rw [h₂, h₁]⟩
  · obtain ⟨m₁, hm₁, h₁⟩ := hB.exists_apply_right hm (p := p) (q := q) (k := j) (Ne.symm hjp) hqj
    obtain ⟨m₂, hm₂, h₂⟩ := key p m₁ hm₁ (Ne.symm hjp)
    exact ⟨m₂, hm₂, by rw [h₂, h₁]⟩

theorem comap (hB : IsRelationalBasis B) {f : ι' → ι} (hf : Function.Injective f)
    (hex : ∀ {a : α}, IsAtom a → ∃ m ∈ B, ∃ p q : ι', p ≠ q ∧ m (f p) (f q) = a) :
    IsRelationalBasis ((fun (m : ι → ι → α) p q => m (f p) (f q)) '' B) where
  isBasicMatrix := by
    rintro _ ⟨m, hm, rfl⟩
    exact (hB.isBasicMatrix hm).comp f
  exists_apply_eq ha :=
    let ⟨m, hm, p, q, hpq, h⟩ := hex ha
    ⟨_, ⟨m, hm, rfl⟩, p, q, hpq, h⟩
  exists_apply_eq_apply_eq := by
    rintro _ i j k a b ⟨m, hm, rfl⟩ hik hjk ha hb hab
    obtain ⟨m', hm', h₁, h₂, h₃⟩ :=
      hB.exists_apply_eq_apply_eq hm (hf.ne hik) (hf.ne hjk) ha hb hab
    exact ⟨_, ⟨m', hm', rfl⟩, h₁, h₂, fun l h hl hh => h₃ _ _ (hf.ne hl) (hf.ne hh)⟩

end IsRelationalBasis

namespace Dimensional

theorem of_equiv (e : ι ≃ ι') (h : Dimensional α ι) : Dimensional α ι' := by
  obtain ⟨β, _, f, hf, hβ, B, hB⟩ := h
  refine ⟨β, _, f, hf, hβ, _, hB.comap e.symm.injective fun ha => ?_⟩
  obtain ⟨m, hm, i, j, hij, h⟩ := hB.exists_apply_eq ha
  exact ⟨m, hm, e i, e j, e.injective.ne hij, by simpa using h⟩

theorem of_injective {f : ι' → ι} (hf : Function.Injective f) {p q r : ι'} (hpq : p ≠ q)
    (hrp : r ≠ p) (hrq : r ≠ q) (h : Dimensional α ι) : Dimensional α ι' := by
  obtain ⟨β, _, g, hg, hβ, B, hB⟩ := h
  refine ⟨β, _, g, hg, hβ, _, hB.comap hf fun ha => ?_⟩
  obtain ⟨m, hm, h⟩ := hB.exists_apply_eq_of_ne (hf.ne hpq) (hf.ne hrp) (hf.ne hrq) ha
  exact ⟨m, hm, p, q, hpq, h⟩

end Dimensional

theorem dimensional_congr (e : ι ≃ ι') : Dimensional α ι ↔ Dimensional α ι' :=
  ⟨.of_equiv e, .of_equiv e.symm⟩

theorem ra_natCast_iff {n : ℕ} : RA α n ↔ Dimensional α (Fin n) :=
  dimensional_congr
    { toFun i := ⟨i.1, ENat.natCast_lt_natCast.mp i.2⟩
      invFun i := ⟨i.1, ENat.natCast_lt_natCast.mpr i.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }

theorem ra_top_iff : RA α ⊤ ↔ Dimensional α ℕ :=
  dimensional_congr <| Equiv.subtypeUnivEquiv ENat.natCast_lt_top

theorem RA.mono {m n : ℕ∞} (hm : 3 ≤ m) (hmn : m ≤ n) (h : RA α n) : RA α m := by
  have hlt : ∀ i : ℕ, i < 3 → (i : ℕ∞) < m := fun i hi =>
    (ENat.natCast_lt_natCast.mpr hi).trans_le hm
  let f : {i : ℕ // (i : ℕ∞) < m} → {i : ℕ // (i : ℕ∞) < n} := fun i => ⟨i, i.2.trans_le hmn⟩
  have hf : Function.Injective f := fun i j hij => Subtype.ext (congrArg Subtype.val hij :)
  exact Dimensional.of_injective hf (p := ⟨0, hlt 0 (by decide)⟩) (q := ⟨1, hlt 1 (by decide)⟩)
    (r := ⟨2, hlt 2 (by decide)⟩) (by simp) (by simp) (by simp) h

end Cslib.RelationAlgebra
