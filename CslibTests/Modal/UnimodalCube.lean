/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Logics.Modal.Unimodal.Cube

namespace Cslib.Logic.Modal.Unimodal

open scoped Proposition

variable {World Atom : Type*} {φ : Proposition Atom}

-- Compound modal logics contain conjunctions of the axioms validated by their combined frame
-- conditions. Defining them as unions of the individual logics loses these conjunctions.

example : ((◇◇φ → ◇φ) ∧ (◇φ → □◇φ) : Proposition Atom) ∈ K45 World Atom := by
  intro m h w
  let : IsTrans World m.rel := h.1
  let : Relation.RightEuclidean m.rel := h.2
  apply Satisfies.and_iff_and.mpr
  exact ⟨Satisfies.unimodal_four _ φ _ _, Satisfies.unimodal_five _ φ _ _⟩

example : ((□φ → ◇φ) ∧ (◇◇φ → ◇φ) : Proposition Atom) ∈ D4 World Atom := by
  intro m h w
  let : Relation.Serial m.rel := h.1
  let : IsTrans World m.rel := h.2
  apply Satisfies.and_iff_and.mpr
  exact ⟨Satisfies.d _ φ _ _, Satisfies.unimodal_four _ φ _ _⟩

example : ((□φ → ◇φ) ∧ (◇φ → □◇φ) : Proposition Atom) ∈ D5 World Atom := by
  intro m h w
  let : Relation.Serial m.rel := h.1
  let : Relation.RightEuclidean m.rel := h.2
  apply Satisfies.and_iff_and.mpr
  exact ⟨Satisfies.d _ φ _ _, Satisfies.unimodal_five _ φ _ _⟩

example :
    Proposition.and (□φ → ◇φ) (Proposition.and (◇◇φ → ◇φ) (◇φ → □◇φ)) ∈
      D45 World Atom := by
  intro m h w
  let : Relation.Serial m.rel := h.1
  let : IsTrans World m.rel := h.2.1
  let : Relation.RightEuclidean m.rel := h.2.2
  simp only [Proposition.and_def, Satisfies.and_iff_and]
  exact ⟨Satisfies.d _ φ _ _, Satisfies.unimodal_four _ φ _ _, Satisfies.unimodal_five _ φ _ _⟩

example : ((□φ → ◇φ) ∧ (φ → □◇φ) : Proposition Atom) ∈ DB World Atom := by
  intro m h w
  let : Relation.Serial m.rel := h.1
  let : Std.Symm m.rel := h.2
  apply Satisfies.and_iff_and.mpr
  exact ⟨Satisfies.d _ φ _ _, Satisfies.unimodal_b _ φ _ _⟩

example : ((φ → ◇φ) ∧ (φ → □◇φ) : Proposition Atom) ∈ TB World Atom := by
  intro m h w
  let : Std.Refl m.rel := h.1
  let : Std.Symm m.rel := h.2
  apply Satisfies.and_iff_and.mpr
  exact ⟨Satisfies.t _ φ _ _, Satisfies.unimodal_b _ φ _ _⟩

example : ((φ → □◇φ) ∧ (◇φ → □◇φ) : Proposition Atom) ∈ KB5 World Atom := by
  intro m h w
  let : Std.Symm m.rel := h.1
  let : Relation.RightEuclidean m.rel := h.2
  apply Satisfies.and_iff_and.mpr
  exact ⟨Satisfies.unimodal_b _ φ _ _, Satisfies.unimodal_five _ φ _ _⟩

example : ((φ → ◇φ) ∧ (◇◇φ → ◇φ) : Proposition Atom) ∈ S4 World Atom := by
  intro m h w
  let : Std.Refl m.rel := h.1
  let : IsTrans World m.rel := h.2
  apply Satisfies.and_iff_and.mpr
  exact ⟨Satisfies.t _ φ _ _, Satisfies.unimodal_four _ φ _ _⟩

example :
    Proposition.and (φ → ◇φ) (Proposition.and (◇◇φ → ◇φ) (◇φ → □◇φ)) ∈
      S5 World Atom := by
  intro m h w
  let : Std.Refl m.rel := h.1
  let : IsTrans World m.rel := h.2.1
  let : Relation.RightEuclidean m.rel := h.2.2
  simp only [Proposition.and_def, Satisfies.and_iff_and]
  exact ⟨Satisfies.t _ φ _ _, Satisfies.unimodal_four _ φ _ _, Satisfies.unimodal_five _ φ _ _⟩

end Cslib.Logic.Modal.Unimodal
