/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Logics.Modal.Cube

namespace Cslib.Logic.Modal

open scoped Proposition

variable {World Atom : Type*} {φ : Proposition Atom}

-- Compound modal logics contain conjunctions of the axioms validated by their combined frame
-- conditions. Defining them as unions of the individual logics loses these conjunctions.

example : ((◇◇φ → ◇φ) ∧ (◇φ → □◇φ) : Proposition Atom) ∈ K45 World Atom := by
  intro m h w
  let : IsTrans World m.r := h.1
  let : Relation.RightEuclidean m.r := h.2
  exact ⟨Satisfies.four _ φ _ _, Satisfies.five _ φ _ _⟩

example : ((□φ → ◇φ) ∧ (◇◇φ → ◇φ) : Proposition Atom) ∈ D4 World Atom := by
  intro m h w
  let : Relation.Serial m.r := h.1
  let : IsTrans World m.r := h.2
  exact ⟨Satisfies.d _ φ _ _, Satisfies.four _ φ _ _⟩

example : ((□φ → ◇φ) ∧ (◇φ → □◇φ) : Proposition Atom) ∈ D5 World Atom := by
  intro m h w
  let : Relation.Serial m.r := h.1
  let : Relation.RightEuclidean m.r := h.2
  exact ⟨Satisfies.d _ φ _ _, Satisfies.five _ φ _ _⟩

example :
    Proposition.and (□φ → ◇φ) (Proposition.and (◇◇φ → ◇φ) (◇φ → □◇φ)) ∈
      D45 World Atom := by
  intro m h w
  let : Relation.Serial m.r := h.1
  let : IsTrans World m.r := h.2.1
  let : Relation.RightEuclidean m.r := h.2.2
  exact ⟨Satisfies.d _ φ _ _, Satisfies.four _ φ _ _, Satisfies.five _ φ _ _⟩

example : ((□φ → ◇φ) ∧ (φ → □◇φ) : Proposition Atom) ∈ DB World Atom := by
  intro m h w
  let : Relation.Serial m.r := h.1
  let : Std.Symm m.r := h.2
  exact ⟨Satisfies.d _ φ _ _, Satisfies.b _ φ _ _⟩

example : ((φ → ◇φ) ∧ (φ → □◇φ) : Proposition Atom) ∈ TB World Atom := by
  intro m h w
  let : Std.Refl m.r := h.1
  let : Std.Symm m.r := h.2
  exact ⟨Satisfies.t _ φ _ _, Satisfies.b _ φ _ _⟩

example : ((φ → □◇φ) ∧ (◇φ → □◇φ) : Proposition Atom) ∈ KB5 World Atom := by
  intro m h w
  let : Std.Symm m.r := h.1
  let : Relation.RightEuclidean m.r := h.2
  exact ⟨Satisfies.b _ φ _ _, Satisfies.five _ φ _ _⟩

example : ((φ → ◇φ) ∧ (◇◇φ → ◇φ) : Proposition Atom) ∈ S4 World Atom := by
  intro m h w
  let : Std.Refl m.r := h.1
  let : IsTrans World m.r := h.2
  exact ⟨Satisfies.t _ φ _ _, Satisfies.four _ φ _ _⟩

example :
    Proposition.and (φ → ◇φ) (Proposition.and (◇◇φ → ◇φ) (◇φ → □◇φ)) ∈
      S5 World Atom := by
  intro m h w
  let : Std.Refl m.r := h.1
  let : IsTrans World m.r := h.2.1
  let : Relation.RightEuclidean m.r := h.2.2
  exact ⟨Satisfies.t _ φ _ _, Satisfies.four _ φ _ _, Satisfies.five _ φ _ _⟩

end Cslib.Logic.Modal
