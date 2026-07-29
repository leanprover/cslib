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
  letI : IsTrans World m.r := h.1
  letI : Relation.RightEuclidean m.r := h.2
  exact ⟨Satisfies.four φ, Satisfies.five φ⟩

example : ((□φ → ◇φ) ∧ (◇◇φ → ◇φ) : Proposition Atom) ∈ D4 World Atom := by
  intro m h w
  letI : Relation.Serial m.r := h.1
  letI : IsTrans World m.r := h.2
  exact ⟨Satisfies.d φ, Satisfies.four φ⟩

example : ((□φ → ◇φ) ∧ (◇φ → □◇φ) : Proposition Atom) ∈ D5 World Atom := by
  intro m h w
  letI : Relation.Serial m.r := h.1
  letI : Relation.RightEuclidean m.r := h.2
  exact ⟨Satisfies.d φ, Satisfies.five φ⟩

example :
    Proposition.and (□φ → ◇φ) (Proposition.and (◇◇φ → ◇φ) (◇φ → □◇φ)) ∈
      D45 World Atom := by
  intro m h w
  letI : Relation.Serial m.r := h.1
  letI : IsTrans World m.r := h.2.1
  letI : Relation.RightEuclidean m.r := h.2.2
  exact ⟨Satisfies.d φ, Satisfies.four φ, Satisfies.five φ⟩

example : ((□φ → ◇φ) ∧ (φ → □◇φ) : Proposition Atom) ∈ DB World Atom := by
  intro m h w
  letI : Relation.Serial m.r := h.1
  letI : Std.Symm m.r := h.2
  exact ⟨Satisfies.d φ, Satisfies.b φ⟩

example : ((φ → ◇φ) ∧ (φ → □◇φ) : Proposition Atom) ∈ TB World Atom := by
  intro m h w
  letI : Std.Refl m.r := h.1
  letI : Std.Symm m.r := h.2
  exact ⟨Satisfies.t φ, Satisfies.b φ⟩

example : ((φ → □◇φ) ∧ (◇φ → □◇φ) : Proposition Atom) ∈ KB5 World Atom := by
  intro m h w
  letI : Std.Symm m.r := h.1
  letI : Relation.RightEuclidean m.r := h.2
  exact ⟨Satisfies.b φ, Satisfies.five φ⟩

example : ((φ → ◇φ) ∧ (◇◇φ → ◇φ) : Proposition Atom) ∈ S4 World Atom := by
  intro m h w
  letI : Std.Refl m.r := h.1
  letI : IsTrans World m.r := h.2
  exact ⟨Satisfies.t φ, Satisfies.four φ⟩

example :
    Proposition.and (φ → ◇φ) (Proposition.and (◇◇φ → ◇φ) (◇φ → □◇φ)) ∈
      S5 World Atom := by
  intro m h w
  letI : Std.Refl m.r := h.1
  letI : IsTrans World m.r := h.2.1
  letI : Relation.RightEuclidean m.r := h.2.2
  exact ⟨Satisfies.t φ, Satisfies.four φ, Satisfies.five φ⟩

end Cslib.Logic.Modal
