/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marianna Girlando
-/

module

public import Cslib.Logics.Modal.Basic
public import Cslib.Foundations.Relation.Euclidean

/-! # Modal Logic Cube

This module formalises the Modal Cube, including all the 15 foundational modal logics and their
relationships.

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]

-/

@[expose] public section

namespace Cslib.Logic.Modal

/-- The modal logic K. -/
@[scoped grind =]
def K World Atom := logic (Set.univ (α := Model World Atom))

/-- The modal logic T. -/
@[scoped grind =]
def T World Atom := logic {m : Model World Atom | Std.Refl m.r}

/-- The modal logic B. -/
@[scoped grind =]
def B World Atom := logic {m : Model World Atom | Std.Symm m.r}

/-- The modal logic 4. -/
@[scoped grind =]
def Four World Atom := logic {m : Model World Atom | IsTrans World m.r}

/-- The modal logic 5. -/
@[scoped grind =]
def Five World Atom := logic {m : Model World Atom | Relation.RightEuclidean m.r}

/-- The modal logic K45. -/
@[scoped grind =]
def K45 World Atom :=
  logic {m : Model World Atom | IsTrans World m.r ∧ Relation.RightEuclidean m.r}

/-- The modal logic D. -/
@[scoped grind =]
def D World Atom := logic {m : Model World Atom | Relation.Serial m.r}

/-- The modal logic D4. -/
@[scoped grind =]
def D4 World Atom :=
  logic {m : Model World Atom | Relation.Serial m.r ∧ IsTrans World m.r}

/-- The modal logic D5. -/
@[scoped grind =]
def D5 World Atom :=
  logic {m : Model World Atom | Relation.Serial m.r ∧ Relation.RightEuclidean m.r}

/-- The modal logic D45. -/
@[scoped grind =]
def D45 World Atom :=
  logic {m : Model World Atom |
    Relation.Serial m.r ∧ IsTrans World m.r ∧ Relation.RightEuclidean m.r}

/-- The modal logic DB. -/
@[scoped grind =]
def DB World Atom :=
  logic {m : Model World Atom | Relation.Serial m.r ∧ Std.Symm m.r}

/-- The modal logic TB. -/
@[scoped grind =]
def TB World Atom :=
  logic {m : Model World Atom | Std.Refl m.r ∧ Std.Symm m.r}

/-- The modal logic KB5. -/
@[scoped grind =]
def KB5 World Atom :=
  logic {m : Model World Atom | Std.Symm m.r ∧ Relation.RightEuclidean m.r}

/-- The modal logic S4. -/
@[scoped grind =]
def S4 World Atom :=
  logic {m : Model World Atom | Std.Refl m.r ∧ IsTrans World m.r}

/-- The modal logic S5. -/
@[scoped grind =]
def S5 World Atom :=
  logic {m : Model World Atom |
    Std.Refl m.r ∧ IsTrans World m.r ∧ Relation.RightEuclidean m.r}

section Order

/-! ## Ordering of Modal Logics

This section proves the essential inclusions of modal logics. Inclusions among compound logics
follow by forgetting frame conditions in their defining model classes.
-/

open scoped Proposition
open Set

theorem k_subset_d : K World Atom ⊆ D World Atom := by
  grind only [subset_def, D, K, = ofPred_true, = logic, mem_ofPred_eq, = Proposition.valid]

theorem k_subset_b : K World Atom ⊆ B World Atom := by
  grind only [subset_def, B, K, = ofPred_true, = logic, mem_ofPred_eq, = Proposition.valid]

theorem k_subset_four : K World Atom ⊆ Four World Atom := by
  grind only [subset_def, Four, K, = ofPred_true, = logic, mem_ofPred_eq, = Proposition.valid]

theorem k_subset_five : K World Atom ⊆ Five World Atom := by
  grind only [subset_def, Five, K, = ofPred_true, = logic, mem_ofPred_eq, = Proposition.valid]

open scoped Relation in
theorem d_subset_t : D World Atom ⊆ T World Atom := by
  grind

theorem k_subset_t : (K World Atom ⊆ T World Atom) := by
  calc
    K World Atom ⊆ D World Atom := k_subset_d
    D World Atom ⊆ T World Atom := d_subset_t

end Order

section Validity

/-! ## Validity

This section showcases how to prove the expected validities in the different modal logics.
-/

open InferenceSystem

open scoped Satisfies

/-- The axiom K is valid in the logic K. -/
theorem K.k_valid : (□(φ₁ → φ₂) → (□φ₁ → □φ₂) : Proposition Atom) ∈ K World Atom := by
  open scoped Proposition in grind [Satisfies.k]

/-- The axiom T is valid in the logic T. -/
theorem T.t_valid : (φ → ◇φ : Proposition Atom) ∈ T World Atom := by
  intro _ h
  grind [Satisfies.t (instRefl := h)]

end Validity

end Cslib.Logic.Modal
