/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Atomic
public import Cslib.Foundations.RelationAlgebra.Classification

/-!
# Atom labellings from finite signatures

The atom counts in a relation-algebra signature yield concrete labellings of the Boolean atoms.
The labellings preserve identity and converse, as required by the atomic reconstruction theorem.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {A : Type*} [RelationAlgebra A]

/-- The three indices consisting of identity and one converse pair exhaust `Atom 0 1`. -/
theorem atom_zero_one_cases (x : Atom 0 1) :
    x = none ∨ x = some (.inr (0, false)) ∨ x = some (.inr (0, true)) := by
  rcases x with _ | x
  · exact Or.inl rfl
  rcases x with x | ⟨i, b⟩
  · exact Fin.elim0 x
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  cases b <;> simp

/-- An integral finite signature supplies an identity- and converse-preserving atom labelling. -/
noncomputable def AtomLabelling.ofHasSignature {j k : ℕ} (h : HasSignature A 1 j k) :
    AtomLabelling A j k := by
  let : Finite A := h.1
  exact AtomLabelling.ofCardinalities (integral_of_hasSignature_one h) h.2.2.1 h.2.2.2

end Cslib.RelationAlgebra
