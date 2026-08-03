/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.OmegaLanguage
public import Cslib.Foundations.Data.Topology.ClosedDenseDecomposition

/-!
# Safety and Liveness properties of ω-sequences

This file formalizes the main results of [AlpernSchneider1985].  Namely, given
an appropriate topology on ω-sequences:
* Safety properties can be identified with closed sets.
* Liveness properties can be identified with dense sets.
* Every property is the intersection of a safety property and a liveness property.

## References
* [Alpern, Bowen; Schneider, Fred B. (1985). "Defining liveness".
Information Processing Letters. 21 (4): 181–185.][AlpernSchneider1985]
-/

@[expose] public section

namespace Cslib.ωLanguage

open Set ωSequence TopologicalSpace

variable {α : Type*}

/-- Safety properties are identified with closed sets. -/
abbrev IsSafety (p : ωLanguage α) : Prop := IsClosed p.toSet

/-- An alternative characterization of `IsSafety` that justifies its definition:
if an ω-sequence violates a safety property, then it has a finite prefix all of whose
infinite extensions also violate the property. -/
theorem isSafety_iff (p : ωLanguage α) :
    p.IsSafety ↔ ∀ xs, xs ∉ p → ∃ n, ∀ ys, (xs.take n) ++ω ys ∉ p := by
  simp [← isOpen_compl_iff, isOpen_iff, mem_def]

/-- Liveness properties are identified with dense sets. -/
abbrev IsLiveness (p : ωLanguage α) : Prop := Dense p.toSet

/-- An alternative characterization of `IsLiveness` that justifies its definition:
any finite sequence can be extended to an infinite sequence satisfying a liveness property. -/
theorem isLiveness_iff (p : ωLanguage α) :
    p.IsLiveness ↔ ∀ (xs : ωSequence α) (n : ℕ), ∃ ys, (xs.take n) ++ω ys ∈ p := by
  exact Dense_iff p.toSet

/-- `SafetyLivenessDecomposition p ps pl` means that `ps` is a safety property,
`pl` is a liveness property, and `ps ⊓ pl = p`. -/
def SafetyLivenessDecomposition (p ps pl : ωLanguage α) : Prop :=
  IsSafety ps ∧ IsLiveness pl ∧ ps ⊓ pl = p

/-- Every property `p` is the intersection of the safety property `p.closure` and
the liveness property `p ⊔ p.closureᶜ`. -/
theorem SafetyLivenessDecomposition_exists (p : ωLanguage α) :
    SafetyLivenessDecomposition p p.closure (p ⊔ p.closureᶜ) := by
  obtain ⟨_, _, _⟩ := ClosedDenseDecomposition_exists p.toSet
  split_ands
  · simpa
  · simpa [sup_def, closure, compl_def]
  · simpa [ωLanguage.ext_iff, sup_def, closure, compl_def]

end Cslib.ωLanguage
