/-
Copyright (c) 2026 Shaopeng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaopeng Zhu
-/

module

public import Cslib.MachineLearning.PACLearning.Defs

/-! # Realizable Distributions

For a concept class `C`, a distribution `D` on `α × β` is *realizable* by `C` when some concept in
`C` has zero true error under `D`. This is the realizability assumption of
[ShalevShwartzBenDavid2014] (Definition 2.1, stated there for a domain distribution together with a
labelling function), transported to joint distributions with the 0-1 risk of their Equation (3.1).
The resulting family is the one with respect to which realizable PAC learning is defined.

## Main definitions

- `IsRealizableBy`: a distribution has a zero-error concept in a given concept class.
- `realizableDistributions`: the family of distributions realizable by a concept class.

## Main results

- `IsRealizableBy.mono`: realizability is monotone in the concept class.
- `realizableDistributions_mono`: the realizable distribution family is monotone in the
  concept class.
- `IsRealizableBy.optimalError_eq_zero`: realizability implies zero optimal error.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

@[expose] public section

open MeasureTheory

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A distribution `D` is *realizable* by a concept class `C` if some concept in `C` has
zero true error under `D`. -/
def IsRealizableBy (D : Measure (α × β)) (C : ConceptClass α β) : Prop :=
  ∃ h ∈ C, error D h = 0

/-- The family of distributions realizable by a concept class `C`. -/
def realizableDistributions (C : ConceptClass α β) : Set (Measure (α × β)) :=
  {D | IsRealizableBy D C}

/-- Realizability is monotone in the concept class: a distribution realizable by `C` is
also realizable by every superclass `C'`. -/
theorem IsRealizableBy.mono {D : Measure (α × β)} {C C' : ConceptClass α β}
    (hC : C ⊆ C') (h : IsRealizableBy D C) : IsRealizableBy D C' := by
  obtain ⟨c, hc, herror⟩ := h
  exact ⟨c, hC hc, herror⟩

/-- The family of realizable distributions is monotone in the concept class. -/
theorem realizableDistributions_mono {C C' : ConceptClass α β} (hC : C ⊆ C') :
    realizableDistributions C ⊆ realizableDistributions C' :=
  fun _ h => h.mono hC

/-- A concept class that realizes `D` has zero optimal error under `D`.

The converse is false in general because the infimum defining `optimalError` need not be
attained by a concept in the class. -/
theorem IsRealizableBy.optimalError_eq_zero {D : Measure (α × β)}
    {C : ConceptClass α β} (h : IsRealizableBy D C) : optimalError D C = 0 := by
  obtain ⟨c, hc, herror⟩ := h
  apply le_antisymm ?_ bot_le
  calc
    optimalError D C ≤ error D c := iInf_le_of_le c (iInf_le_of_le hc le_rfl)
    _ = 0 := herror

end Cslib.MachineLearning.PACLearning
