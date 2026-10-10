/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.MachineLearning.PACLearning.Defs
public import Mathlib.Combinatorics.SetFamily.Shatter

/-! # VC Dimension for Concept Classes

This file defines *shattering* and the *Vapnik-Chervonenkis dimension* for
binary concept classes `C : ConceptClass α Bool`, i.e. sets of `α → Bool`
classifiers. Each Boolean classifier `c` is identified with the subset
`c ⁻¹' {true} ⊆ α` (the "positive set"), and `C` shatters a set `W` if every
subset of `W` can be obtained as the positive set of some `c ∈ C` intersected
with `W`. See also the `Finset`-based definitions in
`Mathlib.Combinatorics.SetFamily.Shatter`.

## Main definitions

- `SetShatters C W`: the concept class `C` shatters the set `W`.
- `vcDim C`: the VC dimension of `C`, i.e. the supremum of the cardinalities of
  finite sets shattered by `C`.

## Main statements

- `SetShatters.subset`: shattering is anti-monotone in the shattered set.
- `SetShatters.superset`: shattering is monotone in the concept class.
- `Finset.Shatters.toSetShatters`: bridge from Mathlib's `Finset.Shatters`
  to `SetShatters`.

## References

* [A. Ehrenfeucht, D. Haussler, M. Kearns, L. Valiant,
  *A General Lower Bound on the Number of Examples Needed
  for Learning*][EHKV1989]
-/

@[expose] public section

open Set

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-- A binary concept class `C` *shatters* a set `W` if for every subset `W' ⊆ W`,
there exists a concept `c ∈ C` whose positive set `c ⁻¹' {true}` intersects `W`
in exactly `W'`. -/
def SetShatters (C : ConceptClass α Bool) (W : Set α) : Prop :=
  ∀ W' ⊆ W, ∃ c ∈ C, c ⁻¹' {true} ∩ W = W'

/-- Shattering is anti-monotone in the shattered set: if `C` shatters `W` and
`V ⊆ W`, then `C` shatters `V`. -/
theorem SetShatters.subset {C : ConceptClass α Bool} {W V : Set α}
    (hW : SetShatters C W) (hVW : V ⊆ W) : SetShatters C V := by
  intro V' hV'V
  obtain ⟨c, hc, hc_eq⟩ := hW (V' ∪ (W \ V))
    (union_subset (hV'V.trans hVW) sdiff_subset)
  refine ⟨c, hc, ?_⟩
  rw [show V = W ∩ V from (inter_eq_self_of_subset_right hVW).symm,
    ← inter_assoc, hc_eq]
  ext x
  simp only [mem_inter_iff, mem_union, mem_sdiff]
  refine ⟨?_, fun h => ⟨Or.inl h, hV'V h⟩⟩
  rintro ⟨h1 | ⟨_, h2⟩, h3⟩
  · exact h1
  · exact absurd h3 h2

/-- Shattering is monotone in the concept class: if `C` shatters `W` and `C ⊆ C'`,
then `C'` shatters `W`. -/
theorem SetShatters.superset {C C' : ConceptClass α Bool} {W : Set α}
    (hW : SetShatters C W) (hCC' : C ⊆ C') : SetShatters C' W := by
  intro W' hW'
  obtain ⟨c, hc, hcW⟩ := hW W' hW'
  exact ⟨c, hCC' hc, hcW⟩

open scoped Classical in
/-- If a finite set family `𝒜` shatters a finite set `s` in the sense of Mathlib's
`Finset.Shatters`, then the concept class of characteristic functions of sets in `𝒜`
shatters `↑s` in the sense of `SetShatters`. This bridges Mathlib's finset-based
shattering to the predicate used by the PAC learning lower bounds. -/
theorem _root_.Finset.Shatters.toSetShatters {𝒜 : Finset (Finset α)} {s : Finset α}
    (h : 𝒜.Shatters s) :
    SetShatters
      {c : α → Bool | ∃ t ∈ 𝒜, ∀ x, c x = decide (x ∈ t)} ↑s := by
  intro W' hW'
  have hfin : Set.Finite W' := s.finite_toSet.subset hW'
  set t := hfin.toFinset
  have ht_eq : (↑t : Set α) = W' := hfin.coe_toFinset
  have ht_sub : t ⊆ s := Finset.coe_subset.mp (ht_eq ▸ hW')
  obtain ⟨u, hu, hsu⟩ := h ht_sub
  have hut : u ∩ s = t := by rwa [Finset.inter_comm] at hsu
  refine ⟨fun x => decide (x ∈ u), ⟨u, hu, fun _ => rfl⟩, ?_⟩
  rw [← ht_eq]
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff,
    decide_eq_true_eq, Finset.mem_coe]
  exact ⟨fun ⟨h1, h2⟩ => hut ▸ Finset.mem_inter.mpr ⟨h1, h2⟩,
    fun h => Finset.mem_inter.mp (hut.symm ▸ h)⟩

/-- The *Vapnik-Chervonenkis dimension* of a binary concept class `C` is the
supremum of the cardinalities of finite sets shattered by `C`. Returns `0` when
no finite set is shattered (i.e. the defining set is empty).

**Caveat**: because `sSup` on `ℕ` returns `0` for unbounded sets, this definition
is only meaningful when the VC dimension is finite — see `HasFiniteVCDim`. -/
noncomputable def vcDim (C : ConceptClass α Bool) : ℕ :=
  sSup {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)}

/-- A binary concept class `C` has *finite VC dimension* if there is a uniform
upper bound on the cardinalities of finite sets it shatters. This is the
hypothesis under which `vcDim C` is mathematically meaningful (otherwise
`vcDim` returns `0` for unbounded shattered families via `sSup` on `ℕ`). -/
def HasFiniteVCDim (C : ConceptClass α Bool) : Prop :=
  BddAbove {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)}

/-- A class has finite VC dimension iff there is a uniform bound on the
cardinality of every shattered finite set. -/
theorem hasFiniteVCDim_iff {C : ConceptClass α Bool} :
    HasFiniteVCDim C ↔ ∃ N : ℕ, ∀ W : Finset α, SetShatters C ↑W → W.card ≤ N :=
  ⟨fun ⟨N, hN⟩ => ⟨N, fun W hW => hN ⟨W, rfl, hW⟩⟩,
   fun ⟨N, hN⟩ => ⟨N, fun _ ⟨W, hWc, hW⟩ => hWc ▸ hN W hW⟩⟩

end Cslib.MachineLearning.PACLearning
