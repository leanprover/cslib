/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.MachineLearning.PACLearning.Defs
public import Mathlib.Combinatorics.SetFamily.Shatter

@[expose] public section

/-! # VC Dimension for Concept Classes

This file defines *shattering* and the *Vapnik-Chervonenkis dimension* for
concept classes modeled as `Set (Set α)`.  See also the `Finset`-based
definitions in `Mathlib.Combinatorics.SetFamily.Shatter`.

The VC dimension of a concept class `C` is the cardinality of the largest
finite set that `C` shatters: a set `W` is shattered by `C` if every
subset of `W` can be obtained as the intersection of `W` with some
concept in `C`.

## Main definitions

- `SetShatters C W`: the concept class `C` shatters the set `W`.
- `vcDim C`: the VC dimension of `C`, i.e., the supremum of the
  cardinalities of finite sets shattered by `C`.

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

open Set

namespace Cslib.MachineLearning

/-- A concept class `C` *shatters* a set `W` if for every subset `W'`
of `W`, there exists a concept `c ∈ C` such that `c ∩ W = W'`. -/
def SetShatters (C : ConceptClass α) (W : Set α) : Prop :=
  ∀ W' ⊆ W, ∃ c ∈ C, c ∩ W = W'

/-- Shattering is anti-monotone in the shattered set: if `C` shatters
`W` and `V ⊆ W`, then `C` shatters `V`. -/
theorem SetShatters.subset {C : ConceptClass α} {W V : Set α}
    (hW : SetShatters C W) (hVW : V ⊆ W) : SetShatters C V := by
  intro V' hV'V
  -- We need c ∈ C with c ∩ V = V'.
  -- Use that C shatters W: pick c with c ∩ W = V' ∪ (W \ V).
  have hV'W : V' ⊆ W := hV'V.trans hVW
  have hsub : V' ∪ (W \ V) ⊆ W :=
    union_subset hV'W diff_subset
  obtain ⟨c, hc, hc_eq⟩ := hW (V' ∪ (W \ V)) hsub
  refine ⟨c, hc, ?_⟩
  ext x
  simp only [mem_inter_iff]
  constructor
  · intro ⟨hxc, hxV⟩
    have hxW : x ∈ W := hVW hxV
    have : x ∈ c ∩ W := ⟨hxc, hxW⟩
    rw [hc_eq] at this
    exact this.elim (fun h => h) (fun ⟨_, hxnV⟩ => absurd hxV hxnV)
  · intro hxV'
    have hxV : x ∈ V := hV'V hxV'
    have : x ∈ V' ∪ (W \ V) := Or.inl hxV'
    rw [← hc_eq] at this
    exact ⟨this.1, hxV⟩

/-- Shattering is monotone in the concept class: if `C` shatters
`W` and `C ⊆ C'`, then `C'` shatters `W`. -/
theorem SetShatters.superset {C C' : ConceptClass α} {W : Set α}
    (hW : SetShatters C W) (hCC' : C ⊆ C') : SetShatters C' W := by
  intro W' hW'
  obtain ⟨c, hc, hcW⟩ := hW W' hW'
  exact ⟨c, hCC' hc, hcW⟩

open Classical in
/-- If a finite set family `𝒜` shatters a finite set `s` in the sense of
Mathlib's `Finset.Shatters`, then the coerced concept class shatters `↑s`
in the sense of `SetShatters`. This bridges Mathlib's finset-based shattering
to the set-based notion used by the PAC learning lower bounds. -/
theorem Finset.Shatters.toSetShatters {𝒜 : Finset (Finset α)} {s : Finset α}
    (h : 𝒜.Shatters s) :
    SetShatters {c : Set α | ∃ t ∈ 𝒜, (↑t : Set α) = c} ↑s := by
  intro W' hW'
  have hfin : Set.Finite W' := s.finite_toSet.subset hW'
  set t := hfin.toFinset
  have ht_eq : (↑t : Set α) = W' := hfin.coe_toFinset
  have ht_sub : t ⊆ s := Finset.coe_subset.mp (ht_eq ▸ hW')
  obtain ⟨u, hu, hsu⟩ := h ht_sub
  have hut : u ∩ s = t := by rwa [Finset.inter_comm] at hsu
  exact ⟨↑u, ⟨u, hu, rfl⟩, by rw [← ht_eq]; exact_mod_cast hut⟩

/-- The *Vapnik-Chervonenkis dimension* of a concept class `C` is the
supremum of the cardinalities of finite sets shattered by `C`.
Returns `0` when no finite set is shattered (i.e., the defining set is empty).

**Caveat**: because `sSup` on `ℕ` returns `0` for unbounded sets, this definition
is only meaningful when the VC dimension is finite. -/
noncomputable def vcDim (C : ConceptClass α) : ℕ :=
  sSup {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)}

end Cslib.MachineLearning
