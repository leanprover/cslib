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
- `evcDim C`: the extended-natural VC dimension, with `⊤` for infinite dimension.

## Main statements

- `SetShatters.subset`: shattering is anti-monotone in the shattered set.
- `SetShatters.superset`: shattering is monotone in the concept class.
- `Finset.Shatters.toSetShatters`: bridge from Mathlib's `Finset.Shatters`
  to `SetShatters`.
- `evcDim_mono`: extended VC dimension is monotone in the concept class.
- `evcDim_lt_top_iff`, `HasFiniteVCDim.coe_vcDim`: finiteness and the bridge to `vcDim`.

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
  intro V' hV'
  obtain ⟨c, hc, heq⟩ := hW V' (hV'.trans hVW)
  refine ⟨c, hc, ?_⟩
  calc
    c ⁻¹' {true} ∩ V = (c ⁻¹' {true} ∩ W) ∩ V := by
      rw [inter_assoc, inter_eq_right.mpr hVW]
    _ = V' := by rw [heq, inter_eq_left.mpr hV']

/-- Shattering is monotone in the concept class: if `C` shatters `W` and `C ⊆ C'`,
then `C'` shatters `W`. -/
theorem SetShatters.superset {C C' : ConceptClass α Bool} {W : Set α}
    (hW : SetShatters C W) (hCC' : C ⊆ C') : SetShatters C' W := by
  intro W' hW'
  obtain ⟨c, hc, hcW⟩ := hW W' hW'
  exact ⟨c, hCC' hc, hcW⟩

open Classical in
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
is only meaningful when the VC dimension is finite — see `HasFiniteVCDim`.
Use `evcDim` to distinguish infinite dimension from dimension zero. -/
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

/-- The extended-natural VC dimension. Unbounded shattered cardinalities give `⊤`,
while a class that shatters no nonempty finite set has dimension zero. -/
noncomputable def evcDim (C : ConceptClass α Bool) : ℕ∞ :=
  ⨆ W : Finset α, ⨆ _ : SetShatters C ↑W, (W.card : ℕ∞)

/-- Every shattered finite set has cardinality at most the extended VC dimension. -/
theorem SetShatters.card_le_evcDim {C : ConceptClass α Bool} {W : Finset α}
    (hW : SetShatters C ↑W) : (W.card : ℕ∞) ≤ evcDim C :=
  le_iSup₂_of_le W hW le_rfl

/-- An upper bound on the extended VC dimension is a bound on every shattered finite set. -/
theorem evcDim_le_iff {C : ConceptClass α Bool} {n : ℕ∞} :
    evcDim C ≤ n ↔ ∀ W : Finset α, SetShatters C ↑W → (W.card : ℕ∞) ≤ n :=
  iSup₂_le_iff

/-- Extended VC dimension is monotone in the concept class, even at infinite dimension. -/
theorem evcDim_mono {C C' : ConceptClass α Bool} (hC : C ⊆ C') :
    evcDim C ≤ evcDim C' :=
  evcDim_le_iff.mpr fun _ hW => (hW.superset hC).card_le_evcDim

/-- For finite VC dimension, the natural and extended-natural definitions agree. -/
theorem HasFiniteVCDim.coe_vcDim {C : ConceptClass α Bool} (hC : HasFiniteVCDim C) :
    (vcDim C : ℕ∞) = evcDim C := by
  rw [vcDim, ENat.natCast_sSup hC]
  refine le_antisymm (iSup₂_le ?_) (evcDim_le_iff.mpr ?_)
  · rintro n ⟨W, rfl, hW⟩
    exact hW.card_le_evcDim
  · intro W hW
    exact le_iSup₂_of_le W.card ⟨W, rfl, hW⟩ le_rfl

/-- Finite VC dimension is equivalent to the extended dimension being below infinity. -/
theorem evcDim_lt_top_iff {C : ConceptClass α Bool} :
    evcDim C < ⊤ ↔ HasFiniteVCDim C := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h.ne
    refine hasFiniteVCDim_iff.mpr ⟨n, fun W hW => ?_⟩
    exact_mod_cast hn ▸ hW.card_le_evcDim
  · intro h
    rw [← h.coe_vcDim]
    exact ENat.natCast_lt_top _

/-- The extended VC dimension is infinite precisely when shattered cardinalities are unbounded. -/
theorem evcDim_eq_top_iff {C : ConceptClass α Bool} :
    evcDim C = ⊤ ↔ ¬ HasFiniteVCDim C := by
  rw [← evcDim_lt_top_iff, not_lt, top_le_iff]

end Cslib.MachineLearning.PACLearning
