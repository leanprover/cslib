/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ExtFormula
public import Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ExtDerivation

/-!
# Substitution for Conservative Extension

This module defines the substitution `sigma[q -> bot]` that maps `ExtFormula` to `ExtFormula`
by replacing the fresh atom `q = Sum.inr ()` with `bot`. The key properties are:

1. `substFormula_preserves_qfree`: q-free formulas are fixed points of substitution
2. `substFormula_of_embedded`: embedded formulas are unchanged
3. Various structural lemmas for derived operators

These are the foundation for proving axiom closure and the lifting theorem.

## References

- Goldblatt 1992, Logics of Time and Computation
-/

set_option linter.style.emptyLine false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.ConservativeExtension

open Cslib.Logic.Bimodal

variable {Atom : Type u}

/-- Substitution sigma[q -> bot]: replace the fresh atom `Sum.inr ()` with `bot`.
All other atoms (of the form `Sum.inl a`) are unchanged. -/
def substFormula : ExtFormula Atom → ExtFormula Atom
  | ExtFormula.atom (Sum.inl a) => ExtFormula.atom (Sum.inl a)
  | ExtFormula.atom (Sum.inr ()) => ExtFormula.bot
  | ExtFormula.bot => ExtFormula.bot
  | ExtFormula.imp φ ψ => ExtFormula.imp (substFormula φ) (substFormula ψ)
  | ExtFormula.box φ => ExtFormula.box (substFormula φ)
  | ExtFormula.untl φ ψ => ExtFormula.untl (substFormula φ) (substFormula ψ)
  | ExtFormula.snce φ ψ => ExtFormula.snce (substFormula φ) (substFormula ψ)

/-!
## Structural Lemmas
-/

@[simp]
theorem substFormula_bot : substFormula (Atom := Atom) ExtFormula.bot = ExtFormula.bot := rfl

@[simp]
theorem substFormula_atom_inl (a : Atom) :
    substFormula (ExtFormula.atom (Sum.inl a)) = ExtFormula.atom (Sum.inl a) := rfl

@[simp]
theorem substFormula_atom_fresh :
    substFormula (Atom := Atom) (ExtFormula.atom freshAtom) = ExtFormula.bot := rfl

@[simp]
theorem substFormula_imp (φ ψ : ExtFormula Atom) :
    substFormula (φ.imp ψ) = (substFormula φ).imp (substFormula ψ) := rfl

@[simp]
theorem substFormula_box (φ : ExtFormula Atom) :
    substFormula (φ.box) = (substFormula φ).box := rfl

@[simp]
theorem substFormula_untl (φ ψ : ExtFormula Atom) :
    substFormula (ExtFormula.untl φ ψ) =
      ExtFormula.untl (substFormula φ) (substFormula ψ) := rfl

@[simp]
theorem substFormula_snce (φ ψ : ExtFormula Atom) :
    substFormula (ExtFormula.snce φ ψ) =
      ExtFormula.snce (substFormula φ) (substFormula ψ) := rfl

/-!
## Derived Operator Preservation
-/

@[simp]
theorem substFormula_neg (φ : ExtFormula Atom) :
    substFormula φ.neg = (substFormula φ).neg := rfl

@[simp]
theorem substFormula_and (φ ψ : ExtFormula Atom) :
    substFormula (φ.and ψ) = (substFormula φ).and (substFormula ψ) := rfl

@[simp]
theorem substFormula_or (φ ψ : ExtFormula Atom) :
    substFormula (φ.or ψ) = (substFormula φ).or (substFormula ψ) := rfl

@[simp]
theorem substFormula_diamond (φ : ExtFormula Atom) :
    substFormula φ.diamond = (substFormula φ).diamond := rfl

@[simp]
theorem substFormula_top : substFormula (Atom := Atom) ExtFormula.top = ExtFormula.top := rfl

@[simp]
theorem substFormula_someFuture (φ : ExtFormula Atom) :
    substFormula φ.someFuture = (substFormula φ).someFuture := rfl

@[simp]
theorem substFormula_somePast (φ : ExtFormula Atom) :
    substFormula φ.somePast = (substFormula φ).somePast := rfl

@[simp]
theorem substFormula_allFuture (φ : ExtFormula Atom) :
    substFormula φ.allFuture = (substFormula φ).allFuture := rfl

@[simp]
theorem substFormula_allPast (φ : ExtFormula Atom) :
    substFormula φ.allPast = (substFormula φ).allPast := rfl

@[simp]
theorem substFormula_always (φ : ExtFormula Atom) :
    substFormula φ.always = (substFormula φ).always := rfl

/-!
## Swap Temporal Preservation
-/

theorem substFormula_swapTemporal (φ : ExtFormula Atom) :
    substFormula φ.swapTemporal = (substFormula φ).swapTemporal := by
  induction φ with
  | atom a =>
    cases a with
    | inl s => simp [ExtFormula.swapTemporal, substFormula]
    | inr u => cases u; simp [ExtFormula.swapTemporal, substFormula]
  | bot => rfl
  | imp _ _ ih1 ih2 =>
    simp [ExtFormula.swapTemporal, substFormula, ih1, ih2]
  | box _ ih =>
    simp [ExtFormula.swapTemporal, substFormula, ih]
  | untl _ _ ih1 ih2 =>
    simp [ExtFormula.swapTemporal, substFormula, ih1, ih2]
  | snce _ _ ih1 ih2 =>
    simp [ExtFormula.swapTemporal, substFormula, ih1, ih2]

/-!
## Key Preservation Lemma: q-free formulas are fixed points
-/

section DecEq

variable [DecidableEq Atom]

/-- If the fresh atom is not in a formula's atoms, substitution is the identity. -/
theorem substFormula_preserves_qfree (φ : ExtFormula Atom) (h : freshAtom ∉ φ.atoms) :
    substFormula φ = φ := by
  induction φ with
  | atom a =>
    cases a with
    | inl s => rfl
    | inr u =>
      cases u
      simp [ExtFormula.atoms, freshAtom] at h
  | bot => rfl
  | imp a b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp [substFormula, iha h.1, ihb h.2]
  | box a ih =>
    simp [ExtFormula.atoms] at h
    simp [substFormula, ih h]
  | untl a b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp [substFormula, iha h.1, ihb h.2]
  | snce a b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp [substFormula, iha h.1, ihb h.2]

/-- Embedded formulas are unchanged by substitution. -/
theorem substFormula_of_embedded (φ : Formula Atom) :
    substFormula (embedFormula φ) = embedFormula φ :=
  substFormula_preserves_qfree _ (fresh_not_in_embedFormula_atoms φ)

/-!
## Idempotence
-/

/-- After substitution, the fresh atom does not appear. -/
theorem freshAtom_not_in_substFormula_atoms (φ : ExtFormula Atom) :
    freshAtom ∉ (substFormula φ).atoms := by
  induction φ with
  | atom a =>
    cases a with
    | inl s => simp [substFormula, ExtFormula.atoms, freshAtom]
    | inr u => cases u; simp [substFormula, ExtFormula.atoms]
  | bot => simp [substFormula, ExtFormula.atoms]
  | imp a b iha ihb =>
    simp [substFormula, ExtFormula.atoms, Finset.mem_union]
    exact ⟨iha, ihb⟩
  | box a ih => simp [substFormula, ExtFormula.atoms]; exact ih
  | untl a b iha ihb =>
    simp [substFormula, ExtFormula.atoms, Finset.mem_union]
    exact ⟨iha, ihb⟩
  | snce a b iha ihb =>
    simp [substFormula, ExtFormula.atoms, Finset.mem_union]
    exact ⟨iha, ihb⟩

/-- Substitution is idempotent: applying it twice gives the same result. -/
theorem substFormula_idempotent (φ : ExtFormula Atom) :
    substFormula (substFormula φ) = substFormula φ :=
  substFormula_preserves_qfree _ (freshAtom_not_in_substFormula_atoms φ)

end DecEq

/-!
## Axiom Substitution Closure

Every axiom schema is closed under uniform substitution: if `ExtAxiom φ` then
`ExtAxiom (substFormula φ)`. This is because each axiom has the form
`A(φ₁, ..., φₙ)` and substitution distributes over all constructors, so
`substFormula (A(φ₁, ..., φₙ)) = A(substFormula φ₁, ..., substFormula φₙ)`.
-/

/-- All axiom schemas are closed under the substitution sigma[q -> bot]. -/
def substAxiom {φ : ExtFormula Atom} (h : ExtAxiom φ) : ExtAxiom (substFormula φ) := by
  cases h with
  | imp_k a b c => exact .imp_k (substFormula a) (substFormula b) (substFormula c)
  | imp_s a b => exact .imp_s (substFormula a) (substFormula b)
  | efq a => exact .efq (substFormula a)
  | peirce a b => exact .peirce (substFormula a) (substFormula b)
  | modal_t a => exact .modal_t (substFormula a)
  | modal_4 a => exact .modal_4 (substFormula a)
  | modal_b a => exact .modal_b (substFormula a)
  | modal_5_collapse a => exact .modal_5_collapse (substFormula a)
  | modal_k_dist a b => exact .modal_k_dist (substFormula a) (substFormula b)
  | serial_future => exact .serial_future
  | serial_past => exact .serial_past
  | left_mono_until_G a b c =>
    exact .left_mono_until_G (substFormula a) (substFormula b) (substFormula c)
  | left_mono_since_H a b c =>
    exact .left_mono_since_H (substFormula a) (substFormula b) (substFormula c)
  | right_mono_until a b c =>
    exact .right_mono_until (substFormula a) (substFormula b) (substFormula c)
  | right_mono_since a b c =>
    exact .right_mono_since (substFormula a) (substFormula b) (substFormula c)
  | connect_future a => exact .connect_future (substFormula a)
  | connect_past a => exact .connect_past (substFormula a)
  | enrichment_until a b c =>
    exact .enrichment_until (substFormula a) (substFormula b) (substFormula c)
  | enrichment_since a b c =>
    exact .enrichment_since (substFormula a) (substFormula b) (substFormula c)
  | self_accum_until a b => exact .self_accum_until (substFormula a) (substFormula b)
  | self_accum_since a b => exact .self_accum_since (substFormula a) (substFormula b)
  | absorb_until a b => exact .absorb_until (substFormula a) (substFormula b)
  | absorb_since a b => exact .absorb_since (substFormula a) (substFormula b)
  | linear_until a b c d =>
    exact .linear_until (substFormula a) (substFormula b) (substFormula c) (substFormula d)
  | linear_since a b c d =>
    exact .linear_since (substFormula a) (substFormula b) (substFormula c) (substFormula d)
  | until_F a b => exact .until_F (substFormula a) (substFormula b)
  | since_P a b => exact .since_P (substFormula a) (substFormula b)
  | temp_linearity a b =>
    exact .temp_linearity (substFormula a) (substFormula b)
  | temp_linearity_past a b =>
    exact .temp_linearity_past (substFormula a) (substFormula b)
  | F_until_equiv a => exact .F_until_equiv (substFormula a)
  | P_since_equiv a => exact .P_since_equiv (substFormula a)
  | modal_future a => exact .modal_future (substFormula a)
  | discrete_symm_fwd => exact .discrete_symm_fwd
  | discrete_symm_bwd => exact .discrete_symm_bwd
  | discrete_propagate_fwd => exact .discrete_propagate_fwd
  | discrete_propagate_bwd => exact .discrete_propagate_bwd
  | discrete_box_necessity => exact .discrete_box_necessity
  | prior_UZ a => exact .prior_UZ (substFormula a)
  | prior_SZ a => exact .prior_SZ (substFormula a)
  | z1 a => exact .z1 (substFormula a)
  | density a => exact .density (substFormula a)
  | dense_indicator => exact .dense_indicator

/-- Substitution preserves `minFrameClass`. -/
theorem substAxiom_preserves_minFrameClass {φ : ExtFormula Atom} (h : ExtAxiom φ) :
    (substAxiom h).minFrameClass = h.minFrameClass := by
  cases h <;> rfl

/-!
## List Substitution
-/

/-- Substitution distributes over list map. -/
theorem substFormula_map_embedded [DecidableEq Atom] (L : List (Formula Atom)) :
    (L.map embedFormula).map substFormula = L.map embedFormula := by
  simp [List.map_map, Function.comp, substFormula_of_embedded]

end Cslib.Logic.Bimodal.Metalogic.ConservativeExtension
