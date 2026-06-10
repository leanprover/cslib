/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
import Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.Substitution
import Mathlib.Data.Fintype.EquivFin

/-!
# Lifting Infrastructure for Conservative Extension

This module provides the lifting infrastructure for projecting F+ derivations back
to F derivations via the substitution sigma[q -> bot].

## Main Results

- `substDerivation`: Substitution sigma[q -> bot] preserves derivations in Ext
- `unembedFormula`: Project q-free ExtFormula back to Formula
- `unembed_embed`: unembedFormula is left-inverse of embedFormula
- `embed_unembed_qfree`: embedFormula is left-inverse of unembedFormula for q-free formulas
- `substFreshWith`: Parameterized substitution replacing freshAtom with atom (Sum.inl a)
- `substAxiomFresh`: Axiom closure under parameterized substitution
- `lift_derivation_qfree`: Main conservative extension theorem

## Key Insight

The IRR case with `p = freshAtom` in substDerivation is handled by the observation
that `substFormula phi = phi` when `freshAtom not-in phi.atoms`, so the original IRR
step can be preserved without modification.

## References

- Goldblatt 1992, Logics of Time and Computation
-/

set_option linter.style.emptyLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace Cslib.Logic.Bimodal.Metalogic.ConservativeExtension

open Cslib.Logic.Bimodal

variable {Atom : Type u}

/-!
## Unembedding: Inverse of embedFormula for q-free formulas
-/

/-- Partial inverse of embedFormula. Maps `Sum.inl a` atoms back to `Atom` atoms.
For q-free formulas (after substitution), this is a true inverse. -/
def unembedFormula : ExtFormula Atom → Formula Atom
  | ExtFormula.atom (Sum.inl a) => Formula.atom a
  | ExtFormula.atom (Sum.inr ()) => Formula.bot  -- unreachable for q-free formulas
  | ExtFormula.bot => Formula.bot
  | ExtFormula.imp φ ψ => Formula.imp (unembedFormula φ) (unembedFormula ψ)
  | ExtFormula.box φ => Formula.box (unembedFormula φ)
  | ExtFormula.untl φ ψ => Formula.untl (unembedFormula φ) (unembedFormula ψ)
  | ExtFormula.snce φ ψ => Formula.snce (unembedFormula φ) (unembedFormula ψ)

/-- unembedFormula is left-inverse of embedFormula. -/
theorem unembed_embed (φ : Formula Atom) : unembedFormula (embedFormula φ) = φ := by
  induction φ with
  | atom s => rfl
  | bot => rfl
  | imp a b iha ihb => simp [embedFormula, unembedFormula, iha, ihb]
  | box a ih => simp [embedFormula, unembedFormula, ih]
  | untl a b iha ihb => simp [embedFormula, unembedFormula, iha, ihb]
  | snce a b iha ihb => simp [embedFormula, unembedFormula, iha, ihb]

section DecEq

variable [DecidableEq Atom]

/-- embedFormula is left-inverse of unembedFormula for q-free formulas. -/
theorem embed_unembed_qfree (φ : ExtFormula Atom) (h : freshAtom ∉ φ.atoms) :
    embedFormula (unembedFormula φ) = φ := by
  induction φ with
  | atom a =>
    cases a with
    | inl s => rfl
    | inr u => cases u; simp [ExtFormula.atoms, freshAtom] at h
  | bot => rfl
  | imp a b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp [unembedFormula, embedFormula, iha h.1, ihb h.2]
  | box a ih =>
    simp [ExtFormula.atoms] at h; simp [unembedFormula, embedFormula, ih h]
  | untl a b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp [unembedFormula, embedFormula, iha h.1, ihb h.2]
  | snce a b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp [unembedFormula, embedFormula, iha h.1, ihb h.2]

end DecEq

/-- List unembedding inverts list embedding. -/
theorem unembed_embed_list (L : List (Formula Atom)) :
    (L.map embedFormula).map unembedFormula = L := by
  induction L with
  | nil => rfl
  | cons hd tl ih => simp [List.map, unembed_embed hd, ih]

/-!
## Helper Lemmas for substDerivation
-/

section DecEq

variable [DecidableEq Atom]

/-- Sum.inl atoms are preserved by substitution. -/
private theorem inl_not_in_substFormula_atoms {a : Atom} {phi : ExtFormula Atom}
    (h : Sum.inl a ∉ phi.atoms) : Sum.inl a ∉ (substFormula phi).atoms := by
  induction phi with
  | atom x =>
    cases x with
    | inl t => simp [substFormula, ExtFormula.atoms] at h ⊢; exact h
    | inr u => cases u; simp [substFormula, ExtFormula.atoms]
  | bot => simp [substFormula, ExtFormula.atoms]
  | imp a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp only [substFormula, ExtFormula.atoms, Finset.mem_union, not_or]
    exact ⟨iha h.1, ihb h.2⟩
  | box a' ih =>
    simp [ExtFormula.atoms] at h; simp [substFormula, ExtFormula.atoms, ih h]
  | untl a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp only [substFormula, ExtFormula.atoms, Finset.mem_union, not_or]
    exact ⟨iha h.1, ihb h.2⟩
  | snce a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp only [substFormula, ExtFormula.atoms, Finset.mem_union, not_or]
    exact ⟨iha h.1, ihb h.2⟩

end DecEq

/-- Subset preserved under substFormula map. -/
private theorem map_substFormula_subset {Gamma Delta : ExtContext Atom}
    (h : Gamma ⊆ Delta) : Gamma.map substFormula ⊆ Delta.map substFormula := by
  intro x hx
  rw [List.mem_map] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, h ha, rfl⟩

/-!
## substDerivation: Substitution sigma[q -> bot] Preserves Derivations

Apply sigma[q -> bot] to an entire derivation tree. The IRR case with
p = freshAtom is handled by observing that substFormula phi = phi when
freshAtom not-in phi.atoms, so the IRR step is preserved unchanged.
-/

/-- Apply substitution sigma[q -> bot] to a derivation tree. -/
noncomputable def substDerivation {fc : FrameClass} :
    {Gamma : ExtContext Atom} → {phi : ExtFormula Atom} →
    ExtDerivationTree fc Gamma phi →
    ExtDerivationTree fc (Gamma.map substFormula) (substFormula phi)
  | _, _, ExtDerivationTree.axiom _Gamma _phi h h_fc =>
    ExtDerivationTree.axiom _ _ (substAxiom h) (substAxiom_preserves_minFrameClass h ▸ h_fc)
  | _, _, ExtDerivationTree.assumption _Gamma _phi h =>
    ExtDerivationTree.assumption _ _ (List.mem_map_of_mem (f := substFormula) h)
  | _, _, ExtDerivationTree.modus_ponens _Gamma a b d1 d2 =>
    ExtDerivationTree.modus_ponens _ (substFormula a) (substFormula b)
      (substDerivation d1) (substDerivation d2)
  | _, _, ExtDerivationTree.necessitation _phi d =>
    ExtDerivationTree.necessitation _ (substDerivation d)
  | _, _, ExtDerivationTree.temporal_necessitation _phi d =>
    ExtDerivationTree.temporal_necessitation _ (substDerivation d)
  | _, _, ExtDerivationTree.temporal_duality phi d =>
    substFormula_swapTemporal phi ▸
      ExtDerivationTree.temporal_duality _ (substDerivation d)
  | _, _, ExtDerivationTree.weakening _Gamma _Delta _phi d h =>
    ExtDerivationTree.weakening _ _ _ (substDerivation d) (map_substFormula_subset h)

/-!
## Parameterized Substitution: Replace freshAtom with atom (Sum.inl a)
-/

/-- Replace freshAtom with atom (Sum.inl a) in an ExtFormula. -/
def substFreshWith (a : Atom) : ExtFormula Atom → ExtFormula Atom
  | ExtFormula.atom (Sum.inl t) => ExtFormula.atom (Sum.inl t)
  | ExtFormula.atom (Sum.inr ()) => ExtFormula.atom (Sum.inl a)
  | ExtFormula.bot => ExtFormula.bot
  | ExtFormula.imp φ ψ => ExtFormula.imp (substFreshWith a φ) (substFreshWith a ψ)
  | ExtFormula.box φ => ExtFormula.box (substFreshWith a φ)
  | ExtFormula.untl φ ψ => ExtFormula.untl (substFreshWith a φ) (substFreshWith a ψ)
  | ExtFormula.snce φ ψ => ExtFormula.snce (substFreshWith a φ) (substFreshWith a ψ)

theorem substFreshWith_swapTemporal (a : Atom) (φ : ExtFormula Atom) :
    substFreshWith a φ.swapTemporal = (substFreshWith a φ).swapTemporal := by
  induction φ with
  | atom x =>
    cases x with
    | inl t => simp [ExtFormula.swapTemporal, substFreshWith]
    | inr u => cases u; simp [ExtFormula.swapTemporal, substFreshWith]
  | bot => rfl
  | imp _ _ ih1 ih2 => simp [ExtFormula.swapTemporal, substFreshWith, ih1, ih2]
  | box _ ih => simp [ExtFormula.swapTemporal, substFreshWith, ih]
  | untl _ _ ih1 ih2 => simp [ExtFormula.swapTemporal, substFreshWith, ih1, ih2]
  | snce _ _ ih1 ih2 => simp [ExtFormula.swapTemporal, substFreshWith, ih1, ih2]

section DecEq

variable [DecidableEq Atom]

theorem substFreshWith_preserves_qfree (a : Atom) (φ : ExtFormula Atom)
    (h : freshAtom ∉ φ.atoms) :
    substFreshWith a φ = φ := by
  induction φ with
  | atom x =>
    cases x with
    | inl t => rfl
    | inr u => cases u; simp [ExtFormula.atoms, freshAtom] at h
  | bot => rfl
  | imp a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp [substFreshWith, iha h.1, ihb h.2]
  | box a' ih => simp [ExtFormula.atoms] at h; simp [substFreshWith, ih h]
  | untl a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp [substFreshWith, iha h.1, ihb h.2]
  | snce a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp [substFreshWith, iha h.1, ihb h.2]

theorem substFreshWith_of_embedded (a : Atom) (φ : Formula Atom) :
    substFreshWith a (embedFormula φ) = embedFormula φ :=
  substFreshWith_preserves_qfree a _ (fresh_not_in_embedFormula_atoms φ)

end DecEq

/-- Axioms are closed under replacing freshAtom with atom (Sum.inl a). -/
def substAxiomFresh (a : Atom) {φ : ExtFormula Atom} (h : ExtAxiom φ) :
    ExtAxiom (substFreshWith a φ) := by
  cases h with
  | imp_k x y z => exact .imp_k _ _ _
  | imp_s x y => exact .imp_s _ _
  | efq x => exact .efq _
  | peirce x y => exact .peirce _ _
  | modal_t x => exact .modal_t _
  | modal_4 x => exact .modal_4 _
  | modal_b x => exact .modal_b _
  | modal_5_collapse x => exact .modal_5_collapse _
  | modal_k_dist x y => exact .modal_k_dist _ _
  | serial_future => exact .serial_future
  | serial_past => exact .serial_past
  | left_mono_until_G x y z => exact .left_mono_until_G _ _ _
  | left_mono_since_H x y z => exact .left_mono_since_H _ _ _
  | right_mono_until x y z => exact .right_mono_until _ _ _
  | right_mono_since x y z => exact .right_mono_since _ _ _
  | connect_future x => exact .connect_future _
  | connect_past x => exact .connect_past _
  | enrichment_until x y z => exact .enrichment_until _ _ _
  | enrichment_since x y z => exact .enrichment_since _ _ _
  | self_accum_until x y => exact .self_accum_until _ _
  | self_accum_since x y => exact .self_accum_since _ _
  | absorb_until x y => exact .absorb_until _ _
  | absorb_since x y => exact .absorb_since _ _
  | linear_until x y z w => exact .linear_until _ _ _ _
  | linear_since x y z w => exact .linear_since _ _ _ _
  | until_F x y => exact .until_F _ _
  | since_P x y => exact .since_P _ _
  | temp_linearity x y => exact .temp_linearity _ _
  | temp_linearity_past x y => exact .temp_linearity_past _ _
  | F_until_equiv x => exact .F_until_equiv _
  | P_since_equiv x => exact .P_since_equiv _
  | modal_future x => exact .modal_future _
  | discrete_symm_fwd => exact .discrete_symm_fwd
  | discrete_symm_bwd => exact .discrete_symm_bwd
  | discrete_propagate_fwd => exact .discrete_propagate_fwd
  | discrete_propagate_bwd => exact .discrete_propagate_bwd
  | discrete_box_necessity => exact .discrete_box_necessity
  | prior_UZ x => exact .prior_UZ _
  | prior_SZ x => exact .prior_SZ _
  | z1 x => exact .z1 _
  | density x => exact .density _
  | dense_indicator => exact .dense_indicator

/-- substFreshWith preserves minFrameClass. -/
private theorem substAxiomFresh_preserves_minFrameClass (a : Atom) {φ : ExtFormula Atom}
    (h : ExtAxiom φ) : (substAxiomFresh a h).minFrameClass = h.minFrameClass := by
  cases h <;> rfl

/-!
## Unembedding Axioms: ExtAxiom to Axiom
-/

/-- Convert an ExtAxiom to a base Axiom under unembedFormula. -/
def unembedAxiom {φ : ExtFormula Atom} (h : ExtAxiom φ) : Axiom (unembedFormula φ) := by
  cases h with
  | imp_k a b c => exact .imp_k _ _ _
  | imp_s a b => exact .imp_s _ _
  | efq a => exact .efq _
  | peirce a b => exact .peirce _ _
  | modal_t a => exact .modal_t _
  | modal_4 a => exact .modal_4 _
  | modal_b a => exact .modal_b _
  | modal_5_collapse a => exact .modal_5_collapse _
  | modal_k_dist a b => exact .modal_k_dist _ _
  | serial_future => exact .serial_future
  | serial_past => exact .serial_past
  | left_mono_until_G a b c => exact .left_mono_until_G _ _ _
  | left_mono_since_H a b c => exact .left_mono_since_H _ _ _
  | right_mono_until a b c => exact .right_mono_until _ _ _
  | right_mono_since a b c => exact .right_mono_since _ _ _
  | connect_future a => exact .connect_future _
  | connect_past a => exact .connect_past _
  | enrichment_until a b c => exact .enrichment_until _ _ _
  | enrichment_since a b c => exact .enrichment_since _ _ _
  | self_accum_until a b => exact .self_accum_until _ _
  | self_accum_since a b => exact .self_accum_since _ _
  | absorb_until a b => exact .absorb_until _ _
  | absorb_since a b => exact .absorb_since _ _
  | linear_until a b c d => exact .linear_until _ _ _ _
  | linear_since a b c d => exact .linear_since _ _ _ _
  | until_F a b => exact .until_F _ _
  | since_P a b => exact .since_P _ _
  | temp_linearity a b => exact .temp_linearity _ _
  | temp_linearity_past a b => exact .temp_linearity_past _ _
  | F_until_equiv a => exact .F_until_equiv _
  | P_since_equiv a => exact .P_since_equiv _
  | modal_future a => exact .modal_future _
  | discrete_symm_fwd => exact .discrete_symm_fwd
  | discrete_symm_bwd => exact .discrete_symm_bwd
  | discrete_propagate_fwd => exact .discrete_propagate_fwd
  | discrete_propagate_bwd => exact .discrete_propagate_bwd
  | discrete_box_necessity => exact .discrete_box_necessity
  | prior_UZ a => exact .prior_UZ _
  | prior_SZ a => exact .prior_SZ _
  | z1 a => exact .z1 _
  | density a => exact .density _
  | dense_indicator => exact .dense_indicator

/-- unembedFormula commutes with swapTemporal. -/
theorem unembed_swapTemporal (φ : ExtFormula Atom) :
    unembedFormula φ.swapTemporal = (unembedFormula φ).swapTemporal := by
  induction φ with
  | atom a => cases a with | inl s => rfl | inr u => cases u; rfl
  | bot => rfl
  | imp _ _ ih1 ih2 =>
    simp [ExtFormula.swapTemporal, Formula.swapTemporal, unembedFormula, ih1, ih2]
  | box _ ih =>
    simp [ExtFormula.swapTemporal, Formula.swapTemporal, unembedFormula, ih]
  | untl _ _ ih1 ih2 =>
    simp [ExtFormula.swapTemporal, Formula.swapTemporal, unembedFormula, ih1, ih2]
  | snce _ _ ih1 ih2 =>
    simp [ExtFormula.swapTemporal, Formula.swapTemporal, unembedFormula, ih1, ih2]

/-- Membership preserved under unembedFormula map. -/
private theorem mem_map_unembedFormula {Gamma : ExtContext Atom} {phi : ExtFormula Atom}
    (h : phi ∈ Gamma) : unembedFormula phi ∈ Gamma.map unembedFormula :=
  List.mem_map_of_mem (f := unembedFormula) h

/-- Subset preserved under unembedFormula map. -/
private theorem map_unembed_subset {Gamma Delta : ExtContext Atom}
    (h : Gamma ⊆ Delta) : Gamma.map unembedFormula ⊆ Delta.map unembedFormula := by
  intro x hx
  rw [List.mem_map] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, h ha, rfl⟩

/-!
## Atom Relationship Lemmas for Unembedding
-/

section DecEq

variable [DecidableEq Atom]

/-- If Sum.inl a ∉ φ.atoms then a ∉ (unembedFormula φ).atoms.
This transfers the freshness condition from Ext to base. -/
theorem inl_not_in_atoms_implies_unembed {a : Atom} {φ : ExtFormula Atom}
    (h : Sum.inl a ∉ φ.atoms) : a ∉ (unembedFormula φ).atoms := by
  induction φ with
  | atom x =>
    cases x with
    | inl t =>
      simp [ExtFormula.atoms] at h
      simp [unembedFormula, Formula.atoms, h]
    | inr u => cases u; simp [unembedFormula, Formula.atoms]
  | bot => simp [unembedFormula, Formula.atoms]
  | imp a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp only [unembedFormula, Formula.atoms, Finset.mem_union, not_or]
    exact ⟨iha h.1, ihb h.2⟩
  | box a' ih =>
    simp [ExtFormula.atoms] at h; simp [unembedFormula, Formula.atoms, ih h]
  | untl a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp only [unembedFormula, Formula.atoms, Finset.mem_union, not_or]
    exact ⟨iha h.1, ihb h.2⟩
  | snce a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp only [unembedFormula, Formula.atoms, Finset.mem_union, not_or]
    exact ⟨iha h.1, ihb h.2⟩

/-!
## Lifting Theorem: F+ to F via Substitution

The lifting theorem transfers F+ derivations of embedded F-formulas back to F.
This is the key conservative extension result.

### Strategy

1. Collect all Sum.inl atoms from the derivation tree
2. Choose a fresh atom `a` not among them
3. Apply `substFreshWith a` to replace Sum.inr () with Sum.inl a throughout
4. Unembed the result (now using only Sum.inl atoms) to a DerivationTree
-/

/-- Collect all Sum.inl atoms from an ExtFormula. -/
private def collectInl : ExtFormula Atom → Finset Atom
  | ExtFormula.atom (Sum.inl a) => {a}
  | ExtFormula.atom (Sum.inr ()) => ∅
  | ExtFormula.bot => ∅
  | ExtFormula.imp φ ψ => collectInl φ ∪ collectInl ψ
  | ExtFormula.box φ => collectInl φ
  | ExtFormula.untl φ ψ => collectInl φ ∪ collectInl ψ
  | ExtFormula.snce φ ψ => collectInl φ ∪ collectInl ψ

private theorem inl_mem_implies_collectInl {a : Atom} {φ : ExtFormula Atom}
    (h : Sum.inl a ∈ φ.atoms) : a ∈ collectInl φ := by
  induction φ with
  | atom x => cases x with
    | inl t => simp [ExtFormula.atoms] at h; simp [collectInl, h]
    | inr u => cases u; simp [ExtFormula.atoms] at h
  | bot => simp [ExtFormula.atoms] at h
  | imp a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union] at h
    simp only [collectInl, Finset.mem_union]
    cases h with | inl h => left; exact iha h | inr h => right; exact ihb h
  | box a' ih => exact ih h
  | untl a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union] at h
    simp only [collectInl, Finset.mem_union]
    cases h with | inl h => left; exact iha h | inr h => right; exact ihb h
  | snce a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union] at h
    simp only [collectInl, Finset.mem_union]
    cases h with | inl h => left; exact iha h | inr h => right; exact ihb h

/-- Collect all Sum.inl atoms from all formulas in an ExtDerivationTree. -/
private noncomputable def collectDerivInl {fc : FrameClass} :
    {Γ : ExtContext Atom} → {φ : ExtFormula Atom} →
    ExtDerivationTree fc Γ φ → Finset Atom
  | _, _, ExtDerivationTree.axiom _ φ _ _ => collectInl φ
  | _, _, ExtDerivationTree.assumption _ φ _ => collectInl φ
  | _, _, ExtDerivationTree.modus_ponens _ a b d1 d2 =>
    collectInl a ∪ collectInl b ∪ collectDerivInl d1 ∪ collectDerivInl d2
  | _, _, ExtDerivationTree.necessitation φ d => collectInl φ ∪ collectDerivInl d
  | _, _, ExtDerivationTree.temporal_necessitation φ d =>
    collectInl φ ∪ collectDerivInl d
  | _, _, ExtDerivationTree.temporal_duality φ d => collectInl φ ∪ collectDerivInl d
  | _, _, ExtDerivationTree.weakening _ Δ φ d _ =>
    collectInl φ ∪ collectDerivInl d ∪ Δ.foldl (fun acc ψ => acc ∪ collectInl ψ) ∅

/-- Subderivation atoms are included in parent atoms (monotonicity lemmas). -/
private theorem collectDerivInl_sub_modus_ponens_left {fc : FrameClass}
    {Γ : ExtContext Atom} {a b : ExtFormula Atom}
    {d1 : ExtDerivationTree fc Γ (a.imp b)}
    {d2 : ExtDerivationTree fc Γ a} :
    collectDerivInl d1 ⊆
      collectDerivInl (ExtDerivationTree.modus_ponens Γ a b d1 d2) := by
  intro x hx; simp only [collectDerivInl, Finset.mem_union]; tauto

private theorem collectDerivInl_sub_modus_ponens_right {fc : FrameClass}
    {Γ : ExtContext Atom} {a b : ExtFormula Atom}
    {d1 : ExtDerivationTree fc Γ (a.imp b)}
    {d2 : ExtDerivationTree fc Γ a} :
    collectDerivInl d2 ⊆
      collectDerivInl (ExtDerivationTree.modus_ponens Γ a b d1 d2) := by
  intro x hx; simp only [collectDerivInl, Finset.mem_union]; tauto

private theorem collectDerivInl_sub_nec {fc : FrameClass}
    {φ : ExtFormula Atom} {d : ExtDerivationTree fc [] φ} :
    collectDerivInl d ⊆
      collectDerivInl (ExtDerivationTree.necessitation φ d) := by
  intro x hx; simp only [collectDerivInl, Finset.mem_union]; tauto

private theorem collectDerivInl_sub_tnec {fc : FrameClass}
    {φ : ExtFormula Atom} {d : ExtDerivationTree fc [] φ} :
    collectDerivInl d ⊆
      collectDerivInl (ExtDerivationTree.temporal_necessitation φ d) := by
  intro x hx; simp only [collectDerivInl, Finset.mem_union]; tauto

private theorem collectDerivInl_sub_tdual {fc : FrameClass}
    {φ : ExtFormula Atom} {d : ExtDerivationTree fc [] φ} :
    collectDerivInl d ⊆
      collectDerivInl (ExtDerivationTree.temporal_duality φ d) := by
  intro x hx; simp only [collectDerivInl, Finset.mem_union]; tauto

private theorem collectDerivInl_sub_weak {fc : FrameClass}
    {Γ Δ : ExtContext Atom} {φ : ExtFormula Atom}
    {d : ExtDerivationTree fc Γ φ} {h : Γ ⊆ Δ} :
    collectDerivInl d ⊆
      collectDerivInl (ExtDerivationTree.weakening Γ Δ φ d h) := by
  intro x hx; simp only [collectDerivInl, Finset.mem_union]; tauto

/-- For any Finset of atoms, there exists an atom not in it.
Requires `[Infinite Atom]`. -/
private theorem exists_fresh_atom [Infinite Atom]
    (s : Finset Atom) : ∃ a : Atom, a ∉ s :=
  Infinite.exists_notMem_finset s

/-!
### substFreshWith preserves freshness

Key lemma: if `t ≠ a` and `Sum.inl t ∉ phi.atoms`,
then `Sum.inl t ∉ (substFreshWith a phi).atoms`.
-/

private theorem substFreshWith_preserves_irr_fresh {a t : Atom}
    {phi : ExtFormula Atom}
    (h : Sum.inl t ∉ phi.atoms) (h_ne : t ≠ a) :
    Sum.inl t ∉ (substFreshWith a phi).atoms := by
  induction phi with
  | atom x =>
    cases x with
    | inl u => simp [substFreshWith, ExtFormula.atoms] at h ⊢; exact h
    | inr u => cases u; simp [substFreshWith, ExtFormula.atoms]; exact h_ne
  | bot => simp [substFreshWith, ExtFormula.atoms]
  | imp a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp only [substFreshWith, ExtFormula.atoms, Finset.mem_union, not_or]
    exact ⟨iha h.1, ihb h.2⟩
  | box a' ih =>
    simp [ExtFormula.atoms] at h; simp [substFreshWith, ExtFormula.atoms, ih h]
  | untl a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp only [substFreshWith, ExtFormula.atoms, Finset.mem_union, not_or]
    exact ⟨iha h.1, ihb h.2⟩
  | snce a' b iha ihb =>
    simp only [ExtFormula.atoms, Finset.mem_union, not_or] at h
    simp only [substFreshWith, ExtFormula.atoms, Finset.mem_union, not_or]
    exact ⟨iha h.1, ihb h.2⟩

/-- Subset preserved under substFreshWith map. -/
private theorem map_substFreshWith_subset (a : Atom) {Gamma Delta : ExtContext Atom}
    (h : Gamma ⊆ Delta) :
    Gamma.map (substFreshWith a) ⊆ Delta.map (substFreshWith a) := by
  intro x hx; rw [List.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx; exact ⟨y, h hy, rfl⟩

/-!
### Combined Lifting: substFreshWith a + unembedFormula

We define a single recursive function that applies substFreshWith a to eliminate
Sum.inr () atoms, then unembeds to the base language. The parameter a must be
fresh for the entire derivation tree (not appearing in collectDerivInl).
-/

/-- The combined formula transformation: substFreshWith then unembed. -/
private def liftFormula (a : Atom) (φ : ExtFormula Atom) : Formula Atom :=
  unembedFormula (substFreshWith a φ)

/-- liftFormula preserves embedFormula (embedded formulas are q-free). -/
private theorem liftFormula_embed (a : Atom) (φ : Formula Atom) :
    liftFormula a (embedFormula φ) = φ := by
  simp [liftFormula, substFreshWith_of_embedded, unembed_embed]

/-- liftFormula distributes over imp. -/
private theorem liftFormula_imp (a : Atom) (x y : ExtFormula Atom) :
    liftFormula a (x.imp y) = (liftFormula a x).imp (liftFormula a y) := by
  simp [liftFormula, substFreshWith, unembedFormula]

/-- liftFormula distributes over swapTemporal. -/
private theorem liftFormula_swapTemporal (a : Atom) (φ : ExtFormula Atom) :
    liftFormula a φ.swapTemporal = (liftFormula a φ).swapTemporal := by
  simp [liftFormula, substFreshWith_swapTemporal, unembed_swapTemporal]

/-- Lift an ExtAxiom to a base Axiom via liftFormula. -/
private def liftAxiom (a : Atom) {φ : ExtFormula Atom} (h : ExtAxiom φ) :
    Axiom (liftFormula a φ) := by
  cases h with
  | imp_k x y z => exact .imp_k _ _ _
  | imp_s x y => exact .imp_s _ _
  | efq x => exact .efq _
  | peirce x y => exact .peirce _ _
  | modal_t x => exact .modal_t _
  | modal_4 x => exact .modal_4 _
  | modal_b x => exact .modal_b _
  | modal_5_collapse x => exact .modal_5_collapse _
  | modal_k_dist x y => exact .modal_k_dist _ _
  | serial_future => exact .serial_future
  | serial_past => exact .serial_past
  | left_mono_until_G x y z => exact .left_mono_until_G _ _ _
  | left_mono_since_H x y z => exact .left_mono_since_H _ _ _
  | right_mono_until x y z => exact .right_mono_until _ _ _
  | right_mono_since x y z => exact .right_mono_since _ _ _
  | connect_future x => exact .connect_future _
  | connect_past x => exact .connect_past _
  | enrichment_until x y z => exact .enrichment_until _ _ _
  | enrichment_since x y z => exact .enrichment_since _ _ _
  | self_accum_until x y => exact .self_accum_until _ _
  | self_accum_since x y => exact .self_accum_since _ _
  | absorb_until x y => exact .absorb_until _ _
  | absorb_since x y => exact .absorb_since _ _
  | linear_until x y z w => exact .linear_until _ _ _ _
  | linear_since x y z w => exact .linear_since _ _ _ _
  | until_F x y => exact .until_F _ _
  | since_P x y => exact .since_P _ _
  | temp_linearity x y => exact .temp_linearity _ _
  | temp_linearity_past x y => exact .temp_linearity_past _ _
  | F_until_equiv x => exact .F_until_equiv _
  | P_since_equiv x => exact .P_since_equiv _
  | modal_future x => exact .modal_future _
  | discrete_symm_fwd => exact .discrete_symm_fwd
  | discrete_symm_bwd => exact .discrete_symm_bwd
  | discrete_propagate_fwd => exact .discrete_propagate_fwd
  | discrete_propagate_bwd => exact .discrete_propagate_bwd
  | discrete_box_necessity => exact .discrete_box_necessity
  | prior_UZ x => exact .prior_UZ _
  | prior_SZ x => exact .prior_SZ _
  | z1 x => exact .z1 _
  | density x => exact .density _
  | dense_indicator => exact .dense_indicator

/-- liftAxiom preserves minFrameClass. -/
private theorem liftAxiom_preserves_minFrameClass (a : Atom) {φ : ExtFormula Atom}
    (h : ExtAxiom φ) : (liftAxiom a h).minFrameClass = h.minFrameClass := by
  cases h <;> rfl

/-- The combined lifting function: convert an ExtDerivationTree to a DerivationTree
by replacing Sum.inr () with Sum.inl a and unembedding.

Requires a to be fresh for the entire derivation (a ∉ collectDerivInl d). -/
private noncomputable def liftDerivationWith {fc : FrameClass} (a : Atom) :
    {Γ : ExtContext Atom} → {φ : ExtFormula Atom} →
    (d : ExtDerivationTree fc Γ φ) →
    (h_fresh : a ∉ collectDerivInl d) →
    DerivationTree fc (Γ.map (liftFormula a)) (liftFormula a φ)
  | _, _, ExtDerivationTree.axiom Γ φ h_ax h_fc, _ =>
    DerivationTree.axiom _ _ (liftAxiom a h_ax)
      (liftAxiom_preserves_minFrameClass a h_ax ▸ h_fc)
  | _, _, ExtDerivationTree.assumption Γ φ h_mem, _ =>
    DerivationTree.assumption _ _
      (List.mem_map_of_mem (f := liftFormula a) h_mem)
  | _, _, ExtDerivationTree.modus_ponens Γ x y d1 d2, h_fr => by
    have h_fr1 : a ∉ collectDerivInl d1 := by
      intro h; apply h_fr; exact collectDerivInl_sub_modus_ponens_left h
    have h_fr2 : a ∉ collectDerivInl d2 := by
      intro h; apply h_fr; exact collectDerivInl_sub_modus_ponens_right h
    exact DerivationTree.modus_ponens _ (liftFormula a x) (liftFormula a y)
      (liftDerivationWith a d1 h_fr1) (liftDerivationWith a d2 h_fr2)
  | _, _, ExtDerivationTree.necessitation φ d, h_fr => by
    have h_fr_d : a ∉ collectDerivInl d := by
      intro h; apply h_fr; exact collectDerivInl_sub_nec h
    exact DerivationTree.necessitation _ (liftDerivationWith a d h_fr_d)
  | _, _, ExtDerivationTree.temporal_necessitation φ d, h_fr => by
    have h_fr_d : a ∉ collectDerivInl d := by
      intro h; apply h_fr; exact collectDerivInl_sub_tnec h
    exact DerivationTree.temporal_necessitation _
      (liftDerivationWith a d h_fr_d)
  | _, _, ExtDerivationTree.temporal_duality φ d, h_fr => by
    have h_fr_d : a ∉ collectDerivInl d := by
      intro h; apply h_fr; exact collectDerivInl_sub_tdual h
    exact liftFormula_swapTemporal a φ ▸
      DerivationTree.temporal_duality _ (liftDerivationWith a d h_fr_d)
  | _, _, ExtDerivationTree.weakening Γ Δ φ d h_sub, h_fr => by
    have h_fr_d : a ∉ collectDerivInl d := by
      intro h; apply h_fr; exact collectDerivInl_sub_weak h
    have h_lift_sub : Γ.map (liftFormula a) ⊆ Δ.map (liftFormula a) := by
      intro x hx; rw [List.mem_map] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx; exact ⟨y, h_sub hy, rfl⟩
    exact DerivationTree.weakening _ _ _
      (liftDerivationWith a d h_fr_d) h_lift_sub

/-!
### Main Lifting Theorem

Projects F+ derivations of embedded formulas back to F derivations.
-/

/-- F+ is a conservative extension of F: if F+ derives `embedFormula phi` from
`L.map embedFormula`, then F derives `phi` from `L`.

This is the key result enabling the irreflexivity proof. The proof works by:
1. Collecting all inl atoms from the derivation tree
2. Choosing a fresh atom a not among them
3. Applying liftDerivationWith a to convert the ExtDerivationTree to a DerivationTree
4. Using liftFormula_embed to simplify the context and conclusion -/
theorem lift_derivation_qfree [Infinite Atom]
    {fc : FrameClass} (L : List (Formula Atom)) (phi : Formula Atom)
    (d : ExtDerivationTree fc (L.map embedFormula) (embedFormula phi)) :
    Nonempty (DerivationTree fc L phi) := by
  obtain ⟨a, ha⟩ := exists_fresh_atom (collectDerivInl d)
  have lifted := liftDerivationWith a d ha
  -- The context and conclusion simplify via liftFormula_embed
  have h_ctx : (L.map embedFormula).map (liftFormula a) = L := by
    rw [List.map_map]
    conv => lhs; arg 1; ext x; rw [Function.comp, liftFormula_embed]
    simp
  have h_concl : liftFormula a (embedFormula phi) = phi := liftFormula_embed a phi
  rw [h_ctx, h_concl] at lifted
  exact ⟨lifted⟩

end DecEq

end Cslib.Logic.Bimodal.Metalogic.ConservativeExtension
