/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Bundle.TemporalContent
public import Cslib.Logics.Bimodal.Metalogic.Bundle.WitnessSeed
public import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
public import Cslib.Logics.Bimodal.Syntax.Formula

/-!
# Canonical Frame for Bimodal Completeness

This module defines the canonical frame where:
- **Worlds** = all maximal consistent sets (MCSes)
- **Future relation** `ExistsTask M M'` iff `gContent M ⊆ M'`
- **Past relation** `ExistsTask_past M M'` iff `hContent M ⊆ M'`

## Key Results

- `canonical_forward_F`: F(psi) in M implies exists MCS W with psi in W and ExistsTask M W
- `canonical_backward_P`: P(psi) in M implies exists MCS W with psi in W and ExistsTask_past M W
- `canonical_forward_G`: G(phi) in M and ExistsTask M M' implies phi in M'
- `canonical_backward_H`: H(phi) in M and ExistsTask_past M M' implies phi in M'

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Bundle/CanonicalFrame.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Bundle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## Bridging Lemmas

The fc-parameterized `SetConsistent` (from MCSProperties) and `BimodalSetConsistent`
(from MaximalConsistent, delegating to the generic framework) are definitionally
equivalent at `FrameClass.Base`. We provide explicit bridges to use `bimodal_lindenbaum`
with `SetConsistent FrameClass.Base`.
-/

/--
Bridge: `SetConsistent FrameClass.Base` implies `BimodalSetConsistent`.

Both definitions unfold to `∀ L, (∀ phi ∈ L, phi ∈ Ω) → ¬Nonempty(DerivationTree Base L ⊥)`.
-/
theorem setConsistent_to_bimodalSetConsistent {Ω : Set (Formula Atom)}
    (h : SetConsistent FrameClass.Base Ω) : BimodalSetConsistent Ω := by
  intro L hL_sub
  exact h L hL_sub

/--
Bridge: `BimodalSetMaximalConsistent` implies `SetMaximalConsistent FrameClass.Base`.
-/
theorem bimodalSetMCS_to_setMCS {Ω : Set (Formula Atom)}
    (h : BimodalSetMaximalConsistent Ω) : SetMaximalConsistent FrameClass.Base Ω := by
  constructor
  · intro L hL_sub
    exact h.1 L hL_sub
  · intro phi h_not_mem h_cons
    exact h.2 phi h_not_mem (setConsistent_to_bimodalSetConsistent h_cons)

/--
fc-parameterized Lindenbaum's lemma at `FrameClass.Base`, bridging through the generic framework.
-/
theorem set_lindenbaum_base {Omega : Set (Formula Atom)} (hOmega : SetConsistent FrameClass.Base Omega) :
    ∃ M : Set (Formula Atom), Omega ⊆ M ∧ SetMaximalConsistent FrameClass.Base M := by
  have hBimodal := setConsistent_to_bimodalSetConsistent hOmega
  obtain ⟨M, hSM, hM_mcs⟩ := bimodal_lindenbaum Omega hBimodal
  exact ⟨M, hSM, bimodalSetMCS_to_setMCS hM_mcs⟩

/-!
## Canonical Relations
-/

/--
Canonical future relation: `M` sees `M'` in the future iff `gContent M ⊆ M'`.
-/
def ExistsTask (M M' : Set (Formula Atom)) : Prop :=
  gContent M ⊆ M'

/-- Unfolding lemma for ExistsTask. -/
@[simp] lemma ExistsTask_def {M M' : Set (Formula Atom)} : ExistsTask M M' = (gContent M ⊆ M') := rfl


/--
Canonical past relation: `M` sees `M'` in the past iff `hContent M ⊆ M'`.
-/
def ExistsTask_past (M M' : Set (Formula Atom)) : Prop :=
  hContent M ⊆ M'

/-- Unfolding lemma for ExistsTask_past. -/
@[simp] lemma ExistsTask_past_def {M M' : Set (Formula Atom)} : ExistsTask_past M M' = (hContent M ⊆ M') := rfl


/-!
## Forward G and Backward H (Trivial by Definition)
-/

/--
G-forward property: If `G phi ∈ M` and `ExistsTask M M'`, then `phi ∈ M'`.
-/
theorem canonical_forward_G (M M' : Set (Formula Atom))
    (h_R : ExistsTask M M') (phi : Formula Atom) (h_G : Formula.allFuture phi ∈ M) :
    phi ∈ M' := by
  exact h_R h_G

/--
H-backward property: If `H phi ∈ M` and `ExistsTask_past M M'`, then `phi ∈ M'`.
-/
theorem canonical_backward_H (M M' : Set (Formula Atom))
    (h_R : ExistsTask_past M M') (phi : Formula Atom) (h_H : Formula.allPast phi ∈ M) :
    phi ∈ M' := by
  exact h_R h_H

/-!
## Forward F (The Key Trivial Property)
-/

/--
F-forward property: If `F(psi) ∈ M` and `M` is MCS, then there exists an MCS `W`
such that `ExistsTask M W` and `psi ∈ W`.
-/
theorem canonical_forward_F (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (psi : Formula Atom) (h_F : Formula.someFuture psi ∈ M) :
    ∃ W : Set (Formula Atom), SetMaximalConsistent FrameClass.Base W ∧ ExistsTask M W ∧ psi ∈ W := by
  -- Step 1: {psi} ∪ gContent(M) is consistent
  have h_seed_cons : SetConsistent FrameClass.Base (forwardTemporalWitnessSeed M psi) :=
    forward_temporal_witness_seed_consistent M h_mcs psi h_F
  -- Step 2: Extend to an MCS via Lindenbaum
  obtain ⟨W, h_extends, h_W_mcs⟩ := set_lindenbaum_base h_seed_cons
  -- Step 3: W is the witness
  use W, h_W_mcs
  constructor
  · -- ExistsTask M W: gContent M ⊆ W
    exact Set.Subset.trans (g_content_subset_forward_temporal_witness_seed M psi) h_extends
  · -- psi ∈ W: psi ∈ forwardTemporalWitnessSeed M psi ⊆ W
    exact h_extends (psi_mem_forward_temporal_witness_seed M psi)

/-!
## Backward P (Symmetric Key Property)
-/

/--
P-backward property: If `P(psi) ∈ M` and `M` is MCS, then there exists an MCS `W`
such that `ExistsTask_past M W` and `psi ∈ W`.
-/
theorem canonical_backward_P (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (psi : Formula Atom) (h_P : Formula.somePast psi ∈ M) :
    ∃ W : Set (Formula Atom), SetMaximalConsistent FrameClass.Base W ∧ ExistsTask_past M W ∧ psi ∈ W := by
  -- Step 1: {psi} ∪ hContent(M) is consistent
  have h_seed_cons : SetConsistent (FrameClass.Base : FrameClass) (pastTemporalWitnessSeed M psi) :=
    past_temporal_witness_seed_consistent M h_mcs psi h_P
  -- Step 2: Extend to an MCS via Lindenbaum
  obtain ⟨W, h_extends, h_W_mcs⟩ := set_lindenbaum_base h_seed_cons
  -- Step 3: W is the witness
  use W, h_W_mcs
  constructor
  · -- ExistsTask_past M W: hContent M ⊆ W
    exact Set.Subset.trans (h_content_subset_past_temporal_witness_seed M psi) h_extends
  · -- psi ∈ W
    exact h_extends (psi_mem_past_temporal_witness_seed M psi)

/-!
## Forward U and Backward S (Until/Since Witness Properties)
-/

/--
U-forward property: If `φ U ψ ∈ M` and `M` is MCS, then there exists an MCS `W`
such that `ExistsTask M W` and `ψ ∈ W`.
-/
theorem canonical_forward_U (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (φ ψ : Formula Atom) (h_U : Formula.untl ψ φ ∈ M) :
    ∃ W : Set (Formula Atom), SetMaximalConsistent FrameClass.Base W ∧ ExistsTask M W ∧ ψ ∈ W := by
  -- Step 1: {ψ} ∪ gContent(M) is consistent (uses until_induction)
  have h_seed_cons : SetConsistent (FrameClass.Base : FrameClass) (untilWitnessSeed M ψ) :=
    until_witness_seed_consistent M h_mcs φ ψ h_U
  -- Step 2: Extend to an MCS via Lindenbaum
  obtain ⟨W, h_extends, h_W_mcs⟩ := set_lindenbaum_base h_seed_cons
  -- Step 3: W is the witness
  use W, h_W_mcs
  constructor
  · -- ExistsTask M W: gContent M ⊆ W
    exact Set.Subset.trans (g_content_subset_until_witness_seed M ψ) h_extends
  · -- ψ ∈ W
    exact h_extends (psi_mem_until_witness_seed M ψ)

/--
S-backward property: If `φ S ψ ∈ M` and `M` is MCS, then there exists an MCS `W`
such that `ExistsTask_past M W` and `ψ ∈ W`.
-/
theorem canonical_backward_S (M : Set (Formula Atom)) (h_mcs : SetMaximalConsistent (FrameClass.Base : FrameClass) M)
    (φ ψ : Formula Atom) (h_S : Formula.snce ψ φ ∈ M) :
    ∃ W : Set (Formula Atom), SetMaximalConsistent FrameClass.Base W ∧ ExistsTask_past M W ∧ ψ ∈ W := by
  -- Step 1: {ψ} ∪ hContent(M) is consistent (uses since_induction)
  have h_seed_cons : SetConsistent (FrameClass.Base : FrameClass) (pastTemporalWitnessSeed M ψ) :=
    since_witness_seed_consistent M h_mcs φ ψ h_S
  -- Step 2: Extend to an MCS via Lindenbaum
  obtain ⟨W, h_extends, h_W_mcs⟩ := set_lindenbaum_base h_seed_cons
  -- Step 3: W is the witness
  use W, h_W_mcs
  constructor
  · -- ExistsTask_past M W: hContent M ⊆ W
    exact Set.Subset.trans (h_content_subset_past_temporal_witness_seed M ψ) h_extends
  · -- ψ ∈ W
    exact h_extends (psi_mem_past_temporal_witness_seed M ψ)

/-!
## Transitivity of Canonical Relations
-/

/--
ExistsTask is transitive using the Temporal 4 axiom (G phi -> GG phi).
-/
theorem existsTask_transitive {fc : FrameClass} (M M' M'' : Set (Formula Atom))
    (h_mcs : SetMaximalConsistent fc M)
    (h_R1 : ExistsTask M M') (h_R2 : ExistsTask M' M'') :
    ExistsTask M M'' := by
  intro phi h_G_phi
  -- phi ∈ gContent M means G phi ∈ M
  -- By Temporal 4: ⊢ G phi → G(G phi), so G(G phi) ∈ M
  have h_T4 : DerivationTree fc [] ((Formula.allFuture phi).imp (Formula.allFuture (Formula.allFuture phi))) :=
    (temp_4_derived phi).lift (FrameClass.base_le fc)
  have h_GG : Formula.allFuture (Formula.allFuture phi) ∈ M :=
    SetMaximalConsistent.implication_property h_mcs (theoremInMcsFc h_mcs h_T4) h_G_phi
  -- G phi ∈ gContent M, and gContent M ⊆ M' by h_R1
  have h_G_in_M' : Formula.allFuture phi ∈ M' := h_R1 h_GG
  -- phi ∈ gContent M', and gContent M' ⊆ M'' by h_R2
  exact h_R2 h_G_in_M'

/-- Backward compatibility alias. -/
abbrev canonicalRTransitive := @existsTask_transitive

/--
hContent chain transitivity using the Temporal 4 axiom for past (H phi -> HH phi).
-/
theorem h_content_chain_transitive {fc : FrameClass} (M N V : Set (Formula Atom))
    (h_mcs_V : SetMaximalConsistent fc V)
    (hNV : hContent V ⊆ N) (hMN : hContent N ⊆ M) :
    hContent V ⊆ M := by
  intro phi h_H_phi
  -- h_H_phi : phi ∈ hContent V, i.e., H phi ∈ V
  -- By Temporal 4 for H: H phi → H(H phi), so H(H phi) ∈ V
  have h_H4 : DerivationTree fc [] (phi.allPast.imp phi.allPast.allPast) :=
    (temp_4_past phi).lift (FrameClass.base_le fc)
  have h_HH_in_V := SetMaximalConsistent.implication_property h_mcs_V (theoremInMcsFc h_mcs_V h_H4) h_H_phi
  -- H phi ∈ hContent V, and hContent V ⊆ N, so H phi ∈ N
  have h_Hphi_in_N := hNV h_HH_in_V
  -- phi ∈ hContent N, and hContent N ⊆ M, so phi ∈ M
  exact hMN h_Hphi_in_N

end Cslib.Logic.Bimodal.Metalogic.Bundle
