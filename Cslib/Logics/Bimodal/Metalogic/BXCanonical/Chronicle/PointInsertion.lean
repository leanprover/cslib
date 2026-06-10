/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame
import Cslib.Logics.Bimodal.Metalogic.BXCanonical.OrderedSeedConsistency
import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleTypes
import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.RRelation
import Cslib.Logics.Bimodal.Metalogic.BXCanonical.CanonicalModel
import Cslib.Logics.Bimodal.Theorems.TemporalDerived

/-!
# Point Insertion Lemmas (Burgess 2.4-2.8)

Implements the core point insertion machinery for the Burgess chronicle
construction, adapted for strict (irreflexive) temporal semantics on the
`irr_until` branch.

## Key Adaptations from Burgess 1982

Burgess uses axioms A3a and A4a which are **not valid** under strict semantics
(see counterexample in `TemporalDerived.lean`). We replace them with BX axioms:

- **A3a's role** (Lemma 2.4 seed consistency): BX4 (`connect_future: φ → G(P(φ))`)
  + BX5 (`self_accum_until`) provide the algebraic content directly.
- **A4a's role** (Lemma 2.6 point insertion): BX5 + BX6 (`absorb_until`)
  + BX7 (`linear_until`) provide the needed structural properties.

## Open Guard Semantics (Task 113)

Under open guard semantics with guard interval (t,s):
- U(γ,β) at t means ∃s>t, β(s) ∧ ∀u∈(t,s), γ(u)
- The guard γ does NOT cover the current point t (open interval)
- BX9 (until_elim) is REMOVED: γ ∨ β at t is not guaranteed
- The until_guard axiom is REMOVED: γ at t is not guaranteed
- BX10 (until_F: γ U β → F(β)) remains valid

Several lemmas in this file are INVALID under open guard and retained as
sorry stubs with documentation. Key valid tools:
- BX10: γ U β → F(β) (eventuality extraction)
- BX5: γ U β → (γ ∧ (γ U β)) U β (self-accumulation)
- BX4: φ → G(P(φ)) (connect_future)

Burgess's Lemma 2.4 produces an endpoint MCS with β and g_content(A),
plus evidence that U(γ,β) was active in the past (via BX4). The guard γ
is handled by the interval DCS construction in Phase 4.

## Definitions

Local definitions used for point insertion lemmas.

## Main Results

- `lemma_2_4`: Until witness endpoint construction
- `lemma_2_5b`: Composition of g_content ordering (transitivity)
- `lemma_2_6`: Counterexample insertion (delta not in C -> insert D with neg delta)
- `dc_delta_B_burgessR3`: Extension of B by delta preserves burgessR3
- `BurgessR3Maximal_extension_fails`: Maximality prevents consistent proper extensions

### Withdrawn (Phase 3, Task 107) / Re-assessed (Phase 5, Task 107)

- `lemma_2_6_strong`: FALSE under strict semantics (g_content(D) <= C unprovable)
- `lemma_2_7`: Re-assessed as VALID (Phase 5, plan v27). The earlier "FALSE"
  assessment was for a D2-branch proof that predated BX13. Burgess's original
  proof using BX5+BX7+BX13 works under strict/open-guard semantics.
- `lemma_2_8`: Depends on D2-style reasoning; may be recoverable but not needed

## References

- Burgess 1982: "Basic tense logic", Section 2, Lemmas 2.4-2.8
- Task 107 implementation plan, Phase 3
-/

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.BXCanonical
open Cslib.Logic.Bimodal.Metalogic.BXCanonical.CanonicalModel
open Cslib.Logic.Bimodal.Theorems.Propositional
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.TemporalDerived

/-! ## Private Helper: theorem_in_mcs for SetMaximalConsistent fc -/

private noncomputable def theorem_in_mcs {fc : FrameClass} {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : SetMaximalConsistent fc M)
    (h_deriv : DerivationTree fc [] phi) : phi ∈ M :=
  SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) h_deriv

/-! ## Helper: F(neg phi) from G(phi) not in A

A common pattern: if G(φ) ∉ MCS A, then F(¬φ) ∈ A.
This requires going through double-negation elimination under G,
since F(¬φ) = ¬G(¬¬φ) which is not definitionally equal to ¬G(φ).
-/

/-- If G(φ) ∉ MCS A, then F(¬φ) ∈ A. -/
theorem F_neg_of_G_not (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ : Formula Atom)
    (h_Gφ_not : Formula.all_future φ ∉ A) :
    Formula.some_future φ.neg ∈ A := by
  -- Case split on F(¬φ) directly
  rcases SetMaximalConsistent.negation_complete h_mcs (Formula.some_future φ.neg) with h | h
  · exact h
  · -- ¬F(¬φ) ∈ A: derive G(¬¬φ) via duality bridge
    have h_G_nnφ : Formula.all_future φ.neg.neg ∈ A :=
      neg_some_future_to_all_future_neg h_mcs φ.neg h
    -- G(¬¬φ) → G(φ) via DNE under G
    have h_dne : DerivationTree fc [] (φ.neg.neg.imp φ) :=
      liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.double_negation φ)
    have h_G_dne : DerivationTree fc [] (Formula.all_future (φ.neg.neg.imp φ)) :=
      DerivationTree.temporal_necessitation _ h_dne
    have h_kd : DerivationTree fc [] ((φ.neg.neg.imp φ).all_future.imp
        (φ.neg.neg.all_future.imp φ.all_future)) :=
      liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived φ.neg.neg φ)
    have h1 := theorem_in_mcs h_mcs h_G_dne
    have h2 := theorem_in_mcs h_mcs h_kd
    have h3 := SetMaximalConsistent.implication_property h_mcs h2 h1
    have h_Gφ := SetMaximalConsistent.implication_property h_mcs h3 h_G_nnφ
    exact absurd h_Gφ h_Gφ_not

/-- If H(φ) ∉ MCS A, then P(¬φ) ∈ A. Dual of `F_neg_of_G_not`. -/
theorem P_neg_of_H_not (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ : Formula Atom)
    (h_Hφ_not : Formula.all_past φ ∉ A) :
    Formula.some_past φ.neg ∈ A := by
  rcases SetMaximalConsistent.negation_complete h_mcs (Formula.some_past φ.neg) with h | h
  · exact h
  · have h_H_nnφ : Formula.all_past φ.neg.neg ∈ A :=
      neg_some_past_to_all_past_neg h_mcs φ.neg h
    have h_dne : DerivationTree fc [] (φ.neg.neg.imp φ) :=
      liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.double_negation φ)
    have h_H_dne : DerivationTree fc [] (Formula.all_past (φ.neg.neg.imp φ)) :=
      Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_dne
    have h_kd : DerivationTree fc [] ((φ.neg.neg.imp φ).all_past.imp
        (φ.neg.neg.all_past.imp φ.all_past)) :=
      Cslib.Logic.Bimodal.Theorems.past_k_dist φ.neg.neg φ
    have h1 := theorem_in_mcs h_mcs h_H_dne
    have h2 := theorem_in_mcs h_mcs h_kd
    have h3 := SetMaximalConsistent.implication_property h_mcs h2 h1
    have h_Hφ := SetMaximalConsistent.implication_property h_mcs h3 h_H_nnφ
    exact absurd h_Hφ h_Hφ_not

/-! ## Lemma 2.4: Until Witness Endpoint Construction -/

/-- The Until witness seed: {β} ∪ g_content(A) is consistent when
U(γ,β) ∈ MCS A. -/
theorem until_witness_seed_consistent (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl β γ ∈ A) :
    SetConsistent fc ({β} ∪ g_content A) := by
  have h_F_β : Formula.some_future β ∈ A := by
    have h_ax : DerivationTree fc [] ((Formula.untl β γ).imp (Formula.some_future β)) :=
      DerivationTree.axiom [] _ (Axiom.until_F γ β) trivial
    exact SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs h_mcs h_ax) h_until
  exact forward_temporal_witness_seed_consistent A h_mcs β h_F_β

/-- **Lemma 2.4** (adapted for strict semantics): Given MCS A with U(γ, β) ∈ A
and ¬burgessR3(A, Set.univ, C) for the constructed C, there exists MCS C with
β ∈ C, g_content(A) ⊆ C, P(U(γ,β)) ∈ C, and a DCS interval set B with
BurgessR3Maximal(A, B, C).

The hypothesis `h_not_univ_gen` provides ¬burgessR3(A, Set.univ, C) for ANY MCS C
extending the seed {β} ∪ g_content(A). This is needed because C is constructed
internally and callers cannot know it in advance. -/
noncomputable def lemma_2_4 (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl β γ ∈ A) :
    ∃ B C : Set (Formula Atom), SetMaximalConsistent fc C ∧
      β ∈ C ∧ g_content A ⊆ C ∧
      Formula.some_past (Formula.untl β γ) ∈ C ∧
      BurgessR3Maximal fc A B C := by
  have h_seed_cons := until_witness_seed_consistent fc h_mcs γ β h_until
  obtain ⟨C, h_sup, h_C_mcs⟩ := set_lindenbaum_fc h_seed_cons
  have h_β_C : β ∈ C := h_sup (Set.mem_union_left _ (Set.mem_singleton β))
  have h_g_sub : g_content A ⊆ C := fun χ hχ => h_sup (Set.mem_union_right _ hχ)
  have h_GP : Formula.all_future (Formula.some_past (Formula.untl β γ)) ∈ A := by
    have h_ax : DerivationTree fc [] ((Formula.untl β γ).imp
        (Formula.all_future (Formula.some_past (Formula.untl β γ)))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future (Formula.untl β γ)) trivial
    exact SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs h_mcs h_ax) h_until
  have h_P_until_C : Formula.some_past (Formula.untl β γ) ∈ C :=
    h_g_sub h_GP
  obtain ⟨B, h_B⟩ := burgessR3Maximal_from_g_content_sub fc h_mcs h_C_mcs h_g_sub
  exact ⟨B, C, h_C_mcs, h_β_C, h_g_sub, h_P_until_C, h_B⟩

/-- BX10 at MCS level: U(γ,β) ∈ A implies F(β) ∈ A. -/
theorem until_F_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl β γ ∈ A) :
    Formula.some_future β ∈ A := by
  have h_ax : DerivationTree fc [] ((Formula.untl β γ).imp (Formula.some_future β)) :=
    DerivationTree.axiom [] _ (Axiom.until_F γ β) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs h_ax) h_until

/-- BX5 at MCS level: U(γ,β) ∈ A implies U(γ∧U(γ,β), β) ∈ A. -/
theorem self_accum_until_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl β γ ∈ A) :
    Formula.untl β (Formula.and γ (Formula.untl β γ)) ∈ A := by
  have h_ax : DerivationTree fc [] ((Formula.untl β γ).imp
      (Formula.untl β (Formula.and γ (Formula.untl β γ)))) :=
    DerivationTree.axiom [] _ (Axiom.self_accum_until γ β) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs h_ax) h_until

/-- BX5' at set-MCS level: snce(γ, β) ∈ A implies snce(γ ∧ snce(γ, β), β) ∈ A. -/
theorem self_accum_since_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_since : Formula.snce β γ ∈ A) :
    Formula.snce β (Formula.and γ (Formula.snce β γ)) ∈ A := by
  have h_ax : DerivationTree fc [] ((Formula.snce β γ).imp
      (Formula.snce β (Formula.and γ (Formula.snce β γ)))) :=
    DerivationTree.axiom [] _ (Axiom.self_accum_since γ β) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs h_ax) h_since

/-- BX4 at MCS level: φ ∈ A implies G(P(φ)) ∈ A. -/
theorem connect_future_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ : Formula Atom)
    (h_φ : φ ∈ A) :
    Formula.all_future (Formula.some_past φ) ∈ A := by
  have h_ax : DerivationTree fc [] (φ.imp (Formula.all_future (Formula.some_past φ))) :=
    DerivationTree.axiom [] _ (Axiom.connect_future φ) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs h_ax) h_φ

/-- Conjunction introduction at MCS level. -/
theorem conj_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ ψ : Formula Atom)
    (h_φ : φ ∈ A) (h_ψ : ψ ∈ A) :
    Formula.and φ ψ ∈ A := by
  rcases SetMaximalConsistent.negation_complete h_mcs (φ.imp ψ.neg) with h | h
  · have h_neg_ψ := SetMaximalConsistent.implication_property h_mcs h h_φ
    exact absurd h_ψ (SetMaximalConsistent.neg_excludes h_mcs _ h_neg_ψ)
  · exact h

/-- MCS disjunction elimination (local version): If (φ ∨ ψ) ∈ A then φ ∈ A ∨ ψ ∈ A.
Recall φ.or ψ = φ.neg.imp ψ. -/
private theorem or_elim_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {φ ψ : Formula Atom}
    (h : (φ.or ψ) ∈ A) : φ ∈ A ∨ ψ ∈ A := by
  rcases SetMaximalConsistent.negation_complete h_mcs φ with h_φ | h_neg_φ
  · exact Or.inl h_φ
  · exact Or.inr (SetMaximalConsistent.implication_property h_mcs h h_neg_φ)

/-- BX7 (linear_until) at MCS level: If U(φ,ψ) ∈ A and U(χ,θ) ∈ A,
then one of three disjuncts holds:
  D1: U(φ∧χ, ψ∧θ) ∈ A, or D2: U(φ∧χ, ψ∧χ) ∈ A, or D3: U(φ∧χ, φ∧θ) ∈ A. -/
theorem linear_until_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ ψ χ θ : Formula Atom)
    (h_u1 : Formula.untl ψ φ ∈ A)
    (h_u2 : Formula.untl θ χ ∈ A) :
    Formula.untl (Formula.and ψ θ) (Formula.and φ χ) ∈ A ∨
    Formula.untl (Formula.and ψ χ) (Formula.and φ χ) ∈ A ∨
    Formula.untl (Formula.and φ θ) (Formula.and φ χ) ∈ A := by
  -- Form the conjunction: U(φ,ψ) ∧ U(χ,θ) ∈ A
  have h_conj := conj_mcs fc h_mcs _ _ h_u1 h_u2
  -- Apply BX7 axiom
  have h_bx7 := DerivationTree.axiom (fc := fc) [] _ (Axiom.linear_until φ ψ χ θ) trivial
  have h_disj := SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs h_bx7) h_conj
  -- h_disj : (D1 ∨ D2) ∨ D3 ∈ A
  -- Case split on the outer disjunction
  rcases or_elim_mcs fc h_mcs h_disj with h12 | h3
  · -- D1 ∨ D2 ∈ A
    rcases or_elim_mcs fc h_mcs h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-- BX7' (linear_since) at MCS level: If S(φ,ψ) ∈ A and S(χ,θ) ∈ A,
then one of three disjuncts holds:
  D1: S(φ∧χ, ψ∧θ) ∈ A, or D2: S(φ∧χ, ψ∧χ) ∈ A, or D3: S(φ∧χ, φ∧θ) ∈ A. -/
theorem linear_since_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ ψ χ θ : Formula Atom)
    (h_s1 : Formula.snce ψ φ ∈ A)
    (h_s2 : Formula.snce θ χ ∈ A) :
    Formula.snce (Formula.and ψ θ) (Formula.and φ χ) ∈ A ∨
    Formula.snce (Formula.and ψ χ) (Formula.and φ χ) ∈ A ∨
    Formula.snce (Formula.and φ θ) (Formula.and φ χ) ∈ A := by
  have h_conj := conj_mcs fc h_mcs _ _ h_s1 h_s2
  have h_bx7 := DerivationTree.axiom (fc := fc) [] _ (Axiom.linear_since φ ψ χ θ) trivial
  have h_disj := SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs h_bx7) h_conj
  rcases or_elim_mcs fc h_mcs h_disj with h12 | h3
  · rcases or_elim_mcs fc h_mcs h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-! ## Lemma 2.5: g_content Ordering Composition -/

/-- **Lemma 2.5** (composition): g_content ordering is transitive. -/
theorem lemma_2_5b (fc : FrameClass) {A D C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_AD : g_content A ⊆ D) (h_DC : g_content D ⊆ C) :
    g_content A ⊆ C := by
  intro φ hφ
  have h_GGφ : Formula.all_future (Formula.all_future φ) ∈ A :=
    SetMaximalConsistent.all_future_all_future h_mcs_A hφ
  have h_Gφ_D : Formula.all_future φ ∈ D := h_AD h_GGφ
  exact h_DC h_Gφ_D

/-- Dual of lemma_2_5b: h_content ordering is transitive (past direction). -/
theorem lemma_2_5b_past (fc : FrameClass) {A D C : Set (Formula Atom)}
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_CD : h_content C ⊆ D) (h_DA : h_content D ⊆ A) :
    h_content C ⊆ A := by
  intro φ hφ
  have h_HHφ : Formula.all_past (Formula.all_past φ) ∈ C :=
    SetMaximalConsistent.all_past_all_past h_mcs_C hφ
  have h_Hφ_D : Formula.all_past φ ∈ D := h_CD h_HHφ
  exact h_DA h_Hφ_D

/-! ## Lemma 2.6: Counterexample Insertion (Negative Insertion) -/

/-- **Lemma 2.6** (adapted): Given MCS A and C with g_content(A) ⊆ C,
if δ ∉ C, then there exists MCS D with ¬δ ∈ D and g_content(A) ⊆ D. -/
noncomputable def lemma_2_6 (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_g_AC : g_content A ⊆ C)
    (δ : Formula Atom)
    (h_δ_not_C : δ ∉ C) :
    ∃ D : Set (Formula Atom), SetMaximalConsistent fc D ∧
      δ.neg ∈ D ∧ g_content A ⊆ D := by
  have h_Gδ_not_A : Formula.all_future δ ∉ A := by
    intro h_Gδ; exact h_δ_not_C (h_g_AC h_Gδ)
  have h_F_neg_δ := F_neg_of_G_not fc h_mcs_A δ h_Gδ_not_A
  have h_seed_cons := forward_temporal_witness_seed_consistent A h_mcs_A δ.neg h_F_neg_δ
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  exact ⟨D, h_D_mcs,
    h_sup (Set.mem_union_left _ (Set.mem_singleton _)),
    fun χ hχ => h_sup (Set.mem_union_right _ hχ)⟩

/-! ### Withdrawn and Re-assessed Lemmas

- `lemma_2_6_strong`: FALSE under strict semantics (g_content(D) ≤ C unprovable).
  Remains withdrawn.

- `lemma_2_7`: Previously marked FALSE under strict semantics (Phase 3, task 107),
  but that assessment was for a "D2 branch" proof approach that predated BX13
  (enrichment_until, Burgess A3a). With BX13 now available (Phase 2, task 107),
  Burgess's ORIGINAL proof of Lemma 2.7 is valid:
  1. BX5 (self_accum_until) enriches the Until guard
  2. BX7 (linear_until) provides the three-way disjunction
  3. BX13 (enrichment_until) simplifies the surviving disjunct
  4. BX1/BX2G (monotonicity) rule out two disjuncts
  None of these axioms depend on BX9 (removed) or the T-axiom.
  **Gate verdict (Phase 5, plan v27): VALID. Proceed with Strategy 1.**

- `lemma_2_8`: May also be recoverable with BX13, but Lemma 2.7 suffices
  for the C5 n>0 sub-case 3 (Burgess Lemma 2.10). Not needed if 2.7 works.
-/

/-- Conjunction membership gives left component in MCS. -/
theorem conj_left_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ ψ : Formula Atom)
    (h_conj : Formula.and φ ψ ∈ A) :
    φ ∈ A := by
  have h_ax : DerivationTree fc [] ((Formula.and φ ψ).imp φ) := lce_imp φ ψ
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs h_ax) h_conj

/-- Conjunction membership gives right component in MCS. -/
theorem conj_right_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ ψ : Formula Atom)
    (h_conj : Formula.and φ ψ ∈ A) :
    ψ ∈ A := by
  have h_ax : DerivationTree fc [] ((Formula.and φ ψ).imp ψ) := rce_imp φ ψ
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs h_ax) h_conj

/-! ## G/H Implies F/P (Seriality + BX3 + BX10/BX12) -/

/-- In an MCS, G(α) implies F(α). Uses seriality + BX3 + BX10 + BX12. -/
theorem G_implies_F_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (α : Formula Atom)
    (h_G : Formula.all_future α ∈ A) :
    Formula.some_future α ∈ A := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_weak : DerivationTree fc [] (Formula.imp α (Formula.imp top α)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s α top) trivial
  have h_G_top_α : Formula.all_future (Formula.imp top α) ∈ A := by
    have h1 := theorem_in_mcs h_mcs (DerivationTree.temporal_necessitation _ h_weak)
    have h2 := theorem_in_mcs h_mcs
      (liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived α (Formula.imp top α)))
    exact SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h2 h1) h_G
  have h_top_in : top ∈ A :=
    theorem_in_mcs h_mcs (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))
  have h_F_top : Formula.some_future top ∈ A :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ Axiom.serial_future trivial)) h_top_in
  have h_TUT : Formula.untl top top ∈ A :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.F_until_equiv top) trivial)) h_F_top
  have h_TUα : Formula.untl α top ∈ A := by
    have h1 := SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.right_mono_until top α top) trivial))
      h_G_top_α
    exact SetMaximalConsistent.implication_property h_mcs h1 h_TUT
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.until_F top α) trivial)) h_TUα

/-- In an MCS, H(α) implies P(α). Mirror of G_implies_F_mcs. -/
theorem H_implies_P_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (α : Formula Atom)
    (h_H : Formula.all_past α ∈ A) :
    Formula.some_past α ∈ A := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_weak : DerivationTree fc [] (Formula.imp α (Formula.imp top α)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s α top) trivial
  have h_H_top_α : Formula.all_past (Formula.imp top α) ∈ A := by
    have h1 := theorem_in_mcs h_mcs (Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_weak)
    have h2 := theorem_in_mcs h_mcs (Cslib.Logic.Bimodal.Theorems.past_k_dist α (Formula.imp top α))
    exact SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h2 h1) h_H
  have h_top_in : top ∈ A :=
    theorem_in_mcs h_mcs (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))
  have h_P_top : Formula.some_past top ∈ A :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ Axiom.serial_past trivial)) h_top_in
  have h_TST : Formula.snce top top ∈ A :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.P_since_equiv top) trivial)) h_P_top
  have h_TSα : Formula.snce α top ∈ A := by
    have h1 := SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.right_mono_since top α top) trivial))
      h_H_top_α
    exact SetMaximalConsistent.implication_property h_mcs h1 h_TST
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs (DerivationTree.axiom [] _ (Axiom.since_P top α) trivial)) h_TSα

/-- G-propagation seed consistency. -/
theorem g_propagation_seed_consistent (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (α : Formula Atom)
    (h_G : Formula.all_future α ∈ A) :
    SetConsistent fc (forward_temporal_witness_seed A α) := by
  exact forward_temporal_witness_seed_consistent A h_mcs α (G_implies_F_mcs fc h_mcs α h_G)

/-- G-propagation insertion: given G(α) ∈ f(x), produce MCS D with α ∈ D
and g_content(f(x)) ⊆ D. -/
noncomputable def g_propagation_witness (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (α : Formula Atom)
    (h_G : Formula.all_future α ∈ A) :
    ∃ D : Set (Formula Atom), SetMaximalConsistent fc D ∧ α ∈ D ∧ g_content A ⊆ D := by
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc (g_propagation_seed_consistent fc h_mcs α h_G)
  exact ⟨D, h_D_mcs,
    h_sup (Set.mem_union_left _ (Set.mem_singleton _)),
    fun χ hχ => h_sup (Set.mem_union_right _ hχ)⟩

/-! ## Seed Consistency for DCS Extension -/

/-- If S is a DCS and φ ∉ S, then {φ.neg} ∪ S is consistent. -/
theorem dcs_neg_union_consistent (fc : FrameClass) {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc Sig)
    {φ : Formula Atom} (h_not : φ ∉ Sig) :
    SetConsistent fc ({φ.neg} ∪ Sig) := by
  intro L hL ⟨d⟩
  apply h_not
  by_cases h_neg_in_L : φ.neg ∈ L
  · have d_ext : DerivationTree fc (φ.neg :: L) Formula.bot :=
      DerivationTree.weakening L (φ.neg :: L) Formula.bot d (List.subset_cons_of_subset _ (List.Subset.refl L))
    have d_imp : DerivationTree fc L φ.neg.neg :=
      deduction_theorem L φ.neg Formula.bot d_ext
    have h_dne : DerivationTree fc [] (φ.neg.neg.imp φ) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.double_negation φ
    have d_phi : DerivationTree fc L φ :=
      DerivationTree.modus_ponens L φ.neg.neg φ
        (DerivationTree.weakening [] L (φ.neg.neg.imp φ) h_dne (List.nil_subset L)) d_imp
    set M := L.filter (fun x => !decide (x = φ.neg)) with hM_def
    have hM_sub_S : ∀ ψ ∈ M, ψ ∈ Sig := by
      intro ψ hψ; rw [hM_def] at hψ
      have h_mem := List.mem_filter.mp hψ
      have h1 : ψ ∈ L := h_mem.1
      have h2 : ψ ≠ φ.neg := by simp at h_mem; exact h_mem.2
      rcases hL ψ h1 with h_sing | h_S
      · exact absurd (Set.mem_singleton_iff.mp h_sing) h2
      · exact h_S
    have hL_sub : L ⊆ φ.neg :: M := by
      intro x hx
      by_cases heq : x = φ.neg
      · subst heq; exact .head M
      · exact .tail _ (List.mem_filter.mpr ⟨hx, by simp; exact heq⟩)
    have d_phi_w : DerivationTree fc (φ.neg :: M) φ :=
      DerivationTree.weakening L (φ.neg :: M) φ d_phi hL_sub
    have d_neg_imp : DerivationTree fc M (φ.neg.imp φ) :=
      deduction_theorem M φ.neg φ d_phi_w
    have h_peirce : DerivationTree fc [] ((φ.neg.imp φ).imp φ) := by
      have s1 : DerivationTree fc [φ.neg, φ.neg.imp φ] φ :=
        DerivationTree.modus_ponens [φ.neg, φ.neg.imp φ] φ.neg φ
          (DerivationTree.assumption _ (φ.neg.imp φ) (by simp))
          (DerivationTree.assumption _ φ.neg (by simp))
      have s2 : DerivationTree fc [φ.neg, φ.neg.imp φ] Formula.bot :=
        DerivationTree.modus_ponens [φ.neg, φ.neg.imp φ] φ Formula.bot
          (DerivationTree.assumption _ φ.neg (by simp)) s1
      have s3 := deduction_theorem [φ.neg.imp φ] φ.neg Formula.bot s2
      have s4 : DerivationTree fc [φ.neg.imp φ] φ :=
        DerivationTree.modus_ponens [φ.neg.imp φ] φ.neg.neg φ
          (DerivationTree.weakening [] [φ.neg.imp φ] (φ.neg.neg.imp φ) h_dne (List.nil_subset _)) s3
      exact deduction_theorem [] (φ.neg.imp φ) φ s4
    have d_phi_M : DerivationTree fc M φ :=
      DerivationTree.modus_ponens M (φ.neg.imp φ) φ
        (DerivationTree.weakening [] M ((φ.neg.imp φ).imp φ) h_peirce (List.nil_subset M)) d_neg_imp
    exact h_dcs.2 M φ hM_sub_S d_phi_M
  · have hL_S : ∀ ψ ∈ L, ψ ∈ Sig := by
      intro ψ hψ
      have h_mem := hL ψ hψ
      rcases h_mem with h_sing | h_S
      · have : ψ = φ.neg := Set.mem_singleton_iff.mp h_sing
        exact absurd (this ▸ hψ) h_neg_in_L
      · exact h_S
    exact absurd (h_dcs.1 L hL_S ⟨d⟩) (not_false)

/-! ## R3Maximal Properties -/

/-- R3Maximal negation completeness: δ ∉ B implies δ.neg ∈ B. -/
theorem r3Maximal_neg_of_not_mem (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_R3 : R3Maximal fc A B C) (δ : Formula Atom) (h_not : δ ∉ B) :
    δ.neg ∈ B := by
  by_contra h_neg_not
  have h_cons := dcs_neg_union_consistent fc h_R3.1 h_not
  have h_dc_dcs := deductiveClosure_is_dcs fc h_cons
  have h_B_sub : B ⊆ deductiveClosure fc ({δ.neg} ∪ B) :=
    fun φ hφ => subset_deductiveClosure fc ({δ.neg} ∪ B) (Set.mem_union_right _ hφ)
  have h_neg_in : δ.neg ∈ deductiveClosure fc ({δ.neg} ∪ B) :=
    subset_deductiveClosure fc ({δ.neg} ∪ B) (Set.mem_union_left _ (Set.mem_singleton δ.neg))
  have h_proper : B ⊂ deductiveClosure fc ({δ.neg} ∪ B) :=
    ⟨h_B_sub, fun h_eq => h_neg_not (h_eq h_neg_in)⟩
  have h_r3 : r3Relation A (deductiveClosure fc ({δ.neg} ∪ B)) C :=
    r3Relation_subset h_R3.2.1 h_B_sub
  exact h_R3.2.2 _ h_dc_dcs h_proper h_r3

/-- R3Maximal forces MCS (via monotonicity of r3Relation). -/
theorem R3Maximal_is_mcs (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_R3 : R3Maximal fc A B C) : SetMaximalConsistent fc B := by
  refine ⟨h_R3.1.1, ?_⟩
  intro φ h_not_φ h_cons_insert
  have h_cons : SetConsistent fc ({φ} ∪ B) := by rwa [Set.insert_eq] at h_cons_insert
  have h_dc_dcs := deductiveClosure_is_dcs fc h_cons
  have h_B_sub : B ⊆ deductiveClosure fc ({φ} ∪ B) :=
    fun ψ hψ => subset_deductiveClosure fc ({φ} ∪ B) (Set.mem_union_right _ hψ)
  have h_φ_in : φ ∈ deductiveClosure fc ({φ} ∪ B) :=
    subset_deductiveClosure fc ({φ} ∪ B) (Set.mem_union_left _ (Set.mem_singleton φ))
  exact h_R3.2.2 _ h_dc_dcs ⟨h_B_sub, fun h_eq => h_not_φ (h_eq h_φ_in)⟩
    (r3Relation_subset h_R3.2.1 h_B_sub)

/-- An MCS has no proper DCS extension. -/
theorem mcs_no_proper_dcs_extension (fc : FrameClass) {B D : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc B) (h_dcs : SetDeductivelyClosed fc D)
    (hBD : B ⊂ D) : False := by
  obtain ⟨φ, h_φ_D, h_φ_not_B⟩ := Set.not_subset.mp hBD.2
  have h_incons := h_mcs.2 φ h_φ_not_B
  apply h_incons
  intro L hL ⟨d⟩
  exact h_dcs.1 L (fun ψ hψ => (Set.insert_subset h_φ_D hBD.1) (hL ψ hψ)) ⟨d⟩

/-! ## Burgess Lemma 2.6 for BurgessR3Maximal (Content-Based)

The content-based BurgessR3Maximal is ANTI-monotone in B (adding elements to B
adds more requirements on A and C), so B is a genuinely non-MCS DCS in general.
The maximality witness lemma proves that if delta not in B, then some extension
of B by delta violates burgessR3, which is the key to the splitting construction.
-/

/--
Helper: If L is a subset of {delta} union B with B a DCS, and L derives phi, then either
phi is in B, or there exists beta in B with a theorem (beta AND delta) implies phi.
-/
theorem dc_delta_B_controlled (fc : FrameClass) {B : Set (Formula Atom)} (h_dcs : ClosedUnderDerivation fc B)
    {delta phi : Formula Atom} {L : List (Formula Atom)}
    (hL_sub : ∀ psi ∈ L, psi ∈ ({delta} : Set (Formula Atom)) ∪ B)
    (hL_deriv : DerivationTree fc L phi) :
    (phi ∈ B) ∨ (∃ beta ∈ B, Nonempty (DerivationTree fc [] ((Formula.and beta delta).imp phi))) := by
  haveI : ∀ x : Formula Atom, Decidable (x ∈ B) := fun x => Classical.propDecidable _
  by_cases h_delta_L : delta ∈ L
  · let L_B := L.filter (· ∈ B)
    have hL_sub_dB : L ⊆ delta :: L_B := by
      intro psi hpsi
      by_cases h_B : psi ∈ B
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hpsi, decide_eq_true_eq.mpr h_B⟩)
      · rcases hL_sub psi hpsi with h | h
        · rw [Set.mem_singleton_iff.mp h]; exact .head _
        · exact absurd h h_B
    have d_w : DerivationTree fc (delta :: L_B) phi :=
      DerivationTree.weakening L (delta :: L_B) phi hL_deriv hL_sub_dB
    have d_imp := deduction_theorem L_B delta phi d_w
    have hLB_sub : ∀ psi ∈ L_B, psi ∈ B := by
      intro psi hpsi; exact decide_eq_true_eq.mp (List.mem_filter.mp hpsi).2
    by_cases hLB_empty : L_B = []
    · rw [hLB_empty] at d_imp
      have h_top_B : (Formula.bot.imp Formula.bot) ∈ B :=
        cud_contains_theorems h_dcs (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))
      exact Or.inr ⟨Formula.bot.imp Formula.bot, h_top_B, ⟨Cslib.Logic.Bimodal.Theorems.Combinators.imp_trans
        (Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp (Formula.bot.imp Formula.bot) delta) d_imp⟩⟩
    · have h_imp_B : delta.imp phi ∈ B := h_dcs L_B _ hLB_sub d_imp
      right
      refine ⟨delta.imp phi, h_imp_B, ⟨?_⟩⟩
      have h_l : DerivationTree fc [(Formula.and (delta.imp phi) delta)] (delta.imp phi) :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)]
          (Formula.and (delta.imp phi) delta) (delta.imp phi)
          (DerivationTree.weakening [] [(Formula.and (delta.imp phi) delta)] _
            (Cslib.Logic.Bimodal.Theorems.Propositional.lce_imp (delta.imp phi) delta) (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp))
      have h_r : DerivationTree fc [(Formula.and (delta.imp phi) delta)] delta :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)]
          (Formula.and (delta.imp phi) delta) delta
          (DerivationTree.weakening [] [(Formula.and (delta.imp phi) delta)] _
            (Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp (delta.imp phi) delta) (List.nil_subset _))
          (DerivationTree.assumption _ _ (by simp))
      have h_mp : DerivationTree fc [(Formula.and (delta.imp phi) delta)] phi :=
        DerivationTree.modus_ponens [(Formula.and (delta.imp phi) delta)] delta phi h_l h_r
      exact deduction_theorem [] (Formula.and (delta.imp phi) delta) phi h_mp
  · left
    have hL_B : ∀ psi ∈ L, psi ∈ B := by
      intro psi hpsi
      rcases hL_sub psi hpsi with h | h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hpsi) h_delta_L
      · exact h
    exact h_dcs L phi hL_B hL_deriv

/-- If BurgessR3Maximal(A, B, C) and delta ∉ B, the deductive closure of
{delta} ∪ B does NOT satisfy burgessR3(A, -, C).

No consistency requirement: the maximality clause in BurgessR3Maximal
quantifies over `ClosedUnderDerivation` sets, which includes
`deductiveClosure ({delta} ∪ B)` regardless of consistency. -/
theorem BurgessR3Maximal_extension_fails (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_R3M : BurgessR3Maximal fc A B C)
    {delta : Formula Atom} (h_delta_not : delta ∉ B) :
    ¬burgessR3 A (deductiveClosure fc ({delta} ∪ B)) C := by
  intro h_r3
  have h_cud : ClosedUnderDerivation fc (deductiveClosure fc ({delta} ∪ B)) :=
    deductiveClosure_closed_under_derivation fc _
  have h_sub : B ⊆ deductiveClosure fc ({delta} ∪ B) :=
    fun phi hphi => subset_deductiveClosure fc ({delta} ∪ B) (Set.mem_union_right _ hphi)
  have h_delta_in : delta ∈ deductiveClosure fc ({delta} ∪ B) :=
    subset_deductiveClosure fc ({delta} ∪ B) (Set.mem_union_left _ (Set.mem_singleton delta))
  have h_proper : B ⊂ deductiveClosure fc ({delta} ∪ B) :=
    ⟨h_sub, fun h_eq => h_delta_not (h_eq h_delta_in)⟩
  exact h_R3M.2.2 _ h_cud h_proper h_r3

/-- If both until and since conditions hold for delta extension of B,
then DC({delta} union B) satisfies burgessR3(A, -, C). -/
theorem dc_delta_B_burgessR3 (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_dcs : ClosedUnderDerivation fc B)
    (h_r3 : burgessR3 A B C)
    {delta : Formula Atom}
    (h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C, Formula.untl gamma (Formula.and beta delta) ∈ A)
    (h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A, Formula.snce alpha (Formula.and beta delta) ∈ C) :
    burgessR3 A (deductiveClosure fc ({delta} ∪ B)) C := by
  constructor
  · intro phi hphi gamma hgamma
    obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
    rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta, hbeta, ⟨h_impl⟩⟩
    · exact h_r3.1 phi h_B gamma hgamma
    · exact untl_left_mono_thm fc h_mcs_A h_impl (h_until_all beta hbeta gamma hgamma)
  · intro phi hphi alpha halpha
    obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
    rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta, hbeta, ⟨h_impl⟩⟩
    · exact h_r3.2 phi h_B alpha halpha
    · exact snce_left_mono_thm fc h_mcs_C h_impl (h_since_all beta hbeta alpha halpha)

/-! ## Xu Lemma 2.3: Guard Strengthening via left_mono_until_G

Xu 1988 Lemma 2.3: If R(A, B, C), then
  (i)  snce(alpha, top) ∈ B for every alpha ∈ A  (P(alpha) ∈ B)
  (ii) untl(gamma, top) ∈ B for every gamma ∈ C  (F(gamma) ∈ B)

This replaces the need for separation_until (BX14/A4a) in the chronicle
splitting construction by enabling a simpler DCS extension argument (Xu Lemma 2.4).

The proof uses left_mono_until_G (BX2G) for guard strengthening:
from G(snce(alpha, top)) ∈ A (derived via BX4 + BX12'), strengthen the guard
of untl(gamma, beta) ∈ A to untl(gamma, beta ∧ snce(alpha, top)) ∈ A,
then apply burgessR_implies_burgessRSince fc for the Since direction.
-/

/-- Xu Lemma 2.3 (i): If R(A, B, C) then snce(alpha, top) ∈ B for all alpha ∈ A.

Proof by contradiction: if snce(alpha, top) ∉ B, then
BurgessR3Maximal_extension_fails gives ¬burgessR3(A, DC({snce(alpha,top)}∪B), C).
But dc_delta_B_burgessR3 fc shows both Until and Since conditions hold, using
left_mono_until_G with G(snce(alpha, top)) ∈ A (derived from alpha ∈ A via BX4 + BX12'). -/
theorem xu_lemma_2_3_since_top (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    {alpha : Formula Atom} (h_alpha : alpha ∈ A) :
    Formula.snce alpha (Formula.bot.imp Formula.bot) ∈ B := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_dcs : ClosedUnderDerivation fc B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Suppose snce(alpha, top) ∉ B, derive contradiction
  by_contra h_not_in_B
  -- Step 1: BurgessR3Maximal_extension_fails gives ¬burgessR3 for extension
  have h_fails := BurgessR3Maximal_extension_fails fc h_r3m h_not_in_B
  -- Step 2: Derive G(snce(alpha, top)) ∈ A from alpha ∈ A
  -- BX4: alpha → G(P(alpha))
  have h_bx4 : DerivationTree fc [] (alpha.imp (alpha.some_past.all_future)) :=
    DerivationTree.axiom [] _ (Axiom.connect_future alpha) trivial
  have h_G_P_alpha : alpha.some_past.all_future ∈ A :=
    SetMaximalConsistent.implication_property h_mcs_A (theorem_in_mcs h_mcs_A h_bx4) h_alpha
  -- BX12': P(alpha) → snce(alpha, top) (theorem)
  have h_bx12' : DerivationTree fc [] (alpha.some_past.imp (Formula.snce alpha top)) :=
    DerivationTree.axiom [] _ (Axiom.P_since_equiv alpha) trivial
  -- G(P(alpha) → snce(alpha, top)) via temporal necessitation
  have h_G_impl : (alpha.some_past.imp (Formula.snce alpha top)).all_future ∈ A :=
    theorem_in_mcs h_mcs_A (DerivationTree.temporal_necessitation _ h_bx12')
  -- G(P(alpha)) → G(snce(alpha, top)) via temporal K distribution
  have h_temp_k :=
    liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived alpha.some_past (Formula.snce alpha top))
  have h_G_snce : (Formula.snce alpha top).all_future ∈ A :=
    SetMaximalConsistent.implication_property h_mcs_A
      (SetMaximalConsistent.implication_property h_mcs_A
        (theorem_in_mcs h_mcs_A h_temp_k) h_G_impl)
      h_G_P_alpha
  -- Step 3: Show both conditions for dc_delta_B_burgessR3
  -- Until condition: ∀ beta ∈ B, ∀ gamma ∈ C, untl(gamma, beta ∧ snce(alpha, top)) ∈ A
  have h_until_all : ∀ beta ∈ B, ∀ gamma ∈ C,
      Formula.untl gamma (Formula.and beta (Formula.snce alpha top)) ∈ A := by
    intro beta h_beta gamma h_gamma
    -- untl(gamma, beta) ∈ A from R3
    have h_untl := h_r3.1 beta h_beta gamma h_gamma
    -- ⊢ snce(alpha,top) → (beta → beta ∧ snce(alpha,top))
    -- From pairing + theorem_flip: flip(pairing) gives snce → beta → beta ∧ snce
    have h_flip : DerivationTree fc []
        ((Formula.snce alpha top).imp (beta.imp (Formula.and beta (Formula.snce alpha top)))) :=
      mp (pairing beta (Formula.snce alpha top)) theorem_flip
    -- G(snce → (beta → beta ∧ snce)) via temporal necessitation
    have h_G_flip := theorem_in_mcs h_mcs_A (DerivationTree.temporal_necessitation _ h_flip)
    -- G(snce) → G(beta → beta ∧ snce) via temporal K distribution
    have h_temp_k2 :=
      liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived (Formula.snce alpha top) (beta.imp (Formula.and beta (Formula.snce alpha top))))
    have h_G_guard_str : (beta.imp (Formula.and beta (Formula.snce alpha top))).all_future ∈ A :=
      SetMaximalConsistent.implication_property h_mcs_A
        (SetMaximalConsistent.implication_property h_mcs_A
          (theorem_in_mcs h_mcs_A h_temp_k2) h_G_flip)
        h_G_snce
    -- left_mono_until_G: G(beta → beta ∧ snce) → untl(gamma, beta) → untl(gamma, beta ∧ snce)
    exact untl_left_mono_G fc h_mcs_A h_G_guard_str h_untl
  -- Since condition: ∀ beta ∈ B, ∀ alpha' ∈ A, snce(alpha', beta ∧ snce(alpha, top)) ∈ C
  -- From burgessR_implies_burgessRSince applied to the Until condition
  have h_since_all : ∀ beta ∈ B, ∀ alpha' ∈ A,
      Formula.snce alpha' (Formula.and beta (Formula.snce alpha top)) ∈ C := by
    intro beta h_beta alpha' h_alpha'
    have h_burgessR : burgessR A (Formula.and beta (Formula.snce alpha top)) C :=
      fun gamma h_gamma => h_until_all beta h_beta gamma h_gamma
    exact burgessR_implies_burgessRSince fc h_mcs_A h_mcs_C h_burgessR alpha' h_alpha'
  -- Step 4: Apply dc_delta_B_burgessR3 to get burgessR3 for extension
  have h_r3_ext := dc_delta_B_burgessR3 fc h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  -- Step 5: Contradiction with BurgessR3Maximal_extension_fails
  exact absurd h_r3_ext h_fails

/-- Xu Lemma 2.3 (ii): If R(A, B, C) then untl(gamma, top) ∈ B for all gamma ∈ C.
Dual of xu_lemma_2_3_since_top: uses BX4' + BX12 + left_mono_since_H
for the Since guard strengthening, and burgessRSince_implies_burgessR fc for the Until direction. -/
theorem xu_lemma_2_3_until_top (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    {gamma : Formula Atom} (h_gamma : gamma ∈ C) :
    Formula.untl gamma (Formula.bot.imp Formula.bot) ∈ B := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_dcs : ClosedUnderDerivation fc B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Suppose untl(gamma, top) ∉ B, derive contradiction
  by_contra h_not_in_B
  have h_fails := BurgessR3Maximal_extension_fails fc h_r3m h_not_in_B
  -- Step 2: Derive H(untl(gamma, top)) ∈ C from gamma ∈ C
  -- BX4': gamma → H(F(gamma))
  have h_bx4' : DerivationTree fc [] (gamma.imp (gamma.some_future.all_past)) :=
    DerivationTree.axiom [] _ (Axiom.connect_past gamma) trivial
  have h_H_F_gamma : gamma.some_future.all_past ∈ C :=
    SetMaximalConsistent.implication_property h_mcs_C (theorem_in_mcs h_mcs_C h_bx4') h_gamma
  -- BX12: F(gamma) → untl(gamma, top) (theorem)
  have h_bx12 : DerivationTree fc [] (gamma.some_future.imp (Formula.untl gamma top)) :=
    DerivationTree.axiom [] _ (Axiom.F_until_equiv gamma) trivial
  -- H(F(gamma) → untl(gamma, top)) via past necessitation
  have h_H_impl : (gamma.some_future.imp (Formula.untl gamma top)).all_past ∈ C :=
    theorem_in_mcs h_mcs_C (Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_bx12)
  -- H(F(gamma)) → H(untl(gamma, top)) via past K distribution
  have h_past_k : DerivationTree fc [] _ := Cslib.Logic.Bimodal.Theorems.past_k_dist gamma.some_future (Formula.untl gamma top)
  have h_H_untl : (Formula.untl gamma top).all_past ∈ C :=
    SetMaximalConsistent.implication_property h_mcs_C
      (SetMaximalConsistent.implication_property h_mcs_C
        (theorem_in_mcs h_mcs_C h_past_k) h_H_impl)
      h_H_F_gamma
  -- Step 3: Since condition: ∀ beta ∈ B, ∀ alpha ∈ A, snce(alpha, beta ∧ untl(gamma, top)) ∈ C
  have h_since_all : ∀ beta ∈ B, ∀ alpha ∈ A,
      Formula.snce alpha (Formula.and beta (Formula.untl gamma top)) ∈ C := by
    intro beta h_beta alpha' h_alpha'
    have h_snce := h_r3.2 beta h_beta alpha' h_alpha'
    -- ⊢ untl(gamma,top) → (beta → beta ∧ untl(gamma,top))
    have h_flip : DerivationTree fc []
        ((Formula.untl gamma top).imp (beta.imp (Formula.and beta (Formula.untl gamma top)))) :=
      mp (pairing beta (Formula.untl gamma top)) theorem_flip
    -- H(untl(gamma,top) → (beta → beta ∧ untl(gamma,top))) via past necessitation
    have h_H_flip := theorem_in_mcs h_mcs_C (Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_flip)
    -- H(untl(gamma,top)) → H(beta → beta ∧ untl(gamma,top)) via past K
    have h_past_k2 : DerivationTree fc [] _ := Cslib.Logic.Bimodal.Theorems.past_k_dist
      (Formula.untl gamma top) (beta.imp (Formula.and beta (Formula.untl gamma top)))
    have h_H_guard_str : (beta.imp (Formula.and beta (Formula.untl gamma top))).all_past ∈ C :=
      SetMaximalConsistent.implication_property h_mcs_C
        (SetMaximalConsistent.implication_property h_mcs_C
          (theorem_in_mcs h_mcs_C h_past_k2) h_H_flip)
        h_H_untl
    -- left_mono_since_H: H(beta → beta ∧ untl) → snce(alpha, beta) → snce(alpha, beta ∧ untl)
    exact snce_left_mono_H fc h_mcs_C h_H_guard_str h_snce
  -- Step 4: Until condition from burgessRSince_implies_burgessR
  have h_until_all : ∀ beta ∈ B, ∀ gamma' ∈ C,
      Formula.untl gamma' (Formula.and beta (Formula.untl gamma top)) ∈ A := by
    intro beta h_beta gamma' h_gamma'
    have h_burgessRSince : burgessRSince C (Formula.and beta (Formula.untl gamma top)) A :=
      fun alpha h_alpha => h_since_all beta h_beta alpha h_alpha
    exact burgessRSince_implies_burgessR fc h_mcs_A h_mcs_C h_burgessRSince gamma' h_gamma'
  -- Step 5: Apply dc_delta_B_burgessR3 and contradiction
  have h_r3_ext := dc_delta_B_burgessR3 fc h_mcs_A h_mcs_C h_dcs h_r3 h_until_all h_since_all
  exact absurd h_r3_ext h_fails

/-! ## Set.univ is ClosedUnderDerivation -/

/-- `Set.univ` is `ClosedUnderDerivation` -- every formula is in `Set.univ`. -/
theorem set_univ_closed_under_derivation (fc : FrameClass) : ClosedUnderDerivation fc (Set.univ : Set (Formula Atom)) :=
  fun _ _ _ _ => Set.mem_univ _

/-! ## Inconsistent case helpers for g_content/h_content ⊆ B

When `{φ} ∪ B` is inconsistent and `G(φ) ∈ A` with `burgessR3(A, B, C)`,
we show `burgessR3(A, Set.univ, C)` using ex-falso propagation through
`left_mono_until_G`. The maximality clause of `BurgessR3Maximal` (now over
`ClosedUnderDerivation`) then gives a contradiction via `Set.univ`.
-/

/-- Helper: `⊢ φ → (φ.neg → ψ)` for any ψ (ex falso from assumption). -/
private noncomputable def ex_falso_from_assumption (fc : FrameClass) (φ ψ : Formula Atom) :
    DerivationTree fc [] (φ.imp (φ.neg.imp ψ)) := by
  -- [φ.neg, φ] ⊢ ⊥ via modus ponens (φ.neg = φ → ⊥)
  have h1 : DerivationTree fc [φ.neg, φ] Formula.bot :=
    DerivationTree.modus_ponens [φ.neg, φ] φ Formula.bot
      (DerivationTree.assumption _ φ.neg (by simp))
      (DerivationTree.assumption _ φ (by simp))
  -- [φ.neg, φ] ⊢ ψ via ex falso
  have h2 : DerivationTree fc [φ.neg, φ] ψ :=
    DerivationTree.modus_ponens [φ.neg, φ] Formula.bot ψ
      (DerivationTree.weakening [] [φ.neg, φ] (Formula.bot.imp ψ)
        (Cslib.Logic.Bimodal.Theorems.Propositional.efq_axiom ψ) (List.nil_subset _))
      h1
  -- Discharge φ.neg then φ: [φ] ⊢ φ.neg → ψ, then [] ⊢ φ → (φ.neg → ψ)
  exact deduction_theorem [] φ _ (deduction_theorem [φ] φ.neg ψ h2)

/-- Helper: G(φ.neg → ψ) ∈ A from G(φ) ∈ A, using ex_falso_from_assumption + TG + temp_k_dist. -/
private theorem G_ex_falso_strengthen (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (φ ψ : Formula Atom)
    (h_Gφ : Formula.all_future φ ∈ A) :
    (φ.neg.imp ψ).all_future ∈ A := by
  have d_ef := ex_falso_from_assumption fc φ ψ
  exact SetMaximalConsistent.implication_property h_mcs_A
    (SetMaximalConsistent.implication_property h_mcs_A
      (theorem_in_mcs h_mcs_A (liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived φ (φ.neg.imp ψ))))
      (theorem_in_mcs h_mcs_A (DerivationTree.temporal_necessitation _ d_ef)))
    h_Gφ

/-- Helper: H(ψ.neg → χ) ∈ C from H(ψ) ∈ C, using ex_falso_from_assumption + past_necessitation + past_k_dist. -/
private theorem H_ex_falso_strengthen (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs_C : SetMaximalConsistent fc C) (ψ χ : Formula Atom)
    (h_Hψ : Formula.all_past ψ ∈ C) :
    (ψ.neg.imp χ).all_past ∈ C := by
  have d_ef := ex_falso_from_assumption fc ψ χ
  exact SetMaximalConsistent.implication_property h_mcs_C
    (SetMaximalConsistent.implication_property h_mcs_C
      (theorem_in_mcs h_mcs_C (Cslib.Logic.Bimodal.Theorems.past_k_dist ψ (ψ.neg.imp χ)))
      (theorem_in_mcs h_mcs_C (Cslib.Logic.Bimodal.Theorems.past_necessitation _ d_ef)))
    h_Hψ

/-- When {φ} ∪ B is inconsistent with DCS B, we have φ.neg ∈ B.
Proof: ¬SetConsistent means ∃ derivation of ⊥ from {φ} ∪ B.
By deduction theorem: derivation of φ.neg from B. By closure: φ.neg ∈ B. -/
private theorem neg_mem_of_inconsistent_union (fc : FrameClass) {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation fc B)
    {φ : Formula Atom} (h_not_cons : ¬SetConsistent fc ({φ} ∪ B)) :
    φ.neg ∈ B := by
  -- ¬SetConsistent means ∃ L ⊆ {φ} ∪ B with Nonempty (DerivationTree fc L ⊥)
  -- SetConsistent S = ∀ L, (∀ ψ ∈ L, ψ ∈ S) → ¬Nonempty (DerivationTree fc L ⊥)
  -- Use classical logic to extract witness
  by_contra h_neg_not_B
  apply h_not_cons
  -- If φ.neg ∉ B, then {φ.neg.neg} ∪ B would extend B... Actually, use dcs_neg_union_consistent
  -- The contrapositive: if {φ} ∪ B is inconsistent, then φ ∉ B (already known) and φ.neg ∈ B.
  -- We prove: if φ.neg ∉ B, then {φ} ∪ B IS consistent.
  -- Since B is DCS and φ.neg ∉ B, by dcs_neg_union_consistent: {φ.neg.neg} ∪ B is consistent.
  -- And φ.neg.neg → φ (double negation elimination), so {φ} ∪ B ⊆ DC({φ.neg.neg} ∪ B).
  -- Any subset of a consistent set is consistent.
  -- Actually, we can be more direct: if φ.neg ∉ B and B is DCS, then for any L ⊆ {φ} ∪ B,
  -- if we had DerivationTree fc L ⊥, we could derive φ.neg from B (contradiction).
  intro L hL ⟨d⟩
  -- L ⊆ {φ} ∪ B and DerivationTree fc L ⊥.
  -- Partition L: separate φ occurrences from B elements.
  set M := L.filter (fun x => !decide (x = φ)) with hM_def
  have hM_sub_B : ∀ ψ ∈ M, ψ ∈ B := by
    intro ψ hψ; rw [hM_def] at hψ
    have h_mem := List.mem_filter.mp hψ
    have h1 : ψ ∈ L := h_mem.1
    have h2 : ψ ≠ φ := by simp at h_mem; exact h_mem.2
    rcases hL ψ h1 with h | h
    · exact absurd (Set.mem_singleton_iff.mp h) h2
    · exact h
  have hL_sub_φM : L ⊆ φ :: M := by
    intro x hx
    by_cases heq : x = φ
    · subst heq; exact .head M
    · exact .tail _ (List.mem_filter.mpr ⟨hx, by simp; exact heq⟩)
  have d_w : DerivationTree fc (φ :: M) Formula.bot :=
    DerivationTree.weakening L (φ :: M) Formula.bot d hL_sub_φM
  -- By deduction theorem: M ⊢ φ → ⊥ = φ.neg
  have d_neg : DerivationTree fc M φ.neg := deduction_theorem M φ Formula.bot d_w
  -- By DCS closure: φ.neg ∈ B — contradiction
  exact h_neg_not_B (h_cud M φ.neg hM_sub_B d_neg)

/-- **Unified interface**: Given BurgessR3Maximal(A, B, C) and delta ∉ B,
EITHER delta.neg ∈ B (when {delta}∪B is inconsistent)
OR ¬burgessR3(A, DC({delta}∪B), C).

The second disjunct always holds (BurgessR3Maximal_extension_fails). The first
disjunct holds additionally when {delta}∪B is inconsistent. -/
theorem BurgessR3Maximal_neg_or_ext_fails (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_R3M : BurgessR3Maximal fc A B C)
    {delta : Formula Atom} (h_delta_not : delta ∉ B) :
    delta.neg ∈ B ∨ ¬burgessR3 A (deductiveClosure fc ({delta} ∪ B)) C := by
  by_cases h_cons : SetConsistent fc ({delta} ∪ B)
  · exact Or.inr (BurgessR3Maximal_extension_fails fc h_R3M h_delta_not)
  · exact Or.inl (neg_mem_of_inconsistent_union fc h_R3M.1 h_cons)


/-- When {φ} ∪ B is inconsistent, φ.neg ∈ B, G(φ) ∈ A, and burgessR3(A, B, C),
then burgessR3(A, Set.univ, C). The argument: from φ.neg ∈ B and G(φ) ∈ A,
for any ψ: G(φ.neg → ψ) ∈ A (ex falso), then untl_left_mono_G fc gives
untl(ψ, γ) ∈ A from untl(φ.neg, γ) ∈ A. This gives burgessRSet for Set.univ.
burgessR_implies_burgessRSince fc gives the Since direction. -/
private theorem burgessR3_univ_of_inconsistent_ext (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3 : burgessR3 A B C)
    {φ : Formula Atom} (h_Gφ : Formula.all_future φ ∈ A)
    (h_neg_in_B : φ.neg ∈ B) :
    burgessR3 A Set.univ C := by
  constructor
  · -- burgessRSet(A, Set.univ, C): for any ψ ∈ Set.univ, for any γ ∈ C, untl(ψ, γ) ∈ A
    intro ψ _ γ hγ
    -- untl(φ.neg, γ) ∈ A from burgessR3(A, B, C) and φ.neg ∈ B
    have h_untl_neg := h_r3.1 φ.neg h_neg_in_B γ hγ
    -- G(φ.neg → ψ) ∈ A from G(φ) ∈ A
    have h_G_impl := G_ex_falso_strengthen fc h_mcs_A φ ψ h_Gφ
    -- untl_left_mono_G: G(φ.neg → ψ) and untl(φ.neg, γ) give untl(ψ, γ)
    exact untl_left_mono_G fc h_mcs_A h_G_impl h_untl_neg
  · -- burgessRSetSince(C, Set.univ, A): for any ψ ∈ Set.univ, for any α ∈ A, snce(ψ, α) ∈ C
    intro ψ _ α hα
    -- burgessR(A, ψ, C) from the Until direction above
    have h_burgessR : burgessR A ψ C := fun γ hγ => by
      have h_untl_neg := h_r3.1 φ.neg h_neg_in_B γ hγ
      have h_G_impl := G_ex_falso_strengthen fc h_mcs_A φ ψ h_Gφ
      exact untl_left_mono_G fc h_mcs_A h_G_impl h_untl_neg
    -- burgessR_implies_burgessRSince gives snce(ψ, α) ∈ C
    exact burgessR_implies_burgessRSince fc h_mcs_A h_mcs_C h_burgessR α hα

/-! ## g_content(A) ⊆ B from BurgessR3Maximal

Given `BurgessR3Maximal(A, B, C)` with A, C MCS and g_content(A) ⊆ C,
every φ ∈ g_content(A) (i.e., G(φ) ∈ A) must also be in B.

**Proof** (Report 47, task 107 Phase 5b v31, corrected v32):
- **Consistent case** ({φ}∪B consistent): `dc_delta_B_burgessR3` shows
  burgessR3(A, DC({φ}∪B), C) using left_mono_until_G/since_H. But
  `BurgessR3Maximal_extension_fails` gives ¬burgessR3. Contradiction.
- **Inconsistent case** ({φ}∪B inconsistent): φ.neg ∈ B (by DCS closure).
  `burgessR3_univ_of_inconsistent_ext` gives burgessR3(A, Set.univ, C).
  Set.univ is ClosedUnderDerivation. B ⊂ Set.univ (B is consistent).
  BurgessR3Maximal maximality (over ClosedUnderDerivation) gives contradiction.
-/

/-- Helper: ⊢ φ → (β → (β ∧ φ)). Conjunction introduction curried. -/
private noncomputable def conj_intro_curried (fc : FrameClass) (β φ : Formula Atom) :
    DerivationTree fc [] (φ.imp (β.imp (Formula.and β φ))) := by
  have h1 : DerivationTree fc [β, φ] (Formula.and β φ) :=
    DerivationTree.modus_ponens [β, φ] _ _
      (DerivationTree.modus_ponens [β, φ] β _
        (DerivationTree.weakening [] [β, φ] _
          (pairing β φ) (List.nil_subset _))
        (DerivationTree.assumption _ β (by simp)))
      (DerivationTree.assumption _ φ (by simp))
  exact deduction_theorem [] φ _ (deduction_theorem [φ] β _ h1)

/-! ## Duality: h_content(C) ⊆ D implies g_content(D) ⊆ C

Local proof of the duality theorem needed for Lemma 2.6 splitting.
(The canonical version lives in ChronicleConstruction.lean which imports
this file, so we reproduce it here to avoid circular imports.)
-/

/-- h_content(B) ⊆ A implies g_content(A) ⊆ B for MCS A, B.
Proof: Suppose G(ψ) ∈ A and ψ ∉ B. Then ¬ψ ∈ B (MCS). By BX4' (connect_past):
¬ψ → H(F(¬ψ)), so H(F(¬ψ)) ∈ B, hence F(¬ψ) ∈ h_content(B) ⊆ A.
But F(¬ψ) = ¬G(ψ^{nn}), so G(ψ^{nn}) ∉ A. Yet G(ψ) → G(ψ^{nn}) by DNI
+ temporal necessitation + K distribution, contradiction. -/
private theorem h_content_sub_imp_g_content_sub' (fc : FrameClass) {A B : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_B : SetMaximalConsistent fc B)
    (h_hBA : h_content B ⊆ A) :
    g_content A ⊆ B := by
  intro ψ hψ
  by_contra h_not
  have h_neg_ψ : ψ.neg ∈ B := by
    rcases SetMaximalConsistent.negation_complete h_mcs_B ψ with h | h
    · exact absurd h h_not
    · exact h
  have h_ax : DerivationTree fc [] (ψ.neg.imp (ψ.neg.some_future.all_past)) :=
    DerivationTree.axiom [] _ (Axiom.connect_past ψ.neg) trivial
  have h_HF : Formula.all_past (Formula.some_future ψ.neg) ∈ B :=
    SetMaximalConsistent.implication_property h_mcs_B
      (theorem_in_mcs h_mcs_B h_ax) h_neg_ψ
  have h_F_neg_ψ_A : Formula.some_future ψ.neg ∈ A := h_hBA h_HF
  -- G(¬¬ψ) ∈ A from G(ψ) via DNI under G
  have h_dni : DerivationTree fc [] (ψ.imp ψ.neg.neg) :=
    Cslib.Logic.Bimodal.Theorems.Combinators.dni ψ
  have h_G_dni : DerivationTree fc [] (Formula.all_future (ψ.imp ψ.neg.neg)) :=
    DerivationTree.temporal_necessitation _ h_dni
  have h_G_dist : DerivationTree fc [] ((Formula.all_future (ψ.imp ψ.neg.neg)).imp
      (Formula.all_future ψ |>.imp (Formula.all_future ψ.neg.neg))) :=
    liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived ψ ψ.neg.neg)
  have h_G_nn : Formula.all_future ψ.neg.neg ∈ A := by
    have h1 := theorem_in_mcs h_mcs_A h_G_dni
    have h2 := theorem_in_mcs h_mcs_A h_G_dist
    have h3 := SetMaximalConsistent.implication_property h_mcs_A h2 h1
    exact SetMaximalConsistent.implication_property h_mcs_A h3 hψ
  -- F(¬ψ) and G(¬¬ψ) = G(neg(ψ.neg)) are contradictory
  exact some_future_all_future_neg_absurd h_mcs_A ψ.neg h_F_neg_ψ_A h_G_nn

/-- g_content(A) ⊆ B implies h_content(B) ⊆ A for MCS A, B. Dual of above. -/
private theorem g_content_sub_imp_h_content_sub' (fc : FrameClass) {A B : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_B : SetMaximalConsistent fc B)
    (h_gAB : g_content A ⊆ B) :
    h_content B ⊆ A := by
  intro ψ hψ
  by_contra h_not
  have h_neg_ψ : ψ.neg ∈ A := by
    rcases SetMaximalConsistent.negation_complete h_mcs_A ψ with h | h
    · exact absurd h h_not
    · exact h
  have h_GP : Formula.all_future (Formula.some_past ψ.neg) ∈ A :=
    connect_future_mcs fc h_mcs_A ψ.neg h_neg_ψ
  have h_P_neg_ψ_B : Formula.some_past ψ.neg ∈ B := h_gAB h_GP
  -- H(¬¬ψ) ∈ B from H(ψ) via DNI under H
  have h_dni : DerivationTree fc [] (ψ.imp ψ.neg.neg) :=
    Cslib.Logic.Bimodal.Theorems.Combinators.dni ψ
  have h_H_dni : DerivationTree fc [] (Formula.all_past (ψ.imp ψ.neg.neg)) :=
    Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_dni
  have h_H_dist : DerivationTree fc [] ((Formula.all_past (ψ.imp ψ.neg.neg)).imp
      (Formula.all_past ψ |>.imp (Formula.all_past ψ.neg.neg))) :=
    Cslib.Logic.Bimodal.Theorems.past_k_dist ψ ψ.neg.neg
  have h_H_nn : Formula.all_past ψ.neg.neg ∈ B := by
    have h1 := theorem_in_mcs h_mcs_B h_H_dni
    have h2 := theorem_in_mcs h_mcs_B h_H_dist
    have h3 := SetMaximalConsistent.implication_property h_mcs_B h2 h1
    exact SetMaximalConsistent.implication_property h_mcs_B h3 hψ
  exact some_past_all_past_neg_absurd h_mcs_B ψ.neg h_P_neg_ψ_B h_H_nn

/-! ## Lemma 2.6 Splitting: BurgessR3Maximal Interval Insertion

Given `BurgessR3Maximal(A, B, C)` with `β ∉ B` and `g_content(A) ⊆ C`,
produce MCS D with `¬β ∈ D` and `BurgessR3Maximal(A, B', D)` and
`BurgessR3Maximal(D, B'', C)`.

## Burgess D₀ Seed Construction (Burgess 1982, p.370)

The original Burgess (1982) approach used a rich D₀ seed with explicit Until/Since
formulas, requiring BX14 (separation_until) for consistency. Task 115 replaced this
with the Xu 1988 Lemma 3.2.2 approach: the seed is simply B* ∪ {β.neg}, with
consistency following trivially from `dcs_neg_union_consistent`. The Until/Since
formulas needed for r(A, B*, D) are already in B* via Xu 3.2.1. -/

/-! ## Lemma 2.7: Until-Formula Splitting (Burgess 1982)

Lemma 2.7 (Until-formula splitting): given `BurgessR3Maximal(A, B, C)` with
`U(xi, eta) ∈ A` and `eta ∉ B`, produce `B', D, B''` with:
- `BurgessR3Maximal(A, B', D)`
- `BurgessR3Maximal(D, B'', C)`
- `xi ∈ D` and `eta ∈ B'`

## Proof Strategy (Burgess 1982, direct seed)

From `eta ∉ B` and maximality of B: `BurgessR3Maximal_extension_fails` gives
`¬burgessR3(A, DC({eta}∪B), C)` (when {eta}∪B consistent). This means some
formula `phi ∈ DC({eta}∪B)` with some `gamma ∈ C` has `¬U(phi, gamma) ∈ A`.
By `dc_delta_B_controlled`, either `phi ∈ B` (impossible since burgessR3(A,B,C)
holds) or there exists `beta₀ ∈ B` with `⊢ (beta₀∧eta) → phi`.

So we obtain `beta₀ ∈ B`, `gamma₀ ∈ C` with `¬U(beta₀∧eta, gamma₀) ∈ A`.

**Core BX5+BX7+BX13 chain** (adapted from Burgess 1982 p. 371):

1. BX5 on `U(xi, eta)`: get `U(xi∧U(xi,eta), eta) ∈ A`
2. BX5 on `U(beta₀, gamma₀)` (from burgessR3): get `U(beta₀∧U(beta₀,gamma₀), gamma₀) ∈ A`
3. BX7 on these two enriched Until formulas → three-way disjunction D1∨D2∨D3
4. Eliminate D1 and D2 using `¬U(beta₀∧eta, gamma₀) ∈ A` + left_mono_until_G
5. D3 survives: `U(phi₁∧phi₂, phi₁∧gamma₀) ∈ A` where phi₁ = xi∧U(xi,eta)
6. BX10 gives F(phi₁∧gamma₀) ∈ A, so `{phi₁∧gamma₀} ∪ g_content(A) ∪ h_content(C)` consistent
7. Lindenbaum → MCS D with `xi ∈ D`, `g_content(A) ⊆ D`, `g_content(D) ⊆ C`
8. `BurgessR3Maximal(A, B', D)` and `BurgessR3Maximal(D, B'', C)` from g_content
9. `eta ∈ B'` from `U(xi, beta∧eta) ∈ A` for all beta ∈ B, plus maximality
-/

/-- Helper: BX3 (right_mono_until) at MCS level. If ⊢ ψ → χ and
U(φ, ψ) ∈ A, then U(φ, χ) ∈ A. -/
private theorem right_mono_until_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {φ ψ χ : Formula Atom}
    (h_impl : DerivationTree fc [] (ψ.imp χ))
    (h_untl : Formula.untl ψ φ ∈ A) :
    Formula.untl χ φ ∈ A := by
  -- G(ψ → χ) ∈ A from temporal necessitation
  have h_G_impl : Formula.all_future (ψ.imp χ) ∈ A :=
    theorem_in_mcs h_mcs (DerivationTree.temporal_necessitation _ h_impl)
  -- BX3: G(ψ → χ) → U(φ, ψ) → U(φ, χ)
  have h_bx3 := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until ψ χ φ) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs h_mcs h_bx3) h_G_impl) h_untl

/-- Right monotonicity for Since at MCS level: if ⊢ ψ→χ and S(φ,ψ) ∈ C, then S(φ,χ) ∈ C. -/
private theorem right_mono_since_mcs (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C) {φ ψ χ : Formula Atom}
    (h_impl : DerivationTree fc [] (ψ.imp χ))
    (h_snce : Formula.snce ψ φ ∈ C) :
    Formula.snce χ φ ∈ C := by
  have h_H_impl : Formula.all_past (ψ.imp χ) ∈ C :=
    theorem_in_mcs h_mcs (Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_impl)
  have h_bx3' := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since ψ χ φ) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs h_mcs h_bx3') h_H_impl) h_snce

/-! ## Lemma 2.7 Helpers and Implementation -/

/-- BX13 (enrichment_until) at MCS level: If p ∈ A and untl(phi, psi) ∈ A,
then untl(phi, psi ∧ snce(phi, p)) ∈ A. -/
private theorem enrichment_until_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {phi psi p : Formula Atom}
    (h_p : p ∈ A)
    (h_untl : Formula.untl psi phi ∈ A) :
    Formula.untl (Formula.and psi (Formula.snce p phi)) phi ∈ A := by
  have h_conj := conj_mcs fc h_mcs p (Formula.untl psi phi) h_p h_untl
  have h_bx13 := DerivationTree.axiom (fc := fc) [] _ (Axiom.enrichment_until phi psi p) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs h_bx13) h_conj

/-- BX10 (until_F) at MCS level: If untl(phi, psi) ∈ A, then F(psi) ∈ A.
Alias for `until_F_mcs` for local use. -/
private theorem until_implies_F_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {phi psi : Formula Atom}
    (h_untl : Formula.untl psi phi ∈ A) :
    Formula.some_future psi ∈ A :=
  until_F_mcs fc h_mcs phi psi h_untl

/-- F-monotonicity at MCS level: If ⊢ phi → psi and F(phi) ∈ A, then F(psi) ∈ A.
F(phi) = ¬G(¬phi). From ⊢ phi → psi we get ⊢ ¬psi → ¬phi, then G(¬psi) → G(¬phi),
so ¬G(¬phi) → ¬G(¬psi), i.e., F(phi) → F(psi). -/
private theorem F_mono_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {phi psi : Formula Atom}
    (h_impl : DerivationTree fc [] (phi.imp psi))
    (h_F : Formula.some_future phi ∈ A) :
    Formula.some_future psi ∈ A := by
  -- F(phi) = ¬G(¬phi). Suppose G(¬psi) ∈ A for contradiction.
  by_contra h_not_F
  -- ¬F(psi) ∈ A, derive G(¬psi) ∈ A via duality bridge
  have h_neg_F : (Formula.some_future psi).neg ∈ A :=
    (SetMaximalConsistent.negation_complete h_mcs _).resolve_left h_not_F
  have h_G_neg_psi : Formula.all_future psi.neg ∈ A :=
    neg_some_future_to_all_future_neg h_mcs psi h_neg_F
  -- From ⊢ phi → psi: ⊢ ¬psi → ¬phi (contrapositive)
  -- G(¬psi → ¬phi) is a theorem
  -- G(¬psi) → G(¬phi) by K-distribution
  have h_contra : DerivationTree fc [] (psi.neg.imp phi.neg) := by
    have h1 : DerivationTree fc [phi, psi.neg] psi :=
      DerivationTree.modus_ponens _ _ _
        (DerivationTree.weakening [] _ _ h_impl (List.nil_subset _))
        (DerivationTree.assumption _ phi (by simp))
    have h2 : DerivationTree fc [phi, psi.neg] Formula.bot :=
      DerivationTree.modus_ponens _ _ _
        (DerivationTree.assumption _ psi.neg (by simp)) h1
    have h3 := deduction_theorem [psi.neg] phi Formula.bot h2
    exact deduction_theorem [] psi.neg phi.neg h3
  have h_G_contra := theorem_in_mcs h_mcs
    (DerivationTree.temporal_necessitation _ h_contra)
  have h_kd := theorem_in_mcs h_mcs
    (liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived psi.neg phi.neg))
  have h_G_neg_phi : Formula.all_future phi.neg ∈ A :=
    SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h_kd h_G_contra) h_G_neg_psi
  -- F(phi) and G(¬phi) are contradictory in MCS A
  exact some_future_all_future_neg_absurd h_mcs phi h_F h_G_neg_phi

/-- Helper: ⊢ (a ∧ b) → a (left conjunction elimination). -/
private noncomputable def and_left_impl (fc : FrameClass) (a b : Formula Atom) :
    DerivationTree fc [] ((Formula.and a b).imp a) :=
  lce_imp a b

/-- Helper: ⊢ (a ∧ b) → b (right conjunction elimination). -/
private noncomputable def and_right_impl (fc : FrameClass) (a b : Formula Atom) :
    DerivationTree fc [] ((Formula.and a b).imp b) :=
  rce_imp a b

/-- **List-level cut** (derivation from implied context):
If Γ ⊢ φ for each φ ∈ L, and L ⊢ ψ, then Γ ⊢ ψ.

This is the substitution principle: we can replace assumptions in L
with their derivations from Γ. Proved by induction on L. -/
private noncomputable def derivation_from_implied (fc : FrameClass) (Γ : Context Atom) :
    (L : Context Atom) → (ψ : Formula Atom) →
    (∀ φ ∈ L, DerivationTree fc Γ φ) →
    DerivationTree fc L ψ →
    DerivationTree fc Γ ψ
  | [], ψ, _, d => DerivationTree.weakening [] Γ ψ d (List.nil_subset Γ)
  | l :: L', ψ, h_derives, d => by
    -- Apply deduction theorem to remove l from the head
    have d_impl : DerivationTree fc L' (l.imp ψ) := deduction_theorem L' l ψ d
    -- Recursively derive l.imp ψ from Γ
    have h_derives' : ∀ φ ∈ L', DerivationTree fc Γ φ := fun φ hφ =>
      h_derives φ (List.mem_cons.mpr (Or.inr hφ))
    have d_impl_Γ : DerivationTree fc Γ (l.imp ψ) :=
      derivation_from_implied fc Γ L' (l.imp ψ) h_derives' d_impl
    -- Derive l from Γ
    have d_l : DerivationTree fc Γ l := h_derives l (List.mem_cons.mpr (Or.inl rfl))
    -- Apply modus ponens: Γ ⊢ l.imp ψ and Γ ⊢ l gives Γ ⊢ ψ
    exact DerivationTree.modus_ponens Γ l ψ d_impl_Γ d_l

/-- Corollary: If a set S implies each element of L (i.e., for each φ∈L
there exist premises in S deriving φ), and L ⊢ ⊥, then S is inconsistent.
Contrapositive: if S is consistent, then no L derived from S can derive ⊥,
hence the set of formulas implied by S is consistent. -/
private theorem inconsistent_from_implied (fc : FrameClass) {Sig : Set (Formula Atom)}
    (h_cons : SetConsistent fc Sig)
    (L : List (Formula Atom)) (hL : ∀ φ ∈ L, φ ∈ Sig)
    (d : Nonempty (DerivationTree fc L Formula.bot)) : False :=
  h_cons L hL d

/-! ### List Conjunction and Helpers for Burgess Compression

These helpers support the Burgess compression argument: given a finite
subset L of a seed D₀, we compress it into a single conjunction and
show that conjunction is consistent via the BX chain. -/

/-- Conjunction of a list of formulas. Empty list gives ⊤ (= ⊥→⊥). -/
private noncomputable def list_conj (fc : FrameClass) : List (Formula Atom) → Formula Atom
  | [] => Formula.bot.imp Formula.bot  -- top
  | [φ] => φ
  | (φ :: rest) => Formula.and φ (list_conj fc rest)

/-- ⊢ list_conj L → φ for each φ ∈ L. -/
private noncomputable def list_conj_implies_elem (fc : FrameClass) :
    (L : List (Formula Atom)) → (φ : Formula Atom) → (h : φ ∈ L) →
    DerivationTree fc [] ((list_conj fc L).imp φ)
  | [ψ], φ, h => by
    simp [List.mem_singleton] at h
    subst h; simp [list_conj]; exact identity φ
  | (ψ₁ :: ψ₂ :: rest), φ, h => by
    simp [list_conj]
    -- Cannot use rcases on Or into Type; use decidable equality instead
    by_cases h_eq : φ = ψ₁
    · -- φ = ψ₁: extract left component of ψ₁ ∧ list_conj(ψ₂::rest)
      subst h_eq; exact lce_imp φ (list_conj fc (ψ₂ :: rest))
    · -- φ ∈ ψ₂ :: rest: extract right component, then recurse
      have h' : φ ∈ ψ₂ :: rest := by
        rcases List.mem_cons.mp h with rfl | h'
        · exact absurd rfl h_eq
        · exact h'
      have h_right : DerivationTree fc [] _ := rce_imp ψ₁ (list_conj fc (ψ₂ :: rest))
      have h_rec := list_conj_implies_elem fc (ψ₂ :: rest) φ h'
      exact imp_trans h_right h_rec

/-- If B is DCS and all elements of L are in B, then list_conj L ∈ B. -/
private theorem list_conj_mem_dcs (fc : FrameClass) {B : Set (Formula Atom)} (h_dcs : ClosedUnderDerivation fc B) :
    (L : List (Formula Atom)) → (h : ∀ φ ∈ L, φ ∈ B) → list_conj fc L ∈ B
  | [], _ => cud_contains_theorems h_dcs (identity (Formula.bot : Formula Atom))
  | [φ], h => by simp [list_conj]; exact h φ (List.mem_singleton.mpr rfl)
  | (φ₁ :: φ₂ :: rest), h => by
    simp [list_conj]
    have h1 : φ₁ ∈ B := h φ₁ (List.mem_cons.mpr (Or.inl rfl))
    have h2 : list_conj fc (φ₂ :: rest) ∈ B :=
      list_conj_mem_dcs fc h_dcs (φ₂ :: rest) (fun ψ hψ =>
        h ψ (List.mem_cons.mpr (Or.inr hψ)))
    exact cud_conj_closed h_dcs h1 h2

/-- If A is MCS and all elements of L are in A, then list_conj L ∈ A. -/
private theorem list_conj_mem_mcs (fc : FrameClass) {A : Set (Formula Atom)} (h_mcs : SetMaximalConsistent fc A) :
    (L : List (Formula Atom)) → (h : ∀ φ ∈ L, φ ∈ A) → list_conj fc L ∈ A
  | [], _ => theorem_in_mcs h_mcs (identity (Formula.bot : Formula Atom))
  | [φ], h => by simp [list_conj]; exact h φ (List.mem_singleton.mpr rfl)
  | (φ₁ :: φ₂ :: rest), h => by
    simp [list_conj]
    have h1 : φ₁ ∈ A := h φ₁ (List.mem_cons.mpr (Or.inl rfl))
    have h2 : list_conj fc (φ₂ :: rest) ∈ A :=
      list_conj_mem_mcs fc h_mcs (φ₂ :: rest) (fun ψ hψ =>
        h ψ (List.mem_cons.mpr (Or.inr hψ)))
    exact conj_mcs fc h_mcs φ₁ (list_conj fc (φ₂ :: rest)) h1 h2

/-- If F(φ)∈A (MCS), then {φ} is consistent. -/
private theorem consistent_of_F_mem (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    (φ : Formula Atom) (h_F : Formula.some_future φ ∈ A) :
    SetConsistent fc ({φ} : Set (Formula Atom)) := by
  -- {φ} ⊆ {φ} ∪ g_content(A), and the latter is consistent
  have h_seed := forward_temporal_witness_seed_consistent A h_mcs φ h_F
  exact SetConsistent_of_subset (Set.subset_union_left) h_seed

/-- If {φ} is consistent and [φ] ⊢ ⊥, then False. -/
private theorem inconsistent_singleton_false (fc : FrameClass) {φ : Formula Atom}
    (h_cons : SetConsistent fc ({φ} : Set (Formula Atom)))
    (d : DerivationTree fc [φ] Formula.bot) : False :=
  h_cons [φ] (fun ψ hψ => by simp [List.mem_singleton] at hψ; subst hψ; exact Set.mem_singleton _) ⟨d⟩


/-- Derivation-level left_mono for Until: if ⊢ φ→χ then ⊢ untl(φ,ψ) → untl(χ,ψ).
Uses BX2G (left_mono_until_G): G(φ→χ) → untl(φ,ψ) → untl(χ,ψ). -/
private noncomputable def untl_left_mono_deriv (fc : FrameClass) (φ ψ χ : Formula Atom)
    (h_impl : DerivationTree fc [] (φ.imp χ)) :
    DerivationTree fc [] ((Formula.untl ψ φ).imp (Formula.untl ψ χ)) := by
  have h_G := DerivationTree.temporal_necessitation _ h_impl
  have h_ax := DerivationTree.axiom (fc := fc) [] _ (Axiom.left_mono_until_G φ χ ψ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_G

/-- Derivation-level left_mono for Since: if ⊢ φ→χ then ⊢ snce(φ,ψ) → snce(χ,ψ).
Uses BX2H (left_mono_since_H): H(φ→χ) → snce(φ,ψ) → snce(χ,ψ). -/
private noncomputable def snce_left_mono_deriv (fc : FrameClass) (φ ψ χ : Formula Atom)
    (h_impl : DerivationTree fc [] (φ.imp χ)) :
    DerivationTree fc [] ((Formula.snce ψ φ).imp (Formula.snce ψ χ)) := by
  have h_H := Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_impl
  have h_ax := DerivationTree.axiom (fc := fc) [] _ (Axiom.left_mono_since_H φ χ ψ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_H

/-- Derivation-level right_mono for Until: if ⊢ φ→ψ then ⊢ untl(χ,φ) → untl(χ,ψ).
Uses BX3 (right_mono_until): G(φ→ψ) → untl(χ,φ) → untl(χ,ψ). -/
private noncomputable def untl_right_mono_deriv (fc : FrameClass) (φ ψ χ : Formula Atom)
    (h_impl : DerivationTree fc [] (φ.imp ψ)) :
    DerivationTree fc [] ((Formula.untl φ χ).imp (Formula.untl ψ χ)) := by
  have h_G := DerivationTree.temporal_necessitation _ h_impl
  have h_ax := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until φ ψ χ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_G

/-- Derivation-level right_mono for Since: if ⊢ φ→ψ then ⊢ snce(χ,φ) → snce(χ,ψ).
Uses BX3' (right_mono_since): H(φ→ψ) → snce(χ,φ) → snce(χ,ψ). -/
private noncomputable def snce_right_mono_deriv (fc : FrameClass) (φ ψ χ : Formula Atom)
    (h_impl : DerivationTree fc [] (φ.imp ψ)) :
    DerivationTree fc [] ((Formula.snce φ χ).imp (Formula.snce ψ χ)) := by
  have h_H := Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_impl
  have h_ax := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since φ ψ χ) trivial
  exact DerivationTree.modus_ponens [] _ _ h_ax h_H

/-- BX13' (enrichment_since) at MCS level: If p ∈ C and snce(phi, psi) ∈ C,
then snce(phi, psi ∧ untl(phi, p)) ∈ C. -/
private theorem enrichment_since_mcs (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C) {phi psi p : Formula Atom}
    (h_p : p ∈ C)
    (h_snce : Formula.snce psi phi ∈ C) :
    Formula.snce (Formula.and psi (Formula.untl p phi)) phi ∈ C := by
  have h_conj := conj_mcs fc h_mcs p (Formula.snce psi phi) h_p h_snce
  have h_bx13 := DerivationTree.axiom (fc := fc) [] _ (Axiom.enrichment_since phi psi p) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs h_mcs h_bx13) h_conj

/-- BX10' (since_P) at MCS level: If snce(phi, psi) ∈ C, then P(psi) ∈ C. -/
private theorem since_implies_P_mcs (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C) {phi psi : Formula Atom}
    (h_snce : Formula.snce psi phi ∈ C) :
    Formula.some_past psi ∈ C :=
  since_implies_P_in_mcs fc h_mcs h_snce

/-- If P(φ)∈C (MCS), then {φ} is consistent. -/
private theorem consistent_of_P_mem (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C)
    (φ : Formula Atom) (h_P : Formula.some_past φ ∈ C) :
    SetConsistent fc ({φ} : Set (Formula Atom)) := by
  have h_seed := past_temporal_witness_seed_consistent C h_mcs φ h_P
  exact SetConsistent_of_subset (Set.subset_union_left) h_seed

/-- P-monotonicity at MCS level: If ⊢ phi → psi and P(phi) ∈ C, then P(psi) ∈ C.
Mirror of F_mono_mcs fc using H instead of G. -/
private theorem P_mono_mcs (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C) {phi psi : Formula Atom}
    (h_impl : DerivationTree fc [] (phi.imp psi))
    (h_P : Formula.some_past phi ∈ C) :
    Formula.some_past psi ∈ C := by
  by_contra h_not_P
  have h_neg_P : (Formula.some_past psi).neg ∈ C :=
    (SetMaximalConsistent.negation_complete h_mcs _).resolve_left h_not_P
  have h_H_neg_psi : Formula.all_past psi.neg ∈ C :=
    neg_some_past_to_all_past_neg h_mcs psi h_neg_P
  have h_contra : DerivationTree fc [] (psi.neg.imp phi.neg) := by
    have h1 : DerivationTree fc [phi, psi.neg] psi :=
      DerivationTree.modus_ponens _ _ _
        (DerivationTree.weakening [] _ _ h_impl (List.nil_subset _))
        (DerivationTree.assumption _ phi (by simp))
    have h2 : DerivationTree fc [phi, psi.neg] Formula.bot :=
      DerivationTree.modus_ponens _ _ _
        (DerivationTree.assumption _ psi.neg (by simp)) h1
    have h3 := deduction_theorem [psi.neg] phi Formula.bot h2
    exact deduction_theorem [] psi.neg phi.neg h3
  have h_H_contra := theorem_in_mcs h_mcs
    (Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_contra)
  have h_kd := theorem_in_mcs h_mcs
    (Cslib.Logic.Bimodal.Theorems.past_k_dist psi.neg phi.neg)
  have h_H_neg_phi : Formula.all_past phi.neg ∈ C :=
    SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h_kd h_H_contra) h_H_neg_psi
  exact some_past_all_past_neg_absurd h_mcs phi h_P h_H_neg_phi

/-- Structure to hold the result of iterated BX13 enrichment. -/
structure EnrichedEvent (fc : FrameClass) (A : Set (Formula Atom)) (guard event : Formula Atom) (alphas : List (Formula Atom)) where
  event' : Formula Atom
  h_untl : Formula.untl event' guard ∈ A
  h_impl : DerivationTree fc [] (event'.imp event)
  h_snce : ∀ α ∈ alphas, DerivationTree fc [] (event'.imp (Formula.snce α guard))

/-- Iterated BX13 enrichment: given untl(guard, event) ∈ A and a list of
formulas each in A, enrich the event with snce(guard, αⱼ) for each αⱼ.

Result: EnrichedEvent fc containing the new event and proofs. -/
private noncomputable def iterated_enrichment (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    (guard : Formula Atom) :
    (alphas : List (Formula Atom)) →
    (h_alphas : ∀ α ∈ alphas, α ∈ A) →
    (event : Formula Atom) →
    Formula.untl event guard ∈ A →
    EnrichedEvent fc A guard event alphas
  | [], _, event, h_untl => EnrichedEvent.mk event h_untl (identity event) (fun _ h => by simp at h)
  | α :: rest, h_alphas, event, h_untl => by
    have h_α : α ∈ A := h_alphas α (List.mem_cons.mpr (Or.inl rfl))
    have h_enriched := enrichment_until_mcs fc h_mcs h_α h_untl
    have h_rest : ∀ α' ∈ rest, α' ∈ A := fun α' hα' =>
      h_alphas α' (List.mem_cons.mpr (Or.inr hα'))
    let evt := iterated_enrichment fc h_mcs guard rest h_rest
      (Formula.and event (Formula.snce α guard)) h_enriched
    exact EnrichedEvent.mk evt.event' evt.h_untl
      (imp_trans evt.h_impl (lce_imp event (Formula.snce α guard)))
      (fun α' hα' => by
        by_cases h_eq : α' = α
        · subst h_eq; exact imp_trans evt.h_impl (rce_imp event (Formula.snce α' guard))
        · have h : α' ∈ rest := by
            rcases List.mem_cons.mp hα' with rfl | h
            · exact absurd rfl h_eq
            · exact h
          exact evt.h_snce α' h)

/-- Structure for iterated BX13' (Since-direction) enrichment. -/
structure EnrichedEventSince (fc : FrameClass) (C : Set (Formula Atom)) (guard event : Formula Atom) (gammas : List (Formula Atom)) where
  event' : Formula Atom
  h_snce : Formula.snce event' guard ∈ C
  h_impl : DerivationTree fc [] (event'.imp event)
  h_untl : ∀ γ ∈ gammas, DerivationTree fc [] (event'.imp (Formula.untl γ guard))

/-- Iterated BX13' enrichment (Since direction): given snce(guard, event) ∈ C and
a list of formulas each in C, enrich the event with untl(guard, γⱼ) for each γⱼ. -/
private noncomputable def iterated_enrichment_since (fc : FrameClass) {C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C)
    (guard : Formula Atom) :
    (gammas : List (Formula Atom)) →
    (h_gammas : ∀ γ ∈ gammas, γ ∈ C) →
    (event : Formula Atom) →
    Formula.snce event guard ∈ C →
    EnrichedEventSince fc C guard event gammas
  | [], _, event, h_snce => EnrichedEventSince.mk event h_snce (identity event) (fun _ h => by simp at h)
  | γ :: rest, h_gammas, event, h_snce => by
    have h_γ : γ ∈ C := h_gammas γ (List.mem_cons.mpr (Or.inl rfl))
    have h_enriched := enrichment_since_mcs fc h_mcs h_γ h_snce
    have h_rest : ∀ γ' ∈ rest, γ' ∈ C := fun γ' hγ' =>
      h_gammas γ' (List.mem_cons.mpr (Or.inr hγ'))
    let evt := iterated_enrichment_since fc h_mcs guard rest h_rest
      (Formula.and event (Formula.untl γ guard)) h_enriched
    exact EnrichedEventSince.mk evt.event' evt.h_snce
      (imp_trans evt.h_impl (lce_imp event (Formula.untl γ guard)))
      (fun γ' hγ' => by
        by_cases h_eq : γ' = γ
        · subst h_eq; exact imp_trans evt.h_impl (rce_imp event (Formula.untl γ' guard))
        · have h : γ' ∈ rest := by
            rcases List.mem_cons.mp hγ' with rfl | h
            · exact absurd rfl h_eq
            · exact h
          exact evt.h_untl γ' h)

/-! ## Xu Lemma 3.2.1: Full Guard Strengthening for Transitive Frames

Xu 1988 Lemma 3.2.1 (Section 3, transitive frames): If R(A, B, C), then
  (i)  untl(gamma, beta) ∈ B for every beta ∈ B and gamma ∈ C
  (ii) snce(alpha, beta) ∈ B for every beta ∈ B and alpha ∈ A

This strengthens Xu Lemma 2.3 from top-guard (untl(gamma, top)) to arbitrary
guards (untl(gamma, beta) for all beta ∈ B). The proof uses BX5 (self_accum_until)
for the key self-accumulation step, then BX2G+BX3 monotonicity for the
contradiction. No BX14 (separation_until) is needed.

The proof follows the same contradiction pattern as xu_lemma_2_3:
if the formula is not in B, BurgessR3Maximal_extension_fails gives
¬burgessR3(A, DC(delta ∪ B), C). We extract a neg-until witness and derive
a contradiction using BX5 + monotonicity.
-/

/-- Xu Lemma 3.2.1 (i): If R(A, B, C) then untl(gamma, beta) ∈ B for all
beta ∈ B and gamma ∈ C.

Proof by contradiction: suppose untl(gamma, beta) ∉ B. By maximality,
¬burgessR3(A, DC({untl(gamma,beta)} ∪ B), C). Extract witnesses beta' ∈ B,
gamma' ∈ C with ¬untl(gamma', beta' ∧ untl(gamma, beta)) ∈ A.
Let gamma'' = gamma ∧ gamma', beta'' = beta ∧ beta'. From burgessR3:
untl(gamma'', beta'') ∈ A. By BX5: untl(gamma'', beta'' ∧ untl(gamma'', beta'')) ∈ A.
By BX3+BX2G monotonicity: untl(gamma', beta' ∧ untl(gamma, beta)) ∈ A. Contradiction. -/
theorem xu_lemma_3_2_1_until (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    {beta : Formula Atom} (h_beta : beta ∈ B)
    {gamma : Formula Atom} (h_gamma : gamma ∈ C) :
    Formula.untl gamma beta ∈ B := by
  have h_dcs : ClosedUnderDerivation fc B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Suppose untl(gamma, beta) ∉ B, derive contradiction
  by_contra h_not_in_B
  -- Step 1: BurgessR3Maximal_extension_fails gives ¬burgessR3 for extension
  have h_fails := BurgessR3Maximal_extension_fails fc h_r3m h_not_in_B
  -- Step 2: Extract neg-until witness
  -- If ∀ beta' ∈ B, ∀ gamma' ∈ C, untl(gamma', beta' ∧ untl(gamma, beta)) ∈ A,
  -- then burgessR3(A, DC({untl(gamma,beta)} ∪ B), C) would hold, contradiction.
  have h_neg_until_exists : ∃ beta' ∈ B, ∃ gamma' ∈ C,
      Formula.untl gamma' (Formula.and beta' (Formula.untl gamma beta)) ∉ A := by
    by_contra h_all
    push_neg at h_all
    -- Show burgessRSet(A, DC({untl(gamma,beta)} ∪ B), C)
    have h_rset : burgessRSet A (deductiveClosure fc ({Formula.untl gamma beta} ∪ B)) C := by
      intro phi hphi gamma' hgamma'
      obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta', hbeta', ⟨h_impl⟩⟩
      · exact h_r3.1 phi h_B gamma' hgamma'
      · exact untl_left_mono_thm fc h_mcs_A h_impl (h_all beta' hbeta' gamma' hgamma')
    -- Show burgessRSetSince(C, DC({untl(gamma,beta)} ∪ B), A)
    have h_rsince : burgessRSetSince C (deductiveClosure fc ({Formula.untl gamma beta} ∪ B)) A := by
      intro phi hphi alpha halpha
      obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta', hbeta', ⟨h_impl⟩⟩
      · exact h_r3.2 phi h_B alpha halpha
      · have h_burgessR_ext : burgessR A (Formula.and beta' (Formula.untl gamma beta)) C :=
          fun gamma' hgamma' => h_all beta' hbeta' gamma' hgamma'
        have h_snce_ext := burgessR_implies_burgessRSince fc h_mcs_A h_mcs_C h_burgessR_ext alpha halpha
        exact snce_left_mono_thm fc h_mcs_C h_impl h_snce_ext
    exact h_fails ⟨h_rset, h_rsince⟩
  obtain ⟨beta', h_beta', gamma', h_gamma', h_not_in_A⟩ := h_neg_until_exists
  -- Convert to neg formula in A
  have h_neg_until_in_A : (Formula.untl gamma' (Formula.and beta' (Formula.untl gamma beta))).neg ∈ A := by
    rcases SetMaximalConsistent.negation_complete h_mcs_A
      (Formula.untl gamma' (Formula.and beta' (Formula.untl gamma beta))) with h | h
    · exact absurd h h_not_in_A
    · exact h
  -- Step 3: Conjunctions
  -- beta'' = beta ∧ beta' ∈ B (CUD closed under conjunction)
  set beta'' := Formula.and beta beta' with beta''_def
  have h_beta'' : beta'' ∈ B := cud_conj_closed h_dcs h_beta h_beta'
  -- gamma'' = gamma ∧ gamma' ∈ C (MCS closed under conjunction)
  set gamma'' := Formula.and gamma gamma' with gamma''_def
  have h_gamma'' : gamma'' ∈ C := conj_mcs fc h_mcs_C gamma gamma' h_gamma h_gamma'
  -- Step 4: From burgessR3: untl(gamma'', beta'') ∈ A
  have h_untl_gg_bb : Formula.untl gamma'' beta'' ∈ A :=
    h_r3.1 beta'' h_beta'' gamma'' h_gamma''
  -- Step 5: BX5 (self_accum_until): untl(gamma'', beta'' ∧ untl(gamma'', beta'')) ∈ A
  have h_bx5 : Formula.untl gamma'' (Formula.and beta'' (Formula.untl gamma'' beta'')) ∈ A :=
    self_accum_until_mcs fc h_mcs_A beta'' gamma'' h_untl_gg_bb
  -- Step 6: Monotonicity chain to derive contradiction
  -- We need untl(gamma', beta' ∧ untl(gamma, beta)) ∈ A.
  -- From h_bx5: untl(gamma'', beta'' ∧ untl(gamma'', beta'')) ∈ A
  -- Step 6a: Build ⊢ (beta'' ∧ untl(gamma'', beta'')) → (beta' ∧ untl(gamma, beta))
  -- Component 1: ⊢ beta'' → beta' (right projection since beta'' = beta ∧ beta')
  -- Component 2: ⊢ untl(gamma'', beta'') → untl(gamma, beta)
  --   = ⊢ untl(gamma'', beta'') → untl(gamma, beta'') (BX3: event γ∧γ' → γ)
  --     composed with ⊢ untl(gamma, beta'') → untl(gamma, beta) (BX2G: guard β∧β' → β)
  -- Event monotonicity: G(gamma'' → gamma) → untl(gamma'', beta'') → untl(gamma, beta'')
  -- Since ⊢ gamma'' → gamma (lce_imp), ⊢ G(gamma'' → gamma) by temporal_necessitation
  have h_event_impl : DerivationTree fc [] (gamma''.imp gamma) := lce_imp gamma gamma'
  have h_G_event : DerivationTree fc [] (gamma''.imp gamma).all_future :=
    DerivationTree.temporal_necessitation _ h_event_impl
  have h_bx3_ax := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until gamma'' gamma beta'') trivial
  -- ⊢ untl(gamma'', beta'') → untl(gamma, beta'')
  have h_event_mono : DerivationTree fc [] ((Formula.untl gamma'' beta'').imp (Formula.untl gamma beta'')) :=
    DerivationTree.modus_ponens [] _ _ h_bx3_ax h_G_event
  -- Guard monotonicity: ⊢ untl(gamma, beta'') → untl(gamma, beta) via untl_left_mono_deriv
  have h_guard_impl : DerivationTree fc [] (beta''.imp beta) := lce_imp beta beta'
  have h_guard_mono : DerivationTree fc [] ((Formula.untl gamma beta'').imp (Formula.untl gamma beta)) :=
    untl_left_mono_deriv fc beta'' gamma beta h_guard_impl
  -- Compose: ⊢ untl(gamma'', beta'') → untl(gamma, beta)
  have h_untl_mono : DerivationTree fc [] ((Formula.untl gamma'' beta'').imp (Formula.untl gamma beta)) :=
    imp_trans h_event_mono h_guard_mono
  -- Step 6b: Build the full guard implication
  -- ⊢ (beta'' ∧ untl(gamma'', beta'')) → (beta' ∧ untl(gamma, beta))
  -- By extracting components and re-pairing
  have h_full_guard_impl : DerivationTree fc []
      ((Formula.and beta'' (Formula.untl gamma'' beta'')).imp
       (Formula.and beta' (Formula.untl gamma beta))) := by
    -- Derivation in context [beta'' ∧ untl(gamma'', beta'')]
    set ctx := Formula.and beta'' (Formula.untl gamma'' beta'')
    -- From ctx, extract beta' via beta'' → beta' (right projection)
    have h_get_beta' : DerivationTree fc [ctx] beta' := by
      have h1 : DerivationTree fc [ctx] beta'' :=
        DerivationTree.modus_ponens [ctx] ctx beta''
          (DerivationTree.weakening [] [ctx] _ (lce_imp beta'' (Formula.untl gamma'' beta'')) (List.nil_subset _))
          (DerivationTree.assumption _ ctx (by simp))
      exact DerivationTree.modus_ponens [ctx] beta'' beta'
        (DerivationTree.weakening [] [ctx] _ (rce_imp beta beta') (List.nil_subset _))
        h1
    -- From ctx, extract untl(gamma, beta) via monotonicity
    have h_get_untl : DerivationTree fc [ctx] (Formula.untl gamma beta) := by
      have h1 : DerivationTree fc [ctx] (Formula.untl gamma'' beta'') :=
        DerivationTree.modus_ponens [ctx] ctx (Formula.untl gamma'' beta'')
          (DerivationTree.weakening [] [ctx] _ (rce_imp beta'' (Formula.untl gamma'' beta'')) (List.nil_subset _))
          (DerivationTree.assumption _ ctx (by simp))
      exact DerivationTree.modus_ponens [ctx] (Formula.untl gamma'' beta'') (Formula.untl gamma beta)
        (DerivationTree.weakening [] [ctx] _ h_untl_mono (List.nil_subset _))
        h1
    -- Pair them
    have h_paired : DerivationTree fc [ctx] (Formula.and beta' (Formula.untl gamma beta)) :=
      DerivationTree.modus_ponens [ctx] (Formula.untl gamma beta) _
        (DerivationTree.modus_ponens [ctx] beta' _
          (DerivationTree.weakening [] [ctx] _ (pairing beta' (Formula.untl gamma beta)) (List.nil_subset _))
          h_get_beta')
        h_get_untl
    exact deduction_theorem [] ctx (Formula.and beta' (Formula.untl gamma beta)) h_paired
  -- Step 6c: Apply guard monotonicity to BX5 result
  -- untl_left_mono_thm: ⊢ guard_old → guard_new and untl(event, guard_old) ∈ A → untl(event, guard_new) ∈ A
  have h_step1 : Formula.untl gamma'' (Formula.and beta' (Formula.untl gamma beta)) ∈ A :=
    untl_left_mono_thm fc h_mcs_A h_full_guard_impl h_bx5
  -- Step 6d: Apply event monotonicity to change gamma'' → gamma'
  -- right_mono_until_mcs: ⊢ event_old → event_new and untl(event_old, guard) ∈ A → untl(event_new, guard) ∈ A
  have h_event_impl' : DerivationTree fc [] (gamma''.imp gamma') := rce_imp gamma gamma'
  have h_final : Formula.untl gamma' (Formula.and beta' (Formula.untl gamma beta)) ∈ A :=
    right_mono_until_mcs fc h_mcs_A h_event_impl' h_step1
  -- Step 7: Contradiction
  exact absurd h_final (SetMaximalConsistent.neg_excludes h_mcs_A _ h_neg_until_in_A)

/-- Xu Lemma 3.2.1 (ii): If R(A, B, C) then snce(alpha, beta) ∈ B for all
beta ∈ B and alpha ∈ A.

Dual of xu_lemma_3_2_1_until: uses BX5' (self_accum_since), BX3' (right_mono_since),
and BX2H (left_mono_since_H) for the guard strengthening and contradiction. -/
theorem xu_lemma_3_2_1_since (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    {beta : Formula Atom} (h_beta : beta ∈ B)
    {alpha : Formula Atom} (h_alpha : alpha ∈ A) :
    Formula.snce alpha beta ∈ B := by
  have h_dcs : ClosedUnderDerivation fc B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Suppose snce(alpha, beta) ∉ B, derive contradiction
  by_contra h_not_in_B
  -- Step 1: BurgessR3Maximal_extension_fails gives ¬burgessR3 for extension
  have h_fails := BurgessR3Maximal_extension_fails fc h_r3m h_not_in_B
  -- Step 2: Extract neg-since witness
  -- Since condition in burgessR3: ∀ beta' ∈ B, ∀ alpha' ∈ A, snce(alpha', beta') ∈ C
  -- If ∀ beta' ∈ B, ∀ alpha' ∈ A, snce(alpha', beta' ∧ snce(alpha, beta)) ∈ C,
  -- then burgessR3(A, DC({snce(alpha,beta)} ∪ B), C) would hold, contradiction.
  have h_neg_since_exists : ∃ beta' ∈ B, ∃ alpha' ∈ A,
      Formula.snce alpha' (Formula.and beta' (Formula.snce alpha beta)) ∉ C := by
    by_contra h_all
    push_neg at h_all
    -- Show burgessRSetSince(C, DC({snce(alpha,beta)} ∪ B), A)
    have h_rsince : burgessRSetSince C (deductiveClosure fc ({Formula.snce alpha beta} ∪ B)) A := by
      intro phi hphi alpha' halpha'
      obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta', hbeta', ⟨h_impl⟩⟩
      · exact h_r3.2 phi h_B alpha' halpha'
      · exact snce_left_mono_thm fc h_mcs_C h_impl (h_all beta' hbeta' alpha' halpha')
    -- Show burgessRSet(A, DC({snce(alpha,beta)} ∪ B), C)
    have h_rset : burgessRSet A (deductiveClosure fc ({Formula.snce alpha beta} ∪ B)) C := by
      intro phi hphi gamma hgamma
      obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta', hbeta', ⟨h_impl⟩⟩
      · exact h_r3.1 phi h_B gamma hgamma
      · have h_burgessRSince_ext : burgessRSince C (Formula.and beta' (Formula.snce alpha beta)) A :=
          fun alpha' halpha' => h_all beta' hbeta' alpha' halpha'
        have h_untl_ext := burgessRSince_implies_burgessR fc h_mcs_A h_mcs_C h_burgessRSince_ext gamma hgamma
        exact untl_left_mono_thm fc h_mcs_A h_impl h_untl_ext
    exact h_fails ⟨h_rset, h_rsince⟩
  obtain ⟨beta', h_beta', alpha', h_alpha', h_not_in_C⟩ := h_neg_since_exists
  -- Convert to neg formula in C
  have h_neg_since_in_C : (Formula.snce alpha' (Formula.and beta' (Formula.snce alpha beta))).neg ∈ C := by
    rcases SetMaximalConsistent.negation_complete h_mcs_C
      (Formula.snce alpha' (Formula.and beta' (Formula.snce alpha beta))) with h | h
    · exact absurd h h_not_in_C
    · exact h
  -- Step 3: Conjunctions
  set beta'' := Formula.and beta beta' with beta''_def
  have h_beta'' : beta'' ∈ B := cud_conj_closed h_dcs h_beta h_beta'
  set alpha'' := Formula.and alpha alpha' with alpha''_def
  have h_alpha'' : alpha'' ∈ A := conj_mcs fc h_mcs_A alpha alpha' h_alpha h_alpha'
  -- Step 4: From burgessR3: snce(alpha'', beta'') ∈ C
  have h_snce_aa_bb : Formula.snce alpha'' beta'' ∈ C :=
    h_r3.2 beta'' h_beta'' alpha'' h_alpha''
  -- Step 5: BX5' (self_accum_since): snce(alpha'', beta'' ∧ snce(alpha'', beta'')) ∈ C
  have h_bx5 : Formula.snce alpha'' (Formula.and beta'' (Formula.snce alpha'' beta'')) ∈ C :=
    self_accum_since_mcs fc h_mcs_C beta'' alpha'' h_snce_aa_bb
  -- Step 6: Monotonicity chain to derive contradiction
  -- Event monotonicity for Since: H(alpha'' → alpha') → snce(alpha'', guard) → snce(alpha', guard)
  have h_event_impl : DerivationTree fc [] (alpha''.imp alpha') := rce_imp alpha alpha'
  have h_H_event : DerivationTree fc [] (alpha''.imp alpha').all_past :=
    Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_event_impl
  have h_bx3'_ax := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since alpha'' alpha' beta'') trivial
  -- ⊢ snce(alpha'', beta'') → snce(alpha', beta'')
  have h_event_mono : DerivationTree fc [] ((Formula.snce alpha'' beta'').imp (Formula.snce alpha' beta'')) :=
    DerivationTree.modus_ponens [] _ _ h_bx3'_ax h_H_event
  -- Guard monotonicity: ⊢ snce(alpha', beta'') → snce(alpha', beta) via snce_left_mono_deriv
  have h_guard_impl : DerivationTree fc [] (beta''.imp beta) := lce_imp beta beta'
  have h_guard_mono : DerivationTree fc [] ((Formula.snce alpha' beta'').imp (Formula.snce alpha' beta)) :=
    snce_left_mono_deriv fc beta'' alpha' beta h_guard_impl
  -- Compose: ⊢ snce(alpha'', beta'') → snce(alpha', beta)
  have h_snce_mono : DerivationTree fc [] ((Formula.snce alpha'' beta'').imp (Formula.snce alpha' beta)) :=
    imp_trans h_event_mono h_guard_mono
  -- Build the full guard implication
  -- ⊢ (beta'' ∧ snce(alpha'', beta'')) → (beta' ∧ snce(alpha, beta))
  have h_full_guard_impl : DerivationTree fc []
      ((Formula.and beta'' (Formula.snce alpha'' beta'')).imp
       (Formula.and beta' (Formula.snce alpha beta))) := by
    set ctx := Formula.and beta'' (Formula.snce alpha'' beta'')
    have h_get_beta' : DerivationTree fc [ctx] beta' := by
      have h1 : DerivationTree fc [ctx] beta'' :=
        DerivationTree.modus_ponens [ctx] ctx beta''
          (DerivationTree.weakening [] [ctx] _ (lce_imp beta'' (Formula.snce alpha'' beta'')) (List.nil_subset _))
          (DerivationTree.assumption _ ctx (by simp))
      exact DerivationTree.modus_ponens [ctx] beta'' beta'
        (DerivationTree.weakening [] [ctx] _ (rce_imp beta beta') (List.nil_subset _))
        h1
    have h_get_snce : DerivationTree fc [ctx] (Formula.snce alpha beta) := by
      have h1 : DerivationTree fc [ctx] (Formula.snce alpha'' beta'') :=
        DerivationTree.modus_ponens [ctx] ctx (Formula.snce alpha'' beta'')
          (DerivationTree.weakening [] [ctx] _ (rce_imp beta'' (Formula.snce alpha'' beta'')) (List.nil_subset _))
          (DerivationTree.assumption _ ctx (by simp))
      -- snce(alpha'', beta'') → snce(alpha, beta) via event + guard mono
      -- Event: alpha'' → alpha (lce_imp)
      have h_ev : DerivationTree fc [] (alpha''.imp alpha) := lce_imp alpha alpha'
      have h_H_ev : DerivationTree fc [] (alpha''.imp alpha).all_past :=
        Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_ev
      have h_bx3'_ev := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since alpha'' alpha beta'') trivial
      have h_ev_mono : DerivationTree fc [] ((Formula.snce alpha'' beta'').imp (Formula.snce alpha beta'')) :=
        DerivationTree.modus_ponens [] _ _ h_bx3'_ev h_H_ev
      -- Guard: beta'' → beta (lce_imp)
      have h_gd_mono : DerivationTree fc [] ((Formula.snce alpha beta'').imp (Formula.snce alpha beta)) :=
        snce_left_mono_deriv fc beta'' alpha beta (lce_imp beta beta')
      have h_full_snce_mono : DerivationTree fc [] ((Formula.snce alpha'' beta'').imp (Formula.snce alpha beta)) :=
        imp_trans h_ev_mono h_gd_mono
      exact DerivationTree.modus_ponens [ctx] (Formula.snce alpha'' beta'') (Formula.snce alpha beta)
        (DerivationTree.weakening [] [ctx] _ h_full_snce_mono (List.nil_subset _))
        h1
    have h_paired : DerivationTree fc [ctx] (Formula.and beta' (Formula.snce alpha beta)) :=
      DerivationTree.modus_ponens [ctx] (Formula.snce alpha beta) _
        (DerivationTree.modus_ponens [ctx] beta' _
          (DerivationTree.weakening [] [ctx] _ (pairing beta' (Formula.snce alpha beta)) (List.nil_subset _))
          h_get_beta')
        h_get_snce
    exact deduction_theorem [] ctx (Formula.and beta' (Formula.snce alpha beta)) h_paired
  -- Apply guard monotonicity to BX5 result
  have h_step1 : Formula.snce alpha'' (Formula.and beta' (Formula.snce alpha beta)) ∈ C :=
    snce_left_mono_thm fc h_mcs_C h_full_guard_impl h_bx5
  -- Apply event monotonicity to change alpha'' → alpha'
  have h_event_impl' : DerivationTree fc [] (alpha''.imp alpha') := rce_imp alpha alpha'
  have h_final : Formula.snce alpha' (Formula.and beta' (Formula.snce alpha beta)) ∈ C :=
    right_mono_since_mcs fc h_mcs_C h_event_impl' h_step1
  -- Step 7: Contradiction
  exact absurd h_final (SetMaximalConsistent.neg_excludes h_mcs_C _ h_neg_since_in_C)

/-- **Lemma 2.6 Splitting** (Burgess 1982, Lemma 2.6): Given BurgessR3Maximal(A, B, C)
with β ∉ B, construct MCS D with β.neg ∈ D and decomposed BurgessR3Maximal relations:
BurgessR3Maximal(A, B', D) and BurgessR3Maximal(D, B'', C).

Uses Xu 1988 Lemma 3.2.2 (transitive frames): trivial seed {β.neg} ∪ B (consistent
by dcs_neg_union_consistent since B is SDC and β ∉ B). The Until/Since formulas
needed for burgessR3 follow from Xu 3.2.1 (guard strengthening), which proves
untl(γ, β') ∈ B and snce(α, β') ∈ B for all β' ∈ B, γ ∈ C, α ∈ A.
No BX14 (separation_until) is needed. -/
theorem lemma_2_6_splitting (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (_h_gc : g_content A ⊆ C)
    (β : Formula Atom)
    (h_β_not_B : β ∉ B) :
    ∃ B' D B'', BurgessR3Maximal fc A B' D ∧ BurgessR3Maximal fc D B'' C ∧
      SetMaximalConsistent fc D ∧ β.neg ∈ D ∧ B ⊆ D ∧ B ⊆ B' ∧ B ⊆ B'' := by
  -- Step 1: Trivial seed {β.neg} ∪ B is consistent
  -- B is CUD (from BurgessR3Maximal) and β ∉ B, so B is SDC (cud_not_mem_is_sdc).
  -- dcs_neg_union_consistent then gives SetConsistent fc ({β.neg} ∪ B).
  have h_sdc : SetDeductivelyClosed fc B := cud_not_mem_is_sdc h_B_dcs h_β_not_B
  have h_seed_cons : SetConsistent fc ({β.neg} ∪ B) := dcs_neg_union_consistent fc h_sdc h_β_not_B
  -- Step 2: Lindenbaum-extend to MCS D
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  -- Step 3: Extract seed memberships
  have h_β_neg_D : β.neg ∈ D := h_sup (Set.mem_union_left _ (Set.mem_singleton β.neg))
  have h_B_sub_D : B ⊆ D := fun φ hφ => h_sup (Set.mem_union_right _ hφ)
  -- Step 4: Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  -- Xu 3.2.1(i): untl(γ, β') ∈ B for all β' ∈ B, γ ∈ C. Since B ⊆ D: untl(γ, β') ∈ D.
  have h_untl_D : ∀ β' ∈ B, ∀ γ ∈ C, Formula.untl γ β' ∈ D := by
    intro β' hβ' γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until fc h_mcs_A h_mcs_C h_r3m hβ' hγ)
  -- Xu 3.2.1(ii): snce(α, β') ∈ B for all β' ∈ B, α ∈ A. Since B ⊆ D: snce(α, β') ∈ D.
  have h_snce_D : ∀ β' ∈ B, ∀ α ∈ A, Formula.snce α β' ∈ D := by
    intro β' hβ' α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since fc h_mcs_A h_mcs_C h_r3m hβ' hα)
  -- Step 5: Establish burgessR3(D, B, C) from Until formulas
  have h_rSet_D : burgessRSet D B C := fun β' hβ' γ hγ => h_untl_D β' hβ' γ hγ
  -- burgessRSetSince(C, B, D) follows from burgessR via standard conversion
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β' hβ'
    exact burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C (h_rSet_D β' hβ')
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  -- Step 6: Establish burgessR3(A, B, D) from Since formulas
  -- snce(α, β') ∈ D for all β' ∈ B, α ∈ A gives burgessRSetSince(D, B, A)
  have h_rSetSince_A : burgessRSetSince D B A := fun β' hβ' α hα => h_snce_D β' hβ' α hα
  -- burgessR(A, β', D) follows from burgessRSince via standard conversion
  have h_rSet_A : burgessRSet A B D := by
    intro β' hβ'
    exact burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs (h_rSetSince_A β' hβ')
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Step 7: BurgessR3Maximal via Zorn (burgessR3Maximal_extension_exists)
  obtain ⟨B', h_B_sub_B', _, h_B'_max⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_B_sub_B'', _, h_B''_max⟩ := burgessR3Maximal_extension_exists fc h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_β_neg_D, h_B_sub_D, h_B_sub_B', h_B_sub_B''⟩

/-- The D0 seed for Lemma 2.7 (Burgess 1982 p.372), simplified via Xu 3.2.1:
  B ∪ {eta} ∪ {snce(α, β ∧ xi) : β ∈ B, α ∈ A}.

The original 5-component seed included {untl(γ, β)} and {snce(α, β)} but these
are redundant: Xu 3.2.1 proves untl(γ, β) ∈ B and snce(α, β) ∈ B for all
β ∈ B, γ ∈ C, α ∈ A when BurgessR3Maximal(A, B, C). Since B ⊆ D (from
the seed's first component), these formulas are already in D.

The 3rd component snce(α, β∧xi) cannot be dropped because xi ∉ B prevents
Xu 3.2.1 from applying.

Convention alignment with Burgess:
  untl(xi, eta) ∈ A where xi = guard (Burgess η), eta = event (Burgess ξ).
  The condition is xi ∉ B (guard not in B, matching Burgess η ∉ B).
  The seed contains {eta} (event, Burgess ξ) → eta ∈ D.
  The 3rd component snce(β∧xi, α) (Burgess S(α, β∧η)) → xi ∈ B'. -/
private def lemma_2_7_seed (fc : FrameClass) (A B _C : Set (Formula Atom)) (xi eta : Formula Atom) : Set (Formula Atom) :=
  B ∪ {eta} ∪ {φ | ∃ β ∈ B, ∃ α ∈ A, φ = Formula.snce α (Formula.and β xi)}

/-- Extract a B-guard from a single element of the lemma_2_7_seed.
For each of the 3 cases:
1. φ ∈ B: guard = φ
2. φ = eta: guard = ⊤ (any theorem)
3. φ = snce(β'∧xi, α'): guard = β' -/
private noncomputable def l27_guard (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B)
    (xi eta : Formula Atom) (φ : Formula Atom) (h : φ ∈ lemma_2_7_seed fc A B C xi eta) :
    { g : Formula Atom // g ∈ B } := by
  classical
  by_cases h1 : φ ∈ B
  · exact ⟨φ, h1⟩
  · by_cases h5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce α (Formula.and β' xi)
    · exact ⟨Classical.choose h5, (Classical.choose_spec h5).1⟩
    · -- Must be eta
      exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_dcs (identity (Formula.bot : Formula Atom))⟩

/-- Recursively extract B-guards from L ⊆ lemma_2_7_seed.
Includes β₀ (maximality witness guard) to ensure guard→β₀ via conjunction elimination. -/
private noncomputable def l27_collect_guards (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B)
    (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed fc A B C xi eta) →
    { gs : List (Formula Atom) // ∀ g ∈ gs, g ∈ B }
  | [], _ => ⟨[], fun _ h => (by simp at h)⟩
  | φ :: rest, hL =>
    let ⟨g, hg⟩ := l27_guard fc h_dcs xi eta φ (hL φ (List.mem_cons.mpr (Or.inl rfl)))
    let ⟨gs, hgs⟩ := l27_collect_guards fc h_dcs xi eta rest
      (fun ψ hψ => hL ψ (List.mem_cons.mpr (Or.inr hψ)))
    ⟨g :: gs, fun g' hg' => by
      rcases List.mem_cons.mp hg' with rfl | h
      · exact hg
      · exact hgs g' h⟩

/-- For each element of L ⊆ lemma_2_7_seed, extract the A-event
(if snce(β'∧xi, α') formula from component 3). -/
private noncomputable def l27_a_event_list (fc : FrameClass) {A B C : Set (Formula Atom)}
    (xi eta : Formula Atom) (L : List (Formula Atom))
    (_hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed fc A B C xi eta) : List (Formula Atom) :=
  L.filterMap (fun φ => by
    classical
    exact if h : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce α (Formula.and β' xi) then
      some (Classical.choose (Classical.choose_spec h).2)
    else none)

/-- Elements of l27_a_event_list are in A. -/
private theorem l27_a_event_list_mem (fc : FrameClass) {A B C : Set (Formula Atom)}
    {xi eta : Formula Atom} {L : List (Formula Atom)}
    {hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed fc A B C xi eta}
    {α : Formula Atom} (hα : α ∈ l27_a_event_list fc xi eta L hL) : α ∈ A := by
  unfold l27_a_event_list at hα
  rcases List.mem_filterMap.mp hα with ⟨φ, _, h_eq⟩
  split at h_eq
  · next h_snce5 =>
    simp at h_eq
    rw [← h_eq]
    exact (Classical.choose_spec ((Classical.choose_spec h_snce5).2)).1
  · simp at h_eq

/-- If φ ∈ L ∩ B then φ is in l27_collect_guards output. -/
private theorem l27_collect_guards_mem_of_B (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B) (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed fc A B C xi eta) →
    ∀ φ ∈ L, φ ∈ B → φ ∈ (l27_collect_guards fc h_dcs xi eta L hL).val
  | [], _, φ, hφ, _ => (by simp at hφ)
  | ψ :: rest, hL, φ, hφ, h_B => by
    simp [l27_collect_guards]
    rcases List.mem_cons.mp hφ with rfl | h_rest
    · left
      unfold l27_guard; simp [h_B]
    · right; exact l27_collect_guards_mem_of_B fc h_dcs xi eta rest _ φ h_rest h_B

/-- Formula.and is injective in the first argument. -/
private theorem formula_and_left_cancel (fc : FrameClass) {a b c : Formula Atom}
    (h : Formula.and a c = Formula.and b c) : a = b := by
  simp only [Formula.and, Formula.neg] at h
  exact (Formula.imp.injEq _ _ _ _ |>.mp (Formula.imp.injEq _ _ _ _ |>.mp h).1).1

/-- l27_guard for snce(β'∧xi,α') when snce(β'∧xi,α') ∉ B returns β'. -/
private theorem l27_guard_snce_xi_val (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B) (xi eta β' α' : Formula Atom)
    (h_seed : Formula.snce α' (Formula.and β' xi) ∈ lemma_2_7_seed fc A B C xi eta)
    (h_not_B : Formula.snce α' (Formula.and β' xi) ∉ B)
    (hβ' : β' ∈ B) (hα' : α' ∈ A) :
    (l27_guard fc h_dcs xi eta (Formula.snce α' (Formula.and β' xi)) h_seed).val = β' := by
  unfold l27_guard; simp [h_not_B]
  split
  · next h =>
    -- h : β' ∈ B ∧ α' ∈ A (after simp simplified the existential)
    -- The Classical.choose was applied to the original ∃ form.
    -- After simp, the ∃ was resolved. We need to recover the original spec.
    have h_exists : ∃ β'' ∈ B, ∃ α'' ∈ A,
        Formula.snce α' (Formula.and β' xi) = Formula.snce α'' (Formula.and β'' xi) :=
      ⟨β', h.1, α', h.2, rfl⟩
    have h_spec := Classical.choose_spec h_exists
    obtain ⟨hβ_B, α'', hα'', h_eq⟩ := h_spec
    rw [Formula.snce.injEq] at h_eq
    have h_β_eq := (formula_and_left_cancel fc h_eq.2).symm
    convert h_β_eq using 1; simp
  · next h =>
    exfalso; exact h ⟨hβ', hα'⟩

/-- If snce(β'∧xi,α') ∈ L with β'∈B, α'∈A, snce(β'∧xi,α') ∉ B,
then β' is in the guard list. -/
private theorem l27_collect_guards_mem_of_snce_xi (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B) (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed fc A B C xi eta) →
    ∀ β' α', Formula.snce α' (Formula.and β' xi) ∈ L → β' ∈ B → α' ∈ A →
      Formula.snce α' (Formula.and β' xi) ∉ B →
      β' ∈ (l27_collect_guards fc h_dcs xi eta L hL).val
  | [], _, β', α', hφ, _, _, _ => (by simp at hφ)
  | ψ :: rest, hL, β', α', hφ, hβ', hα', h_not_B => by
    simp [l27_collect_guards]
    rcases List.mem_cons.mp hφ with rfl | h_rest
    · left
      exact (l27_guard_snce_xi_val fc h_dcs xi eta β' α'
        (hL (Formula.snce α' (Formula.and β' xi)) (List.mem_cons.mpr (Or.inl rfl)))
        h_not_B hβ' hα').symm
    · right
      exact l27_collect_guards_mem_of_snce_xi fc h_dcs xi eta rest _ β' α' h_rest hβ' hα' h_not_B

/-- If snce(β'∧xi,α') ∈ L with β'∈B, α'∈A, and appropriate conditions,
then α' ∈ l27_a_event_list. -/
private theorem l27_a_event_list_α_mem_xi (fc : FrameClass) {A B C : Set (Formula Atom)}
    {xi eta : Formula Atom} {L : List (Formula Atom)}
    {hL : ∀ φ ∈ L, φ ∈ lemma_2_7_seed fc A B C xi eta}
    {β' α' : Formula Atom} (hφ : Formula.snce α' (Formula.and β' xi) ∈ L)
    (hβ' : β' ∈ B) (hα' : α' ∈ A) :
    α' ∈ l27_a_event_list fc xi eta L hL := by
  unfold l27_a_event_list
  apply List.mem_filterMap.mpr
  refine ⟨Formula.snce α' (Formula.and β' xi), hφ, ?_⟩
  have h_ex : ∃ β'' ∈ B, ∃ α'' ∈ A, Formula.snce α' (Formula.and β' xi) = Formula.snce α'' (Formula.and β'' xi) :=
    ⟨β', hβ', α', hα', rfl⟩
  rw [dif_pos h_ex]
  congr 1
  have h_spec := Classical.choose_spec (Classical.choose_spec h_ex).2
  rw [Formula.snce.injEq] at h_spec
  exact h_spec.2.1.symm


/-- Consistency of the Lemma 2.7 D0 seed (Burgess 1982 p.372), simplified via Xu 3.2.1.

The simplified seed has 3 components: B ∪ {eta} ∪ {snce(α, β∧xi)}.
Uses BX5 (self-accumulation) + BX7 (linearity) + BX13 (enrichment) to derive
F(event) ∈ A, which ensures the seed is consistent. -/
private theorem lemma_2_7_seed_consistent (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (_h_gc : g_content A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : Formula.untl eta xi ∈ A)
    (h_xi_not_B : xi ∉ B) :
    SetConsistent fc (lemma_2_7_seed fc A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Step 1: Extract neg-until witness from xi ∉ B + BurgessR3Maximal
  have h_not_r3_xi := BurgessR3Maximal_extension_fails fc h_r3m h_xi_not_B
  have h_neg_until_exists : ∃ beta0 ∈ B, ∃ gamma0 ∈ C,
      Formula.untl gamma0 (Formula.and beta0 xi) ∉ A := by
    by_contra h_all_until
    push_neg at h_all_until
    have h_rset : burgessRSet A (deductiveClosure fc ({xi} ∪ B)) C := by
      intro phi hphi gamma hgamma
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨h_impl⟩⟩
      · exact h_r3.1 phi h_B_case gamma hgamma
      · exact untl_left_mono_thm fc h_mcs_A h_impl (h_all_until beta_w hbeta_w gamma hgamma)
    have h_rsince : burgessRSetSince C (deductiveClosure fc ({xi} ∪ B)) A := by
      intro phi hphi alpha halpha
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨h_impl⟩⟩
      · exact h_r3.2 phi h_B_case alpha halpha
      · have h_burgessR_ext : burgessR A (Formula.and beta_w xi) C :=
          fun gamma hgamma => h_all_until beta_w hbeta_w gamma hgamma
        have h_snce_ext := burgessR_implies_burgessRSince fc h_mcs_A h_mcs_C h_burgessR_ext alpha halpha
        exact snce_left_mono_thm fc h_mcs_C h_impl h_snce_ext
    exact h_not_r3_xi ⟨h_rset, h_rsince⟩
  obtain ⟨beta0, h_beta0, gamma0, h_gamma0, h_not_in_A⟩ := h_neg_until_exists
  have h_neg_until_in_A : (Formula.untl gamma0 (Formula.and beta0 xi)).neg ∈ A := by
    rcases SetMaximalConsistent.negation_complete h_mcs_A
      (Formula.untl gamma0 (Formula.and beta0 xi)) with h | h
    · exfalso; exact h_not_in_A h
    · exact h
  -- Step 2: Suppose for contradiction some finite L ⊆ seed derives ⊥.
  intro L hL ⟨d⟩
  have h_bx5_xe := self_accum_until_mcs fc h_mcs_A xi eta h_until
  -- h_key: For any b∈B (with ⊢ b→beta0), γ_hat∈C (with ⊢ γ_hat→gamma0), and alpha_list⊆A,
  -- produce event with F(event)∈A and event implies b, eta, untl(γ_hat, b),
  -- and snce(b∧χ_gen, α) for each α∈alpha_list where χ_gen = xi∧untl(xi,eta).
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B) (h_b_beta0 : DerivationTree fc [] (b.imp beta0))
      (γ_hat : Formula Atom) (hγ : γ_hat ∈ C) (h_γ_gamma0 : DerivationTree fc [] (γ_hat.imp gamma0))
      (alpha_list : List (Formula Atom)) (h_alphas : ∀ α ∈ alpha_list, α ∈ A),
      Σ' (event : Formula Atom),
        Formula.some_future event ∈ A ×'
        DerivationTree fc [] (event.imp b) ×'
        DerivationTree fc [] (event.imp eta) ×'
        DerivationTree fc [] (event.imp (Formula.untl γ_hat b)) ×'
        (∀ α ∈ alpha_list, DerivationTree fc [] (event.imp (Formula.snce α (Formula.and b (Formula.and xi (Formula.untl eta xi)))))) by
    -- Extract B-guards and A-events from L
    let b_list_raw := (l27_collect_guards fc h_B_dcs xi eta L hL).val
    have hb_list : ∀ g ∈ b_list_raw, g ∈ B := (l27_collect_guards fc h_B_dcs xi eta L hL).property
    let b_list := beta0 :: b_list_raw
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact h_beta0
      · exact hb_list g h
    let a_list := l27_a_event_list fc xi eta L hL
    have ha_list : ∀ α ∈ a_list, α ∈ A := fun α hα => l27_a_event_list_mem fc hα
    -- Form compressed formulas (gamma0 alone suffices since no untl in seed)
    let b := list_conj fc b_list
    let γ_hat := gamma0
    have hb_B : b ∈ B := list_conj_mem_dcs fc h_B_dcs b_list hb_list'
    have hγ_C : γ_hat ∈ C := h_gamma0
    have h_b_to_beta0 : DerivationTree fc [] (b.imp beta0) :=
      list_conj_implies_elem fc b_list beta0 (List.mem_cons.mpr (Or.inl rfl))
    have h_γ_to_gamma0 : DerivationTree fc [] (γ_hat.imp gamma0) := identity gamma0
    -- Apply h_key
    obtain ⟨event, h_F_event, h_ev_b, h_ev_eta, _h_ev_untl, h_ev_snce⟩ :=
      h_key b hb_B h_b_to_beta0 γ_hat hγ_C h_γ_to_gamma0 a_list ha_list
    -- Show event implies each element of L (3-way case split)
    let χ_gen := Formula.and xi (Formula.untl eta xi)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree fc [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      -- Case 1: φ ∈ B
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_raw : φ ∈ b_list_raw := l27_collect_guards_mem_of_B fc h_B_dcs xi eta L hL φ hφ h_B_case
        have h_φ_in_b : φ ∈ b_list := List.mem_cons.mpr (Or.inr h_φ_in_raw)
        have h_b_to_φ : DerivationTree fc [] (b.imp φ) := list_conj_implies_elem fc b_list φ h_φ_in_b
        have h_ev_to_φ : DerivationTree fc [] (event.imp φ) := imp_trans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · -- Case 2: φ = eta
        by_cases h_eta : φ = eta
        · subst h_eta
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · -- Case 3: φ = snce(β'∧xi, α') with β' ∈ B
          by_cases h_snce5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce α (Formula.and β' xi)
          · let β' := Classical.choose h_snce5
            have hβ' : β' ∈ B := (Classical.choose_spec h_snce5).1
            let α' := Classical.choose (Classical.choose_spec h_snce5).2
            have hα' : α' ∈ A := (Classical.choose_spec (Classical.choose_spec h_snce5).2).1
            have h_eq : φ = Formula.snce α' (Formula.and β' xi) := (Classical.choose_spec (Classical.choose_spec h_snce5).2).2
            have h_φ_eq_snce5 : Formula.snce α' (Formula.and β' xi) ∈ L := by rw [←h_eq]; exact hφ
            rw [h_eq]
            by_cases h_snce5_B : Formula.snce α' (Formula.and β' xi) ∈ B
            · -- In B: treat as B-element
              have h_in_raw := l27_collect_guards_mem_of_B fc h_B_dcs xi eta L hL (Formula.snce α' (Formula.and β' xi)) h_φ_eq_snce5 h_snce5_B
              have h_in_b : Formula.snce α' (Formula.and β' xi) ∈ b_list := List.mem_cons.mpr (Or.inr h_in_raw)
              have h_b_imp : DerivationTree fc [] (b.imp (Formula.snce α' (Formula.and β' xi))) :=
                list_conj_implies_elem fc b_list (Formula.snce α' (Formula.and β' xi)) h_in_b
              have h_ev_imp := imp_trans h_ev_b h_b_imp
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_ev_imp (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
            · -- Not in B: use monotonicity
              have h_α'_in_a := @l27_a_event_list_α_mem_xi _ fc A B C xi eta L hL β' α' h_φ_eq_snce5 hβ' hα'
              have h_ev_snce_α' := h_ev_snce α' h_α'_in_a
              have h_β'_in_raw := l27_collect_guards_mem_of_snce_xi fc h_B_dcs xi eta L hL β' α' h_φ_eq_snce5 hβ' hα' h_snce5_B
              have h_β'_in_b : β' ∈ b_list := List.mem_cons.mpr (Or.inr h_β'_in_raw)
              have h_b_to_β' : DerivationTree fc [] (b.imp β') := list_conj_implies_elem fc b_list β' h_β'_in_b
              have h_bχ_to_β'xi : DerivationTree fc [] ((Formula.and b χ_gen).imp (Formula.and β' xi)) := by
                have h1 : DerivationTree fc [] _ := imp_trans (lce_imp b χ_gen) h_b_to_β'
                have h2 : DerivationTree fc [] _ := imp_trans (rce_imp b χ_gen) (lce_imp xi (Formula.untl eta xi))
                exact combine_imp_conj h1 h2
              have h_mono := snce_left_mono_deriv fc (Formula.and b χ_gen) α' (Formula.and β' xi) h_bχ_to_β'xi
              have h_chain := imp_trans h_ev_snce_α' h_mono
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · -- Contradiction: φ must be in one of the three sets
            exfalso
            simp [lemma_2_7_seed, h_B_case, h_eta, h_snce5] at h_φ_seed
    -- Derive contradiction.
    have d_event : DerivationTree fc [event] Formula.bot :=
      derivation_from_implied fc [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_F_mem fc h_mcs_A event h_F_event
    exact inconsistent_singleton_false fc h_event_cons d_event
  -- Prove h_key: the generalized BX5+BX7+BX13 chain helper.
  intro b hb h_b_beta0 γ_hat hγ h_γ_gamma0 alpha_list h_alphas
  have h_untl_bg : Formula.untl γ_hat b ∈ A := h_r3.1 b hb γ_hat hγ
  have h_bx5_bg := self_accum_until_mcs fc h_mcs_A b γ_hat h_untl_bg
  let φ_gen := Formula.and b (Formula.untl γ_hat b)
  let χ_gen := Formula.and xi (Formula.untl eta xi)
  have h_bx7_gen := linear_until_mcs fc h_mcs_A φ_gen γ_hat χ_gen eta h_bx5_bg h_bx5_xe
  have h_guard_to_b0xi : DerivationTree fc [] ((Formula.and φ_gen χ_gen).imp (Formula.and beta0 xi)) := by
    have h1 : DerivationTree fc [] _ := imp_trans (imp_trans (lce_imp φ_gen χ_gen) (lce_imp b (Formula.untl γ_hat b))) h_b_beta0
    have h2 : DerivationTree fc [] _ := imp_trans (rce_imp φ_gen χ_gen) (lce_imp xi (Formula.untl eta xi))
    exact combine_imp_conj h1 h2
  have h_D3_gen : Formula.untl (Formula.and φ_gen eta) (Formula.and φ_gen χ_gen) ∈ A := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_rm : DerivationTree fc [] ((Formula.and γ_hat eta).imp gamma0) :=
        imp_trans (lce_imp γ_hat eta) h_γ_gamma0
      have h_contra := right_mono_until_mcs fc h_mcs_A h_rm
        (untl_left_mono_thm fc h_mcs_A h_guard_to_b0xi h_D1)
      exact SetMaximalConsistent.neg_excludes h_mcs_A _ h_neg_until_in_A h_contra
    · exfalso
      have h_rm : DerivationTree fc [] ((Formula.and γ_hat χ_gen).imp gamma0) :=
        imp_trans (lce_imp γ_hat χ_gen) h_γ_gamma0
      have h_contra := right_mono_until_mcs fc h_mcs_A h_rm
        (untl_left_mono_thm fc h_mcs_A h_guard_to_b0xi h_D2)
      exact SetMaximalConsistent.neg_excludes h_mcs_A _ h_neg_until_in_A h_contra
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iterated_enrichment fc h_mcs_A guard alpha_list h_alphas base_event h_D3_gen
  let event := evt.event'
  have h_F_event : Formula.some_future event ∈ A := until_implies_F_mcs fc h_mcs_A evt.h_untl
  have h_ev_base := evt.h_impl
  have h_ev_b : DerivationTree fc [] (event.imp b) :=
    imp_trans h_ev_base (imp_trans (lce_imp φ_gen eta) (lce_imp b (Formula.untl γ_hat b)))
  have h_ev_eta : DerivationTree fc [] (event.imp eta) :=
    imp_trans h_ev_base (rce_imp φ_gen eta)
  have h_ev_untl : DerivationTree fc [] (event.imp (Formula.untl γ_hat b)) :=
    imp_trans h_ev_base (imp_trans (lce_imp φ_gen eta) (rce_imp b (Formula.untl γ_hat b)))
  have h_ev_snce : ∀ α ∈ alpha_list,
      DerivationTree fc [] (event.imp (Formula.snce α (Formula.and b χ_gen))) := by
    intro α hα
    have h_snce_guard := evt.h_snce α hα
    have h_guard_to_bχ : DerivationTree fc [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree fc [] _ := imp_trans (lce_imp φ_gen χ_gen) (lce_imp b (Formula.untl γ_hat b))
      have h2 : DerivationTree fc [] _ := rce_imp φ_gen χ_gen
      exact combine_imp_conj h1 h2
    exact imp_trans h_snce_guard (snce_left_mono_deriv fc guard α (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_F_event, h_ev_b, h_ev_eta, h_ev_untl, h_ev_snce⟩


/-- **Lemma 2.7** (Burgess 1982 p.372): Given BurgessR3Maximal(A, B, C) with
untl(xi, eta) ∈ A and xi ∉ B (guard not in B), construct MCS D with eta ∈ D
(event in D) and B' with B ⊆ B' and xi ∈ B' (guard in B').

The Zorn seed for B' is DC(B ∪ {xi}) (not just B), which ensures xi ∈ B'.
This requires the guard conjunction theorem (burgessR_conj) to derive
burgessR3(A, DC(B ∪ {xi}), D) via dc_delta_B_burgessR3.

Convention: untl(xi, eta) = U(eta, xi) in Burgess.
  xi = guard (Burgess η), eta = event (Burgess ξ).
  Burgess: U(ξ,η) ∈ A, η ∉ B, ξ ∈ D, η ∈ B', B ⊆ B'. -/
theorem lemma_2_7 (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (h_gc : g_content A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : Formula.untl eta xi ∈ A)
    (h_xi_not_B : xi ∉ B) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal fc A B' D ∧
      BurgessR3Maximal fc D B'' C ∧
      SetMaximalConsistent fc D ∧
      eta ∈ D ∧
      B ⊆ B' ∧
      B ⊆ D ∧
      B ⊆ B'' ∧
      xi ∈ B' := by
  -- Step 1: The D0 seed is consistent
  have h_seed_cons := lemma_2_7_seed_consistent fc h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_until h_xi_not_B
  -- Step 2: Lindenbaum-extend to MCS D
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  -- Step 3: Extract key memberships from seed
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma_2_7_seed fc A B C xi eta; simp [lemma_2_7_seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma_2_7_seed fc A B C xi eta; simp [lemma_2_7_seed, hφ]
  -- Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  -- Xu 3.2.1(i): untl(γ, β) ∈ B for all β ∈ B, γ ∈ C. Since B ⊆ D: untl(γ, β) ∈ D.
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl γ β ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until fc h_mcs_A h_mcs_C h_r3m hβ hγ)
  -- Xu 3.2.1(ii): snce(α, β) ∈ B for all β ∈ B, α ∈ A. Since B ⊆ D: snce(α, β) ∈ D.
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce α β ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since fc h_mcs_A h_mcs_C h_r3m hβ hα)
  -- Step 4: Establish burgessR3(D, B, C) from Until formulas
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  -- burgessRSince(C, B, D) follows from burgessR via Lemma 2.3
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  -- Step 5: Establish burgessR3(A, B, D) from seed Since formulas
  -- snce(β, α) ∈ D for all β ∈ B, α ∈ A gives burgessRSetSince(D, B, A)
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  -- burgessR(A, β, D) follows from burgessRSince via Lemma 2.3 backward
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Step 5b: Extract snce(β∧xi, α) ∈ D from the 5th seed component
  -- (xi = guard = Burgess η; the 5th component is S(α, β∧η) in Burgess)
  have h_snce_conj_xi_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce α (Formula.and β xi) ∈ D := by
    intro β hβ α hα; apply h_sup
    show Formula.snce α (Formula.and β xi) ∈ lemma_2_7_seed fc A B C xi eta
    simp only [lemma_2_7_seed, Set.mem_union, Set.mem_setOf_eq]; right; exact ⟨β, hβ, α, hα, rfl⟩
  -- Step 5c: Derive snce(xi, α) ∈ D for all α ∈ A (via left_mono_since_H)
  -- From snce(β∧xi, α) ∈ D and ⊢ (β∧xi) → xi: snce(xi, α) ∈ D
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_snce_xi_D : ∀ α ∈ A, Formula.snce α xi ∈ D := by
    intro α hα
    have h_impl : DerivationTree fc [] ((Formula.and β₀ xi).imp xi) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp β₀ xi
    exact snce_left_mono_thm fc h_D_mcs h_impl (h_snce_conj_xi_D β₀ hβ₀ α hα)
  -- Step 5d: Derive untl(xi, δ) ∈ A for all δ ∈ D (via burgessRSince_implies_burgessR)
  -- snce(xi, α) ∈ D for all α ∈ A gives burgessRSince(D, xi, A)
  have h_burgessRSince_xi : burgessRSince D xi A := h_snce_xi_D
  have h_burgessR_xi : burgessR A xi D :=
    burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs h_burgessRSince_xi
  -- Step 6: Derive burgessR(A, β∧xi, D) for all β ∈ B using guard conjunction (Phase 1)
  have h_burgessR_conj : ∀ β ∈ B, burgessR A (Formula.and β xi) D := by
    intro β hβ
    exact burgessR_conj fc h_mcs_A (h_rSet_A β hβ) h_burgessR_xi
  -- Step 6b: Derive untl(β∧xi, δ) ∈ A for all β ∈ B, δ ∈ D
  have h_until_conj : ∀ β ∈ B, ∀ δ ∈ D, Formula.untl δ (Formula.and β xi) ∈ A := by
    intro β hβ δ hδ
    exact h_burgessR_conj β hβ δ hδ
  -- Step 6c: Apply dc_delta_B_burgessR3 to get burgessR3(A, DC({xi} ∪ B), D)
  have h_r3_DC_ABD : burgessR3 A (deductiveClosure fc ({xi} ∪ B)) D :=
    dc_delta_B_burgessR3 fc h_mcs_A h_D_mcs h_B_dcs h_r3_ABD h_until_conj h_snce_conj_xi_D
  -- Step 6d: DC({xi} ∪ B) is CUD (always true, no consistency needed)
  have h_DC_cud : ClosedUnderDerivation fc (deductiveClosure fc ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation fc _
  -- Step 6e: BurgessR3Maximal via Zorn from DC({xi} ∪ B) — gives xi ∈ B'
  obtain ⟨B', h_DC_sub_B', _, h_B'_max⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_D_mcs
    h_DC_cud h_r3_DC_ABD
  obtain ⟨B'', h_B_sub_B'', _, h_B''_max⟩ := burgessR3Maximal_extension_exists fc h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  -- Extract B ⊆ B' from B ⊆ {xi} ∪ B ⊆ DC({xi} ∪ B) ⊆ B'
  have h_B_sub_DC : B ⊆ deductiveClosure fc ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure fc _ (Set.mem_union_right _ hφ)
  have h_B_sub_B' : B ⊆ B' := Set.Subset.trans h_B_sub_DC h_DC_sub_B'
  -- Extract xi ∈ B' from {xi} ⊆ DC({xi} ∪ B) ⊆ B'
  have h_xi_in_DC : xi ∈ deductiveClosure fc ({xi} ∪ B) :=
    subset_deductiveClosure fc _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B' : xi ∈ B' := h_DC_sub_B' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_B', h_B_sub_D,
    h_B_sub_B'', h_xi_in_B'⟩


/-- **Lemma 2.8 seed consistency** (Burgess 1982 p.372):
The same seed as Lemma 2.7 (3 components after Xu 3.2.1 simplification), but
consistency proved using ¬(eta ∨ (xi ∧ untl(xi, eta))) ∈ C instead of xi ∉ B. -/
private theorem lemma_2_8_seed_consistent (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (_h_gc : g_content A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : Formula.untl eta xi ∈ A)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.untl eta xi))).neg ∈ C) :
    SetConsistent fc (lemma_2_7_seed fc A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  set γ' := (Formula.or eta (Formula.and xi (Formula.untl eta xi))).neg with γ'_def
  have h_γ'_to_neg_eta : DerivationTree fc [] (γ'.imp eta.neg) :=
    imp_trans (liftBase fc (demorgan_disj_neg_forward eta (Formula.and xi (Formula.untl eta xi))))
      (lce_imp eta.neg (Formula.and xi (Formula.untl eta xi)).neg)
  have h_γ'_to_neg_chi : DerivationTree fc [] (γ'.imp (Formula.and xi (Formula.untl eta xi)).neg) :=
    imp_trans (liftBase fc (demorgan_disj_neg_forward eta (Formula.and xi (Formula.untl eta xi))))
      (rce_imp eta.neg (Formula.and xi (Formula.untl eta xi)).neg)
  have h_bx5_xe := self_accum_until_mcs fc h_mcs_A xi eta h_until
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B)
      (γ_hat : Formula Atom) (hγ : γ_hat ∈ C) (h_γ_to_γ' : DerivationTree fc [] (γ_hat.imp γ'))
      (alpha_list : List (Formula Atom)) (h_alphas : ∀ α ∈ alpha_list, α ∈ A),
      Σ' (event : Formula Atom),
        Formula.some_future event ∈ A ×'
        DerivationTree fc [] (event.imp b) ×'
        DerivationTree fc [] (event.imp eta) ×'
        DerivationTree fc [] (event.imp (Formula.untl γ_hat b)) ×'
        (∀ α ∈ alpha_list, DerivationTree fc [] (event.imp (Formula.snce α (Formula.and b (Formula.and xi (Formula.untl eta xi)))))) by
    intro L hL ⟨d⟩
    let b_list_raw := (l27_collect_guards fc h_B_dcs xi eta L hL).val
    have hb_list : ∀ g ∈ b_list_raw, g ∈ B := (l27_collect_guards fc h_B_dcs xi eta L hL).property
    let a_list := l27_a_event_list fc xi eta L hL
    have ha_list : ∀ α ∈ a_list, α ∈ A := fun α hα => l27_a_event_list_mem fc hα
    -- b_list with ⊤ prefix for nonemptiness
    let b_list_full := (Formula.bot.imp Formula.bot) :: b_list_raw
    have hb_list_full : ∀ g ∈ b_list_full, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact cud_contains_theorems h_B_dcs (identity (Formula.bot : Formula Atom))
      · exact hb_list g h
    let b := list_conj fc b_list_full
    -- γ_hat = γ' (the neg-disjunction witness)
    let γ_hat := γ'
    have hb_B : b ∈ B := list_conj_mem_dcs fc h_B_dcs b_list_full hb_list_full
    have hγ_C : γ_hat ∈ C := h_neg_disj
    have h_γhat_to_γ' : DerivationTree fc [] (γ_hat.imp γ') := identity γ'
    obtain ⟨event, h_F_event, h_ev_b, h_ev_eta, _h_ev_untl, h_ev_snce⟩ :=
      h_key b hb_B γ_hat hγ_C h_γhat_to_γ' a_list ha_list
    -- Show event implies each element of L (3-way case split)
    let χ_gen := Formula.and xi (Formula.untl eta xi)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree fc [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_raw : φ ∈ b_list_raw := l27_collect_guards_mem_of_B fc h_B_dcs xi eta L hL φ hφ h_B_case
        have h_φ_in_b : φ ∈ b_list_full := List.mem_cons.mpr (Or.inr h_φ_in_raw)
        have h_b_to_φ : DerivationTree fc [] (b.imp φ) := list_conj_implies_elem fc b_list_full φ h_φ_in_b
        have h_ev_to_φ : DerivationTree fc [] (event.imp φ) := imp_trans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta : φ = eta
        · subst h_eta
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · by_cases h_snce5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce α (Formula.and β' xi)
          · let β' := Classical.choose h_snce5
            have hβ' : β' ∈ B := (Classical.choose_spec h_snce5).1
            let α' := Classical.choose (Classical.choose_spec h_snce5).2
            have hα' : α' ∈ A := (Classical.choose_spec (Classical.choose_spec h_snce5).2).1
            have h_eq : φ = Formula.snce α' (Formula.and β' xi) := (Classical.choose_spec (Classical.choose_spec h_snce5).2).2
            have h_φ_eq_snce5 : Formula.snce α' (Formula.and β' xi) ∈ L := by rw [←h_eq]; exact hφ
            rw [h_eq]
            by_cases h_snce5_B : Formula.snce α' (Formula.and β' xi) ∈ B
            · have h_in_raw := l27_collect_guards_mem_of_B fc h_B_dcs xi eta L hL (Formula.snce α' (Formula.and β' xi)) h_φ_eq_snce5 h_snce5_B
              have h_in_b : Formula.snce α' (Formula.and β' xi) ∈ b_list_full := List.mem_cons.mpr (Or.inr h_in_raw)
              have h_b_imp : DerivationTree fc [] (b.imp (Formula.snce α' (Formula.and β' xi))) :=
                list_conj_implies_elem fc b_list_full (Formula.snce α' (Formula.and β' xi)) h_in_b
              have h_ev_imp := imp_trans h_ev_b h_b_imp
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_ev_imp (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
            · have h_α'_in_a := @l27_a_event_list_α_mem_xi _ fc A B C xi eta L hL β' α' h_φ_eq_snce5 hβ' hα'
              have h_ev_snce_α' := h_ev_snce α' h_α'_in_a
              have h_β'_in_raw := l27_collect_guards_mem_of_snce_xi fc h_B_dcs xi eta L hL β' α' h_φ_eq_snce5 hβ' hα' h_snce5_B
              have h_β'_in_b : β' ∈ b_list_full := List.mem_cons.mpr (Or.inr h_β'_in_raw)
              have h_b_to_β' : DerivationTree fc [] (b.imp β') := list_conj_implies_elem fc b_list_full β' h_β'_in_b
              have h_bχ_to_β'xi : DerivationTree fc [] ((Formula.and b χ_gen).imp (Formula.and β' xi)) := by
                have h1 : DerivationTree fc [] _ := imp_trans (lce_imp b χ_gen) h_b_to_β'
                have h2 : DerivationTree fc [] _ := imp_trans (rce_imp b χ_gen) (lce_imp xi (Formula.untl eta xi))
                exact combine_imp_conj h1 h2
              have h_mono := snce_left_mono_deriv fc (Formula.and b χ_gen) α' (Formula.and β' xi) h_bχ_to_β'xi
              have h_chain := imp_trans h_ev_snce_α' h_mono
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp [lemma_2_7_seed, h_B_case, h_eta, h_snce5] at h_φ_seed
    have d_event : DerivationTree fc [event] Formula.bot :=
      derivation_from_implied fc [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_F_mem fc h_mcs_A event h_F_event
    exact inconsistent_singleton_false fc h_event_cons d_event
  -- Prove h_key: BX5+BX7+BX13 chain with D1/D2 eliminated via γ'
  intro b hb γ_hat hγ h_γ_to_γ' alpha_list h_alphas
  have h_untl_bg : Formula.untl γ_hat b ∈ A := h_r3.1 b hb γ_hat hγ
  have h_bx5_bg := self_accum_until_mcs fc h_mcs_A b γ_hat h_untl_bg
  let φ_gen := Formula.and b (Formula.untl γ_hat b)
  let χ_gen := Formula.and xi (Formula.untl eta xi)
  have h_bx7_gen := linear_until_mcs fc h_mcs_A φ_gen γ_hat χ_gen eta h_bx5_bg h_bx5_xe
  have h_D3_gen : Formula.untl (Formula.and φ_gen eta) (Formula.and φ_gen χ_gen) ∈ A := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_event_to_bot : DerivationTree fc [] ((Formula.and γ_hat eta).imp Formula.bot) := by
        have h1 : DerivationTree fc [] ((Formula.and γ_hat eta).imp eta.neg) :=
          imp_trans (lce_imp γ_hat eta) (imp_trans h_γ_to_γ' h_γ'_to_neg_eta)
        have h2 : DerivationTree fc [] _ := rce_imp γ_hat eta
        let PConj := Formula.and γ_hat eta
        have d1 : DerivationTree fc [PConj] eta.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree fc [PConj] eta := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deduction_theorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_F_bot := F_mono_mcs fc h_mcs_A h_event_to_bot
        (until_implies_F_mcs fc h_mcs_A h_D1)
      have h_G_top : Formula.all_future (Formula.bot.imp Formula.bot) ∈ A :=
        theorem_in_mcs h_mcs_A (DerivationTree.temporal_necessitation _
          (identity (Formula.bot : Formula Atom)))
      exact some_future_all_future_neg_absurd h_mcs_A Formula.bot h_F_bot h_G_top
    · exfalso
      have h_event_to_bot : DerivationTree fc [] ((Formula.and γ_hat χ_gen).imp Formula.bot) := by
        have h1 : DerivationTree fc [] ((Formula.and γ_hat χ_gen).imp χ_gen.neg) :=
          imp_trans (lce_imp γ_hat χ_gen) (imp_trans h_γ_to_γ' h_γ'_to_neg_chi)
        have h2 : DerivationTree fc [] _ := rce_imp γ_hat χ_gen
        let PConj := Formula.and γ_hat χ_gen
        have d1 : DerivationTree fc [PConj] χ_gen.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree fc [PConj] χ_gen := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deduction_theorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_F_bot := F_mono_mcs fc h_mcs_A h_event_to_bot
        (until_implies_F_mcs fc h_mcs_A h_D2)
      have h_G_top : Formula.all_future (Formula.bot.imp Formula.bot) ∈ A :=
        theorem_in_mcs h_mcs_A (DerivationTree.temporal_necessitation _
          (identity (Formula.bot : Formula Atom)))
      exact some_future_all_future_neg_absurd h_mcs_A Formula.bot h_F_bot h_G_top
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iterated_enrichment fc h_mcs_A guard alpha_list h_alphas base_event h_D3_gen
  let event := evt.event'
  have h_F_event : Formula.some_future event ∈ A := until_implies_F_mcs fc h_mcs_A evt.h_untl
  have h_ev_base := evt.h_impl
  have h_ev_b : DerivationTree fc [] (event.imp b) :=
    imp_trans h_ev_base (imp_trans (lce_imp φ_gen eta) (lce_imp b (Formula.untl γ_hat b)))
  have h_ev_eta : DerivationTree fc [] (event.imp eta) :=
    imp_trans h_ev_base (rce_imp φ_gen eta)
  have h_ev_untl : DerivationTree fc [] (event.imp (Formula.untl γ_hat b)) :=
    imp_trans h_ev_base (imp_trans (lce_imp φ_gen eta) (rce_imp b (Formula.untl γ_hat b)))
  have h_ev_snce : ∀ α ∈ alpha_list,
      DerivationTree fc [] (event.imp (Formula.snce α (Formula.and b χ_gen))) := by
    intro α hα
    have h_snce_guard := evt.h_snce α hα
    have h_guard_to_bχ : DerivationTree fc [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree fc [] _ := imp_trans (lce_imp φ_gen χ_gen) (lce_imp b (Formula.untl γ_hat b))
      have h2 : DerivationTree fc [] _ := rce_imp φ_gen χ_gen
      exact combine_imp_conj h1 h2
    exact imp_trans h_snce_guard (snce_left_mono_deriv fc guard α (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_F_event, h_ev_b, h_ev_eta, h_ev_untl, h_ev_snce⟩

/-- **Lemma 2.8** (Burgess 1982 p.372): Given BurgessR3Maximal(A, B, C) with
untl(xi, eta) ∈ A and ¬(eta ∨ (xi ∧ untl(xi, eta))) ∈ C, construct MCS D
with eta ∈ D splitting the R3 pair. Also returns xi ∈ B' (guard in B')
via DC(B ∪ {xi}) Zorn seed, matching lemma_2_7's strengthening.

Convention: untl(xi, eta) = U(eta, xi) in Burgess.
  xi = guard (Burgess η), eta = event (Burgess ξ). -/
theorem lemma_2_8 (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (h_gc : g_content A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : Formula.untl eta xi ∈ A)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.untl eta xi))).neg ∈ C) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal fc A B' D ∧
      BurgessR3Maximal fc D B'' C ∧
      SetMaximalConsistent fc D ∧
      eta ∈ D ∧
      B ⊆ D ∧
      B ⊆ B' ∧
      B ⊆ B'' ∧
      xi ∈ B' := by
  -- Step 1: Seed consistency (Lemma 2.8 variant)
  have h_seed_cons := lemma_2_8_seed_consistent fc h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_until h_neg_disj
  -- Step 2: Lindenbaum-extend to MCS D (same as 2.7)
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  -- Step 3: Extract key memberships from seed
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma_2_7_seed fc A B C xi eta; simp [lemma_2_7_seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma_2_7_seed fc A B C xi eta; simp [lemma_2_7_seed, hφ]
  -- Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl γ β ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until fc h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce α β ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since fc h_mcs_A h_mcs_C h_r3m hβ hα)
  -- Step 4: burgessR3(D, B, C) from Until formulas
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  -- Step 5: burgessR3(A, B, D) from Since formulas
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Step 5b: Extract snce(β∧xi, α) ∈ D from the 5th seed component (same as lemma_2_7)
  have h_snce_conj_xi_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce α (Formula.and β xi) ∈ D := by
    intro β hβ α hα; apply h_sup
    show Formula.snce α (Formula.and β xi) ∈ lemma_2_7_seed fc A B C xi eta
    simp only [lemma_2_7_seed, Set.mem_union, Set.mem_setOf_eq]; right; exact ⟨β, hβ, α, hα, rfl⟩
  -- Step 5c: Derive snce(xi, α) ∈ D for all α ∈ A
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_snce_xi_D : ∀ α ∈ A, Formula.snce α xi ∈ D := by
    intro α hα
    have h_impl : DerivationTree fc [] ((Formula.and β₀ xi).imp xi) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp β₀ xi
    exact snce_left_mono_thm fc h_D_mcs h_impl (h_snce_conj_xi_D β₀ hβ₀ α hα)
  -- Step 5d: Derive burgessR(A, xi, D)
  have h_burgessRSince_xi : burgessRSince D xi A := h_snce_xi_D
  have h_burgessR_xi : burgessR A xi D :=
    burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs h_burgessRSince_xi
  -- Step 6: Guard conjunction + DC(B ∪ {xi}) Zorn seed (same as lemma_2_7)
  have h_burgessR_conj : ∀ β ∈ B, burgessR A (Formula.and β xi) D := by
    intro β hβ
    exact burgessR_conj fc h_mcs_A (h_rSet_A β hβ) h_burgessR_xi
  have h_until_conj : ∀ β ∈ B, ∀ δ ∈ D, Formula.untl δ (Formula.and β xi) ∈ A := by
    intro β hβ δ hδ
    exact h_burgessR_conj β hβ δ hδ
  have h_r3_DC_ABD : burgessR3 A (deductiveClosure fc ({xi} ∪ B)) D :=
    dc_delta_B_burgessR3 fc h_mcs_A h_D_mcs h_B_dcs h_r3_ABD h_until_conj h_snce_conj_xi_D
  -- DC({xi} ∪ B) is CUD (always true, no consistency needed)
  have h_DC_cud : ClosedUnderDerivation fc (deductiveClosure fc ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation fc _
  obtain ⟨B', h_DC_sub_B', _, h_B'_max⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_D_mcs
    h_DC_cud h_r3_DC_ABD
  obtain ⟨B'', h_B_sub_B'', _, h_B''_max⟩ := burgessR3Maximal_extension_exists fc h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure fc ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure fc _ (Set.mem_union_right _ hφ)
  have h_B_sub_B' : B ⊆ B' := Set.Subset.trans h_B_sub_DC h_DC_sub_B'
  have h_xi_in_DC : xi ∈ deductiveClosure fc ({xi} ∪ B) :=
    subset_deductiveClosure fc _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B' : xi ∈ B' := h_DC_sub_B' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_D, h_B_sub_B',
    h_B_sub_B'', h_xi_in_B'⟩

/-! ## Lemma 2.7' (Since direction): Since-Formula Splitting

Mirror of Lemma 2.7 for the Since direction. Given `BurgessR3Maximal(A, B, C)` with
`snce(xi, eta) ∈ C` and `xi ∉ B`, produce `B', D, B''` with:
- `BurgessR3Maximal(A, B', D)`
- `BurgessR3Maximal(D, B'', C)`
- `eta ∈ D`

Uses BX5'+BX7'+BX13' (Since-direction chain) instead of BX5+BX7+BX13. -/

/-- Since-direction seed, simplified via Xu 3.2.1:
B ∪ {eta} ∪ {untl(γ, β∧xi) | β∈B, γ∈C}.

The original 5-component seed included {untl(γ,β)} and {snce(α,β)} but these are
redundant: Xu 3.2.1 proves they are already in B. The 3rd component untl(γ, β∧xi)
cannot be dropped because xi ∉ B prevents Xu 3.2.1 from applying. -/
private def lemma_2_7_since_seed (_A B C : Set (Formula Atom)) (xi eta : Formula Atom) : Set (Formula Atom) :=
  B ∪ {eta} ∪ {φ | ∃ β ∈ B, ∃ γ ∈ C, φ = Formula.untl γ (Formula.and β xi)}

/-- Extract γ' events from component 3 elements (untl(γ, β∧xi)) of a list. -/
private noncomputable def l27s_c5_event_list (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  L.filterMap (fun φ => by
    classical
    exact if h : ∃ β' ∈ B, ∃ γ ∈ C, φ = Formula.untl γ (Formula.and β' xi) then
      some (Classical.choose (Classical.choose_spec h).2)
    else none)

/-- Elements of l27s_c5_event_list are in C. -/
private theorem l27s_c5_event_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {γ : Formula Atom} (hγ : γ ∈ l27s_c5_event_list B C xi L) : γ ∈ C := by
  unfold l27s_c5_event_list at hγ
  simp [List.mem_filterMap] at hγ
  obtain ⟨φ, _, hγ_eq⟩ := hγ
  by_cases h : ∃ β' ∈ B, ∃ γ' ∈ C, φ = Formula.untl γ' (Formula.and β' xi)
  · simp [h] at hγ_eq; subst hγ_eq
    exact (Classical.choose_spec (Classical.choose_spec h).2).1
  · simp [h] at hγ_eq

/-- Extract β' guards from component 3 elements (untl(γ, β∧xi)) of a list. -/
private noncomputable def l27s_b5_guard_list (B C : Set (Formula Atom)) (xi : Formula Atom)
    (L : List (Formula Atom)) : List (Formula Atom) :=
  L.filterMap (fun φ => by
    classical
    exact if h : ∃ β' ∈ B, ∃ γ ∈ C, φ = Formula.untl γ (Formula.and β' xi) then
      some (Classical.choose h)
    else none)

/-- Elements of l27s_b5_guard_list are in B. -/
private theorem l27s_b5_guard_list_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β : Formula Atom} (hβ : β ∈ l27s_b5_guard_list B C xi L) : β ∈ B := by
  unfold l27s_b5_guard_list at hβ
  simp [List.mem_filterMap] at hβ
  obtain ⟨φ, _, hβ_eq⟩ := hβ
  by_cases h : ∃ β' ∈ B, ∃ γ' ∈ C, φ = Formula.untl γ' (Formula.and β' xi)
  · simp [h] at hβ_eq; subst hβ_eq
    exact (Classical.choose_spec h).1
  · simp [h] at hβ_eq

/-- For a component 3 element untl(γ', β'∧xi) in L, the extracted γ' is in c5_event_list. -/
private theorem l27s_c5_γ_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl γ' (Formula.and β' xi) ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    γ' ∈ l27s_c5_event_list B C xi L := by
  unfold l27s_c5_event_list
  simp only [List.mem_filterMap]
  refine ⟨Formula.untl γ' (Formula.and β' xi), hφ, ?_⟩
  have h : ∃ β'' ∈ B, ∃ γ'' ∈ C, Formula.untl γ' (Formula.and β' xi) =
      Formula.untl γ'' (Formula.and β'' xi) := ⟨β', hβ', γ', hγ', rfl⟩
  simp only [h, ↓reduceDIte]
  have h_spec := (Classical.choose_spec (Classical.choose_spec h).2)
  exact congr_arg some (Formula.untl.inj h_spec.2).1.symm

/-- For a component 3 element untl(γ', β'∧xi) in L, the extracted β' is in b5_guard_list. -/
private theorem l27s_b5_β_mem {B C : Set (Formula Atom)} {xi : Formula Atom}
    {L : List (Formula Atom)} {β' γ' : Formula Atom}
    (hφ : Formula.untl γ' (Formula.and β' xi) ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    β' ∈ l27s_b5_guard_list B C xi L := by
  unfold l27s_b5_guard_list
  simp only [List.mem_filterMap]
  refine ⟨Formula.untl γ' (Formula.and β' xi), hφ, ?_⟩
  have h : ∃ β'' ∈ B, ∃ γ'' ∈ C, Formula.untl γ' (Formula.and β' xi) =
      Formula.untl γ'' (Formula.and β'' xi) := ⟨β', hβ', γ', hγ', rfl⟩
  simp only [h, ↓reduceDIte]
  have h_spec := Classical.choose_spec h
  obtain ⟨_, γ'', _, h_formula_eq⟩ := h_spec
  have h_inj := Formula.untl.inj h_formula_eq
  simp only [Formula.and, Formula.neg] at h_inj
  exact congr_arg some ((Formula.imp.inj (Formula.imp.inj h_inj.2).1).1).symm

/-- Since-direction seed consistency (simplified via Xu 3.2.1):
Given BurgessR3Maximal(A, B, C) with snce(xi, eta) ∈ C and xi ∉ B,
the 3-component seed B ∪ {eta} ∪ {untl(γ, β∧xi)} is consistent.

Uses BX5'+BX7'+BX13' chain operating on C. -/
private theorem lemma_2_7_since_seed_consistent (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (_h_gc : g_content A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : Formula.snce eta xi ∈ C)
    (h_xi_not_B : xi ∉ B) :
    SetConsistent fc (lemma_2_7_since_seed A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  have h_not_r3_xi := BurgessR3Maximal_extension_fails fc h_r3m h_xi_not_B
  have h_neg_since_exists : ∃ beta0 ∈ B, ∃ alpha0 ∈ A,
      Formula.snce alpha0 (Formula.and beta0 xi) ∉ C := by
    by_contra h_all_since
    push_neg at h_all_since
    have h_rset : burgessRSet A (deductiveClosure fc ({xi} ∪ B)) C := by
      intro phi hphi gamma hgamma
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨h_impl⟩⟩
      · exact h_r3.1 phi h_B_case gamma hgamma
      · have h_burgessRSince_ext : burgessRSince C (Formula.and beta_w xi) A :=
          fun alpha halpha => h_all_since beta_w hbeta_w alpha halpha
        have h_burgessR_ext := burgessRSince_implies_burgessR fc h_mcs_A h_mcs_C h_burgessRSince_ext
        exact untl_left_mono_thm fc h_mcs_A h_impl (h_burgessR_ext gamma hgamma)
    have h_rsince : burgessRSetSince C (deductiveClosure fc ({xi} ∪ B)) A := by
      intro phi hphi alpha halpha
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨h_impl⟩⟩
      · exact h_r3.2 phi h_B_case alpha halpha
      · exact snce_left_mono_thm fc h_mcs_C h_impl (h_all_since beta_w hbeta_w alpha halpha)
    exact h_not_r3_xi ⟨h_rset, h_rsince⟩
  obtain ⟨beta0, h_beta0, alpha0, h_alpha0, h_not_in_C⟩ := h_neg_since_exists
  have h_neg_since_in_C : (Formula.snce alpha0 (Formula.and beta0 xi)).neg ∈ C := by
    rcases SetMaximalConsistent.negation_complete h_mcs_C
      (Formula.snce alpha0 (Formula.and beta0 xi)) with h | h
    · exfalso; exact h_not_in_C h
    · exact h
  intro L hL ⟨d⟩
  have h_bx5_xe := self_accum_since_mcs fc h_mcs_C xi eta h_since
  -- h_key: BX5'+BX7'+BX13' chain for the since direction
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B) (h_b_beta0 : DerivationTree fc [] (b.imp beta0))
      (α_hat : Formula Atom) (hα : α_hat ∈ A) (h_α_alpha0 : DerivationTree fc [] (α_hat.imp alpha0))
      (gamma_list : List (Formula Atom)) (h_gammas : ∀ γ ∈ gamma_list, γ ∈ C),
      Σ' (event : Formula Atom),
        Formula.some_past event ∈ C ×'
        DerivationTree fc [] (event.imp b) ×'
        DerivationTree fc [] (event.imp eta) ×'
        DerivationTree fc [] (event.imp (Formula.snce α_hat b)) ×'
        (∀ γ ∈ gamma_list, DerivationTree fc [] (event.imp (Formula.untl γ (Formula.and b (Formula.and xi (Formula.snce eta xi)))))) by
    -- Extract B-guards, C-events from L
    let b_list_5 := l27s_b5_guard_list B C xi L
    have hb_list_5 : ∀ g ∈ b_list_5, g ∈ B := fun g hg => l27s_b5_guard_list_mem hg
    let c_list := l27s_c5_event_list B C xi L
    have hc_list : ∀ γ ∈ c_list, γ ∈ C := fun γ hγ => l27s_c5_event_list_mem hγ
    -- Also need B-guards for elements of L that are in B directly
    haveI : DecidablePred (· ∈ B) := fun _ => Classical.dec _
    let b_list_B := L.filter (· ∈ B)
    have hb_list_B : ∀ g ∈ b_list_B, g ∈ B := by
      intro g hg; exact decide_eq_true_eq.mp (List.mem_filter.mp hg).2
    let b_list := beta0 :: (b_list_B ++ b_list_5)
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact h_beta0
      · rcases List.mem_append.mp h with h1 | h2
        · exact hb_list_B g h1
        · exact hb_list_5 g h2
    let a_list : List (Formula Atom) := [alpha0]
    have ha_list : ∀ α ∈ a_list, α ∈ A := by
      intro α hα; simp [a_list] at hα; subst hα; exact h_alpha0
    let b := list_conj fc b_list
    let α_hat := list_conj fc a_list
    have hb_B : b ∈ B := list_conj_mem_dcs fc h_B_dcs b_list hb_list'
    have hα_A : α_hat ∈ A := list_conj_mem_mcs fc h_mcs_A a_list ha_list
    have h_b_to_beta0 : DerivationTree fc [] (b.imp beta0) :=
      list_conj_implies_elem fc b_list beta0 (List.mem_cons.mpr (Or.inl rfl))
    have h_α_to_alpha0 : DerivationTree fc [] (α_hat.imp alpha0) :=
      list_conj_implies_elem fc a_list alpha0 (by simp [a_list])
    obtain ⟨event, h_P_event, h_ev_b, h_ev_eta, _h_ev_snce, h_ev_untl⟩ :=
      h_key b hb_B h_b_to_beta0 α_hat hα_A h_α_to_alpha0 c_list hc_list
    -- Show event implies each element of L (3-way case split)
    let χ_gen := Formula.and xi (Formula.snce eta xi)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree fc [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      -- Case 1: φ ∈ B
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_B_list : φ ∈ b_list_B :=
          List.mem_filter.mpr ⟨hφ, decide_eq_true_eq.mpr h_B_case⟩
        have h_φ_in_b : φ ∈ b_list :=
          List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h_φ_in_B_list)))
        have h_b_to_φ := list_conj_implies_elem fc b_list φ h_φ_in_b
        have h_ev_to_φ := imp_trans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · -- Case 2: φ = eta
        by_cases h_eta : φ = eta
        · subst h_eta
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · -- Case 3: φ = untl(γ', β'∧xi) with β'∈B, γ'∈C
          by_cases h_comp5 : ∃ β' ∈ B, ∃ γ' ∈ C, φ = Formula.untl γ' (Formula.and β' xi)
          · let β' := Classical.choose h_comp5
            have hβ' : β' ∈ B := (Classical.choose_spec h_comp5).1
            let γ' := Classical.choose (Classical.choose_spec h_comp5).2
            have hγ' : γ' ∈ C :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).1
            have h_eq : φ = Formula.untl γ' (Formula.and β' xi) :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).2
            rw [h_eq]
            have h_φ_eq : Formula.untl γ' (Formula.and β' xi) ∈ L := by
              rw [← h_eq]; exact hφ
            have h_β'_in_5 := l27s_b5_β_mem h_φ_eq hβ' hγ'
            have h_β'_in_b : β' ∈ b_list :=
              List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h_β'_in_5)))
            have h_b_to_β' := list_conj_implies_elem fc b_list β' h_β'_in_b
            have h_γ'_in_c := l27s_c5_γ_mem h_φ_eq hβ' hγ'
            have h_ev_untl_γ' := h_ev_untl γ' h_γ'_in_c
            have h_bχ_to_β'xi : DerivationTree fc [] ((Formula.and b χ_gen).imp
                (Formula.and β' xi)) := by
              have h1 := imp_trans (lce_imp b χ_gen) h_b_to_β'
              have h2 : DerivationTree fc [] ((Formula.and b χ_gen).imp xi) :=
                imp_trans (rce_imp b χ_gen) (lce_imp xi (Formula.snce eta xi))
              exact combine_imp_conj h1 h2
            have h_left := untl_left_mono_deriv fc (Formula.and b χ_gen) γ'
              (Formula.and β' xi) h_bχ_to_β'xi
            have h_chain := imp_trans h_ev_untl_γ' h_left
            exact DerivationTree.modus_ponens _ _ _
              (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
              (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp only [lemma_2_7_since_seed, Set.mem_union, Set.mem_setOf_eq,
              Set.mem_singleton_iff] at h_φ_seed
            rcases h_φ_seed with ((h1 | h2) | h5)
            · exact h_B_case h1
            · exact h_eta h2
            · exact h_comp5 h5
    have d_event : DerivationTree fc [event] Formula.bot :=
      derivation_from_implied fc [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_P_mem fc h_mcs_C event h_P_event
    exact inconsistent_singleton_false fc h_event_cons d_event
  -- Prove h_key: BX5'+BX7'+BX13' chain.
  intro b hb h_b_beta0 α_hat hα h_α_alpha0 gamma_list h_gammas
  have h_snce_ba : Formula.snce α_hat b ∈ C := h_r3.2 b hb α_hat hα
  have h_bx5_ba := self_accum_since_mcs fc h_mcs_C b α_hat h_snce_ba
  let φ_gen := Formula.and b (Formula.snce α_hat b)
  let χ_gen := Formula.and xi (Formula.snce eta xi)
  have h_bx7_gen := linear_since_mcs fc h_mcs_C φ_gen α_hat χ_gen eta h_bx5_ba h_bx5_xe
  have h_guard_to_b0xi : DerivationTree fc [] ((Formula.and φ_gen χ_gen).imp (Formula.and beta0 xi)) := by
    have h1 : DerivationTree fc [] _ := imp_trans (imp_trans (lce_imp φ_gen χ_gen) (lce_imp b (Formula.snce α_hat b))) h_b_beta0
    have h2 : DerivationTree fc [] _ := imp_trans (rce_imp φ_gen χ_gen) (lce_imp xi (Formula.snce eta xi))
    exact combine_imp_conj h1 h2
  have h_guard_to_alpha0 : DerivationTree fc [] ((Formula.and α_hat eta).imp alpha0) :=
    imp_trans (lce_imp α_hat eta) h_α_alpha0
  have h_D3_gen : Formula.snce (Formula.and φ_gen eta) (Formula.and φ_gen χ_gen) ∈ C := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_rm : DerivationTree fc [] ((Formula.and α_hat eta).imp alpha0) := h_guard_to_alpha0
      have h_contra := right_mono_since_mcs fc h_mcs_C h_rm
        (snce_left_mono_thm fc h_mcs_C h_guard_to_b0xi h_D1)
      exact SetMaximalConsistent.neg_excludes h_mcs_C _ h_neg_since_in_C h_contra
    · exfalso
      have h_rm : DerivationTree fc [] ((Formula.and α_hat χ_gen).imp alpha0) :=
        imp_trans (lce_imp α_hat χ_gen) h_α_alpha0
      have h_contra := right_mono_since_mcs fc h_mcs_C h_rm
        (snce_left_mono_thm fc h_mcs_C h_guard_to_b0xi h_D2)
      exact SetMaximalConsistent.neg_excludes h_mcs_C _ h_neg_since_in_C h_contra
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iterated_enrichment_since fc h_mcs_C guard gamma_list h_gammas base_event h_D3_gen
  let event := evt.event'
  have h_P_event : Formula.some_past event ∈ C := since_implies_P_mcs fc h_mcs_C evt.h_snce
  have h_ev_base := evt.h_impl
  have h_ev_b : DerivationTree fc [] (event.imp b) :=
    imp_trans h_ev_base (imp_trans (lce_imp φ_gen eta) (lce_imp b (Formula.snce α_hat b)))
  have h_ev_eta : DerivationTree fc [] (event.imp eta) :=
    imp_trans h_ev_base (rce_imp φ_gen eta)
  have h_ev_snce_ba : DerivationTree fc [] (event.imp (Formula.snce α_hat b)) :=
    imp_trans h_ev_base (imp_trans (lce_imp φ_gen eta) (rce_imp b (Formula.snce α_hat b)))
  have h_ev_untl : ∀ γ ∈ gamma_list,
      DerivationTree fc [] (event.imp (Formula.untl γ (Formula.and b χ_gen))) := by
    intro γ hγ
    have h_untl_guard := evt.h_untl γ hγ
    have h_guard_to_bχ : DerivationTree fc [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree fc [] _ := imp_trans (lce_imp φ_gen χ_gen) (lce_imp b (Formula.snce α_hat b))
      have h2 : DerivationTree fc [] _ := rce_imp φ_gen χ_gen
      exact combine_imp_conj h1 h2
    exact imp_trans h_untl_guard (untl_left_mono_deriv fc guard γ (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_P_event, h_ev_b, h_ev_eta, h_ev_snce_ba, h_ev_untl⟩

/-- **Lemma 2.7'** (Since direction, Burgess 1982): Given BurgessR3Maximal(A, B, C) with
snce(xi, eta) ∈ C and xi ∉ B, construct MCS D with eta ∈ D splitting the R3 pair.

Mirror of lemma_2_7 fc using BX5'+BX7'+BX13' instead of BX5+BX7+BX13. -/
theorem lemma_2_7_since (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (h_gc : g_content A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : Formula.snce eta xi ∈ C)
    (h_xi_not_B : xi ∉ B) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal fc A B' D ∧
      BurgessR3Maximal fc D B'' C ∧
      SetMaximalConsistent fc D ∧
      eta ∈ D ∧
      B ⊆ B' ∧
      B ⊆ D ∧
      B ⊆ B'' ∧
      xi ∈ B'' := by
  have h_seed_cons := lemma_2_7_since_seed_consistent fc h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_since h_xi_not_B
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma_2_7_since_seed A B C xi eta
    simp [lemma_2_7_since_seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma_2_7_since_seed A B C xi eta; simp [lemma_2_7_since_seed, hφ]
  -- Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl γ β ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until fc h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce α β ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since fc h_mcs_A h_mcs_C h_r3m hβ hα)
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Extract untl(γ, β∧xi) ∈ D from the 3rd seed component
  have h_untl_conj_xi_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl γ (Formula.and β xi) ∈ D := by
    intro β hβ γ hγ; apply h_sup
    show Formula.untl γ (Formula.and β xi) ∈ lemma_2_7_since_seed A B C xi eta
    simp only [lemma_2_7_since_seed, Set.mem_union, Set.mem_setOf_eq]
    right; exact ⟨β, hβ, γ, hγ, rfl⟩
  -- Derive untl(γ, xi) ∈ D via left_mono
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_untl_xi_D : ∀ γ ∈ C, Formula.untl γ xi ∈ D := by
    intro γ hγ
    have h_impl : DerivationTree fc [] ((Formula.and β₀ xi).imp xi) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp β₀ xi
    exact untl_left_mono_thm fc h_D_mcs h_impl (h_untl_conj_xi_D β₀ hβ₀ γ hγ)
  have h_burgessR_xi : burgessR D xi C := h_untl_xi_D
  have h_burgessRSince_xi : burgessRSince C xi D :=
    burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C h_burgessR_xi
  -- Guard conjunction + DC(B ∪ {xi}) Zorn seed for B'' with xi ∈ B''
  have h_burgessR_conj : ∀ β ∈ B, burgessR D (Formula.and β xi) C := by
    intro β hβ
    exact burgessR_conj fc h_D_mcs (h_rSet_D β hβ) h_burgessR_xi
  have h_snce_conj_xi_C : ∀ β ∈ B, ∀ δ ∈ D, Formula.snce δ (Formula.and β xi) ∈ C := by
    intro β hβ δ hδ
    have h_rSince := burgessRSince_conj fc h_mcs_C (h_rSetSince_D β hβ) h_burgessRSince_xi
    exact h_rSince δ hδ
  have h_r3_DC_DBC : burgessR3 D (deductiveClosure fc ({xi} ∪ B)) C :=
    dc_delta_B_burgessR3 fc h_D_mcs h_mcs_C h_B_dcs h_r3_DBC h_untl_conj_xi_D h_snce_conj_xi_C
  have h_DC_cud : ClosedUnderDerivation fc (deductiveClosure fc ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation fc _
  obtain ⟨B', h_B_sub_B', _, h_B'_max⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_DC_sub_B'', _, h_B''_max⟩ := burgessR3Maximal_extension_exists fc h_D_mcs h_mcs_C
    h_DC_cud h_r3_DC_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure fc ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure fc _ (Set.mem_union_right _ hφ)
  have h_B_sub_B'' : B ⊆ B'' := Set.Subset.trans h_B_sub_DC h_DC_sub_B''
  have h_xi_in_DC : xi ∈ deductiveClosure fc ({xi} ∪ B) :=
    subset_deductiveClosure fc _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B'' : xi ∈ B'' := h_DC_sub_B'' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_B', h_B_sub_D,
    h_B_sub_B'', h_xi_in_B''⟩

/-- **Lemma 2.8' seed consistency** (Since direction): Same seed as lemma_2_7_since,
but consistency proved using ¬(eta ∨ (xi ∧ snce(xi,eta))) ∈ A instead of xi ∉ B. -/
private theorem lemma_2_8_since_seed_consistent (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (_h_gc : g_content A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : Formula.snce eta xi ∈ C)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.snce eta xi))).neg ∈ A) :
    SetConsistent fc (lemma_2_7_since_seed A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  set α' := (Formula.or eta (Formula.and xi (Formula.snce eta xi))).neg with α'_def
  have h_α'_to_neg_eta : DerivationTree fc [] (α'.imp eta.neg) :=
    imp_trans (liftBase fc (demorgan_disj_neg_forward eta (Formula.and xi (Formula.snce eta xi))))
      (lce_imp eta.neg (Formula.and xi (Formula.snce eta xi)).neg)
  have h_α'_to_neg_chi : DerivationTree fc [] (α'.imp (Formula.and xi (Formula.snce eta xi)).neg) :=
    imp_trans (liftBase fc (demorgan_disj_neg_forward eta (Formula.and xi (Formula.snce eta xi))))
      (rce_imp eta.neg (Formula.and xi (Formula.snce eta xi)).neg)
  have h_bx5_xe := self_accum_since_mcs fc h_mcs_C xi eta h_since
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B)
      (α_hat : Formula Atom) (hα : α_hat ∈ A) (h_α_to_α' : DerivationTree fc [] (α_hat.imp α'))
      (gamma_list : List (Formula Atom)) (h_gammas : ∀ γ ∈ gamma_list, γ ∈ C),
      Σ' (event : Formula Atom),
        Formula.some_past event ∈ C ×'
        DerivationTree fc [] (event.imp b) ×'
        DerivationTree fc [] (event.imp eta) ×'
        DerivationTree fc [] (event.imp (Formula.snce α_hat b)) ×'
        (∀ γ ∈ gamma_list, DerivationTree fc [] (event.imp (Formula.untl γ (Formula.and b (Formula.and xi (Formula.snce eta xi)))))) by
    intro L hL ⟨d⟩
    haveI : DecidablePred (· ∈ B) := fun _ => Classical.dec _
    -- Extract B-guards and C-events from L
    let b_list_5 := l27s_b5_guard_list B C xi L
    have hb_list_5 : ∀ g ∈ b_list_5, g ∈ B := fun g hg => l27s_b5_guard_list_mem hg
    let c_list := l27s_c5_event_list B C xi L
    have hc_list : ∀ γ ∈ c_list, γ ∈ C := fun γ hγ => l27s_c5_event_list_mem hγ
    let b_list_B := L.filter (· ∈ B)
    have hb_list_B : ∀ g ∈ b_list_B, g ∈ B := by
      intro g hg; exact decide_eq_true_eq.mp (List.mem_filter.mp hg).2
    let b_list := (Formula.bot.imp Formula.bot) :: (b_list_B ++ b_list_5)
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact cud_contains_theorems h_B_dcs (identity (Formula.bot : Formula Atom))
      · rcases List.mem_append.mp h with h1 | h2
        · exact hb_list_B g h1
        · exact hb_list_5 g h2
    let a_list : List (Formula Atom) := [α']
    have ha_list : ∀ α_elem ∈ a_list, α_elem ∈ A := by
      intro α_elem hα_elem; simp [a_list] at hα_elem; subst hα_elem; exact h_neg_disj
    let b := list_conj fc b_list
    let α_hat := list_conj fc a_list
    have hb_B : b ∈ B := list_conj_mem_dcs fc h_B_dcs b_list hb_list'
    have hα_A : α_hat ∈ A := list_conj_mem_mcs fc h_mcs_A a_list ha_list
    have h_αhat_to_α' : DerivationTree fc [] (α_hat.imp α') :=
      list_conj_implies_elem fc a_list α' (by simp [a_list])
    obtain ⟨event, h_P_event, h_ev_b, h_ev_eta, _h_ev_snce, h_ev_untl⟩ :=
      h_key b hb_B α_hat hα_A h_αhat_to_α' c_list hc_list
    -- Show event implies each element of L (3-way case split)
    let χ_gen := Formula.and xi (Formula.snce eta xi)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree fc [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_B_list : φ ∈ b_list_B :=
          List.mem_filter.mpr ⟨hφ, decide_eq_true_eq.mpr h_B_case⟩
        have h_φ_in_b : φ ∈ b_list :=
          List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h_φ_in_B_list)))
        have h_b_to_φ := list_conj_implies_elem fc b_list φ h_φ_in_b
        have h_ev_to_φ := imp_trans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta_case : φ = eta
        · subst h_eta_case
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · by_cases h_comp5 : ∃ β' ∈ B, ∃ γ' ∈ C, φ = Formula.untl γ' (Formula.and β' xi)
          · let β' := Classical.choose h_comp5
            have hβ' : β' ∈ B := (Classical.choose_spec h_comp5).1
            let γ' := Classical.choose (Classical.choose_spec h_comp5).2
            have hγ' : γ' ∈ C :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).1
            have h_eq : φ = Formula.untl γ' (Formula.and β' xi) :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).2
            rw [h_eq]
            have h_φ_eq : Formula.untl γ' (Formula.and β' xi) ∈ L := by
              rw [← h_eq]; exact hφ
            have h_β'_in_5 := l27s_b5_β_mem h_φ_eq hβ' hγ'
            have h_β'_in_b : β' ∈ b_list :=
              List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h_β'_in_5)))
            have h_b_to_β' := list_conj_implies_elem fc b_list β' h_β'_in_b
            have h_γ'_in_c := l27s_c5_γ_mem h_φ_eq hβ' hγ'
            have h_ev_untl_γ' := h_ev_untl γ' h_γ'_in_c
            have h_bχ_to_β'xi : DerivationTree fc [] ((Formula.and b χ_gen).imp
                (Formula.and β' xi)) := by
              have h1 := imp_trans (lce_imp b χ_gen) h_b_to_β'
              have h2 : DerivationTree fc [] ((Formula.and b χ_gen).imp xi) :=
                imp_trans (rce_imp b χ_gen) (lce_imp xi (Formula.snce eta xi))
              exact combine_imp_conj h1 h2
            have h_left := untl_left_mono_deriv fc (Formula.and b χ_gen) γ'
              (Formula.and β' xi) h_bχ_to_β'xi
            have h_chain := imp_trans h_ev_untl_γ' h_left
            exact DerivationTree.modus_ponens _ _ _
              (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
              (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp only [lemma_2_7_since_seed, Set.mem_union, Set.mem_setOf_eq,
              Set.mem_singleton_iff] at h_φ_seed
            rcases h_φ_seed with ((h1 | h2) | h5)
            · exact h_B_case h1
            · exact h_eta_case h2
            · exact h_comp5 h5
    have d_event : DerivationTree fc [event] Formula.bot :=
      derivation_from_implied fc [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_P_mem fc h_mcs_C event h_P_event
    exact inconsistent_singleton_false fc h_event_cons d_event
  -- Prove h_key: BX5'+BX7'+BX13' chain with D1/D2 eliminated via α'
  intro b hb α_hat hα h_α_to_α' gamma_list h_gammas
  have h_snce_ba : Formula.snce α_hat b ∈ C := h_r3.2 b hb α_hat hα
  have h_bx5_ba := self_accum_since_mcs fc h_mcs_C b α_hat h_snce_ba
  let φ_gen := Formula.and b (Formula.snce α_hat b)
  let χ_gen := Formula.and xi (Formula.snce eta xi)
  have h_bx7_gen := linear_since_mcs fc h_mcs_C φ_gen α_hat χ_gen eta h_bx5_ba h_bx5_xe
  have h_D3_gen : Formula.snce (Formula.and φ_gen eta) (Formula.and φ_gen χ_gen) ∈ C := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_event_to_bot : DerivationTree fc [] ((Formula.and α_hat eta).imp Formula.bot) := by
        have h1 : DerivationTree fc [] ((Formula.and α_hat eta).imp eta.neg) :=
          imp_trans (lce_imp α_hat eta) (imp_trans h_α_to_α' h_α'_to_neg_eta)
        have h2 : DerivationTree fc [] _ := rce_imp α_hat eta
        let PConj := Formula.and α_hat eta
        have d1 : DerivationTree fc [PConj] eta.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree fc [PConj] eta := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deduction_theorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_P_bot := P_mono_mcs fc h_mcs_C h_event_to_bot
        (since_implies_P_mcs fc h_mcs_C h_D1)
      have h_H_top : Formula.all_past (Formula.bot.imp Formula.bot) ∈ C :=
        theorem_in_mcs h_mcs_C (Cslib.Logic.Bimodal.Theorems.past_necessitation _
          (identity (Formula.bot : Formula Atom)))
      exact some_past_all_past_neg_absurd h_mcs_C Formula.bot h_P_bot h_H_top
    · exfalso
      have h_event_to_bot : DerivationTree fc [] ((Formula.and α_hat χ_gen).imp Formula.bot) := by
        have h1 : DerivationTree fc [] ((Formula.and α_hat χ_gen).imp χ_gen.neg) :=
          imp_trans (lce_imp α_hat χ_gen) (imp_trans h_α_to_α' h_α'_to_neg_chi)
        have h2 : DerivationTree fc [] _ := rce_imp α_hat χ_gen
        let PConj := Formula.and α_hat χ_gen
        have d1 : DerivationTree fc [PConj] χ_gen.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree fc [PConj] χ_gen := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deduction_theorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_P_bot := P_mono_mcs fc h_mcs_C h_event_to_bot
        (since_implies_P_mcs fc h_mcs_C h_D2)
      have h_H_top : Formula.all_past (Formula.bot.imp Formula.bot) ∈ C :=
        theorem_in_mcs h_mcs_C (Cslib.Logic.Bimodal.Theorems.past_necessitation _
          (identity (Formula.bot : Formula Atom)))
      exact some_past_all_past_neg_absurd h_mcs_C Formula.bot h_P_bot h_H_top
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iterated_enrichment_since fc h_mcs_C guard gamma_list h_gammas base_event h_D3_gen
  let event := evt.event'
  have h_P_event : Formula.some_past event ∈ C := since_implies_P_mcs fc h_mcs_C evt.h_snce
  have h_ev_base := evt.h_impl
  have h_ev_b : DerivationTree fc [] (event.imp b) :=
    imp_trans h_ev_base (imp_trans (lce_imp φ_gen eta) (lce_imp b (Formula.snce α_hat b)))
  have h_ev_eta : DerivationTree fc [] (event.imp eta) :=
    imp_trans h_ev_base (rce_imp φ_gen eta)
  have h_ev_snce_ba : DerivationTree fc [] (event.imp (Formula.snce α_hat b)) :=
    imp_trans h_ev_base (imp_trans (lce_imp φ_gen eta) (rce_imp b (Formula.snce α_hat b)))
  have h_ev_untl : ∀ γ ∈ gamma_list,
      DerivationTree fc [] (event.imp (Formula.untl γ (Formula.and b χ_gen))) := by
    intro γ hγ
    have h_untl_guard := evt.h_untl γ hγ
    have h_guard_to_bχ : DerivationTree fc [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree fc [] _ := imp_trans (lce_imp φ_gen χ_gen) (lce_imp b (Formula.snce α_hat b))
      have h2 : DerivationTree fc [] _ := rce_imp φ_gen χ_gen
      exact combine_imp_conj h1 h2
    exact imp_trans h_untl_guard (untl_left_mono_deriv fc guard γ (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_P_event, h_ev_b, h_ev_eta, h_ev_snce_ba, h_ev_untl⟩

/-- **Lemma 2.8'** (Since direction, Burgess 1982): Given BurgessR3Maximal(A, B, C) with
snce(xi, eta) ∈ C and ¬(eta ∨ (xi ∧ snce(xi, eta))) ∈ A, construct MCS D
with eta ∈ D splitting the R3 pair. Returns xi ∈ B'' via DC(B∪{xi}) Zorn seed. -/
theorem lemma_2_8_since (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (h_gc : g_content A ⊆ C)
    (xi eta : Formula Atom)
    (h_since : Formula.snce eta xi ∈ C)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.snce eta xi))).neg ∈ A) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal fc A B' D ∧
      BurgessR3Maximal fc D B'' C ∧
      SetMaximalConsistent fc D ∧
      eta ∈ D ∧
      B ⊆ D ∧
      B ⊆ B' ∧
      B ⊆ B'' ∧
      xi ∈ B'' := by
  have h_seed_cons := lemma_2_8_since_seed_consistent fc h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_since h_neg_disj
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma_2_7_since_seed A B C xi eta
    simp [lemma_2_7_since_seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma_2_7_since_seed A B C xi eta; simp [lemma_2_7_since_seed, hφ]
  -- Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl γ β ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until fc h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce α β ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since fc h_mcs_A h_mcs_C h_r3m hβ hα)
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Extract untl(γ, β∧xi) ∈ D from the 3rd seed component
  have h_untl_conj_xi_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl γ (Formula.and β xi) ∈ D := by
    intro β hβ γ hγ; apply h_sup
    show Formula.untl γ (Formula.and β xi) ∈ lemma_2_7_since_seed A B C xi eta
    simp only [lemma_2_7_since_seed, Set.mem_union, Set.mem_setOf_eq]
    right; exact ⟨β, hβ, γ, hγ, rfl⟩
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_untl_xi_D : ∀ γ ∈ C, Formula.untl γ xi ∈ D := by
    intro γ hγ
    have h_impl : DerivationTree fc [] ((Formula.and β₀ xi).imp xi) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp β₀ xi
    exact untl_left_mono_thm fc h_D_mcs h_impl (h_untl_conj_xi_D β₀ hβ₀ γ hγ)
  have h_burgessR_xi : burgessR D xi C := h_untl_xi_D
  have h_burgessRSince_xi : burgessRSince C xi D :=
    burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C h_burgessR_xi
  have h_snce_conj_xi_C : ∀ β ∈ B, ∀ δ ∈ D, Formula.snce δ (Formula.and β xi) ∈ C := by
    intro β hβ δ hδ
    exact (burgessRSince_conj fc h_mcs_C (h_rSetSince_D β hβ) h_burgessRSince_xi) δ hδ
  have h_r3_DC_DBC : burgessR3 D (deductiveClosure fc ({xi} ∪ B)) C :=
    dc_delta_B_burgessR3 fc h_D_mcs h_mcs_C h_B_dcs h_r3_DBC h_untl_conj_xi_D h_snce_conj_xi_C
  have h_DC_cud : ClosedUnderDerivation fc (deductiveClosure fc ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation fc _
  obtain ⟨B', h_B_sub_B', _, h_B'_max⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_DC_sub_B'', _, h_B''_max⟩ := burgessR3Maximal_extension_exists fc h_D_mcs h_mcs_C
    h_DC_cud h_r3_DC_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure fc ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure fc _ (Set.mem_union_right _ hφ)
  have h_B_sub_B'' : B ⊆ B'' := Set.Subset.trans h_B_sub_DC h_DC_sub_B''
  have h_xi_in_DC : xi ∈ deductiveClosure fc ({xi} ∪ B) :=
    subset_deductiveClosure fc _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B'' : xi ∈ B'' := h_DC_sub_B'' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_D, h_B_sub_B',
    h_B_sub_B'', h_xi_in_B''⟩

/-! ## Lemma 2.4 with Guard: Enriched Seed Version (Burgess 2.4)

Strengthens `lemma_2_4` to additionally return `γ ∈ B` (guard membership in the
interval DCS). This matches Burgess 1982, Lemma 2.4 exactly: "there exist B, C
such that β ∈ B, γ ∈ C, and R(A,B,C)". In our convention, γ is the guard
(first arg of untl) and β is the event (second arg).

The enriched seed `{β} ∪ g_content(A) ∪ {snce(γ, α) : α ∈ A}` ensures the
Lindenbaum extension C satisfies burgessRSince(C, γ, A), enabling
`burgessR3Maximal_with_guard` to produce B with γ ∈ B. -/

/-- **Enriched Until witness seed consistency**: {β} ∪ g_content(A) ∪ {snce(γ, α) : α ∈ A}
is consistent when untl(γ,β) ∈ MCS A.

Proof (Burgess 2.4): For any finite L ⊆ seed with L ⊢ ⊥, extract α-witnesses
from Since-obligations, form α* ∈ A, apply BX13 enrichment to get
F(β ∧ snce(γ, α*)) ∈ A, then derive ⊥ from {β ∧ snce(γ, α*)} ∪ g_content(A),
contradicting forward_temporal_witness_seed_consistent. -/
theorem until_witness_enriched_seed_consistent (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl β γ ∈ A) :
    SetConsistent fc ({β} ∪ g_content A ∪ {φ | ∃ α ∈ A, φ = Formula.snce α γ}) := by
  intro L hL ⟨d⟩
  have h_extract : ∀ φ ∈ L, (φ ∈ {β} ∪ g_content A) ∨ (∃ α ∈ A, φ = Formula.snce α γ) := by
    intro φ hφ
    have := hL φ hφ
    simp only [Set.mem_union] at this
    rcases this with (h | h) | h
    · exact Or.inl (Set.mem_union_left _ h)
    · exact Or.inl (Set.mem_union_right _ h)
    · exact Or.inr h
  haveI : ∀ φ : Formula Atom, Decidable (∃ α ∈ A, φ = Formula.snce α γ) :=
    fun φ => Classical.dec _
  let get_alpha : Formula Atom → Option (Formula Atom) := fun φ =>
    if h : ∃ α ∈ A, φ = Formula.snce α γ then some h.choose else none
  let alpha_list := L.filterMap get_alpha
  have h_get_alpha_some : ∀ (φ α : Formula Atom),
      get_alpha φ = some α → α ∈ A ∧ φ = Formula.snce α γ := by
    intro φ α hga
    simp only [get_alpha] at hga
    split at hga
    · rename_i h_ex; simp at hga; subst hga
      exact ⟨h_ex.choose_spec.1, h_ex.choose_spec.2⟩
    · simp at hga
  have h_alphas_in_A : ∀ α ∈ alpha_list, α ∈ A := by
    intro α hα
    simp only [alpha_list, List.mem_filterMap] at hα
    obtain ⟨φ, _, hga⟩ := hα
    exact (h_get_alpha_some φ α hga).1
  have h_since_extracted : ∀ φ ∈ L, (∃ α ∈ A, φ = Formula.snce α γ) →
      ∃ α ∈ alpha_list, φ = Formula.snce α γ := by
    intro φ hφ h_ex
    have h_ga_ne_none : get_alpha φ ≠ none := by
      simp only [get_alpha, dif_pos h_ex]; exact Option.some_ne_none _
    obtain ⟨α', hα'⟩ := Option.ne_none_iff_exists'.mp h_ga_ne_none
    have ⟨hα'_A, hφ_eq'⟩ := h_get_alpha_some φ α' hα'
    exact ⟨α', List.mem_filterMap.mpr ⟨φ, hφ, hα'⟩, hφ_eq'⟩
  by_cases h_empty : alpha_list = []
  · have hL' : ∀ φ ∈ L, φ ∈ {β} ∪ g_content A := by
      intro φ hφ
      rcases h_extract φ hφ with h_cov | h_since
      · exact h_cov
      · exfalso
        obtain ⟨α, hα_list, _⟩ := h_since_extracted φ hφ h_since
        rw [h_empty] at hα_list; simp at hα_list
    exact until_witness_seed_consistent fc h_mcs γ β h_until L hL' ⟨d⟩
  · set α_star := list_conj fc alpha_list
    have hα_star_A : α_star ∈ A := list_conj_mem_mcs fc h_mcs alpha_list h_alphas_in_A
    have h_enriched := enrichment_until_mcs fc h_mcs hα_star_A h_until
    have h_F := until_implies_F_mcs fc h_mcs h_enriched
    set ψ_star := Formula.and β (Formula.snce α_star γ)
    have h_cons := forward_temporal_witness_seed_consistent A h_mcs ψ_star h_F
    suffices h_derives : ∀ φ ∈ L, φ ∈ g_content A ∨
        (Nonempty (DerivationTree fc [] (ψ_star.imp φ))) by
      haveI : DecidablePred (· ∈ g_content A) := fun φ => Classical.dec _
      let Γ := L.map (fun φ => if φ ∈ g_content A then φ else ψ_star)
      have hΓ_sub : ∀ ψ ∈ Γ, ψ ∈ {ψ_star} ∪ g_content A := by
        intro ψ hψ
        simp only [Γ, List.mem_map] at hψ
        obtain ⟨φ, _, hψ_eq⟩ := hψ
        split at hψ_eq
        · subst hψ_eq; exact Set.mem_union_right _ ‹_›
        · subst hψ_eq; exact Set.mem_union_left _ (Set.mem_singleton ψ_star)
      have h_L_from_Γ : ∀ φ ∈ L, DerivationTree fc Γ φ := by
        intro φ hφ
        have h_d := h_derives φ hφ
        by_cases h_gc : φ ∈ g_content A
        · exact DerivationTree.assumption Γ φ
            (List.mem_map.mpr ⟨φ, hφ, by simp [h_gc]⟩)
        · have h_ne : Nonempty (DerivationTree fc [] (ψ_star.imp φ)) := by
            rcases h_d with h | h
            · exact absurd h h_gc
            · exact h
          let h_impl := h_ne.some
          have hψ_in_Γ : ψ_star ∈ Γ := by
            simp only [Γ, List.mem_map]
            exact ⟨φ, hφ, by simp [h_gc]⟩
          exact DerivationTree.modus_ponens Γ _ _
            (DerivationTree.weakening [] Γ _ h_impl (List.nil_subset _))
            (DerivationTree.assumption Γ ψ_star hψ_in_Γ)
      exact h_cons Γ hΓ_sub ⟨derivation_from_implied fc Γ L Formula.bot h_L_from_Γ d⟩
    intro φ hφ
    rcases h_extract φ hφ with h_cov | h_since
    · simp only [Set.mem_union, Set.mem_singleton_iff] at h_cov
      rcases h_cov with h_eq | h_gc
      · rw [h_eq]
        exact Or.inr ⟨lce_imp β (Formula.snce α_star γ)⟩
      · exact Or.inl h_gc
    · obtain ⟨α, hα_list, hφ_eq⟩ := h_since_extracted φ hφ h_since
      rw [hφ_eq]
      have h_proj := list_conj_implies_elem fc alpha_list α hα_list
      have h_H_proj := Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_proj
      have h_bx3' := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since α_star α γ) trivial
      have h_snce_mono : DerivationTree fc [] ((Formula.snce α_star γ).imp (Formula.snce α γ)) :=
        mp h_H_proj h_bx3'
      exact Or.inr ⟨imp_trans (rce_imp β (Formula.snce α_star γ)) h_snce_mono⟩

/-- **Lemma 2.4 with guard** (Burgess 2.4, full version): Given MCS A with
untl(γ, β) ∈ A, there exist B, C such that β ∈ C, g_content(A) ⊆ C,
γ ∈ B, and BurgessR3Maximal(A, B, C).

This strengthens `lemma_2_4` by additionally returning `γ ∈ B`. The guard
membership follows from enriching the seed with Since-obligations
{snce(γ, α) : α ∈ A}, which gives burgessRSince(C, γ, A), then applying
burgessR3Maximal_with_guard (RRelation.lean). -/
noncomputable def lemma_2_4_with_guard (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl β γ ∈ A) :
    ∃ B C : Set (Formula Atom), SetMaximalConsistent fc C ∧
      β ∈ C ∧ g_content A ⊆ C ∧
      Formula.some_past (Formula.untl β γ) ∈ C ∧
      γ ∈ B ∧ BurgessR3Maximal fc A B C := by
  have h_seed_cons := until_witness_enriched_seed_consistent fc h_mcs γ β h_until
  obtain ⟨C, h_sup, h_C_mcs⟩ := set_lindenbaum_fc h_seed_cons
  -- β ∈ C from seed
  have h_β_C : β ∈ C := h_sup (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_singleton β)))
  -- g_content(A) ⊆ C from seed
  have h_g_sub : g_content A ⊆ C := fun χ hχ =>
    h_sup (Set.mem_union_left _ (Set.mem_union_right _ hχ))
  -- P(untl(γ,β)) ∈ C from g_content
  have h_GP : Formula.all_future (Formula.some_past (Formula.untl β γ)) ∈ A := by
    have h_ax : DerivationTree fc [] ((Formula.untl β γ).imp
        (Formula.all_future (Formula.some_past (Formula.untl β γ)))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future (Formula.untl β γ)) trivial
    exact SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs h_mcs h_ax) h_until
  have h_P_until_C : Formula.some_past (Formula.untl β γ) ∈ C := h_g_sub h_GP
  -- snce(γ, α) ∈ C for all α ∈ A (from Since-obligation part of enriched seed)
  have h_burgessRSince : burgessRSince C γ A := by
    intro α hα
    exact h_sup (Set.mem_union_right _ ⟨α, hα, rfl⟩)
  -- burgessR(A, γ, C) from burgessRSince via Lemma 2.3 backward
  have h_burgessR := burgessRSince_implies_burgessR fc h_mcs h_C_mcs h_burgessRSince
  -- B with γ ∈ B and BurgessR3Maximal(A, B, C)
  obtain ⟨B, h_γ_B, h_r3m⟩ := burgessR3Maximal_with_guard fc A C γ h_mcs h_C_mcs
    h_burgessR h_burgessRSince
  exact ⟨B, C, h_C_mcs, h_β_C, h_g_sub, h_P_until_C, h_γ_B, h_r3m⟩

/-! ## Lemma 2.4 Since with Guard (Burgess 2.4, backward direction)

Mirror of `lemma_2_4_with_guard` for the Since direction. Given snce(γ,β) ∈ A (MCS),
produces C, B such that β ∈ C, h_content(A) ⊆ C, γ ∈ B, BurgessR3Maximal(C, B, A).

The enriched seed `{β} ∪ h_content(A) ∪ {untl(γ, α) : α ∈ A}` ensures
burgessR(C, γ, A), then `burgessR_implies_burgessRSince` gives
burgessRSince(A, γ, C), enabling `burgessR3Maximal_with_guard C A γ`. -/

/-- **Enriched Since witness seed consistency**: `{β} ∪ h_content(A) ∪ {untl(γ, α) : α ∈ A}`
is consistent when `snce(γ,β) ∈ MCS A`.

Proof (mirror of until_witness_enriched_seed_consistent): For finite L ⊆ seed with L ⊢ ⊥,
extract α-witnesses from Until-obligations, form α*, apply enrichment_since to get
P(β ∧ untl(γ, α*)) ∈ A, then derive ⊥ from `{β ∧ untl(γ, α*)} ∪ h_content(A)`,
contradicting past_temporal_witness_seed_consistent. -/
theorem since_witness_enriched_seed_consistent (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_since : Formula.snce β γ ∈ A) :
    SetConsistent fc ({β} ∪ h_content A ∪ {φ | ∃ α ∈ A, φ = Formula.untl α γ}) := by
  intro L hL ⟨d⟩
  have h_extract : ∀ φ ∈ L, (φ ∈ {β} ∪ h_content A) ∨ (∃ α ∈ A, φ = Formula.untl α γ) := by
    intro φ hφ
    have := hL φ hφ
    simp only [Set.mem_union] at this
    rcases this with (h | h) | h
    · exact Or.inl (Set.mem_union_left _ h)
    · exact Or.inl (Set.mem_union_right _ h)
    · exact Or.inr h
  haveI : ∀ φ : Formula Atom, Decidable (∃ α ∈ A, φ = Formula.untl α γ) :=
    fun φ => Classical.dec _
  let get_alpha : Formula Atom → Option (Formula Atom) := fun φ =>
    if h : ∃ α ∈ A, φ = Formula.untl α γ then some h.choose else none
  let alpha_list := L.filterMap get_alpha
  have h_get_alpha_some : ∀ (φ α : Formula Atom),
      get_alpha φ = some α → α ∈ A ∧ φ = Formula.untl α γ := by
    intro φ α hga
    simp only [get_alpha] at hga
    split at hga
    · rename_i h_ex; simp at hga; subst hga
      exact ⟨h_ex.choose_spec.1, h_ex.choose_spec.2⟩
    · simp at hga
  have h_alphas_in_A : ∀ α ∈ alpha_list, α ∈ A := by
    intro α hα
    simp only [alpha_list, List.mem_filterMap] at hα
    obtain ⟨φ, _, hga⟩ := hα
    exact (h_get_alpha_some φ α hga).1
  have h_untl_extracted : ∀ φ ∈ L, (∃ α ∈ A, φ = Formula.untl α γ) →
      ∃ α ∈ alpha_list, φ = Formula.untl α γ := by
    intro φ hφ h_ex
    have h_ga_ne_none : get_alpha φ ≠ none := by
      simp only [get_alpha, dif_pos h_ex]; exact Option.some_ne_none _
    obtain ⟨α', hα'⟩ := Option.ne_none_iff_exists'.mp h_ga_ne_none
    have ⟨hα'_A, hφ_eq'⟩ := h_get_alpha_some φ α' hα'
    exact ⟨α', List.mem_filterMap.mpr ⟨φ, hφ, hα'⟩, hφ_eq'⟩
  by_cases h_empty : alpha_list = []
  · have hL' : ∀ φ ∈ L, φ ∈ {β} ∪ h_content A := by
      intro φ hφ
      rcases h_extract φ hφ with h_cov | h_untl
      · exact h_cov
      · exfalso
        obtain ⟨α, hα_list, _⟩ := h_untl_extracted φ hφ h_untl
        rw [h_empty] at hα_list; simp at hα_list
    exact past_temporal_witness_seed_consistent A h_mcs β
      (since_implies_P_in_mcs fc h_mcs h_since) L hL' ⟨d⟩
  · set α_star := list_conj fc alpha_list
    have hα_star_A : α_star ∈ A := list_conj_mem_mcs fc h_mcs alpha_list h_alphas_in_A
    have h_enriched := enrichment_since_mcs fc h_mcs hα_star_A h_since
    -- enrichment_since gives: snce(γ, β ∧ untl(γ, α_star)) ∈ A
    -- since_implies_P gives: P(β ∧ untl(γ, α_star)) ∈ A
    have h_P := since_implies_P_mcs fc h_mcs h_enriched
    set ψ_star := Formula.and β (Formula.untl α_star γ)
    have h_cons := past_temporal_witness_seed_consistent A h_mcs ψ_star h_P
    suffices h_derives : ∀ φ ∈ L, φ ∈ h_content A ∨
        (Nonempty (DerivationTree fc [] (ψ_star.imp φ))) by
      haveI : DecidablePred (· ∈ h_content A) := fun φ => Classical.dec _
      let Γ := L.map (fun φ => if φ ∈ h_content A then φ else ψ_star)
      have hΓ_sub : ∀ ψ ∈ Γ, ψ ∈ {ψ_star} ∪ h_content A := by
        intro ψ hψ
        simp only [Γ, List.mem_map] at hψ
        obtain ⟨φ, _, hψ_eq⟩ := hψ
        split at hψ_eq
        · subst hψ_eq; exact Set.mem_union_right _ ‹_›
        · subst hψ_eq; exact Set.mem_union_left _ (Set.mem_singleton ψ_star)
      have h_L_from_Γ : ∀ φ ∈ L, DerivationTree fc Γ φ := by
        intro φ hφ
        have h_d := h_derives φ hφ
        by_cases h_hc : φ ∈ h_content A
        · exact DerivationTree.assumption Γ φ
            (List.mem_map.mpr ⟨φ, hφ, by simp [h_hc]⟩)
        · have h_ne : Nonempty (DerivationTree fc [] (ψ_star.imp φ)) := by
            rcases h_d with h | h
            · exact absurd h h_hc
            · exact h
          let h_impl := h_ne.some
          have hψ_in_Γ : ψ_star ∈ Γ := by
            simp only [Γ, List.mem_map]
            exact ⟨φ, hφ, by simp [h_hc]⟩
          exact DerivationTree.modus_ponens Γ _ _
            (DerivationTree.weakening [] Γ _ h_impl (List.nil_subset _))
            (DerivationTree.assumption Γ ψ_star hψ_in_Γ)
      exact h_cons Γ hΓ_sub ⟨derivation_from_implied fc Γ L Formula.bot h_L_from_Γ d⟩
    intro φ hφ
    rcases h_extract φ hφ with h_cov | h_untl_case
    · simp only [Set.mem_union, Set.mem_singleton_iff] at h_cov
      rcases h_cov with h_eq | h_hc
      · rw [h_eq]
        exact Or.inr ⟨lce_imp β (Formula.untl α_star γ)⟩
      · exact Or.inl h_hc
    · obtain ⟨α, hα_list, hφ_eq⟩ := h_untl_extracted φ hφ h_untl_case
      rw [hφ_eq]
      have h_proj := list_conj_implies_elem fc alpha_list α hα_list
      -- G(α_star → α) gives untl(γ, α_star) → untl(γ, α) via BX3 (right_mono_until)
      have h_G_proj := DerivationTree.temporal_necessitation _ h_proj
      have h_bx2 := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until α_star α γ) trivial
      have h_untl_mono : DerivationTree fc [] ((Formula.untl α_star γ).imp (Formula.untl α γ)) :=
        mp h_G_proj h_bx2
      exact Or.inr ⟨imp_trans (rce_imp β (Formula.untl α_star γ)) h_untl_mono⟩

/-- **Lemma 2.4 Since with guard** (Burgess 2.4, backward direction): Given MCS A with
snce(γ, β) ∈ A, there exist B, C such that β ∈ C, h_content(A) ⊆ C,
γ ∈ B, and BurgessR3Maximal(C, B, A).

This is the Since mirror of `lemma_2_4_with_guard`. The guard membership
follows from enriching the seed with Until-obligations
{untl(γ, α) : α ∈ A}, which gives burgessR(C, γ, A), then
burgessR_implies_burgessRSince fc and burgessR3Maximal_with_guard. -/
noncomputable def lemma_2_4_since_with_guard (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_since : Formula.snce β γ ∈ A) :
    ∃ B C : Set (Formula Atom), SetMaximalConsistent fc C ∧
      β ∈ C ∧ h_content A ⊆ C ∧
      γ ∈ B ∧ BurgessR3Maximal fc C B A := by
  have h_seed_cons := since_witness_enriched_seed_consistent fc h_mcs γ β h_since
  obtain ⟨C, h_sup, h_C_mcs⟩ := set_lindenbaum_fc h_seed_cons
  -- β ∈ C from seed
  have h_β_C : β ∈ C := h_sup (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_singleton β)))
  -- h_content(A) ⊆ C from seed
  have h_h_sub : h_content A ⊆ C := fun χ hχ =>
    h_sup (Set.mem_union_left _ (Set.mem_union_right _ hχ))
  -- burgessR(C, γ, A): ∀ α ∈ A, untl(γ, α) ∈ C (from Until-obligations in seed)
  have h_burgessR : burgessR C γ A := by
    intro α hα
    exact h_sup (Set.mem_union_right _ ⟨α, hα, rfl⟩)
  -- burgessRSince(A, γ, C) from burgessR via Lemma 2.3 forward
  have h_burgessRSince := burgessR_implies_burgessRSince fc h_C_mcs h_mcs h_burgessR
  -- B with γ ∈ B and BurgessR3Maximal(C, B, A)
  obtain ⟨B, h_γ_B, h_r3m⟩ := burgessR3Maximal_with_guard fc C A γ h_C_mcs h_mcs
    h_burgessR h_burgessRSince
  exact ⟨B, C, h_C_mcs, h_β_C, h_h_sub, h_γ_B, h_r3m⟩

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle
