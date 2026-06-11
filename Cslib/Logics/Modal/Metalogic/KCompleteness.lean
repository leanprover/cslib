/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.MCS
public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for Modal Logic K

This module proves completeness for modal logic K via the canonical Kripke model
construction, following Blackburn, de Rijke, Venema "Modal Logic" (2002), Theorem 4.23.

The key challenge is the K-specific Existence Lemma (BRV Lemma 4.20): the existing
`mcs_box_witness` requires axiom T, which K does not have. We provide a K-specific
version `k_mcs_box_witness` that uses EFQ + `derive_box_from_box_context` instead.

## Main Results

- `k_derive_box_from_inconsistency`: K-specific consistency helper (no `h_T`).
- `k_mcs_box_witness`: K-specific Existence Lemma (BRV Lemma 4.20 for K).
- `k_truth_lemma`: K-specific Truth Lemma (BRV Lemma 4.21 for K).
- `k_completeness`: K completeness theorem (BRV Theorem 4.23).

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.20-4.23)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## K-Specific Box Witness Consistency (BRV Lemma 4.20) -/

/-- K-specific version of `derive_box_from_inconsistency` without axiom T.

When `neg phi not in L`, all elements of L have box-versions in S. From `L |- bot`,
we derive `L |- phi` via EFQ, then use `derive_box_from_box_context` to get
`box phi in S`, contradicting `h_not_box`. -/
theorem k_derive_box_from_inconsistency
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not_box : Proposition.box φ ∉ S)
    {L : List (Proposition Atom)}
    (hL : ∀ x ∈ L, x ∈ {ψ | Proposition.box ψ ∈ S} ∪ {Proposition.neg φ})
    (d_bot : DerivationTree Axioms L Proposition.bot) : False := by
  classical
  let L' := L.filter (· ≠ Proposition.neg φ)
  have h_L'_box : ∀ ψ ∈ L', Proposition.box ψ ∈ S := by
    intro ψ hψ
    simp only [L', List.mem_filter, decide_eq_true_eq] at hψ
    rcases hL ψ hψ.1 with h | h
    · exact h
    · exact absurd h hψ.2
  by_cases h_neg_in_L : Proposition.neg φ ∈ L
  · -- Case: neg phi in L -- identical to existing code (does not use h_T)
    have h_perm : ∀ x, x ∈ L → x ∈ Proposition.neg φ :: L' := by
      intro x hx
      by_cases hxn : x = Proposition.neg φ
      · exact List.mem_cons.mpr (Or.inl hxn)
      · exact List.mem_cons.mpr (Or.inr (by
          simp only [L', List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
    have d_reord := DerivationTree.weakening L (Proposition.neg φ :: L')
      Proposition.bot d_bot h_perm
    have d_dne := deductionTheorem h_implyK h_implyS L' (Proposition.neg φ)
      Proposition.bot d_reord
    let neg_phi := Proposition.neg φ
    have efq_ax : DerivationTree Axioms L' (Proposition.bot.imp φ) :=
      .weakening [] L' _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h)
    have ik : DerivationTree Axioms L'
        ((Proposition.bot.imp φ).imp (neg_phi.imp (Proposition.bot.imp φ))) :=
      .weakening [] L' _ (.ax [] _ (h_implyK (Proposition.bot.imp φ) neg_phi))
        (fun _ h => nomatch h)
    have step_k := DerivationTree.modus_ponens L' _ _ ik efq_ax
    have is_ax : DerivationTree Axioms L'
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .weakening [] L' _ (.ax [] _ (h_implyS neg_phi Proposition.bot φ))
        (fun _ h => nomatch h)
    have step_s := DerivationTree.modus_ponens L' _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens L' _ _ step_s d_dne
    have peirce_ax : DerivationTree Axioms L'
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .weakening [] L' _ (.ax [] _ (h_peirce φ Proposition.bot))
        (fun _ h => nomatch h)
    have d_phi := DerivationTree.modus_ponens L' _ _ peirce_ax step3
    exact h_not_box (derive_box_from_box_context h_implyK h_implyS h_K h_mcs
      d_phi h_L'_box)
  · -- Case: neg phi NOT in L -- K-SPECIFIC FIX (BRV Lemma 4.20)
    -- All elements of L have box-versions in S.
    -- From L |- bot, derive L |- phi via EFQ, then box-lift to get box phi in S.
    have h_all_box : ∀ x ∈ L, Proposition.box x ∈ S := by
      intro x hx
      rcases hL x hx with h | h
      · exact h
      · exact absurd (h ▸ hx) h_neg_in_L
    -- Build L |- phi from L |- bot via EFQ
    have efq_ax : DerivationTree Axioms L (Proposition.bot.imp φ) :=
      .weakening [] L _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h)
    have d_phi : DerivationTree Axioms L φ :=
      .modus_ponens L .bot φ efq_ax d_bot
    -- derive_box_from_box_context: from L |- phi with all box x in S, get box phi in S
    exact h_not_box (derive_box_from_box_context h_implyK h_implyS h_K h_mcs
      d_phi h_all_box)

/-! ## K-Specific Box Witness (BRV Lemma 4.20 for K) -/

/-- **K-Specific Box Witness** (BRV Lemma 4.20 for K):
If `box phi not in S` and `S` is MCS, then there exists an MCS `T`
such that `forall psi, box psi in S -> psi in T` and `phi not in T`.
No axiom T hypothesis needed. -/
theorem k_mcs_box_witness
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not_box : Proposition.box φ ∉ S) :
    ∃ T : Set (Proposition Atom), Modal.SetMaximalConsistent Axioms T ∧
      (∀ ψ, Proposition.box ψ ∈ S → ψ ∈ T) ∧ φ ∉ T := by
  let W := {ψ : Proposition Atom | Proposition.box ψ ∈ S} ∪ {Proposition.neg φ}
  have hW : Modal.SetConsistent Axioms W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    exact k_derive_box_from_inconsistency h_implyK h_implyS h_efq h_peirce h_K
      h_mcs h_not_box hL d_bot
  obtain ⟨T, hWT, hT_mcs⟩ := modal_lindenbaum hW
  refine ⟨T, hT_mcs, ?_, ?_⟩
  · intro ψ h_box
    exact hWT (Set.mem_union_left _ h_box)
  · have h_neg : Proposition.neg φ ∈ T :=
      hWT (Set.mem_union_right _ (Set.mem_singleton _))
    exact mcs_not_mem_of_neg h_implyK h_implyS hT_mcs h_neg

/-! ## K-Specific Truth Lemma (BRV Lemma 4.21 for K) -/

/-- **K-Specific Truth Lemma** (BRV Lemma 4.21 for K):
For any canonical world `S` and formula `phi`,
`Satisfies (CanonicalModel Axioms) S phi <-> phi in S.val`.
Uses `k_mcs_box_witness` instead of `mcs_box_witness` (no axiom T). -/
theorem k_truth_lemma
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (S : CanonicalWorld Axioms) :
    (φ : Proposition Atom) →
    (Satisfies (CanonicalModel Axioms) S φ ↔ φ ∈ S.val)
  | .atom p => by
    constructor
    · intro h; exact h
    · intro h; exact h
  | .bot => by
    constructor
    · intro h; exact absurd h id
    · intro h; exact absurd h (mcs_bot_not_mem S.property)
  | .imp φ ψ => by
    constructor
    · intro h_sat
      rcases modal_negation_complete h_implyK h_implyS S.property (φ.imp ψ)
        with h | h
      · exact h
      · exfalso
        have h_phi_S : φ ∈ S.val := by
          apply modal_closed_under_derivation h_implyK h_implyS S.property
            (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          have d_bot' : DerivationTree Axioms
              [φ.imp ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              (.assumption _ _ (by simp [List.mem_cons]))
          have d_efq' : DerivationTree Axioms
              [φ.imp ψ, (φ.imp ψ).imp .bot] φ :=
            .modus_ponens _ .bot φ
              (.weakening [] _ _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h))
              d_bot'
          have d_dt := deductionTheorem h_implyK h_implyS
            [(φ.imp ψ).imp .bot] (φ.imp ψ) φ d_efq'
          have d_peirce' : DerivationTree Axioms
              [(φ.imp ψ).imp .bot] (((φ.imp ψ).imp φ).imp φ) :=
            .weakening [] _ _ (.ax [] _ (h_peirce φ ψ)) (fun _ h => nomatch h)
          exact ⟨.modus_ponens _ _ _ d_peirce' d_dt⟩
        have h_sat_phi :=
          (k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K S φ).mpr h_phi_S
        have h_psi_S :=
          (k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K S ψ).mp
            (h_sat h_sat_phi)
        have h_neg_psi_S : Proposition.neg ψ ∈ S.val := by
          apply modal_closed_under_derivation h_implyK h_implyS S.property
            (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          have d_imp : DerivationTree Axioms
              [ψ, (φ.imp ψ).imp .bot] (φ.imp ψ) :=
            .modus_ponens _ ψ (φ.imp ψ)
              (.weakening [] _ _ (.ax [] _ (h_implyK ψ φ))
                (fun _ h => nomatch h))
              (.assumption _ _ (by simp [List.mem_cons]))
          have d_bot'' : DerivationTree Axioms
              [ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              d_imp
          exact ⟨deductionTheorem h_implyK h_implyS
            [(φ.imp ψ).imp .bot] ψ .bot d_bot''⟩
        exact mcs_bot_not_mem S.property
          (modal_implication_property h_implyK h_implyS S.property
            h_neg_psi_S h_psi_S)
    · intro h_mem h_sat_phi
      exact (k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K S ψ).mpr
        (modal_implication_property h_implyK h_implyS S.property h_mem
          ((k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K S φ).mp
            h_sat_phi))
  | .box φ => by
    constructor
    · intro h_sat
      by_contra h_not_box
      obtain ⟨T, hT_mcs, hST, h_phi_not_T⟩ :=
        k_mcs_box_witness h_implyK h_implyS h_efq h_peirce h_K
          S.property h_not_box
      exact h_phi_not_T
        ((k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K
          ⟨T, hT_mcs⟩ φ).mp (h_sat ⟨T, hT_mcs⟩ hST))
    · intro h_box T hST
      exact (k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K T φ).mpr
        (hST φ h_box)

/-! ## K Completeness Theorem (BRV Theorem 4.23) -/

/-- **Completeness Theorem for Modal Logic K** (BRV Theorem 4.23):

If `phi` is valid over all frames (no frame conditions), then `phi`
is K-derivable from the empty context. -/
theorem k_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      ∀ w, Satisfies m w φ) :
    Derivable (@KAxiom Atom) φ := by
  by_contra h_not_deriv
  have h_cons : Modal.SetConsistent (@KAxiom Atom)
      ({Proposition.neg φ} : Set (Proposition Atom)) := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d⟩
    have d_weak : DerivationTree (@KAxiom Atom) [Proposition.neg φ]
        Proposition.bot :=
      .weakening L [Proposition.neg φ] .bot d (fun x hx => by
        have := hL x hx; simp at this
        exact List.mem_cons.mpr (Or.inl this))
    have d_dne := deductionTheorem
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      [] (Proposition.neg φ) .bot d_weak
    let neg_phi := Proposition.neg φ
    have efq_ax : DerivationTree (@KAxiom Atom) (Atom := Atom) []
        (Proposition.bot.imp φ) :=
      .ax [] _ (.efq φ)
    have ik : DerivationTree (@KAxiom Atom) (Atom := Atom) []
        ((Proposition.bot.imp φ).imp
          (neg_phi.imp (Proposition.bot.imp φ))) :=
      .ax [] _ (.implyK (Proposition.bot.imp φ) neg_phi)
    have step_k := DerivationTree.modus_ponens [] _ _ ik efq_ax
    have is_ax : DerivationTree (@KAxiom Atom) (Atom := Atom) []
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .ax [] _ (.implyS neg_phi Proposition.bot φ)
    have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
    have peirce_ax : DerivationTree (@KAxiom Atom) (Atom := Atom) []
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .ax [] _ (.peirce φ Proposition.bot)
    have d_phi := DerivationTree.modus_ponens [] _ _ peirce_ax step3
    exact h_not_deriv ⟨d_phi⟩
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@KAxiom Atom) := ⟨M, hM_mcs⟩
  exact mcs_not_mem_of_neg
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    hM_mcs (hM_sup (Set.mem_singleton _))
    ((k_truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      w φ).mp
      (h_valid (CanonicalWorld (@KAxiom Atom))
        (CanonicalModel (@KAxiom Atom))
        w))

end Cslib.Logic.Modal
