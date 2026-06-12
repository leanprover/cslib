/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.DeductionTheorem

/-! # Maximal Consistent Sets for Normal Modal Logics

This module instantiates the generic MCS framework (from `Consistency.lean`)
parameterized over an axiom predicate `Axioms : Proposition Atom -> Prop` and proves
modal-specific MCS properties needed for canonical model constructions.

## Parameterization Design

- **Generic properties** (lindenbaum, closed_under_derivation, etc.) take `{Axioms}`
  and, where needed, explicit `h_implyK`/`h_implyS` for the deduction theorem.
- **Modal-specific properties** (mcs_box_closure, mcs_box_box, etc.) take explicit
  axiom hypotheses (e.g., `h_T`, `h_4`, `h_B`, `h_K`) instead of relying on specific
  `ModalAxiom` constructors.

## Backward Compatibility

All definitions are parameterized. S5-specific usage passes `ModalAxiom` and the
corresponding constructor proofs.

## References

* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS framework
* BimodalLogic/Theories/Bimodal/Metalogic/Core/MCSProperties.lean -- reference pattern
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Abbreviations for readability -/

/-- Set consistency for a parameterized modal derivation system. -/
abbrev SetConsistent (Axioms : Proposition Atom → Prop)
    (S : Set (Proposition Atom)) : Prop :=
  Metalogic.SetConsistent (modalDerivationSystem Axioms) S

/-- Set maximal consistency for a parameterized modal derivation system. -/
abbrev SetMaximalConsistent (Axioms : Proposition Atom → Prop)
    (S : Set (Proposition Atom)) : Prop :=
  Metalogic.SetMaximalConsistent (modalDerivationSystem Axioms) S

/-! ## Generic MCS Properties (instantiated) -/

/-- Lindenbaum's lemma: every consistent set extends to an MCS. -/
theorem modal_lindenbaum {Axioms : Proposition Atom → Prop}
    {S : Set (Proposition Atom)}
    (hS : SetConsistent Axioms S) :
    ∃ M : Set (Proposition Atom),
      S ⊆ M ∧ SetMaximalConsistent Axioms M :=
  Metalogic.set_lindenbaum (modalDerivationSystem Axioms) hS

/-- Derivable formulas are in MCS. -/
theorem modal_closed_under_derivation
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {L : List (Proposition Atom)} (h_sub : ∀ ψ ∈ L, ψ ∈ S)
    {φ : Proposition Atom}
    (h_deriv : (modalDerivationSystem Axioms).Deriv L φ) : φ ∈ S :=
  Metalogic.SetMaximalConsistent.closed_under_derivation
    (modalDerivationSystem Axioms)
    (modal_has_deduction_theorem h_implyK h_implyS)
    h_mcs h_sub h_deriv

/-- Implication property: if `phi -> psi in S` and `phi in S`, then `psi in S`. -/
theorem modal_implication_property
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ ψ : Proposition Atom} (h_imp : (φ → ψ) ∈ S) (h_phi : φ ∈ S) :
    ψ ∈ S :=
  Metalogic.SetMaximalConsistent.implication_property
    (modalDerivationSystem Axioms)
    (modal_has_deduction_theorem h_implyK h_implyS)
    h_mcs h_imp h_phi

/-- Negation completeness: for any formula `phi`, either `phi in S` or `neg phi in S`. -/
theorem modal_negation_complete
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    (φ : Proposition Atom) : φ ∈ S ∨ (¬φ) ∈ S :=
  Metalogic.SetMaximalConsistent.negation_complete
    (modalDerivationSystem Axioms)
    (modal_has_deduction_theorem h_implyK h_implyS)
    h_mcs φ

/-! ## Modal-Specific MCS Properties -/

/-- Helper: derive a formula from membership in an MCS using an axiom and MP. -/
theorem mcs_mp_axiom
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ ψ : Proposition Atom} (h_mem : φ ∈ S) (h_ax : Axioms (φ → ψ)) :
    ψ ∈ S := by
  apply modal_closed_under_derivation h_implyK h_implyS h_mcs
    (L := [φ]) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h_mem)
  unfold modalDerivationSystem Deriv
  exact ⟨.modus_ponens [φ] φ ψ
    (.weakening [] [φ] (φ → ψ) (.ax [] _ h_ax) (fun _ h => nomatch h))
    (.assumption [φ] φ (List.mem_cons.mpr (Or.inl rfl)))⟩

/-- `bot not in S` for any MCS `S`. -/
theorem mcs_bot_not_mem
    {Axioms : Proposition Atom → Prop}
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S) :
    ⊥ ∉ S := by
  intro h_bot
  exact h_mcs.1 [⊥]
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h_bot)
    (by simp only [modalDerivationSystem, Deriv]
        exact ⟨.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))⟩)

/-- If `box phi in S` and `S` is MCS, then `phi in S` (using axiom T). -/
theorem mcs_box_closure
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_T : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp φ))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_box : (□φ) ∈ S) : φ ∈ S :=
  mcs_mp_axiom h_implyK h_implyS h_mcs h_box (h_T φ)

/-- If `box phi in S` and `S` is MCS, then `box box phi in S` (using axiom 4). -/
theorem mcs_box_box
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_4 : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp (Proposition.box (Proposition.box φ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_box : (□φ) ∈ S) :
    (□□φ) ∈ S :=
  mcs_mp_axiom h_implyK h_implyS h_mcs h_box (h_4 φ)

/-- If `phi in S` and `S` is MCS, then `box diamond phi in S` (using axiom B). -/
theorem mcs_box_diamond
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_B : ∀ (φ : Proposition Atom),
      Axioms (φ.imp (Proposition.box (Proposition.diamond φ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_phi : φ ∈ S) :
    (□◇φ) ∈ S :=
  mcs_mp_axiom h_implyK h_implyS h_mcs h_phi (h_B φ)

/-- If `box(phi -> psi) in S` and `box phi in S`, then `box psi in S` (using axiom K). -/
theorem mcs_box_mp
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ ψ : Proposition Atom} (h_box_imp : (□(φ → ψ)) ∈ S)
    (h_box_phi : (□φ) ∈ S) : (□ψ) ∈ S := by
  have h_k := mcs_mp_axiom h_implyK h_implyS h_mcs h_box_imp (h_K φ ψ)
  exact modal_implication_property h_implyK h_implyS h_mcs h_k h_box_phi

/-! ## Not-in-MCS Lemmas -/

/-- If `phi not in S` (MCS), then `neg phi in S`. -/
theorem mcs_neg_of_not_mem
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not : φ ∉ S) : (¬φ) ∈ S := by
  rcases modal_negation_complete h_implyK h_implyS h_mcs φ with h | h
  · exact absurd h h_not
  · exact h

/-- If `neg phi in S` (MCS), then `phi not in S`. -/
theorem mcs_not_mem_of_neg
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_neg : (¬φ) ∈ S) : φ ∉ S := by
  intro h_phi
  exact mcs_bot_not_mem h_mcs
    (modal_implication_property h_implyK h_implyS h_mcs h_neg h_phi)

/-- `phi in S <-> neg phi not in S` for MCS `S`. -/
theorem mcs_mem_iff_neg_not_mem
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} : φ ∈ S ↔ (¬φ) ∉ S := by
  constructor
  · intro h hn; exact mcs_bot_not_mem h_mcs
      (modal_implication_property h_implyK h_implyS h_mcs hn h)
  · intro h; rcases modal_negation_complete h_implyK h_implyS h_mcs φ with h' | h'
    · exact h'
    · exact absurd h' h

/-! ## Derivation Helpers for Box Witness -/

/-- Iterated deduction theorem: from `L |- phi`, derive `[] |- chain L phi` where
`chain` builds a right-nested implication. -/
noncomputable def iteratedDeduction
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ)))) :
    (L : List (Proposition Atom)) → (φ : Proposition Atom) →
    DerivationTree Axioms L φ → (ψ : Proposition Atom) ×'
      DerivationTree Axioms [] ψ ×'
      (∀ (S : Set (Proposition Atom)),
        SetMaximalConsistent Axioms S →
        (□ψ) ∈ S →
        (∀ x ∈ L, (□x) ∈ S) →
        (□φ) ∈ S)
  | [], φ, d => ⟨φ, d, fun _S _h_mcs h_box _ => h_box⟩
  | A :: L', φ, d => by
    have dt := deductionTheorem h_implyK h_implyS L' A φ d
    have ⟨ψ, d_empty, h_prop⟩ :=
      iteratedDeduction h_implyK h_implyS h_K L' (A → φ) dt
    exact ⟨ψ, d_empty, fun S h_mcs h_box_psi h_all_box => by
      have h_box_imp := h_prop S h_mcs h_box_psi
        (fun x hx => h_all_box x (List.mem_cons.mpr (Or.inr hx)))
      have h_box_a := h_all_box A (List.mem_cons.mpr (Or.inl rfl))
      exact mcs_box_mp h_implyK h_implyS h_K h_mcs h_box_imp h_box_a⟩

/-- From `L |- phi` where all elements of `L` have box-versions in MCS `S`,
derive `box phi in S`. -/
theorem derive_box_from_box_context
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {L : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms L φ)
    (h_all_box : ∀ ψ ∈ L, (□ψ) ∈ S) :
    (□φ) ∈ S := by
  have ⟨ψ, d_empty, h_prop⟩ :=
    iteratedDeduction h_implyK h_implyS h_K L φ d
  have d_box := DerivationTree.necessitation ψ d_empty
  have h_box_psi : (□ψ) ∈ S :=
    modal_closed_under_derivation h_implyK h_implyS h_mcs
      (L := []) (fun _ h => nomatch h) ⟨d_box⟩
  exact h_prop S h_mcs h_box_psi h_all_box

/-! ## Box Witness Consistency -/

/-- From `L |- bot` where `L <= {psi | box psi in S} union {neg phi}`,
derive `False`. -/
theorem derive_box_from_inconsistency
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
    (h_T : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp φ))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not_box : (□φ) ∉ S)
    {L : List (Proposition Atom)}
    (hL : ∀ x ∈ L, x ∈ {ψ | (□ψ) ∈ S} ∪ {(¬φ)})
    (d_bot : DerivationTree Axioms L ⊥) : False := by
  classical
  let L' := L.filter (· ≠ (¬φ))
  have h_L'_box : ∀ ψ ∈ L', (□ψ) ∈ S := by
    intro ψ hψ
    simp only [L', List.mem_filter, decide_eq_true_eq] at hψ
    rcases hL ψ hψ.1 with h | h
    · exact h
    · exact absurd h hψ.2
  by_cases h_neg_in_L : (¬φ) ∈ L
  · have h_perm : ∀ x, x ∈ L → x ∈ (¬φ) :: L' := by
      intro x hx
      by_cases hxn : x = (¬φ)
      · exact List.mem_cons.mpr (Or.inl hxn)
      · exact List.mem_cons.mpr (Or.inr (by
          simp only [L', List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
    have d_reord := DerivationTree.weakening L ((¬φ) :: L')
      ⊥ d_bot h_perm
    have d_dne := deductionTheorem h_implyK h_implyS L' (¬φ)
      ⊥ d_reord
    let neg_phi := (¬φ)
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
  · have h_all_S : ∀ x ∈ L, x ∈ S := by
      intro x hx
      rcases hL x hx with h | h
      · exact mcs_box_closure h_implyK h_implyS h_T h_mcs h
      · exact absurd (h ▸ hx) h_neg_in_L
    exact h_mcs.1 L h_all_S ⟨d_bot⟩

/-! ## Box Witness -/

/-- **Box Witness**: If `box phi not in S` and `S` is MCS, then there exists an MCS `T`
such that `forall psi, box psi in S -> psi in T` and `phi not in T`. -/
theorem mcs_box_witness
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
    (h_T : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp φ))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not_box : (□φ) ∉ S) :
    ∃ T : Set (Proposition Atom), SetMaximalConsistent Axioms T ∧
      (∀ ψ, (□ψ) ∈ S → ψ ∈ T) ∧ φ ∉ T := by
  let W := {ψ : Proposition Atom | (□ψ) ∈ S} ∪ {(¬φ)}
  have hW : SetConsistent Axioms W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    exact derive_box_from_inconsistency h_implyK h_implyS h_efq h_peirce h_K h_T
      h_mcs h_not_box hL d_bot
  obtain ⟨T, hWT, hT_mcs⟩ := modal_lindenbaum hW
  refine ⟨T, hT_mcs, ?_, ?_⟩
  · intro ψ h_box
    exact hWT (Set.mem_union_left _ h_box)
  · have h_neg : (¬φ) ∈ T :=
      hWT (Set.mem_union_right _ (Set.mem_singleton _))
    exact mcs_not_mem_of_neg h_implyK h_implyS hT_mcs h_neg

end Cslib.Logic.Modal
