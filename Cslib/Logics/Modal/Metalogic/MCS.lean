/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.DeductionTheorem

/-! # Maximal Consistent Sets for S5 Modal Logic

This module instantiates the generic MCS framework (from `Consistency.lean`) for
S5 modal logic and proves modal-specific MCS properties needed for the canonical
model construction in the completeness theorem.

## Main Results

### Generic MCS properties (instantiated from Consistency.lean)
- `modal_lindenbaum`: Every consistent set extends to a maximally consistent set.
- `modal_closed_under_derivation`: Derivable formulas are in MCS.
- `modal_implication_property`: Modus ponens reflected in membership.
- `modal_negation_complete`: Either `φ` or `¬φ` is in every MCS.

### Modal-specific properties
- `mcs_box_closure`: If `□φ ∈ S` then `φ ∈ S` (via axiom T).
- `mcs_box_box`: If `□φ ∈ S` then `□□φ ∈ S` (via axiom 4).
- `mcs_bot_not_mem`: `⊥ ∉ S` for any MCS `S`.
- `mcs_box_witness`: If `□φ ∉ S` then there exists an MCS `T` with
  `∀ ψ, □ψ ∈ S → ψ ∈ T` and `φ ∉ T`.

## References

* Cslib/Foundations/Logic/Metalogic/Consistency.lean — generic MCS framework
* BimodalLogic/Theories/Bimodal/Metalogic/Core/MCSProperties.lean — reference pattern
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Abbreviations for readability -/

/-- Set consistency for the modal derivation system. -/
abbrev Modal.SetConsistent (S : Set (Proposition Atom)) : Prop :=
  Metalogic.SetConsistent modalDerivationSystem S

/-- Set maximal consistency for the modal derivation system. -/
abbrev Modal.SetMaximalConsistent (S : Set (Proposition Atom)) : Prop :=
  Metalogic.SetMaximalConsistent modalDerivationSystem S

/-! ## Generic MCS Properties (instantiated) -/

/-- Lindenbaum's lemma for modal logic: every consistent set extends to an MCS. -/
theorem modal_lindenbaum {S : Set (Proposition Atom)}
    (hS : Modal.SetConsistent S) :
    ∃ M : Set (Proposition Atom), S ⊆ M ∧ Modal.SetMaximalConsistent M :=
  Metalogic.set_lindenbaum modalDerivationSystem hS

/-- Derivable formulas are in MCS. -/
theorem modal_closed_under_derivation
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {L : List (Proposition Atom)} (h_sub : ∀ ψ ∈ L, ψ ∈ S)
    {φ : Proposition Atom} (h_deriv : modalDerivationSystem.Deriv L φ) : φ ∈ S :=
  Metalogic.SetMaximalConsistent.closed_under_derivation
    modalDerivationSystem modal_has_deduction_theorem h_mcs h_sub h_deriv

/-- Implication property: if `φ → ψ ∈ S` and `φ ∈ S`, then `ψ ∈ S`. -/
theorem modal_implication_property
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {φ ψ : Proposition Atom} (h_imp : Proposition.imp φ ψ ∈ S) (h_phi : φ ∈ S) : ψ ∈ S :=
  Metalogic.SetMaximalConsistent.implication_property
    modalDerivationSystem modal_has_deduction_theorem h_mcs h_imp h_phi

/-- Negation completeness: for any formula `φ`, either `φ ∈ S` or `¬φ ∈ S`. -/
theorem modal_negation_complete
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    (φ : Proposition Atom) : φ ∈ S ∨ Proposition.neg φ ∈ S :=
  Metalogic.SetMaximalConsistent.negation_complete
    modalDerivationSystem modal_has_deduction_theorem h_mcs φ

/-! ## Modal-Specific MCS Properties -/

/-- Helper: derive a formula from membership in an MCS using an axiom and MP. -/
theorem mcs_mp_axiom
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {φ ψ : Proposition Atom} (h_mem : φ ∈ S) (h_ax : ModalAxiom (φ.imp ψ)) : ψ ∈ S := by
  apply modal_closed_under_derivation h_mcs (L := [φ]) (fun x hx => by
    simp [List.mem_cons] at hx; exact hx ▸ h_mem)
  unfold modalDerivationSystem Deriv
  exact ⟨.modus_ponens [φ] φ ψ
    (.weakening [] [φ] (φ.imp ψ) (.ax [] _ h_ax) (fun _ h => nomatch h))
    (.assumption [φ] φ (List.mem_cons.mpr (Or.inl rfl)))⟩

/-- `⊥ ∉ S` for any MCS `S`. -/
theorem mcs_bot_not_mem
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S) :
    Proposition.bot ∉ S := by
  intro h_bot
  exact h_mcs.1 [Proposition.bot]
    (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h_bot)
    (by simp [modalDerivationSystem, Deriv]
        exact ⟨.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))⟩)

/-- If `□φ ∈ S` and `S` is MCS, then `φ ∈ S` (using axiom T: `□φ → φ`). -/
theorem mcs_box_closure
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {φ : Proposition Atom} (h_box : Proposition.box φ ∈ S) : φ ∈ S :=
  mcs_mp_axiom h_mcs h_box (.modalT φ)

/-- If `□φ ∈ S` and `S` is MCS, then `□□φ ∈ S` (using axiom 4: `□φ → □□φ`). -/
theorem mcs_box_box
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {φ : Proposition Atom} (h_box : Proposition.box φ ∈ S) :
    Proposition.box (Proposition.box φ) ∈ S :=
  mcs_mp_axiom h_mcs h_box (.modalFour φ)

/-- If `φ ∈ S` and `S` is MCS, then `□◇φ ∈ S` (using axiom B: `φ → □◇φ`). -/
theorem mcs_box_diamond
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {φ : Proposition Atom} (h_phi : φ ∈ S) :
    Proposition.box (Proposition.diamond φ) ∈ S :=
  mcs_mp_axiom h_mcs h_phi (.modalB φ)

/-- If `□(φ → ψ) ∈ S` and `□φ ∈ S`, then `□ψ ∈ S` (using axiom K). -/
theorem mcs_box_mp
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {φ ψ : Proposition Atom} (h_box_imp : Proposition.box (φ.imp ψ) ∈ S)
    (h_box_phi : Proposition.box φ ∈ S) : Proposition.box ψ ∈ S := by
  have h_k := mcs_mp_axiom h_mcs h_box_imp (.modalK φ ψ)
  exact modal_implication_property h_mcs h_k h_box_phi

/-! ## Not-in-MCS Lemmas -/

/-- If `φ ∉ S` (MCS), then `¬φ ∈ S`. -/
theorem mcs_neg_of_not_mem
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {φ : Proposition Atom} (h_not : φ ∉ S) : Proposition.neg φ ∈ S := by
  rcases modal_negation_complete h_mcs φ with h | h
  · exact absurd h h_not
  · exact h

/-- If `¬φ ∈ S` (MCS), then `φ ∉ S`. -/
theorem mcs_not_mem_of_neg
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {φ : Proposition Atom} (h_neg : Proposition.neg φ ∈ S) : φ ∉ S := by
  intro h_phi
  exact mcs_bot_not_mem h_mcs (modal_implication_property h_mcs h_neg h_phi)

/-- `φ ∈ S ↔ ¬φ ∉ S` for MCS `S`. -/
theorem mcs_mem_iff_neg_not_mem
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {φ : Proposition Atom} : φ ∈ S ↔ Proposition.neg φ ∉ S := by
  constructor
  · intro h hn; exact mcs_bot_not_mem h_mcs (modal_implication_property h_mcs hn h)
  · intro h; rcases modal_negation_complete h_mcs φ with h' | h'
    · exact h'
    · exact absurd h' h

/-! ## Derivation Helpers for Box Witness -/

/-- Iterated deduction theorem: from `L ⊢ φ`, derive `[] ⊢ chain L φ` where
`chain` builds a right-nested implication. Processes by repeatedly applying
the deduction theorem to the head element. -/
noncomputable def iterated_deduction :
    (L : List (Proposition Atom)) → (φ : Proposition Atom) →
    DerivationTree L φ → (ψ : Proposition Atom) ×' DerivationTree [] ψ ×'
      (∀ (S : Set (Proposition Atom)),
        Modal.SetMaximalConsistent S →
        Proposition.box ψ ∈ S →
        (∀ x ∈ L, Proposition.box x ∈ S) →
        Proposition.box φ ∈ S)
  | [], φ, d => ⟨φ, d, fun _S _h_mcs h_box _ => h_box⟩
  | A :: L', φ, d => by
    -- d : (A :: L') ⊢ φ
    -- Deduction theorem: L' ⊢ A → φ
    have dt := deduction_theorem L' A φ d
    -- IH on L' with (A → φ): get chain and property
    have ⟨ψ, d_empty, h_prop⟩ := iterated_deduction L' (A.imp φ) dt
    exact ⟨ψ, d_empty, fun S h_mcs h_box_psi h_all_box => by
      -- h_prop gives: □(A → φ) ∈ S from □ψ and □-versions of L'
      have h_box_imp := h_prop S h_mcs h_box_psi
        (fun x hx => h_all_box x (List.mem_cons.mpr (Or.inr hx)))
      -- □(A → φ) ∈ S and □A ∈ S → □φ ∈ S by K
      have h_box_a := h_all_box A (List.mem_cons.mpr (Or.inl rfl))
      exact mcs_box_mp h_mcs h_box_imp h_box_a⟩

/-- From `L ⊢ φ` where all elements of `L` have box-versions in MCS `S`,
derive `□φ ∈ S`.

Uses iterated deduction theorem to get `⊢ ψ` (empty context), necessitation to
get `⊢ □ψ`, then the chain property to distribute K and get `□φ ∈ S`. -/
theorem derive_box_from_box_context
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {L : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree L φ)
    (h_all_box : ∀ ψ ∈ L, Proposition.box ψ ∈ S) :
    Proposition.box φ ∈ S := by
  -- Get the empty-context derivation and the box-distribution property
  have ⟨ψ, d_empty, h_prop⟩ := iterated_deduction L φ d
  -- Necessitation: ⊢ □ψ
  have d_box := DerivationTree.necessitation ψ d_empty
  -- □ψ ∈ S (from empty derivation)
  have h_box_psi : Proposition.box ψ ∈ S :=
    modal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h) ⟨d_box⟩
  -- Apply the chain property
  exact h_prop S h_mcs h_box_psi h_all_box

/-! ## Box Witness Consistency -/

/-- From `L ⊢ ⊥` where `L ⊆ {ψ | □ψ ∈ S} ∪ {¬φ}`, derive `False` (i.e., `□φ ∈ S`
contradicts `□φ ∉ S`).

Handles two cases:
- `¬φ ∉ L`: all of L has box-versions in S, so L ⊆ S by box_closure, contradicting
  S consistent since L ⊢ ⊥.
- `¬φ ∈ L`: use deduction theorem to extract φ from the inconsistency via double
  negation, then necessitation + K distribution to get □φ ∈ S. -/
theorem derive_box_from_inconsistency
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {φ : Proposition Atom} (h_not_box : Proposition.box φ ∉ S)
    {L : List (Proposition Atom)}
    (hL : ∀ x ∈ L, x ∈ {ψ | Proposition.box ψ ∈ S} ∪ {Proposition.neg φ})
    (d_bot : DerivationTree L Proposition.bot) : False := by
  classical
  -- Separate L into box-members and ¬φ
  let L' := L.filter (· ≠ Proposition.neg φ)
  -- All elements of L' have □-versions in S
  have h_L'_box : ∀ ψ ∈ L', Proposition.box ψ ∈ S := by
    intro ψ hψ
    simp only [L', List.mem_filter, decide_eq_true_eq] at hψ
    rcases hL ψ hψ.1 with h | h
    · exact h
    · exact absurd h hψ.2
  -- Check if ¬φ ∈ L
  by_cases h_neg_in_L : Proposition.neg φ ∈ L
  · -- ¬φ ∈ L. Weaken to (¬φ :: L') context, then deduction theorem.
    have h_perm : ∀ x, x ∈ L → x ∈ Proposition.neg φ :: L' := by
      intro x hx
      by_cases hxn : x = Proposition.neg φ
      · exact List.mem_cons.mpr (Or.inl hxn)
      · exact List.mem_cons.mpr (Or.inr (by
          simp only [L', List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
    have d_reord := DerivationTree.weakening L (Proposition.neg φ :: L') Proposition.bot
      d_bot h_perm
    -- Deduction theorem: L' ⊢ ¬φ → ⊥ = L' ⊢ (φ → ⊥) → ⊥
    have d_dne := deduction_theorem L' (Proposition.neg φ) Proposition.bot d_reord
    -- Derive φ from double negation using Peirce's law and EFQ
    let neg_phi := Proposition.neg φ
    -- EFQ: ⊥ → φ
    have efq : DerivationTree L' (Proposition.bot.imp φ) :=
      .weakening [] L' _ (.ax [] _ (.efq φ)) (fun _ h => nomatch h)
    -- implyK: (⊥→φ) → (neg_phi → (⊥→φ))
    have ik : DerivationTree L' ((Proposition.bot.imp φ).imp (neg_phi.imp (Proposition.bot.imp φ))) :=
      .weakening [] L' _ (.ax [] _ (.implyK (Proposition.bot.imp φ) neg_phi)) (fun _ h => nomatch h)
    -- L' ⊢ neg_phi → (⊥ → φ)
    have step_k := DerivationTree.modus_ponens L' _ _ ik efq
    -- implyS: (neg_phi → ⊥ → φ) → ((neg_phi → ⊥) → (neg_phi → φ))
    have is_ax : DerivationTree L'
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .weakening [] L' _ (.ax [] _ (.implyS neg_phi Proposition.bot φ)) (fun _ h => nomatch h)
    -- L' ⊢ (neg_phi → ⊥) → (neg_phi → φ)
    have step_s := DerivationTree.modus_ponens L' _ _ is_ax step_k
    -- d_dne : L' ⊢ neg_phi → ⊥ = L' ⊢ (φ→⊥) → ⊥
    -- step_s : L' ⊢ ((φ→⊥) → ⊥) → ((φ→⊥) → φ)
    -- Wait, neg_phi = φ → ⊥, so neg_phi → ⊥ = (φ→⊥) → ⊥.
    -- step_s : L' ⊢ (neg_phi → ⊥) → (neg_phi → φ)
    -- MP with d_dne: L' ⊢ neg_phi → φ = L' ⊢ (φ→⊥) → φ
    have step3 := DerivationTree.modus_ponens L' _ _ step_s d_dne
    -- Peirce: ((φ→⊥)→φ)→φ
    have peirce_ax : DerivationTree L' (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .weakening [] L' _ (.ax [] _ (.peirce φ Proposition.bot)) (fun _ h => nomatch h)
    -- MP: L' ⊢ φ
    have d_phi := DerivationTree.modus_ponens L' _ _ peirce_ax step3
    -- Now: L' ⊢ φ and all elements of L' have □-versions in S.
    -- derive_box_from_box_context: □φ ∈ S.
    exact h_not_box (derive_box_from_box_context h_mcs d_phi h_L'_box)
  · -- ¬φ ∉ L. All elements of L have box-versions in S, so in S by box_closure.
    have h_all_S : ∀ x ∈ L, x ∈ S := by
      intro x hx
      rcases hL x hx with h | h
      · exact mcs_box_closure h_mcs h
      · exact absurd (h ▸ hx) h_neg_in_L
    exact h_mcs.1 L h_all_S ⟨d_bot⟩

/-! ## Box Witness -/

/-- **Box Witness**: If `□φ ∉ S` and `S` is MCS, then there exists an MCS `T` such that
`∀ ψ, □ψ ∈ S → ψ ∈ T` and `φ ∉ T`.

This is the key lemma for the truth lemma's box case in the completeness proof.
The proof shows `{ψ | □ψ ∈ S} ∪ {¬φ}` is consistent (otherwise we could derive
`□φ ∈ S` via the deduction theorem + necessitation + K distribution), then extends
it to an MCS via Lindenbaum's lemma. -/
theorem mcs_box_witness
    {S : Set (Proposition Atom)} (h_mcs : Modal.SetMaximalConsistent S)
    {φ : Proposition Atom} (h_not_box : Proposition.box φ ∉ S) :
    ∃ T : Set (Proposition Atom), Modal.SetMaximalConsistent T ∧
      (∀ ψ, Proposition.box ψ ∈ S → ψ ∈ T) ∧ φ ∉ T := by
  -- The witness set
  let W := {ψ : Proposition Atom | Proposition.box ψ ∈ S} ∪ {Proposition.neg φ}
  -- W is consistent
  have hW : Modal.SetConsistent W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    exact derive_box_from_inconsistency h_mcs h_not_box hL d_bot
  -- Extend W to MCS via Lindenbaum
  obtain ⟨T, hWT, hT_mcs⟩ := modal_lindenbaum hW
  refine ⟨T, hT_mcs, ?_, ?_⟩
  · -- ∀ ψ, □ψ ∈ S → ψ ∈ T
    intro ψ h_box
    exact hWT (Set.mem_union_left _ h_box)
  · -- φ ∉ T
    have h_neg : Proposition.neg φ ∈ T :=
      hWT (Set.mem_union_right _ (Set.mem_singleton _))
    exact mcs_not_mem_of_neg hT_mcs h_neg

end Cslib.Logic.Modal
