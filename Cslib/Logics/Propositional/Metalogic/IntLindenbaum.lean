/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Metalogic.DeductionTheorem
public import Cslib.Logics.Propositional.Metalogic.MCS
public import Cslib.Logics.Propositional.Metalogic.Soundness

/-! # Deductively Closed Consistent Sets for Intuitionistic Propositional Logic

This module defines DCCS for IntPropAxiom and proves the implication witness lemma.

## References

* CZ Section 5.1, Theorem 2.43
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open Cslib.Logic.Helpers

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## IntPropAxiom helper hypotheses -/

private def int_h_implyK :
    ∀ (φ ψ : PL.Proposition Atom), IntPropAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

private def int_h_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    IntPropAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

/-! ## DCCS Definition -/

/-- A deductively closed consistent set (DCCS) for IntPropAxiom. -/
def IntDCCS (S : Set (PL.Proposition Atom)) : Prop :=
  PropSetConsistent IntPropAxiom S ∧
  ∀ (L : List (PL.Proposition Atom)) (φ : PL.Proposition Atom),
    (∀ x ∈ L, x ∈ S) → (propDerivationSystem IntPropAxiom).Deriv L φ → φ ∈ S

/-! ## Basic DCCS Properties -/

/-- `⊥ ∉ S` for any IntDCCS `S`. -/
theorem int_dccs_bot_not_mem {S : Set (PL.Proposition Atom)}
    (h : IntDCCS S) : (⊥ : PL.Proposition Atom) ∉ S := by
  intro h_bot
  exact h.1 [⊥]
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h_bot)
    ((propDerivationSystem IntPropAxiom).assumption (List.mem_cons.mpr (Or.inl rfl)))

/-- Modus ponens closure: if `φ → ψ ∈ S` and `φ ∈ S`, then `ψ ∈ S`. -/
theorem int_dccs_imp_property {S : Set (PL.Proposition Atom)}
    (h : IntDCCS S) {φ ψ : PL.Proposition Atom}
    (h_imp : (φ → ψ) ∈ S) (h_phi : φ ∈ S) : ψ ∈ S := by
  apply h.2 [(φ → ψ), φ] ψ
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  · exact (propDerivationSystem IntPropAxiom).mp
      ((propDerivationSystem IntPropAxiom).assumption
        (List.mem_cons.mpr (Or.inl rfl)))
      ((propDerivationSystem IntPropAxiom).assumption
        (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

/-! ## EFQ Composition Derivation -/

/-- `[¬φ] ⊢ φ → ψ` via EFQ composition. -/
noncomputable def intNegPhiImpPsi (φ ψ : PL.Proposition Atom) :
    DerivationTree IntPropAxiom [Proposition.neg φ] (φ.imp ψ) :=
  let efq_ax := DerivationTree.ax (Atom := Atom) [] (Proposition.bot.imp ψ) (.efq ψ)
  let ik := DerivationTree.ax (Atom := Atom) []
    ((Proposition.bot.imp ψ).imp (φ.imp (Proposition.bot.imp ψ)))
    (.implyK (Proposition.bot.imp ψ) φ)
  let step3 := DerivationTree.modus_ponens [] _ _ ik efq_ax
  let is_ax := DerivationTree.ax (Atom := Atom) []
    ((φ.imp (Proposition.bot.imp ψ)).imp ((Proposition.neg φ).imp (φ.imp ψ)))
    (.implyS φ Proposition.bot ψ)
  let step5 := DerivationTree.modus_ponens [] _ _ is_ax step3
  let step5w := DerivationTree.weakening [] [Proposition.neg φ] _ step5
    (fun _ h => nomatch h)
  DerivationTree.modus_ponens [Proposition.neg φ] (Proposition.neg φ) (φ.imp ψ)
    step5w
    (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))

/-- Prop-level EFQ composition. -/
theorem intNegPhiImpPsi_deriv (φ ψ : PL.Proposition Atom) :
    (propDerivationSystem IntPropAxiom).Deriv [Proposition.neg φ] (φ.imp ψ) :=
  ⟨intNegPhiImpPsi φ ψ⟩

/-! ## Compiling Derivations from Closure Elements -/

/-- If every element of L is derivable from some list in S,
then any φ derivable from L is also derivable from some list in S.

The proof works by induction on L, using the deduction theorem to
"cut" each element `a` out of the context, replacing it with its
witness derivation from S. -/
theorem int_deriv_from_closure_to_S {S : Set (PL.Proposition Atom)}
    (L : List (PL.Proposition Atom))
    (hL : ∀ x ∈ L, ∃ Lx : List (PL.Proposition Atom),
      (∀ y ∈ Lx, y ∈ S) ∧ (propDerivationSystem IntPropAxiom).Deriv Lx x)
    (φ : PL.Proposition Atom)
    (hd : (propDerivationSystem IntPropAxiom).Deriv L φ) :
    ∃ L' : List (PL.Proposition Atom),
      (∀ y ∈ L', y ∈ S) ∧ (propDerivationSystem IntPropAxiom).Deriv L' φ := by
  induction L generalizing φ with
  | nil => exact ⟨[], fun _ h => (nomatch h), hd⟩
  | cons a L' ih =>
    -- DT: L' ⊢ a → φ
    have hd_dt := prop_has_deduction_theorem int_h_implyK int_h_implyS hd
    -- IH on L' with formula (a → φ): get L_imp ⊆ S with L_imp ⊢ a → φ
    obtain ⟨L_imp, hL_imp_sub, hL_imp_deriv⟩ :=
      ih (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))) (a → φ) hd_dt
    -- Witness for a: La ⊆ S with La ⊢ a
    obtain ⟨La, hLa_sub, hLa_deriv⟩ := hL a (List.mem_cons.mpr (Or.inl rfl))
    -- Combine: La ++ L_imp ⊆ S, La ++ L_imp ⊢ φ (by MP)
    exact ⟨La ++ L_imp,
      fun y hy => by
        rw [List.mem_append] at hy
        exact hy.elim (hLa_sub y) (hL_imp_sub y),
      (propDerivationSystem IntPropAxiom).mp
        ((propDerivationSystem IntPropAxiom).weakening hL_imp_deriv
          (fun x hx => List.mem_append.mpr (Or.inr hx)))
        ((propDerivationSystem IntPropAxiom).weakening hLa_deriv
          (fun x hx => List.mem_append.mpr (Or.inl hx)))⟩

/-! ## Cut Lemma for Union Contexts -/

/-- If `L ⊢ ψ` and `L ⊆ S ∪ {φ}`, then `∃ L' ⊆ S, L' ⊢ φ → ψ`.

Uses `deductionWithMem` + `removeAll` to eliminate all occurrences of `φ`
from the derivation context. -/
theorem int_deriv_imp_of_union
    {S : Set (PL.Proposition Atom)}
    {L : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (hL : ∀ x ∈ L, x ∈ S ∪ {φ})
    (hd : (propDerivationSystem IntPropAxiom).Deriv L ψ) :
    ∃ L' : List (PL.Proposition Atom),
      (∀ x ∈ L', x ∈ S) ∧
      (propDerivationSystem IntPropAxiom).Deriv L' (φ → ψ) := by
  obtain ⟨d⟩ := hd
  -- Weaken to φ :: L, then DT gives L ⊢ φ → ψ
  have d_ext := DerivationTree.weakening L (φ :: L) ψ d
    (fun x hx => List.mem_cons.mpr (Or.inr hx))
  have d_dt := deductionTheorem int_h_implyK int_h_implyS L φ ψ d_ext
  by_cases hφL : φ ∈ L
  · -- φ ∈ L: use deductionWithMem to remove ALL occurrences of φ
    have d_mem := deductionWithMem int_h_implyK int_h_implyS L φ (φ → ψ) d_dt hφL
    -- d_mem : DerivationTree (removeAll L φ) (φ → (φ → ψ))
    -- removeAll L φ ⊆ S
    have h_rem_sub : ∀ x ∈ removeAll L φ, x ∈ S := by
      intro x hx
      simp only [removeAll, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not] at hx
      obtain ⟨hx_in, hx_ne⟩ := hx
      rcases hL x hx_in with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hx_ne
    -- Collapse φ → (φ → ψ) to φ → ψ via S-combinator + identity
    -- implyS: (φ → (φ → ψ)) → ((φ → φ) → (φ → ψ))
    let ctx := removeAll L φ
    have d_is : DerivationTree IntPropAxiom (Atom := Atom) ctx
        ((φ.imp (φ.imp ψ)).imp ((φ.imp φ).imp (φ.imp ψ))) :=
      .weakening [] ctx _ (.ax [] _ (.implyS φ φ ψ)) (fun _ h => nomatch h)
    -- MP: ctx ⊢ (φ → φ) → (φ → ψ)
    have d_step1 := DerivationTree.modus_ponens ctx _ _ d_is d_mem
    -- Build identity ⊢ φ → φ
    have d_k1 : DerivationTree IntPropAxiom (Atom := Atom) [] (φ.imp ((φ.imp φ).imp φ)) :=
      .ax [] _ (.implyK φ (φ.imp φ))
    have d_s1 : DerivationTree IntPropAxiom (Atom := Atom) []
        ((φ.imp ((φ.imp φ).imp φ)).imp ((φ.imp (φ.imp φ)).imp (φ.imp φ))) :=
      .ax [] _ (.implyS φ (φ.imp φ) φ)
    have d_mp1 := DerivationTree.modus_ponens [] _ _ d_s1 d_k1
    have d_k2 : DerivationTree IntPropAxiom (Atom := Atom) [] (φ.imp (φ.imp φ)) :=
      .ax [] _ (.implyK φ φ)
    have d_id := DerivationTree.modus_ponens [] _ _ d_mp1 d_k2
    have d_id_w := DerivationTree.weakening [] ctx _ d_id (fun _ h => nomatch h)
    -- MP: ctx ⊢ φ → ψ
    have d_final := DerivationTree.modus_ponens ctx _ _ d_step1 d_id_w
    exact ⟨ctx, h_rem_sub, ⟨d_final⟩⟩
  · -- φ ∉ L: L ⊆ S already
    have hL_S : ∀ x ∈ L, x ∈ S := by
      intro x hx
      rcases hL x hx with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hx) hφL
    exact ⟨L, hL_S, ⟨d_dt⟩⟩

/-! ## Deductive Closure -/

/-- The deductive closure of a set `S` w.r.t. IntPropAxiom. -/
def intDeductiveClosure (S : Set (PL.Proposition Atom)) :
    Set (PL.Proposition Atom) :=
  {φ | ∃ L : List (PL.Proposition Atom),
    (∀ x ∈ L, x ∈ S) ∧ (propDerivationSystem IntPropAxiom).Deriv L φ}

/-- `S ⊆ intDeductiveClosure S`. -/
theorem int_subset_deductive_closure (S : Set (PL.Proposition Atom)) :
    S ⊆ intDeductiveClosure S :=
  fun φ hφ => ⟨[φ],
    fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ hφ,
    (propDerivationSystem IntPropAxiom).assumption (List.mem_cons.mpr (Or.inl rfl))⟩

/-- The deductive closure is deductively closed. -/
theorem intDeductiveClosure_dccs_closed (S : Set (PL.Proposition Atom))
    (L : List (PL.Proposition Atom)) (φ : PL.Proposition Atom)
    (hL : ∀ x ∈ L, x ∈ intDeductiveClosure S)
    (hd : (propDerivationSystem IntPropAxiom).Deriv L φ) :
    φ ∈ intDeductiveClosure S :=
  int_deriv_from_closure_to_S L (fun x hx => hL x hx) φ hd

/-- If `S` is consistent, the deductive closure of `S` is consistent. -/
theorem intDeductiveClosure_consistent {S : Set (PL.Proposition Atom)}
    (hS : PropSetConsistent IntPropAxiom S) :
    PropSetConsistent IntPropAxiom (intDeductiveClosure S) := by
  intro L hL hd
  obtain ⟨L', hL'_sub, hL'_deriv⟩ :=
    int_deriv_from_closure_to_S L (fun x hx => hL x hx) _ hd
  exact hS L' hL'_sub hL'_deriv

/-- The deductive closure of a consistent set is a DCCS. -/
theorem intDeductiveClosure_is_dccs {S : Set (PL.Proposition Atom)}
    (hS : PropSetConsistent IntPropAxiom S) :
    IntDCCS (intDeductiveClosure S) :=
  ⟨intDeductiveClosure_consistent hS,
   fun L φ hL hd => intDeductiveClosure_dccs_closed S L φ hL hd⟩

/-! ## Implication Witness Lemma -/

/-- **Implication Witness Lemma**: If `S` is IntDCCS and `φ → ψ ∉ S`,
then the deductive closure of `S ∪ {φ}` is a DCCS `T ⊇ S` with
`φ ∈ T` and `ψ ∉ T`. -/
theorem int_imp_witness {S : Set (PL.Proposition Atom)}
    (h_dccs : IntDCCS S) {φ ψ : PL.Proposition Atom}
    (h_not : (φ → ψ) ∉ S) :
    ∃ T : Set (PL.Proposition Atom),
      S ⊆ T ∧ IntDCCS T ∧ φ ∈ T ∧ ψ ∉ T := by
  have h_cons_union : PropSetConsistent IntPropAxiom (S ∪ {φ}) := by
    intro L hL hd
    obtain ⟨L', hL'_sub, hL'_deriv⟩ := int_deriv_imp_of_union hL hd
    have h_neg_phi : (¬φ) ∈ S := h_dccs.2 L' _ hL'_sub hL'_deriv
    have h_imp_psi : (φ → ψ) ∈ S := by
      apply h_dccs.2 [(¬φ)] (φ → ψ)
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h_neg_phi
      · exact intNegPhiImpPsi_deriv φ ψ
    exact h_not h_imp_psi
  refine ⟨intDeductiveClosure (S ∪ {φ}), ?_, ?_, ?_, ?_⟩
  · exact Set.Subset.trans Set.subset_union_left (int_subset_deductive_closure _)
  · exact intDeductiveClosure_is_dccs h_cons_union
  · exact int_subset_deductive_closure _ (Set.mem_union_right S (Set.mem_singleton_iff.mpr rfl))
  · intro ⟨L, hL_sub, hL_deriv⟩
    obtain ⟨L', hL'_sub, hL'_deriv⟩ := int_deriv_imp_of_union hL_sub hL_deriv
    exact h_not (h_dccs.2 L' _ hL'_sub hL'_deriv)

/-! ## Int Theorems Form a DCCS -/

/-- IntPropAxiom is consistent: `[] ⊬ ⊥`. -/
private noncomputable def lift_int_to_cl {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree IntPropAxiom Γ φ) :
    DerivationTree PropositionalAxiom Γ φ := by
  match d with
  | .ax Γ ψ h_ax => exact .ax Γ ψ h_ax.toProp
  | .assumption Γ ψ h_mem => exact .assumption Γ ψ h_mem
  | .modus_ponens Γ ψ χ d₁ d₂ =>
    exact .modus_ponens Γ ψ χ (lift_int_to_cl d₁) (lift_int_to_cl d₂)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact .weakening Γ' Δ ψ (lift_int_to_cl d') h_sub

/-- IntPropAxiom is consistent: `[] ⊬ ⊥`. -/
theorem int_consistent :
    ¬ Derivable (Atom := Atom) IntPropAxiom (⊥ : PL.Proposition Atom) := by
  intro ⟨d⟩
  have d_cl := lift_int_to_cl d
  exact prop_soundness d_cl (fun _ => True) (fun _ h => nomatch h)

/-- The set of IntPropAxiom-theorems `{ψ | Derivable IntPropAxiom ψ}` is a DCCS. -/
theorem int_theorems_dccs :
    IntDCCS ({ψ : PL.Proposition Atom | Derivable IntPropAxiom ψ}) := by
  constructor
  · -- Consistent
    intro L hL hd
    have hL_empty : ∀ x ∈ L, ∃ Lx : List (PL.Proposition Atom),
        (∀ y ∈ Lx, y ∈ (∅ : Set (PL.Proposition Atom))) ∧
        (propDerivationSystem IntPropAxiom).Deriv Lx x := by
      intro x hx
      obtain ⟨dx⟩ := (hL x hx : Derivable IntPropAxiom x)
      exact ⟨[], fun _ h => (nomatch h), ⟨dx⟩⟩
    obtain ⟨L', hL'_sub, hL'_deriv⟩ :=
      int_deriv_from_closure_to_S L hL_empty _ hd
    have hL'_nil : L' = [] := by
      by_contra h
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L' h
      exact (hL'_sub a ha).elim
    rw [hL'_nil] at hL'_deriv
    exact int_consistent hL'_deriv
  · -- Deductively closed
    intro L φ hL hd
    have hL_empty : ∀ x ∈ L, ∃ Lx : List (PL.Proposition Atom),
        (∀ y ∈ Lx, y ∈ (∅ : Set (PL.Proposition Atom))) ∧
        (propDerivationSystem IntPropAxiom).Deriv Lx x := by
      intro x hx
      obtain ⟨dx⟩ := (hL x hx : Derivable IntPropAxiom x)
      exact ⟨[], fun _ h => (nomatch h), ⟨dx⟩⟩
    obtain ⟨L', hL'_sub, hL'_deriv⟩ :=
      int_deriv_from_closure_to_S L hL_empty _ hd
    have hL'_nil : L' = [] := by
      by_contra h
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L' h
      exact (hL'_sub a ha).elim
    rw [hL'_nil] at hL'_deriv
    exact hL'_deriv

end Cslib.Logic.PL
