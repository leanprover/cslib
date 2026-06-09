/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Mathlib.Order.Zorn
import Cslib.Foundations.Logic.Connectives

/-! # Generic Maximal Consistent Set (MCS) Foundations

This module provides a generic framework for maximal consistent set (MCS) theory,
parameterized over an abstract derivation relation. The key components are:

- `DerivationSystem`: A structure bundling a context-based derivability predicate with
  weakening, assumption, and modus ponens properties.
- `SetConsistent`, `SetMaximalConsistent`: Set-based consistency predicates.
- `consistent_chain_union`: Chain unions preserve set-consistency (input to Zorn's lemma).
- `set_lindenbaum`: Lindenbaum's lemma -- every consistent set extends to a maximally
  consistent set (via Zorn's lemma).
- `HasDeductionTheorem`: A separate hypothesis type for the deduction theorem.
- Closure properties (`closed_under_derivation`, `implication_property`,
  `negation_complete`) conditional on the deduction theorem.

Downstream modal (task 30) and temporal (task 31) metalogic tasks instantiate
`DerivationSystem` from their concrete `DerivationTree` types and supply deduction
theorem proofs.
-/

open Cslib.Logic

namespace Cslib.Logic.Metalogic

variable {F : Type*} [HasBot F] [HasImp F]

/-- A derivation system abstracts over logic-specific proof systems.

`F` is the formula type with bottom and implication.
`Deriv` maps a context (list of assumptions) and a conclusion to a `Prop`.

Required properties:
- `weakening`: derivations can be extended with additional assumptions
- `assumption`: any formula in the context is derivable from it
- `mp`: modus ponens is admissible -/
structure DerivationSystem (F : Type*) [HasBot F] [HasImp F] where
  /-- Context-based derivability: `Deriv Γ φ` means `φ` is derivable from `Γ`. -/
  Deriv : List F → F → Prop
  /-- Weakening: if `Γ ⊢ φ` and `Γ ⊆ Δ`, then `Δ ⊢ φ`. -/
  weakening : ∀ {Γ Δ : List F} {φ : F}, Deriv Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Deriv Δ φ
  /-- Assumption: if `φ ∈ Γ`, then `Γ ⊢ φ`. -/
  assumption : ∀ {Γ : List F} {φ : F}, φ ∈ Γ → Deriv Γ φ
  /-- Modus ponens: from `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`. -/
  mp : ∀ {Γ : List F} {φ ψ : F}, Deriv Γ (HasImp.imp φ ψ) → Deriv Γ φ → Deriv Γ ψ

/-! ## Consistency Definitions -/

/-- List-based consistency: `Γ` is consistent iff `Γ` does not derive `⊥`. -/
def Consistent (D : DerivationSystem F) (Γ : List F) : Prop :=
  ¬ D.Deriv Γ HasBot.bot

/-- Set-based consistency: `S` is set-consistent iff every finite subset is consistent. -/
def SetConsistent (D : DerivationSystem F) (S : Set F) : Prop :=
  ∀ L : List F, (∀ φ ∈ L, φ ∈ S) → Consistent D L

/-- Set-based maximal consistency: `S` is maximally consistent iff it is set-consistent
and adding any formula not in `S` makes it inconsistent. -/
def SetMaximalConsistent (D : DerivationSystem F) (S : Set F) : Prop :=
  SetConsistent D S ∧ ∀ φ : F, φ ∉ S → ¬ SetConsistent D (insert φ S)

/-- The collection of consistent supersets of `S`. Used as the domain for Zorn's lemma
in Lindenbaum's lemma. -/
def ConsistentSupersets (D : DerivationSystem F) (S : Set F) : Set (Set F) :=
  {T | S ⊆ T ∧ SetConsistent D T}

/-- In a set-consistent set, `φ` and `φ → ⊥` cannot both be members. -/
theorem set_consistent_not_both (D : DerivationSystem F) {S : Set F}
    (hcons : SetConsistent D S) {φ : F} (hφ : φ ∈ S)
    (hneg : HasImp.imp φ HasBot.bot ∈ S) : False := by
  have h := hcons [HasImp.imp φ HasBot.bot, φ] (by
    intro ψ hψ
    rw [List.mem_cons] at hψ
    rcases hψ with rfl | hψ
    · exact hneg
    · rw [List.mem_cons] at hψ; rcases hψ with rfl | hψ
      · exact hφ
      · simp at hψ)
  apply h
  exact D.mp (D.assumption (List.mem_cons.mpr (Or.inl rfl)))
    (D.assumption (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

/-- A set-consistent set `S` is in its own collection of consistent supersets. -/
theorem base_mem_consistent_supersets (D : DerivationSystem F) {S : Set F}
    (hS : SetConsistent D S) : S ∈ ConsistentSupersets D S :=
  ⟨Set.Subset.refl S, hS⟩

/-! ## Chain Union Lemmas -/

/-- Any finite list whose elements all belong to `⋃₀ C` (a chain union) has all its
elements in some single chain member. Proved by induction on the list. -/
lemma finite_list_in_chain_member {F' : Type*} {C : Set (Set F')}
    (hchain : IsChain (· ⊆ ·) C) (hCne : C.Nonempty)
    (L : List F') (h : ∀ φ ∈ L, φ ∈ ⋃₀ C) :
    ∃ S ∈ C, ∀ φ ∈ L, φ ∈ S := by
  induction L with
  | nil =>
    obtain ⟨S, hS⟩ := hCne
    exact ⟨S, hS, fun _ h => by simp at h⟩
  | cons a L ih =>
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨S₁, hS₁C, haS₁⟩ := Set.mem_sUnion.mp ha
    have hL : ∀ φ ∈ L, φ ∈ ⋃₀ C := fun φ hφ => h φ (List.mem_cons.mpr (Or.inr hφ))
    obtain ⟨S₂, hS₂C, hLS₂⟩ := ih hL
    rcases hchain.total hS₁C hS₂C with hsub | hsub
    · exact ⟨S₂, hS₂C, fun φ hφ => by
        rw [List.mem_cons] at hφ
        rcases hφ with rfl | hφ
        · exact hsub haS₁
        · exact hLS₂ φ hφ⟩
    · exact ⟨S₁, hS₁C, fun φ hφ => by
        rw [List.mem_cons] at hφ
        rcases hφ with rfl | hφ
        · exact haS₁
        · exact hsub (hLS₂ φ hφ)⟩

/-- The union of a nonempty chain of set-consistent sets is set-consistent.
This is the key input to Zorn's lemma in Lindenbaum's lemma. -/
theorem consistent_chain_union (D : DerivationSystem F)
    {C : Set (Set F)} (hchain : IsChain (· ⊆ ·) C) (hCne : C.Nonempty)
    (hcons : ∀ S ∈ C, SetConsistent D S) :
    SetConsistent D (⋃₀ C) := by
  intro L hL
  obtain ⟨S, hSC, hLS⟩ := finite_list_in_chain_member hchain hCne L hL
  exact hcons S hSC L hLS

/-! ## Lindenbaum's Lemma -/

/-- **Lindenbaum's Lemma**: Every set-consistent set can be extended to a maximally
consistent set. The proof applies `zorn_subset_nonempty` to the collection of consistent
supersets, using `consistent_chain_union` to verify the chain condition. -/
theorem set_lindenbaum (D : DerivationSystem F) {S : Set F}
    (hS : SetConsistent D S) :
    ∃ M : Set F, S ⊆ M ∧ SetMaximalConsistent D M := by
  -- Apply Zorn's lemma to the consistent supersets of S
  have ⟨M, hSM, hmax⟩ := zorn_subset_nonempty (ConsistentSupersets D S)
    (fun C hCsub hchain hCne => by
      -- The chain union is a consistent superset
      refine ⟨⋃₀ C, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      -- S ⊆ ⋃₀ C: S is contained in every chain member
      · intro x hx
        obtain ⟨T, hT⟩ := hCne
        exact Set.mem_sUnion.mpr ⟨T, hT, (hCsub hT).1 hx⟩
      -- ⋃₀ C is set-consistent
      · exact consistent_chain_union D hchain hCne (fun T hT => (hCsub hT).2))
    S (base_mem_consistent_supersets D hS)
  refine ⟨M, hSM, hmax.prop.2, fun φ hφ hcons => ?_⟩
  -- If φ ∉ M, then insert φ M strictly extends M in ConsistentSupersets
  have hins : insert φ M ∈ ConsistentSupersets D S :=
    ⟨Set.Subset.trans hSM (Set.subset_insert φ M), hcons⟩
  -- But M is maximal, so insert φ M = M
  have := hmax.eq_of_ge hins (Set.subset_insert φ M)
  -- This contradicts φ ∉ M since φ ∈ insert φ M = M
  exact hφ (this ▸ Set.mem_insert φ M)

/-! ## Deduction Theorem and Closure Properties -/

/-- The deduction theorem hypothesis for a derivation system. States that if
`φ :: Γ ⊢ ψ` then `Γ ⊢ φ → ψ`. This is NOT bundled into `DerivationSystem` because
the base MCS theory (consistency, chain union, Lindenbaum) does not require it.
Each logic supplies its own proof of this property. -/
def HasDeductionTheorem (D : DerivationSystem F) : Prop :=
  ∀ {Γ : List F} {φ ψ : F}, D.Deriv (φ :: Γ) ψ → D.Deriv Γ (HasImp.imp φ ψ)

/-- Helper: given a derivation `L ⊢ ψ` where `L ⊆ insert φ S`, produce a derivation
from `φ :: L_S ⊢ ψ` where `L_S` contains only elements of `S`. Uses classical
decidability for list filtering. -/
private lemma derives_from_insert_to_cons (D : DerivationSystem F)
    {S : Set F} {φ : F} {L : List F} {ψ : F}
    (hL : ∀ x ∈ L, x ∈ insert φ S) (hd : D.Deriv L ψ) :
    ∃ L_S : List F, (∀ x ∈ L_S, x ∈ S) ∧ D.Deriv (φ :: L_S) ψ := by
  classical
  let L_S := L.filter (fun x => decide (x ≠ φ) = true)
  refine ⟨L_S, ?_, ?_⟩
  · intro x hx
    simp only [L_S, List.mem_filter, decide_eq_true_eq] at hx
    rcases Set.mem_insert_iff.mp (hL x hx.1) with rfl | hxS
    · exact absurd rfl hx.2
    · exact hxS
  · exact D.weakening hd (fun x hx => by
      by_cases hxφ : x = φ
      · exact List.mem_cons.mpr (Or.inl hxφ)
      · exact List.mem_cons.mpr (Or.inr (by
          simp only [L_S, List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxφ⟩)))

/-- A maximally consistent set is closed under derivation, given the deduction theorem.

If `L ⊆ S` and `L ⊢ φ`, then `φ ∈ S`. Proof: assume `φ ∉ S`. By maximality,
`insert φ S` is inconsistent, so some `L' ⊆ insert φ S` derives `⊥`. Extract a
derivation `φ :: L_S ⊢ ⊥` where `L_S ⊆ S`, apply the deduction theorem to get
`L_S ⊢ φ → ⊥`. Combined with the weakened `L_S ++ L ⊢ φ` and `L_S ++ L ⊢ φ → ⊥`,
we get `L_S ++ L ⊢ ⊥` from `S`, contradicting set-consistency. -/
theorem SetMaximalConsistent.closed_under_derivation
    (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
    {S : Set F} (h_mcs : SetMaximalConsistent D S)
    {L : List F} (h_sub : ∀ ψ ∈ L, ψ ∈ S)
    {φ : F} (h_deriv : D.Deriv L φ) : φ ∈ S := by
  by_contra hφ
  -- By maximality, insert φ S is inconsistent
  have hinc := h_mcs.2 φ hφ
  unfold SetConsistent Consistent at hinc
  push Not at hinc
  obtain ⟨L', hL'sub, hL'bot⟩ := hinc
  -- Extract derivation from φ :: L_S where L_S ⊆ S
  obtain ⟨L_S, hL_S_sub, hcons_deriv⟩ := derives_from_insert_to_cons D hL'sub hL'bot
  -- Apply DT: L_S ⊢ φ → ⊥
  have h_neg : D.Deriv L_S (HasImp.imp φ HasBot.bot) := hdt hcons_deriv
  -- Weaken both to L_S ++ L
  have h_neg' : D.Deriv (L_S ++ L) (HasImp.imp φ HasBot.bot) :=
    D.weakening h_neg (fun x hx => List.mem_append.mpr (Or.inl hx))
  have h_phi : D.Deriv (L_S ++ L) φ :=
    D.weakening h_deriv (fun x hx => List.mem_append.mpr (Or.inr hx))
  -- MP: L_S ++ L ⊢ ⊥
  have h_bot : D.Deriv (L_S ++ L) HasBot.bot := D.mp h_neg' h_phi
  -- All elements of L_S ++ L are in S
  have h_all_S : ∀ ψ ∈ L_S ++ L, ψ ∈ S := by
    intro ψ hψ
    rcases List.mem_append.mp hψ with h | h
    · exact hL_S_sub ψ h
    · exact h_sub ψ h
  -- Contradiction with set-consistency
  exact h_mcs.1 (L_S ++ L) h_all_S h_bot

/-- Implication property: if `φ → ψ ∈ S` and `φ ∈ S`, then `ψ ∈ S`.
Follows directly from `closed_under_derivation` via modus ponens. -/
theorem SetMaximalConsistent.implication_property
    (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
    {S : Set F} (h_mcs : SetMaximalConsistent D S)
    {φ ψ : F} (h_imp : HasImp.imp φ ψ ∈ S) (h_phi : φ ∈ S) : ψ ∈ S :=
  closed_under_derivation D hdt h_mcs
    (L := [HasImp.imp φ ψ, φ])
    (fun x hx => by
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h_imp
      · rw [List.mem_cons] at hx; rcases hx with rfl | hx
        · exact h_phi
        · simp at hx)
    (D.mp (D.assumption (List.mem_cons.mpr (Or.inl rfl)))
      (D.assumption (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))

/-- Negation completeness: for any formula `φ`, either `φ ∈ S` or `(φ → ⊥) ∈ S`.
Uses the deduction theorem and maximality. -/
theorem SetMaximalConsistent.negation_complete
    (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
    {S : Set F} (h_mcs : SetMaximalConsistent D S)
    (φ : F) : φ ∈ S ∨ HasImp.imp φ HasBot.bot ∈ S := by
  by_contra h
  push Not at h
  obtain ⟨hφ, hneg⟩ := h
  -- φ ∉ S, so insert φ S is inconsistent
  have hinc := h_mcs.2 φ hφ
  unfold SetConsistent Consistent at hinc
  push Not at hinc
  obtain ⟨L', hL'sub, hL'bot⟩ := hinc
  -- Extract derivation from φ :: L_S where L_S ⊆ S
  obtain ⟨L_S, hL_S_sub, hcons_deriv⟩ := derives_from_insert_to_cons D hL'sub hL'bot
  -- Apply DT: L_S ⊢ φ → ⊥
  have h_neg : D.Deriv L_S (HasImp.imp φ HasBot.bot) := hdt hcons_deriv
  -- (φ → ⊥) ∈ S by closed_under_derivation
  have : HasImp.imp φ HasBot.bot ∈ S :=
    closed_under_derivation D hdt h_mcs hL_S_sub h_neg
  exact hneg this

end Cslib.Logic.Metalogic
