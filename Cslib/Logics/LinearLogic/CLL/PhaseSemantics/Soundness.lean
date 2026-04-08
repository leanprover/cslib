/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Bhavik Mehta, Aleph Prover
-/

module

public import Cslib.Logics.LinearLogic.CLL.Basic
public import Cslib.Logics.LinearLogic.CLL.PhaseSemantics.Basic

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# Soundness of phase semantics for CLL

This file proves that provable sequents of classical linear logic are valid in every
phase space under every valuation.

## Main results

* `interpProp_dual`: interpretation commutes with duality
* `ax_valid`: the axiom sequent is valid
* `cut_valid`: cut preserves validity
* `bang_valid_of_allQuest`: promotion is sound for all-quest contexts
* `soundness`: every provable sequent is semantically valid
-/

@[expose] public section

namespace Cslib
namespace CLL

open scoped Pointwise
open PhaseSpace PhaseSpace.Fact Logic InferenceSystem

universe u

variable {Atom : Type u} {M : Type*} [PhaseSpace M]

theorem Fact.isValid_monotone
    {G H : Fact M} (hGH : G ≤ H) (hG : G.IsValid) : H.IsValid := hGH hG

open Fact

@[simp] theorem interpProp_atomDual
    (v : Atom → Fact M) (a : Atom) :
    interpProp v (Proposition.atomDual a) = (v a)ᗮ := rfl

theorem dualFact_coe (S : Set M) :
    (dualFact S) = S⫠ := by
  simp [dualFact]

@[simp] theorem interpProp_bang
    (v : Atom → Fact M) (A : Proposition Atom) :
    interpProp v (!A) = (!(interpProp v A)) := rfl

@[simp] theorem interpProp_bot (v : Atom → Fact M) :
    interpProp v ⊥ = ⊥ := rfl

@[simp] theorem interpProp_one (v : Atom → Fact M) :
    interpProp v 1 = 1 := rfl

@[simp] theorem interpProp_oplus
    (v : Atom → Fact M) (A B : Proposition Atom) :
    interpProp v (A ⊕ B) = (interpProp v A ⊕ interpProp v B : Fact M) := rfl

@[simp] theorem interpProp_parr
    (v : Atom → Fact M) (A B : Proposition Atom) :
    interpProp v (A ⅋ B) = (interpProp v A ⅋ interpProp v B) := rfl

@[simp] theorem interpProp_quest
    (v : Atom → Fact M) (A : Proposition Atom) :
    interpProp v (ʔA) = (ʔ(interpProp v A)) := rfl

@[simp] theorem interpProp_tensor
    (v : Atom → Fact M) (A B : Proposition Atom) :
    interpProp v (A ⊗ B) = (interpProp v A ⊗ interpProp v B) := rfl

@[simp] theorem interpProp_top (v : Atom → Fact M) :
    interpProp v (⊤ : Proposition Atom) = ⊤ := rfl

@[simp] theorem interpProp_with
    (v : Atom → Fact M) (A B : Proposition Atom) :
    interpProp v (A & B) = (interpProp v A & interpProp v B) := rfl

/-! ## Exponential structural lemmas -/

theorem quest_contract_le (G : Fact M) :
    (ʔG ⅋ ʔG) ≤ ʔG := by
  intro m hm x ⟨hxG, hxI⟩
  exact hxI.1.eq ▸ hm (x * x) (Set.mem_mul.mpr ⟨x, orth_extensive _ ⟨hxG, hxI⟩,
    x, orth_extensive _ ⟨hxG, hxI⟩, rfl⟩)

theorem quest_le (G : Fact M) : G ≤ ʔG := by
  intro x hx y ⟨hy, _⟩
  exact mul_comm y x ▸ hy x hx

theorem bot_le_quest (G : Fact M) :
    ⊥ ≤ ʔG := by
  intro m hm x ⟨_, hxI⟩
  exact mul_comm m x ▸ (mem_one.mp hxI.2) m hm

theorem quest_idem_le {G : Fact M} :
    ʔ(ʔG) ≤ ʔG := by
  intro m hm x hx
  exact hm x ⟨fun y hy => mul_comm x y ▸ hy x hx, hx.2⟩

theorem quest_monotone {G H : Fact M}
    (hGH : G ≤ H) : (ʔG : Fact M) ≤ ʔH := by
  intro x hx y ⟨hyH, hyI⟩
  exact hx y ⟨orth_antitone hGH hyH, hyI⟩

theorem tensor_mem_inter_I_of_mem_inter_I
    {G H : Fact M} {g h : M}
    (hg : g ∈ (G : Set M) ∩ I) (hh : h ∈ (H : Set M) ∩ I) :
    g * h ∈ ((G ⊗ H) : Set M) ∩ I :=
  ⟨mul_subset_tensor (Set.mul_mem_mul hg.1 hh.1),
   hg.2.1.mul hh.2.1, mul_mem_one hg.2.2 hh.2.2⟩

theorem mul_inter_I_subset_tensor_inter_I {G H : Fact M} :
    Set.image2 (· * ·) ((G : Set M) ∩ I) ((H : Set M) ∩ I) ⊆
    ((G ⊗ H : Fact M) : Set M) ∩ I := by
  rintro _ ⟨g, hg, h, hh, rfl⟩
  exact tensor_mem_inter_I_of_mem_inter_I hg hh

theorem bang_tensor_le {G H : Fact M} :
    (bang G ⊗ bang H : Fact M) ≤ bang (G ⊗ H) := by
  rw [show (bang G ⊗ bang H) ≤ bang (G ⊗ H) ↔
    (bang G : Set M) * bang H ⊆ bang (G ⊗ H)
    from dual_dual_subset_Fact_iff]
  have step1 : (bang G : Set M) * bang H ⊆
      (((G : Set M) ∩ I) * ((H : Set M) ∩ I))⫠⫠ := by
    simp only [bang, dualFact, mk_dual, mk_subset]
    exact tensor_assoc_aux
  have step2 : ((G : Set M) ∩ I) * ((H : Set M) ∩ I) ⊆
      (G ⊗ H) ∩ I := mul_inter_I_subset_tensor_inter_I
  exact step1.trans (dual_dual_subset_Fact_iff.mpr (step2.trans (orth_extensive _)))

/-! ## Duality between ! and ? -/

theorem quest_neg_set (G : Fact M) :
    quest Gᗮ = ((@bang M _ G) : Set M)⫠ := by
  calc (@quest M _ (Gᗮ))
      = ((Gᗮ : Set M)⫠ ∩ I)⫠ := by
          simp only [quest, dualFact_coe]
    _ = ((G⫠⫠ ∩ I))⫠ := by simp only [coe_neg]
    _ = ((G ∩ I))⫠ := by
      grind [isFact, congrArg (fun S => (S ∩ I)⫠) G.property.symm]
    _ = ((bang (P := M) G : Fact M))⫠ := by
        simp only [bang, dualFact_coe, triple_orth]

theorem quest_neg (G : Fact M) :
    (ʔ (Gᗮ)) = (!G)ᗮ := by
  apply SetLike.coe_injective
  simp [quest_neg_set]

theorem bang_neg (G : Fact M) :
    (!(Gᗮ)) = (ʔG)ᗮ := by
  have h' := congrArg (fun H => (Hᗮ)) (quest_neg Gᗮ)
  simp_all only [Fact.neg_neg]

theorem quest_par_le {G H : Fact M} :
    (ʔ(G ⅋ H)) ≤ ʔG ⅋ ʔH := by
  rw [← neg_le_neg_iff, neg_par, ← bang_neg G, ← bang_neg H,
    ← bang_neg (G ⅋ H), neg_par]
  exact bang_tensor_le

/-! ## Quest-stability of all-quest contexts -/

theorem Sequent.toFact_allQuest_quest_stable
    {v : Atom → Fact M} {Γ : Sequent Atom} (hQuest : Γ.allQuest) :
    ʔ(Sequent.toFact M v Γ) ≤ Sequent.toFact M v Γ := by
  induction Γ using Multiset.induction_on with
  | empty =>
    intro m hm
    exact mul_one m ▸
      hm 1 ⟨fun x hx => by rwa [one_mul], ⟨IsIdempotentElem.one, one_mem_one⟩⟩
  | @cons A Γ ih =>
    cases A <;> simp only [Sequent.allQuest, Multiset.map_cons,
      Multiset.fold_cons_left, Bool.false_and, Bool.false_eq_true] at hQuest ⊢
    simp only [Sequent.toFact_cons, interpProp_quest]
    exact le_trans quest_par_le (par_le_par quest_idem_le (ih hQuest))

/-! ## Validity helpers -/

theorem isValid_par_iff {G H : Fact M} : (G ⅋ H).IsValid ↔ Gᗮ ≤ H := by
  constructor
  · intro hvalid x hx
    rw [par_of_linImpl] at hvalid
    have := linImpl_iff_implies.mp hvalid x hx
    rwa [one_mul] at this
  · intro h
    rw [Fact.IsValid, par_of_linImpl]
    exact linImpl_iff_implies.mpr fun x hx => by
      rw [one_mul]
      exact h hx

theorem bang_valid_of_stable_context {G H : Fact M}
    (hstable : ʔH ≤ H) (hvalid : (G ⅋ H).IsValid) :
    ((bang G) ⅋ H).IsValid := by
  rw [isValid_par_iff, ← quest_neg]
  exact le_trans (quest_monotone (isValid_par_iff.mp hvalid)) hstable

theorem bang_valid_of_allQuest
    {v : Atom → Fact M} {a : Proposition Atom} {Γ : Sequent Atom}
    (hΓ : Γ.allQuest) (hall : (interpProp v a ⅋ Sequent.toFact M v Γ).IsValid) :
    ((bang (interpProp v a)) ⅋ Sequent.toFact M v Γ).IsValid :=
  bang_valid_of_stable_context (Sequent.toFact_allQuest_quest_stable hΓ) hall

theorem interpProp_dual
    (v : Atom → Fact M) (A : Proposition Atom) :
    interpProp v (A⫠) = (interpProp v A)ᗮ := by
  induction A with
  | atom _ | atomDual _ | one | zero | top | bot => simp [interpProp, Proposition.dual]
  | tensor _ _ ihA ihB | parr _ _ ihA ihB =>
    simp [interpProp, Proposition.dual, ihA, ihB, neg_tensor, neg_par]
  | oplus _ _ ihA ihB | «with» _ _ ihA ihB =>
    simp [interpProp, Proposition.dual, ihA, ihB, neg_plus, neg_with]
  | bang _ ih =>
    simp only [interpProp, Proposition.dual, ih]
    exact quest_neg ..
  | quest _ ih =>
    simp only [interpProp, Proposition.dual, ih]
    exact bang_neg ..

theorem ax_valid (v : Atom → Fact M) (A : Proposition Atom) :
    (interpProp v A ⅋ (interpProp v A)ᗮ).IsValid :=
  isValid_par_iff.mpr le_rfl

theorem cut_valid {v : Atom → Fact M}
    {A : Proposition Atom} {Γ Δ : Sequent Atom}
    (hΓ : (interpProp v A ⅋ Sequent.toFact M v Γ).IsValid)
    (hΔ : ((interpProp v A)ᗮ ⅋ Sequent.toFact M v Δ).IsValid) :
    (Sequent.toFact M v Γ ⅋ Sequent.toFact M v Δ).IsValid := by
  exact isValid_monotone
    (par_le_par le_rfl (le_trans (orth_antitone (isValid_par_iff.mp hΓ))
    (isValid_par_iff.mp hΔ)))
    (isValid_par_iff.mpr le_rfl)

theorem quest_valid_of_valid {G : Fact M}
    (hG : G.IsValid) : (ʔG).IsValid :=
  isValid_monotone (quest_le G) hG

/-! ## Soundness -/

theorem soundness (Γ : Sequent Atom) :
    Derivable Γ → ∀ (M : Type*) [PhaseSpace M] (v : Atom → Fact M),
    (Sequent.toFact M v Γ).IsValid := by
  intro ⟨p⟩ M _ v
  induction p with
  | @ax a =>
    have : ({a, a⫠} : Sequent Atom) = a ::ₘ (a⫠ ::ₘ 0) := by simp
    simp only [this, Sequent.toFact_cons, Sequent.toFact_nil, par_bot, interpProp_dual]
    exact ax_valid v a
  | cut _ _ ihp ihq =>
    simp only [Sequent.toFact_add]
    exact cut_valid (by aesop)
      (by grind [Sequent.toFact_cons, interpProp_dual])
  | one =>
    have : ({1} : Sequent Atom) = 1 ::ₘ 0 := by simp
    simp only [this, Sequent.toFact_cons, Sequent.toFact_nil, interpProp_one, par_bot]
    exact one_mem_one
  | bot _ ih => aesop
  | parr _ ih => aesop
  | @tensor a Γ b Δ p q ihp ihq =>
    let A := interpProp v a; let B := interpProp v b
    let G := Sequent.toFact M v Γ; let H := Sequent.toFact M v Δ
    have hAG : (A ⅋ G).IsValid := by aesop
    have hBH : (B ⅋ H).IsValid := by aesop
    have hgoal : ((A ⊗ B) ⅋ (G ⅋ H)).IsValid := by
      rw [isValid_par_iff, neg_tensor]
      exact par_le_par (isValid_par_iff.mp hAG) (isValid_par_iff.mp hBH)
    grind [Sequent.toFact_cons, Sequent.toFact_add, interpProp_tensor, par_assoc]
  | oplus₁ _ ih =>
    simp only [Sequent.toFact_cons, interpProp_oplus] at ih ⊢
    exact isValid_monotone (par_le_par le_plus_left le_rfl) ih
  | oplus₂ _ ih =>
    simp only [Sequent.toFact_cons, interpProp_oplus] at ih ⊢
    exact isValid_monotone (par_le_par le_plus_right le_rfl) ih
  | «with» _ _ ihp ihq =>
    simp only [Sequent.toFact_cons, interpProp_with, with_par_distrib]
    constructor
    · simp only [Sequent.toFact_cons] at ihp
      exact ihp
    · simp only [Sequent.toFact_cons] at ihq
      exact ihq
  | top => simp only [Sequent.toFact_cons, interpProp_top, top_par]; trivial
  | quest _ ih =>
    simp only [Sequent.toFact_cons, interpProp_quest] at ih ⊢
    exact isValid_monotone (par_le_par (quest_le _) le_rfl) ih
  | weaken p ih =>
    rename_i Γ a
    simp only [Sequent.toFact_cons, interpProp_quest]
    have hle : Sequent.toFact M v Γ ≤
        (quest (interpProp v a) ⅋ Sequent.toFact M v Γ) := by
      have := (par_le_par (bot_le_quest (interpProp v a)) le_rfl :
        (⊥ ⅋ Sequent.toFact M v Γ) ≤ _)
      simp only [bot_par] at this
      exact this
    exact isValid_monotone hle ih
  | contract _ ih =>
    simp only [Sequent.toFact_cons, interpProp_quest] at ih ⊢
    rw [← par_assoc] at ih
    exact isValid_monotone (par_le_par (quest_contract_le _) le_rfl) ih
  | bang hQuestCtx _ ih =>
    simp only [Sequent.toFact_cons, interpProp_bang]
    simp only [Sequent.toFact_cons] at ih
    exact bang_valid_of_allQuest hQuestCtx ih

end CLL
end Cslib
