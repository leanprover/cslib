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

variable {Atom : Type u}

theorem IsValid_monotone {M : Type*} [PhaseSpace M]
    {G H : Fact M} (hGH : G ≤ H) (hG : G.IsValid) : H.IsValid := hGH hG

@[simp] theorem interpProp_atomDual {M : Type*} [PhaseSpace M]
    (v : Atom → Fact M) (a : Atom) :
    interpProp v (Proposition.atomDual a) = (v a)ᗮ := rfl

theorem dualFact_coe (M : Type*) [PhaseSpace M] (S : Set M) :
    (dualFact S) = S⫠ := by
  simp [dualFact]

@[simp] theorem interpProp_bang {M : Type*} [PhaseSpace M]
    (v : Atom → Fact M) (A : Proposition Atom) :
    interpProp v (!A) = (!(interpProp v A)) := rfl

@[simp] theorem interpProp_bot {M : Type*} [PhaseSpace M] (v : Atom → Fact M) :
    interpProp v ⊥ = ⊥ := rfl

@[simp] theorem interpProp_one {M : Type*} [PhaseSpace M] (v : Atom → Fact M) :
    interpProp v 1 = 1 := rfl

@[simp] theorem interpProp_oplus {M : Type*} [PhaseSpace M]
    (v : Atom → Fact M) (A B : Proposition Atom) :
    interpProp v (A ⊕ B) = (interpProp v A ⊕ interpProp v B : Fact M) := rfl

@[simp] theorem interpProp_parr {M : Type*} [PhaseSpace M]
    (v : Atom → Fact M) (A B : Proposition Atom) :
    interpProp v (A ⅋ B) = (interpProp v A ⅋ interpProp v B) := rfl

@[simp] theorem interpProp_quest {M : Type*} [PhaseSpace M]
    (v : Atom → Fact M) (A : Proposition Atom) :
    interpProp v (ʔA) = (ʔ(interpProp v A)) := rfl

@[simp] theorem interpProp_tensor {M : Type*} [PhaseSpace M]
    (v : Atom → Fact M) (A B : Proposition Atom) :
    interpProp v (A ⊗ B) = (interpProp v A ⊗ interpProp v B) := rfl

@[simp] theorem interpProp_top {M : Type*} [PhaseSpace M] (v : Atom → Fact M) :
    interpProp v (⊤ : Proposition Atom) = ⊤ := rfl

@[simp] theorem interpProp_with {M : Type*} [PhaseSpace M]
    (v : Atom → Fact M) (A B : Proposition Atom) :
    interpProp v (A & B) = (interpProp v A & interpProp v B) := rfl

/-! ## Exponential structural lemmas -/

theorem quest_contract_le {M : Type*} [PhaseSpace M] (G : Fact M) :
    (ʔG ⅋ ʔG) ≤ ʔG := by
  intro m hm x ⟨hxG, hxI⟩
  exact hxI.1.eq ▸ hm (x * x) (Set.mem_mul.mpr ⟨x, orth_extensive _ ⟨hxG, hxI⟩,
    x, orth_extensive _ ⟨hxG, hxI⟩, rfl⟩)

theorem quest_le {M : Type*} [PhaseSpace M] (G : Fact M) : G ≤ ʔG := by
  intro x hx y ⟨hy, _⟩; exact mul_comm y x ▸ hy x hx

theorem bot_le_quest {M : Type*} [PhaseSpace M] (G : Fact M) :
    ⊥ ≤ ʔG := by
  intro m hm x ⟨_, hxI⟩; exact mul_comm m x ▸ (mem_one.mp hxI.2) m hm

theorem quest_idem_le {M : Type*} [PhaseSpace M] {G : Fact M} :
    ʔ(ʔG) ≤ ʔG := by
  intro m hm x hx; exact hm x ⟨fun y hy => mul_comm x y ▸ hy x hx, hx.2⟩

theorem quest_monotone {M : Type*} [PhaseSpace M] {G H : Fact M}
    (hGH : G ≤ H) : (ʔG : Fact M) ≤ ʔH := by
  intro x hx y ⟨hyH, hyI⟩; exact hx y ⟨orth_antitone hGH hyH, hyI⟩

theorem tensor_mem_inter_I_of_mem_inter_I {M : Type*} [PhaseSpace M]
    {G H : Fact M} {g h : M}
    (hg : g ∈ (G : Set M) ∩ I) (hh : h ∈ (H : Set M) ∩ I) :
    g * h ∈ ((G ⊗ H) : Set M) ∩ I :=
  ⟨mul_subset_tensor (Set.mul_mem_mul hg.1 hh.1),
   hg.2.1.mul hh.2.1, mul_mem_one hg.2.2 hh.2.2⟩

theorem mul_inter_I_subset_tensor_inter_I {M : Type*} [PhaseSpace M] {G H : Fact M} :
    Set.image2 (· * ·) ((G : Set M) ∩ I) ((H : Set M) ∩ I) ⊆
    ((G ⊗ H : Fact M) : Set M) ∩ I := by
  rintro _ ⟨g, hg, h, hh, rfl⟩; exact tensor_mem_inter_I_of_mem_inter_I hg hh

theorem bang_tensor_le {M : Type*} [PhaseSpace M] {G H : Fact M} :
    (bang G ⊗ bang H : Fact M) ≤ bang (G ⊗ H) := by
  rw [show (bang G ⊗ bang H) ≤ bang (G ⊗ H) ↔
    (bang G : Set M) * bang H ⊆ bang (G ⊗ H)
    from dual_dual_subset_Fact_iff]
  have step1 : (bang G : Set M) * bang H ⊆
      (((G : Set M) ∩ I) * ((H : Set M) ∩ I))⫠⫠ := by
    change ((bang G).carrier * (bang H).carrier) ⊆ _
    simp only [bang, dualFact, mk_dual, mk_subset]
    exact tensor_assoc_aux
  have step2 : ((G : Set M) ∩ I) * ((H : Set M) ∩ I) ⊆
      ((G ⊗ H : Fact M) : Set M) ∩ I := mul_inter_I_subset_tensor_inter_I
  exact step1.trans (dual_dual_subset_Fact_iff.mpr (step2.trans (orth_extensive _)))

/-! ## Duality between ! and ? -/

theorem quest_neg_set (M : Type*) [PhaseSpace M] (G : Fact M) :
    quest Gᗮ = ((@bang M _ G) : Set M)⫠ := by
  calc (@quest M _ (Gᗮ))
      = (((Gᗮ : Set M)⫠ ∩ I))⫠ := by
          simp only [quest, dualFact_coe]
    _ = (((G : Set M)⫠⫠ ∩ I))⫠ := by simp only [coe_neg]
    _ = (((G : Set M) ∩ I))⫠ := by
      grind [isFact, congrArg (fun S => (S ∩ I)⫠) G.property.symm]
    _ = ((bang (P := M) G : Fact M))⫠ := by
        simp only [bang, dualFact_coe, triple_orth]

theorem quest_neg (M : Type*) [PhaseSpace M] (G : Fact M) :
    (ʔ (Gᗮ)) = (!G)ᗮ := by
  apply SetLike.coe_injective; simp [quest_neg_set]

theorem bang_neg (M : Type*) [PhaseSpace M] (G : Fact M) :
    (!(Gᗮ)) = (ʔG)ᗮ := by
  have h' := congrArg (fun H => (Hᗮ)) (quest_neg M Gᗮ)
  simp_all only [Fact.neg_neg]

theorem quest_par_le {M : Type*} [PhaseSpace M] {G H : Fact M} :
    (ʔ(G ⅋ H)) ≤ ʔG ⅋ ʔH := by
  rw [← neg_le_neg_iff, neg_par, ← bang_neg _ G, ← bang_neg _ H,
    ← bang_neg _ (G ⅋ H), neg_par]
  exact bang_tensor_le

/-! ## Quest-stability of all-quest contexts -/

theorem interpSequent_allQuest_quest_stable {M : Type*} [PhaseSpace M]
    {v : Atom → Fact M} {Γ : Sequent Atom} (hQuest : Γ.allQuest) :
    ʔ(interpSequent M v Γ) ≤ interpSequent M v Γ := by
  induction Γ using Multiset.induction_on with
  | empty =>
    intro m hm
    exact mul_one m ▸
      hm 1 ⟨fun x hx => by rwa [one_mul], ⟨IsIdempotentElem.one, one_mem_one⟩⟩
  | @cons A Γ ih =>
    cases A <;> simp only [Sequent.allQuest, Multiset.map_cons,
      Multiset.fold_cons_left, Bool.false_and, Bool.false_eq_true] at hQuest ⊢
    simp only [interpSequent_cons, interpProp_quest]
    exact le_trans quest_par_le (par_le_par quest_idem_le (ih hQuest))

/-! ## Validity helpers -/

theorem valid_par_implies_neg_le {M : Type*} [PhaseSpace M] {G H : Fact M}
    (hvalid : (G ⅋ H).IsValid) : Gᗮ ≤ H := by
  have himp := (@linImpl_iff_implies _ _ 1 Gᗮ H).1 (by aesop)
  intro x hx
  have := himp x hx; rwa [one_mul] at this

theorem bang_valid_of_stable_context {M : Type*} [PhaseSpace M] {G H : Fact M}
    (hstable : ʔH ≤ H) (hvalid : (G ⅋ H).IsValid) :
    ((bang G) ⅋ H).IsValid := by
  change 1 ∈ (bang G) ⅋ H
  rw [par_of_linImpl, ← quest_neg (M := M)]
  apply linImpl_iff_implies.mpr
  intro x (hx : x ∈ ʔ(Gᗮ))
  rw [one_mul]
  exact hstable (quest_monotone (valid_par_implies_neg_le hvalid) hx)

theorem bang_valid_of_allQuest {M : Type*} [PhaseSpace M]
    {v : Atom → Fact M} {a : Proposition Atom} {Γ : Sequent Atom}
    (hΓ : Γ.allQuest) (hall : (interpProp v a ⅋ interpSequent M v Γ).IsValid) :
    ((bang (interpProp v a)) ⅋ interpSequent M v Γ).IsValid :=
  bang_valid_of_stable_context (interpSequent_allQuest_quest_stable hΓ) hall

theorem interpProp_dual {M : Type*} [PhaseSpace M]
    (v : Atom → Fact M) (A : Proposition Atom) :
    interpProp v (A⫠) = (interpProp v A)ᗮ := by
  induction A with
  | atom _ | atomDual _ | one | zero | top | bot => simp [interpProp, Proposition.dual]
  | tensor _ _ ihA ihB | parr _ _ ihA ihB =>
    simp [interpProp, Proposition.dual, ihA, ihB, neg_tensor, neg_par]
  | oplus _ _ ihA ihB | «with» _ _ ihA ihB =>
    simp [interpProp, Proposition.dual, ihA, ihB, neg_plus, neg_with]
  | bang _ ih => simp only [interpProp, Proposition.dual, ih]; exact quest_neg ..
  | quest _ ih => simp only [interpProp, Proposition.dual, ih]; exact bang_neg ..

theorem ax_valid {M : Type*} [PhaseSpace M] (v : Atom → Fact M) (A : Proposition Atom) :
    (interpProp v A ⅋ (interpProp v A)ᗮ).IsValid := by
  change (1 : M) ∈ interpProp v A ⅋ (interpProp v A)ᗮ
  rw [par_of_linImpl]
  apply linImpl_iff_implies.mpr
  intro x hx; rw [one_mul]; exact hx

theorem cut_valid {M : Type*} [PhaseSpace M] {v : Atom → Fact M}
    {A : Proposition Atom} {Γ Δ : Sequent Atom}
    (hΓ : (interpProp v A ⅋ interpSequent M v Γ).IsValid)
    (hΔ : ((interpProp v A)ᗮ ⅋ interpSequent M v Δ).IsValid) :
    (interpSequent M v Γ ⅋ interpSequent M v Δ).IsValid := by
  set G := interpSequent M v Γ
  set H := interpSequent M v Δ
  set F := interpProp v A
  exact IsValid_monotone
    (par_le_par le_rfl (le_trans (orth_antitone (valid_par_implies_neg_le hΓ))
    (valid_par_implies_neg_le hΔ)))
    (by change (1 : M) ∈ G ⅋ Gᗮ; rw [par_of_linImpl]
        apply linImpl_iff_implies.mpr; intro x hx; rw [one_mul]; exact hx)

theorem quest_valid_of_valid {M : Type*} [PhaseSpace M] {G : Fact M}
    (hG : G.IsValid) : (ʔG).IsValid :=
  IsValid_monotone (quest_le G) hG

/-! ## Soundness -/

theorem soundness (Γ : Sequent Atom) :
    Derivable Γ → ∀ (M : Type*) [PhaseSpace M] (v : Atom → Fact M),
    (interpSequent M v Γ).IsValid := by
  intro ⟨p⟩ M _ v
  induction p with
  | ax =>
    rename_i a
    simp only [show ({a, a⫠} : Sequent Atom) = a ::ₘ (a⫠ ::ₘ 0) from by simp,
      interpSequent_cons, interpSequent_nil, par_bot, interpProp_dual]
    exact ax_valid v a
  | cut _ _ ihp ihq =>
    simp only [interpSequent_add]
    exact cut_valid (by aesop)
      (by grind [interpSequent_cons, interpProp_dual])
  | one =>
    simp only [show ({1} : Sequent Atom) = 1 ::ₘ 0
      from by simp, interpSequent_cons, interpSequent_nil, interpProp_one, par_bot]
    exact one_mem_one
  | bot _ ih => aesop
  | parr _ ih => aesop
  | tensor p q ihp ihq =>
    rename_i a Γ b Δ
    let A := interpProp v a; let B := interpProp v b
    let G := interpSequent M v Γ; let H := interpSequent M v Δ
    have hAG : (A ⅋ G).IsValid := by aesop
    have hBH : (B ⅋ H).IsValid := by aesop
    have hA := valid_par_implies_neg_le hAG
    have hB := valid_par_implies_neg_le hBH
    have hgoal : ((A ⊗ B) ⅋ (G ⅋ H)).IsValid := by
      change 1 ∈ (A ⊗ B) ⅋ (G ⅋ H)
      simp only [par_of_linImpl, neg_tensor]
      exact (@linImpl_iff_implies _ _ 1 (Aᗮ ⅋ Bᗮ) (G ⅋ H)).2
        (fun x hx => by rw [one_mul]; exact par_le_par hA hB hx)
    grind [interpSequent_cons, interpSequent_add, interpProp_tensor, par_assoc]
  | oplus₁ _ ih =>
    simp only [interpSequent_cons, interpProp_oplus] at ih ⊢
    exact IsValid_monotone (par_le_par le_plus_left le_rfl) ih
  | oplus₂ _ ih =>
    simp only [interpSequent_cons, interpProp_oplus] at ih ⊢
    exact IsValid_monotone (par_le_par le_plus_right le_rfl) ih
  | «with» _ _ ihp ihq =>
    simp only [interpSequent_cons, interpProp_with, with_par_distrib]
    constructor
    · simp only [interpSequent_cons] at ihp; exact ihp
    · simp only [interpSequent_cons] at ihq; exact ihq
  | top => simp only [interpSequent_cons, interpProp_top, top_par]; trivial
  | quest _ ih =>
    simp only [interpSequent_cons, interpProp_quest] at ih ⊢
    exact IsValid_monotone (par_le_par (quest_le _) le_rfl) ih
  | weaken p ih =>
    rename_i Γ a
    simp only [interpSequent_cons, interpProp_quest]
    have hle : interpSequent M v Γ ≤
        (quest (interpProp v a) ⅋ interpSequent M v Γ) := by
      have := (par_le_par (bot_le_quest (interpProp v a)) le_rfl :
        (⊥ ⅋ interpSequent M v Γ) ≤ _)
      simp only [bot_par] at this; exact this
    exact IsValid_monotone hle ih
  | contract _ ih =>
    simp only [interpSequent_cons, interpProp_quest] at ih ⊢
    rw [← par_assoc] at ih
    exact IsValid_monotone (par_le_par (quest_contract_le _) le_rfl) ih
  | bang hQuestCtx _ ih =>
    simp only [interpSequent_cons, interpProp_bang]
    simp only [interpSequent_cons] at ih
    exact bang_valid_of_allQuest hQuestCtx ih

end CLL
end Cslib
