/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Data.Relation
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

@[expose] public section

set_option linter.unusedDecidableInType false

/-! # β-confluence for the λ-calculus -/

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation

/-- A parallel β-reduction step. -/
@[reduction_sys "ₚ"]
inductive Parallel : Term Var → Term Var → Prop
/-- Free variables parallel step to themselves. -/
| fvar (x : Var) : Parallel (fvar x) (fvar x)
/-- A parallel left and right congruence rule for application. -/
| app : Parallel L L' → Parallel M M' → Parallel (app L M) (app L' M')
/-- Congruence rule for lambda terms. -/
| abs (xs : Finset Var) :
    (∀ x ∉ xs, Parallel (m ^ fvar x) (m' ^ fvar x)) → Parallel (abs m) (abs m')
/-- A parallel β-reduction. -/
| beta (xs : Finset Var) :
    (∀ x ∉ xs, Parallel (m ^ fvar x) (m' ^ fvar x) ) →
    Parallel n n' →
    Parallel (app (abs m) n) (m' ^ n')

open Parallel

attribute [scoped grind .] Parallel.fvar Parallel.app
attribute [scoped grind cases] Parallel

variable {M M' N N' : Term Var}

/-- The left side of a parallel reduction is locally closed. -/
@[scoped grind →]
lemma para_lc_l (step : M ⭢ₚ N) : LC M  := by
  induction step
  case abs _ _ xs _ ih => exact LC.abs xs _ ih
  case beta => refine LC.app (LC.abs ?_ _ ?_) ?_ <;> assumption
  all_goals grind

/-- Parallel reduction is reflexive for locally closed terms. -/
@[scoped grind →]
lemma Parallel.lc_refl (M : Term Var) (lc : LC M) : M ⭢ₚ M := by
  induction lc
  all_goals constructor <;> assumption

variable [HasFresh Var] [DecidableEq Var]

/-- The right side of a parallel reduction is locally closed. -/
@[scoped grind →]
lemma para_lc_r (step : M ⭢ₚ N) : LC N := by
  induction step
  case abs _ _ xs _ ih => exact LC.abs xs _ ih
  case beta => refine beta_lc (LC.abs ?_ _ ?_) ?_ <;> assumption
  all_goals grind

omit [HasFresh Var] [DecidableEq Var] in
/-- A single β-reduction implies a single parallel reduction. -/
lemma step_to_para (step : M ⭢βᶠ N) : M ⭢ₚ N := by
  induction step
  case beta _ abs_lc _ => cases abs_lc with | abs xs _ => apply Parallel.beta xs <;> grind
  case abs xs _ _ => apply Parallel.abs xs; grind
  all_goals grind

open FullBeta in
/-- A single parallel reduction implies a multiple β-reduction. -/
lemma para_to_redex (para : M ⭢ₚ N) : M ↠βᶠ N := by
  induction para
  case fvar => constructor
  case app L L' R R' l_para m_para redex_l redex_m =>
    have : L.app R ↠βᶠ L'.app R := by grind
    grind [ReflTransGen.trans]
  case abs t t' xs _ ih =>
    apply redex_abs_cong xs
    grind
  case beta m m' n n' xs para_ih para_n redex_ih redex_n =>
    have m'_abs_lc : LC m'.abs := by
      apply LC.abs xs
      grind
    calc
      m.abs.app n ↠βᶠ
      m'.abs.app n :=
        redex_app_l_cong (redex_abs_cong xs (fun _ mem ↦ redex_ih _ mem)) (para_lc_l para_n)
      _           ↠βᶠ m'.abs.app n' := by grind
      _           ⭢βᶠ m' ^ n'       := beta m'_abs_lc (by grind)

/-- Multiple parallel reduction is equivalent to multiple β-reduction. -/
theorem parachain_iff_redex : M ↠ₚ N ↔ M ↠βᶠ N := by
  refine Iff.intro ?chain_redex ?redex_chain <;> intros h <;> induction h <;> try rfl
  case redex_chain redex chain => exact ReflTransGen.tail chain (step_to_para redex)
  case chain_redex para  redex => exact ReflTransGen.trans redex (para_to_redex para)

/-- Parallel reduction respects substitution. -/
@[scoped grind .]
lemma para_subst (x : Var) (pm : M ⭢ₚ M') (pn : N ⭢ₚ N') : M[x := N] ⭢ₚ M'[x := N'] := by
  induction pm with
  | beta =>
    rw [subst_open _ _ _ _ (by grind)]
    refine Parallel.beta (free_union Var) ?_ ?_ <;> grind
  | app => constructor <;> assumption
  | abs => grind [Parallel.abs (free_union Var)]
  | _ => grind

/-- Parallel substitution respects closing and opening. -/
lemma para_open_close (x y z) (para : M ⭢ₚ M') : M⟦z ↜ x⟧⟦z ↝ fvar y⟧ ⭢ₚ M'⟦z ↜ x⟧⟦z ↝ fvar y⟧ :=
  by grind

/-- Parallel substitution respects fresh opening. -/
lemma para_open_out (L : Finset Var) (mem : ∀ x, x ∉ L → (M ^ fvar x) ⭢ₚ N ^ fvar x)
    (para : M' ⭢ₚ N') : (M ^ M') ⭢ₚ (N ^ N') := by
  grind [fresh_exists <| free_union [fv] Var]

-- TODO: the Takahashi translation would be a much nicer and shorter proof, but I had difficultly
-- writing it for locally nameless terms.

-- adapted from https://github.com/ElifUskuplu/Stlc_deBruijn/blob/main/Stlc/confluence.lean
/-- Parallel reduction has the diamond property. -/
theorem para_diamond : Diamond (@Parallel Var) := by
  intros t t1 t2 tpt1
  revert t2
  induction tpt1 <;> intros t2 tpt2
  case fvar x => exact ⟨t2, by grind⟩
  case abs s1 s2' xs mem ih =>
    cases tpt2
    case abs t2' xs' mem' =>
      have ⟨x, qx⟩ := fresh_exists (xs ∪ xs' ∪ free_union [fv] Var)
      simp only [Finset.union_assoc, Finset.mem_union, not_or] at qx
      have ⟨q1, q2, _⟩ := qx
      have ⟨t', _⟩ := ih x q1 (mem' _ q2)
      exists abs (t' ^* x)
      constructor
      <;> [let z := s2' ^ fvar x; let z := t2' ^ fvar x]
      <;> apply Parallel.abs (free_union [fv] Var) <;> grind
  case beta s1 s1' s2 s2' xs mem ps ih1 ih2 =>
    cases tpt2
    case app u2 u2' s1pu2 s2pu2' =>
      cases s1pu2
      case abs s1'' xs' mem' =>
        have ⟨x, qx⟩ := fresh_exists (xs ∪ xs' ∪ free_union [fv] Var)
        simp only [Finset.union_assoc, Finset.mem_union, not_or] at qx
        obtain ⟨q1, q2, _⟩ := qx
        have ⟨t', _⟩ := ih2 s2pu2'
        have ⟨t'', _⟩ := @ih1 x q1 _ (mem' _ q2)
        exists (t'' ^* x) ^ t'
        constructor
        · #adaptation_note
          /-- Moving from `nightly-2025-09-15` to `nightly-2025-10-19`, the grind_pattern for
          subst_intro (defined in Properties.lean) stopped working here. -/
          grind [subst_intro]
        · apply Parallel.beta (free_union [fv] Var) <;> grind
    case beta u1' u2' xs' mem' s2pu2' =>
      have ⟨x, qx⟩ := fresh_exists (xs ∪ xs' ∪ free_union [fv] Var)
      simp only [Finset.union_assoc, Finset.mem_union, not_or] at qx
      have ⟨q1, q2, _⟩ := qx
      have ⟨t', _⟩ := ih2 s2pu2'
      have ⟨t'', _⟩ := @ih1 x q1 _ (mem' _ q2)
      refine ⟨t'' [x := t'], ?_⟩
      grind
  case app s1 s1' s2 s2' s1ps1' _ ih1 ih2  =>
    cases tpt2
    case app u1 u2' s1 s2 =>
      have ⟨l, _, _⟩ := ih1 s1
      have ⟨r, _, _⟩ := ih2 s2
      exact ⟨app l r, by grind⟩
    case beta t1' u1' u2' xs mem s2pu2' =>
      cases s1ps1'
      case abs s1'' xs' mem' =>
        have ⟨x, qx⟩ := fresh_exists (xs ∪ xs' ∪ free_union [fv] Var)
        simp only [Finset.union_assoc, Finset.mem_union, not_or] at qx
        obtain ⟨q1, q2, _⟩ := qx
        have ⟨t', qt'_l, qt'_r⟩ := ih2 s2pu2'
        have ⟨t'', qt''_l, qt''_r⟩ := @ih1 (abs u1') (Parallel.abs xs mem)
        cases qt''_l
        next w1 xs'' mem'' =>
        cases qt''_r
        case abs xs''' mem''' =>
          refine ⟨w1 ^ t', ?_, para_open_out xs''' mem''' qt'_r⟩
          apply Parallel.beta (free_union Var) <;> grind

/-- Parallel reduction is confluent. -/
theorem para_confluence : Confluent (@Parallel Var) :=
  para_diamond.toConfluent

/-- β-reduction is confluent. -/
theorem confluence_beta : Confluent (@FullBeta Var) := by
  have eq : ReflTransGen (@Parallel Var) = ReflTransGen (@FullBeta Var) := by
    ext
    exact parachain_iff_redex
  rw [Confluent, ←eq]
  exact para_confluence

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
