/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleTypes
import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.RRelation
import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.PointInsertion
import Cslib.Logics.Bimodal.Metalogic.BXCanonical.CanonicalModel
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Counterexample Elimination (Burgess 2.9-2.10)

This module implements the key step of the Burgess chronicle construction:
given a chronicle satisfying C0, eliminate individual C5/C5' counterexamples
by inserting new points into the domain.

## Main Results

- `C5Counterexample` / `C5'Counterexample`: Structures representing missing
  Until/Since witnesses.

- `eliminate_C5_counterexample`: (Lemma 2.10) Given x in dom with xi U eta in f(x)
  but no Until witness, extend the chronicle with a new point y such that
  eta in f'(y).

- `eliminate_C5'_counterexample`: Mirror for Since counterexamples.

- `PotentialCounterexample` / `eliminate_potential_counterexample`: Uniform
  interface for the omega-chain construction.

## References

- Burgess 1982: "Axioms for tense logic II: Time periods", Section 2
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
open Cslib.Logic.Bimodal.Metalogic.BXCanonical.CanonicalModel
open Cslib.Logic.Bimodal.Theorems.Combinators

/-! ## C5/C5' Counterexample Structures -/

/--
A **C5 counterexample** for a chronicle: a point x and formulas xi, eta such that
xi U eta in f(x) but no witness exists in the current domain.
-/
structure C5Counterexample (χ : Chronicle Atom) where
  x : Rat
  x_mem : x ∈ χ.dom
  ξ : Formula Atom
  η : Formula Atom
  until_mem : Formula.untl η ξ ∈ χ.f x
  no_witness : ¬∃ y ∈ χ.dom, x < y ∧ η ∈ χ.f y ∧
    ∀ z ∈ χ.dom, x < z → z < y → ξ ∈ χ.f z ∧ Formula.untl η ξ ∈ χ.f z

/--
A **C5' counterexample** (Since direction): a point x and formulas xi, eta such that
xi S eta in f(x) but no backward witness exists.
-/
structure C5'Counterexample (χ : Chronicle Atom) where
  x : Rat
  x_mem : x ∈ χ.dom
  ξ : Formula Atom
  η : Formula Atom
  since_mem : Formula.snce η ξ ∈ χ.f x
  no_witness : ¬∃ y ∈ χ.dom, y < x ∧ η ∈ χ.f y ∧
    ∀ z ∈ χ.dom, y < z → z < x → ξ ∈ χ.f z ∧ Formula.snce η ξ ∈ χ.f z

/-! ## Helper: Finding Fresh Rationals -/

/--
There exists a rational strictly greater than all elements of a finite set
of rationals. (The rationals are unbounded above.)
-/
theorem exists_rat_gt_finset (fs : Finset Rat) :
    ∃ q : Rat, (∀ s ∈ fs, s < q) ∧ q ∉ fs := by
  by_cases h : fs.Nonempty
  · refine ⟨fs.max' h + 1, ?_, ?_⟩
    · intro s hs
      calc s ≤ fs.max' h := Finset.le_max' fs s hs
        _ < fs.max' h + 1 := lt_add_one _
    · intro hmem
      have h1 := Finset.le_max' fs _ hmem
      linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    exact ⟨0, fun s hs => absurd hs (by simp), (by simp)⟩

/--
There exists a rational strictly less than all elements of a finite set
of rationals. (The rationals are unbounded below.)
-/
theorem exists_rat_lt_finset (fs : Finset Rat) :
    ∃ q : Rat, (∀ s ∈ fs, q < s) ∧ q ∉ fs := by
  by_cases h : fs.Nonempty
  · refine ⟨fs.min' h - 1, ?_, ?_⟩
    · intro s hs
      calc fs.min' h - 1 < fs.min' h := sub_one_lt _
        _ ≤ s := Finset.min'_le fs s hs
    · intro hmem
      have h1 := Finset.min'_le fs _ hmem
      linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    exact ⟨0, fun s hs => absurd hs (by simp), (by simp)⟩

/--
There exists a rational strictly between x and y that is NOT in a finite set fs.
Since fs is finite and Q is dense, the open interval (x,y) is infinite while
fs ∩ (x,y) is finite, so there must be a point outside fs.

We construct it explicitly: take z = (x + y) / 2. If z ∉ fs, done. Otherwise,
the interval (x, z) still has no elements of fs strictly between x and z that
block finding a midpoint — but we use a simpler argument: among the finitely
many points of fs in [x,y], there must be a gap, and the midpoint of that gap
works. We use the simpler approach: (x + y) / 2 works when Adjacent, and for
the general case we find any gap in the finite set fs within (x,y).
-/
theorem exists_rat_between_not_in_finset (fs : Finset Rat) (x y : Rat) (hxy : x < y) :
    ∃ z : Rat, x < z ∧ z < y ∧ z ∉ fs := by
  -- The set of fs-elements strictly between x and y
  set T := fs.filter (fun s => x < s ∧ s < y) with hT_def
  by_cases hT : T.Nonempty
  · -- There are fs-elements between x and y. Find the minimum, take midpoint with x.
    set t := T.min' hT with ht_def
    have ht_mem : t ∈ T := Finset.min'_mem T hT
    have ht_prop : x < t ∧ t < y := by
      rw [hT_def] at ht_mem; exact (Finset.mem_filter.mp ht_mem).2
    -- z = (x + t) / 2 is strictly between x and t, hence between x and y
    set z := (x + t) / 2 with hz_def
    have hxz : x < z := by linarith
    have hzt : z < t := by linarith
    have hzy : z < y := lt_trans hzt ht_prop.2
    refine ⟨z, hxz, hzy, ?_⟩
    -- z ∉ fs because z < t = min of fs-elements in (x,y), and z > x
    intro hz_mem
    have hz_in_T : z ∈ T := by
      rw [hT_def]; exact Finset.mem_filter.mpr ⟨hz_mem, hxz, hzy⟩
    have : t ≤ z := Finset.min'_le T z hz_in_T
    linarith
  · -- No fs-elements between x and y. Midpoint works.
    rw [Finset.not_nonempty_iff_eq_empty] at hT
    set z := (x + y) / 2 with hz_def
    have hxz : x < z := by linarith
    have hzy : z < y := by linarith
    refine ⟨z, hxz, hzy, ?_⟩
    intro hz_mem
    have : z ∈ T := by
      rw [hT_def]; exact Finset.mem_filter.mpr ⟨hz_mem, hxz, hzy⟩
    rw [hT] at this
    exact absurd this (by simp)

/-! ## BurgessR3Maximal fc Helper Lemmas -/

/--
**BurgessR3Maximal fc implies g_content subset**: If BurgessR3Maximal(A, B, C) holds with
A and C both MCS, then g_content(A) ⊆ C.

Proof: Suppose G(φ) ∈ A but φ ∉ C. Then φ.neg ∈ C (MCS). Since B is CUD, ⊤ ∈ B (a
theorem is in any CUD set). From burgessRSet(A, B, C): untl(⊤, φ.neg) ∈ A. By BX10
(until_F), F(φ.neg) ∈ A. But G(φ) ∈ A gives ¬F(φ.neg) ∈ A (by G = ¬F¬ equivalence
in MCS), contradicting consistency of A.
-/
theorem BurgessR3Maximal_g_content_sub {fc : FrameClass} {A B C : Set (Formula Atom)}
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C) :
    g_content A ⊆ C := by
  intro φ hφ
  -- hφ : G(φ) ∈ A, i.e., allFuture(φ) ∈ A
  change Formula.allFuture φ ∈ A at hφ
  -- Suppose φ ∉ C, derive contradiction
  by_contra h_not_C
  have h_neg_C : φ.neg ∈ C := by
    rcases SetMaximalConsistent.negation_complete h_mcs_C φ with h | h
    · exact absurd h h_not_C
    · exact h
  -- ⊤ ∈ B (CUD contains all theorems)
  set top := Formula.bot.imp Formula.bot with top_def
  have h_top_B : top ∈ B :=
    cud_contains_theorems h_r3m.1 (Cslib.Logic.Bimodal.Theorems.Combinators.identity Formula.bot)
  -- burgessRSet(A, B, C): ∀ β ∈ B, ∀ γ ∈ C, untl(β, γ) ∈ A
  have h_untl : Formula.untl φ.neg top ∈ A :=
    h_r3m.2.1.1 top h_top_B φ.neg h_neg_C
  -- BX10: untl(γ, δ) ∈ A → F(δ) ∈ A, here F(φ.neg) ∈ A
  have h_F_neg : Formula.someFuture φ.neg ∈ A :=
    until_F_mcs fc h_mcs_A top φ.neg h_untl
  -- G(φ) ∈ A implies F(φ.neg) ∉ A
  -- F(φ.neg) = someFuture(φ.neg) = (allFuture(φ.neg.neg)).neg
  -- G(φ) ∈ A → G(φ.neg.neg) ∈ A (by φ → ¬¬φ inside G) → F(φ.neg) ∉ A
  -- Derive ⊢ φ → ¬¬φ, i.e., ⊢ φ → (φ.neg → ⊥)
  -- This is ⊢ φ → ((φ → ⊥) → ⊥), which follows from prop_s, prop_k, identity
  have h_dni : DerivationTree fc [] (φ.imp φ.neg.neg) := by
    -- φ.neg.neg = (φ.imp bot).imp bot
    -- Need: ⊢ φ → ((φ → ⊥) → ⊥)
    -- Proof: by deduction, assume φ.neg and φ, apply to get ⊥
    have h1 : DerivationTree fc [φ.neg, φ] Formula.bot :=
      DerivationTree.modus_ponens [φ.neg, φ] φ Formula.bot
        (DerivationTree.assumption _ φ.neg (by simp))
        (DerivationTree.assumption _ φ (by simp))
    have h2 : DerivationTree fc [φ] φ.neg.neg :=
      deduction_theorem [φ] φ.neg Formula.bot h1
    exact deduction_theorem [] φ φ.neg.neg h2
  -- G(φ → ¬¬φ) and temp_k_dist give G(φ) → G(¬¬φ)
  have h_G_dni : DerivationTree fc [] (Formula.allFuture (φ.imp φ.neg.neg)) :=
    DerivationTree.temporal_necessitation _ h_dni
  have h_kd : DerivationTree fc [] ((φ.imp φ.neg.neg).allFuture.imp
      (φ.allFuture.imp φ.neg.neg.allFuture)) :=
    liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived φ φ.neg.neg)
  have h1 := theorem_in_mcs_fc h_mcs_A h_G_dni
  have h2 := theorem_in_mcs_fc h_mcs_A h_kd
  have h3 := SetMaximalConsistent.implication_property h_mcs_A h2 h1
  have h_G_nn : Formula.allFuture φ.neg.neg ∈ A :=
    SetMaximalConsistent.implication_property h_mcs_A h3 hφ
  -- F(¬φ) and G(¬¬φ) = G(neg(φ.neg)) are contradictory in MCS A
  exact someFuture_allFuture_neg_absurd h_mcs_A φ.neg h_F_neg h_G_nn

/--
**BurgessR3Maximal fc implies SetDeductivelyClosed** when some formula is not in B.
Since B is CUD (from BurgessR3Maximal) and phi not in B, B is not Set.univ, hence consistent.
-/
theorem BurgessR3Maximal_sdc {fc : FrameClass} {A B C : Set (Formula Atom)}
    (h_r3m : BurgessR3Maximal fc A B C)
    {phi : Formula Atom} (h_not_mem : phi ∉ B) :
    SetDeductivelyClosed fc B :=
  cud_not_mem_is_sdc h_r3m.1 h_not_mem

/--
**BurgessR3Maximal fc excludes ⊥ when B is consistent**: In Burgess's framework,
g-values are DCS (deductively closed sets = consistent + CUD). When `B` is
known to be `SetConsistent`, `⊥ ∉ B` follows directly: if `⊥ ∈ B`, then
the singleton list `[⊥]` witnesses inconsistency via the identity derivation.

The consistency hypothesis `h_cons` must be discharged at call sites.
In the omega chain, g-value consistency is established through the
chronicle construction in ChronicleConstruction.lean.

See Burgess 1982, Section 2: "g is a function from {(x,y) : x,y ∈ dom f,
x < y} to the set of all DCSs" where DCS = deductively closed set
(consistent + CUD). -/
theorem BurgessR3Maximal_bot_not_mem {fc : FrameClass} {A B C : Set (Formula Atom)}
    (_h_r3m : BurgessR3Maximal fc A B C)
    (h_cons : SetConsistent fc B) :
    Formula.bot ∉ B := by
  intro h_bot
  exact h_cons [Formula.bot] (fun φ hφ => by simp at hφ; rw [hφ]; exact h_bot)
    ⟨DerivationTree.assumption [Formula.bot] Formula.bot (by simp)⟩

/--
Helper: for adjacent pairs in a chronicle satisfying c2', when inserting a new point
that splits an existing adjacent pair, the old adjacent pairs that don't involve the
split are preserved. Adjacent pairs involving the split point need BurgessR3Maximal
from lemma_2_6_splitting or lemma_2_7.
-/
theorem c2'_preserved_on_old_adjacent {fc : FrameClass} {χ χ' : Chronicle Atom}
    (h_c2' : χ.c2' fc)
    (h_f_agrees : ∀ x ∈ χ.dom, χ'.f x = χ.f x)
    (h_g_agrees : ∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b)
    (h_dom_sub : χ.dom ⊆ χ'.dom)
    {a b : Rat}
    (h_adj' : Adjacent χ'.dom a b)
    (h_a_old : a ∈ χ.dom) (h_b_old : b ∈ χ.dom)
    (h_adj_old : Adjacent χ.dom a b) :
    BurgessR3Maximal fc (χ'.f a) (χ'.g a b) (χ'.f b) := by
  rw [h_f_agrees a h_a_old, h_g_agrees a b h_a_old h_b_old, h_f_agrees b h_b_old]
  exact h_c2' a b h_adj_old

/--
**BurgessR3Maximal fc from h_content subset (backward direction)**:
If h_content(C) ⊆ A (i.e., H(φ) ∈ C → φ ∈ A), then ∃ B, BurgessR3Maximal(A, B, C).

This is the backward mirror of `burgessR3Maximal_from_g_content_sub`:
- Forward: g_content(A) ⊆ C gives BurgessR3Maximal(A, _, C)
- Backward: h_content(C) ⊆ A gives BurgessR3Maximal(A, _, C)

Proof: Use η = ⊤ as the seed element.
- burgessR(A, ⊤, C): F(γ) ∈ A for all γ ∈ C.
  Proof: By BX4' (connect_past), γ → H(F(γ)), so γ ∈ C → H(F(γ)) ∈ C → F(γ) ∈ h_content(C) ⊆ A.
  Then F(γ) → U(⊤, γ) by F_until_equiv.
- burgessRSince(C, ⊤, A): P(α) ∈ C for all α ∈ A.
  Proof: If H(α.neg) ∈ C, then α.neg ∈ h_content(C) ⊆ A, contradicting α ∈ A. So P(α) ∈ C.
  Then P(α) → S(⊤, α) by P_since_equiv.
-/
theorem burgessR3Maximal_from_h_content_sub {fc : FrameClass} {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_hc : h_content C ⊆ A) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal fc A B C := by
  set top := Formula.bot.imp Formula.bot with top_def
  have h_top_A : top ∈ A :=
    theorem_in_mcs_fc h_mcs_A (Cslib.Logic.Bimodal.Theorems.Combinators.identity Formula.bot)
  -- burgessR(A, ⊤, C): ∀ γ ∈ C, U(⊤, γ) ∈ A
  have h_bR : burgessR A top C := by
    intro γ hγ
    -- BX4': γ → H(F(γ))
    have h_ax_cp : DerivationTree fc [] (γ.imp (Formula.allPast (Formula.someFuture γ))) :=
      DerivationTree.axiom [] _ (Axiom.connect_past γ) trivial
    have h_HF : Formula.allPast (Formula.someFuture γ) ∈ C :=
      SetMaximalConsistent.implication_property h_mcs_C
        (theorem_in_mcs_fc h_mcs_C h_ax_cp) hγ
    -- H(F(γ)) ∈ C → F(γ) ∈ h_content(C) ⊆ A
    have h_F : Formula.someFuture γ ∈ A := h_hc h_HF
    -- F(γ) → U(⊤, γ) by F_until_equiv
    have h_bx12 : DerivationTree fc [] ((Formula.someFuture γ).imp (Formula.untl γ top)) :=
      DerivationTree.axiom [] _ (Axiom.F_until_equiv γ) trivial
    exact SetMaximalConsistent.implication_property h_mcs_A
      (theorem_in_mcs_fc h_mcs_A h_bx12) h_F
  -- burgessRSince(C, ⊤, A): ∀ α ∈ A, S(⊤, α) ∈ C
  have h_bRS : burgessRSince C top A := by
    intro α hα
    -- If H(α.neg) ∈ C, then α.neg ∈ h_content(C) ⊆ A, contradicting α ∈ A
    have h_P : Formula.somePast α ∈ C := by
      by_contra h_not_P
      have h_neg_P : (Formula.somePast α).neg ∈ C :=
        (SetMaximalConsistent.negation_complete h_mcs_C _).resolve_left h_not_P
      have h_H_neg : Formula.allPast α.neg ∈ C :=
        neg_somePast_to_allPast_neg h_mcs_C α h_neg_P
      have h_neg_A : α.neg ∈ A := h_hc h_H_neg
      exact SetMaximalConsistent.neg_excludes h_mcs_A α h_neg_A hα
    -- P(α) → S(⊤, α) by P_since_equiv
    have h_bx12' : DerivationTree fc [] ((Formula.somePast α).imp (Formula.snce α top)) :=
      DerivationTree.axiom [] _ (Axiom.P_since_equiv α) trivial
    exact SetMaximalConsistent.implication_property h_mcs_C
      (theorem_in_mcs_fc h_mcs_C h_bx12') h_P
  exact burgessR3Maximal_exists_from_seed fc A C top h_mcs_A h_mcs_C h_bR h_bRS h_top_A

/-! ## Lemma 2.10: C5 Counterexample Elimination -/

/--
**Lemma 2.10** (C5 Counterexample Elimination): Given a chronicle satisfying C0
and a C5 counterexample (x, xi, eta), extend the chronicle by adding a new point y
with eta in f'(y).

The construction uses Lemma 2.4 to obtain an MCS C with:
- eta in C (the Until eventuality is witnessed)
- g_content(f(x)) subset of C (temporal coherence)

The new point y is placed beyond all current domain points.
-/
noncomputable def eliminate_C5_counterexample {fc : FrameClass} {χ : Chronicle Atom}
    (h_c0 : χ.c0 fc)
    (ce : C5Counterexample χ)
    :
    ∃ χ' : Chronicle Atom,
      χ.dom ⊆ χ'.dom ∧
      (∀ x ∈ χ.dom, χ'.f x = χ.f x) ∧
      χ'.c0 fc ∧
      (∃ y ∈ χ'.dom, ce.x < y ∧ ce.η ∈ χ'.f y) ∧
      χ.dom ⊂ χ'.dom ∧
      (∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b) ∧
      (∀ a b, χ'.g a b = χ.g a b) := by
  -- Step 1: Get a fresh point y > all domain points
  obtain ⟨y, hy_gt, hy_notin⟩ := exists_rat_gt_finset χ.dom
  -- Step 2: Use Lemma 2.4 to get an MCS with eta and g_content(f(x)), plus interval DCS B
  have h_mcs_x := h_c0 ce.x ce.x_mem
  obtain ⟨_B, C, h_C_mcs, h_η_C, _, _, _⟩ :=
    lemma_2_4 fc h_mcs_x ce.ξ ce.η ce.until_mem
  -- Step 3: Build the new chronicle
  -- f' agrees with f on old domain, assigns C to y
  -- g' is unchanged (placeholder; full interval assignment in ChronicleConstruction)
  refine ⟨⟨fun q => if q = y then C else χ.f q, χ.g, insert y χ.dom⟩,
    Finset.subset_insert y χ.dom, ?_, ?_, ?_, Finset.ssubset_insert hy_notin,
    fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  · -- f agrees on old points
    intro x hx
    have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
    exact if_neg h_ne
  · -- C0
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · simp only [ite_true]; exact h_C_mcs
    · have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
      simp only [h_ne, ite_false]; exact h_c0 x hx
  · -- Witness
    refine ⟨y, Finset.mem_insert_self y χ.dom, hy_gt ce.x ce.x_mem, ?_⟩
    simp only [ite_true]
    exact h_η_C

/--
**Lemma 2.10'** (C5' Counterexample Elimination): Mirror of Lemma 2.10 for Since.
Given a C5' counterexample (x, xi, eta), extend the chronicle by adding a new point
y < x with eta in f'(y).
-/
noncomputable def eliminate_C5'_counterexample {fc : FrameClass} {χ : Chronicle Atom}
    (h_c0 : χ.c0 fc)
    (ce : C5'Counterexample χ) :
    ∃ χ' : Chronicle Atom,
      χ.dom ⊆ χ'.dom ∧
      (∀ x ∈ χ.dom, χ'.f x = χ.f x) ∧
      χ'.c0 fc ∧
      (∃ y ∈ χ'.dom, y < ce.x ∧ ce.η ∈ χ'.f y) ∧
      χ.dom ⊂ χ'.dom ∧
      (∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b) ∧
      (∀ a b, χ'.g a b = χ.g a b) := by
  -- Step 1: Get a fresh point y < all domain points
  obtain ⟨y, hy_lt, hy_notin⟩ := exists_rat_lt_finset χ.dom
  -- Step 2: Construct MCS with eta via BX10' (since_P)
  have h_mcs_x := h_c0 ce.x ce.x_mem
  have h_P_η : Formula.somePast ce.η ∈ χ.f ce.x := by
    have h_ax : DerivationTree fc [] ((Formula.snce ce.η ce.ξ).imp (Formula.somePast ce.η)) :=
      DerivationTree.axiom [] _ (Axiom.since_P ce.ξ ce.η) trivial
    exact SetMaximalConsistent.implication_property h_mcs_x
      (theorem_in_mcs_fc h_mcs_x h_ax) ce.since_mem
  have h_seed := past_temporal_witness_seed_consistent (χ.f ce.x) h_mcs_x ce.η h_P_η
  obtain ⟨C, h_sup, h_C_mcs⟩ := set_lindenbaum_fc h_seed
  have h_η_C : ce.η ∈ C := h_sup (Set.mem_union_left _ (Set.mem_singleton _))
  -- Step 3: Build new chronicle
  refine ⟨⟨fun q => if q = y then C else χ.f q, χ.g, insert y χ.dom⟩,
    Finset.subset_insert y χ.dom, ?_, ?_, ?_, Finset.ssubset_insert hy_notin,
    fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  · intro x hx
    have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
    exact if_neg h_ne
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · simp only [ite_true]; exact h_C_mcs
    · have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
      simp only [h_ne, ite_false]; exact h_c0 x hx
  · refine ⟨y, Finset.mem_insert_self y χ.dom, hy_lt ce.x ce.x_mem, ?_⟩
    simp only [ite_true]
    exact h_η_C

/-! ## G-Propagation Counterexample Elimination

When G(α) ∈ f(x) and α ∉ f(y) for adjacent x < y, insert a new point z between
x and y with α ∈ f(z) and g_content(f(x)) ⊆ f(z). This breaks the adjacency of
(x, y), ensuring the G-propagation failure cannot persist to the limit.

The seed {α} ∪ g_content(f(x)) is consistent because G(α) → F(α) (by
`G_implies_F_mcs`), so `forward_temporal_witness_seed_consistent` applies.
-/

/--
**G-propagation counterexample elimination**: Given G(α) ∈ f(x) and α ∉ f(y)
for adjacent x < y, insert z = (x+y)/2 between x and y with α ∈ f(z) and
g_content(f(x)) ⊆ f(z).
-/
noncomputable def eliminate_g_prop_counterexample {fc : FrameClass} {χ : Chronicle Atom}
    (h_c0 : χ.c0 fc)
    (x y : Rat) (α : Formula Atom)
    (h_x_mem : x ∈ χ.dom) (h_y_mem : y ∈ χ.dom)
    (h_adj : Adjacent χ.dom x y)
    (h_G : Formula.allFuture α ∈ χ.f x)
    (h_not : α ∉ χ.f y) :
    ∃ χ' : Chronicle Atom,
      χ.dom ⊆ χ'.dom ∧
      (∀ q ∈ χ.dom, χ'.f q = χ.f q) ∧
      χ'.c0 fc ∧
      χ.dom ⊂ χ'.dom ∧
      (∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b) ∧
      (∀ a b, χ'.g a b = χ.g a b) := by
  set z := (x + y) / 2 with hz_def
  have hxy := h_adj.2.2.1
  have hz_lt_y : z < y := by linarith
  have hx_lt_z : x < z := by linarith
  have hz_notin : z ∉ χ.dom := by
    intro h_mem; exact h_adj.2.2.2 z h_mem ⟨hx_lt_z, hz_lt_y⟩
  have h_mcs_x := h_c0 x h_x_mem
  -- Use g_propagation_witness to get an MCS D with α ∈ D and g_content(f(x)) ⊆ D
  obtain ⟨D, h_D_mcs, h_α_D, _h_g_sub⟩ := g_propagation_witness fc h_mcs_x α h_G
  refine ⟨⟨fun q => if q = z then D else χ.f q, χ.g, insert z χ.dom⟩,
    Finset.subset_insert z χ.dom, ?_, ?_, Finset.ssubset_insert hz_notin,
    fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  · intro q hq
    have h_ne : q ≠ z := fun h => hz_notin (h ▸ hq)
    exact if_neg h_ne
  · intro q hq
    simp only [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · simp only [ite_true]; exact h_D_mcs
    · have h_ne : q ≠ z := fun h => hz_notin (h ▸ hq)
      simp only [h_ne, ite_false]; exact h_c0 q hq

/--
**H-propagation counterexample elimination**: Mirror for backward direction.
Given H(α) ∈ f(x) and α ∉ f(y) for adjacent y < x, insert z between y and x.
-/
noncomputable def eliminate_h_prop_counterexample {fc : FrameClass} {χ : Chronicle Atom}
    (h_c0 : χ.c0 fc)
    (x y : Rat) (α : Formula Atom)
    (h_x_mem : x ∈ χ.dom) (h_y_mem : y ∈ χ.dom)
    (h_adj : Adjacent χ.dom y x)
    (h_H : Formula.allPast α ∈ χ.f x)
    (h_not : α ∉ χ.f y) :
    ∃ χ' : Chronicle Atom,
      χ.dom ⊆ χ'.dom ∧
      (∀ q ∈ χ.dom, χ'.f q = χ.f q) ∧
      χ'.c0 fc ∧
      χ.dom ⊂ χ'.dom ∧
      (∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b) ∧
      (∀ a b, χ'.g a b = χ.g a b) := by
  set z := (y + x) / 2 with hz_def
  have hyx := h_adj.2.2.1
  have hz_lt_x : z < x := by linarith
  have hy_lt_z : y < z := by linarith
  have hz_notin : z ∉ χ.dom := by
    intro h_mem; exact h_adj.2.2.2 z h_mem ⟨hy_lt_z, hz_lt_x⟩
  have h_mcs_x := h_c0 x h_x_mem
  -- P(α) ∈ f(x) by H_implies_P_mcs, then past_temporal_witness_seed gives us D
  have h_P := H_implies_P_mcs fc h_mcs_x α h_H
  have h_seed := past_temporal_witness_seed_consistent (χ.f x) h_mcs_x α h_P
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed
  have h_α_D : α ∈ D := h_sup (Set.mem_union_left _ (Set.mem_singleton _))
  refine ⟨⟨fun q => if q = z then D else χ.f q, χ.g, insert z χ.dom⟩,
    Finset.subset_insert z χ.dom, ?_, ?_, Finset.ssubset_insert hz_notin,
    fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  · intro q hq
    have h_ne : q ≠ z := fun h => hz_notin (h ▸ hq)
    exact if_neg h_ne
  · intro q hq
    simp only [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · simp only [ite_true]; exact h_D_mcs
    · have h_ne : q ≠ z := fun h => hz_notin (h ▸ hq)
      simp only [h_ne, ite_false]; exact h_c0 q hq

/-! ## Potential Counterexample Interface -/

/--
The **kind** of a potential counterexample, distinguishing between
C4 (backward counterexample) and C5 (forward witness) conditions,
each in forward (Until) and backward (Since) directions.
-/
inductive PotentialCounterexampleKind : Type where
  | c4_forward    : PotentialCounterexampleKind  -- C4: Until backward counterexample
  | c4_backward   : PotentialCounterexampleKind  -- C4': Since backward counterexample
  | c5_forward    : PotentialCounterexampleKind  -- C5: Until forward witness
  | c5_backward   : PotentialCounterexampleKind  -- C5': Since forward witness
  deriving DecidableEq

instance : Fintype PotentialCounterexampleKind where
  elems := {.c4_forward, .c4_backward, .c5_forward, .c5_backward}
  complete := by intro x; cases x <;> simp

instance : Encodable PotentialCounterexampleKind where
  encode
    | .c4_forward => 0
    | .c4_backward => 1
    | .c5_forward => 2
    | .c5_backward => 3
  decode
    | 0 => some .c4_forward
    | 1 => some .c4_backward
    | 2 => some .c5_forward
    | 3 => some .c5_backward
    | _ => none
  encodek := by intro x; cases x <;> simp

/--
A **potential counterexample** encodes a tuple (x, y, xi, eta, kind) that MIGHT
be a C4/C4'/C5/C5' counterexample depending on the current chronicle state.

- For C5/C5' counterexamples: only `x`, `ξ`, `η` are relevant; `y` is ignored.
- For C4/C4' counterexamples: both `x` and `y` identify the adjacent pair,
  `γ = ξ` is the GUARD formula, and `δ = η` is the EVENT formula.
  C4 checks EVENT (η) at f(y) and negates GUARD (ξ) at f(z).
-/
structure PotentialCounterexample where
  x : Rat
  y : Rat
  ξ : Formula Atom
  η : Formula Atom
  kind : PotentialCounterexampleKind

/--
Result type for `eliminate_potential_counterexample`, bundling the core
properties (domain extension, C0, f-agreement) together with the
C5/C5' witness guarantees needed by the limit construction.

The `c5_forward_witness` field states: if the input counterexample is c5_forward
and the point x is in the domain with U(ξ,η) ∈ f(x), then a witness y exists
in the result domain with η ∈ f(y) AND the guard ξ is in g(a,b) for every
adjacent pair (a,b) between x and y. This adjacent-pair guard condition is
the correct formulation for non-adjacent witnesses in finite-stage chronicles
(per Burgess C5a, p.374). Similarly for `c5_backward_witness` and Since.
-/
structure EliminationResult (fc : FrameClass) (χ : Chronicle Atom) (pc : PotentialCounterexample) where
  val : Chronicle Atom
  dom_sub : χ.dom ⊆ val.dom
  c0 : val.c0 fc
  f_agrees : ∀ x ∈ χ.dom, val.f x = χ.f x
  g_agrees : ∀ a b, a ∈ χ.dom → b ∈ χ.dom → val.g a b = χ.g a b
  /-- c2' is preserved: for all adjacent pairs in the new chronicle that were
  also adjacent in the original, BurgessR3Maximal fc holds. New adjacent pairs
  from the elimination also satisfy BurgessR3Maximal. -/
  c2' : val.c2' fc
  c5_forward_witness : pc.kind = .c5_forward → pc.x ∈ χ.dom →
    Formula.untl pc.η pc.ξ ∈ χ.f pc.x →
    ∃ y ∈ val.dom, pc.x < y ∧ pc.η ∈ val.f y ∧
      (∀ a b, Adjacent val.dom a b → pc.x ≤ a → b ≤ y → pc.ξ ∈ val.g a b) ∧
      (∀ w ∈ χ.dom, pc.x < w → w < y → pc.ξ ∈ val.f w) ∧
      (y ∉ χ.dom ∨ ∀ u ∈ val.dom, u ∈ χ.dom)
  c5_backward_witness : pc.kind = .c5_backward → pc.x ∈ χ.dom →
    Formula.snce pc.η pc.ξ ∈ χ.f pc.x →
    ∃ y ∈ val.dom, y < pc.x ∧ pc.η ∈ val.f y ∧
      (∀ a b, Adjacent val.dom a b → y ≤ a → b ≤ pc.x → pc.ξ ∈ val.g a b) ∧
      (∀ w ∈ χ.dom, y < w → w < pc.x → pc.ξ ∈ val.f w) ∧
      (y ∉ χ.dom ∨ ∀ u ∈ val.dom, u ∈ χ.dom)
  c4_forward_witness : pc.kind = .c4_forward → pc.x ∈ χ.dom → pc.y ∈ χ.dom →
    pc.x < pc.y →
    (Formula.untl pc.η pc.ξ).neg ∈ χ.f pc.x →
    pc.η ∈ χ.f pc.y →
    ∃ z ∈ val.dom, pc.x < z ∧ z < pc.y ∧ pc.ξ.neg ∈ val.f z
  c4_backward_witness : pc.kind = .c4_backward → pc.x ∈ χ.dom → pc.y ∈ χ.dom →
    pc.y < pc.x →
    (Formula.snce pc.η pc.ξ).neg ∈ χ.f pc.x →
    pc.η ∈ χ.f pc.y →
    ∃ z ∈ val.dom, pc.y < z ∧ z < pc.x ∧ pc.ξ.neg ∈ val.f z
  /-- Old g-values flow into new f-values: when a point w is inserted between
  adjacent (a,b) in the old domain, the old interval set g(a,b) is contained
  in f'(w). This follows from B ⊆ D in all splitting lemmas (2.6, 2.7, 2.8).
  Vacuously true when no new point is inserted. -/
  g_sub_f_insert : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.f w
  g_sub_g_new : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.g a w ∧ χ.g a b ⊆ val.g w b
  dom_new_unique : ∀ u v, u ∈ val.dom → u ∉ χ.dom → v ∈ val.dom → v ∉ χ.dom → u = v
  /-- When the C5 forward counterexample is already resolved (a witness with the right
  guard exists in χ.dom), the elimination is the identity: no new domain points.
  In the ¬h_actual branch: val = χ so val.dom = χ.dom.
  In the h_actual branch: the hypothesis contradicts h_no_wit, so vacuously true. -/
  c5_forward_resolved_no_new : pc.kind = .c5_forward → pc.x ∈ χ.dom →
    Formula.untl pc.η pc.ξ ∈ χ.f pc.x →
    (∃ y ∈ χ.dom, pc.x < y ∧ pc.η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → pc.x ≤ a → b ≤ y → pc.ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, pc.x < w → w < y → pc.ξ ∈ χ.f w)) →
    ∀ u ∈ val.dom, u ∈ χ.dom
  /-- Mirror of c5_forward_resolved_no_new for the backward (Since) case. -/
  c5_backward_resolved_no_new : pc.kind = .c5_backward → pc.x ∈ χ.dom →
    Formula.snce pc.η pc.ξ ∈ χ.f pc.x →
    (∃ y ∈ χ.dom, y < pc.x ∧ pc.η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → y ≤ a → b ≤ pc.x → pc.ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, y < w → w < pc.x → pc.ξ ∈ χ.f w)) →
    ∀ u ∈ val.dom, u ∈ χ.dom

/--
Result of the C5 forward recursive walk (Burgess 2.10 induction).
Given a chronicle and a starting point where U(ξ,η) ∈ f(start),
the walk produces an extended chronicle with a witness y > start such that
η ∈ f'(y) and the guard ξ ∈ g'(a,b) holds for all adjacent pairs from start to y.
-/
structure C5ForwardWalkResult (fc : FrameClass) (χ : Chronicle Atom) (ξ η : Formula Atom) (start : Rat) where
  val : Chronicle Atom
  dom_sub : χ.dom ⊆ val.dom
  c0 : val.c0 fc
  c2' : val.c2' fc
  f_agrees : ∀ x ∈ χ.dom, val.f x = χ.f x
  g_agrees : ∀ a b, a ∈ χ.dom → b ∈ χ.dom → val.g a b = χ.g a b
  witness : Rat
  witness_mem : witness ∈ val.dom
  witness_gt : start < witness
  witness_event : η ∈ val.f witness
  witness_guard : ∀ a b, Adjacent val.dom a b → start ≤ a → b ≤ witness → ξ ∈ val.g a b
  g_sub_f_insert : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.f w
  g_sub_g_new : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.g a w ∧ χ.g a b ⊆ val.g w b
  dom_new_unique : ∀ u v, u ∈ val.dom → u ∉ χ.dom → v ∈ val.dom → v ∉ χ.dom → u = v
  /-- All new domain points are strictly after `start`. This ensures that
  (start, x') remains adjacent in val.dom when composing recursive guards. -/
  new_point_after : ∀ w ∈ val.dom, w ∉ χ.dom → start < w
  /-- Domain guard: ξ ∈ f(w) for all original domain points strictly between
  start and witness. This follows from the walk's condition (i) check at each
  intermediate point (ξ ∧ (ξ U η) ∈ f(x') gives ξ ∈ f(x') by conj_left_mcs).
  In split cases, the witness is the midpoint between start and successor,
  so no original domain points exist in (start, witness) and this is vacuous. -/
  domain_guard : ∀ w ∈ χ.dom, start < w → w < witness → ξ ∈ val.f w
  /-- The witness is always a new point, not in the original domain χ.dom.
  Base case: witness is placed beyond all domain points.
  Walk/condition(i) case: witness comes from recursion (induction).
  Split case: witness is the midpoint z, which is not in χ.dom. -/
  witness_not_old : witness ∉ χ.dom

/--
Recursive walk for C5 forward guard (Burgess 2.10 induction).

At each step from `start`, find x' = successor in dom:
- **Base case** (start = max dom): Use `lemma_2_4_with_guard` to insert witness beyond.
- **Condition (i)** (conj ∈ f(x') ∧ ξ ∈ g(start,x')): Recurse at x', compose guard.
- **Not condition (i)**: Split at (start, x') using lemma_2_7/2_8/2_6.

Termination: `(dom.filter (· > start)).card` strictly decreases at each recursive step.
-/
private noncomputable def c5_forward_walk (fc : FrameClass)
    (χ : Chronicle Atom) (h_c0 : χ.c0 fc) (h_c2' : χ.c2' fc)
    (ξ η : Formula Atom) (pt : Rat)
    (h_start_mem : pt ∈ χ.dom)
    (h_until_start : Formula.untl η ξ ∈ χ.f pt)
    (h_no_wit : ¬∃ y ∈ χ.dom, pt < y ∧ η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → pt ≤ a → b ≤ y → ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, pt < w → w < y → ξ ∈ χ.f w)) :
    C5ForwardWalkResult fc χ ξ η pt := by
  -- Set up domain facts
  have h_dom_ne : χ.dom.Nonempty := ⟨pt, h_start_mem⟩
  set max_old := χ.dom.max' h_dom_ne with max_old_def
  have h_max_mem : max_old ∈ χ.dom := Finset.max'_mem χ.dom h_dom_ne
  have h_max_le : ∀ s ∈ χ.dom, s ≤ max_old := fun s hs => Finset.le_max' χ.dom s hs
  have h_mcs_start := h_c0 pt h_start_mem
  by_cases h_eq_max : pt = max_old
  · -- **BASE CASE**: pt = max(dom). Insert witness y beyond max_old.
    have h_fresh := exists_rat_gt_finset χ.dom
    let y := h_fresh.choose
    have hy_gt : ∀ s ∈ χ.dom, s < y := h_fresh.choose_spec.1
    have hy_notin : y ∉ χ.dom := h_fresh.choose_spec.2
    have h_l24 := lemma_2_4_with_guard fc h_mcs_start ξ η h_until_start
    let B := h_l24.choose
    let C := h_l24.choose_spec.choose
    have h_l24_prop := h_l24.choose_spec.choose_spec
    have h_C_mcs : SetMaximalConsistent fc C := h_l24_prop.1
    have h_η_C : η ∈ C := h_l24_prop.2.1
    have h_ξ_B : ξ ∈ B := h_l24_prop.2.2.2.2.1
    have h_r3m : BurgessR3Maximal fc (χ.f pt) B C := h_l24_prop.2.2.2.2.2
    have h_max_lt_y : max_old < y := hy_gt max_old h_max_mem
    let g' := fun a b =>
      if a = max_old ∧ b = y then B
      else χ.g a b
    let χ' : Chronicle Atom := ⟨fun q => if q = y then C else χ.f q, g', insert y χ.dom⟩
    have h_c2'_new : χ'.c2' fc := by
      intro a b h_adj_new
      obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
      simp only [χ', Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd hab (lt_irrefl _)
      · exact absurd hab (not_lt.mpr (le_of_lt (hy_gt b hb)))
      · have ha_eq : a = max_old := by
          by_contra ha_ne
          have ha_le : a ≤ max_old := h_max_le a ha
          have ha_lt : a < max_old := lt_of_le_of_ne ha_le ha_ne
          exact h_no_between max_old (Finset.mem_insert_of_mem h_max_mem) ⟨ha_lt, h_max_lt_y⟩
        subst ha_eq
        show BurgessR3Maximal fc
          (if max_old = y then C else χ.f max_old)
          (g' max_old y)
          (if y = y then C else χ.f y)
        have hmax_ne_y : max_old ≠ y := ne_of_lt h_max_lt_y
        simp only [hmax_ne_y, ite_false, ite_true, g']
        simp only [and_self, ite_true]
        rw [← h_eq_max]; exact h_r3m
      · have ha_ne : a ≠ y := fun h => hy_notin (h ▸ ha)
        have hb_ne : b ≠ y := fun h => hy_notin (h ▸ hb)
        show BurgessR3Maximal fc
          (if a = y then C else χ.f a)
          (g' a b)
          (if b = y then C else χ.f b)
        simp only [ha_ne, hb_ne, ite_false, ite_true]
        show BurgessR3Maximal fc (χ.f a)
          (if a = max_old ∧ b = y then B else χ.g a b) (χ.f b)
        rw [if_neg (fun ⟨_, hby⟩ => hb_ne hby)]
        have h_adj_old : Adjacent χ.dom a b := by
          refine ⟨ha, hb, hab, ?_⟩
          intro u hu ⟨hau, hub⟩
          exact h_no_between u (Finset.mem_insert_of_mem hu) ⟨hau, hub⟩
        exact h_c2' a b h_adj_old
    exact { val := χ'
            dom_sub := Finset.subset_insert y χ.dom
            c0 := by
              intro q hq
              show SetMaximalConsistent fc (if q = y then C else χ.f q)
              change q ∈ insert y χ.dom at hq
              simp only [Finset.mem_insert] at hq
              rcases hq with rfl | hq
              · simp only [ite_true]; exact h_C_mcs
              · have h_ne : q ≠ y := fun h => hy_notin (h ▸ hq)
                simp only [h_ne, ite_false]; exact h_c0 q hq
            c2' := h_c2'_new
            f_agrees := by
              intro x hx
              have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
              exact if_neg h_ne
            g_agrees := by
              intro a b ha hb
              show g' a b = χ.g a b
              simp only [g']
              have hb_ne : b ≠ y := fun h => hy_notin (h ▸ hb)
              simp only [hb_ne, and_false, ite_false]
            witness := y
            witness_mem := Finset.mem_insert_self y χ.dom
            witness_gt := hy_gt pt h_start_mem
            witness_event := by simp only [χ', ite_true]; exact h_η_C
            witness_guard := by
              intro a b h_adj_ab h_le_a h_le_b
              have ha_dom : a ∈ insert y χ.dom := h_adj_ab.1
              have hb_dom : b ∈ insert y χ.dom := h_adj_ab.2.1
              simp only [Finset.mem_insert] at ha_dom hb_dom
              have hb_eq : b = y := by
                rcases hb_dom with rfl | hb_old
                · rfl
                · have : b ≤ max_old := h_max_le b hb_old
                  linarith [h_adj_ab.2.2.1]
              subst hb_eq
              have ha_ne_y : a ≠ y := ne_of_lt h_adj_ab.2.2.1
              have ha_old : a ∈ χ.dom := by
                rcases ha_dom with rfl | h
                · exact absurd rfl ha_ne_y
                · exact h
              have ha_eq : a = max_old := by
                have ha_le_max : a ≤ max_old := h_max_le a ha_old
                have hmax_le_a : max_old ≤ a := by
                  by_contra hlt; push_neg at hlt
                  exact h_adj_ab.2.2.2 max_old
                    (Finset.mem_insert_of_mem h_max_mem) ⟨hlt, h_max_lt_y⟩
                exact le_antisymm ha_le_max hmax_le_a
              subst ha_eq
              show ξ ∈ g' max_old y
              simp only [g', and_self, ite_true]
              exact h_ξ_B
            g_sub_f_insert := by
              intro a b h_adj w hw hw_not haw hwb
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact absurd hwb (not_lt.mpr (le_of_lt (hy_gt b h_adj.2.1)))
              · exact absurd hw hw_not
            g_sub_g_new := by
              intro a b h_adj w hw hw_not haw hwb
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact absurd hwb (not_lt.mpr (le_of_lt (hy_gt b h_adj.2.1)))
              · exact absurd hw hw_not
            dom_new_unique := by
              intro u v hu hu_not hv hv_not
              simp only [χ', Finset.mem_insert] at hu hv
              rcases hu with rfl | hu <;> rcases hv with rfl | hv
              · rfl
              · exact absurd hv hv_not
              · exact absurd hu hu_not
              · exact absurd hu hu_not
            new_point_after := by
              intro w hw hw_not
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact hy_gt pt h_start_mem
              · exact absurd hw hw_not
            domain_guard := by
              -- Base case: pt = max(dom), witness = y > max(dom).
              -- No w ∈ χ.dom with pt < w exists (pt is max).
              intro w hw hsw _
              exact absurd (h_max_le w hw) (not_le.mpr (h_eq_max ▸ hsw))
            witness_not_old := hy_notin }
  · -- **RECURSIVE CASE**: pt < max_old. Find successor x'.
    have h_start_lt_max : pt < max_old := lt_of_le_of_ne (h_max_le pt h_start_mem) h_eq_max
    let T_succ := χ.dom.filter (fun v => v > pt)
    have hT_ne : T_succ.Nonempty :=
      ⟨max_old, Finset.mem_filter.mpr ⟨h_max_mem, h_start_lt_max⟩⟩
    let x' := T_succ.min' hT_ne
    have hx'_mem_T := Finset.min'_mem T_succ hT_ne
    have hx'_dom : x' ∈ χ.dom := (Finset.mem_filter.mp hx'_mem_T).1
    have hstart_lt_x' : pt < x' := (Finset.mem_filter.mp hx'_mem_T).2
    have h_adj_sx' : Adjacent χ.dom pt x' := by
      refine ⟨h_start_mem, hx'_dom, hstart_lt_x', ?_⟩
      intro u hu ⟨hsu, hux⟩
      have hu_T : u ∈ T_succ := Finset.mem_filter.mpr ⟨hu, hsu⟩
      have := Finset.min'_le T_succ u hu_T
      linarith
    have h_mcs_x' := h_c0 x' hx'_dom
    -- Derive: xi ∈ g(pt, x') → eta ∉ f(x')
    have h_guard_implies_no_event : ξ ∈ χ.g pt x' → η ∉ χ.f x' :=
      fun h_guard h_event => h_no_wit ⟨x', hx'_dom, hstart_lt_x', h_event,
        ⟨fun a b h_adj_ab h_le_a h_le_b => by
          have ha_eq : a = pt := by
            by_contra ha_ne
            have ha_gt : pt < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
            exact h_adj_sx'.2.2.2 a h_adj_ab.1 ⟨ha_gt, lt_of_lt_of_le h_adj_ab.2.2.1 h_le_b⟩
          have hb_eq : b = x' := by
            rw [ha_eq] at h_adj_ab
            by_contra hb_ne
            have hb_lt : b < x' := lt_of_le_of_ne h_le_b hb_ne
            exact h_adj_sx'.2.2.2 b h_adj_ab.2.1 ⟨h_adj_ab.2.2.1, hb_lt⟩
          rw [ha_eq, hb_eq]; exact h_guard,
        fun w hw hsw hwx' => absurd ⟨hsw, hwx'⟩ (h_adj_sx'.2.2.2 w hw)⟩⟩
    -- Get BurgessR3Maximal fc facts for (pt, x')
    have h_r3m_adj := h_c2' pt x' h_adj_sx'
    have h_gc_adj := BurgessR3Maximal_g_content_sub h_r3m_adj h_mcs_start h_mcs_x'
    -- Check condition (i): conj ∈ f(x') AND ξ ∈ g(pt, x')
    by_cases h_cond_i : Formula.and ξ (Formula.untl η ξ) ∈ χ.f x' ∧ ξ ∈ χ.g pt x'
    · -- **Condition (i)**: recurse at x'
      have h_untl_x' : Formula.untl η ξ ∈ χ.f x' :=
        conj_right_mcs fc h_mcs_x' ξ (Formula.untl η ξ) h_cond_i.1
      -- Derive: h_no_wit at x'
      have h_no_wit_x' : ¬∃ y ∈ χ.dom, x' < y ∧ η ∈ χ.f y ∧
          (∀ a b, Adjacent χ.dom a b → x' ≤ a → b ≤ y → ξ ∈ χ.g a b) ∧
          (∀ w ∈ χ.dom, x' < w → w < y → ξ ∈ χ.f w) := by
        intro ⟨y, hy_dom, hx'y, hη_y, h_guard_y, h_dom_guard_y⟩
        exact h_no_wit ⟨y, hy_dom, lt_trans hstart_lt_x' hx'y, hη_y,
          ⟨fun a b h_adj_ab h_le_a h_le_b => by
            by_cases h_a_lt_x' : a < x'
            · -- a < x', so a = pt and b = x' (since x' is successor of pt)
              have ha_eq : a = pt := by
                have : pt ≤ a := h_le_a
                by_contra ha_ne
                have ha_gt : pt < a := lt_of_le_of_ne this (Ne.symm ha_ne)
                exact h_adj_sx'.2.2.2 a h_adj_ab.1 ⟨ha_gt, h_a_lt_x'⟩
              have hb_eq : b = x' := by
                rw [ha_eq] at h_adj_ab
                have hb_le : b ≤ x' := by
                  by_contra hgt; push_neg at hgt
                  exact h_adj_ab.2.2.2 x' hx'_dom ⟨hstart_lt_x', hgt⟩
                exact le_antisymm hb_le (by
                  by_contra hlt; push_neg at hlt
                  exact h_adj_sx'.2.2.2 b h_adj_ab.2.1 ⟨h_adj_ab.2.2.1, hlt⟩)
              rw [ha_eq, hb_eq]; exact h_cond_i.2
            · -- a ≥ x'
              push_neg at h_a_lt_x'
              exact h_guard_y a b h_adj_ab h_a_lt_x' h_le_b,
          fun w hw hsw hwy => by
            -- w ∈ χ.dom with pt < w < y. Case split on w vs x'.
            rcases lt_or_eq_of_le (not_lt.mp fun h =>
              h_adj_sx'.2.2.2 w hw ⟨hsw, h⟩) with hwx' | hwx'
            · -- w > x': use h_dom_guard_y from hypothesis
              exact h_dom_guard_y w hw hwx' hwy
            · -- w = x': ξ ∈ f(x') from condition (i) via conj_left_mcs
              rw [← hwx']
              exact conj_left_mcs fc h_mcs_x' ξ (Formula.untl η ξ) h_cond_i.1⟩⟩
      -- Termination: (dom.filter (· > x')).card < (dom.filter (· > pt)).card
      have h_term : (χ.dom.filter (fun v => v > x')).card < (χ.dom.filter (fun v => v > pt)).card := by
        apply Finset.card_lt_card
        constructor
        · intro v hv
          have hv_dom := (Finset.mem_filter.mp hv).1
          have hv_gt : v > x' := (Finset.mem_filter.mp hv).2
          exact Finset.mem_filter.mpr ⟨hv_dom, lt_trans hstart_lt_x' hv_gt⟩
        · simp only [Finset.not_subset]
          exact ⟨x', Finset.mem_filter.mpr ⟨hx'_dom, hstart_lt_x'⟩,
            fun h => absurd (Finset.mem_filter.mp h).2 (lt_irrefl _)⟩
      -- Recurse
      have r := c5_forward_walk fc χ h_c0 h_c2' ξ η x' hx'_dom h_untl_x' h_no_wit_x'
      -- Compose: guard at (pt, x') from condition (i) + recursive guard from x'
      exact { val := r.val
              dom_sub := r.dom_sub
              c0 := r.c0
              c2' := r.c2'
              f_agrees := r.f_agrees
              g_agrees := r.g_agrees
              witness := r.witness
              witness_mem := r.witness_mem
              witness_gt := lt_trans hstart_lt_x' r.witness_gt
              witness_event := r.witness_event
              witness_guard := by
                intro a b h_adj_ab h_le_a h_le_b
                by_cases h_a_ge_x' : x' ≤ a
                · exact r.witness_guard a b h_adj_ab h_a_ge_x' h_le_b
                · -- a < x'. Show a = pt and b = x', then use condition (i) guard.
                  push_neg at h_a_ge_x'
                  have ha_eq : a = pt := by
                    by_contra ha_ne
                    have ha_gt : pt < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
                    by_cases ha_old : a ∈ χ.dom
                    · exact h_adj_sx'.2.2.2 a ha_old ⟨ha_gt, h_a_ge_x'⟩
                    · -- a is new from recursion at x', so x' < a by new_point_after. Contradicts a < x'.
                      exact absurd (r.new_point_after a h_adj_ab.1 ha_old) (not_lt.mpr (le_of_lt h_a_ge_x'))
                  subst ha_eq
                  -- b must be x': x' in val.dom, pt < x', no new point between
                  have hb_eq : b = x' := by
                    have hx'_val : x' ∈ r.val.dom := r.dom_sub hx'_dom
                    by_contra hb_ne
                    rcases lt_or_gt_of_ne hb_ne with hb_lt | hb_gt
                    · by_cases hb_old : b ∈ χ.dom
                      · exact h_adj_sx'.2.2.2 b hb_old ⟨h_adj_ab.2.2.1, hb_lt⟩
                      · exact absurd (r.new_point_after b h_adj_ab.2.1 hb_old) (not_lt.mpr (le_of_lt hb_lt))
                    · exact h_adj_ab.2.2.2 x' hx'_val ⟨hstart_lt_x', hb_gt⟩
                  subst hb_eq
                  rw [r.g_agrees _ x' h_start_mem hx'_dom]
                  exact h_cond_i.2
              g_sub_f_insert := r.g_sub_f_insert
              g_sub_g_new := r.g_sub_g_new
              dom_new_unique := r.dom_new_unique
              new_point_after := by
                intro w hw hw_not
                exact lt_trans hstart_lt_x' (r.new_point_after w hw hw_not)
              domain_guard := by
                -- Condition (i): ξ ∧ (ξ U η) ∈ f(x'), so ξ ∈ f(x') by conj_left_mcs.
                -- For w between start and x': vacuous (x' is immediate successor).
                -- For w between x' and witness: from recursive domain_guard.
                intro w hw hsw hwr
                rcases lt_or_eq_of_le (not_lt.mp fun h =>
                  h_adj_sx'.2.2.2 w hw ⟨hsw, h⟩) with hwx' | hwx'
                · -- w > x', use recursive domain_guard
                  exact r.domain_guard w hw hwx' hwr
                · -- w = x', use condition (i)
                  rw [← hwx', r.f_agrees x' hx'_dom]
                  exact conj_left_mcs fc h_mcs_x' ξ (Formula.untl η ξ) h_cond_i.1
              witness_not_old := r.witness_not_old }
    · -- **Not condition (i)**: split at (pt, x')
      have h_split_result : ∃ B' D B'' : Set (Formula Atom),
          BurgessR3Maximal fc (χ.f pt) B' D ∧
          BurgessR3Maximal fc D B'' (χ.f x') ∧
          SetMaximalConsistent fc D ∧
          η ∈ D ∧
          χ.g pt x' ⊆ D ∧
          χ.g pt x' ⊆ B' ∧
          χ.g pt x' ⊆ B'' ∧
          ξ ∈ B' := by
        by_cases h_eta_g : η ∈ χ.g pt x'
        · by_cases h_xi_g : ξ ∈ χ.g pt x'
          · -- η ∈ g, ξ ∈ g: use lemma_2_8 (avoids needing SetConsistent g)
            -- Derive h_neg_disj: ¬(η ∨ (ξ ∧ U(ξ,η))) ∈ f(x')
            have h_conj_not_f : Formula.and ξ (Formula.untl η ξ) ∉ χ.f x' :=
              fun h => h_cond_i ⟨h, h_xi_g⟩
            have h_neg_disj : (Formula.or η (Formula.and ξ (Formula.untl η ξ))).neg ∈ χ.f x' := by
              have h1 : η.neg ∈ χ.f x' := by
                rcases SetMaximalConsistent.negation_complete h_mcs_x' η with h | h
                · exact absurd h (h_guard_implies_no_event h_xi_g)
                · exact h
              have h2 : (Formula.and ξ (Formula.untl η ξ)).neg ∈ χ.f x' := by
                rcases SetMaximalConsistent.negation_complete h_mcs_x'
                  (Formula.and ξ (Formula.untl η ξ)) with h | h
                · exact absurd h h_conj_not_f
                · exact h
              exact SetMaximalConsistent.implication_property h_mcs_x'
                (theorem_in_mcs_fc h_mcs_x'
                  (liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.demorgan_disj_neg_backward η
                    (Formula.and ξ (Formula.untl η ξ)))))
                (conj_mcs fc h_mcs_x' η.neg (Formula.and ξ (Formula.untl η ξ)).neg h1 h2)
            obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
              lemma_2_8 fc h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_until_start h_neg_disj
            exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB' h_xi_g⟩
          · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B'⟩ :=
              lemma_2_7 fc h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_until_start h_xi_g
            exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B'⟩
        · by_cases h_eta_neg_g : η.neg ∈ χ.g pt x'
          · by_cases h_xi_g : ξ ∈ χ.g pt x'
            · by_cases h_conj_g : Formula.and ξ (Formula.untl η ξ) ∈ χ.g pt x'
              · -- conj in g but not-condition(i): conj not in f(x')
                have h_conj_not_f : Formula.and ξ (Formula.untl η ξ) ∉ χ.f x' :=
                  fun h => h_cond_i ⟨h, h_xi_g⟩
                have h_neg_disj : (Formula.or η (Formula.and ξ (Formula.untl η ξ))).neg ∈ χ.f x' := by
                  have h1 : η.neg ∈ χ.f x' := by
                    rcases SetMaximalConsistent.negation_complete h_mcs_x' η with h | h
                    · exact absurd h (h_guard_implies_no_event h_xi_g)
                    · exact h
                  have h2 : (Formula.and ξ (Formula.untl η ξ)).neg ∈ χ.f x' := by
                    rcases SetMaximalConsistent.negation_complete h_mcs_x'
                      (Formula.and ξ (Formula.untl η ξ)) with h | h
                    · exact absurd h h_conj_not_f
                    · exact h
                  exact SetMaximalConsistent.implication_property h_mcs_x'
                    (theorem_in_mcs_fc h_mcs_x'
                      (liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.demorgan_disj_neg_backward η
                        (Formula.and ξ (Formula.untl η ξ)))))
                    (conj_mcs fc h_mcs_x' η.neg (Formula.and ξ (Formula.untl η ξ)).neg h1 h2)
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
                  lemma_2_8 fc h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_until_start h_neg_disj
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB' h_xi_g⟩
              · have h_bx5 := self_accum_until_mcs fc h_mcs_start ξ η h_until_start
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, hBB', h_B_sub_D, hBB'', _⟩ :=
                  lemma_2_7 fc h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj
                    (Formula.and ξ (Formula.untl η ξ)) η h_bx5 h_conj_g
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB' h_xi_g⟩
            · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B'⟩ :=
                lemma_2_7 fc h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_until_start h_xi_g
              exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B'⟩
          · by_cases h_xi_g2 : ξ ∈ χ.g pt x'
            · have h_sp := lemma_2_6_splitting fc h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj
                η.neg h_eta_neg_g
              obtain ⟨B', D, B'', hB', hB'', hD_mcs, h_dne_D, h_B_sub_D, hBB', hBB''⟩ := h_sp
              exact ⟨B', D, B'', hB', hB'', hD_mcs,
                SetMaximalConsistent.implication_property hD_mcs
                  (theorem_in_mcs_fc hD_mcs (Cslib.Logic.Bimodal.Theorems.Propositional.double_negation η)) h_dne_D,
                h_B_sub_D, hBB', hBB'', hBB' h_xi_g2⟩
            · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B'⟩ :=
                lemma_2_7 fc h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_until_start h_xi_g2
              exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B'⟩
      let B' := h_split_result.choose
      let D := h_split_result.choose_spec.choose
      let B'' := h_split_result.choose_spec.choose_spec.choose
      have h_split_prop := h_split_result.choose_spec.choose_spec.choose_spec
      have h_B'_max : BurgessR3Maximal fc (χ.f pt) B' D := h_split_prop.1
      have h_B''_max : BurgessR3Maximal fc D B'' (χ.f x') := h_split_prop.2.1
      have h_D_mcs : SetMaximalConsistent fc D := h_split_prop.2.2.1
      have h_eta_D : η ∈ D := h_split_prop.2.2.2.1
      have h_g_sub_D : χ.g pt x' ⊆ D := h_split_prop.2.2.2.2.1
      have h_g_sub_B' : χ.g pt x' ⊆ B' := h_split_prop.2.2.2.2.2.1
      have h_g_sub_B'' : χ.g pt x' ⊆ B'' := h_split_prop.2.2.2.2.2.2.1
      have h_xi_B' : ξ ∈ B' := h_split_prop.2.2.2.2.2.2.2
      set z := (pt + x') / 2 with hz_def
      have hz_lt_x' : z < x' := by linarith
      have hstart_lt_z : pt < z := by linarith
      have hz_notin : z ∉ χ.dom := by
        intro h_mem_z; exact h_adj_sx'.2.2.2 z h_mem_z ⟨hstart_lt_z, hz_lt_x'⟩
      let g' := fun a b =>
        if a = pt ∧ b = z then B'
        else if a = z ∧ b = x' then B''
        else χ.g a b
      let val : Chronicle Atom := ⟨fun q => if q = z then D else χ.f q, g', insert z χ.dom⟩
      have h_c2'_new : val.c2' fc := by
        intro a b h_adj_new
        obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
        simp only [val, Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd hab (lt_irrefl _)
        · have hb_eq : b = x' := by
            by_contra hb_ne
            have hb_ge : x' ≤ b := by
              by_contra hlt; push_neg at hlt
              exact h_adj_sx'.2.2.2 b hb ⟨lt_trans hstart_lt_z hab, hlt⟩
            exact h_no_between x' (Finset.mem_insert_of_mem hx'_dom) ⟨hz_lt_x', lt_of_le_of_ne hb_ge (Ne.symm hb_ne)⟩
          subst hb_eq
          have hz_ne_pt : z ≠ pt := ne_of_gt hstart_lt_z
          have hx'_ne_z : x' ≠ z := ne_of_gt hz_lt_x'
          simp only [val, g', if_true, hx'_ne_z, if_false, hz_ne_pt, and_true, and_self, if_true]
          exact h_B''_max
        · -- a is in old domain, a < z. Show a = pt.
          have ha_le_start : a ≤ pt := by
            by_contra hgt; push_neg at hgt
            exact h_adj_sx'.2.2.2 a ha ⟨hgt, lt_trans hab hz_lt_x'⟩
          have ha_eq_start : a = pt := by
            by_contra ha_ne
            exact h_no_between pt (Finset.mem_insert_of_mem h_start_mem) ⟨lt_of_le_of_ne ha_le_start ha_ne, hstart_lt_z⟩
          subst ha_eq_start
          dsimp only [val, g']
          simp only [ne_of_lt hstart_lt_z, if_false, if_true, and_self, if_true, ne_of_gt hstart_lt_z]
          exact h_B'_max
        · have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
          have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
          show BurgessR3Maximal fc (if a = z then D else χ.f a) (g' a b) (if b = z then D else χ.f b)
          simp only [ha_ne, hb_ne, ite_false, g', and_false, false_and]
          exact h_c2' a b ⟨ha, hb, hab, fun u hu huab => h_no_between u (Finset.mem_insert_of_mem hu) huab⟩
      exact { val := val
              dom_sub := Finset.subset_insert z χ.dom
              c0 := by
                intro q hq; show SetMaximalConsistent fc (if q = z then D else χ.f q)
                simp only [val, Finset.mem_insert] at hq
                rcases hq with rfl | hq
                · simp only [ite_true]; exact h_D_mcs
                · simp only [show q ≠ z from fun h => hz_notin (h ▸ hq), ite_false]; exact h_c0 q hq
              c2' := h_c2'_new
              f_agrees := by
                intro x hx; dsimp only [val]
                have hx_ne_z : x ≠ z := by intro h; exact hz_notin (h ▸ hx)
                simp only [hx_ne_z, if_false]
              g_agrees := by
                intro a b ha hb; show g' a b = χ.g a b; simp only [g']
                simp only [show a ≠ z from fun h => hz_notin (h ▸ ha),
                  show b ≠ z from fun h => hz_notin (h ▸ hb), false_and, and_false, ite_false]
              witness := z
              witness_mem := Finset.mem_insert_self z χ.dom
              witness_gt := hstart_lt_z
              witness_event := by show η ∈ (if z = z then D else χ.f z); simp only [ite_true]; exact h_eta_D
              witness_guard := by
                intro a b h_adj_ab h_le_a h_le_b
                obtain ⟨ha_dom, hb_dom, hab_lt, h_no_btw⟩ := h_adj_ab
                simp only [val, Finset.mem_insert] at ha_dom hb_dom
                have ha_eq : a = pt := by
                  by_contra ha_ne
                  have ha_gt := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
                  rcases ha_dom with rfl | ha_mem
                  · exact absurd h_le_b (not_le.mpr hab_lt)
                  · exact h_adj_sx'.2.2.2 a ha_mem ⟨ha_gt, lt_trans (lt_of_lt_of_le hab_lt h_le_b) hz_lt_x'⟩
                subst ha_eq
                have hb_eq : b = z := by
                  by_contra hb_ne
                  have hb_lt : b < z := lt_of_le_of_ne h_le_b hb_ne
                  rcases hb_dom with rfl | hb_mem
                  · exact absurd (le_refl z) (not_le.mpr hb_lt)
                  · exact h_adj_sx'.2.2.2 b hb_mem ⟨hab_lt, lt_trans hb_lt hz_lt_x'⟩
                subst hb_eq
                dsimp only [val, g']
                simp only [and_self, if_true]; exact h_xi_B'
              g_sub_f_insert := by
                intro a b h_adj w hw hw_not haw hwb
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · show χ.g a b ⊆ (if z = z then D else χ.f z); simp only [ite_true]
                  have hab : a = pt ∧ b = x' := by
                    constructor
                    · by_contra ha_ne
                      rcases lt_or_gt_of_ne ha_ne with h | h
                      · exact h_adj.2.2.2 pt h_start_mem ⟨h, lt_trans hstart_lt_z hwb⟩
                      · exact h_adj_sx'.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_x'⟩
                    · by_contra hb_ne
                      rcases lt_or_gt_of_ne hb_ne with h | h
                      · exact h_adj_sx'.2.2.2 b h_adj.2.1 ⟨lt_trans hstart_lt_z hwb, h⟩
                      · exact h_adj.2.2.2 x' hx'_dom ⟨lt_trans haw hz_lt_x', h⟩
                  rw [hab.1, hab.2]; exact h_g_sub_D
                · exact absurd hw hw_not
              g_sub_g_new := by
                intro a b h_adj w hw hw_not haw hwb
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · have ha_eq : a = pt := by
                    by_contra ha_ne
                    rcases lt_or_gt_of_ne ha_ne with h | h
                    · exact h_adj.2.2.2 pt h_start_mem ⟨h, lt_trans hstart_lt_z hwb⟩
                    · exact h_adj_sx'.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_x'⟩
                  have hb_eq : b = x' := by
                    by_contra hb_ne
                    rcases lt_or_gt_of_ne hb_ne with h | h
                    · exact h_adj_sx'.2.2.2 b h_adj.2.1 ⟨lt_trans hstart_lt_z hwb, h⟩
                    · exact h_adj.2.2.2 x' hx'_dom ⟨lt_trans haw hz_lt_x', h⟩
                  subst ha_eq; subst hb_eq; constructor
                  · dsimp only [val, g']; simp only [and_self, if_true]; exact h_g_sub_B'
                  · dsimp only [val, g']
                    simp only [ne_of_gt hstart_lt_z, false_and, if_false, and_self, if_true]
                    exact h_g_sub_B''
                · exact absurd hw hw_not
              dom_new_unique := by
                intro u v hu hu_not hv hv_not
                simp only [val, Finset.mem_insert] at hu hv
                rcases hu with rfl | hu <;> rcases hv with rfl | hv
                · rfl
                · exact absurd hv hv_not
                · exact absurd hu hu_not
                · exact absurd hu hu_not
              new_point_after := by
                intro w hw hw_not
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · exact hstart_lt_z
                · exact absurd hw hw_not
              domain_guard := by
                -- Split case: witness = z (midpoint between start and x').
                -- No w ∈ χ.dom with start < w < z exists (adjacency of (start, x')).
                intro w hw hsw hwz
                exact absurd ⟨hsw, lt_trans hwz hz_lt_x'⟩
                  (h_adj_sx'.2.2.2 w hw)
              witness_not_old := hz_notin }
termination_by (χ.dom.filter (fun v => v > pt)).card
decreasing_by
  /- Using `have r` (not `let r`) makes the recursive result opaque,
     preventing the WF elaborator from duplicating context with daggers.
     This yields a single WF goal closed by simp_all + exact h_term. -/
  all_goals simp_all only [gt_iff_lt]
  all_goals exact h_term

/--
Result of the C5 backward recursive walk (Burgess 2.10' induction, Since direction).
Given a chronicle and a starting point where S(ξ,η) ∈ f(start),
the walk produces an extended chronicle with a witness y < start such that
η ∈ f'(y) and the guard ξ ∈ g'(a,b) holds for all adjacent pairs from y to start.
-/
structure C5BackwardWalkResult (fc : FrameClass) (χ : Chronicle Atom) (ξ η : Formula Atom) (start : Rat) where
  val : Chronicle Atom
  dom_sub : χ.dom ⊆ val.dom
  c0 : val.c0 fc
  c2' : val.c2' fc
  f_agrees : ∀ x ∈ χ.dom, val.f x = χ.f x
  g_agrees : ∀ a b, a ∈ χ.dom → b ∈ χ.dom → val.g a b = χ.g a b
  witness : Rat
  witness_mem : witness ∈ val.dom
  witness_lt : witness < start
  witness_event : η ∈ val.f witness
  witness_guard : ∀ a b, Adjacent val.dom a b → witness ≤ a → b ≤ start → ξ ∈ val.g a b
  g_sub_f_insert : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.f w
  g_sub_g_new : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.g a w ∧ χ.g a b ⊆ val.g w b
  dom_new_unique : ∀ u v, u ∈ val.dom → u ∉ χ.dom → v ∈ val.dom → v ∉ χ.dom → u = v
  /-- All new domain points are strictly before `start`. This ensures that
  (x'', start) remains adjacent in val.dom when composing recursive guards. -/
  new_point_before : ∀ w ∈ val.dom, w ∉ χ.dom → w < start
  /-- Domain guard (Since mirror): ξ ∈ f(w) for all original domain points strictly
  between witness and start. Vacuous in split cases (midpoint between predecessor
  and start, no original domain points exist there). -/
  domain_guard : ∀ w ∈ χ.dom, witness < w → w < start → ξ ∈ val.f w
  /-- The witness is always a new point, not in the original domain χ.dom.
  Mirror of C5ForwardWalkResult.witness_not_old for the Since direction. -/
  witness_not_old : witness ∉ χ.dom

/--
Recursive walk for C5 backward guard (Burgess 2.10' induction, Since direction).

At each step from `start`, find x'' = predecessor in dom:
- **Base case** (start = min dom): Use `past_temporal_witness_seed` + Lindenbaum to insert witness below.
- **Condition (i)** (conj ∈ f(x'') ∧ ξ ∈ g(x'',start)): Recurse at x'', compose guard.
- **Not condition (i)**: Split at (x'', start) using lemma_2_7_since/2_8_since/2_6.

Termination: `(dom.filter (· < start)).card` strictly decreases at each recursive step.
-/
private noncomputable def c5_backward_walk (fc : FrameClass)
    (χ : Chronicle Atom) (h_c0 : χ.c0 fc) (h_c2' : χ.c2' fc)
    (ξ η : Formula Atom) (pt : Rat)
    (h_start_mem : pt ∈ χ.dom)
    (h_since_start : Formula.snce η ξ ∈ χ.f pt)
    (h_no_wit : ¬∃ y ∈ χ.dom, y < pt ∧ η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → y ≤ a → b ≤ pt → ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, y < w → w < pt → ξ ∈ χ.f w)) :
    C5BackwardWalkResult fc χ ξ η pt := by
  -- Set up domain facts
  have h_dom_ne : χ.dom.Nonempty := ⟨pt, h_start_mem⟩
  set min_old := χ.dom.min' h_dom_ne with min_old_def
  have h_min_mem : min_old ∈ χ.dom := Finset.min'_mem χ.dom h_dom_ne
  have h_min_le : ∀ s ∈ χ.dom, min_old ≤ s := fun s hs => Finset.min'_le χ.dom s hs
  have h_mcs_start := h_c0 pt h_start_mem
  by_cases h_eq_min : pt = min_old
  · -- **BASE CASE**: pt = min(dom). Insert witness y below min_old.
    have h_fresh := exists_rat_lt_finset χ.dom
    let y := h_fresh.choose
    have hy_lt : ∀ s ∈ χ.dom, y < s := h_fresh.choose_spec.1
    have hy_notin : y ∉ χ.dom := h_fresh.choose_spec.2
    -- Use lemma_2_4_since_with_guard: from snce(ξ,η) ∈ f(pt), get B,C with
    -- η ∈ C, ξ ∈ B, BurgessR3Maximal(C, B, f(pt))
    have h_l24s := lemma_2_4_since_with_guard fc h_mcs_start ξ η h_since_start
    let B := h_l24s.choose
    let C := h_l24s.choose_spec.choose
    have h_l24s_prop := h_l24s.choose_spec.choose_spec
    have h_C_mcs : SetMaximalConsistent fc C := h_l24s_prop.1
    have h_η_C : η ∈ C := h_l24s_prop.2.1
    have h_ξ_B : ξ ∈ B := h_l24s_prop.2.2.2.1
    have h_r3m : BurgessR3Maximal fc C B (χ.f pt) := h_l24s_prop.2.2.2.2
    have h_min_lt_y : y < min_old := hy_lt min_old h_min_mem
    let g' := fun a b =>
      if a = y ∧ b = min_old then B
      else χ.g a b
    let χ' : Chronicle Atom := ⟨fun q => if q = y then C else χ.f q, g', insert y χ.dom⟩
    have h_c2'_new : χ'.c2' fc := by
      intro a b h_adj_new
      obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
      simp only [χ', Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd hab (lt_irrefl _)
      · have hb_eq : b = min_old := by
          by_contra hb_ne
          have hb_ge : min_old ≤ b := h_min_le b hb
          have hb_gt : min_old < b := lt_of_le_of_ne hb_ge (Ne.symm hb_ne)
          exact h_no_between min_old (Finset.mem_insert_of_mem h_min_mem) ⟨h_min_lt_y, hb_gt⟩
        subst hb_eq
        show BurgessR3Maximal fc
          (if y = y then C else χ.f y)
          (g' y min_old)
          (if min_old = y then C else χ.f min_old)
        have hmin_ne_y : min_old ≠ y := ne_of_gt h_min_lt_y
        simp only [ite_true, hmin_ne_y, ite_false, g', and_self]
        rw [← h_eq_min]; exact h_r3m
      · exact absurd hab (not_lt.mpr (le_of_lt (hy_lt a ha)))
      · have ha_ne : a ≠ y := fun h => hy_notin (h ▸ ha)
        have hb_ne : b ≠ y := fun h => hy_notin (h ▸ hb)
        show BurgessR3Maximal fc
          (if a = y then C else χ.f a)
          (g' a b)
          (if b = y then C else χ.f b)
        simp only [ha_ne, hb_ne, ite_false, g', false_and, ite_false]
        exact h_c2' a b ⟨ha, hb, hab, fun u hu huab => h_no_between u (Finset.mem_insert_of_mem hu) huab⟩
    exact { val := χ'
            dom_sub := Finset.subset_insert y χ.dom
            c0 := by
              intro q hq
              show SetMaximalConsistent fc (if q = y then C else χ.f q)
              change q ∈ insert y χ.dom at hq
              simp only [Finset.mem_insert] at hq
              rcases hq with rfl | hq
              · simp only [ite_true]; exact h_C_mcs
              · have h_ne : q ≠ y := fun h => hy_notin (h ▸ hq)
                simp only [h_ne, ite_false]; exact h_c0 q hq
            c2' := h_c2'_new
            f_agrees := by
              intro x hx
              have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
              exact if_neg h_ne
            g_agrees := by
              intro a b ha hb
              show g' a b = χ.g a b
              simp only [g']
              have ha_ne : a ≠ y := fun h => hy_notin (h ▸ ha)
              simp only [ha_ne, false_and, ite_false]
            witness := y
            witness_mem := Finset.mem_insert_self y χ.dom
            witness_lt := hy_lt pt h_start_mem
            witness_event := by simp only [χ', ite_true]; exact h_η_C
            witness_guard := by
              intro a b h_adj_ab h_le_a h_le_b
              have ha_dom : a ∈ insert y χ.dom := h_adj_ab.1
              have hb_dom : b ∈ insert y χ.dom := h_adj_ab.2.1
              simp only [Finset.mem_insert] at ha_dom hb_dom
              -- a must be y (a ≥ y and a < b ≤ pt = min_old ≤ all old)
              have ha_eq : a = y := by
                rcases ha_dom with rfl | ha_old
                · rfl
                · -- a is old, so min_old ≤ a; but b ≤ pt = min_old, a < b
                  have : min_old ≤ a := h_min_le a ha_old
                  linarith [h_adj_ab.2.2.1]
              subst ha_eq
              -- b must be min_old
              have hb_ne_y : b ≠ y := ne_of_gt h_adj_ab.2.2.1
              have hb_old : b ∈ χ.dom := by
                rcases hb_dom with rfl | h
                · exact absurd rfl hb_ne_y
                · exact h
              have hb_eq : b = min_old := by
                have hb_le_min : b ≤ min_old := by
                  rw [← h_eq_min]; exact h_le_b
                have hmin_le_b : min_old ≤ b := h_min_le b hb_old
                exact le_antisymm hb_le_min hmin_le_b
              subst hb_eq
              show ξ ∈ g' y min_old
              simp only [g', and_self, ite_true]
              exact h_ξ_B
            g_sub_f_insert := by
              intro a b h_adj w hw hw_not haw hwb
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact absurd haw (not_lt.mpr (le_of_lt (hy_lt a h_adj.1)))
              · exact absurd hw hw_not
            g_sub_g_new := by
              intro a b h_adj w hw hw_not haw hwb
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact absurd haw (not_lt.mpr (le_of_lt (hy_lt a h_adj.1)))
              · exact absurd hw hw_not
            dom_new_unique := by
              intro u v hu hu_not hv hv_not
              simp only [χ', Finset.mem_insert] at hu hv
              rcases hu with rfl | hu <;> rcases hv with rfl | hv
              · rfl
              · exact absurd hv hv_not
              · exact absurd hu hu_not
              · exact absurd hu hu_not
            new_point_before := by
              intro w hw hw_not
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact hy_lt pt h_start_mem
              · exact absurd hw hw_not
            domain_guard := by
              -- Base case: pt = min(dom), witness = y < min(dom).
              -- No w ∈ χ.dom with w < pt exists (pt is min).
              intro w hw _ hws
              exact absurd (h_min_le w hw) (not_le.mpr (h_eq_min ▸ hws))
            witness_not_old := hy_notin }
  · -- **RECURSIVE CASE**: pt > min_old. Find predecessor x''.
    have h_start_gt_min : min_old < pt := lt_of_le_of_ne (h_min_le pt h_start_mem) (Ne.symm h_eq_min)
    let T_pred := χ.dom.filter (fun v => v < pt)
    have hT_ne : T_pred.Nonempty :=
      ⟨min_old, Finset.mem_filter.mpr ⟨h_min_mem, h_start_gt_min⟩⟩
    let x'' := T_pred.max' hT_ne
    have hx''_mem_T := Finset.max'_mem T_pred hT_ne
    have hx''_dom : x'' ∈ χ.dom := (Finset.mem_filter.mp hx''_mem_T).1
    have hx''_lt_start : x'' < pt := (Finset.mem_filter.mp hx''_mem_T).2
    have h_adj_x''s : Adjacent χ.dom x'' pt := by
      refine ⟨hx''_dom, h_start_mem, hx''_lt_start, ?_⟩
      intro u hu ⟨hx''u, hus⟩
      have hu_T : u ∈ T_pred := Finset.mem_filter.mpr ⟨hu, hus⟩
      have := Finset.le_max' T_pred u hu_T
      linarith
    have h_mcs_x'' := h_c0 x'' hx''_dom
    -- Derive: xi ∈ g(x'', pt) → eta ∉ f(x'')
    have h_guard_implies_no_event : ξ ∈ χ.g x'' pt → η ∉ χ.f x'' :=
      fun h_guard h_event => h_no_wit ⟨x'', hx''_dom, hx''_lt_start, h_event,
        ⟨fun a b h_adj_ab h_le_a h_le_b => by
          have ha_eq : a = x'' := by
            by_contra ha_ne
            have ha_gt : x'' < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
            exact h_adj_x''s.2.2.2 a h_adj_ab.1 ⟨ha_gt, lt_of_lt_of_le h_adj_ab.2.2.1 h_le_b⟩
          have hb_eq : b = pt := by
            rw [ha_eq] at h_adj_ab
            by_contra hb_ne
            have hb_lt : b < pt := lt_of_le_of_ne h_le_b hb_ne
            exact h_adj_x''s.2.2.2 b h_adj_ab.2.1 ⟨h_adj_ab.2.2.1, hb_lt⟩
          rw [ha_eq, hb_eq]; exact h_guard,
        fun w hw hx''w hws => absurd ⟨hx''w, hws⟩ (h_adj_x''s.2.2.2 w hw)⟩⟩
    -- Get BurgessR3Maximal fc facts for (x'', pt)
    have h_r3m_adj := h_c2' x'' pt h_adj_x''s
    have h_gc_adj := BurgessR3Maximal_g_content_sub h_r3m_adj h_mcs_x'' h_mcs_start
    -- Check condition (i): conj ∈ f(x'') AND ξ ∈ g(x'', pt)
    by_cases h_cond_i : Formula.and ξ (Formula.snce η ξ) ∈ χ.f x'' ∧ ξ ∈ χ.g x'' pt
    · -- **Condition (i)**: recurse at x''
      have h_snce_x'' : Formula.snce η ξ ∈ χ.f x'' :=
        conj_right_mcs fc h_mcs_x'' ξ (Formula.snce η ξ) h_cond_i.1
      -- Derive: h_no_wit at x''
      have h_no_wit_x'' : ¬∃ y ∈ χ.dom, y < x'' ∧ η ∈ χ.f y ∧
          (∀ a b, Adjacent χ.dom a b → y ≤ a → b ≤ x'' → ξ ∈ χ.g a b) ∧
          (∀ w ∈ χ.dom, y < w → w < x'' → ξ ∈ χ.f w) := by
        intro ⟨y, hy_dom, hy_lt_x'', hη_y, h_guard_y, h_dom_guard_y⟩
        exact h_no_wit ⟨y, hy_dom, lt_trans hy_lt_x'' hx''_lt_start, hη_y,
          ⟨fun a b h_adj_ab h_le_a h_le_b => by
            by_cases h_b_gt_x'' : x'' < b
            · -- b > x'', so b = pt and a = x'' (since x'' is predecessor of pt)
              have hb_eq : b = pt := by
                have : b ≤ pt := h_le_b
                by_contra hb_ne
                have hb_lt : b < pt := lt_of_le_of_ne this hb_ne
                exact h_adj_x''s.2.2.2 b h_adj_ab.2.1 ⟨h_b_gt_x'', hb_lt⟩
              have ha_eq : a = x'' := by
                rw [hb_eq] at h_adj_ab
                have ha_le : a ≤ x'' := by
                  by_contra hgt; push_neg at hgt
                  exact h_adj_x''s.2.2.2 a h_adj_ab.1 ⟨hgt, h_adj_ab.2.2.1⟩
                exact le_antisymm ha_le (by
                  by_contra hlt; push_neg at hlt
                  exact h_adj_ab.2.2.2 x'' hx''_dom ⟨hlt, hx''_lt_start⟩)
              rw [ha_eq, hb_eq]; exact h_cond_i.2
            · -- b ≤ x''
              push_neg at h_b_gt_x''
              exact h_guard_y a b h_adj_ab h_le_a h_b_gt_x'',
          fun w hw hyw hws => by
            -- w ∈ χ.dom with y < w < pt. Case split on w vs x''.
            rcases lt_or_eq_of_le (not_lt.mp fun h =>
              h_adj_x''s.2.2.2 w hw ⟨h, hws⟩) with hwx'' | hwx''
            · -- w < x'': use h_dom_guard_y from hypothesis
              exact h_dom_guard_y w hw hyw hwx''
            · -- w = x'': ξ ∈ f(x'') from condition (i) via conj_left_mcs
              rw [hwx'']
              exact conj_left_mcs fc h_mcs_x'' ξ (Formula.snce η ξ) h_cond_i.1⟩⟩
      -- Termination: (dom.filter (· < x'')).card < (dom.filter (· < pt)).card
      have h_term : (χ.dom.filter (fun v => v < x'')).card < (χ.dom.filter (fun v => v < pt)).card := by
        apply Finset.card_lt_card
        constructor
        · intro v hv
          have hv_dom := (Finset.mem_filter.mp hv).1
          have hv_lt : v < x'' := (Finset.mem_filter.mp hv).2
          exact Finset.mem_filter.mpr ⟨hv_dom, lt_trans hv_lt hx''_lt_start⟩
        · simp only [Finset.not_subset]
          exact ⟨x'', Finset.mem_filter.mpr ⟨hx''_dom, hx''_lt_start⟩,
            fun h => absurd (Finset.mem_filter.mp h).2 (lt_irrefl _)⟩
      -- Recurse
      have r := c5_backward_walk fc χ h_c0 h_c2' ξ η x'' hx''_dom h_snce_x'' h_no_wit_x''
      -- Compose: guard at (x'', pt) from condition (i) + recursive guard from x''
      exact { val := r.val
              dom_sub := r.dom_sub
              c0 := r.c0
              c2' := r.c2'
              f_agrees := r.f_agrees
              g_agrees := r.g_agrees
              witness := r.witness
              witness_mem := r.witness_mem
              witness_lt := lt_trans r.witness_lt hx''_lt_start
              witness_event := r.witness_event
              witness_guard := by
                intro a b h_adj_ab h_le_a h_le_b
                by_cases h_b_le_x'' : b ≤ x''
                · exact r.witness_guard a b h_adj_ab h_le_a h_b_le_x''
                · -- b > x''. Show a = x'' and b = pt, then use condition (i) guard.
                  push_neg at h_b_le_x''
                  have hb_eq : b = pt := by
                    by_contra hb_ne
                    have hb_lt : b < pt := lt_of_le_of_ne h_le_b hb_ne
                    by_cases hb_old : b ∈ χ.dom
                    · exact h_adj_x''s.2.2.2 b hb_old ⟨h_b_le_x'', hb_lt⟩
                    · -- b is new from recursion at x'', so b < x'' by new_point_before. Contradicts b > x''.
                      exact absurd (r.new_point_before b h_adj_ab.2.1 hb_old) (not_lt.mpr (le_of_lt h_b_le_x''))
                  subst hb_eq
                  -- a must be x'': x'' in val.dom, a < pt, nothing between a and pt
                  have ha_eq : a = x'' := by
                    have hx''_val : x'' ∈ r.val.dom := r.dom_sub hx''_dom
                    by_contra ha_ne
                    rcases lt_or_gt_of_ne ha_ne with ha_lt | ha_gt
                    · -- a < x'': then x'' is between a and pt=b, contradicting adjacency
                      exact h_adj_ab.2.2.2 x'' hx''_val ⟨ha_lt, hx''_lt_start⟩
                    · -- a > x'': a ∈ r.val.dom, x'' < a < pt. If old, contradicts h_adj_x''s.
                      -- If new, new_point_before gives a < x'', contradiction.
                      by_cases ha_old : a ∈ χ.dom
                      · exact h_adj_x''s.2.2.2 a ha_old ⟨ha_gt, h_adj_ab.2.2.1⟩
                      · exact absurd (r.new_point_before a h_adj_ab.1 ha_old) (not_lt.mpr (le_of_lt ha_gt))
                  rw [ha_eq, r.g_agrees x'' _ hx''_dom h_start_mem]
                  exact h_cond_i.2
              g_sub_f_insert := r.g_sub_f_insert
              g_sub_g_new := r.g_sub_g_new
              dom_new_unique := r.dom_new_unique
              new_point_before := by
                intro w hw hw_not
                exact lt_trans (r.new_point_before w hw hw_not) hx''_lt_start
              domain_guard := by
                -- Condition (i): ξ ∧ (ξ S η) ∈ f(x''), so ξ ∈ f(x'') by conj_left_mcs.
                -- For w between x'' and start: vacuous (x'' is immediate predecessor).
                -- For w between witness and x'': from recursive domain_guard.
                intro w hw hwr hws
                rcases lt_or_eq_of_le (not_lt.mp fun h =>
                  h_adj_x''s.2.2.2 w hw ⟨h, hws⟩) with hwx'' | hwx''
                · -- w < x'', use recursive domain_guard
                  exact r.domain_guard w hw hwr hwx''
                · -- w = x'', use condition (i)
                  rw [hwx'', r.f_agrees x'' hx''_dom]
                  exact conj_left_mcs fc h_mcs_x'' ξ (Formula.snce η ξ) h_cond_i.1
              witness_not_old := r.witness_not_old }
    · -- **Not condition (i)**: split at (x'', pt)
      have h_split_result : ∃ B' D B'' : Set (Formula Atom),
          BurgessR3Maximal fc (χ.f x'') B' D ∧
          BurgessR3Maximal fc D B'' (χ.f pt) ∧
          SetMaximalConsistent fc D ∧
          η ∈ D ∧
          χ.g x'' pt ⊆ D ∧
          χ.g x'' pt ⊆ B' ∧
          χ.g x'' pt ⊆ B'' ∧
          ξ ∈ B'' := by
        by_cases h_eta_g : η ∈ χ.g x'' pt
        · by_cases h_xi_g : ξ ∈ χ.g x'' pt
          · -- η ∈ g, ξ ∈ g: use lemma_2_8_since (avoids needing SetConsistent g)
            have h_conj_not_f : Formula.and ξ (Formula.snce η ξ) ∉ χ.f x'' :=
              fun h => h_cond_i ⟨h, h_xi_g⟩
            have h_neg_disj : (Formula.or η (Formula.and ξ (Formula.snce η ξ))).neg ∈ χ.f x'' := by
              have h1 : η.neg ∈ χ.f x'' := by
                rcases SetMaximalConsistent.negation_complete h_mcs_x'' η with h | h
                · exact absurd h (h_guard_implies_no_event h_xi_g)
                · exact h
              have h2 : (Formula.and ξ (Formula.snce η ξ)).neg ∈ χ.f x'' := by
                rcases SetMaximalConsistent.negation_complete h_mcs_x''
                  (Formula.and ξ (Formula.snce η ξ)) with h | h
                · exact absurd h h_conj_not_f
                · exact h
              exact SetMaximalConsistent.implication_property h_mcs_x''
                (theorem_in_mcs_fc h_mcs_x''
                  (liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.demorgan_disj_neg_backward η
                    (Formula.and ξ (Formula.snce η ξ)))))
                (conj_mcs fc h_mcs_x'' η.neg (Formula.and ξ (Formula.snce η ξ)).neg h1 h2)
            obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
              lemma_2_8_since fc h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_since_start h_neg_disj
            exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB'' h_xi_g⟩
          · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B''⟩ :=
              lemma_2_7_since fc h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_since_start h_xi_g
            exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B''⟩
        · by_cases h_eta_neg_g : η.neg ∈ χ.g x'' pt
          · by_cases h_xi_g : ξ ∈ χ.g x'' pt
            · by_cases h_conj_g : Formula.and ξ (Formula.snce η ξ) ∈ χ.g x'' pt
              · -- conj in g but not-condition(i): conj not in f(x'')
                have h_conj_not_f : Formula.and ξ (Formula.snce η ξ) ∉ χ.f x'' :=
                  fun h => h_cond_i ⟨h, h_xi_g⟩
                have h_neg_disj : (Formula.or η (Formula.and ξ (Formula.snce η ξ))).neg ∈ χ.f x'' := by
                  have h1 : η.neg ∈ χ.f x'' := by
                    rcases SetMaximalConsistent.negation_complete h_mcs_x'' η with h | h
                    · exact absurd h (h_guard_implies_no_event h_xi_g)
                    · exact h
                  have h2 : (Formula.and ξ (Formula.snce η ξ)).neg ∈ χ.f x'' := by
                    rcases SetMaximalConsistent.negation_complete h_mcs_x''
                      (Formula.and ξ (Formula.snce η ξ)) with h | h
                    · exact absurd h h_conj_not_f
                    · exact h
                  exact SetMaximalConsistent.implication_property h_mcs_x''
                    (theorem_in_mcs_fc h_mcs_x''
                      (liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.demorgan_disj_neg_backward η
                        (Formula.and ξ (Formula.snce η ξ)))))
                    (conj_mcs fc h_mcs_x'' η.neg (Formula.and ξ (Formula.snce η ξ)).neg h1 h2)
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
                  lemma_2_8_since fc h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_since_start h_neg_disj
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB'' h_xi_g⟩
              · have h_bx5 := self_accum_since_mcs fc h_mcs_start ξ η h_since_start
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, hBB', h_B_sub_D, hBB'', _⟩ :=
                  lemma_2_7_since fc h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj
                    (Formula.and ξ (Formula.snce η ξ)) η h_bx5 h_conj_g
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB'' h_xi_g⟩
            · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B''⟩ :=
                lemma_2_7_since fc h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_since_start h_xi_g
              exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B''⟩
          · by_cases h_xi_g2 : ξ ∈ χ.g x'' pt
            · have h_sp := lemma_2_6_splitting fc h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj
                η.neg h_eta_neg_g
              obtain ⟨B', D, B'', hB', hB'', hD_mcs, h_dne_D, h_B_sub_D, hBB', hBB''⟩ := h_sp
              exact ⟨B', D, B'', hB', hB'', hD_mcs,
                SetMaximalConsistent.implication_property hD_mcs
                  (theorem_in_mcs_fc hD_mcs (Cslib.Logic.Bimodal.Theorems.Propositional.double_negation η)) h_dne_D,
                h_B_sub_D, hBB', hBB'', hBB'' h_xi_g2⟩
            · obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, hBB', h_B_sub_D, hBB'', h_xi_B''⟩ :=
                lemma_2_7_since fc h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_since_start h_xi_g2
              exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', h_xi_B''⟩
      let B' := h_split_result.choose
      let D := h_split_result.choose_spec.choose
      let B'' := h_split_result.choose_spec.choose_spec.choose
      have h_split_prop := h_split_result.choose_spec.choose_spec.choose_spec
      have h_B'_max : BurgessR3Maximal fc (χ.f x'') B' D := h_split_prop.1
      have h_B''_max : BurgessR3Maximal fc D B'' (χ.f pt) := h_split_prop.2.1
      have h_D_mcs : SetMaximalConsistent fc D := h_split_prop.2.2.1
      have h_eta_D : η ∈ D := h_split_prop.2.2.2.1
      have h_g_sub_D : χ.g x'' pt ⊆ D := h_split_prop.2.2.2.2.1
      have h_g_sub_B' : χ.g x'' pt ⊆ B' := h_split_prop.2.2.2.2.2.1
      have h_g_sub_B'' : χ.g x'' pt ⊆ B'' := h_split_prop.2.2.2.2.2.2.1
      have h_xi_B'' : ξ ∈ B'' := h_split_prop.2.2.2.2.2.2.2
      set z := (x'' + pt) / 2 with hz_def
      have hz_lt_pt : z < pt := by linarith
      have hx''_lt_z : x'' < z := by linarith
      have hz_notin : z ∉ χ.dom := by
        intro h_mem_z; exact h_adj_x''s.2.2.2 z h_mem_z ⟨hx''_lt_z, hz_lt_pt⟩
      let g' := fun a b =>
        if a = x'' ∧ b = z then B'
        else if a = z ∧ b = pt then B''
        else χ.g a b
      let val : Chronicle Atom := ⟨fun q => if q = z then D else χ.f q, g', insert z χ.dom⟩
      have h_c2'_new : val.c2' fc := by
        intro a b h_adj_new
        obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
        simp only [val, Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd hab (lt_irrefl _)
        · have hb_eq : b = pt := by
            by_contra hb_ne
            have hb_ge : pt ≤ b := by
              by_contra hlt; push_neg at hlt
              exact h_adj_x''s.2.2.2 b hb ⟨lt_trans hx''_lt_z hab, hlt⟩
            exact h_no_between pt (Finset.mem_insert_of_mem h_start_mem) ⟨hz_lt_pt, lt_of_le_of_ne hb_ge (Ne.symm hb_ne)⟩
          subst hb_eq
          show BurgessR3Maximal fc (if z = z then D else χ.f z) (g' z b) (if b = z then D else χ.f b)
          have hz_ne_x'' : z ≠ x'' := ne_of_gt hx''_lt_z
          have hb_ne_z : b ≠ z := ne_of_gt hz_lt_pt
          simp only [ite_true, hb_ne_z, ite_false, g', hz_ne_x'', false_and, ite_false, and_self, ite_true]
          exact h_B''_max
        · -- a is in old domain, a < z. Show a = x''.
          have ha_le_x'' : a ≤ x'' := by
            by_contra hgt; push_neg at hgt
            exact h_adj_x''s.2.2.2 a ha ⟨hgt, lt_trans hab hz_lt_pt⟩
          have ha_eq_x'' : a = x'' := by
            by_contra ha_ne
            exact h_no_between x'' (Finset.mem_insert_of_mem hx''_dom) ⟨lt_of_le_of_ne ha_le_x'' ha_ne, hx''_lt_z⟩
          subst ha_eq_x''
          dsimp only [val, g']
          simp only [ne_of_lt hx''_lt_z, if_false, if_true, and_self, if_true, ne_of_gt hx''_lt_z]
          exact h_B'_max
        · have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
          have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
          show BurgessR3Maximal fc (if a = z then D else χ.f a) (g' a b) (if b = z then D else χ.f b)
          simp only [ha_ne, hb_ne, ite_false, g', and_false, false_and]
          exact h_c2' a b ⟨ha, hb, hab, fun u hu huab => h_no_between u (Finset.mem_insert_of_mem hu) huab⟩
      exact { val := val
              dom_sub := Finset.subset_insert z χ.dom
              c0 := by
                intro q hq; show SetMaximalConsistent fc (if q = z then D else χ.f q)
                simp only [val, Finset.mem_insert] at hq
                rcases hq with rfl | hq
                · simp only [ite_true]; exact h_D_mcs
                · simp only [show q ≠ z from fun h => hz_notin (h ▸ hq), ite_false]; exact h_c0 q hq
              c2' := h_c2'_new
              f_agrees := by
                intro x hx; dsimp only [val]
                have hx_ne_z : x ≠ z := by intro h; exact hz_notin (h ▸ hx)
                simp only [hx_ne_z, if_false]
              g_agrees := by
                intro a b ha hb; show g' a b = χ.g a b; simp only [g']
                simp only [show a ≠ z from fun h => hz_notin (h ▸ ha),
                  show b ≠ z from fun h => hz_notin (h ▸ hb), false_and, and_false, ite_false]
              witness := z
              witness_mem := Finset.mem_insert_self z χ.dom
              witness_lt := hz_lt_pt
              witness_event := by show η ∈ (if z = z then D else χ.f z); simp only [ite_true]; exact h_eta_D
              witness_guard := by
                intro a b h_adj_ab h_le_a h_le_b
                obtain ⟨ha_dom, hb_dom, hab_lt, h_no_btw⟩ := h_adj_ab
                simp only [val, Finset.mem_insert] at ha_dom hb_dom
                have hb_eq : b = pt := by
                  by_contra hb_ne
                  have hb_lt : b < pt := lt_of_le_of_ne h_le_b hb_ne
                  rcases hb_dom with rfl | hb_mem
                  · -- b = z: then a < z and z ≤ a, contradiction
                    exact absurd h_le_a (not_le.mpr hab_lt)
                  · -- b ∈ old dom, b < pt, and z ≤ a < b so x'' < z ≤ a < b < pt
                    exact h_adj_x''s.2.2.2 b hb_mem
                      ⟨lt_of_lt_of_le hx''_lt_z (le_trans h_le_a (le_of_lt hab_lt)), hb_lt⟩
                subst hb_eq
                have ha_eq : a = z := by
                  by_contra ha_ne
                  -- z ≤ a and a ≠ z gives z < a
                  have ha_gt : z < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
                  -- z < a < b = pt, so a is between z and pt. But z ∈ val.dom...
                  -- Actually, a > z. After subst hb_eq, b = pt. So a < pt (from hab_lt).
                  -- a ∈ val.dom, z < a < pt. z ∈ val.dom. So h_no_btw z gives contradiction... no, h_no_btw says no points between a and b.
                  -- Actually adjacency h_no_btw says ¬∃ u, u between a and b.
                  -- We have z < a and z ∈ val.dom... but z is NOT between a and b since a > z.
                  -- The right approach: if a ∈ χ.dom, then x'' < a < pt (since a > z > x''), contradicting h_adj_x''s.
                  -- If a ∉ χ.dom, then a is a new point. But there are no new points in val (this is the split case, not recursion).
                  -- Actually, this is the split case in c5_backward_walk. val = insert z χ.dom. The only new point is z.
                  -- So a ∈ val.dom means a = z ∨ a ∈ χ.dom. Since a ≠ z, a ∈ χ.dom.
                  rcases ha_dom with rfl | ha_mem
                  · exact absurd (le_refl z) (not_le.mpr ha_gt)
                  · -- a ∈ χ.dom, z < a, and a < b = pt. So x'' < z < a < pt, contradicts h_adj_x''s.
                    exact h_adj_x''s.2.2.2 a ha_mem ⟨lt_trans hx''_lt_z ha_gt, hab_lt⟩
                subst ha_eq
                -- Need: ξ ∈ g'(z, b) where b = pt (after subst). g' checks:
                -- z = x'' ∧ b = z? No (z ≠ x''). Then z = z ∧ b = pt? Yes. Result: B''.
                show ξ ∈ g' z b
                simp only [g', show z ≠ x'' from ne_of_gt hx''_lt_z, false_and, ite_false, and_self, ite_true]
                exact h_xi_B''
              g_sub_f_insert := by
                intro a b h_adj w hw hw_not haw hwb
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · show χ.g a b ⊆ (if z = z then D else χ.f z); simp only [ite_true]
                  have hab : a = x'' ∧ b = pt := by
                    constructor
                    · by_contra ha_ne
                      rcases lt_or_gt_of_ne ha_ne with h | h
                      · exact h_adj.2.2.2 x'' hx''_dom ⟨h, lt_trans hx''_lt_z hwb⟩
                      · exact h_adj_x''s.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_pt⟩
                    · by_contra hb_ne
                      rcases lt_or_gt_of_ne hb_ne with h | h
                      · exact h_adj_x''s.2.2.2 b h_adj.2.1 ⟨lt_trans hx''_lt_z hwb, h⟩
                      · exact h_adj.2.2.2 pt h_start_mem ⟨lt_trans haw hz_lt_pt, h⟩
                  rw [hab.1, hab.2]; exact h_g_sub_D
                · exact absurd hw hw_not
              g_sub_g_new := by
                intro a b h_adj w hw hw_not haw hwb
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · have ha_eq : a = x'' := by
                    by_contra ha_ne
                    rcases lt_or_gt_of_ne ha_ne with h | h
                    · exact h_adj.2.2.2 x'' hx''_dom ⟨h, lt_trans hx''_lt_z hwb⟩
                    · exact h_adj_x''s.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_pt⟩
                  have hb_eq : b = pt := by
                    by_contra hb_ne
                    rcases lt_or_gt_of_ne hb_ne with h | h
                    · exact h_adj_x''s.2.2.2 b h_adj.2.1 ⟨lt_trans hx''_lt_z hwb, h⟩
                    · exact h_adj.2.2.2 pt h_start_mem ⟨lt_trans haw hz_lt_pt, h⟩
                  subst ha_eq; subst hb_eq; constructor
                  · dsimp only [val, g']; simp only [and_self, if_true]; exact h_g_sub_B'
                  · dsimp only [val, g']
                    simp only [ne_of_gt hx''_lt_z, false_and, if_false, and_self, if_true]
                    exact h_g_sub_B''
                · exact absurd hw hw_not
              dom_new_unique := by
                intro u v hu hu_not hv hv_not
                simp only [val, Finset.mem_insert] at hu hv
                rcases hu with rfl | hu <;> rcases hv with rfl | hv
                · rfl
                · exact absurd hv hv_not
                · exact absurd hu hu_not
                · exact absurd hu hu_not
              new_point_before := by
                intro w hw hw_not
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · exact hz_lt_pt
                · exact absurd hw hw_not
              domain_guard := by
                -- Split case: witness = z (midpoint between x'' and start).
                -- No w ∈ χ.dom with z < w < pt exists (adjacency of (x'', pt)).
                intro w hw hwz hws
                exact absurd ⟨lt_trans hx''_lt_z hwz, hws⟩
                  (h_adj_x''s.2.2.2 w hw)
              witness_not_old := hz_notin }
termination_by (χ.dom.filter (fun v => v < pt)).card
decreasing_by
  all_goals simp_all only [gt_iff_lt]
  all_goals exact h_term

/--
Attempt to eliminate a potential counterexample. If it is not an actual
counterexample for the current chronicle, the chronicle is returned unchanged.
Otherwise, a new chronicle with the counterexample eliminated is returned.

Returns an `EliminationResult` bundling domain extension, C0, f-agreement,
and C5/C5' witness guarantees.
-/
noncomputable def eliminate_potential_counterexample (fc : FrameClass)
    (χ : Chronicle Atom) (h_c0 : χ.c0 fc) (h_c2' : χ.c2' fc)
    (pc : PotentialCounterexample)
    :
    EliminationResult fc χ pc := by
  -- Helper for impossible kind discriminants
  have absurd_kind {k : PotentialCounterexampleKind} {Q : Prop}
      (h : k = .c5_forward) (hk : k = .c4_forward ∨ k = .c4_backward ∨ k = .c5_backward) : Q :=
    by rcases hk with rfl | rfl | rfl <;> exact absurd h (by decide)
  match h_kind : pc.kind with
  | .c5_forward =>
    -- Forward (Until) C5 case
    -- Burgess C5a counterexample check (g-value based per Burgess 2.10):
    -- Actual counterexample iff NO y exists with event ∈ f(y) AND guard ∈ g(x,y).
    by_cases h_actual : pc.x ∈ χ.dom ∧ Formula.untl pc.η pc.ξ ∈ χ.f pc.x ∧
        ¬∃ y ∈ χ.dom, pc.x < y ∧ pc.η ∈ χ.f y ∧
          (∀ a b, Adjacent χ.dom a b → pc.x ≤ a → b ≤ y → pc.ξ ∈ χ.g a b) ∧
          (∀ w ∈ χ.dom, pc.x < w → w < y → pc.ξ ∈ χ.f w)
    · obtain ⟨h_mem, h_until, h_no_wit⟩ := h_actual
      have h_mcs_x := h_c0 pc.x h_mem
      have h_dom_ne : χ.dom.Nonempty := ⟨pc.x, h_mem⟩
      set max_old := χ.dom.max' h_dom_ne with max_old_def
      have h_max_mem : max_old ∈ χ.dom := Finset.max'_mem χ.dom h_dom_ne
      have h_max_le : ∀ s ∈ χ.dom, s ≤ max_old := fun s hs => Finset.le_max' χ.dom s hs
      -- Split on whether pc.x is the last point (n=0) or not (n≥1)
      by_cases h_eq_max : pc.x = max_old
      · -- **Case n=0**: pc.x is the maximum domain point.
        -- Use Lemma 2.4: place y after all points (only new pair is (pc.x, y)).
        have h_fresh := exists_rat_gt_finset χ.dom
        let y := h_fresh.choose
        have hy_gt : ∀ s ∈ χ.dom, s < y := h_fresh.choose_spec.1
        have hy_notin : y ∉ χ.dom := h_fresh.choose_spec.2
        have h_l24 := lemma_2_4_with_guard fc h_mcs_x pc.ξ pc.η h_until
        let B := h_l24.choose
        let C := h_l24.choose_spec.choose
        have h_l24_prop := h_l24.choose_spec.choose_spec
        have h_C_mcs : SetMaximalConsistent fc C := h_l24_prop.1
        have h_η_C : pc.η ∈ C := h_l24_prop.2.1
        have h_ξ_B : pc.ξ ∈ B := h_l24_prop.2.2.2.2.1
        have h_r3m : BurgessR3Maximal fc (χ.f pc.x) B C := h_l24_prop.2.2.2.2.2
        have h_max_lt_y : max_old < y := hy_gt max_old h_max_mem
        let g' := fun a b =>
          if a = max_old ∧ b = y then B
          else χ.g a b
        let χ' : Chronicle Atom := ⟨fun q => if q = y then C else χ.f q, g', insert y χ.dom⟩
        have h_c2'_new : χ'.c2' fc := by
          intro a b h_adj_new
          obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
          simp only [χ', Finset.mem_insert] at ha hb
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact absurd hab (lt_irrefl _)
          · exact absurd hab (not_lt.mpr (le_of_lt (hy_gt b hb)))
          · have ha_eq : a = max_old := by
              by_contra ha_ne
              have ha_le : a ≤ max_old := h_max_le a ha
              have ha_lt : a < max_old := lt_of_le_of_ne ha_le ha_ne
              exact h_no_between max_old (Finset.mem_insert_of_mem h_max_mem) ⟨ha_lt, h_max_lt_y⟩
            subst ha_eq
            show BurgessR3Maximal fc
              (if max_old = y then C else χ.f max_old)
              (g' max_old y)
              (if y = y then C else χ.f y)
            have hmax_ne_y : max_old ≠ y := ne_of_lt h_max_lt_y
            simp only [hmax_ne_y, ite_false, ite_true, g']
            simp only [and_self, ite_true]
            rw [← h_eq_max]; exact h_r3m
          · have ha_ne : a ≠ y := fun h => hy_notin (h ▸ ha)
            have hb_ne : b ≠ y := fun h => hy_notin (h ▸ hb)
            show BurgessR3Maximal fc
              (if a = y then C else χ.f a)
              (g' a b)
              (if b = y then C else χ.f b)
            simp only [ha_ne, hb_ne, ite_false]
            show BurgessR3Maximal fc (χ.f a)
              (if a = max_old ∧ b = y then B else χ.g a b) (χ.f b)
            rw [if_neg (fun ⟨_, hby⟩ => hb_ne hby)]
            have h_adj_old : Adjacent χ.dom a b := by
              refine ⟨ha, hb, hab, ?_⟩
              intro u hu ⟨hau, hub⟩
              exact h_no_between u (Finset.mem_insert_of_mem hu) ⟨hau, hub⟩
            exact h_c2' a b h_adj_old
        exact { val := χ'
                dom_sub := Finset.subset_insert y χ.dom
                c0 := by
                  intro q hq
                  show SetMaximalConsistent fc (if q = y then C else χ.f q)
                  change q ∈ insert y χ.dom at hq
                  simp only [Finset.mem_insert] at hq
                  rcases hq with rfl | hq
                  · simp only [ite_true]; exact h_C_mcs
                  · have h_ne : q ≠ y := fun h => hy_notin (h ▸ hq)
                    simp only [h_ne, ite_false]; exact h_c0 q hq
                f_agrees := by
                  intro x hx
                  have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
                  exact if_neg h_ne
                g_agrees := by
                  intro a b ha hb
                  show g' a b = χ.g a b
                  simp only [g']
                  have hb_ne : b ≠ y := fun h => hy_notin (h ▸ hb)
                  simp only [hb_ne, and_false, ite_false]
                c2' := h_c2'_new
                c5_forward_witness := by
                  intro _ _ _
                  refine ⟨y, Finset.mem_insert_self y χ.dom, hy_gt pc.x h_mem, ?_, ?_, ?_, ?_⟩
                  · simp only [χ', ite_true]; exact h_η_C
                  · -- Adjacent-pair guard: only pair (a,b) with pc.x ≤ a, b ≤ y is (max_old, y)
                    intro a b h_adj_ab h_le_a h_le_b
                    have ha_dom : a ∈ insert y χ.dom := h_adj_ab.1
                    have hb_dom : b ∈ insert y χ.dom := h_adj_ab.2.1
                    simp only [Finset.mem_insert] at ha_dom hb_dom
                    -- b must be y (b ≤ y and b > a ≥ pc.x = max_old ≥ all old)
                    have hb_eq : b = y := by
                      rcases hb_dom with rfl | hb_old
                      · rfl
                      · -- b is old, so b ≤ max_old; but a < b and a ≥ pc.x = max_old
                        have : b ≤ max_old := h_max_le b hb_old
                        linarith [h_adj_ab.2.2.1]
                    subst hb_eq
                    -- a must be max_old (a ∈ old dom since a ≠ y, and a is maximal with a < y)
                    have ha_ne_y : a ≠ y := ne_of_lt h_adj_ab.2.2.1
                    have ha_old : a ∈ χ.dom := by
                      rcases ha_dom with rfl | h
                      · exact absurd rfl ha_ne_y
                      · exact h
                    have ha_eq : a = max_old := by
                      have ha_le_max : a ≤ max_old := h_max_le a ha_old
                      have hmax_le_a : max_old ≤ a := by
                        by_contra hlt; push_neg at hlt
                        exact h_adj_ab.2.2.2 max_old
                          (Finset.mem_insert_of_mem h_max_mem) ⟨hlt, h_max_lt_y⟩
                      exact le_antisymm ha_le_max hmax_le_a
                    subst ha_eq
                    show pc.ξ ∈ g' max_old y
                    simp only [g', and_self, ite_true]
                    exact h_ξ_B
                  · -- Domain guard: no w ∈ χ.dom with pc.x < w < y (pc.x = max_old ≥ all old)
                    intro w hw hxw _
                    exact absurd (h_max_le w hw) (not_le.mpr (h_eq_max ▸ hxw))
                  · exact Or.inl hy_notin
                c5_backward_witness := fun h => absurd h (by rw [h_kind] at h; exact absurd h (by decide))
                c4_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
                c4_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)

                g_sub_f_insert := by
                  intro a b h_adj w hw hw_not haw hwb
                  simp only [χ', Finset.mem_insert] at hw
                  rcases hw with rfl | hw
                  · exact absurd hwb (not_lt.mpr (le_of_lt (hy_gt b h_adj.2.1)))
                  · exact absurd hw hw_not
                g_sub_g_new := by
                  intro a b h_adj w hw hw_not haw hwb
                  simp only [χ', Finset.mem_insert] at hw
                  rcases hw with rfl | hw
                  · exact absurd hwb (not_lt.mpr (le_of_lt (hy_gt b h_adj.2.1)))
                  · exact absurd hw hw_not
                dom_new_unique := by
                  intro u v hu hu_not hv hv_not
                  simp only [χ', Finset.mem_insert] at hu hv
                  rcases hu with rfl | hu <;> rcases hv with rfl | hv
                  · rfl
                  · exact absurd hv hv_not
                  · exact absurd hu hu_not
                  · exact absurd hu hu_not
                c5_forward_resolved_no_new := fun _ _ _ h_wit => absurd h_wit h_no_wit
                c5_backward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide) }
      · -- **Case n≥1**: pc.x is NOT the maximum. Burgess 2.10 induction case.
        -- Find x' = immediate successor of pc.x in dom.
        set T_succ := χ.dom.filter (fun v => decide (pc.x < v)) with T_succ_def
        have hT_ne : T_succ.Nonempty := by
          have h_pc_lt_max : pc.x < max_old := lt_of_le_of_ne (h_max_le pc.x h_mem) h_eq_max
          exact ⟨max_old, Finset.mem_filter.mpr ⟨h_max_mem, by simp [h_pc_lt_max]⟩⟩
        set x' := T_succ.min' hT_ne with x'_def
        have hx'_mem_T := Finset.min'_mem T_succ hT_ne
        have hx'_dom : x' ∈ χ.dom := (Finset.mem_filter.mp hx'_mem_T).1
        have hx_lt_x' : pc.x < x' := by
          have := (Finset.mem_filter.mp hx'_mem_T).2
          simp only [decide_eq_true_eq] at this; exact this
        have h_adj_xx' : Adjacent χ.dom pc.x x' := by
          refine ⟨h_mem, hx'_dom, hx_lt_x', ?_⟩
          intro u hu ⟨hxu, hux'⟩
          have hu_T : u ∈ T_succ := Finset.mem_filter.mpr ⟨hu, by simp [hxu]⟩
          have := Finset.min'_le T_succ u hu_T
          linarith
        -- Key fact: x' is NOT a C5 witness (eta ∉ f(x')), because x' is adjacent
        -- to pc.x so the guard condition is vacuous, and h_no_wit would be violated.
        have h_mcs_x' := h_c0 x' hx'_dom
        -- Burgess 2.10 (ii): guard ∈ g(x,x') implies event ∉ f(x')
        have h_guard_implies_no_event : pc.ξ ∈ χ.g pc.x x' → pc.η ∉ χ.f x' :=
          fun h_guard h_event => h_no_wit ⟨x', hx'_dom, hx_lt_x', h_event,
            ⟨fun a b h_adj_ab h_le_a h_le_b => by
              have ha_eq : a = pc.x := by
                by_contra ha_ne
                have ha_gt : pc.x < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
                exact h_adj_xx'.2.2.2 a h_adj_ab.1 ⟨ha_gt, lt_of_lt_of_le h_adj_ab.2.2.1 h_le_b⟩
              have hb_eq : b = x' := by
                rw [ha_eq] at h_adj_ab
                by_contra hb_ne
                have hb_lt : b < x' := lt_of_le_of_ne h_le_b hb_ne
                exact h_adj_xx'.2.2.2 b h_adj_ab.2.1 ⟨h_adj_ab.2.2.1, hb_lt⟩
              rw [ha_eq, hb_eq]; exact h_guard,
            fun w hw hsw hwx' => absurd ⟨hsw, hwx'⟩ (h_adj_xx'.2.2.2 w hw)⟩⟩
        -- Get BurgessR3Maximal fc for the adjacent pair (pc.x, x') from c2'
        have h_r3m_adj := h_c2' pc.x x' h_adj_xx'
        have h_gc_adj := BurgessR3Maximal_g_content_sub h_r3m_adj h_mcs_x h_mcs_x'
        -- Burgess 2.10: check condition (i) — does the conjunction persist into f(x')
        -- AND is the guard in g(x, x')? Both parts are needed for the forward walk.
        -- If condition (i) holds, splitting at (pc.x, x') fails; use forward walk.
        -- If not, the existing splitting lemmas handle all cases.
        by_cases h_cond_i : Formula.and pc.ξ (Formula.untl pc.η pc.ξ) ∈ χ.f x' ∧ pc.ξ ∈ χ.g pc.x x'
        · -- **Condition (i)**: use recursive walk helper (Burgess 2.10 induction).
          let r := c5_forward_walk fc χ h_c0 h_c2' pc.ξ pc.η pc.x h_mem h_until h_no_wit
          exact { val := r.val
                  dom_sub := r.dom_sub
                  c0 := r.c0
                  f_agrees := r.f_agrees
                  g_agrees := r.g_agrees
                  c2' := r.c2'
                  c5_forward_witness := by
                    intro _ _ _
                    exact ⟨r.witness, r.witness_mem, r.witness_gt, r.witness_event,
                      r.witness_guard, r.domain_guard, Or.inl r.witness_not_old⟩
                  c5_backward_witness := fun h => absurd h (by rw [h_kind] at h; exact absurd h (by decide))
                  c4_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
                  c4_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)

                  g_sub_f_insert := r.g_sub_f_insert
                  g_sub_g_new := r.g_sub_g_new
                  dom_new_unique := r.dom_new_unique
                  c5_forward_resolved_no_new := fun _ _ _ h_wit => absurd h_wit h_no_wit
                  c5_backward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide) }
        · -- **Not condition (i)**: splitting at (pc.x, x') succeeds.
          -- Get the splitting result: B', D, B'' with eta ∈ D.
          -- Case split on eta ∈ g(pc.x, x'):
          have h_split_result : ∃ B' D B'' : Set (Formula Atom),
              BurgessR3Maximal fc (χ.f pc.x) B' D ∧
              BurgessR3Maximal fc D B'' (χ.f x') ∧
              SetMaximalConsistent fc D ∧
              pc.η ∈ D ∧
              χ.g pc.x x' ⊆ D ∧
              χ.g pc.x x' ⊆ B' ∧
              χ.g pc.x x' ⊆ B'' ∧
              pc.ξ ∈ B' := by
            by_cases h_eta_g : pc.η ∈ χ.g pc.x x'
            · by_cases h_xi_g : pc.ξ ∈ χ.g pc.x x'
              · -- η ∈ g, ξ ∈ g: use lemma_2_8 (avoids needing SetConsistent g)
                have h_conj_not_f : Formula.and pc.ξ (Formula.untl pc.η pc.ξ) ∉ χ.f x' :=
                  fun h_conj_f => h_cond_i ⟨h_conj_f, h_xi_g⟩
                have h_neg_disj : (Formula.or pc.η (Formula.and pc.ξ (Formula.untl pc.η pc.ξ))).neg ∈ χ.f x' := by
                  have h_neg_conj : (pc.η.neg.and (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)).neg) ∈ χ.f x' := by
                    have h1 : pc.η.neg ∈ χ.f x' := by
                      rcases SetMaximalConsistent.negation_complete h_mcs_x' pc.η with h | h
                      · exact absurd h (h_guard_implies_no_event h_xi_g)
                      · exact h
                    have h2 : (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)).neg ∈ χ.f x' := by
                      rcases SetMaximalConsistent.negation_complete h_mcs_x' (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)) with h | h
                      · exact absurd h h_conj_not_f
                      · exact h
                    exact conj_mcs fc h_mcs_x' pc.η.neg (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)).neg h1 h2
                  have h_dm := liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.demorgan_disj_neg_backward pc.η (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)))
                  exact SetMaximalConsistent.implication_property h_mcs_x'
                    (theorem_in_mcs_fc h_mcs_x' h_dm) h_neg_conj
                obtain ⟨B'2, D2, B''2, h_B'2, h_B''2, h_D2_mcs, h_eta_D2, h_B_sub_D2, h_B_sub_B'2, h_B_sub_B''2, _⟩ :=
                  lemma_2_8 fc h_mcs_x h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj pc.ξ pc.η h_until h_neg_disj
                exact ⟨B'2, D2, B''2, h_B'2, h_B''2, h_D2_mcs, h_eta_D2, h_B_sub_D2, h_B_sub_B'2, h_B_sub_B''2, h_B_sub_B'2 h_xi_g⟩
              · obtain ⟨B'3, D3, B''3, h_B'3, h_B''3, h_D3_mcs, h_eta_D3, h_B_sub_B'3, h_B_sub_D3, h_B_sub_B''3, h_xi_B'3⟩ :=
                  lemma_2_7 fc h_mcs_x h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj
                    pc.ξ pc.η h_until h_xi_g
                exact ⟨B'3, D3, B''3, h_B'3, h_B''3, h_D3_mcs, h_eta_D3, h_B_sub_D3, h_B_sub_B'3, h_B_sub_B''3, h_xi_B'3⟩
            · by_cases h_eta_neg_g : pc.η.neg ∈ χ.g pc.x x'
              · by_cases h_xi_g : pc.ξ ∈ χ.g pc.x x'
                · by_cases h_conj_g : Formula.and pc.ξ (Formula.untl pc.η pc.ξ) ∈ χ.g pc.x x'
                  · -- conj ∈ g and xi ∈ g but condition (i) fails: conj ∉ f(x'). Lemma 2.8 applies.
                    have h_conj_not_f : Formula.and pc.ξ (Formula.untl pc.η pc.ξ) ∉ χ.f x' :=
                      fun h_conj_f => h_cond_i ⟨h_conj_f, h_xi_g⟩
                    have h_neg_disj : (Formula.or pc.η (Formula.and pc.ξ (Formula.untl pc.η pc.ξ))).neg ∈ χ.f x' := by
                      have h_neg_conj : (pc.η.neg.and (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)).neg) ∈ χ.f x' := by
                        have h1 : pc.η.neg ∈ χ.f x' := by
                          rcases SetMaximalConsistent.negation_complete h_mcs_x' pc.η with h | h
                          · exact absurd h (h_guard_implies_no_event h_xi_g)
                          · exact h
                        have h2 : (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)).neg ∈ χ.f x' := by
                          rcases SetMaximalConsistent.negation_complete h_mcs_x' (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)) with h | h
                          · exact absurd h h_conj_not_f
                          · exact h
                        exact conj_mcs fc h_mcs_x' pc.η.neg (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)).neg h1 h2
                      have h_dm := liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.demorgan_disj_neg_backward pc.η (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)))
                      exact SetMaximalConsistent.implication_property h_mcs_x'
                        (theorem_in_mcs_fc h_mcs_x' h_dm) h_neg_conj
                    have h_l28 := lemma_2_8 fc h_mcs_x h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj
                      pc.ξ pc.η h_until h_neg_disj
                    obtain ⟨B'5, D5, B''5, h_B'5, h_B''5, h_D5_mcs, h_eta_D5, h_B_sub_D5, h_B_sub_B'5, h_B_sub_B''5, _⟩ := h_l28
                    exact ⟨B'5, D5, B''5, h_B'5, h_B''5, h_D5_mcs, h_eta_D5, h_B_sub_D5, h_B_sub_B'5, h_B_sub_B''5, h_B_sub_B'5 h_xi_g⟩
                  · have h_bx5 := self_accum_until_mcs fc h_mcs_x pc.ξ pc.η h_until
                    obtain ⟨B'6, D6, B''6, h_B'6, h_B''6, h_D6_mcs, h_eta_D6, h_B_sub_B'6, h_B_sub_D6, h_B_sub_B''6, h_conj_B'6⟩ :=
                      lemma_2_7 fc h_mcs_x h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj
                        (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)) pc.η h_bx5 h_conj_g
                    -- xi ∈ g and g ⊆ B'6 gives xi ∈ B'6
                    exact ⟨B'6, D6, B''6, h_B'6, h_B''6, h_D6_mcs, h_eta_D6, h_B_sub_D6, h_B_sub_B'6, h_B_sub_B''6, h_B_sub_B'6 h_xi_g⟩
                · obtain ⟨B'4, D4, B''4, h_B'4, h_B''4, h_D4_mcs, h_eta_D4, h_B_sub_B'4, h_B_sub_D4, h_B_sub_B''4, h_xi_B'4⟩ :=
                    lemma_2_7 fc h_mcs_x h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj
                      pc.ξ pc.η h_until h_xi_g
                  exact ⟨B'4, D4, B''4, h_B'4, h_B''4, h_D4_mcs, h_eta_D4, h_B_sub_D4, h_B_sub_B'4, h_B_sub_B''4, h_xi_B'4⟩
              · -- eta ∉ g, eta.neg ∉ g. Case split on xi ∈ g for the guard.
                by_cases h_xi_g6 : pc.ξ ∈ χ.g pc.x x'
                · -- xi ∈ g: use lemma_2_6 and derive xi ∈ B' from g ⊆ B'
                  have h_split5 := lemma_2_6_splitting fc h_mcs_x h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj
                    pc.η.neg h_eta_neg_g
                  obtain ⟨B'5, D5, B''5, h_B'5, h_B''5, h_D5_mcs, h_eta_neg_neg_D5, h_B_sub_D5, h_B_sub_B'5, h_B_sub_B''5⟩ := h_split5
                  have h_eta_D5 : pc.η ∈ D5 := by
                    have h_dne : DerivationTree fc [] (pc.η.neg.neg.imp pc.η) :=
                      Cslib.Logic.Bimodal.Theorems.Propositional.double_negation pc.η
                    exact SetMaximalConsistent.implication_property h_D5_mcs
                      (theorem_in_mcs_fc h_D5_mcs h_dne) h_eta_neg_neg_D5
                  exact ⟨B'5, D5, B''5, h_B'5, h_B''5, h_D5_mcs, h_eta_D5, h_B_sub_D5, h_B_sub_B'5, h_B_sub_B''5, h_B_sub_B'5 h_xi_g6⟩
                · -- xi ∉ g: use lemma_2_7 which returns xi ∈ B' directly
                  obtain ⟨B'5, D5, B''5, h_B'5, h_B''5, h_D5_mcs, h_eta_D5, h_B_sub_B'5, h_B_sub_D5, h_B_sub_B''5, h_xi_B'5⟩ :=
                    lemma_2_7 fc h_mcs_x h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj
                      pc.ξ pc.η h_until h_xi_g6
                  exact ⟨B'5, D5, B''5, h_B'5, h_B''5, h_D5_mcs, h_eta_D5, h_B_sub_D5, h_B_sub_B'5, h_B_sub_B''5, h_xi_B'5⟩
          let B' := h_split_result.choose
          let D := h_split_result.choose_spec.choose
          let B'' := h_split_result.choose_spec.choose_spec.choose
          have h_split_prop := h_split_result.choose_spec.choose_spec.choose_spec
          have h_B'_max : BurgessR3Maximal fc (χ.f pc.x) B' D := h_split_prop.1
          have h_B''_max : BurgessR3Maximal fc D B'' (χ.f x') := h_split_prop.2.1
          have h_D_mcs : SetMaximalConsistent fc D := h_split_prop.2.2.1
          have h_η_D : pc.η ∈ D := h_split_prop.2.2.2.1
          have h_g_sub_D : χ.g pc.x x' ⊆ D := h_split_prop.2.2.2.2.1
          have h_g_sub_B' : χ.g pc.x x' ⊆ B' := h_split_prop.2.2.2.2.2.1
          have h_g_sub_B'' : χ.g pc.x x' ⊆ B'' := h_split_prop.2.2.2.2.2.2.1
          have h_ξ_B' : pc.ξ ∈ B' := h_split_prop.2.2.2.2.2.2.2
          -- Insert z = midpoint of pc.x and x'
          set z := (pc.x + x') / 2 with hz_def
          have hz_lt_x' : z < x' := by linarith
          have hx_lt_z : pc.x < z := by linarith
          have hz_notin : z ∉ χ.dom := by
            intro h_mem_z; exact h_adj_xx'.2.2.2 z h_mem_z ⟨hx_lt_z, hz_lt_x'⟩
          -- Build new chronicle with f'(z) = D
          let g' := fun a b =>
            if a = pc.x ∧ b = z then B'
            else if a = z ∧ b = x' then B''
            else χ.g a b
          let χ' : Chronicle Atom := ⟨fun q => if q = z then D else χ.f q, g', insert z χ.dom⟩
          -- Prove c2' for the new chronicle
          have h_c2'_new : χ'.c2' fc := by
            intro a b h_adj_new
            obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
            simp only [χ', Finset.mem_insert] at ha hb
            rcases ha with rfl | ha <;> rcases hb with rfl | hb
            · exact absurd hab (lt_irrefl _)
            · -- a = z, b ∈ old dom: must be (z, x')
              have hb_eq : b = x' := by
                by_contra hb_ne
                have hb_ge : x' ≤ b := by
                  by_contra hlt; push_neg at hlt
                  have : pc.x < b := lt_trans hx_lt_z hab
                  exact h_adj_xx'.2.2.2 b hb ⟨this, hlt⟩
                have hb_gt : x' < b := lt_of_le_of_ne hb_ge (Ne.symm hb_ne)
                exact h_no_between x' (Finset.mem_insert_of_mem hx'_dom) ⟨hz_lt_x', hb_gt⟩
              subst hb_eq
              show BurgessR3Maximal fc
                (if z = z then D else χ.f z)
                (g' z x')
                (if x' = z then D else χ.f x')
              have hx'_ne : x' ≠ z := by linarith
              simp only [ite_true, hx'_ne, ite_false, g']
              simp only [ite_false, ite_true, and_false, and_self]
              exact h_B''_max
            · -- a ∈ old dom, b = z: must be (pc.x, z)
              have ha_eq : a = pc.x := by
                by_contra ha_ne
                have ha_le : a ≤ pc.x := by
                  by_contra hgt; push_neg at hgt
                  exact h_adj_xx'.2.2.2 a ha ⟨hgt, lt_trans hab hz_lt_x'⟩
                have ha_lt : a < pc.x := lt_of_le_of_ne ha_le ha_ne
                exact h_no_between pc.x (Finset.mem_insert_of_mem h_mem) ⟨ha_lt, hx_lt_z⟩
              subst ha_eq
              show BurgessR3Maximal fc
                (if pc.x = z then D else χ.f pc.x)
                (g' pc.x z)
                (if z = z then D else χ.f z)
              have hx_ne : pc.x ≠ z := by linarith
              simp only [hx_ne, ite_false, ite_true, g']
              exact h_B'_max
            · -- Both old: preserved
              have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
              have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
              show BurgessR3Maximal fc
                (if a = z then D else χ.f a)
                (g' a b)
                (if b = z then D else χ.f b)
              simp only [ha_ne, hb_ne, ite_false, g', and_false, false_and]
              have h_adj_old : Adjacent χ.dom a b := by
                refine ⟨ha, hb, hab, ?_⟩
                intro u hu ⟨hau, hub⟩
                exact h_no_between u (Finset.mem_insert_of_mem hu) ⟨hau, hub⟩
              exact h_c2' a b h_adj_old
          exact { val := χ'
                  dom_sub := Finset.subset_insert z χ.dom
                  c0 := by
                    intro q hq
                    show SetMaximalConsistent fc (if q = z then D else χ.f q)
                    change q ∈ insert z χ.dom at hq
                    simp only [Finset.mem_insert] at hq
                    rcases hq with rfl | hq
                    · simp only [ite_true]; exact h_D_mcs
                    · have h_ne : q ≠ z := fun h => hz_notin (h ▸ hq)
                      simp only [h_ne, ite_false]; exact h_c0 q hq
                  f_agrees := by
                    intro x hx
                    have h_ne : x ≠ z := fun h => hz_notin (h ▸ hx)
                    exact if_neg h_ne
                  g_agrees := by
                    intro a b ha hb
                    show g' a b = χ.g a b
                    simp only [g']
                    have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
                    have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
                    simp only [ha_ne, hb_ne, false_and, and_false, ite_false]
                  c2' := h_c2'_new
                  c5_forward_witness := by
                    intro _ _ _
                    refine ⟨z, Finset.mem_insert_self z χ.dom, hx_lt_z, ?_, ?_, ?_, ?_⟩
                    · show pc.η ∈ (if z = z then D else χ.f z)
                      simp only [ite_true]
                      exact h_η_D
                    · -- Guard: for all adjacent (a,b) with pc.x ≤ a, b ≤ z, show ξ ∈ g'(a,b)
                      -- The only such pair is (pc.x, z) since z is a fresh point
                      intro a b h_adj_ab h_le_a h_le_b
                      have ha_eq : a = pc.x := by
                        by_contra ha_ne
                        have ha_gt : pc.x < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
                        -- a is in insert z χ.dom, a > pc.x, a < b ≤ z < x'
                        -- so a is between pc.x and x' in the old domain, contradiction
                        have ha_mem := h_adj_ab.1
                        simp only [χ', Finset.mem_insert] at ha_mem
                        rcases ha_mem with rfl | ha_mem
                        · -- a = z, but b ≤ z and a < b, contradiction
                          exact absurd h_le_b (not_le.mpr h_adj_ab.2.2.1)
                        · -- a ∈ old dom, pc.x < a, a < b ≤ z < x'
                          exact h_adj_xx'.2.2.2 a ha_mem ⟨ha_gt, lt_trans (lt_of_lt_of_le h_adj_ab.2.2.1 h_le_b) hz_lt_x'⟩
                      subst ha_eq
                      have hb_eq : b = z := by
                        by_contra hb_ne
                        have hb_lt : b < z := lt_of_le_of_ne h_le_b hb_ne
                        have hb_mem := h_adj_ab.2.1
                        simp only [χ', Finset.mem_insert] at hb_mem
                        rcases hb_mem with rfl | hb_mem
                        · exact absurd (le_refl z) (not_le.mpr hb_lt)
                        · -- b ∈ old dom, pc.x < b < z < x', so b between pc.x and x'
                          exact h_adj_xx'.2.2.2 b hb_mem ⟨h_adj_ab.2.2.1, lt_trans hb_lt hz_lt_x'⟩
                      subst hb_eq
                      -- Need ξ ∈ g'(pc.x, z) = B'
                      show pc.ξ ∈ g' pc.x z
                      simp only [g', and_self, ite_true]
                      exact h_ξ_B'
                    · -- Domain guard: no w ∈ χ.dom with pc.x < w < z (z between adjacent (pc.x, x'))
                      intro w hw hxw hwz
                      exact absurd ⟨hxw, lt_trans hwz hz_lt_x'⟩ (h_adj_xx'.2.2.2 w hw)
                    · exact Or.inl hz_notin
                  c5_backward_witness := fun h => absurd h (by rw [h_kind] at h; exact absurd h (by decide))
                  c4_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
                  c4_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)

                  g_sub_f_insert := by
                    intro a b h_adj w hw hw_not haw hwb
                    simp only [χ', Finset.mem_insert] at hw
                    rcases hw with rfl | hw
                    · show χ.g a b ⊆ (if z = z then D else χ.f z)
                      simp only [ite_true]
                      have hab : a = pc.x ∧ b = x' := by
                        constructor
                        · by_contra ha_ne
                          have : a < pc.x ∨ pc.x < a := lt_or_gt_of_ne ha_ne
                          rcases this with h | h
                          · exact h_adj.2.2.2 pc.x h_mem ⟨h, lt_trans hx_lt_z hwb⟩
                          · exact h_adj_xx'.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_x'⟩
                        · by_contra hb_ne
                          have : b < x' ∨ x' < b := lt_or_gt_of_ne hb_ne
                          rcases this with h | h
                          · exact h_adj_xx'.2.2.2 b h_adj.2.1 ⟨lt_trans hx_lt_z hwb, h⟩
                          · exact h_adj.2.2.2 x' hx'_dom ⟨lt_trans haw hz_lt_x', h⟩
                      rw [hab.1, hab.2]; exact h_g_sub_D
                    · exact absurd hw hw_not
                  g_sub_g_new := by
                    intro a b h_adj w hw hw_not haw hwb
                    simp only [χ', Finset.mem_insert] at hw
                    rcases hw with rfl | hw
                    · have ha_eq : a = pc.x := by
                        by_contra ha_ne
                        rcases lt_or_gt_of_ne ha_ne with h | h
                        · exact h_adj.2.2.2 pc.x h_mem ⟨h, lt_trans hx_lt_z hwb⟩
                        · exact h_adj_xx'.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_x'⟩
                      have hb_eq : b = x' := by
                        by_contra hb_ne
                        rcases lt_or_gt_of_ne hb_ne with h | h
                        · exact h_adj_xx'.2.2.2 b h_adj.2.1 ⟨lt_trans hx_lt_z hwb, h⟩
                        · exact h_adj.2.2.2 x' hx'_dom ⟨lt_trans haw hz_lt_x', h⟩
                      subst ha_eq; subst hb_eq
                      constructor
                      · show χ.g pc.x x' ⊆ g' pc.x z
                        simp only [g', and_self, ite_true]
                        exact h_g_sub_B'
                      · show χ.g pc.x x' ⊆ g' z x'
                        simp only [g']
                        have : ¬(z = pc.x ∧ x' = z) := by
                          intro ⟨h1, _⟩; linarith
                        simp only [this, ite_false, and_self, ite_true]
                        exact h_g_sub_B''
                    · exact absurd hw hw_not
                  dom_new_unique := by
                    intro u v hu hu_not hv hv_not
                    simp only [χ', Finset.mem_insert] at hu hv
                    rcases hu with rfl | hu <;> rcases hv with rfl | hv
                    · rfl
                    · exact absurd hv hv_not
                    · exact absurd hu hu_not
                    · exact absurd hu hu_not
                  c5_forward_resolved_no_new := fun _ _ _ h_wit => absurd h_wit h_no_wit
                  c5_backward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide) }
    · exact { val := χ
              dom_sub := Finset.Subset.refl _
              c0 := h_c0
              f_agrees := fun _ _ => rfl
              g_agrees := fun _ _ _ _ => rfl
              c2' := by exact h_c2'
              c5_forward_witness := by
                intro _ h_mem h_until
                push_neg at h_actual
                obtain ⟨y, hy_dom, hy_lt, hy_η, h_guard, h_dom_guard⟩ := h_actual h_mem h_until
                exact ⟨y, hy_dom, hy_lt, hy_η, h_guard, h_dom_guard, Or.inr (fun u hu => hu)⟩
              c5_backward_witness := fun h => absurd h (by rw [h_kind] at h; exact absurd h (by decide))
              c4_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c4_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)

              g_sub_f_insert := fun _ _ _ w hw hw_not _ _ => absurd hw hw_not
              g_sub_g_new := fun _ _ _ w hw hw_not _ _ => absurd hw hw_not
              dom_new_unique := fun u _ hu hu_not _ _ => absurd hu hu_not
              c5_forward_resolved_no_new := fun _ _ _ _ u hu => hu
              c5_backward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide) }
  | .c5_backward =>
    -- Backward (Since) C5' case
    -- Burgess C5b counterexample check (g-value based, mirror of C5a):
    by_cases h_actual : pc.x ∈ χ.dom ∧ Formula.snce pc.η pc.ξ ∈ χ.f pc.x ∧
        ¬∃ y ∈ χ.dom, y < pc.x ∧ pc.η ∈ χ.f y ∧
          (∀ a b, Adjacent χ.dom a b → y ≤ a → b ≤ pc.x → pc.ξ ∈ χ.g a b) ∧
          (∀ w ∈ χ.dom, y < w → w < pc.x → pc.ξ ∈ χ.f w)
    · obtain ⟨h_mem, h_since, h_no_wit⟩ := h_actual
      have h_mcs_x := h_c0 pc.x h_mem
      have h_dom_ne : χ.dom.Nonempty := ⟨pc.x, h_mem⟩
      set min_old := χ.dom.min' h_dom_ne with min_old_def
      have h_min_mem : min_old ∈ χ.dom := Finset.min'_mem χ.dom h_dom_ne
      have h_min_le : ∀ s ∈ χ.dom, min_old ≤ s := fun s hs => Finset.min'_le χ.dom s hs
      -- Split on whether pc.x is the first point (n=0) or not (n≥1)
      by_cases h_eq_min : pc.x = min_old
      · -- **Case n=0**: pc.x is the minimum domain point.
        -- Place y before all points. Only new pair is (y, pc.x).
        -- Use lemma_2_4_since_with_guard for guard ξ ∈ B.
        have h_fresh := exists_rat_lt_finset χ.dom
        let y := h_fresh.choose
        have hy_lt : ∀ s ∈ χ.dom, y < s := h_fresh.choose_spec.1
        have hy_notin : y ∉ χ.dom := h_fresh.choose_spec.2
        have h_l24s := lemma_2_4_since_with_guard fc h_mcs_x pc.ξ pc.η h_since
        let B_new := h_l24s.choose
        let C := h_l24s.choose_spec.choose
        have h_l24s_prop := h_l24s.choose_spec.choose_spec
        have h_C_mcs : SetMaximalConsistent fc C := h_l24s_prop.1
        have h_η_C : pc.η ∈ C := h_l24s_prop.2.1
        have h_ξ_B : pc.ξ ∈ B_new := h_l24s_prop.2.2.2.1
        have h_B_new_r3m : BurgessR3Maximal fc C B_new (χ.f pc.x) := h_l24s_prop.2.2.2.2
        have h_y_lt_min : y < min_old := hy_lt min_old h_min_mem
        let g' := fun a b =>
          if a = y ∧ b = min_old then B_new
          else χ.g a b
        let χ' : Chronicle Atom := ⟨fun q => if q = y then C else χ.f q, g', insert y χ.dom⟩
        have h_c2'_new : χ'.c2' fc := by
          intro a b h_adj_new
          obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
          simp only [χ', Finset.mem_insert] at ha hb
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact absurd hab (lt_irrefl _)
          · have hb_eq : b = min_old := by
              by_contra hb_ne
              have hb_ge : min_old ≤ b := h_min_le b hb
              have hb_gt : min_old < b := lt_of_le_of_ne hb_ge (Ne.symm hb_ne)
              exact h_no_between min_old (Finset.mem_insert_of_mem h_min_mem) ⟨h_y_lt_min, hb_gt⟩
            subst hb_eq
            show BurgessR3Maximal fc
              (if y = y then C else χ.f y)
              (g' y min_old)
              (if min_old = y then C else χ.f min_old)
            have hmin_ne_y : min_old ≠ y := ne_of_gt h_y_lt_min
            simp only [ite_true, hmin_ne_y, ite_false, g', and_self]
            rw [← h_eq_min]; exact h_B_new_r3m
          · exact absurd hab (not_lt.mpr (le_of_lt (hy_lt a ha)))
          · have ha_ne : a ≠ y := fun h => hy_notin (h ▸ ha)
            have hb_ne : b ≠ y := fun h => hy_notin (h ▸ hb)
            show BurgessR3Maximal fc
              (if a = y then C else χ.f a)
              (g' a b)
              (if b = y then C else χ.f b)
            simp only [ha_ne, hb_ne, ite_false]
            show BurgessR3Maximal fc (χ.f a)
              (if a = y ∧ b = min_old then B_new else χ.g a b) (χ.f b)
            rw [if_neg (fun ⟨hay, _⟩ => ha_ne hay)]
            have h_adj_old : Adjacent χ.dom a b := by
              refine ⟨ha, hb, hab, ?_⟩
              intro u hu ⟨hau, hub⟩
              exact h_no_between u (Finset.mem_insert_of_mem hu) ⟨hau, hub⟩
            exact h_c2' a b h_adj_old
        exact { val := χ'
                dom_sub := Finset.subset_insert y χ.dom
                c0 := by
                  intro q hq
                  show SetMaximalConsistent fc (if q = y then C else χ.f q)
                  change q ∈ insert y χ.dom at hq
                  simp only [Finset.mem_insert] at hq
                  rcases hq with rfl | hq
                  · simp only [ite_true]; exact h_C_mcs
                  · have h_ne : q ≠ y := fun h => hy_notin (h ▸ hq)
                    simp only [h_ne, ite_false]; exact h_c0 q hq
                f_agrees := by
                  intro x hx
                  have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
                  exact if_neg h_ne
                g_agrees := by
                  intro a b ha hb
                  show g' a b = χ.g a b
                  simp only [g']
                  have ha_ne : a ≠ y := fun h => hy_notin (h ▸ ha)
                  simp only [ha_ne, false_and, ite_false]
                c2' := h_c2'_new
                c5_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
                c5_backward_witness := by
                  intro _ _ _
                  refine ⟨y, Finset.mem_insert_self y χ.dom, hy_lt pc.x h_mem, ?_, ?_, ?_, ?_⟩
                  · show pc.η ∈ (if y = y then C else χ.f y)
                    simp only [ite_true]; exact h_η_C
                  · -- Guard: only adjacent pair from y to pc.x is (y, min_old)
                    intro a b h_adj_ab h_le_a h_le_b
                    have ha_eq : a = y := by
                      have ha_dom := h_adj_ab.1
                      simp only [χ', Finset.mem_insert] at ha_dom
                      rcases ha_dom with rfl | ha_old
                      · rfl
                      · have : min_old ≤ a := h_min_le a ha_old
                        linarith [h_adj_ab.2.2.1]
                    subst ha_eq
                    have hb_ne_y : b ≠ y := ne_of_gt h_adj_ab.2.2.1
                    have hb_old : b ∈ χ.dom := by
                      have hb_dom := h_adj_ab.2.1
                      simp only [χ', Finset.mem_insert] at hb_dom
                      rcases hb_dom with rfl | h
                      · exact absurd rfl hb_ne_y
                      · exact h
                    have hb_eq : b = min_old := by
                      have : min_old ≤ b := h_min_le b hb_old
                      have : b ≤ min_old := by rw [← h_eq_min]; exact h_le_b
                      exact le_antisymm ‹b ≤ min_old› ‹min_old ≤ b›
                    subst hb_eq
                    show pc.ξ ∈ g' y min_old
                    simp only [g', and_self, ite_true]; exact h_ξ_B
                  · -- Domain guard: no w ∈ χ.dom with y < w < pc.x (pc.x = min_old ≤ all old)
                    intro w hw _ hws
                    exact absurd (h_min_le w hw) (not_le.mpr (h_eq_min ▸ hws))
                  · exact Or.inl hy_notin
                c4_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
                c4_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)

                g_sub_f_insert := by
                  intro a b h_adj w hw hw_not haw hwb
                  change w ∈ insert y χ.dom at hw
                  simp only [Finset.mem_insert] at hw
                  rcases hw with rfl | hw
                  · exact absurd haw (not_lt.mpr (le_of_lt (hy_lt a h_adj.1)))
                  · exact absurd hw hw_not
                g_sub_g_new := by
                  intro a b h_adj w hw hw_not haw hwb
                  change w ∈ insert y χ.dom at hw
                  simp only [Finset.mem_insert] at hw
                  rcases hw with rfl | hw
                  · exact absurd haw (not_lt.mpr (le_of_lt (hy_lt a h_adj.1)))
                  · exact absurd hw hw_not
                dom_new_unique := by
                  intro u v hu hu_not hv hv_not
                  change u ∈ insert y χ.dom at hu
                  change v ∈ insert y χ.dom at hv
                  simp only [Finset.mem_insert] at hu hv
                  rcases hu with rfl | hu <;> rcases hv with rfl | hv
                  · rfl
                  · exact absurd hv hv_not
                  · exact absurd hu hu_not
                  · exact absurd hu hu_not
                c5_forward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide)
                c5_backward_resolved_no_new := fun _ _ _ h_wit => absurd h_wit h_no_wit }
      · -- **Case n≥1**: pc.x is NOT the minimum. Burgess 2.10' induction case (backward mirror).
        -- Find x'' = immediate predecessor of pc.x in dom.
        set T_pred := χ.dom.filter (fun v => decide (v < pc.x)) with T_pred_def
        have hT_ne_pred : T_pred.Nonempty := by
          have h_pc_gt_min : min_old < pc.x := lt_of_le_of_ne (h_min_le pc.x h_mem) (Ne.symm h_eq_min)
          exact ⟨min_old, Finset.mem_filter.mpr ⟨h_min_mem, by simp [h_pc_gt_min]⟩⟩
        set x'' := T_pred.max' hT_ne_pred with x''_def
        have hx''_mem_T := Finset.max'_mem T_pred hT_ne_pred
        have hx''_dom : x'' ∈ χ.dom := (Finset.mem_filter.mp hx''_mem_T).1
        have hx''_lt_x : x'' < pc.x := by
          have := (Finset.mem_filter.mp hx''_mem_T).2
          simp only [decide_eq_true_eq] at this; exact this
        have h_adj_x''x : Adjacent χ.dom x'' pc.x := by
          refine ⟨hx''_dom, h_mem, hx''_lt_x, ?_⟩
          intro u hu ⟨hx''u, hux⟩
          have hu_T : u ∈ T_pred := Finset.mem_filter.mpr ⟨hu, by simp [hux]⟩
          have := Finset.le_max' T_pred u hu_T
          linarith
        have h_mcs_x'' := h_c0 x'' hx''_dom
        -- Burgess 2.10' (ii): guard ∈ g(x'',x) implies event ∉ f(x'')
        have h_guard_implies_no_event_back : pc.ξ ∈ χ.g x'' pc.x → pc.η ∉ χ.f x'' :=
          fun h_guard h_event => h_no_wit ⟨x'', hx''_dom, hx''_lt_x, h_event,
            ⟨fun a b h_adj_ab h_le_a h_le_b => by
              have ha_eq : a = x'' := by
                by_contra ha_ne
                have ha_gt : x'' < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
                exact h_adj_x''x.2.2.2 a h_adj_ab.1 ⟨ha_gt, lt_of_lt_of_le h_adj_ab.2.2.1 h_le_b⟩
              have hb_eq : b = pc.x := by
                rw [ha_eq] at h_adj_ab
                by_contra hb_ne
                have hb_lt : b < pc.x := lt_of_le_of_ne h_le_b hb_ne
                exact h_adj_x''x.2.2.2 b h_adj_ab.2.1 ⟨h_adj_ab.2.2.1, hb_lt⟩
              rw [ha_eq, hb_eq]; exact h_guard,
            fun w hw hx''w hwx => absurd ⟨hx''w, hwx⟩ (h_adj_x''x.2.2.2 w hw)⟩⟩
        -- Get BurgessR3Maximal fc for the adjacent pair (x'', pc.x)
        have h_r3m_adj := h_c2' x'' pc.x h_adj_x''x
        have h_gc_adj := BurgessR3Maximal_g_content_sub h_r3m_adj h_mcs_x'' h_mcs_x
        -- Backward condition (i) check: xi ∧ snce(xi, eta) ∈ f(x'') AND xi ∈ g(x'', pc.x)?
        -- Both parts needed for backward walk (Burgess 2.10 mirror).
        -- If yes, the Since counterexample persists backward. We walk backward.
        -- If no, splitting at (x'', pc.x) succeeds.
        by_cases h_cond_i_back : Formula.and pc.ξ (Formula.snce pc.η pc.ξ) ∈ χ.f x'' ∧ pc.ξ ∈ χ.g x'' pc.x
        · -- **Condition (i) backward**: use recursive backward walk helper
          let r := c5_backward_walk fc χ h_c0 h_c2' pc.ξ pc.η pc.x h_mem h_since h_no_wit
          exact { val := r.val
                  dom_sub := r.dom_sub
                  c0 := r.c0
                  f_agrees := r.f_agrees
                  g_agrees := r.g_agrees
                  c2' := r.c2'
                  c5_forward_witness := fun h => absurd h (by rw [h_kind] at h; exact absurd h (by decide))
                  c5_backward_witness := by
                    intro _ _ _
                    exact ⟨r.witness, r.witness_mem, r.witness_lt, r.witness_event,
                      r.witness_guard, r.domain_guard, Or.inl r.witness_not_old⟩
                  c4_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
                  c4_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)

                  g_sub_f_insert := r.g_sub_f_insert
                  g_sub_g_new := r.g_sub_g_new
                  dom_new_unique := r.dom_new_unique
                  c5_forward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide)
                  c5_backward_resolved_no_new := fun _ _ _ h_wit => absurd h_wit h_no_wit }
        · -- **Not condition (i) backward**: splitting at (x'', pc.x) succeeds.
          have h_split_result : ∃ B' D B'' : Set (Formula Atom),
            BurgessR3Maximal fc (χ.f x'') B' D ∧
            BurgessR3Maximal fc D B'' (χ.f pc.x) ∧
            SetMaximalConsistent fc D ∧
            pc.η ∈ D ∧
            χ.g x'' pc.x ⊆ D ∧
            χ.g x'' pc.x ⊆ B' ∧
            χ.g x'' pc.x ⊆ B'' ∧
            pc.ξ ∈ B'' := by
            by_cases h_eta_g : pc.η ∈ χ.g x'' pc.x
            · by_cases h_xi_g : pc.ξ ∈ χ.g x'' pc.x
              · -- η ∈ g, ξ ∈ g: use lemma_2_8_since (avoids needing SetConsistent g)
                have h_conj_not_f_back : Formula.and pc.ξ (Formula.snce pc.η pc.ξ) ∉ χ.f x'' :=
                  fun h_conj_f => h_cond_i_back ⟨h_conj_f, h_xi_g⟩
                have h_neg_disj_x'' : (Formula.or pc.η (Formula.and pc.ξ (Formula.snce pc.η pc.ξ))).neg ∈ χ.f x'' := by
                  have h_neg_conj_x'' : (pc.η.neg.and (Formula.and pc.ξ (Formula.snce pc.η pc.ξ)).neg) ∈ χ.f x'' := by
                    have h2 : (Formula.and pc.ξ (Formula.snce pc.η pc.ξ)).neg ∈ χ.f x'' := by
                      rcases SetMaximalConsistent.negation_complete h_mcs_x''
                        (Formula.and pc.ξ (Formula.snce pc.η pc.ξ)) with h | h
                      · exact absurd h h_conj_not_f_back
                      · exact h
                    have h_eta_neg_x''_local : pc.η.neg ∈ χ.f x'' := by
                      rcases SetMaximalConsistent.negation_complete h_mcs_x'' pc.η with h | h
                      · exact absurd h (h_guard_implies_no_event_back h_xi_g)
                      · exact h
                    exact conj_mcs fc h_mcs_x'' pc.η.neg
                      (Formula.and pc.ξ (Formula.snce pc.η pc.ξ)).neg h_eta_neg_x''_local h2
                  exact SetMaximalConsistent.implication_property h_mcs_x''
                    (theorem_in_mcs_fc h_mcs_x''
                      (liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.demorgan_disj_neg_backward pc.η
                        (Formula.and pc.ξ (Formula.snce pc.η pc.ξ))))) h_neg_conj_x''
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, h_B_sub_B', h_B_sub_B'', _⟩ := lemma_2_8_since fc h_mcs_x'' h_mcs_x h_r3m_adj h_r3m_adj.1 h_gc_adj
                  pc.ξ pc.η h_since h_neg_disj_x''
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, h_B_sub_B', h_B_sub_B'', h_B_sub_B'' h_xi_g⟩
              · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B''⟩ :=
                  lemma_2_7_since fc h_mcs_x'' h_mcs_x h_r3m_adj h_r3m_adj.1 h_gc_adj pc.ξ pc.η h_since h_xi_g
                exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B''⟩
            · by_cases h_eta_neg_g : pc.η.neg ∈ χ.g x'' pc.x
              · by_cases h_xi_g : pc.ξ ∈ χ.g x'' pc.x
                · by_cases h_conj_g : Formula.and pc.ξ (Formula.snce pc.η pc.ξ) ∈ χ.g x'' pc.x
                  · have h_conj_not_f_back : Formula.and pc.ξ (Formula.snce pc.η pc.ξ) ∉ χ.f x'' :=
                      fun h_conj_f => h_cond_i_back ⟨h_conj_f, h_xi_g⟩
                    have h_neg_disj_x'' : (Formula.or pc.η (Formula.and pc.ξ (Formula.snce pc.η pc.ξ))).neg ∈ χ.f x'' := by
                      have h_neg_conj_x'' : (pc.η.neg.and (Formula.and pc.ξ (Formula.snce pc.η pc.ξ)).neg) ∈ χ.f x'' := by
                        have h2 : (Formula.and pc.ξ (Formula.snce pc.η pc.ξ)).neg ∈ χ.f x'' := by
                          rcases SetMaximalConsistent.negation_complete h_mcs_x''
                            (Formula.and pc.ξ (Formula.snce pc.η pc.ξ)) with h | h
                          · exact absurd h h_conj_not_f_back
                          · exact h
                        have h_eta_neg_x''_local : pc.η.neg ∈ χ.f x'' := by
                          rcases SetMaximalConsistent.negation_complete h_mcs_x'' pc.η with h | h
                          · exact absurd h (h_guard_implies_no_event_back h_xi_g)
                          · exact h
                        exact conj_mcs fc h_mcs_x'' pc.η.neg
                          (Formula.and pc.ξ (Formula.snce pc.η pc.ξ)).neg h_eta_neg_x''_local h2
                      exact SetMaximalConsistent.implication_property h_mcs_x''
                        (theorem_in_mcs_fc h_mcs_x''
                          (liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.demorgan_disj_neg_backward pc.η
                            (Formula.and pc.ξ (Formula.snce pc.η pc.ξ))))) h_neg_conj_x''
                    obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, h_B_sub_B', h_B_sub_B'', _⟩ := lemma_2_8_since fc h_mcs_x'' h_mcs_x h_r3m_adj h_r3m_adj.1 h_gc_adj
                      pc.ξ pc.η h_since h_neg_disj_x''
                    exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, h_B_sub_B', h_B_sub_B'', h_B_sub_B'' h_xi_g⟩
                  · have h_bx5_since := self_accum_since_mcs fc h_mcs_x pc.ξ pc.η h_since
                    obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_B', h_B_sub_D, h_B_sub_B'', _⟩ := lemma_2_7_since fc h_mcs_x'' h_mcs_x h_r3m_adj h_r3m_adj.1 h_gc_adj
                      (Formula.and pc.ξ (Formula.snce pc.η pc.ξ)) pc.η h_bx5_since h_conj_g
                    exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, h_B_sub_B', h_B_sub_B'', h_B_sub_B'' h_xi_g⟩
                · obtain ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_B', h_B_sub_D, h_B_sub_B'', h_xi_B''⟩ :=
                    lemma_2_7_since fc h_mcs_x'' h_mcs_x h_r3m_adj h_r3m_adj.1 h_gc_adj
                      pc.ξ pc.η h_since h_xi_g
                  exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, h_B_sub_B', h_B_sub_B'', h_xi_B''⟩
              · by_cases h_xi_g2 : pc.ξ ∈ χ.g x'' pc.x
                · have h_split := lemma_2_6_splitting fc h_mcs_x'' h_mcs_x h_r3m_adj h_r3m_adj.1 h_gc_adj
                    pc.η.neg h_eta_neg_g
                  obtain ⟨B', D, B'', h_B', h_B'', h_D_mcs, h_eta_neg_neg_D, h_B_sub_D, h_B_sub_B', h_B_sub_B''⟩ := h_split
                  have h_eta_D : pc.η ∈ D :=
                    SetMaximalConsistent.implication_property h_D_mcs
                      (theorem_in_mcs_fc h_D_mcs (Cslib.Logic.Bimodal.Theorems.Propositional.double_negation pc.η)) h_eta_neg_neg_D
                  exact ⟨B', D, B'', h_B', h_B'', h_D_mcs, h_eta_D, h_B_sub_D, h_B_sub_B', h_B_sub_B'', h_B_sub_B'' h_xi_g2⟩
                · obtain ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_B', h_B_sub_D, h_B_sub_B'', h_xi_B''⟩ :=
                    lemma_2_7_since fc h_mcs_x'' h_mcs_x h_r3m_adj h_r3m_adj.1 h_gc_adj
                      pc.ξ pc.η h_since h_xi_g2
                  exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, h_B_sub_B', h_B_sub_B'', h_xi_B''⟩
          let B' := h_split_result.choose
          let D := h_split_result.choose_spec.choose
          let B'' := h_split_result.choose_spec.choose_spec.choose
          have h_split_prop := h_split_result.choose_spec.choose_spec.choose_spec
          have h_B'_max : BurgessR3Maximal fc (χ.f x'') B' D := h_split_prop.1
          have h_B''_max : BurgessR3Maximal fc D B'' (χ.f pc.x) := h_split_prop.2.1
          have h_D_mcs : SetMaximalConsistent fc D := h_split_prop.2.2.1
          have h_η_D : pc.η ∈ D := h_split_prop.2.2.2.1
          have h_g_sub_D : χ.g x'' pc.x ⊆ D := h_split_prop.2.2.2.2.1
          have h_g_sub_B' : χ.g x'' pc.x ⊆ B' := h_split_prop.2.2.2.2.2.1
          have h_g_sub_B'' : χ.g x'' pc.x ⊆ B'' := h_split_prop.2.2.2.2.2.2.1
          have h_ξ_B'' : pc.ξ ∈ B'' := h_split_prop.2.2.2.2.2.2.2
          -- Insert z = midpoint of x'' and pc.x
          set z := (x'' + pc.x) / 2 with hz_def
          have hz_lt_x : z < pc.x := by linarith
          have hx''_lt_z : x'' < z := by linarith
          have hz_notin : z ∉ χ.dom := by
            intro h_mem_z; exact h_adj_x''x.2.2.2 z h_mem_z ⟨hx''_lt_z, hz_lt_x⟩
          -- Build new chronicle with f'(z) = D
          let g' := fun a b =>
            if a = x'' ∧ b = z then B'
            else if a = z ∧ b = pc.x then B''
            else χ.g a b
          let χ' : Chronicle Atom := ⟨fun q => if q = z then D else χ.f q, g', insert z χ.dom⟩
          have h_c2'_new : χ'.c2' fc := by
            intro a b h_adj_new
            obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
            simp only [χ', Finset.mem_insert] at ha hb
            rcases ha with rfl | ha <;> rcases hb with rfl | hb
            · exact absurd hab (lt_irrefl _)
            · -- a = z, b ∈ old dom: must be (z, pc.x)
              have hb_eq : b = pc.x := by
                by_contra hb_ne
                have hb_ge : pc.x ≤ b := by
                  by_contra hlt; push_neg at hlt
                  have : x'' < b := lt_trans hx''_lt_z hab
                  exact h_adj_x''x.2.2.2 b hb ⟨this, hlt⟩
                have hb_gt : pc.x < b := lt_of_le_of_ne hb_ge (Ne.symm hb_ne)
                exact h_no_between pc.x (Finset.mem_insert_of_mem h_mem) ⟨hz_lt_x, hb_gt⟩
              subst hb_eq
              show BurgessR3Maximal fc
                (if z = z then D else χ.f z)
                (g' z pc.x)
                (if pc.x = z then D else χ.f pc.x)
              have hx_ne : pc.x ≠ z := by linarith
              simp only [ite_true, hx_ne, ite_false, g']
              simp only [ite_false, ite_true, and_false, and_self]
              exact h_B''_max
            · -- a ∈ old dom, b = z: must be (x'', z)
              have ha_eq : a = x'' := by
                by_contra ha_ne
                have ha_le : a ≤ x'' := by
                  by_contra hgt; push_neg at hgt
                  exact h_adj_x''x.2.2.2 a ha ⟨hgt, lt_trans hab hz_lt_x⟩
                have ha_lt : a < x'' := lt_of_le_of_ne ha_le ha_ne
                exact h_no_between x'' (Finset.mem_insert_of_mem hx''_dom) ⟨ha_lt, hx''_lt_z⟩
              subst ha_eq
              show BurgessR3Maximal fc
                (if x'' = z then D else χ.f x'')
                (g' x'' z)
                (if z = z then D else χ.f z)
              have hx''_ne : x'' ≠ z := by linarith
              simp only [hx''_ne, ite_false, ite_true, g']
              exact h_B'_max
            · -- Both old: preserved
              have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
              have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
              show BurgessR3Maximal fc
                (if a = z then D else χ.f a)
                (g' a b)
                (if b = z then D else χ.f b)
              simp only [ha_ne, hb_ne, ite_false, g', and_false, false_and]
              have h_adj_old : Adjacent χ.dom a b := by
                refine ⟨ha, hb, hab, ?_⟩
                intro u hu ⟨hau, hub⟩
                exact h_no_between u (Finset.mem_insert_of_mem hu) ⟨hau, hub⟩
              exact h_c2' a b h_adj_old
          exact { val := χ'
                  dom_sub := Finset.subset_insert z χ.dom
                  c0 := by
                    intro q hq
                    show SetMaximalConsistent fc (if q = z then D else χ.f q)
                    change q ∈ insert z χ.dom at hq
                    simp only [Finset.mem_insert] at hq
                    rcases hq with rfl | hq
                    · simp only [ite_true]; exact h_D_mcs
                    · have h_ne : q ≠ z := fun h => hz_notin (h ▸ hq)
                      simp only [h_ne, ite_false]; exact h_c0 q hq
                  f_agrees := by
                    intro x hx
                    have h_ne : x ≠ z := fun h => hz_notin (h ▸ hx)
                    exact if_neg h_ne
                  g_agrees := by
                    intro a b ha hb
                    show g' a b = χ.g a b
                    simp only [g']
                    have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
                    have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
                    simp only [ha_ne, hb_ne, false_and, and_false, ite_false]
                  c2' := h_c2'_new
                  c5_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
                  c5_backward_witness := by
                    intro _ _ _
                    refine ⟨z, Finset.mem_insert_self z χ.dom, hz_lt_x, ?_, ?_, ?_, ?_⟩
                    · show pc.η ∈ (if z = z then D else χ.f z)
                      simp only [ite_true]; exact h_η_D
                    · -- Guard: for all adjacent (a,b) with z ≤ a, b ≤ pc.x, show ξ ∈ g'(a,b)
                      -- The only such pair is (z, pc.x)
                      intro a b h_adj_ab h_le_a h_le_b
                      obtain ⟨ha_dom, hb_dom, hab_lt, h_no_btw⟩ := h_adj_ab
                      simp only [χ', Finset.mem_insert] at ha_dom hb_dom
                      have hb_eq : b = pc.x := by
                        by_contra hb_ne
                        have hb_lt : b < pc.x := lt_of_le_of_ne h_le_b hb_ne
                        rcases hb_dom with rfl | hb_mem
                        · exact absurd h_le_a (not_le.mpr hab_lt)
                        · exact h_adj_x''x.2.2.2 b hb_mem ⟨lt_of_lt_of_le hx''_lt_z (le_trans h_le_a (le_of_lt hab_lt)), hb_lt⟩
                      subst hb_eq
                      have ha_eq : a = z := by
                        by_contra ha_ne
                        -- z ≤ a and a ≠ z gives z < a
                        have ha_gt : z < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
                        rcases ha_dom with rfl | ha_mem
                        · exact absurd (le_refl z) (not_le.mpr ha_gt)
                        · -- a ∈ χ.dom, z < a < b = pc.x, so x'' < z < a < pc.x
                          exact h_adj_x''x.2.2.2 a ha_mem ⟨lt_trans hx''_lt_z ha_gt, hab_lt⟩
                      subst ha_eq
                      show pc.ξ ∈ g' z pc.x
                      simp only [g', show z ≠ x'' from ne_of_gt hx''_lt_z, false_and, ite_false, and_self, ite_true]
                      exact h_ξ_B''
                    · -- Domain guard: no w ∈ χ.dom with z < w < pc.x (adjacency of (x'', pc.x))
                      intro w hw hwz hwx
                      exact absurd ⟨lt_trans hx''_lt_z hwz, hwx⟩ (h_adj_x''x.2.2.2 w hw)
                    · exact Or.inl hz_notin
                  c4_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
                  c4_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)

                  g_sub_f_insert := by
                    intro a b h_adj w hw hw_not haw hwb
                    simp only [χ', Finset.mem_insert] at hw
                    rcases hw with rfl | hw
                    · show χ.g a b ⊆ (if z = z then D else χ.f z)
                      simp only [ite_true]
                      have hab : a = x'' ∧ b = pc.x := by
                        constructor
                        · by_contra ha_ne
                          have : a < x'' ∨ x'' < a := lt_or_gt_of_ne ha_ne
                          rcases this with h | h
                          · exact h_adj.2.2.2 x'' hx''_dom ⟨h, lt_trans hx''_lt_z hwb⟩
                          · exact h_adj_x''x.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_x⟩
                        · by_contra hb_ne
                          have : b < pc.x ∨ pc.x < b := lt_or_gt_of_ne hb_ne
                          rcases this with h | h
                          · exact h_adj_x''x.2.2.2 b h_adj.2.1 ⟨lt_trans hx''_lt_z hwb, h⟩
                          · exact h_adj.2.2.2 pc.x h_mem ⟨lt_trans haw hz_lt_x, h⟩
                      rw [hab.1, hab.2]; exact h_g_sub_D
                    · exact absurd hw hw_not
                  g_sub_g_new := by
                    intro a b h_adj w hw hw_not haw hwb
                    simp only [χ', Finset.mem_insert] at hw
                    rcases hw with rfl | hw
                    · have ha_eq : a = x'' := by
                        by_contra ha_ne
                        rcases lt_or_gt_of_ne ha_ne with h | h
                        · exact h_adj.2.2.2 x'' hx''_dom ⟨h, lt_trans hx''_lt_z hwb⟩
                        · exact h_adj_x''x.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_x⟩
                      have hb_eq : b = pc.x := by
                        by_contra hb_ne
                        rcases lt_or_gt_of_ne hb_ne with h | h
                        · exact h_adj_x''x.2.2.2 b h_adj.2.1 ⟨lt_trans hx''_lt_z hwb, h⟩
                        · exact h_adj.2.2.2 pc.x h_mem ⟨lt_trans haw hz_lt_x, h⟩
                      subst ha_eq; subst hb_eq
                      constructor
                      · show χ.g x'' pc.x ⊆ g' x'' z
                        simp only [g', and_self, ite_true]
                        exact h_g_sub_B'
                      · show χ.g x'' pc.x ⊆ g' z pc.x
                        simp only [g']
                        have : ¬(z = x'' ∧ pc.x = z) := by
                          intro ⟨h1, _⟩; linarith
                        simp only [this, ite_false, and_self, ite_true]
                        exact h_g_sub_B''
                    · exact absurd hw hw_not
                  dom_new_unique := by
                    intro u v hu hu_not hv hv_not
                    simp only [χ', Finset.mem_insert] at hu hv
                    rcases hu with rfl | hu <;> rcases hv with rfl | hv
                    · rfl
                    · exact absurd hv hv_not
                    · exact absurd hu hu_not
                    · exact absurd hu hu_not
                  c5_forward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide)
                  c5_backward_resolved_no_new := fun _ _ _ h_wit => absurd h_wit h_no_wit }
    · exact { val := χ
              dom_sub := Finset.Subset.refl _
              c0 := h_c0
              f_agrees := fun _ _ => rfl
              g_agrees := fun _ _ _ _ => rfl
              c2' := by exact h_c2'
              c5_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c5_backward_witness := by
                intro _ h_mem h_since
                push_neg at h_actual
                obtain ⟨y, hy_dom, hy_lt, hy_η, h_guard, h_dom_guard⟩ := h_actual h_mem h_since
                exact ⟨y, hy_dom, hy_lt, hy_η, h_guard, h_dom_guard, Or.inr (fun u hu => hu)⟩
              c4_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c4_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)

              g_sub_f_insert := fun _ _ _ w hw hw_not _ _ => absurd hw hw_not
              g_sub_g_new := fun _ _ _ w hw hw_not _ _ => absurd hw hw_not
              dom_new_unique := fun u _ hu hu_not _ _ => absurd hu hu_not
              c5_forward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide)
              c5_backward_resolved_no_new := fun _ _ _ _ u hu => hu }
  | .c4_forward =>
    -- Forward C4 case (corrected Burgess C4a: check EVENT η at f(y), negate GUARD ξ at f(z))
    -- Now checks ALL pairs x < y, not just adjacent pairs.
    by_cases h_actual : pc.x ∈ χ.dom ∧ pc.y ∈ χ.dom ∧
        pc.x < pc.y ∧
        (Formula.untl pc.η pc.ξ).neg ∈ χ.f pc.x ∧
        pc.η ∈ χ.f pc.y ∧
        ¬∃ z ∈ χ.dom, pc.x < z ∧ z < pc.y ∧ pc.ξ.neg ∈ χ.f z
    · obtain ⟨h_xm, h_ym, h_lt, h_neg_until, h_event, h_no_wit⟩ := h_actual
      -- Inline C4 elimination with c2' preservation.
      -- Strategy: find an adjacent pair (w, w_next) between x and y where
      -- ξ ∉ g(w, w_next), then split using lemma_2_6_splitting with β = ξ.
      --
      -- Key fact: if neg(untl(ξ,η)) ∈ f(w) and η ∈ f(w_next), then ξ ∉ g(w, w_next).
      -- Proof: if ξ ∈ g, burgessRSet gives U(ξ, η) = untl(ξ,η) ∈ f(w),
      -- contradicting neg(untl(ξ,η)) ∈ f(w).
      --
      -- Find w = rightmost domain point in [x, y) with neg(untl(ξ,η)) ∈ f(w).
      -- x is always a valid candidate. w_next is the successor of w in dom.
      -- If w_next = y (or δ ∈ f(w_next)): η ∈ f(w_next), so ξ ∉ g(w, w_next).
      -- If w_next < y and η ∉ f(w_next): hard case (Burgess 2.9 induction needed).
      have h_mcs_x := h_c0 pc.x h_xm
      have h_mcs_y := h_c0 pc.y h_ym
      -- Find w (rightmost with neg-until) and w_next (its successor)
      haveI : DecidablePred (fun w => w < pc.y ∧
          (Formula.untl pc.η pc.ξ).neg ∈ χ.f w) :=
        fun w => Classical.dec _
      set S_w := χ.dom.filter (fun w => w < pc.y ∧ (Formula.untl pc.η pc.ξ).neg ∈ χ.f w)
      have hS_ne : S_w.Nonempty := by
        refine ⟨pc.x, Finset.mem_filter.mpr ⟨h_xm, h_lt, h_neg_until⟩⟩
      set w := S_w.max' hS_ne
      have hw_mem_S := Finset.max'_mem S_w hS_ne
      have hw_dom : w ∈ χ.dom := (Finset.mem_filter.mp hw_mem_S).1
      have hw_lt_y : w < pc.y := (Finset.mem_filter.mp hw_mem_S).2.1
      have hw_neg_until : (Formula.untl pc.η pc.ξ).neg ∈ χ.f w :=
        (Finset.mem_filter.mp hw_mem_S).2.2
      have hw_rightmost : ∀ v ∈ χ.dom, w < v → v < pc.y →
          (Formula.untl pc.η pc.ξ).neg ∉ χ.f v := by
        intro v hv hwv hvy h_neg_v
        have hv_in_S : v ∈ S_w := Finset.mem_filter.mpr ⟨hv, hvy, h_neg_v⟩
        have := Finset.le_max' S_w v hv_in_S
        linarith
      -- Find w_next = successor of w in dom (smallest domain element > w ≤ y)
      set T_w := χ.dom.filter (fun v => decide (w < v))
      have hT_ne : T_w.Nonempty :=
        ⟨pc.y, Finset.mem_filter.mpr ⟨h_ym, by simp [hw_lt_y]⟩⟩
      set w_next := T_w.min' hT_ne
      have hw_next_mem_T := Finset.min'_mem T_w hT_ne
      have hw_next_dom : w_next ∈ χ.dom := (Finset.mem_filter.mp hw_next_mem_T).1
      have hw_lt_next : w < w_next := by
        have := (Finset.mem_filter.mp hw_next_mem_T).2
        simp only [decide_eq_true_eq] at this; exact this
      have hw_next_le_y : w_next ≤ pc.y := by
        have : pc.y ∈ T_w := Finset.mem_filter.mpr ⟨h_ym, by simp [hw_lt_y]⟩
        exact Finset.min'_le T_w pc.y this
      have h_adj_w : Adjacent χ.dom w w_next := by
        refine ⟨hw_dom, hw_next_dom, hw_lt_next, ?_⟩
        intro u hu ⟨hwu, hu_next⟩
        have hu_T : u ∈ T_w := Finset.mem_filter.mpr ⟨hu, by simp [hwu]⟩
        have := Finset.min'_le T_w u hu_T
        linarith
      -- w_next = y: η ∈ f(w_next) = f(y), so ξ ∉ g(w, w_next)
      -- w_next < y: neg(untl(ξ,η)) ∉ f(w_next) (w is rightmost), need different argument
      have h_mcs_w := h_c0 w hw_dom
      have h_mcs_wn := h_c0 w_next hw_next_dom
      have h_r3m_w := h_c2' w w_next h_adj_w
      -- Key lemma: ξ ∉ g(w, w_next) when η ∈ f(w_next)
      -- (which holds when w_next = y since h_event : η ∈ f(y))
      -- When w_next ≤ y and neg(untl) ∉ f(w_next): untl ∈ f(w_next).
      -- If w_next = y: η ∈ f(w_next) from h_event.
      -- Use this to prove ξ ∉ g(w, w_next).
      have h_xi_not_g : pc.ξ ∉ χ.g w w_next := by
        intro h_xi_g
        -- Burgess 2.9 case analysis (both sub-cases proved):
        -- Case 1: η ∈ f(w_next) → direct contradiction via burgessRSet.
        -- Case 2: η ∉ f(w_next) → use ξ ∈ f(w_next) (from h_no_wit) and
        --   untl(ξ,η) ∈ f(w_next) (from w rightmost with neg-until) to form
        --   ξ ∧ untl(ξ,η) ∈ f(w_next), then BX6 absorption gives contradiction.
        by_cases h_eta_wn : pc.η ∈ χ.f w_next
        · -- η ∈ f(w_next): direct contradiction
          have h_untl := h_r3m_w.2.1.1 pc.ξ h_xi_g pc.η h_eta_wn
          exact absurd h_untl (SetMaximalConsistent.neg_excludes h_mcs_w (Formula.untl pc.η pc.ξ) hw_neg_until)
        · -- η ∉ f(w_next): need more involved argument
          -- w_next must be < y (if w_next = y, then η ∈ f(y) = f(w_next) by h_event)
          have hw_next_lt_y : w_next < pc.y := by
            rcases lt_or_eq_of_le hw_next_le_y with h | h
            · exact h
            · exact absurd (h ▸ h_event) h_eta_wn
          -- untl(ξ,η) ∈ f(w_next) (since neg(untl) ∉ f(w_next) by w rightmost)
          have h_untl_wn : Formula.untl pc.η pc.ξ ∈ χ.f w_next := by
            rcases SetMaximalConsistent.negation_complete h_mcs_wn (Formula.untl pc.η pc.ξ) with h | h
            · exact h
            · exact absurd h (hw_rightmost w_next hw_next_dom hw_lt_next hw_next_lt_y)
          -- Burgess 2.9 case n=m+1: derive contradiction using BX6 absorption.
          -- Key: ξ ∈ f(w_next) (since no ξ.neg between pc.x and pc.y, and pc.x < w_next < pc.y).
          have hx_le_w : pc.x ≤ w := by
            have : pc.x ∈ S_w := Finset.mem_filter.mpr ⟨h_xm, h_lt, h_neg_until⟩
            exact Finset.le_max' S_w pc.x this
          have hx_lt_wn : pc.x < w_next := lt_of_le_of_lt hx_le_w hw_lt_next
          have h_xi_wn : pc.ξ ∈ χ.f w_next := by
            rcases SetMaximalConsistent.negation_complete h_mcs_wn pc.ξ with h | h
            · exact h
            · -- ξ.neg ∈ f(w_next), but w_next is between pc.x and pc.y, contradicting h_no_wit
              exact absurd ⟨w_next, hw_next_dom, hx_lt_wn, hw_next_lt_y, h⟩ h_no_wit
          -- Form ξ ∧ untl(ξ,η) ∈ f(w_next) by conjunction closure in MCS
          have h_conj_wn : Formula.and pc.ξ (Formula.untl pc.η pc.ξ) ∈ χ.f w_next :=
            dcs_conj_closed (mcs_is_dcs h_mcs_wn) h_xi_wn h_untl_wn
          -- From burgessRSet: untl(ξ, ξ ∧ untl(ξ,η)) ∈ f(w)
          have h_untl_conj := h_r3m_w.2.1.1 pc.ξ h_xi_g
            (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)) h_conj_wn
          -- BX6 absorption: untl(φ, φ ∧ untl(φ, ψ)) → untl(φ, ψ)
          have h_bx6 : DerivationTree fc []
            ((Formula.untl (Formula.and pc.ξ (Formula.untl pc.η pc.ξ)) pc.ξ).imp
              (Formula.untl pc.η pc.ξ)) :=
            DerivationTree.axiom [] _ (Axiom.absorb_until pc.ξ pc.η) trivial
          have h_bx6_in := theorem_in_mcs_fc h_mcs_w h_bx6
          have h_untl_eta := SetMaximalConsistent.implication_property h_mcs_w h_bx6_in h_untl_conj
          -- Now untl(ξ,η) ∈ f(w) contradicts neg(untl(ξ,η)) ∈ f(w)
          exact absurd h_untl_eta
            (SetMaximalConsistent.neg_excludes h_mcs_w (Formula.untl pc.η pc.ξ) hw_neg_until)
      -- Now: ξ ∉ g(w, w_next). Apply lemma_2_6_splitting with β = ξ.
      have h_B_sdc_w := BurgessR3Maximal_sdc h_r3m_w h_xi_not_g
      have h_gc_w := BurgessR3Maximal_g_content_sub h_r3m_w h_mcs_w h_mcs_wn
      have h_split := lemma_2_6_splitting fc h_mcs_w h_mcs_wn h_r3m_w h_B_sdc_w.2 h_gc_w
        pc.ξ h_xi_not_g
      let B' := h_split.choose
      let D := h_split.choose_spec.choose
      let B'' := h_split.choose_spec.choose_spec.choose
      have h_split_prop := h_split.choose_spec.choose_spec.choose_spec
      have h_B'_max : BurgessR3Maximal fc (χ.f w) B' D := h_split_prop.1
      have h_B''_max : BurgessR3Maximal fc D B'' (χ.f w_next) := h_split_prop.2.1
      have h_D_mcs : SetMaximalConsistent fc D := h_split_prop.2.2.1
      have h_xi_neg_D : pc.ξ.neg ∈ D := h_split_prop.2.2.2.1
      have h_g_sub_D : χ.g w w_next ⊆ D := h_split_prop.2.2.2.2.1
      have h_g_sub_B' : χ.g w w_next ⊆ B' := h_split_prop.2.2.2.2.2.1
      have h_g_sub_B'' : χ.g w w_next ⊆ B'' := h_split_prop.2.2.2.2.2.2
      -- Insert z between w and w_next
      set z := (w + w_next) / 2 with hz_def
      have hz_lt_wn : z < w_next := by linarith
      have hw_lt_z : w < z := by linarith
      have hz_notin : z ∉ χ.dom := by
        intro h_mem; exact h_adj_w.2.2.2 z h_mem ⟨hw_lt_z, hz_lt_wn⟩
      -- z is between x and y: w ≥ x (w ∈ dom with neg-until, could be x itself)
      -- and w_next ≤ y.
      have hx_le_w : pc.x ≤ w := by
        have : pc.x ∈ S_w := Finset.mem_filter.mpr ⟨h_xm, h_lt, h_neg_until⟩
        exact Finset.le_max' S_w pc.x this
      have hx_lt_z : pc.x < z := lt_of_le_of_lt hx_le_w hw_lt_z
      have hz_lt_y : z < pc.y := lt_of_lt_of_le hz_lt_wn hw_next_le_y
      -- Build new chronicle with f'(z) = D, updated g
      let g' := fun a b =>
        if a = w ∧ b = z then B'
        else if a = z ∧ b = w_next then B''
        else χ.g a b
      let χ' : Chronicle Atom := ⟨fun q => if q = z then D else χ.f q, g', insert z χ.dom⟩
      -- Prove c2' for the new chronicle
      have h_c2'_new : χ'.c2' fc := by
        intro a b h_adj_new
        obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
        simp only [χ', Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd hab (lt_irrefl _)
        · -- a = z, b ∈ old dom: must be (z, w_next)
          have hb_eq : b = w_next := by
            by_contra hb_ne
            have hb_ge : w_next ≤ b := by
              by_contra hlt; push_neg at hlt
              have : w < b := lt_trans hw_lt_z hab
              exact h_adj_w.2.2.2 b hb ⟨this, hlt⟩
            have hb_gt : w_next < b := lt_of_le_of_ne hb_ge (Ne.symm hb_ne)
            exact h_no_between w_next (Finset.mem_insert_of_mem hw_next_dom) ⟨hz_lt_wn, hb_gt⟩
          subst hb_eq
          show BurgessR3Maximal fc
            (if z = z then D else χ.f z)
            (g' z w_next)
            (if w_next = z then D else χ.f w_next)
          have hwn_ne : w_next ≠ z := by linarith
          simp only [ite_true, hwn_ne, ite_false, g']
          simp only [ite_false, ite_true, and_false, and_self]
          exact h_B''_max
        · -- a ∈ old dom, b = z: must be (w, z)
          have ha_eq : a = w := by
            by_contra ha_ne
            have ha_le : a ≤ w := by
              by_contra hgt; push_neg at hgt
              exact h_adj_w.2.2.2 a ha ⟨hgt, lt_trans hab hz_lt_wn⟩
            have ha_lt : a < w := lt_of_le_of_ne ha_le ha_ne
            exact h_no_between w (Finset.mem_insert_of_mem hw_dom) ⟨ha_lt, hw_lt_z⟩
          subst ha_eq
          show BurgessR3Maximal fc
            (if w = z then D else χ.f w)
            (g' w z)
            (if z = z then D else χ.f z)
          have hw_ne : w ≠ z := by linarith
          simp only [hw_ne, ite_false, ite_true, g']
          exact h_B'_max
        · -- Both old: preserved
          have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
          have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
          show BurgessR3Maximal fc
            (if a = z then D else χ.f a)
            (g' a b)
            (if b = z then D else χ.f b)
          simp only [ha_ne, hb_ne, ite_false, g', and_false, false_and]
          have h_adj_old : Adjacent χ.dom a b := by
            refine ⟨ha, hb, hab, ?_⟩
            intro u hu ⟨hau, hub⟩
            exact h_no_between u (Finset.mem_insert_of_mem hu) ⟨hau, hub⟩
          exact h_c2' a b h_adj_old
      exact { val := χ'
              dom_sub := Finset.subset_insert z χ.dom
              c0 := by
                intro q hq
                show SetMaximalConsistent fc (if q = z then D else χ.f q)
                change q ∈ insert z χ.dom at hq
                simp only [Finset.mem_insert] at hq
                rcases hq with rfl | hq
                · simp only [ite_true]; exact h_D_mcs
                · have h_ne : q ≠ z := fun h => hz_notin (h ▸ hq)
                  simp only [h_ne, ite_false]; exact h_c0 q hq
              f_agrees := by
                intro x hx
                have h_ne : x ≠ z := fun h => hz_notin (h ▸ hx)
                exact if_neg h_ne
              g_agrees := by
                intro a b ha hb
                show g' a b = χ.g a b
                simp only [g']
                have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
                have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
                simp only [ha_ne, hb_ne, false_and, and_false, ite_false]
              c2' := h_c2'_new
              c5_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c5_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c4_forward_witness := by
                intro _ _ _ _ _ _
                refine ⟨z, Finset.mem_insert_self z χ.dom, hx_lt_z, hz_lt_y, ?_⟩
                show pc.ξ.neg ∈ (if z = z then D else χ.f z)
                simp only [ite_true]
                exact h_xi_neg_D
              c4_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)

              g_sub_f_insert := by
                intro a b h_adj w0 hw0 hw0_not haw0 hw0b
                simp only [χ', Finset.mem_insert] at hw0
                rcases hw0 with rfl | hw0
                · show χ.g a b ⊆ (if z = z then D else χ.f z)
                  simp only [ite_true]
                  have hab : a = w ∧ b = w_next := by
                    constructor
                    · by_contra ha_ne
                      have : a < w ∨ w < a := lt_or_gt_of_ne ha_ne
                      rcases this with h | h
                      · exact h_adj.2.2.2 w hw_dom ⟨h, lt_trans hw_lt_z hw0b⟩
                      · exact h_adj_w.2.2.2 a h_adj.1 ⟨h, lt_trans haw0 hz_lt_wn⟩
                    · by_contra hb_ne
                      have : b < w_next ∨ w_next < b := lt_or_gt_of_ne hb_ne
                      rcases this with h | h
                      · exact h_adj_w.2.2.2 b h_adj.2.1 ⟨lt_trans hw_lt_z hw0b, h⟩
                      · exact h_adj.2.2.2 w_next hw_next_dom ⟨lt_trans haw0 hz_lt_wn, h⟩
                  rw [hab.1, hab.2]; exact h_g_sub_D
                · exact absurd hw0 hw0_not
              g_sub_g_new := by
                intro a b h_adj w0 hw0 hw0_not haw0 hw0b
                simp only [χ', Finset.mem_insert] at hw0
                rcases hw0 with rfl | hw0
                · have ha_eq : a = w := by
                    by_contra ha_ne
                    rcases lt_or_gt_of_ne ha_ne with h | h
                    · exact h_adj.2.2.2 w hw_dom ⟨h, lt_trans hw_lt_z hw0b⟩
                    · exact h_adj_w.2.2.2 a h_adj.1 ⟨h, lt_trans haw0 hz_lt_wn⟩
                  have hb_eq : b = w_next := by
                    by_contra hb_ne
                    rcases lt_or_gt_of_ne hb_ne with h | h
                    · exact h_adj_w.2.2.2 b h_adj.2.1 ⟨lt_trans hw_lt_z hw0b, h⟩
                    · exact h_adj.2.2.2 w_next hw_next_dom ⟨lt_trans haw0 hz_lt_wn, h⟩
                  subst ha_eq; subst hb_eq
                  constructor
                  · show χ.g w w_next ⊆ g' w z
                    simp only [g', and_self, ite_true]
                    exact h_g_sub_B'
                  · show χ.g w w_next ⊆ g' z w_next
                    simp only [g']
                    have : ¬(z = w ∧ w_next = z) := by
                      intro ⟨h1, _⟩; linarith
                    simp only [this, ite_false, and_self, ite_true]
                    exact h_g_sub_B''
                · exact absurd hw0 hw0_not
              dom_new_unique := by
                intro u v hu hu_not hv hv_not
                simp only [χ', Finset.mem_insert] at hu hv
                rcases hu with rfl | hu <;> rcases hv with rfl | hv
                · rfl
                · exact absurd hv hv_not
                · exact absurd hu hu_not
                · exact absurd hu hu_not
              c5_forward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide)
              c5_backward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide) }
    · exact { val := χ
              dom_sub := Finset.Subset.refl _
              c0 := h_c0
              f_agrees := fun _ _ => rfl
              g_agrees := fun _ _ _ _ => rfl
              c2' := by exact h_c2'
              c5_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c5_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c4_forward_witness := by
                intro _ h_xm' h_ym' h_lt' h_neg_until' h_event'
                push_neg at h_actual
                exact h_actual h_xm' h_ym' h_lt' h_neg_until' h_event'
              c4_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)

              g_sub_f_insert := fun _ _ _ w hw hw_not _ _ => absurd hw hw_not
              g_sub_g_new := fun _ _ _ w hw hw_not _ _ => absurd hw hw_not
              dom_new_unique := fun u _ hu hu_not _ _ => absurd hu hu_not
              c5_forward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide)
              c5_backward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide) }
  | .c4_backward =>
    -- Backward C4' case (corrected Burgess C4b: check EVENT η at f(y), negate GUARD ξ at f(z))
    -- Now checks ALL pairs y < x, not just adjacent pairs.
    by_cases h_actual : pc.x ∈ χ.dom ∧ pc.y ∈ χ.dom ∧
        pc.y < pc.x ∧
        (Formula.snce pc.η pc.ξ).neg ∈ χ.f pc.x ∧
        pc.η ∈ χ.f pc.y ∧
        ¬∃ z ∈ χ.dom, pc.y < z ∧ z < pc.x ∧ pc.ξ.neg ∈ χ.f z
    · obtain ⟨h_xm, h_ym, h_lt, h_neg_since, h_event, h_no_wit⟩ := h_actual
      -- Inline C4' elimination with c2' preservation (Since mirror of c4_forward).
      -- Strategy: find adjacent pair (w_prev, w) between y and x where
      -- ξ ∉ g(w_prev, w), then split using lemma_2_6_splitting with β = ξ.
      --
      -- Key fact: if neg(snce(ξ,η)) ∈ f(w) and η ∈ f(w_prev), then ξ ∉ g(w_prev, w).
      -- Proof: if ξ ∈ g, burgessRSetSince gives S(ξ, η) = snce(ξ,η) ∈ f(w),
      -- contradicting neg(snce(ξ,η)) ∈ f(w).
      --
      -- Find w = leftmost domain point in (y, x] with neg(snce(ξ,η)) ∈ f(w).
      -- x is always a valid candidate. w_prev is the predecessor of w in dom.
      -- If w_prev = y (or η ∈ f(w_prev)): η ∈ f(w_prev), so ξ ∉ g(w_prev, w).
      have h_mcs_x := h_c0 pc.x h_xm
      have h_mcs_y := h_c0 pc.y h_ym
      -- Find w (leftmost with neg-since in (y, x])
      haveI : DecidablePred (fun w => pc.y < w ∧
          (Formula.snce pc.η pc.ξ).neg ∈ χ.f w) :=
        fun w => Classical.dec _
      set S_w := χ.dom.filter (fun w => pc.y < w ∧ (Formula.snce pc.η pc.ξ).neg ∈ χ.f w)
      have hS_ne : S_w.Nonempty := by
        refine ⟨pc.x, Finset.mem_filter.mpr ⟨h_xm, h_lt, h_neg_since⟩⟩
      set w := S_w.min' hS_ne
      have hw_mem_S := Finset.min'_mem S_w hS_ne
      have hw_dom : w ∈ χ.dom := (Finset.mem_filter.mp hw_mem_S).1
      have hy_lt_w : pc.y < w := (Finset.mem_filter.mp hw_mem_S).2.1
      have hw_neg_since : (Formula.snce pc.η pc.ξ).neg ∈ χ.f w :=
        (Finset.mem_filter.mp hw_mem_S).2.2
      have hw_leftmost : ∀ v ∈ χ.dom, pc.y < v → v < w →
          (Formula.snce pc.η pc.ξ).neg ∉ χ.f v := by
        intro v hv hyv hvw h_neg_v
        have hv_in_S : v ∈ S_w := Finset.mem_filter.mpr ⟨hv, hyv, h_neg_v⟩
        have := Finset.min'_le S_w v hv_in_S
        linarith
      -- Find w_prev = predecessor of w in dom (largest domain element < w with w_prev ≥ y)
      set T_w := χ.dom.filter (fun v => decide (v < w))
      have hT_ne : T_w.Nonempty :=
        ⟨pc.y, Finset.mem_filter.mpr ⟨h_ym, by simp [hy_lt_w]⟩⟩
      set w_prev := T_w.max' hT_ne
      have hw_prev_mem_T := Finset.max'_mem T_w hT_ne
      have hw_prev_dom : w_prev ∈ χ.dom := (Finset.mem_filter.mp hw_prev_mem_T).1
      have hw_prev_lt : w_prev < w := by
        have := (Finset.mem_filter.mp hw_prev_mem_T).2
        simp only [decide_eq_true_eq] at this; exact this
      have hy_le_prev : pc.y ≤ w_prev := by
        have : pc.y ∈ T_w := Finset.mem_filter.mpr ⟨h_ym, by simp [hy_lt_w]⟩
        exact Finset.le_max' T_w pc.y this
      have h_adj_w : Adjacent χ.dom w_prev w := by
        refine ⟨hw_prev_dom, hw_dom, hw_prev_lt, ?_⟩
        intro u hu ⟨hpu, huw⟩
        have hu_T : u ∈ T_w := Finset.mem_filter.mpr ⟨hu, by simp [huw]⟩
        have := Finset.le_max' T_w u hu_T
        linarith
      have h_mcs_w := h_c0 w hw_dom
      have h_mcs_wp := h_c0 w_prev hw_prev_dom
      have h_r3m_w := h_c2' w_prev w h_adj_w
      -- Key: ξ ∉ g(w_prev, w) when η ∈ f(w_prev)
      -- burgessRSetSince(f(w), g(w_prev,w), f(w_prev)): ∀ β ∈ g, α ∈ f(w_prev), S(β,α) ∈ f(w)
      -- If ξ ∈ g and η ∈ f(w_prev): snce(ξ,η) ∈ f(w), contradicting neg(snce(ξ,η)) ∈ f(w).
      have h_xi_not_g : pc.ξ ∉ χ.g w_prev w := by
        intro h_xi_g
        by_cases h_eta_wp : pc.η ∈ χ.f w_prev
        · -- η ∈ f(w_prev): S(ξ, η) ∈ f(w) by burgessRSetSince, contradiction
          have h_snce := h_r3m_w.2.1.2 pc.ξ h_xi_g pc.η h_eta_wp
          exact absurd h_snce (SetMaximalConsistent.neg_excludes h_mcs_w (Formula.snce pc.η pc.ξ) hw_neg_since)
        · -- η ∉ f(w_prev): need more involved argument
          have hy_lt_prev : pc.y < w_prev := by
            rcases lt_or_eq_of_le hy_le_prev with h | h
            · exact h
            · exact absurd (h ▸ h_event) h_eta_wp
          have h_snce_wp : Formula.snce pc.η pc.ξ ∈ χ.f w_prev := by
            rcases SetMaximalConsistent.negation_complete h_mcs_wp (Formula.snce pc.η pc.ξ) with h | h
            · exact h
            · exact absurd h (hw_leftmost w_prev hw_prev_dom hy_lt_prev hw_prev_lt)
          -- Burgess 2.9' case n=m+1 (Since mirror): derive contradiction using BX6' absorption.
          -- Key: ξ ∈ f(w_prev) (since no ξ.neg between pc.y and pc.x, and pc.y < w_prev < pc.x).
          have hw_le_x : w ≤ pc.x := by
            have : pc.x ∈ S_w := Finset.mem_filter.mpr ⟨h_xm, h_lt, h_neg_since⟩
            exact Finset.min'_le S_w pc.x this
          have hwp_lt_x : w_prev < pc.x := lt_of_lt_of_le hw_prev_lt hw_le_x
          have h_xi_wp : pc.ξ ∈ χ.f w_prev := by
            rcases SetMaximalConsistent.negation_complete h_mcs_wp pc.ξ with h | h
            · exact h
            · exact absurd ⟨w_prev, hw_prev_dom, hy_lt_prev, hwp_lt_x, h⟩ h_no_wit
          -- Form ξ ∧ snce(ξ,η) ∈ f(w_prev) by conjunction closure in MCS
          have h_conj_wp : Formula.and pc.ξ (Formula.snce pc.η pc.ξ) ∈ χ.f w_prev :=
            dcs_conj_closed (mcs_is_dcs h_mcs_wp) h_xi_wp h_snce_wp
          -- From burgessRSetSince: snce(ξ, ξ ∧ snce(ξ,η)) ∈ f(w)
          have h_snce_conj := h_r3m_w.2.1.2 pc.ξ h_xi_g
            (Formula.and pc.ξ (Formula.snce pc.η pc.ξ)) h_conj_wp
          -- BX6' absorption: snce(φ, φ ∧ snce(φ, ψ)) → snce(φ, ψ)
          have h_bx6' : DerivationTree fc []
            ((Formula.snce (Formula.and pc.ξ (Formula.snce pc.η pc.ξ)) pc.ξ).imp
              (Formula.snce pc.η pc.ξ)) :=
            DerivationTree.axiom [] _ (Axiom.absorb_since pc.ξ pc.η) trivial
          have h_bx6'_in := theorem_in_mcs_fc h_mcs_w h_bx6'
          have h_snce_eta := SetMaximalConsistent.implication_property h_mcs_w h_bx6'_in h_snce_conj
          -- Now snce(ξ,η) ∈ f(w) contradicts neg(snce(ξ,η)) ∈ f(w)
          exact absurd h_snce_eta
            (SetMaximalConsistent.neg_excludes h_mcs_w (Formula.snce pc.η pc.ξ) hw_neg_since)
      -- Now: ξ ∉ g(w_prev, w). Apply lemma_2_6_splitting with β = ξ.
      have h_B_sdc_w := BurgessR3Maximal_sdc h_r3m_w h_xi_not_g
      have h_gc_w := BurgessR3Maximal_g_content_sub h_r3m_w h_mcs_wp h_mcs_w
      have h_split := lemma_2_6_splitting fc h_mcs_wp h_mcs_w h_r3m_w h_B_sdc_w.2 h_gc_w
        pc.ξ h_xi_not_g
      let B' := h_split.choose
      let D := h_split.choose_spec.choose
      let B'' := h_split.choose_spec.choose_spec.choose
      have h_split_prop := h_split.choose_spec.choose_spec.choose_spec
      have h_B'_max : BurgessR3Maximal fc (χ.f w_prev) B' D := h_split_prop.1
      have h_B''_max : BurgessR3Maximal fc D B'' (χ.f w) := h_split_prop.2.1
      have h_D_mcs : SetMaximalConsistent fc D := h_split_prop.2.2.1
      have h_xi_neg_D : pc.ξ.neg ∈ D := h_split_prop.2.2.2.1
      have h_g_sub_D : χ.g w_prev w ⊆ D := h_split_prop.2.2.2.2.1
      have h_g_sub_B' : χ.g w_prev w ⊆ B' := h_split_prop.2.2.2.2.2.1
      have h_g_sub_B'' : χ.g w_prev w ⊆ B'' := h_split_prop.2.2.2.2.2.2
      -- Insert z between w_prev and w
      set z := (w_prev + w) / 2 with hz_def
      have hz_lt_w : z < w := by linarith
      have hwp_lt_z : w_prev < z := by linarith
      have hz_notin : z ∉ χ.dom := by
        intro h_mem; exact h_adj_w.2.2.2 z h_mem ⟨hwp_lt_z, hz_lt_w⟩
      -- z is between y and x: w_prev ≥ y and w ≤ x
      have hw_le_x : w ≤ pc.x := by
        have : pc.x ∈ S_w := Finset.mem_filter.mpr ⟨h_xm, h_lt, h_neg_since⟩
        exact Finset.min'_le S_w pc.x this
      have hy_lt_z : pc.y < z := lt_of_le_of_lt hy_le_prev hwp_lt_z
      have hz_lt_x : z < pc.x := lt_of_lt_of_le hz_lt_w hw_le_x
      -- Build new chronicle
      let g' := fun a b =>
        if a = w_prev ∧ b = z then B'
        else if a = z ∧ b = w then B''
        else χ.g a b
      let χ' : Chronicle Atom := ⟨fun q => if q = z then D else χ.f q, g', insert z χ.dom⟩
      -- Prove c2'
      have h_c2'_new : χ'.c2' fc := by
        intro a b h_adj_new
        obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
        simp only [χ', Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd hab (lt_irrefl _)
        · -- a = z, b ∈ old dom: must be (z, w)
          have hb_eq : b = w := by
            by_contra hb_ne
            have hb_ge : w ≤ b := by
              by_contra hlt; push_neg at hlt
              have : w_prev < b := lt_trans hwp_lt_z hab
              exact h_adj_w.2.2.2 b hb ⟨this, hlt⟩
            have hb_gt : w < b := lt_of_le_of_ne hb_ge (Ne.symm hb_ne)
            exact h_no_between w (Finset.mem_insert_of_mem hw_dom) ⟨hz_lt_w, hb_gt⟩
          subst hb_eq
          show BurgessR3Maximal fc
            (if z = z then D else χ.f z)
            (g' z w)
            (if w = z then D else χ.f w)
          have hw_ne : w ≠ z := by linarith
          simp only [ite_true, hw_ne, ite_false, g']
          simp only [ite_false, ite_true, and_false, and_self]
          exact h_B''_max
        · -- a ∈ old dom, b = z: must be (w_prev, z)
          have ha_eq : a = w_prev := by
            by_contra ha_ne
            have ha_le : a ≤ w_prev := by
              by_contra hgt; push_neg at hgt
              exact h_adj_w.2.2.2 a ha ⟨hgt, lt_trans hab hz_lt_w⟩
            have ha_lt : a < w_prev := lt_of_le_of_ne ha_le ha_ne
            exact h_no_between w_prev (Finset.mem_insert_of_mem hw_prev_dom) ⟨ha_lt, hwp_lt_z⟩
          subst ha_eq
          show BurgessR3Maximal fc
            (if w_prev = z then D else χ.f w_prev)
            (g' w_prev z)
            (if z = z then D else χ.f z)
          have hwp_ne : w_prev ≠ z := by linarith
          simp only [hwp_ne, ite_false, ite_true, g']
          exact h_B'_max
        · -- Both old: preserved
          have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
          have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
          show BurgessR3Maximal fc
            (if a = z then D else χ.f a)
            (g' a b)
            (if b = z then D else χ.f b)
          simp only [ha_ne, hb_ne, ite_false, g', and_false, false_and]
          have h_adj_old : Adjacent χ.dom a b := by
            refine ⟨ha, hb, hab, ?_⟩
            intro u hu ⟨hau, hub⟩
            exact h_no_between u (Finset.mem_insert_of_mem hu) ⟨hau, hub⟩
          exact h_c2' a b h_adj_old
      exact { val := χ'
              dom_sub := Finset.subset_insert z χ.dom
              c0 := by
                intro q hq
                show SetMaximalConsistent fc (if q = z then D else χ.f q)
                change q ∈ insert z χ.dom at hq
                simp only [Finset.mem_insert] at hq
                rcases hq with rfl | hq
                · simp only [ite_true]; exact h_D_mcs
                · have h_ne : q ≠ z := fun h => hz_notin (h ▸ hq)
                  simp only [h_ne, ite_false]; exact h_c0 q hq
              f_agrees := by
                intro x hx
                have h_ne : x ≠ z := fun h => hz_notin (h ▸ hx)
                exact if_neg h_ne
              g_agrees := by
                intro a b ha hb
                show g' a b = χ.g a b
                simp only [g']
                have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
                have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
                simp only [ha_ne, hb_ne, false_and, and_false, ite_false]
              c2' := h_c2'_new
              c5_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c5_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c4_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c4_backward_witness := by
                intro _ _ _ _ _ _
                refine ⟨z, Finset.mem_insert_self z χ.dom, hy_lt_z, hz_lt_x, ?_⟩
                show pc.ξ.neg ∈ (if z = z then D else χ.f z)
                simp only [ite_true]
                exact h_xi_neg_D

              g_sub_f_insert := by
                intro a b h_adj w0 hw0 hw0_not haw0 hw0b
                simp only [χ', Finset.mem_insert] at hw0
                rcases hw0 with rfl | hw0
                · show χ.g a b ⊆ (if z = z then D else χ.f z)
                  simp only [ite_true]
                  have hab : a = w_prev ∧ b = w := by
                    constructor
                    · by_contra ha_ne
                      have : a < w_prev ∨ w_prev < a := lt_or_gt_of_ne ha_ne
                      rcases this with h | h
                      · exact h_adj.2.2.2 w_prev hw_prev_dom ⟨h, lt_trans hwp_lt_z hw0b⟩
                      · exact h_adj_w.2.2.2 a h_adj.1 ⟨h, lt_trans haw0 hz_lt_w⟩
                    · by_contra hb_ne
                      have : b < w ∨ w < b := lt_or_gt_of_ne hb_ne
                      rcases this with h | h
                      · exact h_adj_w.2.2.2 b h_adj.2.1 ⟨lt_trans hwp_lt_z hw0b, h⟩
                      · exact h_adj.2.2.2 w hw_dom ⟨lt_trans haw0 hz_lt_w, h⟩
                  rw [hab.1, hab.2]; exact h_g_sub_D
                · exact absurd hw0 hw0_not
              g_sub_g_new := by
                intro a b h_adj w0 hw0 hw0_not haw0 hw0b
                simp only [χ', Finset.mem_insert] at hw0
                rcases hw0 with rfl | hw0
                · have ha_eq : a = w_prev := by
                    by_contra ha_ne
                    rcases lt_or_gt_of_ne ha_ne with h | h
                    · exact h_adj.2.2.2 w_prev hw_prev_dom ⟨h, lt_trans hwp_lt_z hw0b⟩
                    · exact h_adj_w.2.2.2 a h_adj.1 ⟨h, lt_trans haw0 hz_lt_w⟩
                  have hb_eq : b = w := by
                    by_contra hb_ne
                    rcases lt_or_gt_of_ne hb_ne with h | h
                    · exact h_adj_w.2.2.2 b h_adj.2.1 ⟨lt_trans hwp_lt_z hw0b, h⟩
                    · exact h_adj.2.2.2 w hw_dom ⟨lt_trans haw0 hz_lt_w, h⟩
                  subst ha_eq; subst hb_eq
                  constructor
                  · show χ.g w_prev w ⊆ g' w_prev z
                    simp only [g', and_self, ite_true]
                    exact h_g_sub_B'
                  · show χ.g w_prev w ⊆ g' z w
                    simp only [g']
                    have : ¬(z = w_prev ∧ w = z) := by
                      intro ⟨h1, _⟩; linarith
                    simp only [this, ite_false, and_self, ite_true]
                    exact h_g_sub_B''
                · exact absurd hw0 hw0_not
              dom_new_unique := by
                intro u v hu hu_not hv hv_not
                simp only [χ', Finset.mem_insert] at hu hv
                rcases hu with rfl | hu <;> rcases hv with rfl | hv
                · rfl
                · exact absurd hv hv_not
                · exact absurd hu hu_not
                · exact absurd hu hu_not
              c5_forward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide)
              c5_backward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide) }
    · exact { val := χ
              dom_sub := Finset.Subset.refl _
              c0 := h_c0
              f_agrees := fun _ _ => rfl
              g_agrees := fun _ _ _ _ => rfl
              c2' := by exact h_c2'
              c5_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c5_backward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c4_forward_witness := fun h => by rw [h_kind] at h; exact absurd h (by decide)
              c4_backward_witness := by
                intro _ h_xm' h_ym' h_lt' h_neg_since' h_event'
                push_neg at h_actual
                exact h_actual h_xm' h_ym' h_lt' h_neg_since' h_event'

              g_sub_f_insert := fun _ _ _ w hw hw_not _ _ => absurd hw hw_not
              g_sub_g_new := fun _ _ _ w hw hw_not _ _ => absurd hw hw_not
              dom_new_unique := fun u _ hu hu_not _ _ => absurd hu hu_not
              c5_forward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide)
              c5_backward_resolved_no_new := fun h => absurd h (by rw [h_kind]; decide) }

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle
