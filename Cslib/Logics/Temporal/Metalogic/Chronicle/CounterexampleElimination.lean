/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes
import Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation
import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion
import Cslib.Logics.Temporal.Metalogic.Chronicle.Frame
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

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

/-! ## Private Helper: theorem_in_mcs for Temporal.SetMaximalConsistent -/

private noncomputable def theorem_in_mcs' {M : Set (Formula Atom)} {phi : Formula Atom}
    (h_mcs : Temporal.SetMaximalConsistent M)
    (h_deriv : DerivationTree FrameClass.Base [] phi) : phi ∈ M :=
  temporal_closed_under_derivation h_mcs (L := []) (fun _ h => by simp at h) ⟨h_deriv⟩

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
-/
theorem exists_rat_between_not_in_finset (fs : Finset Rat) (x y : Rat) (hxy : x < y) :
    ∃ z : Rat, x < z ∧ z < y ∧ z ∉ fs := by
  set T := fs.filter (fun s => x < s ∧ s < y) with hT_def
  by_cases hT : T.Nonempty
  · set t := T.min' hT with ht_def
    have ht_mem : t ∈ T := Finset.min'_mem T hT
    have ht_prop : x < t ∧ t < y := by
      rw [hT_def] at ht_mem; exact (Finset.mem_filter.mp ht_mem).2
    set z := (x + t) / 2 with hz_def
    have hxz : x < z := by linarith
    have hzt : z < t := by linarith
    have hzy : z < y := lt_trans hzt ht_prop.2
    refine ⟨z, hxz, hzy, ?_⟩
    intro hz_mem
    have hz_in_T : z ∈ T := by
      rw [hT_def]; exact Finset.mem_filter.mpr ⟨hz_mem, hxz, hzy⟩
    have : t ≤ z := Finset.min'_le T z hz_in_T
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    set z := (x + y) / 2 with hz_def
    have hxz : x < z := by linarith
    have hzy : z < y := by linarith
    refine ⟨z, hxz, hzy, ?_⟩
    intro hz_mem
    have : z ∈ T := by
      rw [hT_def]; exact Finset.mem_filter.mpr ⟨hz_mem, hxz, hzy⟩
    rw [hT] at this
    exact absurd this (by simp)

/-! ## BurgessR3Maximal Helper Lemmas -/

/--
**BurgessR3Maximal implies g_content(A) ⊆ C**: If BurgessR3Maximal(A, B, C) holds with
A and C both MCS, then g_content(A) ⊆ C.
-/
theorem BurgessR3Maximal_g_content_sub {A B C : Set (Formula Atom)}
    (h_r3m : BurgessR3Maximal A B C)
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C) :
    g_content A ⊆ C := by
  intro φ hφ
  change Formula.all_future φ ∈ A at hφ
  by_contra h_not_C
  have h_neg_C : φ.neg ∈ C := by
    rcases temporal_negation_complete h_mcs_C φ with h | h
    · exact absurd h h_not_C
    · exact h
  set top := Formula.bot.imp Formula.bot with top_def
  have h_top_B : top ∈ B :=
    cud_contains_theorems h_r3m.1 (identity Formula.bot)
  have h_untl : Formula.untl φ.neg top ∈ A :=
    h_r3m.2.1.1 top h_top_B φ.neg h_neg_C
  have h_F_neg : Formula.some_future φ.neg ∈ A :=
    until_implies_F_in_mcs h_mcs_A h_untl
  have h_dni : DerivationTree FrameClass.Base [] (φ.imp φ.neg.neg) := by
    have h1 : DerivationTree FrameClass.Base [φ.neg, φ] Formula.bot :=
      DerivationTree.modus_ponens [φ.neg, φ] φ Formula.bot
        (DerivationTree.assumption _ φ.neg (by simp))
        (DerivationTree.assumption _ φ (by simp))
    have h2 : DerivationTree FrameClass.Base [φ] φ.neg.neg :=
      deduction_theorem [φ] φ.neg Formula.bot h1
    exact deduction_theorem [] φ φ.neg.neg h2
  have h_G_dni : DerivationTree FrameClass.Base [] (Formula.all_future (φ.imp φ.neg.neg)) :=
    DerivationTree.temporal_necessitation _ h_dni
  have h_kd := temp_k_dist_derived φ φ.neg.neg
  have h1 := theorem_in_mcs' h_mcs_A h_G_dni
  have h2 := theorem_in_mcs' h_mcs_A h_kd
  have h3 := temporal_implication_property h_mcs_A h2 h1
  have h_G_nn : Formula.all_future φ.neg.neg ∈ A :=
    temporal_implication_property h_mcs_A h3 hφ
  exact some_future_all_future_neg_absurd h_mcs_A φ.neg h_F_neg h_G_nn

/--
**BurgessR3Maximal implies SetDeductivelyClosed** when some formula is not in B.
-/
theorem BurgessR3Maximal_sdc {A B C : Set (Formula Atom)}
    (h_r3m : BurgessR3Maximal A B C)
    {phi : Formula Atom} (h_not_mem : phi ∉ B) :
    SetDeductivelyClosed B :=
  cud_not_mem_is_sdc h_r3m.1 h_not_mem

/--
**BurgessR3Maximal excludes ⊥ when B is consistent**.
-/
theorem BurgessR3Maximal_bot_not_mem {A B C : Set (Formula Atom)}
    (_h_r3m : BurgessR3Maximal A B C)
    (h_cons : Temporal.SetConsistent B) :
    Formula.bot ∉ B := by
  intro h_bot
  exact h_cons [Formula.bot] (fun φ hφ => by simp at hφ; rw [hφ]; exact h_bot)
    ⟨DerivationTree.assumption [Formula.bot] Formula.bot (by simp)⟩

/--
Helper: for adjacent pairs in a chronicle satisfying c2', when inserting a new point
that splits an existing adjacent pair, the old adjacent pairs that don't involve the
split are preserved.
-/
theorem c2'_preserved_on_old_adjacent {χ χ' : Chronicle Atom}
    (h_c2' : χ.c2')
    (h_f_agrees : ∀ x ∈ χ.dom, χ'.f x = χ.f x)
    (h_g_agrees : ∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b)
    (h_dom_sub : χ.dom ⊆ χ'.dom)
    {a b : Rat}
    (h_adj' : Adjacent χ'.dom a b)
    (h_a_old : a ∈ χ.dom) (h_b_old : b ∈ χ.dom)
    (h_adj_old : Adjacent χ.dom a b) :
    BurgessR3Maximal (χ'.f a) (χ'.g a b) (χ'.f b) := by
  rw [h_f_agrees a h_a_old, h_g_agrees a b h_a_old h_b_old, h_f_agrees b h_b_old]
  exact h_c2' a b h_adj_old

/--
**BurgessR3Maximal from h_content subset (backward direction)**:
If h_content(C) ⊆ A (i.e., H(φ) ∈ C → φ ∈ A), then ∃ B, BurgessR3Maximal(A, B, C).
-/
theorem burgessR3Maximal_from_h_content_sub {A C : Set (Formula Atom)}
    (h_mcs_A : Temporal.SetMaximalConsistent A) (h_mcs_C : Temporal.SetMaximalConsistent C)
    (h_hc : h_content C ⊆ A) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal A B C := by
  have h_gc : g_content A ⊆ C :=
    h_content_sub_imp_g_content_sub' h_mcs_A h_mcs_C h_hc
  -- Construct burgessR3 seed using top = ⊥ → ⊥
  set top := Formula.bot.imp (Formula.bot : Formula Atom) with top_def
  have h_top_A : top ∈ A :=
    theorem_in_mcs' h_mcs_A (DerivationTree.axiom [] _ (.efq Formula.bot) trivial)
  have h_bR : burgessR A top C := by
    intro γ hγ
    -- g_content(A) ⊆ C gives F(γ) ∈ A via connect_past + connect_future
    have h_ax_cp : DerivationTree FrameClass.Base [] (γ.imp (Formula.all_past (Formula.some_future γ))) :=
      DerivationTree.axiom [] _ (Axiom.connect_past γ) trivial
    have h_HF : Formula.all_past (Formula.some_future γ) ∈ C :=
      temporal_implication_property h_mcs_C
        (theorem_in_mcs' h_mcs_C h_ax_cp) hγ
    have h_F : Formula.some_future γ ∈ A := h_hc h_HF
    have h_bx12 : DerivationTree FrameClass.Base [] ((Formula.some_future γ).imp (Formula.untl γ top)) :=
      DerivationTree.axiom [] _ (Axiom.F_until_equiv γ) trivial
    exact temporal_implication_property h_mcs_A
      (theorem_in_mcs' h_mcs_A h_bx12) h_F
  have h_bRS : burgessRSince C top A := by
    intro α hα
    have h_P : Formula.some_past α ∈ C := by
      by_contra h_not_P
      have h_neg_P : (Formula.some_past α).neg ∈ C :=
        (temporal_negation_complete h_mcs_C _).resolve_left h_not_P
      -- ¬P(α) ∈ C → H(¬α) ∈ C (via the duality of P and H)
      -- Actually: P(α) = ¬H(¬α), so ¬P(α) = ¬¬H(¬α) which by DNE gives H(¬α)
      -- H(α.neg) ∈ C → α.neg ∈ h_content(C) ⊆ A → contradiction with α ∈ A
      -- Let's use F_neg_of_G_not pattern adapted for P/H
      -- Actually we need: ¬P(α) → H(¬α). This follows from P = ¬H¬.
      -- P(α) = some_past α. If ¬P(α) ∈ C, we need to derive H(α.neg) ∈ C.
      -- some_past α = ¬(all_past (α.neg)) definitionally? No.
      -- some_past α = Formula.snce α (Formula.bot.imp Formula.bot)
      -- This doesn't directly give us H(¬α).
      -- Let's just use: α ∈ A, and show a contradiction.
      -- From ¬P(α) ∈ C, α.neg ∈ g_content(A) would give α.neg ∈ C... wrong direction.
      -- Actually: g_content(A) ⊆ C. If G(α) ∈ A, then α ∈ C.
      -- We need the dual: if something is in A, show P(it) ∈ C.
      -- From α ∈ A, we want P(α) ∈ C.
      -- Use connect_future: α → G(P(α)). So α ∈ A → G(P(α)) ∈ A → P(α) ∈ g_content(A) ⊆ C.
      have h_ax_cf : DerivationTree FrameClass.Base [] (α.imp (Formula.all_future (Formula.some_past α))) :=
        DerivationTree.axiom [] _ (Axiom.connect_future α) trivial
      have h_GP : Formula.all_future (Formula.some_past α) ∈ A :=
        temporal_implication_property h_mcs_A (theorem_in_mcs' h_mcs_A h_ax_cf) hα
      have h_P_in_C : Formula.some_past α ∈ C := h_gc h_GP
      exact h_not_P h_P_in_C
    have h_bx12' : DerivationTree FrameClass.Base [] ((Formula.some_past α).imp (Formula.snce α top)) :=
      DerivationTree.axiom [] _ (Axiom.P_since_equiv α) trivial
    exact temporal_implication_property h_mcs_C
      (theorem_in_mcs' h_mcs_C h_bx12') h_P
  exact burgessR3Maximal_exists_from_seed A C top h_mcs_A h_mcs_C h_bR h_bRS h_top_A

/-! ## Lemma 2.10: C5 Counterexample Elimination -/

/--
**Lemma 2.10** (C5 Counterexample Elimination): Given a chronicle satisfying C0
and a C5 counterexample (x, xi, eta), extend the chronicle by adding a new point y
with eta in f'(y).
-/
noncomputable def eliminate_C5_counterexample {χ : Chronicle Atom}
    (h_c0 : χ.c0)
    (ce : C5Counterexample χ)
    :
    ∃ χ' : Chronicle Atom,
      χ.dom ⊆ χ'.dom ∧
      (∀ x ∈ χ.dom, χ'.f x = χ.f x) ∧
      χ'.c0 ∧
      (∃ y ∈ χ'.dom, ce.x < y ∧ ce.η ∈ χ'.f y) ∧
      χ.dom ⊂ χ'.dom ∧
      (∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b) ∧
      (∀ a b, χ'.g a b = χ.g a b) := by
  obtain ⟨y, hy_gt, hy_notin⟩ := exists_rat_gt_finset χ.dom
  have h_mcs_x := h_c0 ce.x ce.x_mem
  obtain ⟨_B, C, h_C_mcs, h_η_C, _, _, _⟩ :=
    lemma_2_4 h_mcs_x ce.ξ ce.η ce.until_mem
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
  · refine ⟨y, Finset.mem_insert_self y χ.dom, hy_gt ce.x ce.x_mem, ?_⟩
    simp only [ite_true]
    exact h_η_C

/--
**Lemma 2.10'** (C5' Counterexample Elimination): Mirror of Lemma 2.10 for Since.
-/
noncomputable def eliminate_C5'_counterexample {χ : Chronicle Atom}
    (h_c0 : χ.c0)
    (ce : C5'Counterexample χ) :
    ∃ χ' : Chronicle Atom,
      χ.dom ⊆ χ'.dom ∧
      (∀ x ∈ χ.dom, χ'.f x = χ.f x) ∧
      χ'.c0 ∧
      (∃ y ∈ χ'.dom, y < ce.x ∧ ce.η ∈ χ'.f y) ∧
      χ.dom ⊂ χ'.dom ∧
      (∀ a b, a ∈ χ.dom → b ∈ χ.dom → χ'.g a b = χ.g a b) ∧
      (∀ a b, χ'.g a b = χ.g a b) := by
  obtain ⟨y, hy_lt, hy_notin⟩ := exists_rat_lt_finset χ.dom
  have h_mcs_x := h_c0 ce.x ce.x_mem
  have h_P_η : Formula.some_past ce.η ∈ χ.f ce.x := by
    have h_ax : DerivationTree FrameClass.Base [] ((Formula.snce ce.η ce.ξ).imp (Formula.some_past ce.η)) :=
      DerivationTree.axiom [] _ (Axiom.since_P ce.ξ ce.η) trivial
    exact temporal_implication_property h_mcs_x
      (theorem_in_mcs' h_mcs_x h_ax) ce.since_mem
  have h_seed := past_temporal_witness_seed_consistent (χ.f ce.x) h_mcs_x ce.η h_P_η
  obtain ⟨C, h_sup, h_C_mcs⟩ := temporal_lindenbaum h_seed
  have h_η_C : ce.η ∈ C := h_sup (Set.mem_union_left _ (Set.mem_singleton _))
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

/-! ## Potential Counterexample Interface -/

/--
The **kind** of a potential counterexample.
-/
inductive PotentialCounterexampleKind : Type where
  | c4_forward    : PotentialCounterexampleKind
  | c4_backward   : PotentialCounterexampleKind
  | c5_forward    : PotentialCounterexampleKind
  | c5_backward   : PotentialCounterexampleKind
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
A **potential counterexample** encodes a tuple (x, y, xi, eta, kind).
-/
structure PotentialCounterexample where
  x : Rat
  y : Rat
  ξ : Formula Atom
  η : Formula Atom
  kind : PotentialCounterexampleKind

/--
Result type for `eliminate_potential_counterexample`.
-/
structure EliminationResult (χ : Chronicle Atom) (pc : PotentialCounterexample) where
  val : Chronicle Atom
  dom_sub : χ.dom ⊆ val.dom
  c0 : val.c0
  f_agrees : ∀ x ∈ χ.dom, val.f x = χ.f x
  g_agrees : ∀ a b, a ∈ χ.dom → b ∈ χ.dom → val.g a b = χ.g a b
  c2' : val.c2'
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
  g_sub_f_insert : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.f w
  g_sub_g_new : ∀ a b, Adjacent χ.dom a b → ∀ w ∈ val.dom, w ∉ χ.dom →
    a < w → w < b → χ.g a b ⊆ val.g a w ∧ χ.g a b ⊆ val.g w b
  dom_new_unique : ∀ u v, u ∈ val.dom → u ∉ χ.dom → v ∈ val.dom → v ∉ χ.dom → u = v
  c5_forward_resolved_no_new : pc.kind = .c5_forward → pc.x ∈ χ.dom →
    Formula.untl pc.η pc.ξ ∈ χ.f pc.x →
    (∃ y ∈ χ.dom, pc.x < y ∧ pc.η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → pc.x ≤ a → b ≤ y → pc.ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, pc.x < w → w < y → pc.ξ ∈ χ.f w)) →
    ∀ u ∈ val.dom, u ∈ χ.dom
  c5_backward_resolved_no_new : pc.kind = .c5_backward → pc.x ∈ χ.dom →
    Formula.snce pc.η pc.ξ ∈ χ.f pc.x →
    (∃ y ∈ χ.dom, y < pc.x ∧ pc.η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → y ≤ a → b ≤ pc.x → pc.ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, y < w → w < pc.x → pc.ξ ∈ χ.f w)) →
    ∀ u ∈ val.dom, u ∈ χ.dom

/-! ## Walk Result Structures -/

/--
Result of the C5 forward recursive walk (Burgess 2.10 induction).
-/
structure C5ForwardWalkResult (χ : Chronicle Atom) (ξ η : Formula Atom) (start : Rat) where
  val : Chronicle Atom
  dom_sub : χ.dom ⊆ val.dom
  c0 : val.c0
  c2' : val.c2'
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
  new_point_after : ∀ w ∈ val.dom, w ∉ χ.dom → start < w
  domain_guard : ∀ w ∈ χ.dom, start < w → w < witness → ξ ∈ val.f w
  witness_not_old : witness ∉ χ.dom

/--
Result of the C5 backward recursive walk (mirror for Since).
-/
structure C5BackwardWalkResult (χ : Chronicle Atom) (ξ η : Formula Atom) (start : Rat) where
  val : Chronicle Atom
  dom_sub : χ.dom ⊆ val.dom
  c0 : val.c0
  c2' : val.c2'
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
  new_point_before : ∀ w ∈ val.dom, w ∉ χ.dom → w < start
  domain_guard : ∀ w ∈ χ.dom, witness < w → w < start → ξ ∈ val.f w
  witness_not_old : witness ∉ χ.dom

/-! ## Recursive Walks -/

set_option maxHeartbeats 3200000 in
private noncomputable def c5_forward_walk
    (χ : Chronicle Atom) (h_c0 : χ.c0) (h_c2' : χ.c2')
    (ξ η : Formula Atom) (pt : Rat)
    (h_start_mem : pt ∈ χ.dom)
    (h_until_start : Formula.untl η ξ ∈ χ.f pt)
    (h_no_wit : ¬∃ y ∈ χ.dom, pt < y ∧ η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → pt ≤ a → b ≤ y → ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, pt < w → w < y → ξ ∈ χ.f w)) :
    C5ForwardWalkResult χ ξ η pt := by
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
    have h_l24 := lemma_2_4_with_guard h_mcs_start ξ η h_until_start
    let B := h_l24.choose
    let C := h_l24.choose_spec.choose
    have h_l24_prop := h_l24.choose_spec.choose_spec
    have h_C_mcs : Temporal.SetMaximalConsistent C := h_l24_prop.1
    have h_η_C : η ∈ C := h_l24_prop.2.1
    have h_ξ_B : ξ ∈ B := h_l24_prop.2.2.2.2
    have h_r3m : BurgessR3Maximal (χ.f pt) B C := h_l24_prop.2.2.2.1
    have h_max_lt_y : max_old < y := hy_gt max_old h_max_mem
    let g' := fun a b =>
      if a = max_old ∧ b = y then B
      else χ.g a b
    let χ' : Chronicle Atom := ⟨fun q => if q = y then C else χ.f q, g', insert y χ.dom⟩
    have h_c2'_new : χ'.c2' := by
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
        show BurgessR3Maximal
          (if max_old = y then C else χ.f max_old)
          (g' max_old y)
          (if y = y then C else χ.f y)
        have hmax_ne_y : max_old ≠ y := ne_of_lt h_max_lt_y
        simp only [hmax_ne_y, ite_false, ite_true, g']
        simp only [and_self, ite_true]
        rw [← h_eq_max]; exact h_r3m
      · have ha_ne : a ≠ y := fun h => hy_notin (h ▸ ha)
        have hb_ne : b ≠ y := fun h => hy_notin (h ▸ hb)
        show BurgessR3Maximal
          (if a = y then C else χ.f a)
          (g' a b)
          (if b = y then C else χ.f b)
        simp only [ha_ne, hb_ne, ite_false, ite_true]
        show BurgessR3Maximal (χ.f a)
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
              show Temporal.SetMaximalConsistent (if q = y then C else χ.f q)
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
    -- Get BurgessR3Maximal facts for (pt, x')
    have h_r3m_adj := h_c2' pt x' h_adj_sx'
    have h_gc_adj := BurgessR3Maximal_g_content_sub h_r3m_adj h_mcs_start h_mcs_x'
    -- Check condition (i): conj ∈ f(x') AND ξ ∈ g(pt, x')
    by_cases h_cond_i : Formula.and ξ (Formula.untl η ξ) ∈ χ.f x' ∧ ξ ∈ χ.g pt x'
    · -- **Condition (i)**: recurse at x'
      have h_untl_x' : Formula.untl η ξ ∈ χ.f x' :=
        conj_right_mcs h_mcs_x' ξ (Formula.untl η ξ) h_cond_i.1
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
              exact conj_left_mcs h_mcs_x' ξ (Formula.untl η ξ) h_cond_i.1⟩⟩
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
      have r := c5_forward_walk χ h_c0 h_c2' ξ η x' hx'_dom h_untl_x' h_no_wit_x'
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
                  exact conj_left_mcs h_mcs_x' ξ (Formula.untl η ξ) h_cond_i.1
              witness_not_old := r.witness_not_old }
    · -- **Not condition (i)**: split at (pt, x')
      have h_split_result : ∃ B' D B'' : Set (Formula Atom),
          BurgessR3Maximal (χ.f pt) B' D ∧
          BurgessR3Maximal D B'' (χ.f x') ∧
          Temporal.SetMaximalConsistent D ∧
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
                rcases temporal_negation_complete h_mcs_x' η with h | h
                · exact absurd h (h_guard_implies_no_event h_xi_g)
                · exact h
              have h2 : (Formula.and ξ (Formula.untl η ξ)).neg ∈ χ.f x' := by
                rcases temporal_negation_complete h_mcs_x'
                  (Formula.and ξ (Formula.untl η ξ)) with h | h
                · exact absurd h h_conj_not_f
                · exact h
              exact temporal_implication_property h_mcs_x'
                (theorem_in_mcs' h_mcs_x'
                  (demorgan_disj_neg_backward η
                    (Formula.and ξ (Formula.untl η ξ))))
                (conj_mcs h_mcs_x' η.neg (Formula.and ξ (Formula.untl η ξ)).neg h1 h2)
            obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
              lemma_2_8 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_until_start h_neg_disj
            exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB' h_xi_g⟩
          · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B'⟩ :=
              lemma_2_7 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_until_start h_xi_g
            exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B'⟩
        · by_cases h_eta_neg_g : η.neg ∈ χ.g pt x'
          · by_cases h_xi_g : ξ ∈ χ.g pt x'
            · by_cases h_conj_g : Formula.and ξ (Formula.untl η ξ) ∈ χ.g pt x'
              · -- conj in g but not-condition(i): conj not in f(x')
                have h_conj_not_f : Formula.and ξ (Formula.untl η ξ) ∉ χ.f x' :=
                  fun h => h_cond_i ⟨h, h_xi_g⟩
                have h_neg_disj : (Formula.or η (Formula.and ξ (Formula.untl η ξ))).neg ∈ χ.f x' := by
                  have h1 : η.neg ∈ χ.f x' := by
                    rcases temporal_negation_complete h_mcs_x' η with h | h
                    · exact absurd h (h_guard_implies_no_event h_xi_g)
                    · exact h
                  have h2 : (Formula.and ξ (Formula.untl η ξ)).neg ∈ χ.f x' := by
                    rcases temporal_negation_complete h_mcs_x'
                      (Formula.and ξ (Formula.untl η ξ)) with h | h
                    · exact absurd h h_conj_not_f
                    · exact h
                  exact temporal_implication_property h_mcs_x'
                    (theorem_in_mcs' h_mcs_x'
                      (demorgan_disj_neg_backward η
                        (Formula.and ξ (Formula.untl η ξ))))
                    (conj_mcs h_mcs_x' η.neg (Formula.and ξ (Formula.untl η ξ)).neg h1 h2)
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
                  lemma_2_8 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_until_start h_neg_disj
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB' h_xi_g⟩
              · have h_bx5 := self_accum_until_mcs h_mcs_start ξ η h_until_start
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, hBB', h_B_sub_D, hBB'', _⟩ :=
                  lemma_2_7 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj
                    (Formula.and ξ (Formula.untl η ξ)) η h_bx5 h_conj_g
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB' h_xi_g⟩
            · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B'⟩ :=
                lemma_2_7 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_until_start h_xi_g
              exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B'⟩
          · by_cases h_xi_g2 : ξ ∈ χ.g pt x'
            · have h_sp := lemma_2_6_splitting h_mcs_start h_mcs_x' h_r3m_adj
                η.neg h_eta_neg_g
              obtain ⟨B', D, B'', hB', hB'', hD_mcs, h_dne_D, h_B_sub_D, hBB', hBB''⟩ := h_sp
              exact ⟨B', D, B'', hB', hB'', hD_mcs,
                temporal_implication_property hD_mcs
                  (theorem_in_mcs' hD_mcs (double_negation η)) h_dne_D,
                h_B_sub_D, hBB', hBB'', hBB' h_xi_g2⟩
            · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B'⟩ :=
                lemma_2_7 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_until_start h_xi_g2
              exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B'⟩
      let B' := h_split_result.choose
      let D := h_split_result.choose_spec.choose
      let B'' := h_split_result.choose_spec.choose_spec.choose
      have h_split_prop := h_split_result.choose_spec.choose_spec.choose_spec
      have h_B'_max : BurgessR3Maximal (χ.f pt) B' D := h_split_prop.1
      have h_B''_max : BurgessR3Maximal D B'' (χ.f x') := h_split_prop.2.1
      have h_D_mcs : Temporal.SetMaximalConsistent D := h_split_prop.2.2.1
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
      have h_c2'_new : val.c2' := by
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
          show BurgessR3Maximal (if a = z then D else χ.f a) (g' a b) (if b = z then D else χ.f b)
          simp only [ha_ne, hb_ne, ite_false, g', and_false, false_and]
          exact h_c2' a b ⟨ha, hb, hab, fun u hu huab => h_no_between u (Finset.mem_insert_of_mem hu) huab⟩
      exact { val := val
              dom_sub := Finset.subset_insert z χ.dom
              c0 := by
                intro q hq; show Temporal.SetMaximalConsistent (if q = z then D else χ.f q)
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
set_option maxHeartbeats 3200000 in
private noncomputable def c5_backward_walk
    (χ : Chronicle Atom) (h_c0 : χ.c0) (h_c2' : χ.c2')
    (ξ η : Formula Atom) (pt : Rat)
    (h_start_mem : pt ∈ χ.dom)
    (h_since_start : Formula.snce η ξ ∈ χ.f pt)
    (h_no_wit : ¬∃ y ∈ χ.dom, y < pt ∧ η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → y ≤ a → b ≤ pt → ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, y < w → w < pt → ξ ∈ χ.f w)) :
    C5BackwardWalkResult χ ξ η pt := by
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
    have h_l24s := lemma_2_4_since_with_guard h_mcs_start ξ η h_since_start
    let B := h_l24s.choose
    let C := h_l24s.choose_spec.choose
    have h_l24s_prop := h_l24s.choose_spec.choose_spec
    have h_C_mcs : Temporal.SetMaximalConsistent C := h_l24s_prop.1
    have h_η_C : η ∈ C := h_l24s_prop.2.1
    have h_ξ_B : ξ ∈ B := h_l24s_prop.2.2.2
    have h_r3m : BurgessR3Maximal C B (χ.f pt) := h_l24s_prop.2.2.1
    have h_min_lt_y : y < min_old := hy_lt min_old h_min_mem
    let g' := fun a b =>
      if a = y ∧ b = min_old then B
      else χ.g a b
    let χ' : Chronicle Atom := ⟨fun q => if q = y then C else χ.f q, g', insert y χ.dom⟩
    have h_c2'_new : χ'.c2' := by
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
        show BurgessR3Maximal
          (if y = y then C else χ.f y)
          (g' y min_old)
          (if min_old = y then C else χ.f min_old)
        have hmin_ne_y : min_old ≠ y := ne_of_gt h_min_lt_y
        simp only [ite_true, hmin_ne_y, ite_false, g', and_self]
        rw [← h_eq_min]; exact h_r3m
      · exact absurd hab (not_lt.mpr (le_of_lt (hy_lt a ha)))
      · have ha_ne : a ≠ y := fun h => hy_notin (h ▸ ha)
        have hb_ne : b ≠ y := fun h => hy_notin (h ▸ hb)
        show BurgessR3Maximal
          (if a = y then C else χ.f a)
          (g' a b)
          (if b = y then C else χ.f b)
        simp only [ha_ne, hb_ne, ite_false, g', false_and, ite_false]
        exact h_c2' a b ⟨ha, hb, hab, fun u hu huab => h_no_between u (Finset.mem_insert_of_mem hu) huab⟩
    exact { val := χ'
            dom_sub := Finset.subset_insert y χ.dom
            c0 := by
              intro q hq
              show Temporal.SetMaximalConsistent (if q = y then C else χ.f q)
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
    -- Get BurgessR3Maximal facts for (x'', pt)
    have h_r3m_adj := h_c2' x'' pt h_adj_x''s
    have h_gc_adj := BurgessR3Maximal_g_content_sub h_r3m_adj h_mcs_x'' h_mcs_start
    -- Check condition (i): conj ∈ f(x'') AND ξ ∈ g(x'', pt)
    by_cases h_cond_i : Formula.and ξ (Formula.snce η ξ) ∈ χ.f x'' ∧ ξ ∈ χ.g x'' pt
    · -- **Condition (i)**: recurse at x''
      have h_snce_x'' : Formula.snce η ξ ∈ χ.f x'' :=
        conj_right_mcs h_mcs_x'' ξ (Formula.snce η ξ) h_cond_i.1
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
              exact conj_left_mcs h_mcs_x'' ξ (Formula.snce η ξ) h_cond_i.1⟩⟩
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
      have r := c5_backward_walk χ h_c0 h_c2' ξ η x'' hx''_dom h_snce_x'' h_no_wit_x''
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
                  exact conj_left_mcs h_mcs_x'' ξ (Formula.snce η ξ) h_cond_i.1
              witness_not_old := r.witness_not_old }
    · -- **Not condition (i)**: split at (x'', pt)
      have h_split_result : ∃ B' D B'' : Set (Formula Atom),
          BurgessR3Maximal (χ.f x'') B' D ∧
          BurgessR3Maximal D B'' (χ.f pt) ∧
          Temporal.SetMaximalConsistent D ∧
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
                rcases temporal_negation_complete h_mcs_x'' η with h | h
                · exact absurd h (h_guard_implies_no_event h_xi_g)
                · exact h
              have h2 : (Formula.and ξ (Formula.snce η ξ)).neg ∈ χ.f x'' := by
                rcases temporal_negation_complete h_mcs_x''
                  (Formula.and ξ (Formula.snce η ξ)) with h | h
                · exact absurd h h_conj_not_f
                · exact h
              exact temporal_implication_property h_mcs_x''
                (theorem_in_mcs' h_mcs_x''
                  (demorgan_disj_neg_backward η
                    (Formula.and ξ (Formula.snce η ξ))))
                (conj_mcs h_mcs_x'' η.neg (Formula.and ξ (Formula.snce η ξ)).neg h1 h2)
            obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
              lemma_2_8_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_since_start h_neg_disj
            exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB'' h_xi_g⟩
          · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B''⟩ :=
              lemma_2_7_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_since_start h_xi_g
            exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B''⟩
        · by_cases h_eta_neg_g : η.neg ∈ χ.g x'' pt
          · by_cases h_xi_g : ξ ∈ χ.g x'' pt
            · by_cases h_conj_g : Formula.and ξ (Formula.snce η ξ) ∈ χ.g x'' pt
              · -- conj in g but not-condition(i): conj not in f(x'')
                have h_conj_not_f : Formula.and ξ (Formula.snce η ξ) ∉ χ.f x'' :=
                  fun h => h_cond_i ⟨h, h_xi_g⟩
                have h_neg_disj : (Formula.or η (Formula.and ξ (Formula.snce η ξ))).neg ∈ χ.f x'' := by
                  have h1 : η.neg ∈ χ.f x'' := by
                    rcases temporal_negation_complete h_mcs_x'' η with h | h
                    · exact absurd h (h_guard_implies_no_event h_xi_g)
                    · exact h
                  have h2 : (Formula.and ξ (Formula.snce η ξ)).neg ∈ χ.f x'' := by
                    rcases temporal_negation_complete h_mcs_x''
                      (Formula.and ξ (Formula.snce η ξ)) with h | h
                    · exact absurd h h_conj_not_f
                    · exact h
                  exact temporal_implication_property h_mcs_x''
                    (theorem_in_mcs' h_mcs_x''
                      (demorgan_disj_neg_backward η
                        (Formula.and ξ (Formula.snce η ξ))))
                    (conj_mcs h_mcs_x'' η.neg (Formula.and ξ (Formula.snce η ξ)).neg h1 h2)
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
                  lemma_2_8_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_since_start h_neg_disj
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB'' h_xi_g⟩
              · have h_bx5 := self_accum_since_mcs h_mcs_start ξ η h_since_start
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, hBB', h_B_sub_D, hBB'', _⟩ :=
                  lemma_2_7_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj
                    (Formula.and ξ (Formula.snce η ξ)) η h_bx5 h_conj_g
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB'' h_xi_g⟩
            · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B''⟩ :=
                lemma_2_7_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_since_start h_xi_g
              exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B''⟩
          · by_cases h_xi_g2 : ξ ∈ χ.g x'' pt
            · have h_sp := lemma_2_6_splitting h_mcs_x'' h_mcs_start h_r3m_adj
                η.neg h_eta_neg_g
              obtain ⟨B', D, B'', hB', hB'', hD_mcs, h_dne_D, h_B_sub_D, hBB', hBB''⟩ := h_sp
              exact ⟨B', D, B'', hB', hB'', hD_mcs,
                temporal_implication_property hD_mcs
                  (theorem_in_mcs' hD_mcs (double_negation η)) h_dne_D,
                h_B_sub_D, hBB', hBB'', hBB'' h_xi_g2⟩
            · obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, hBB', h_B_sub_D, hBB'', h_xi_B''⟩ :=
                lemma_2_7_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η h_since_start h_xi_g2
              exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', h_xi_B''⟩
      let B' := h_split_result.choose
      let D := h_split_result.choose_spec.choose
      let B'' := h_split_result.choose_spec.choose_spec.choose
      have h_split_prop := h_split_result.choose_spec.choose_spec.choose_spec
      have h_B'_max : BurgessR3Maximal (χ.f x'') B' D := h_split_prop.1
      have h_B''_max : BurgessR3Maximal D B'' (χ.f pt) := h_split_prop.2.1
      have h_D_mcs : Temporal.SetMaximalConsistent D := h_split_prop.2.2.1
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
      have h_c2'_new : val.c2' := by
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
          show BurgessR3Maximal (if z = z then D else χ.f z) (g' z b) (if b = z then D else χ.f b)
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
          show BurgessR3Maximal (if a = z then D else χ.f a) (g' a b) (if b = z then D else χ.f b)
          simp only [ha_ne, hb_ne, ite_false, g', and_false, false_and]
          exact h_c2' a b ⟨ha, hb, hab, fun u hu huab => h_no_between u (Finset.mem_insert_of_mem hu) huab⟩
      exact { val := val
              dom_sub := Finset.subset_insert z χ.dom
              c0 := by
                intro q hq; show Temporal.SetMaximalConsistent (if q = z then D else χ.f q)
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


end Cslib.Logic.Temporal.Metalogic.Chronicle
