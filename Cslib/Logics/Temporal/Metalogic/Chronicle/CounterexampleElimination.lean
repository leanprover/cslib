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

end Cslib.Logic.Temporal.Metalogic.Chronicle
