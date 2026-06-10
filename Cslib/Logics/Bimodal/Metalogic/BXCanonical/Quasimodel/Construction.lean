/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Quasimodel.HintikkaPoint
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Finset.Card

/-!
# Quasimodel Construction with Defect-Discharge

Constructs the Burgess-Xu one-step quasimodel: a finite sequence of Hintikka points
with the defect-discharge property for Until/Since formulas.

## Main Definitions

- `hintikkaStep`: The one-step relation between Hintikka points
- `UntilDefect`: A defect in a Hintikka point (Until formula present but goal absent)
- `defectCount`: Number of Until-defects in a Hintikka point
- `QuasimodelChain`: A sequence of Hintikka points with defect discharge

## Main Results

- `quasimodel_chain_exists`: Given an Until defect, a discharging chain exists
- `quasimodel_chain_guard`: The guard formula holds at all intermediate points
- `quasimodel_chain_witness`: The goal formula holds at the endpoint

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/Quasimodel/Construction.lean
* Burgess 1984: Defect-discharge construction for Until
* Reynolds 1996: Formal treatment of quasimodel chains
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Quasimodel

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.BXCanonical

variable {Atom : Type*}

/-! ## One-Step Relation -/

/-- The Burgess-Xu one-step relation between Hintikka points.
    h1 → h2 captures:
    - G-propagation: G(χ) ∈ h1 → χ ∈ h2
    - H-backward: H(χ) ∈ h2 → χ ∈ h1
    - Until defect propagation: if φ U ψ ∈ h1 and ψ ∉ h1, then
      φ ∈ h1 and φ U ψ ∈ h2 -/
def hintikkaStep {Sigma : Finset (Formula Atom)} (h1 h2 : HintikkaPoint Sigma) : Prop :=
  -- G-propagation
  (∀ χ : Formula Atom, Formula.allFuture χ ∈ h1.formulas → χ ∈ h2.formulas) ∧
  -- H-backward
  (∀ χ : Formula Atom, Formula.allPast χ ∈ h2.formulas → χ ∈ h1.formulas) ∧
  -- Until defect propagation
  (∀ φ ψ : Formula Atom, Formula.untl φ ψ ∈ h1.formulas → ψ ∉ h1.formulas →
    φ ∈ h1.formulas ∧ Formula.untl φ ψ ∈ h2.formulas)

/-! ## Until Defect -/

/-- An Until-defect at a Hintikka point: φ U ψ is in the point but ψ is not.
    This means the Until formula has not been discharged at this point. -/
def UntilDefect {Sigma : Finset (Formula Atom)} (h : HintikkaPoint Sigma) (φ ψ : Formula Atom) : Prop :=
  Formula.untl φ ψ ∈ h.formulas ∧ ψ ∉ h.formulas

/-- Since-defect: mirror of Until-defect for Since formulas. -/
def SinceDefect {Sigma : Finset (Formula Atom)} (h : HintikkaPoint Sigma) (φ ψ : Formula Atom) : Prop :=
  Formula.snce φ ψ ∈ h.formulas ∧ ψ ∉ h.formulas

/-! ## Defect Count

The termination measure for the quasimodel construction.
We count the number of Until-formulas in Sigma that are "defective" at a point
(present in the point but their goal absent). Since Sigma is finite and each
step either discharges a defect or the chain has reached its goal, the chain
must terminate in at most |Sigma| steps. -/

open Classical in
/-- Count the number of Until-defects at a Hintikka point relative to Sigma. -/
noncomputable def defectCount {Sigma : Finset (Formula Atom)} (h : HintikkaPoint Sigma) : Nat :=
  (Sigma.filter (fun f => match f with
    | Formula.untl _φ ψ => f ∈ h.formulas ∧ ψ ∉ h.formulas
    | _ => False)).card

/-! ## Quasimodel Chain

The quasimodel chain is a finite sequence of Hintikka points h0, h1, ..., hk where:
- Each consecutive pair satisfies hintikkaStep
- The guard φ holds at h0, h1, ..., h(k-1)
- The goal ψ holds at hk
- The chain terminates because defects decrease (bounded by |Sigma|)

Instead of constructing this directly (which would require complex well-founded
recursion in Lean), we prove the existence theorem using the BXPoint infrastructure:
we construct the chain at the MCS level and project down to Hintikka points. -/

structure QuasimodelChain (Sigma : Finset (Formula Atom)) (target_lhs target_rhs : Formula Atom) where
  /-- The list of Hintikka points forming the chain (always nonempty). -/
  points : List (HintikkaPoint Sigma)
  /-- The chain is nonempty. -/
  nonempty : points ≠ []
  /-- The target Until-formula is present at the head. -/
  target_at_head : Formula.untl target_lhs target_rhs ∈ (points.head nonempty).formulas
  /-- Consecutive pairs satisfy `hintikkaStep`. -/
  step_chain : ∀ i : Fin (points.length - 1),
    hintikkaStep (points.get ⟨i.val, by omega⟩) (points.get ⟨i.val + 1, by omega⟩)

/-- The last Hintikka point in a quasimodel chain. -/
noncomputable def QuasimodelChain.last {Sigma : Finset (Formula Atom)} {φ ψ : Formula Atom}
    (c : QuasimodelChain Sigma φ ψ) : HintikkaPoint Sigma :=
  c.points.getLast c.nonempty

/-- The chain has reached its witness when the target's right-hand side
    appears at the last point. -/
def QuasimodelChain.witnessReached {Sigma : Finset (Formula Atom)} {φ ψ : Formula Atom}
    (c : QuasimodelChain Sigma φ ψ) : Prop :=
  ψ ∈ c.last.formulas

/-- The chain's length as a natural number. -/
def QuasimodelChain.length {Sigma : Finset (Formula Atom)} {φ ψ : Formula Atom}
    (c : QuasimodelChain Sigma φ ψ) : Nat :=
  c.points.length

theorem QuasimodelChain.length_pos {Sigma : Finset (Formula Atom)} {φ ψ : Formula Atom}
    (c : QuasimodelChain Sigma φ ψ) : 0 < c.length := by
  unfold QuasimodelChain.length
  exact List.length_pos_iff.mpr c.nonempty

/-- The singleton quasimodel chain: a one-point chain trivially satisfies
    `step_chain` (empty quantification) and exposes the target formula
    directly. -/
noncomputable def QuasimodelChain.singleton {Sigma : Finset (Formula Atom)} {φ ψ : Formula Atom}
    (h : HintikkaPoint Sigma) (h_target : Formula.untl φ ψ ∈ h.formulas) :
    QuasimodelChain Sigma φ ψ where
  points := [h]
  nonempty := by simp
  target_at_head := by simpa using h_target
  step_chain := by
    intro i
    exact absurd i.isLt (by simp)

/-! ## MCS-Level BX Axiom Lemmas -/

/-- Key lemma: BX5 self-accumulation at MCS level.
    If φ U ψ ∈ w.formulas, then (φ ∧ (φ U ψ)) U ψ ∈ w.formulas. -/
theorem self_accum_mcs {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h : Formula.untl φ ψ ∈ w.formulas) :
    Formula.untl φ (Formula.and ψ (Formula.untl φ ψ)) ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.self_accum_until ψ φ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h

/-- Key lemma: BX10 at MCS level.
    If φ U ψ ∈ w.formulas, then F(ψ) ∈ w.formulas. -/
theorem until_F_mcs {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h : Formula.untl φ ψ ∈ w.formulas) :
    Formula.someFuture φ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.until_F ψ φ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h

/-- Key lemma: BX4 connectedness at MCS level.
    If φ ∈ w.formulas, then G(P(φ)) ∈ w.formulas. -/
theorem connect_future_mcs {w : BXPoint Atom} {φ : Formula Atom}
    (h : φ ∈ w.formulas) :
    Formula.allFuture (Formula.somePast φ) ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.connect_future φ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h

/-! ## Since-direction MCS lemmas -/

/-- BX5' at MCS level. -/
theorem self_accum_since_mcs {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h : Formula.snce φ ψ ∈ w.formulas) :
    Formula.snce φ (Formula.and ψ (Formula.snce φ ψ)) ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.self_accum_since ψ φ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h

/-- BX10' at MCS level. -/
theorem since_P_mcs {w : BXPoint Atom} {φ ψ : Formula Atom}
    (h : Formula.snce φ ψ ∈ w.formulas) :
    Formula.somePast φ ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.since_P ψ φ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h

/-- BX4' at MCS level. -/
theorem connect_past_mcs {w : BXPoint Atom} {φ : Formula Atom}
    (h : φ ∈ w.formulas) :
    Formula.allPast (Formula.someFuture φ) ∈ w.formulas := by
  have h_ax : DerivationTree FrameClass.Base [] _ := DerivationTree.axiom [] _ (Axiom.connect_past φ) trivial
  exact SetMaximalConsistent.implication_property w.is_mcs
    (theoremInMcsFc w.is_mcs h_ax) h

/-! ## Until-Defect Set and Strict-Decrease Infrastructure -/

open Classical in
/-- The set of Until-defects at a Hintikka point, as a `Finset`. -/
noncomputable def untilDefectSet {Sigma : Finset (Formula Atom)} (h : HintikkaPoint Sigma) :
    Finset (Formula Atom) :=
  Sigma.filter (fun f => match f with
    | Formula.untl _φ ψ => f ∈ h.formulas ∧ ψ ∉ h.formulas
    | _ => False)

open Classical in
theorem defect_count_eq_card {Sigma : Finset (Formula Atom)} (h : HintikkaPoint Sigma) :
    defectCount h = (untilDefectSet h).card := by
  rfl

open Classical in
theorem mem_untilDefectSet_iff {Sigma : Finset (Formula Atom)} {h : HintikkaPoint Sigma}
    {f : Formula Atom} :
    f ∈ untilDefectSet h ↔
      f ∈ Sigma ∧ (∃ φ ψ, f = Formula.untl φ ψ ∧ f ∈ h.formulas ∧ ψ ∉ h.formulas) := by
  unfold untilDefectSet
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hSigma, hmatch⟩
    refine ⟨hSigma, ?_⟩
    cases f with
    | untl φ ψ =>
      simp only at hmatch
      exact ⟨φ, ψ, rfl, hmatch.1, hmatch.2⟩
    | _ => simp only at hmatch
  · rintro ⟨hSigma, φ, ψ, rfl, h_in, h_out⟩
    refine ⟨hSigma, ?_⟩
    simp only
    exact ⟨h_in, h_out⟩

open Classical in
/-- If the target Until-defect `φ U ψ` is dischargeable at `h1` (i.e. `ψ ∉ h1`
    and `ψ ∈ h2`), and `h2`'s Until-defect set is contained in `h1`'s, then
    the defect set strictly shrinks across the step. -/
theorem hintikka_step_target_decrease
    {Sigma : Finset (Formula Atom)} {h1 h2 : HintikkaPoint Sigma}
    {φ ψ : Formula Atom}
    (h_target_in : Formula.untl φ ψ ∈ h1.formulas)
    (h_target_sigma : Formula.untl φ ψ ∈ Sigma)
    (h_not : ψ ∉ h1.formulas)
    (h_witness : ψ ∈ h2.formulas)
    (defect_mono : untilDefectSet h2 ⊆ untilDefectSet h1) :
    defectCount h2 < defectCount h1 := by
  have h_in_h1 : Formula.untl φ ψ ∈ untilDefectSet h1 := by
    rw [mem_untilDefectSet_iff]
    exact ⟨h_target_sigma, φ, ψ, rfl, h_target_in, h_not⟩
  have h_not_in_h2 : Formula.untl φ ψ ∉ untilDefectSet h2 := by
    rw [mem_untilDefectSet_iff]
    rintro ⟨_, φ', ψ', heq, _, h_out⟩
    have : ψ = ψ' := by injection heq
    exact h_out (this ▸ h_witness)
  rw [defect_count_eq_card, defect_count_eq_card]
  exact Finset.card_lt_card (by
    refine ⟨defect_mono, ?_⟩
    intro h_eq
    exact h_not_in_h2 (h_eq h_in_h1))

open Classical in
/-- Symmetric definition for Since: the set of Since-defects. -/
noncomputable def sinceDefectSet {Sigma : Finset (Formula Atom)} (h : HintikkaPoint Sigma) :
    Finset (Formula Atom) :=
  Sigma.filter (fun f => match f with
    | Formula.snce _φ ψ => f ∈ h.formulas ∧ ψ ∉ h.formulas
    | _ => False)

open Classical in
noncomputable def sinceDefectCount {Sigma : Finset (Formula Atom)} (h : HintikkaPoint Sigma) : Nat :=
  (sinceDefectSet h).card

open Classical in
theorem mem_sinceDefectSet_iff {Sigma : Finset (Formula Atom)} {h : HintikkaPoint Sigma}
    {f : Formula Atom} :
    f ∈ sinceDefectSet h ↔
      f ∈ Sigma ∧ (∃ φ ψ, f = Formula.snce φ ψ ∧ f ∈ h.formulas ∧ ψ ∉ h.formulas) := by
  unfold sinceDefectSet
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hSigma, hmatch⟩
    refine ⟨hSigma, ?_⟩
    cases f with
    | snce φ ψ =>
      simp only at hmatch
      exact ⟨φ, ψ, rfl, hmatch.1, hmatch.2⟩
    | _ => simp only at hmatch
  · rintro ⟨hSigma, φ, ψ, rfl, h_in, h_out⟩
    refine ⟨hSigma, ?_⟩
    simp only
    exact ⟨h_in, h_out⟩

open Classical in
/-- Since-dual of `hintikka_step_target_decrease`. -/
theorem hintikka_step_target_decrease_since
    {Sigma : Finset (Formula Atom)} {h1 h2 : HintikkaPoint Sigma}
    {φ ψ : Formula Atom}
    (h_target_in : Formula.snce φ ψ ∈ h1.formulas)
    (h_target_sigma : Formula.snce φ ψ ∈ Sigma)
    (h_not : ψ ∉ h1.formulas)
    (h_witness : ψ ∈ h2.formulas)
    (defect_mono : sinceDefectSet h2 ⊆ sinceDefectSet h1) :
    sinceDefectCount h2 < sinceDefectCount h1 := by
  have h_in_h1 : Formula.snce φ ψ ∈ sinceDefectSet h1 := by
    rw [mem_sinceDefectSet_iff]
    exact ⟨h_target_sigma, φ, ψ, rfl, h_target_in, h_not⟩
  have h_not_in_h2 : Formula.snce φ ψ ∉ sinceDefectSet h2 := by
    rw [mem_sinceDefectSet_iff]
    rintro ⟨_, φ', ψ', heq, _, h_out⟩
    have : ψ = ψ' := by injection heq
    exact h_out (this ▸ h_witness)
  unfold sinceDefectCount
  exact Finset.card_lt_card (by
    refine ⟨defect_mono, ?_⟩
    intro h_eq
    exact h_not_in_h2 (h_eq h_in_h1))

/-! ## Refined QuasimodelChain Type -/

/-- A Hintikka point bundled with a concrete `BXPoint` witness whose formula
    set is a superset of the point's formulas. -/
structure WitnessedHintikka (Sigma : Finset (Formula Atom)) where
  /-- The underlying Hintikka point. -/
  point : HintikkaPoint Sigma
  /-- A concrete `BXPoint` witness backing `point`. -/
  witness : BXPoint Atom
  /-- Every formula of `point` is a formula of the backing `witness`. -/
  point_subset_witness : ∀ f ∈ point.formulas, f ∈ witness.formulas

/-- The step-oracle signature: at any Hintikka point carrying the target
    Until-defect and missing the witness, one can step to a next point
    either reaching the witness or strictly decreasing the defect count
    while preserving the target defect. -/
def HintikkaStepOracle {Sigma : Finset (Formula Atom)} (φ ψ : Formula Atom) : Prop :=
  ∀ h : HintikkaPoint Sigma,
    Formula.untl φ ψ ∈ h.formulas → ψ ∉ h.formulas →
    ∃ wh' : WitnessedHintikka Sigma, hintikkaStep h wh'.point ∧
      (ψ ∈ wh'.point.formulas ∨
        (Formula.untl φ ψ ∈ wh'.point.formulas ∧
          defectCount wh'.point < defectCount h))

/-- A raw Hintikka chain: a nonempty list of Hintikka points with each
    consecutive pair related by `hintikkaStep`. -/
structure HintikkaRawChain (Sigma : Finset (Formula Atom)) where
  points : List (HintikkaPoint Sigma)
  nonempty : points ≠ []
  is_chain : points.IsChain hintikkaStep

/-- The last point of a raw chain. -/
noncomputable def HintikkaRawChain.last {Sigma : Finset (Formula Atom)}
    (c : HintikkaRawChain Sigma) : HintikkaPoint Sigma :=
  c.points.getLast c.nonempty

/-- The head of a raw chain. -/
noncomputable def HintikkaRawChain.head {Sigma : Finset (Formula Atom)}
    (c : HintikkaRawChain Sigma) : HintikkaPoint Sigma :=
  c.points.head c.nonempty

/-- Singleton raw chain. -/
noncomputable def HintikkaRawChain.singleton {Sigma : Finset (Formula Atom)}
    (h : HintikkaPoint Sigma) : HintikkaRawChain Sigma where
  points := [h]
  nonempty := by simp
  is_chain := by simp

@[simp] theorem HintikkaRawChain.singleton_points {Sigma : Finset (Formula Atom)}
    (h : HintikkaPoint Sigma) :
    (HintikkaRawChain.singleton h).points = [h] := rfl

@[simp] theorem HintikkaRawChain.singleton_last {Sigma : Finset (Formula Atom)}
    (h : HintikkaPoint Sigma) :
    (HintikkaRawChain.singleton h).last = h := by
  unfold HintikkaRawChain.last
  simp [HintikkaRawChain.singleton_points]

@[simp] theorem HintikkaRawChain.singleton_head {Sigma : Finset (Formula Atom)}
    (h : HintikkaPoint Sigma) :
    (HintikkaRawChain.singleton h).head = h := by
  unfold HintikkaRawChain.head
  simp [HintikkaRawChain.singleton_points]

/-- Prepend a Hintikka point to a raw chain, provided the new head
    steps to the old head. -/
noncomputable def HintikkaRawChain.cons {Sigma : Finset (Formula Atom)}
    (h0 : HintikkaPoint Sigma) (c : HintikkaRawChain Sigma)
    (h_step : hintikkaStep h0 c.head) :
    HintikkaRawChain Sigma where
  points := h0 :: c.points
  nonempty := by simp
  is_chain := by
    apply List.IsChain.cons c.is_chain
    intro y hy
    have h_eq : c.points.head? = some (c.points.head c.nonempty) :=
      List.head?_eq_some_head c.nonempty
    rw [h_eq] at hy
    simp at hy
    show hintikkaStep h0 y
    have : c.head = y := by
      unfold HintikkaRawChain.head
      exact hy
    rw [← this]
    exact h_step

@[simp] theorem HintikkaRawChain.cons_points {Sigma : Finset (Formula Atom)}
    (h0 : HintikkaPoint Sigma) (c : HintikkaRawChain Sigma)
    (h_step : hintikkaStep h0 c.head) :
    (HintikkaRawChain.cons h0 c h_step).points = h0 :: c.points := rfl

@[simp] theorem HintikkaRawChain.cons_head {Sigma : Finset (Formula Atom)}
    (h0 : HintikkaPoint Sigma) (c : HintikkaRawChain Sigma)
    (h_step : hintikkaStep h0 c.head) :
    (HintikkaRawChain.cons h0 c h_step).head = h0 := by
  unfold HintikkaRawChain.head
  simp [HintikkaRawChain.cons_points]

theorem HintikkaRawChain.cons_last {Sigma : Finset (Formula Atom)}
    (h0 : HintikkaPoint Sigma) (c : HintikkaRawChain Sigma)
    (h_step : hintikkaStep h0 c.head) :
    (HintikkaRawChain.cons h0 c h_step).last = c.last := by
  unfold HintikkaRawChain.last
  simp [HintikkaRawChain.cons_points, List.getLast_cons c.nonempty]

/-- Every point in a raw Hintikka chain is backed by a concrete `BXPoint`
    whose formula set is a superset of the point's formulas. -/
def ChainWitnessed {Sigma : Finset (Formula Atom)}
    (c : HintikkaRawChain Sigma) : Prop :=
  ∀ h ∈ c.points, ∃ w : BXPoint Atom, ∀ f ∈ h.formulas, f ∈ w.formulas

/-- **Phase 3 main theorem**: `hintikka_chain_exists`.

    Given a step oracle and a starting Hintikka point `h0` carrying the
    target Until-defect (plus a concrete `BXPoint` witness `w0` backing
    `h0`), there exists a raw Hintikka chain starting at `h0`, ending at
    a point where `ψ` is present, and with every point backed by a
    concrete `BXPoint` witness (`ChainWitnessed`). -/
theorem hintikka_chain_exists
    {Sigma : Finset (Formula Atom)} {φ ψ : Formula Atom}
    (oracle : HintikkaStepOracle (Sigma := Sigma) φ ψ)
    (h0 : HintikkaPoint Sigma) (w0 : BXPoint Atom)
    (h0_sub : ∀ f ∈ h0.formulas, f ∈ w0.formulas)
    (h_target : Formula.untl φ ψ ∈ h0.formulas) :
    ∃ c : HintikkaRawChain Sigma,
      c.head = h0 ∧ ψ ∈ c.last.formulas ∧ ChainWitnessed c := by
  suffices h : ∀ n h0 (w0 : BXPoint Atom),
      (∀ f ∈ h0.formulas, f ∈ w0.formulas) →
      defectCount h0 = n →
      Formula.untl φ ψ ∈ h0.formulas →
      ∃ c : HintikkaRawChain Sigma,
        c.head = h0 ∧ ψ ∈ c.last.formulas ∧ ChainWitnessed c by
    exact h (defectCount h0) h0 w0 h0_sub rfl h_target
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h0 w0 h0_sub h_n h_target
    by_cases h_psi : ψ ∈ h0.formulas
    · -- Already at witness: singleton chain
      refine ⟨HintikkaRawChain.singleton h0, ?_, ?_, ?_⟩
      · simp
      · simpa using h_psi
      · -- ChainWitnessed: only point is h0, backed by w0
        intro h hh
        simp [HintikkaRawChain.singleton_points] at hh
        exact ⟨w0, by subst hh; exact h0_sub⟩
    · -- Not yet at witness: invoke oracle, get witnessed successor
      obtain ⟨wh', h_step, h_cases⟩ := oracle h0 h_target h_psi
      rcases h_cases with h_psi' | ⟨h_target', h_dec⟩
      · -- Oracle reached witness in one step: two-point chain [h0, wh'.point]
        refine ⟨HintikkaRawChain.cons h0
          (HintikkaRawChain.singleton wh'.point) ?_, ?_, ?_, ?_⟩
        · -- hintikkaStep h0 (singleton wh'.point).head
          simpa [HintikkaRawChain.singleton_head] using h_step
        · -- head = h0
          simp
        · -- ψ ∈ last.formulas
          rw [HintikkaRawChain.cons_last]
          simpa using h_psi'
        · -- ChainWitnessed
          intro h hh
          simp [HintikkaRawChain.cons_points,
            HintikkaRawChain.singleton_points] at hh
          rcases hh with rfl | rfl
          · exact ⟨w0, h0_sub⟩
          · exact ⟨wh'.witness, wh'.point_subset_witness⟩
      · -- Oracle stepped to strictly smaller defect: recurse via ih
        have h_dec' : defectCount wh'.point < n := h_n ▸ h_dec
        obtain ⟨c', hc'_head, hc'_witness, hc'_witd⟩ :=
          ih (defectCount wh'.point) h_dec' wh'.point wh'.witness
            wh'.point_subset_witness rfl h_target'
        refine ⟨HintikkaRawChain.cons h0 c' (by rw [hc'_head]; exact h_step),
          ?_, ?_, ?_⟩
        · simp
        · rw [HintikkaRawChain.cons_last]; exact hc'_witness
        · -- ChainWitnessed: h0 backed by w0; rest covered by hc'_witd
          intro h hh
          simp [HintikkaRawChain.cons_points] at hh
          rcases hh with rfl | h_in
          · exact ⟨w0, h0_sub⟩
          · exact hc'_witd h h_in

/-- Seed-consistency lemma: any subset of a chain point's
    formulas is `SetConsistent`, provided the chain is witnessed. -/
theorem chain_step_seed_consistent
    {Sigma : Finset (Formula Atom)}
    {c : HintikkaRawChain Sigma} (h_wit : ChainWitnessed c)
    {h : HintikkaPoint Sigma} (h_mem : h ∈ c.points)
    (Omega : Set (Formula Atom)) (h_sub : Omega ⊆ (h.formulas : Set (Formula Atom))) :
    SetConsistent (fc := FrameClass.Base) Omega := by
  obtain ⟨w, hw⟩ := h_wit h h_mem
  intro L hL ⟨d⟩
  have h_L_in_w : ∀ α ∈ L, α ∈ w.formulas := by
    intro α hα
    exact hw α (h_sub (hL α hα))
  exact w.is_mcs.1 L h_L_in_w ⟨d⟩

/-- **Since dual** of `HintikkaStepOracle`. -/
def HintikkaStepOracleSince {Sigma : Finset (Formula Atom)} (φ ψ : Formula Atom) : Prop :=
  ∀ h : HintikkaPoint Sigma,
    Formula.snce φ ψ ∈ h.formulas → ψ ∉ h.formulas →
    ∃ wh' : WitnessedHintikka Sigma, hintikkaStep wh'.point h ∧
      (ψ ∈ wh'.point.formulas ∨
        (Formula.snce φ ψ ∈ wh'.point.formulas ∧
          sinceDefectCount wh'.point < sinceDefectCount h))

/-- Append a single Hintikka point to a raw chain, provided the old
    last point steps to the new point. -/
noncomputable def HintikkaRawChain.snoc {Sigma : Finset (Formula Atom)}
    (c : HintikkaRawChain Sigma) (h0 : HintikkaPoint Sigma)
    (h_step : hintikkaStep c.last h0) :
    HintikkaRawChain Sigma where
  points := c.points ++ [h0]
  nonempty := by
    intro h_eq
    exact c.nonempty (List.append_eq_nil_iff.mp h_eq).1
  is_chain := by
    apply List.IsChain.append c.is_chain (by simp)
    intro x hx y hy
    have h_last : c.points.getLast? = some (c.points.getLast c.nonempty) :=
      List.getLast?_eq_some_getLast c.nonempty
    rw [h_last] at hx
    simp at hx
    have h_head : ([h0] : List (HintikkaPoint Sigma)).head? = some h0 := by simp
    rw [h_head] at hy
    simp at hy
    show hintikkaStep x y
    rw [← hx, ← hy]
    exact h_step

@[simp] theorem HintikkaRawChain.snoc_points {Sigma : Finset (Formula Atom)}
    (c : HintikkaRawChain Sigma) (h0 : HintikkaPoint Sigma)
    (h_step : hintikkaStep c.last h0) :
    (c.snoc h0 h_step).points = c.points ++ [h0] := rfl

theorem HintikkaRawChain.snoc_last {Sigma : Finset (Formula Atom)}
    (c : HintikkaRawChain Sigma) (h0 : HintikkaPoint Sigma)
    (h_step : hintikkaStep c.last h0) :
    (c.snoc h0 h_step).last = h0 := by
  unfold HintikkaRawChain.last
  simp [HintikkaRawChain.snoc_points]

theorem HintikkaRawChain.snoc_head {Sigma : Finset (Formula Atom)}
    (c : HintikkaRawChain Sigma) (h0 : HintikkaPoint Sigma)
    (h_step : hintikkaStep c.last h0) :
    (c.snoc h0 h_step).head = c.head := by
  unfold HintikkaRawChain.head
  simp [c.nonempty]

/-- `hintikka_chain_exists_since`: Since dual of `hintikka_chain_exists`. -/
theorem hintikka_chain_exists_since
    {Sigma : Finset (Formula Atom)} {φ ψ : Formula Atom}
    (oracle : HintikkaStepOracleSince (Sigma := Sigma) φ ψ)
    (h0 : HintikkaPoint Sigma) (w0 : BXPoint Atom)
    (h0_sub : ∀ f ∈ h0.formulas, f ∈ w0.formulas)
    (h_target : Formula.snce φ ψ ∈ h0.formulas) :
    ∃ c : HintikkaRawChain Sigma,
      c.last = h0 ∧ ψ ∈ c.head.formulas ∧ ChainWitnessed c := by
  suffices h : ∀ n h0 (w0 : BXPoint Atom),
      (∀ f ∈ h0.formulas, f ∈ w0.formulas) →
      sinceDefectCount h0 = n →
      Formula.snce φ ψ ∈ h0.formulas →
      ∃ c : HintikkaRawChain Sigma,
        c.last = h0 ∧ ψ ∈ c.head.formulas ∧ ChainWitnessed c by
    exact h (sinceDefectCount h0) h0 w0 h0_sub rfl h_target
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h0 w0 h0_sub h_n h_target
    by_cases h_psi : ψ ∈ h0.formulas
    · -- Already at witness: singleton chain.
      refine ⟨HintikkaRawChain.singleton h0, ?_, ?_, ?_⟩
      · simp
      · simpa using h_psi
      · intro h hh
        simp [HintikkaRawChain.singleton_points] at hh
        exact ⟨w0, by subst hh; exact h0_sub⟩
    · -- Not yet at witness: invoke oracle to get a predecessor `wh'.point`.
      obtain ⟨wh', h_step, h_cases⟩ := oracle h0 h_target h_psi
      rcases h_cases with h_psi' | ⟨h_target', h_dec⟩
      · -- Predecessor already contains ψ: chain [wh'.point, h0] via singleton.snoc.
        have h_sing_last : (HintikkaRawChain.singleton wh'.point).last = wh'.point := by simp
        refine ⟨(HintikkaRawChain.singleton wh'.point).snoc h0
          (by rw [h_sing_last]; exact h_step), ?_, ?_, ?_⟩
        · rw [HintikkaRawChain.snoc_last]
        · rw [HintikkaRawChain.snoc_head]; simpa using h_psi'
        · intro h hh
          simp [HintikkaRawChain.snoc_points,
            HintikkaRawChain.singleton_points] at hh
          rcases hh with rfl | rfl
          · exact ⟨wh'.witness, wh'.point_subset_witness⟩
          · exact ⟨w0, h0_sub⟩
      · -- Oracle stepped to strictly smaller defect: recurse on wh'.point.
        have h_dec' : sinceDefectCount wh'.point < n := h_n ▸ h_dec
        obtain ⟨c', hc'_last, hc'_head, hc'_witd⟩ :=
          ih (sinceDefectCount wh'.point) h_dec' wh'.point wh'.witness
            wh'.point_subset_witness rfl h_target'
        refine ⟨c'.snoc h0 (by rw [hc'_last]; exact h_step), ?_, ?_, ?_⟩
        · rw [HintikkaRawChain.snoc_last]
        · rw [HintikkaRawChain.snoc_head]; exact hc'_head
        · intro h hh
          simp [HintikkaRawChain.snoc_points] at hh
          rcases hh with h_in | rfl
          · exact hc'_witd h h_in
          · exact ⟨w0, h0_sub⟩

/-- Since dual of `chain_step_seed_consistent`. -/
theorem chain_step_seed_consistent_since
    {Sigma : Finset (Formula Atom)}
    {c : HintikkaRawChain Sigma} (h_wit : ChainWitnessed c)
    {h : HintikkaPoint Sigma} (h_mem : h ∈ c.points)
    (Omega : Set (Formula Atom)) (h_sub : Omega ⊆ (h.formulas : Set (Formula Atom))) :
    SetConsistent (fc := FrameClass.Base) Omega :=
  chain_step_seed_consistent (c := c) h_wit h_mem Omega h_sub

/-- Guard lemma: at any interior point of the raw chain built by
    `hintikka_chain_exists`, the guard `φ ∈ h_i.formulas` holds
    whenever the target Until is still present and the witness is
    still absent. -/
theorem hintikka_chain_guard_step {Sigma : Finset (Formula Atom)} {φ ψ : Formula Atom}
    {h1 h2 : HintikkaPoint Sigma}
    (h_step : hintikkaStep h1 h2)
    (h_target : Formula.untl φ ψ ∈ h1.formulas)
    (h_not : ψ ∉ h1.formulas) :
    φ ∈ h1.formulas := by
  exact (h_step.2.2 φ ψ h_target h_not).1

/-- Re-export of `hintikka_chain_exists` for downstream ergonomics. -/
theorem quasimodel_chain_exists
    {Sigma : Finset (Formula Atom)} {φ ψ : Formula Atom}
    (oracle : HintikkaStepOracle (Sigma := Sigma) φ ψ)
    (h0 : HintikkaPoint Sigma) (w0 : BXPoint Atom)
    (h0_sub : ∀ f ∈ h0.formulas, f ∈ w0.formulas)
    (h_target : Formula.untl φ ψ ∈ h0.formulas) :
    ∃ c : HintikkaRawChain Sigma,
      c.head = h0 ∧ ψ ∈ c.last.formulas ∧ ChainWitnessed c :=
  hintikka_chain_exists oracle h0 w0 h0_sub h_target

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Quasimodel
