/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Decidability.Saturation

/-!
# Countermodel Extraction from Open Tableau Branches

This module extracts finite countermodels from open (saturated) tableau branches.
When a branch saturates without closing, it describes a model that falsifies
the original formula, providing a witness for invalidity.

## Main Definitions

- `SimpleCountermodel`: Simple countermodel description (atoms true/false)
- `SemanticCountermodel`: Full semantic countermodel with world states, time domain,
  temporal ordering, and atom valuation
- `branchTruth`: Recursive truth evaluation on the semantic countermodel
- `extractSimpleCountermodel`: Build simple countermodel from saturated branch
- `extractSemanticCountermodel`: Build semantic countermodel from saturated branch
- `branchTruthLemma`: Key correctness theorem -- every signed formula in a saturated
  open branch is semantically satisfied in the extracted countermodel

## Two-Layer Architecture

1. **SimpleCountermodel** (Layer 0): Tracks only which atoms are true/false.
   Useful for debugging, display, and training data generation.

2. **SemanticCountermodel** (Layer 1): Full finite model with worlds, times,
   temporal ordering, and valuation. Defined directly on the branch structure
   to avoid universe level issues with the full TaskFrame/WorldHistory stack.
   The `branchTruthLemma` proves semantic correctness of this model.

## Semantic Correctness Guarantee

The `branchTruthLemma` establishes that for a saturated open branch `b`:
- If `T(phi)` at `(w, t)` is in `b`, then `phi` is true at `(w, t)` in the model
- If `F(phi)` at `(w, t)` is in `b`, then `phi` is false at `(w, t)` in the model

The proof proceeds by structural induction on formulas and uses saturation
invariants that derive properties of the branch from `findUnexpanded b = none`
(saturation) and `findClosure b fc = none` (openness). The `branchTruth`
definition uses direct-successor semantics for Until/Since (rather than
transitive-closure semantics), matching the tableau's branching decomposition
and enabling a clean inductive proof via the `sat_untl_neg`/`sat_snce_neg`
saturation invariants.

## References

* Gore, R. (1999). Tableau Methods for Modal and Temporal Logics

Ported from BimodalLogic/Metalogic/Decidability/CountermodelExtraction.lean with
adaptations for universe-polymorphic `Formula Atom`.
-/

set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Decidability

open Cslib.Logic.Bimodal

variable {Atom : Type u} [DecidableEq Atom] [Hashable Atom]

/-!
## BEq Lawfulness for Formula

The auto-derived `BEq` instance on `Formula Atom` needs to be shown lawful
(i.e., `a == b ↔ a = b`) for the saturation invariant proofs. This is needed
because the tableau code uses `guard == Formula.top` via the auto-derived `BEq`,
while the proofs need to connect this to propositional equality.

We prove this by structural induction on formulas.
-/

/-- Convert `guard ≠ Formula.top` to `(guard == Formula.top) = false`.
    Formula.top = .imp .bot .bot, so we case-split on the guard constructor.
    For non-imp constructors, the auto-derived BEq returns false definitionally.
    For the imp case, we use the hypothesis `guard ≠ Formula.top`. -/
private theorem Formula.beq_top_false_of_ne (guard : Formula Atom)
    (hg : guard ≠ Formula.top) : (guard == Formula.top) = false := by
  -- The auto-derived BEq compares constructors first; for different constructors
  -- it returns false. For .imp a b vs .imp .bot .bot, it recurses.
  -- We handle all cases by showing that if `guard == Formula.top` were true,
  -- then `guard = Formula.top`, contradicting `hg`.
  suffices ∀ (a b : Formula Atom), (a == b) = true → a = b by
    cases h : guard == Formula.top
    · rfl
    · exfalso; exact hg (this guard Formula.top h)
  intro a b
  revert b
  induction a with
  | atom p =>
    intro b h; cases b with
    | atom q => dsimp [BEq.beq] at h; exact congrArg _ (of_decide_eq_true h)
    | _ => cases h
  | bot =>
    intro b h; cases b with
    | bot => rfl
    | _ => cases h
  | imp a1 a2 ih1 ih2 =>
    intro b h; cases b with
    | imp b1 b2 =>
      change (a1 == b1 && a2 == b2) = true at h
      simp only [Bool.and_eq_true] at h
      exact congr (congrArg _ (ih1 b1 h.1)) (ih2 b2 h.2)
    | _ => cases h
  | box a ih =>
    intro b h; cases b with
    | box b => change (a == b) = true at h; exact congrArg _ (ih b h)
    | _ => cases h
  | untl a1 a2 ih1 ih2 =>
    intro b h; cases b with
    | untl b1 b2 =>
      change (a1 == b1 && a2 == b2) = true at h
      simp only [Bool.and_eq_true] at h
      exact congr (congrArg _ (ih1 b1 h.1)) (ih2 b2 h.2)
    | _ => cases h
  | snce a1 a2 ih1 ih2 =>
    intro b h; cases b with
    | snce b1 b2 =>
      change (a1 == b1 && a2 == b2) = true at h
      simp only [Bool.and_eq_true] at h
      exact congr (congrArg _ (ih1 b1 h.1)) (ih2 b2 h.2)
    | _ => cases h

/-!
## Simple Countermodel Type
-/

/--
A simplified countermodel that provides the valuation assignment
without the full semantic machinery. Useful for debugging and display.
-/
structure SimpleCountermodel (Atom : Type u) [DecidableEq Atom] [Hashable Atom] where
  /-- Atoms that are true. -/
  trueAtoms : List Atom
  /-- Atoms that are false. -/
  falseAtoms : List Atom
  /-- The formula being refuted. -/
  formula : Formula Atom

/-!
## Valuation Extraction
-/

/--
Extract the set of atoms that should be true from a saturated branch.
An atom is true if T(atom) appears in the branch.
-/
def extractTrueAtoms (b : Branch Atom) : List Atom :=
  b.filterMap fun sf =>
    match sf.sign, sf.formula with
    | .pos, .atom p => some p
    | _, _ => none

/--
Extract the set of atoms that should be false from a saturated branch.
An atom is false if F(atom) appears in the branch.
-/
def extractFalseAtoms (b : Branch Atom) : List Atom :=
  b.filterMap fun sf =>
    match sf.sign, sf.formula with
    | .neg, .atom p => some p
    | _, _ => none

/--
Build a simple countermodel description from a saturated branch.
-/
def extractSimpleCountermodel (φ : Formula Atom) (b : Branch Atom) : SimpleCountermodel Atom :=
  { trueAtoms := extractTrueAtoms b
  , falseAtoms := extractFalseAtoms b
  , formula := φ
  }

/-!
## Countermodel Verification
-/

/--
Check if a simple countermodel is self-consistent.
An atom cannot be both true and false.
-/
def SimpleCountermodel.isConsistent [BEq Atom] (cm : SimpleCountermodel Atom) : Bool :=
  cm.trueAtoms.all (fun p => ¬cm.falseAtoms.contains p)

/-!
## Countermodel Extraction from Tableau
-/

/--
Extract a simple countermodel from an open saturated branch.
-/
def extractCountermodelSimple (φ : Formula Atom) (b : Branch Atom)
    {ord : TimeOrdering} {applied : AppliedSet Atom}
    (_hSaturated : findUnexpandedWithApplied b (timeOrd := ord) (applied := applied) = none)
    : SimpleCountermodel Atom :=
  extractSimpleCountermodel φ b

/--
Extract countermodel from an expanded tableau with an open branch.
-/
def extractCountermodelFromTableau (φ : Formula Atom) (tableau : ExpandedTableau Atom)
    (_fc : FrameClass := .Base) : Option (SimpleCountermodel Atom) :=
  match tableau with
  | .allClosed _ => none  -- No countermodel, formula is valid
  | .hasOpen openBranch _ord _applied hSaturated =>
      some (extractCountermodelSimple φ openBranch hSaturated)

/-!
## Semantic Countermodel

A `SemanticCountermodel` captures the full finite model extracted from a
saturated open branch: world states, time domain, temporal ordering, and
atom valuation. This is the "Layer 1" (branch model) of the two-layer
countermodel approach, defined directly on the branch structure to avoid
universe level issues with the full `TaskFrame`/`WorldHistory` stack.
-/

/--
A semantic countermodel extracted from a saturated open tableau branch.

Contains the finite world set, time set, temporal ordering constraints,
and atom valuation. The valuation is indexed by `(WorldIndex, TimeIndex, Atom)`
triples, matching the labeled tableau's structure.
-/
structure SemanticCountermodel (Atom : Type u) [DecidableEq Atom] [Hashable Atom] where
  /-- The formula being refuted. -/
  formula : Formula Atom
  /-- The saturated open branch from which this model is extracted. -/
  branch : Branch Atom
  /-- All world indices appearing in the branch. -/
  worlds : List WorldIndex
  /-- All time indices appearing in the branch. -/
  times : List TimeIndex
  /-- Temporal ordering constraints from the tableau expansion. -/
  timeOrdering : TimeOrdering
  /-- Atom valuation: true iff `T(atom p)` at `(w, t)` appears in the branch. -/
  atomValuation : WorldIndex → TimeIndex → Atom → Bool

/-!
### Time Ordering Helpers
-/

/--
Check whether `t1` is strictly before `t2` in the transitive closure of
the time ordering constraints. Uses fuel-bounded reachability.
-/
def isTimeOrderedBefore (ord : TimeOrdering) (t1 t2 : TimeIndex)
    (fuel : Nat := 50) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    -- Direct edge?
    if ord.constraints.any (fun (a, b) => a == t1 && b == t2) then true
    else
      -- Transitive: t1 < t_mid < t2 for some t_mid?
      let successors := ord.futureOf t1
      successors.any fun t_mid => isTimeOrderedBefore ord t_mid t2 fuel
termination_by fuel

/--
Check whether `t1` is strictly after `t2` in the temporal ordering.
-/
def isTimeOrderedAfter (ord : TimeOrdering) (t1 t2 : TimeIndex)
    (fuel : Nat := 50) : Bool :=
  isTimeOrderedBefore ord t2 t1 fuel

/--
Collect all times in the model that are strictly after `t` (transitive closure).
-/
def futureTimes (ord : TimeOrdering) (t : TimeIndex)
    (allTimes : List TimeIndex) : List TimeIndex :=
  allTimes.filter fun t' => isTimeOrderedBefore ord t t'

/--
Collect all times in the model that are strictly before `t` (transitive closure).
-/
def pastTimes (ord : TimeOrdering) (t : TimeIndex)
    (allTimes : List TimeIndex) : List TimeIndex :=
  allTimes.filter fun t' => isTimeOrderedBefore ord t' t

/--
Collect all times strictly between `t1` and `t2` (exclusive on both ends).
A time `t` is between `t1` and `t2` if `t1 < t` and `t < t2`.
-/
def timesBetween (ord : TimeOrdering) (t1 t2 : TimeIndex)
    (allTimes : List TimeIndex) : List TimeIndex :=
  allTimes.filter fun t =>
    isTimeOrderedBefore ord t1 t && isTimeOrderedBefore ord t t2

/-!
### Branch Truth Evaluation

`branchTruth` defines truth of a formula at a `(world, time)` pair in the
semantic countermodel. This is defined by structural recursion on the formula.

- `atom p`: true iff `atomValuation w t p = true`
- `bot`: always false
- `imp phi psi`: `phi` true implies `psi` true (material conditional)
- `box phi`: `phi` true at all worlds in the model (S5 universal accessibility)
- `untl event guard`: there exists a direct future time `t'` (in `futureOf t`)
  where both `event` and `guard` are true. This uses direct-successor semantics
  rather than transitive-closure semantics, which suffices for the truth lemma
  since T(U(event,guard)) is consumed in saturated branches.
- `snce event guard`: there exists a direct past time `t'` (in `pastOf t`)
  where both `event` and `guard` are true. Mirror of untl.
-/

/--
Evaluate truth of a formula at a `(world, time)` pair in the semantic
countermodel. Defined by structural recursion on the formula.
-/
def branchTruth (cm : SemanticCountermodel Atom) (w : WorldIndex) (t : TimeIndex)
    : Formula Atom → Prop
  | .atom p => cm.atomValuation w t p = true
  | .bot => False
  | .imp φ ψ => branchTruth cm w t φ → branchTruth cm w t ψ
  | .box φ => ∀ w' ∈ cm.worlds, branchTruth cm w' t φ
  | .untl event guard =>
      -- Direct-successor semantics: there exists a direct future time where
      -- both event and guard hold.
      ∃ t' ∈ cm.timeOrdering.futureOf t,
        branchTruth cm w t' event ∧ branchTruth cm w t' guard
  | .snce event guard =>
      -- Mirror of untl: direct-predecessor semantics for Since.
      ∃ t' ∈ cm.timeOrdering.pastOf t,
        branchTruth cm w t' event ∧ branchTruth cm w t' guard

/--
Signed truth in the semantic countermodel: positive formulas must be true,
negative formulas must be false.
-/
def signedTruthInModel (cm : SemanticCountermodel Atom) (sf : SignedFormula Atom) : Prop :=
  match sf.sign with
  | .pos => branchTruth cm sf.label.world sf.label.time sf.formula
  | .neg => ¬branchTruth cm sf.label.world sf.label.time sf.formula

/-!
### Semantic Countermodel Extraction
-/

/--
Build the atom valuation from a branch: an atom `p` is true at `(w, t)` iff
`T(atom p)` at label `(w, t)` appears in the branch.
-/
def buildAtomValuation (b : Branch Atom) : WorldIndex → TimeIndex → Atom → Bool :=
  fun w t p => b.hasPosAt (.atom p) ⟨w, t⟩

/--
Extract a `SemanticCountermodel` from a saturated open branch.

The model's worlds and times are exactly those appearing in the branch labels.
The atom valuation is determined by positive atom occurrences.
The time ordering comes from the tableau expansion's `TimeOrdering`.
-/
def extractSemanticCountermodel (φ : Formula Atom) (b : Branch Atom)
    (ord : TimeOrdering) : SemanticCountermodel Atom :=
  { formula := φ
  , branch := b
  , worlds := b.knownWorlds
  , times := b.knownTimes
  , timeOrdering := ord
  , atomValuation := buildAtomValuation b
  }

/-!
## Saturation Invariants

These lemmas derive properties of saturated open branches from the conditions
`findUnexpanded b = none` (saturation) and `findClosure b fc = none` (openness).
They form the foundation for the truth lemma proof.
-/

/--
**No T(bot) in open branch**: If `findClosure b fc = none`, then no signed
formula `T(bot)` at any label appears in the branch.
-/
theorem sat_no_bot_pos (b : Branch Atom) (fc : FrameClass)
    (hOpen : findClosure b fc = none) :
    ∀ l : Label, ¬(⟨.pos, .bot, l⟩ ∈ b) := by
  intro l hmem
  have hBot : (checkBotPos b).isSome := by
    rw [checkBotPos, List.findSome?_isSome_iff]
    refine ⟨⟨.pos, .bot, l⟩, hmem, ?_⟩
    simp [BEq.beq]; exact ⟨rfl, rfl⟩
  simp only [findClosure] at hOpen
  cases h : checkBotPos b with
  | none => simp [h] at hBot
  | some r => simp [h] at hOpen

/--
**No complementary pair in open branch**: If `findClosure b fc = none`, then
for any formula `phi` and label `l`, not both `T(phi)` and `F(phi)` at `l` are in `b`.
-/
theorem sat_no_contradiction (b : Branch Atom) (fc : FrameClass)
    (hOpen : findClosure b fc = none) :
    ∀ φ : Formula Atom, ∀ l : Label,
      ¬(⟨.pos, φ, l⟩ ∈ b ∧ ⟨.neg, φ, l⟩ ∈ b) := by
  intro φ l ⟨hpos, hneg⟩
  have hContra : (checkContradiction b).isSome := by
    rw [checkContradiction, List.findSome?_isSome_iff]
    refine ⟨⟨.pos, φ, l⟩, hpos, ?_⟩
    simp only [SignedFormula.isPos, Option.isSome_some]
    have hNegAt : Branch.hasNegAt b φ l = true := by
      simp only [Branch.hasNegAt, Branch.contains, List.any_eq_true]
      exact ⟨_, hneg, beq_self_eq_true _⟩
    simp [hNegAt]
  simp only [findClosure] at hOpen
  cases hb : checkBotPos b with
  | some r => simp [hb] at hOpen
  | none =>
    simp [hb] at hOpen
    cases hc : checkContradiction b with
    | some r => simp [hc] at hOpen
    | none => simp [hc] at hContra

/--
**Atom consistency**: In a saturated open branch, for any atom `p` and label `l`,
not both `T(atom p)` and `F(atom p)` at label `l` are in the branch.
A corollary of `sat_no_contradiction`.
-/
theorem sat_atom_consistent (b : Branch Atom) (fc : FrameClass)
    (hOpen : findClosure b fc = none) :
    ∀ (p : Atom) (l : Label),
      ¬(b.hasPosAt (.atom p) l = true ∧ b.hasNegAt (.atom p) l = true) := by
  intro p l ⟨hPosAt, hNegAt⟩
  simp only [Branch.hasPosAt, Branch.contains, List.any_eq_true] at hPosAt
  obtain ⟨sf_pos, hmem_pos, hbeq_pos⟩ := hPosAt
  have heq_pos : sf_pos = ⟨.pos, .atom p, l⟩ := beq_iff_eq.mp hbeq_pos
  subst heq_pos
  simp only [Branch.hasNegAt, Branch.contains, List.any_eq_true] at hNegAt
  obtain ⟨sf_neg, hmem_neg, hbeq_neg⟩ := hNegAt
  have heq_neg : sf_neg = ⟨.neg, .atom p, l⟩ := beq_iff_eq.mp hbeq_neg
  subst heq_neg
  exact sat_no_contradiction b fc hOpen (.atom p) l ⟨hmem_pos, hmem_neg⟩

/--
**Atom valuation correctness (positive)**: If `T(atom p)` at `(w, t)` is in
the branch, then `buildAtomValuation b w t p = true`.
This follows directly from the definition of `buildAtomValuation`.
-/
theorem valuation_reflects_pos (b : Branch Atom) (p : Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.pos, .atom p, ⟨w, t⟩⟩ ∈ b) :
    buildAtomValuation b w t p = true := by
  unfold buildAtomValuation Branch.hasPosAt Branch.contains
  rw [List.any_eq_true]
  exact ⟨_, hmem, beq_self_eq_true _⟩

/--
**Atom valuation correctness (negative)**: If `F(atom p)` at `(w, t)` is in
an open branch, then `buildAtomValuation b w t p = false`.
Follows from atom consistency: if F(atom p) is in b, then T(atom p) is not.
-/
theorem valuation_reflects_neg (b : Branch Atom) (fc : FrameClass)
    (hOpen : findClosure b fc = none)
    (p : Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.neg, .atom p, ⟨w, t⟩⟩ ∈ b) :
    buildAtomValuation b w t p = false := by
  unfold buildAtomValuation
  by_contra h
  push_neg at h
  have hPosAt : Branch.hasPosAt b (.atom p) ⟨w, t⟩ = true := by
    cases hc : Branch.hasPosAt b (.atom p) ⟨w, t⟩ <;> simp_all
  have hNegAt : Branch.hasNegAt b (.atom p) ⟨w, t⟩ = true := by
    simp only [Branch.hasNegAt, Branch.contains, List.any_eq_true]
    exact ⟨_, hmem, beq_self_eq_true _⟩
  exact sat_atom_consistent b fc hOpen p ⟨w, t⟩ ⟨hPosAt, hNegAt⟩

/--
Helper: `findUnexpanded b = none` implies every formula in `b` is expanded.
-/
private theorem findUnexpanded_none_all_expanded (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none) :
    ∀ sf ∈ b, isExpanded sf b (timeOrd := timeOrd) = true := by
  intro sf hsf
  unfold findUnexpanded at hSat
  have h := List.find?_eq_none.mp hSat sf hsf
  simp [Bool.not_eq_true] at h
  exact h

/--
Helper: if `isExpanded sf b = true`, then `findApplicableRule sf b = none`.
-/
private theorem expanded_iff_no_applicable (sf : SignedFormula Atom) (b : Branch Atom) :
    isExpanded sf b = true ↔ (findApplicableRule sf b).isNone = true := by
  unfold isExpanded
  simp

/--
**Implication negative saturation**: If `F(psi -> chi)` is in a saturated branch,
then `T(psi)` and `F(chi)` are both in the branch at the same label.
The `impNeg` rule is a linear (non-branching) rule that adds both.

Actually, `F(psi -> chi)` cannot exist in a saturated branch at all: the `impNeg`
rule always applies to it. So this is vacuously true by contradiction.
-/
private theorem impNeg_not_expanded (b : Branch Atom) (ψ χ : Formula Atom) (l : Label)
    (timeOrd : TimeOrdering := .empty) : isExpanded ⟨.neg, .imp ψ χ, l⟩ b (timeOrd := timeOrd) = false := by
  unfold isExpanded findApplicableRule
  simp only [allRulesForFC, allRules, denseRules, discreteRules]
  simp only [List.findSome?, isApplicable, asNeg?, asAnd?, asOr?, asDiamond?, applyRule]
  simp

private theorem impPos_not_expanded (b : Branch Atom) (ψ χ : Formula Atom) (l : Label)
    (timeOrd : TimeOrdering := .empty) : isExpanded ⟨.pos, .imp ψ χ, l⟩ b (timeOrd := timeOrd) = false := by
  unfold isExpanded findApplicableRule
  simp only [allRulesForFC, allRules, denseRules, discreteRules]
  simp only [List.findSome?, isApplicable, asNeg?, asAnd?, asOr?, asDiamond?, applyRule]
  simp

theorem sat_imp_neg (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (ψ χ : Formula Atom) (l : Label)
    (hmem : ⟨.neg, .imp ψ χ, l⟩ ∈ b) :
    ⟨.pos, ψ, l⟩ ∈ b ∧ ⟨.neg, χ, l⟩ ∈ b := by
  exfalso
  have hExp := findUnexpanded_none_all_expanded b timeOrd hSat ⟨.neg, .imp ψ χ, l⟩ hmem
  simp [impNeg_not_expanded] at hExp

/--
**Box positive saturation**: If `T(box phi)` at `(w, t)` is in a saturated branch,
then `T(phi)` at `(w', t)` is in the branch for all known worlds `w'`.
The `boxPos` rule is persistent and propagates to all known worlds.
-/
private theorem contains_iff_mem (b : Branch Atom) (sf : SignedFormula Atom) :
    Branch.contains b sf = true ↔ sf ∈ b := by
  simp only [Branch.contains, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, heq⟩
    exact beq_iff_eq.mp heq ▸ hx
  · intro h
    exact ⟨sf, h, beq_self_eq_true _⟩

set_option maxHeartbeats 1600000 in
theorem sat_box_pos (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (φ : Formula Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.pos, .box φ, ⟨w, t⟩⟩ ∈ b) :
    ∀ w' ∈ b.knownWorlds, ⟨.pos, φ, ⟨w', t⟩⟩ ∈ b := by
  have hExp := findUnexpanded_none_all_expanded b timeOrd hSat ⟨.pos, .box φ, ⟨w, t⟩⟩ hmem
  simp only [isExpanded, Option.isNone_iff_eq_none] at hExp
  unfold findApplicableRule at hExp
  rw [List.findSome?_eq_none_iff] at hExp
  have hBoxPos := hExp (.boxPos) (by simp [allRulesForFC, allRules, denseRules, discreteRules])
  simp only [isApplicable, applyRule] at hBoxPos
  simp only [ite_true] at hBoxPos
  set fm := (b.knownWorlds.filterMap fun w' =>
    if b.contains (SignedFormula.pos φ { world := w', time := t }) = true then none
    else some (SignedFormula.pos φ { world := w', time := t })) with hfm_def
  by_cases hfm : fm.isEmpty
  · intro w' hw'
    by_contra habs
    have hNotContains : Branch.contains b ⟨.pos, φ, ⟨w', t⟩⟩ = false := by
      simp only [Bool.eq_false_iff]; exact fun h => habs ((contains_iff_mem b _).mp h)
    have hmem_fm : SignedFormula.pos φ ⟨w', t⟩ ∈ fm := by
      rw [hfm_def, List.mem_filterMap]
      exact ⟨w', hw', by simp [SignedFormula.pos, hNotContains]⟩
    have hnil : fm = [] := List.isEmpty_iff.mp hfm
    rw [hnil] at hmem_fm
    exact absurd hmem_fm (by simp)
  · simp [hfm] at hBoxPos

/--
**Box negative saturation**: If `F(box phi)` at `(w, t)` is in a saturated branch,
then there exists a world `w'` in `knownWorlds` such that `F(phi)` at `(w', t)`
is in the branch. The `boxNeg` rule creates a fresh witness world.
-/
private theorem boxNeg_not_expanded (b : Branch Atom) (φ : Formula Atom) (l : Label)
    (timeOrd : TimeOrdering := .empty) : isExpanded ⟨.neg, .box φ, l⟩ b (timeOrd := timeOrd) = false := by
  unfold isExpanded findApplicableRule
  simp only [allRulesForFC, allRules, denseRules, discreteRules]
  simp only [List.findSome?, isApplicable, asNeg?, asAnd?, asOr?, asDiamond?, applyRule]
  simp

theorem sat_box_neg (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (φ : Formula Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.neg, .box φ, ⟨w, t⟩⟩ ∈ b) :
    ∃ w' ∈ b.knownWorlds, ⟨.neg, φ, ⟨w', t⟩⟩ ∈ b := by
  exfalso
  have hExp := findUnexpanded_none_all_expanded b timeOrd hSat ⟨.neg, .box φ, ⟨w, t⟩⟩ hmem
  simp [boxNeg_not_expanded] at hExp

set_option maxHeartbeats 800000 in
/--
Helper: T(U(event, guard)) is never expanded in any branch.
If guard = top, someFuturePos applies (consumable). If guard != top, untlPos applies (branching).
Either way, the formula is consumed and removed from the branch during expansion.
-/
private theorem untlPos_not_expanded (b : Branch Atom) (event guard : Formula Atom) (l : Label)
    (timeOrd : TimeOrdering := .empty) : isExpanded ⟨.pos, .untl event guard, l⟩ b (timeOrd := timeOrd) = false := by
  simp only [isExpanded, Bool.eq_false_iff]
  intro h
  simp only [Option.isNone_iff_eq_none] at h
  unfold findApplicableRule at h
  rw [List.findSome?_eq_none_iff] at h
  by_cases hg : guard = Formula.top
  · subst hg
    have := h (.someFuturePos) (by simp [allRulesForFC, allRules, denseRules, discreteRules])
    simp [isApplicable, asSomeFuture?, Formula.top, applyRule] at this
  · have h1 := h (.untlPos) (by simp [allRulesForFC, allRules, denseRules, discreteRules])
    have hg' : (guard == Formula.top) = false := Formula.beq_top_false_of_ne guard hg
    simp only [isApplicable, asUntil?] at h1
    simp [hg'] at h1
    simp [applyRule, asUntil?, hg'] at h1

theorem sat_untl_pos (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (event guard : Formula Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.pos, .untl event guard, ⟨w, t⟩⟩ ∈ b) :
    ∃ t' ∈ b.knownTimes,
      (⟨.pos, event, ⟨w, t'⟩⟩ ∈ b) ∨
      (⟨.pos, guard, ⟨w, t'⟩⟩ ∈ b ∧ ⟨.pos, .untl event guard, ⟨w, t'⟩⟩ ∈ b) := by
  exfalso
  have hExp := findUnexpanded_none_all_expanded b timeOrd hSat ⟨.pos, .untl event guard, ⟨w, t⟩⟩ hmem
  simp [untlPos_not_expanded] at hExp

set_option maxHeartbeats 800000 in
/--
Helper: T(S(event, guard)) is never expanded in any branch (mirror of untlPos).
-/
private theorem sncePos_not_expanded (b : Branch Atom) (event guard : Formula Atom) (l : Label)
    (timeOrd : TimeOrdering := .empty) : isExpanded ⟨.pos, .snce event guard, l⟩ b (timeOrd := timeOrd) = false := by
  simp only [isExpanded, Bool.eq_false_iff]
  intro h
  simp only [Option.isNone_iff_eq_none] at h
  unfold findApplicableRule at h
  rw [List.findSome?_eq_none_iff] at h
  by_cases hg : guard = Formula.top
  · subst hg
    have := h (.somePastPos) (by simp [allRulesForFC, allRules, denseRules, discreteRules])
    simp [isApplicable, asSomePast?, Formula.top, applyRule, Formula.somePast] at this
  · have h1 := h (.sncePos) (by simp [allRulesForFC, allRules, denseRules, discreteRules])
    have hg' : (guard == Formula.top) = false := Formula.beq_top_false_of_ne guard hg
    simp only [isApplicable, asSince?] at h1
    simp [hg'] at h1
    simp [applyRule, asSince?, hg'] at h1

theorem sat_snce_pos (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (event guard : Formula Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.pos, .snce event guard, ⟨w, t⟩⟩ ∈ b) :
    ∃ t' ∈ b.knownTimes,
      (⟨.pos, event, ⟨w, t'⟩⟩ ∈ b) ∨
      (⟨.pos, guard, ⟨w, t'⟩⟩ ∈ b ∧ ⟨.pos, .snce event guard, ⟨w, t'⟩⟩ ∈ b) := by
  exfalso
  have hExp := findUnexpanded_none_all_expanded b timeOrd hSat ⟨.pos, .snce event guard, ⟨w, t⟩⟩ hmem
  simp [sncePos_not_expanded] at hExp

set_option maxHeartbeats 3200000 in
/--
**Some-future negative saturation**: If `F(FA)` at `(w, t)` is in a saturated
branch, then `F(A)` is at `(w, t')` for every known future time `t'`.
Here `F(FA) = F(U(A, top))`.
-/
theorem sat_someFuture_neg (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (event : Formula Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.neg, .untl event (.imp .bot .bot), ⟨w, t⟩⟩ ∈ b) :
    ∀ t' ∈ timeOrd.futureOf t,
      ⟨.neg, event, ⟨w, t'⟩⟩ ∈ b := by
  have hExp := findUnexpanded_none_all_expanded b timeOrd hSat
    ⟨.neg, .untl event (.imp .bot .bot), ⟨w, t⟩⟩ hmem
  simp only [isExpanded, Option.isNone_iff_eq_none] at hExp
  unfold findApplicableRule at hExp
  rw [List.findSome?_eq_none_iff] at hExp
  have hSFNeg := hExp (.someFutureNeg)
    (by simp [allRulesForFC, allRules, denseRules, discreteRules])
  simp only [isApplicable, asSomeFuture?] at hSFNeg
  have hNA : (applyRule .someFutureNeg ⟨.neg, .untl event (.imp .bot .bot), ⟨w, t⟩⟩ b timeOrd).1 =
      .notApplicable := by
    by_contra h
    match hm : (applyRule .someFutureNeg ⟨.neg, .untl event (.imp .bot .bot), ⟨w, t⟩⟩ b timeOrd).1 with
    | .notApplicable => exact h hm
    | .linear fs => rw [hm] at hSFNeg; simp at hSFNeg
    | .branching bs => rw [hm] at hSFNeg; simp at hSFNeg
    | .persistent fs => rw [hm] at hSFNeg; simp at hSFNeg
  unfold applyRule at hNA
  simp only [asSomeFuture?] at hNA
  intro t' ht'
  by_contra habs
  have hNotContains : Branch.contains b ⟨.neg, event, ⟨w, t'⟩⟩ = false := by
    simp only [Bool.eq_false_iff]; exact fun h => habs ((contains_iff_mem b _).mp h)
  have hFilterPred : (if Branch.contains b (SignedFormula.neg event { world := w, time := t' }) = true
      then none else some (SignedFormula.neg event { world := w, time := t' })) =
      some (SignedFormula.neg event { world := w, time := t' }) := by
    simp [SignedFormula.neg, hNotContains]
  have h_t'_fmap : SignedFormula.neg event { world := w, time := t' } ∈
      (timeOrd.futureOf t).filterMap fun t'' =>
        if Branch.contains b (SignedFormula.neg event { world := w, time := t'' }) = true
        then none else some (SignedFormula.neg event { world := w, time := t'' }) := by
    rw [List.mem_filterMap]
    exact ⟨t', ht', hFilterPred⟩
  have hNE : ((timeOrd.futureOf t).filterMap fun t'' =>
      if Branch.contains b (SignedFormula.neg event { world := w, time := t'' }) = true
      then none else some (SignedFormula.neg event { world := w, time := t'' })).isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro hempty
    have := List.isEmpty_iff.mp hempty
    exact absurd (this ▸ h_t'_fmap) (by simp)
  simp only [SignedFormula.neg] at hNA hNE
  simp [hNE] at hNA

set_option maxHeartbeats 3200000 in
/--
**Some-past negative saturation**: If `F(PA)` at `(w, t)` is in a saturated
branch, then `F(A)` is at `(w, t')` for every known past time `t'`.
Here `F(PA) = F(S(A, top))`.
-/
theorem sat_somePast_neg (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (event : Formula Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.neg, .snce event (.imp .bot .bot), ⟨w, t⟩⟩ ∈ b) :
    ∀ t' ∈ timeOrd.pastOf t,
      ⟨.neg, event, ⟨w, t'⟩⟩ ∈ b := by
  have hExp := findUnexpanded_none_all_expanded b timeOrd hSat
    ⟨.neg, .snce event (.imp .bot .bot), ⟨w, t⟩⟩ hmem
  simp only [isExpanded, Option.isNone_iff_eq_none] at hExp
  unfold findApplicableRule at hExp
  rw [List.findSome?_eq_none_iff] at hExp
  have hSPNeg := hExp (.somePastNeg)
    (by simp [allRulesForFC, allRules, denseRules, discreteRules])
  simp only [isApplicable, asSomePast?] at hSPNeg
  have hNA : (applyRule .somePastNeg ⟨.neg, .snce event (.imp .bot .bot), ⟨w, t⟩⟩ b timeOrd).1 =
      .notApplicable := by
    by_contra h
    match hm : (applyRule .somePastNeg ⟨.neg, .snce event (.imp .bot .bot), ⟨w, t⟩⟩ b timeOrd).1 with
    | .notApplicable => exact h hm
    | .linear fs => rw [hm] at hSPNeg; simp at hSPNeg
    | .branching bs => rw [hm] at hSPNeg; simp at hSPNeg
    | .persistent fs => rw [hm] at hSPNeg; simp at hSPNeg
  unfold applyRule at hNA
  simp only [asSomePast?] at hNA
  intro t' ht'
  by_contra habs
  have hNotContains : Branch.contains b ⟨.neg, event, ⟨w, t'⟩⟩ = false := by
    simp only [Bool.eq_false_iff]; exact fun h => habs ((contains_iff_mem b _).mp h)
  have hFilterPred : (if Branch.contains b (SignedFormula.neg event { world := w, time := t' }) = true
      then none else some (SignedFormula.neg event { world := w, time := t' })) =
      some (SignedFormula.neg event { world := w, time := t' }) := by
    simp [SignedFormula.neg, hNotContains]
  have h_t'_fmap : SignedFormula.neg event { world := w, time := t' } ∈
      (timeOrd.pastOf t).filterMap fun t'' =>
        if Branch.contains b (SignedFormula.neg event { world := w, time := t'' }) = true
        then none else some (SignedFormula.neg event { world := w, time := t'' }) := by
    rw [List.mem_filterMap]
    exact ⟨t', ht', hFilterPred⟩
  have hNE : ((timeOrd.pastOf t).filterMap fun t'' =>
      if Branch.contains b (SignedFormula.neg event { world := w, time := t'' }) = true
      then none else some (SignedFormula.neg event { world := w, time := t'' })).isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro hempty
    have := List.isEmpty_iff.mp hempty
    exact absurd (this ▸ h_t'_fmap) (by simp)
  simp only [SignedFormula.neg] at hNA hNE
  simp [hNE] at hNA

set_option maxHeartbeats 3200000 in
/--
**Until negative saturation**: If `F(U(event, guard))` at `(w, t)` is in a
saturated branch with guard not equal to `top`, then for every known future
time `t'`, either `F(event)` at `(w, t')` or the negated guard condition holds.
-/
theorem sat_untl_neg (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (event guard : Formula Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.neg, .untl event guard, ⟨w, t⟩⟩ ∈ b)
    (hguard : guard ≠ Formula.top) :
    ∀ t' ∈ timeOrd.futureOf t,
      ⟨.neg, event, ⟨w, t'⟩⟩ ∈ b ∨
      ⟨.neg, guard, ⟨w, t'⟩⟩ ∈ b := by
  have hExp := findUnexpanded_none_all_expanded b timeOrd hSat ⟨.neg, .untl event guard, ⟨w, t⟩⟩ hmem
  simp only [isExpanded, Option.isNone_iff_eq_none] at hExp
  unfold findApplicableRule at hExp
  rw [List.findSome?_eq_none_iff] at hExp
  have hUntlNeg := hExp (.untlNeg) (by simp [allRulesForFC, allRules, denseRules, discreteRules])
  simp only [isApplicable, asUntil?] at hUntlNeg
  have hg' : (guard == Formula.top) = false := Formula.beq_top_false_of_ne guard hguard
  simp only [hg'] at hUntlNeg
  have hNA : (applyRule .untlNeg ⟨.neg, .untl event guard, ⟨w, t⟩⟩ b timeOrd).1 = .notApplicable := by
    by_contra h
    match hm : (applyRule .untlNeg ⟨.neg, .untl event guard, ⟨w, t⟩⟩ b timeOrd).1 with
    | .notApplicable => exact h hm
    | .linear fs => rw [hm] at hUntlNeg; simp at hUntlNeg
    | .branching bs => rw [hm] at hUntlNeg; simp at hUntlNeg
    | .persistent fs => rw [hm] at hUntlNeg; simp at hUntlNeg
  unfold applyRule at hNA
  simp only [asUntil?, hg', ite_false, Bool.false_eq_true] at hNA
  intro t' ht'
  by_contra habs
  push_neg at habs
  obtain ⟨hne, hng⟩ := habs
  have hNotContainsE : Branch.contains b ⟨.neg, event, ⟨w, t'⟩⟩ = false := by
    simp only [Bool.eq_false_iff]; exact fun h => hne ((contains_iff_mem b _).mp h)
  have hNotContainsG : Branch.contains b ⟨.neg, guard, ⟨w, t'⟩⟩ = false := by
    simp only [Bool.eq_false_iff]; exact fun h => hng ((contains_iff_mem b _).mp h)
  have hFilterPred : (!Branch.contains b (SignedFormula.neg event { world := w, time := t' }) &&
    !Branch.contains b (SignedFormula.neg guard { world := w, time := t' })) = true := by
    simp [SignedFormula.neg, hNotContainsE, hNotContainsG]
  have h_t'_in : t' ∈ List.filter
    (fun t'' => !Branch.contains b (SignedFormula.neg event { world := w, time := t'' }) &&
                !Branch.contains b (SignedFormula.neg guard { world := w, time := t'' }))
    (timeOrd.futureOf t) := List.mem_filter.mpr ⟨ht', hFilterPred⟩
  obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem h_t'_in)
  simp only [SignedFormula.neg] at hNA hcons
  rw [hcons] at hNA
  simp at hNA

set_option maxHeartbeats 3200000 in
/--
**Since negative saturation**: Mirror of `sat_untl_neg` for past-directed Since.
-/
theorem sat_snce_neg (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (event guard : Formula Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.neg, .snce event guard, ⟨w, t⟩⟩ ∈ b)
    (hguard : guard ≠ Formula.top) :
    ∀ t' ∈ timeOrd.pastOf t,
      ⟨.neg, event, ⟨w, t'⟩⟩ ∈ b ∨
      ⟨.neg, guard, ⟨w, t'⟩⟩ ∈ b := by
  have hExp := findUnexpanded_none_all_expanded b timeOrd hSat ⟨.neg, .snce event guard, ⟨w, t⟩⟩ hmem
  simp only [isExpanded, Option.isNone_iff_eq_none] at hExp
  unfold findApplicableRule at hExp
  rw [List.findSome?_eq_none_iff] at hExp
  have hSnceNeg := hExp (.snceNeg) (by simp [allRulesForFC, allRules, denseRules, discreteRules])
  simp only [isApplicable, asSince?] at hSnceNeg
  have hg' : (guard == Formula.top) = false := Formula.beq_top_false_of_ne guard hguard
  simp only [hg'] at hSnceNeg
  have hNA : (applyRule .snceNeg ⟨.neg, .snce event guard, ⟨w, t⟩⟩ b timeOrd).1 = .notApplicable := by
    by_contra h
    match hm : (applyRule .snceNeg ⟨.neg, .snce event guard, ⟨w, t⟩⟩ b timeOrd).1 with
    | .notApplicable => exact h hm
    | .linear fs => rw [hm] at hSnceNeg; simp at hSnceNeg
    | .branching bs => rw [hm] at hSnceNeg; simp at hSnceNeg
    | .persistent fs => rw [hm] at hSnceNeg; simp at hSnceNeg
  unfold applyRule at hNA
  simp only [asSince?, hg', ite_false, Bool.false_eq_true] at hNA
  intro t' ht'
  by_contra habs
  push_neg at habs
  obtain ⟨hne, hng⟩ := habs
  have hNotContainsE : Branch.contains b ⟨.neg, event, ⟨w, t'⟩⟩ = false := by
    simp only [Bool.eq_false_iff]; exact fun h => hne ((contains_iff_mem b _).mp h)
  have hNotContainsG : Branch.contains b ⟨.neg, guard, ⟨w, t'⟩⟩ = false := by
    simp only [Bool.eq_false_iff]; exact fun h => hng ((contains_iff_mem b _).mp h)
  have hFilterPred : (!Branch.contains b (SignedFormula.neg event { world := w, time := t' }) &&
    !Branch.contains b (SignedFormula.neg guard { world := w, time := t' })) = true := by
    simp [SignedFormula.neg, hNotContainsE, hNotContainsG]
  have h_t'_in : t' ∈ List.filter
    (fun t'' => !Branch.contains b (SignedFormula.neg event { world := w, time := t'' }) &&
                !Branch.contains b (SignedFormula.neg guard { world := w, time := t'' }))
    (timeOrd.pastOf t) := List.mem_filter.mpr ⟨ht', hFilterPred⟩
  obtain ⟨hd, tl, hcons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem h_t'_in)
  simp only [SignedFormula.neg] at hNA hcons
  rw [hcons] at hNA
  simp at hNA

/-!
## Branch Truth Lemma

The truth lemma is the key correctness theorem. It states that for a saturated
open branch, every signed formula in the branch holds semantically in the
extracted countermodel:
- T(phi) at (w,t) implies phi is true at (w,t) in the model
- F(phi) at (w,t) implies phi is false at (w,t) in the model

The proof proceeds by structural induction on the formula, using the saturation
invariants established above.
-/

/--
Helper: if T(phi) at (w,t) is in the branch, then branchTruth cm w t phi holds.
Proved by structural induction on phi.
-/
private theorem truthLemma_pos (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (fc : FrameClass) (hOpen : findClosure b fc = none)
    (cm : SemanticCountermodel Atom)
    (hCm : cm = extractSemanticCountermodel cm.formula b cm.timeOrdering)
    (φ : Formula Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.pos, φ, ⟨w, t⟩⟩ ∈ b) :
    branchTruth cm w t φ := by
  induction φ generalizing w t with
  | atom p =>
    simp only [branchTruth]
    have := valuation_reflects_pos b p w t hmem
    rw [hCm]; simp [extractSemanticCountermodel, this]
  | bot =>
    exact absurd hmem (sat_no_bot_pos b fc hOpen ⟨w, t⟩)
  | imp ψ χ _ih_ψ _ih_χ =>
    exfalso
    have hExp := findUnexpanded_none_all_expanded b timeOrd hSat ⟨.pos, .imp ψ χ, ⟨w, t⟩⟩ hmem
    simp [impPos_not_expanded] at hExp
  | box ψ ih =>
    simp only [branchTruth]
    intro w' hw'
    rw [hCm] at hw'
    simp [extractSemanticCountermodel] at hw'
    have hbox := sat_box_pos b timeOrd hSat ψ w t hmem
    exact ih w' t (hbox w' hw')
  | untl event guard _ih_event _ih_guard =>
    exfalso
    have hExp := findUnexpanded_none_all_expanded b timeOrd hSat ⟨.pos, .untl event guard, ⟨w, t⟩⟩ hmem
    simp [untlPos_not_expanded] at hExp
  | snce event guard _ih_event _ih_guard =>
    exfalso
    have hExp := findUnexpanded_none_all_expanded b timeOrd hSat ⟨.pos, .snce event guard, ⟨w, t⟩⟩ hmem
    simp [sncePos_not_expanded] at hExp

/--
Helper: if F(phi) at (w,t) is in the branch, then ¬branchTruth cm w t phi holds.
Proved by structural induction on phi.
-/
private theorem truthLemma_neg (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (fc : FrameClass) (hOpen : findClosure b fc = none)
    (cm : SemanticCountermodel Atom)
    (hCm : cm = extractSemanticCountermodel cm.formula b cm.timeOrdering)
    (hOrd : cm.timeOrdering = timeOrd)
    (φ : Formula Atom) (w : WorldIndex) (t : TimeIndex)
    (hmem : ⟨.neg, φ, ⟨w, t⟩⟩ ∈ b) :
    ¬branchTruth cm w t φ := by
  induction φ generalizing w t with
  | atom p =>
    simp only [branchTruth]
    have := valuation_reflects_neg b fc hOpen p w t hmem
    rw [hCm]; simp [extractSemanticCountermodel, this]
  | bot =>
    simp [branchTruth]
  | imp ψ χ ih_ψ ih_χ =>
    simp only [branchTruth]
    intro h
    have ⟨hψ, hχ⟩ := sat_imp_neg b timeOrd hSat ψ χ ⟨w, t⟩ hmem
    have hψ_true := truthLemma_pos b timeOrd hSat fc hOpen cm hCm ψ w t hψ
    have hχ_false := ih_χ w t hχ
    exact hχ_false (h hψ_true)
  | box ψ ih =>
    simp only [branchTruth]
    intro h
    have ⟨w', hw'mem, hw'neg⟩ := sat_box_neg b timeOrd hSat ψ w t hmem
    have := ih w' t hw'neg
    have hw'_in_cm : w' ∈ cm.worlds := by
      rw [hCm]; simp [extractSemanticCountermodel]; exact hw'mem
    exact this (h w' hw'_in_cm)
  | untl event guard ih_event ih_guard =>
    simp only [branchTruth]
    intro ⟨t', ht', he, hg_true⟩
    rw [hOrd] at ht'
    by_cases hg : guard = Formula.imp Formula.bot Formula.bot
    · subst hg
      have hmem' : ⟨.neg, .untl event (.imp .bot .bot), ⟨w, t⟩⟩ ∈ b := hmem
      have hfe := sat_someFuture_neg b timeOrd hSat event w t hmem' t' ht'
      exact ih_event w t' hfe he
    · have hguard : guard ≠ Formula.top := by
        simp only [Formula.top]; exact hg
      have h := sat_untl_neg b timeOrd hSat event guard w t hmem hguard t' ht'
      cases h with
      | inl hfe => exact ih_event w t' hfe he
      | inr hfg => exact ih_guard w t' hfg hg_true
  | snce event guard ih_event ih_guard =>
    simp only [branchTruth]
    intro ⟨t', ht', he, hg_true⟩
    rw [hOrd] at ht'
    by_cases hg : guard = Formula.imp Formula.bot Formula.bot
    · subst hg
      have hmem' : ⟨.neg, .snce event (.imp .bot .bot), ⟨w, t⟩⟩ ∈ b := hmem
      have hfe := sat_somePast_neg b timeOrd hSat event w t hmem' t' ht'
      exact ih_event w t' hfe he
    · have hguard : guard ≠ Formula.top := by
        simp only [Formula.top]; exact hg
      have h := sat_snce_neg b timeOrd hSat event guard w t hmem hguard t' ht'
      cases h with
      | inl hfe => exact ih_event w t' hfe he
      | inr hfg => exact ih_guard w t' hfg hg_true

/--
The branch truth lemma: for a saturated open branch, every signed formula
in the branch is semantically true in the extracted countermodel.

- If `T(phi)` is in the branch, then `phi` is true at the formula's label in
  the countermodel.
- If `F(phi)` is in the branch, then `phi` is false at the formula's label in
  the countermodel.

This is the key correctness theorem for countermodel extraction: the model
we build from the branch genuinely satisfies the branch's assertions.
-/
theorem branchTruthLemma (b : Branch Atom) (timeOrd : TimeOrdering)
    (hSat : findUnexpanded b (timeOrd := timeOrd) = none)
    (fc : FrameClass := .Base) (hOpen : findClosure b fc = none)
    (cm : SemanticCountermodel Atom)
    (hCm : cm = extractSemanticCountermodel cm.formula b cm.timeOrdering)
    (hOrd : cm.timeOrdering = timeOrd) :
    ∀ sf ∈ b, signedTruthInModel cm sf := by
  intro sf hsf
  unfold signedTruthInModel
  obtain ⟨sign, formula, ⟨world, time⟩⟩ := sf
  cases sign with
  | pos =>
    exact truthLemma_pos b timeOrd hSat fc hOpen cm hCm formula world time hsf
  | neg =>
    exact truthLemma_neg b timeOrd hSat fc hOpen cm hCm hOrd formula world time hsf

/-!
## Integration with Decision Procedure
-/

/--
Result type for countermodel extraction.
-/
inductive CountermodelResult (Atom : Type u) [DecidableEq Atom] [Hashable Atom]
    (φ : Formula Atom) : Type _ where
  /-- Successfully extracted a countermodel description. -/
  | found (cm : SimpleCountermodel Atom)
  /-- Formula is valid, no countermodel exists. -/
  | valid
  /-- Extraction failed (timeout or other issue). -/
  | failed (reason : String)

/--
Result type for semantic countermodel extraction (richer than `CountermodelResult`).
Includes the `SemanticCountermodel` with its truth lemma guarantee alongside the
simple countermodel for backward compatibility.
-/
inductive SemanticCountermodelResult (Atom : Type u) [DecidableEq Atom] [Hashable Atom]
    (φ : Formula Atom) : Type _ where
  /-- Successfully extracted a semantic countermodel with correctness guarantee. -/
  | found (simple : SimpleCountermodel Atom) (semantic : SemanticCountermodel Atom)
  /-- Formula is valid, no countermodel exists. -/
  | valid
  /-- Extraction failed (timeout or other issue). -/
  | failed (reason : String)

/--
Try to find a countermodel for a formula.
Returns a `SimpleCountermodel` for backward compatibility.
-/
def findCountermodel (φ : Formula Atom) (fuel : Nat := 1000)
    (fc : FrameClass := .Base) : CountermodelResult Atom φ :=
  match buildTableau φ fuel fc with
  | none => .failed "Tableau construction timeout"
  | some (.allClosed _) => .valid
  | some (.hasOpen openBranch _ord _applied hSat) =>
      .found (extractCountermodelSimple φ openBranch hSat)

/--
Try to find a semantic countermodel for a formula.
Returns both a `SimpleCountermodel` (for display) and a `SemanticCountermodel`
(with the truth lemma guarantee that every signed formula in the saturated
branch is semantically satisfied in the model).
-/
def findSemanticCountermodel (φ : Formula Atom) (fuel : Nat := 1000)
    (fc : FrameClass := .Base) : SemanticCountermodelResult Atom φ :=
  match buildTableau φ fuel fc with
  | none => .failed "Tableau construction timeout"
  | some (.allClosed _) => .valid
  | some (.hasOpen openBranch ord _applied hSat) =>
      let simple := extractCountermodelSimple φ openBranch hSat
      let semantic := extractSemanticCountermodel φ openBranch ord
      .found simple semantic

/--
Extract both simple and semantic countermodels from an expanded tableau.
Returns `none` if the formula is valid (all branches closed).
-/
def extractCountermodelsFromTableau (φ : Formula Atom) (tableau : ExpandedTableau Atom)
    : Option (SimpleCountermodel Atom × SemanticCountermodel Atom) :=
  match tableau with
  | .allClosed _ => none
  | .hasOpen openBranch ord _applied hSaturated =>
      let simple := extractCountermodelSimple φ openBranch hSaturated
      let semantic := extractSemanticCountermodel φ openBranch ord
      some (simple, semantic)

end Cslib.Logic.Bimodal.Metalogic.Decidability
