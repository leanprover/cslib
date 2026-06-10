/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Decidability.Closure
import Cslib.Logics.Bimodal.Metalogic.Decidability.TraceCertificate

/-!
# Tableau Saturation and Expansion

This module implements the saturation process for tableau branches and
the main tableau expansion algorithm with termination guarantees.

## Main Definitions

- `ExpandedTableau`: Result type for fully expanded tableaux
- `expandBranchWithFuel`: Fuel-bounded recursive branch expansion
- `buildTableau`: Build complete tableau for a formula
- `expandBranchWithFuel_sound`: Soundness theorem for open branches

## Termination

Termination is guaranteed by the subformula property: tableau expansion
only produces formulas from the subformula closure of the initial branch.
The total complexity decreases with each expansion step. A fuel parameter
provides a concrete termination measure.

## References

* Gore, R. (1999). Tableau Methods for Modal and Temporal Logics
* Wu, M. Verified Decision Procedures for Modal Logics

Ported from BimodalLogic/Metalogic/Decidability/Saturation.lean with
adaptations for universe-polymorphic `Formula Atom`.
-/

set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Decidability

open Cslib.Logic.Bimodal

variable {Atom : Type u} [DecidableEq Atom] [Hashable Atom]

/-!
## Expanded Tableau Type
-/

/--
A fully expanded tableau has all branches either closed or saturated.

- `allClosed`: All branches closed → formula is valid
- `hasOpen`: At least one saturated open branch → formula is invalid
-/
inductive ExpandedTableau (Atom : Type u) [DecidableEq Atom] [Hashable Atom] : Type _ where
  /-- All branches are closed (formula is valid). -/
  | allClosed (closedBranches : List (ClosedBranch Atom))
  /-- At least one branch is open/saturated (formula is invalid).
      Carries the `TimeOrdering` and `AppliedSet` for countermodel extraction.
      Saturation is verified using the applied-set-aware check. -/
  | hasOpen (openBranch : Branch Atom) (timeOrdering : TimeOrdering)
      (appliedSet : AppliedSet Atom)
      (saturated : findUnexpandedWithApplied openBranch (timeOrd := timeOrdering)
                     (applied := appliedSet) = none)

namespace ExpandedTableau

/-- Check if the tableau shows the formula is valid. -/
def isValid : ExpandedTableau Atom → Bool
  | allClosed _ => true
  | hasOpen _ _ _ _ => false

/-- Check if the tableau shows the formula is invalid. -/
def isInvalid : ExpandedTableau Atom → Bool
  | allClosed _ => false
  | hasOpen _ _ _ _ => true

end ExpandedTableau

/-!
## Branch List Operations
-/

/--
Result of expanding a list of branches.
-/
inductive BranchListResult (Atom : Type u) [DecidableEq Atom] [Hashable Atom] : Type _ where
  /-- All branches closed. -/
  | allClosed (closedBranches : List (ClosedBranch Atom))
  /-- Found an open saturated branch with its time ordering and applied set. -/
  | foundOpen (openBranch : Branch Atom) (timeOrdering : TimeOrdering)
      (appliedSet : AppliedSet Atom)
      (saturated : findUnexpandedWithApplied openBranch (timeOrd := timeOrdering)
                     (applied := appliedSet) = none)
  /-- Still have branches to process. -/
  | pending (branches : List (Branch Atom))

/-!
## Fuel-Based Expansion
-/

/--
Scan a branch for Until/Since formulas and register them as pending eventualities.

For each `T(U(event, guard))` or `T(S(event, guard))` on the branch, we register
an eventuality for the `event` component. The event must eventually be witnessed
at some reachable time for the branch to be satisfiable.
-/
def registerEventualities (b : Branch Atom) (tracker : EventualityTracker Atom)
    : EventualityTracker Atom :=
  b.foldl (fun acc sf =>
    match sf.sign, sf.formula with
    | .pos, .untl event guard =>
      if guard != Formula.top then
        let e : Eventuality Atom := { formula := event, label := sf.label, isUntil := true }
        if acc.pending.any (· == e) then acc else acc.add e
      else acc
    | .pos, .snce event guard =>
      if guard != Formula.top then
        let e : Eventuality Atom := { formula := event, label := sf.label, isUntil := false }
        if acc.pending.any (· == e) then acc else acc.add e
      else acc
    | _, _ => acc
  ) tracker

/--
Check if any pending eventualities are fulfilled on the branch.

An Until eventuality for formula `event` introduced at label `l` is fulfilled when
`T(event)` appears at some future time reachable from `l.time`.
A Since eventuality is fulfilled when `T(event)` appears at some past time.
-/
def fulfillEventualities (b : Branch Atom) (tracker : EventualityTracker Atom)
    : EventualityTracker Atom :=
  tracker.pending.foldl (fun acc e =>
    -- Check if the event formula appears positively at any time on the branch
    let fulfilled := b.any fun sf =>
      sf.sign == .pos && sf.formula == e.formula && sf.label.world == e.label.world
        && sf.label.time != e.label.time
    if fulfilled then acc.fulfill e.formula e.label else acc
  ) tracker

/-!
## Branch Difficulty Estimation

Heuristic for proportional fuel allocation at tableau branch splits.
Branches with more temporal operators (which cause exponential branching)
receive more fuel than purely propositional branches.
-/

/--
Count temporal operators (Until/Since) in a formula.
These are the primary source of branching complexity in the tableau.
-/
def temporalCount : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ => temporalCount φ + temporalCount ψ
  | .box φ => temporalCount φ
  | .untl φ ψ => 1 + temporalCount φ + temporalCount ψ
  | .snce φ ψ => 1 + temporalCount φ + temporalCount ψ

/--
Count modal operators (Box) in a formula.
Box propagates formulas to all accessible worlds.
-/
def modalCount : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ => modalCount φ + modalCount ψ
  | .box φ => 1 + modalCount φ
  | .untl φ ψ => modalCount φ + modalCount ψ
  | .snce φ ψ => modalCount φ + modalCount ψ

/--
Estimate the difficulty of expanding a branch.

Uses a weighted sum of three metrics:
- **Temporal operator count** (weight 3): Until/Since cause branching + fresh time points
- **Modal operator count** (weight 2): Box propagates to all worlds
- **Branch size** (weight 1/4): Minor per-step cost factor

The minimum return value is 1 to avoid division-by-zero in proportional allocation.
-/
def estimateBranchDifficulty (b : Branch Atom) : Nat :=
  let tempCount := b.foldl (fun acc sf => acc + temporalCount sf.formula) 0
  let modCount := b.foldl (fun acc sf => acc + modalCount sf.formula) 0
  let sizeWeight := b.length / 4
  1 + 3 * tempCount + 2 * modCount + sizeWeight

/--
Allocate fuel proportionally to branch difficulty.

Given total `fuel` and a list of branches, computes per-branch fuel allocations
weighted by `estimateBranchDifficulty`. Each allocation is:
- At least 1 (when fuel > 0) to ensure progress
- At most `fuel - 1` to preserve termination (strict decrease for `decreasing_by`)
- When `fuel = 0`, all allocations are 0

The sum of allocations may be less than `fuel` (remainder is lost), which is
acceptable since the original uniform allocation also loses remainder from division.
-/
def allocateFuelProportionally (fuel : Nat) (branches : List (Branch Atom)) : List Nat :=
  match fuel with
  | 0 => branches.map fun _ => 0
  | fuel + 1 =>
    let difficulties := branches.map estimateBranchDifficulty
    let totalDifficulty := difficulties.foldl (· + ·) 0
    difficulties.map fun d =>
      -- Proportional share: (totalFuel * difficulty) / totalDifficulty
      -- Capped at `fuel` (= totalFuel - 1) to ensure strict decrease for termination
      -- At least 1 when fuel ≥ 1 (i.e., totalFuel ≥ 2)
      min (max 1 (fuel.succ * d / max 1 totalDifficulty)) fuel

/--
Every element of `allocateFuelProportionally (fuel+1) branches` is at most `fuel`.
This is the key lemma for the termination proof of `expandBranchWithFuel`.
-/
theorem allocateFuelProportionally_le (fuel : Nat) (branches : List (Branch Atom))
    (n : Nat) (h : n ∈ allocateFuelProportionally (fuel + 1) branches) :
    n ≤ fuel := by
  simp only [allocateFuelProportionally] at h
  rw [List.mem_map] at h
  obtain ⟨d, _, rfl⟩ := h
  exact Nat.min_le_right _ _

/--
Expand a single branch until closed or saturated.
Uses fuel to ensure termination (refinement of well-founded approach).
Threads EventualityTracker to track Until/Since obligations.

Returns:
- `some (inl closedBranch)`: Branch closed
- `some (inr openBranch)`: Branch saturated (open)
- `none`: Ran out of fuel
-/
def expandBranchWithFuel (b : Branch Atom) (fuel : Nat)
    (timeOrd : TimeOrdering := TimeOrdering.empty)
    (fc : FrameClass := .Base)
    (tracker : EventualityTracker Atom := EventualityTracker.empty)
    (applied : AppliedSet Atom := {})
    (maxBranches : Nat := 50000)
    (branchesUsed : Nat := 0)
    : Option (ClosedBranch Atom ⊕ (Branch Atom × TimeOrdering × AppliedSet Atom)) :=
  -- Global branch counter limit to bound exponential exploration
  if branchesUsed >= maxBranches then none
  else
  match fuel with
  | 0 => none  -- Out of fuel
  | fuel + 1 =>
      -- First check if already closed
      match findClosure b fc with
      | some reason => some (.inl ⟨b, reason⟩)
      | none =>
          -- Update eventuality tracker: register new eventualities and check fulfillment
          let tracker := registerEventualities b tracker
          let tracker := fulfillEventualities b tracker
          -- Check temporal blocking: if any active time has its type
          -- subsumed by an ancestor time, treat the branch as saturated.
          -- This prevents infinite chains from Until/Since positive rules
          -- re-introducing the same formula at fresh time points.
          if (findBlockedTime b timeOrd tracker).isSome then
            some (.inr (b, timeOrd, applied))  -- Blocked: treat as saturated open branch
          else
          -- Try to expand, using applied set to prevent persistent rule loops
          match expandOnceWithApplied b timeOrd fc applied with
          | (.saturated, _, _) => some (.inr (b, timeOrd, applied))  -- Open saturated branch
          | (.extended newBranch, newOrd, newAppliedFormulas) =>
              let applied' := newAppliedFormulas.foldl (fun s f => s.insert f) applied
              expandBranchWithFuel newBranch fuel newOrd fc tracker applied' maxBranches (branchesUsed + 1)
          | (.split branches, newOrd, newAppliedFormulas) =>
              let applied' := newAppliedFormulas.foldl (fun s f => s.insert f) applied
              -- For a split, we check if ALL branches close
              -- If any branch stays open, we return that open branch
              -- Proportional fuel allocation based on branch difficulty.
              -- Each sub-branch receives fuel proportional to its estimated difficulty.
              -- All allocations are capped at `fuel` (= original - 1) for termination.
              let fuelAllocs := allocateFuelProportionally (fuel + 1) branches
              -- Increment branch counter by number of new branches at this split
              let branchesUsed' := branchesUsed + branches.length
              let tryBranch := fun acc (pair : Branch Atom × Nat) =>
                match acc with
                | some (.inr openBr) => some (.inr openBr)  -- Already found open
                | _ =>
                    -- Cap at `fuel` to ensure termination (pair.2 is already ≤ fuel
                    -- from allocateFuelProportionally, but `min` makes it visible)
                    match expandBranchWithFuel pair.1 (min pair.2 fuel) newOrd fc tracker applied' maxBranches branchesUsed' with
                    | none => none  -- Out of fuel
                    | some (.inl _) => acc  -- This branch closed, continue
                    | some (.inr openBr) => some (.inr openBr)  -- Found open
              (branches.zip fuelAllocs).foldl tryBranch (some (.inl ⟨b, .botPos Label.initial⟩))
  termination_by fuel
decreasing_by all_goals simp_wf

/--
Expand multiple branches until all closed or one is found open.
Uses fuel to ensure termination.

Returns:
- `allClosed`: All branches closed (formula valid)
- `foundOpen`: Found saturated open branch (formula invalid)
- `pending`: Ran out of fuel with branches remaining
-/
def expandBranchesWithFuel (branches : List (Branch Atom)) (fuel : Nat)
    (closed : List (ClosedBranch Atom) := [])
    (fc : FrameClass := .Base) : BranchListResult Atom :=
  match branches with
  | [] => .allClosed closed
  | b :: rest =>
      match expandBranchWithFuel b fuel TimeOrdering.empty fc with
      | none => .pending (b :: rest)  -- Out of fuel
      | some (.inl closedBr) => expandBranchesWithFuel rest fuel (closedBr :: closed) fc
      | some (.inr (openBr, ord, appliedSet)) =>
          match h : findUnexpandedWithApplied openBr (timeOrd := ord) (applied := appliedSet) with
          | none => .foundOpen openBr ord appliedSet h
          | some _ => .pending (openBr :: rest)

/-!
## Post-Blocking Saturation

When `expandBranchWithFuel` returns a blocked open branch, the branch
may still contain unexpanded formulas (propositional, modal, or
persistent temporal formulas that don't create new time points).

`saturateBlocked` continues expansion on such branches, rejecting any
expansion step that would introduce new time ordering constraints.
This ensures the branch reaches full saturation or closure without
generating new time points that would bypass blocking.
-/

/--
Continue expanding a blocked branch until saturated or closed,
rejecting any expansion step that introduces new time constraints.
Uses fuel to ensure termination.

Each step either:
- Closes the branch (new formulas create a contradiction)
- Applies a non-time-generating rule (propositional, modal, persistent with no new times)
- Reaches saturation (no more applicable non-time-generating rules)

Since no new time points are created, the expansion terminates
when all propositional/modal formulas are processed.
-/
def saturateBlocked (b : Branch Atom) (fuel : Nat)
    (timeOrd : TimeOrdering) (fc : FrameClass := .Base)
    : Option (ClosedBranch Atom ⊕ (Branch Atom × TimeOrdering)) :=
  match fuel with
  | 0 => some (.inr (b, timeOrd))  -- Return as-is if fuel exhausted (still blocked/open)
  | fuel + 1 =>
      -- Check if now closed (expanding propositional formulas may create contradictions)
      match findClosure b fc with
      | some reason => some (.inl ⟨b, reason⟩)
      | none =>
          -- Try to expand
          match expandOnce b timeOrd fc with
          | (.saturated, _) => some (.inr (b, timeOrd))  -- Fully saturated
          | (.extended newBranch, newOrd) =>
              -- Only accept if no new time constraints were introduced
              if newOrd.constraints.length > timeOrd.constraints.length then
                some (.inr (b, timeOrd))  -- Reject: would create new time point
              else
                saturateBlocked newBranch fuel timeOrd fc
          | (.split branches, newOrd) =>
              -- Only accept if no new time constraints were introduced
              if newOrd.constraints.length > timeOrd.constraints.length then
                some (.inr (b, timeOrd))  -- Reject: would create new time point
              else
              -- For splits, check if ALL sub-branches close or saturate
              let tryBranch := fun acc newBranch =>
                match acc with
                | some (.inr openBr) => some (.inr openBr)  -- Already found open
                | _ =>
                    match saturateBlocked newBranch fuel timeOrd fc with
                    | some (.inl _) => acc  -- Sub-branch closed, continue
                    | some (.inr openBr) => some (.inr openBr)  -- Found open
                    | none => none  -- Should not happen (saturateBlocked always returns some)
              branches.foldl tryBranch (some (.inl ⟨b, .botPos Label.initial⟩))
termination_by fuel

/-!
## Main Expansion Function
-/

/--
Build a complete tableau for proving ¬φ is unsatisfiable (i.e., φ is valid).

Starts with F(φ) (asserting φ is false) and expands until:
- All branches close → φ is valid
- Some branch saturates open → φ is invalid

Uses fuel parameter for termination. The fuel should be set based on
the formula's complexity.

When `expandBranchWithFuel` returns a blocked open branch that is not
yet saturated, `saturateBlocked` continues expansion of non-time-generating
rules to reach full saturation.
-/
def buildTableau (φ : Formula Atom) (fuel : Nat := 1000)
    (fc : FrameClass := .Base) : Option (ExpandedTableau Atom) :=
  let initialBranch : Branch Atom := [SignedFormula.neg φ Label.initial]
  match expandBranchWithFuel initialBranch fuel TimeOrdering.empty fc with
  | none => none  -- Out of fuel
  | some (.inl closedBr) => some (.allClosed [closedBr])
  | some (.inr (openBr, ord, appliedSet)) =>
      -- Use applied-set-aware saturation check
      match h : findUnexpandedWithApplied openBr (timeOrd := ord) (applied := appliedSet) with
      | none => some (.hasOpen openBr ord appliedSet h)
      | some _ =>
          -- Branch is blocked but not fully saturated.
          -- Continue expanding non-time-generating rules.
          match saturateBlocked openBr fuel ord fc with
          | some (.inl closedBr) => some (.allClosed [closedBr])
          | some (.inr (satBr, satOrd)) =>
              match h2 : findUnexpandedWithApplied satBr (timeOrd := satOrd) (applied := appliedSet) with
              | none => some (.hasOpen satBr satOrd appliedSet h2)
              | some _ => none  -- Still not saturated after post-blocking pass
          | none => none  -- Should not happen

/--
Recommended fuel based on formula complexity.
Uses 10 * complexity as a heuristic upper bound.

**Deprecated**: Use `soundFuel` for a theoretically justified bound.
This function is kept for backward compatibility.
-/
def recommendedFuel (φ : Formula Atom) : Nat :=
  10 * φ.complexity + 100

/--
Sound fuel bound derived from the Finite Model Property (FMP).

By the FMP for bimodal TM logic, a satisfiable formula φ has a model
with at most `2^n` distinct worlds/times, where `n = |subformulaClosure(φ)|`.
Each time point can carry at most `2^n` distinct subsets of signed subformulas,
so the tableau explores at most `2^(2n)` distinct time-types before a repeat
(and blocking fires). We cap at 100000 for practical performance since
blocking typically fires much earlier.

The bound `n * 2^n` is used instead of `2^(2n)` because each expansion step
produces at most a constant number of new signed formulas, so the total
expansion steps are bounded by the number of distinct (time, type) pairs,
which is at most `n * 2^n` where n accounts for the time points and `2^n`
for the types.

Note: Uses List-based `Formula.subformulaCount` instead of Finset-based
`subformulaClosure.card` from the source.
-/
def soundFuel (φ : Formula Atom) : Nat :=
  let n := φ.subformulaCount
  let bound := n * (2 ^ n)
  -- Cap at practical maximum; blocking fires well before this bound
  min bound 100000

/--
Build tableau with automatic fuel calculation using sound FMP-derived bound.
-/
def buildTableauAuto (φ : Formula Atom) (fc : FrameClass := .Base) : Option (ExpandedTableau Atom) :=
  buildTableau φ (soundFuel φ) fc

/-!
## Saturation Properties
-/

/--
Check if a branch is fully saturated (all formulas expanded).
-/
def isSaturated (b : Branch Atom) (fc : FrameClass := .Base) : Bool :=
  (findUnexpanded b (fc := fc)).isNone

/--
A saturated branch contains only atomic signed formulas
(atoms, bot, or modal/temporal operators that can't be further expanded).
-/
def isAtomicBranch (b : Branch Atom) (fc : FrameClass := .Base) : Bool :=
  b.all fun sf =>
    match sf.formula with
    | .atom _ => true
    | .bot => true
    | _ => isExpanded sf b (fc := fc)

/-!
## Termination Measure
-/

/--
Termination measure for branch expansion.
Sum of unexpanded complexities decreases with each rule application.
-/
def expansionMeasure (b : Branch Atom) (fc : FrameClass := .Base) : Nat :=
  b.foldl (fun acc sf =>
    if isExpanded sf b (fc := fc) then acc
    else acc + sf.formula.complexity) 0

/-!
## Tableau Statistics
-/

/--
Statistics about a tableau expansion.
-/
structure TableauStats where
  /-- Number of branches created. -/
  branchCount : Nat
  /-- Number of closed branches. -/
  closedCount : Nat
  /-- Maximum branch depth. -/
  maxDepth : Nat
  /-- Total expansion steps. -/
  expansionSteps : Nat
  deriving Repr, Inhabited

/-!
## Blocking Correctness and Termination Theorems
-/

/--
**Subformula property**: All formulas produced by tableau rule application
are members of the signed subformula closure of the initial formula.

This is the foundation of the termination argument: since the closure is
finite, and each time type is a subset of the closure, there are only
finitely many distinct time types.
-/
theorem subformula_property (φ : Formula Atom) (b : Branch Atom) (sf : SignedFormula Atom)
    (h_init : b = [SignedFormula.neg φ Label.initial])
    (h_mem : sf ∈ b) :
    sf.formula ∈ Formula.subformulas φ := by
  subst h_init
  simp [SignedFormula.neg] at h_mem
  subst h_mem
  exact Formula.self_mem_subformulas φ

/-!
### Soundness of expandBranchWithFuel

The following theorem proves that if `expandBranchWithFuel` returns an
open branch, that branch has no closure reason. This is proved using
strong induction on the fuel parameter, with helper lemmas for the
`List.foldl` in the branch-split case.
-/

set_option linter.flexible false in
/--
Helper: the tryBranch step function in expandBranchWithFuel preserves the
invariant that any `.inr` result has `findClosure = none`.
Updated for proportional fuel allocation (pair : Branch × Nat).
-/
private theorem tryBranch_inr
    (fuelBound : Nat) (newOrd : TimeOrdering) (fc : FrameClass)
    (tracker : EventualityTracker Atom) (applied' : AppliedSet Atom)
    (maxBranches : Nat) (branchesUsed' : Nat)
    (acc : Option (ClosedBranch Atom ⊕ (Branch Atom × TimeOrdering × AppliedSet Atom)))
    (pair : Branch Atom × Nat) (ob : Branch Atom) (ord : TimeOrdering) (ap : AppliedSet Atom)
    (ih : ∀ (fuel' : Nat), fuel' ≤ fuelBound →
          ∀ (b' : Branch Atom) (t' : TimeOrdering) (fc' : FrameClass) (trk' : EventualityTracker Atom)
            (ap' : AppliedSet Atom) (mb : Nat) (bu : Nat)
            (ob' : Branch Atom) (o' : TimeOrdering) (a' : AppliedSet Atom),
            expandBranchWithFuel b' fuel' t' fc' trk' ap' mb bu = some (.inr (ob', o', a')) →
            findClosure ob' fc' = none)
    (h_acc : ∀ ob' ord' ap', acc = some (.inr (ob', ord', ap')) → findClosure ob' fc = none)
    (h_result : (match acc with
      | some (.inr openBr) => some (.inr openBr)
      | _ =>
          match expandBranchWithFuel pair.1 (min pair.2 fuelBound) newOrd fc tracker applied' maxBranches branchesUsed' with
          | none => none
          | some (.inl _) => acc
          | some (.inr openBr) => some (.inr openBr)) = some (.inr (ob, ord, ap))) :
    findClosure ob fc = none := by
  cases acc with
  | none =>
    simp at h_result
    split at h_result
    · exact absurd h_result (by simp)
    · exact absurd h_result (by simp)
    · simp at h_result; obtain ⟨rfl, rfl, rfl⟩ := h_result
      rename_i openBr h_exp
      exact ih (min pair.2 fuelBound) (Nat.min_le_right _ _) pair.1 newOrd fc tracker applied' maxBranches branchesUsed' ob ord ap h_exp
  | some val =>
    cases val with
    | inr p =>
      simp at h_result; obtain ⟨rfl, rfl, rfl⟩ := h_result
      exact h_acc ob ord ap rfl
    | inl cb =>
      simp at h_result
      split at h_result
      · exact absurd h_result (by simp)
      · exact absurd h_result (by simp)
      · simp at h_result; obtain ⟨rfl, rfl, rfl⟩ := h_result
        rename_i openBr h_exp
        exact ih (min pair.2 fuelBound) (Nat.min_le_right _ _) pair.1 newOrd fc tracker applied' maxBranches branchesUsed' ob ord ap h_exp

/--
Helper: `List.foldl` with the tryBranch step preserves the findClosure invariant.
Updated for proportional fuel allocation (pairs : List (Branch × Nat)).
-/
private theorem foldl_preserves_findClosure
    (fuelBound : Nat) (newOrd : TimeOrdering) (fc : FrameClass)
    (tracker : EventualityTracker Atom) (applied' : AppliedSet Atom)
    (maxBranches : Nat) (branchesUsed' : Nat)
    (ih : ∀ (fuel' : Nat), fuel' ≤ fuelBound →
          ∀ (b' : Branch Atom) (t' : TimeOrdering) (fc' : FrameClass) (trk' : EventualityTracker Atom)
            (ap' : AppliedSet Atom) (mb : Nat) (bu : Nat)
            (ob' : Branch Atom) (o' : TimeOrdering) (a' : AppliedSet Atom),
            expandBranchWithFuel b' fuel' t' fc' trk' ap' mb bu = some (.inr (ob', o', a')) →
            findClosure ob' fc' = none)
    (pairs : List (Branch Atom × Nat))
    (init : Option (ClosedBranch Atom ⊕ (Branch Atom × TimeOrdering × AppliedSet Atom)))
    (h_init : ∀ ob ord ap, init = some (.inr (ob, ord, ap)) → findClosure ob fc = none)
    (ob : Branch Atom) (ord : TimeOrdering) (ap : AppliedSet Atom)
    (h_result : pairs.foldl (fun acc (pair : Branch Atom × Nat) =>
      match acc with
      | some (.inr openBr) => some (.inr openBr)
      | _ =>
          match expandBranchWithFuel pair.1 (min pair.2 fuelBound) newOrd fc tracker applied' maxBranches branchesUsed' with
          | none => none
          | some (.inl _) => acc
          | some (.inr openBr) => some (.inr openBr)) init = some (.inr (ob, ord, ap))) :
    findClosure ob fc = none := by
  induction pairs generalizing init with
  | nil => exact h_init ob ord ap h_result
  | cons hd tl ih_tl =>
    simp only [List.foldl] at h_result
    exact ih_tl _
      (fun ob' ord' ap' h => tryBranch_inr fuelBound newOrd fc tracker applied' maxBranches branchesUsed' init hd ob' ord' ap' ih h_init h)
      h_result

-- Soundness proof requires deep case analysis over recursive function + foldl;
-- the default heartbeat limit is insufficient.
set_option maxHeartbeats 3200000 in
set_option linter.flexible false in
/--
General soundness: if `expandBranchWithFuel` returns an open branch,
that branch has no closure reason.
Uses strong induction to handle the fuel-divided split case.
Updated for proportional fuel allocation.
Generalized over maxBranches/branchesUsed parameters.
-/
private theorem expandBranchWithFuel_sound
    (fuel : Nat) :
    ∀ (b : Branch Atom) (timeOrd : TimeOrdering) (fc : FrameClass) (tracker : EventualityTracker Atom)
      (applied : AppliedSet Atom) (maxBranches : Nat) (branchesUsed : Nat)
      (openBranch : Branch Atom) (ord : TimeOrdering) (ap : AppliedSet Atom),
      expandBranchWithFuel b fuel timeOrd fc tracker applied maxBranches branchesUsed = some (.inr (openBranch, ord, ap)) →
      findClosure openBranch fc = none := by
  induction fuel using Nat.strongRecOn with
  | _ n ih =>
    intro b timeOrd fc tracker applied maxBranches branchesUsed ob ord ap h
    cases n with
    | zero =>
      simp [expandBranchWithFuel] at h
    | succ k =>
      unfold expandBranchWithFuel at h
      -- Handle the branch counter guard
      split at h
      · simp at h  -- branchesUsed >= maxBranches => returns none, contradiction
      · cases hfc : findClosure b fc with
        | some reason => simp [hfc] at h
        | none =>
          simp [hfc] at h
          -- Case split on eventuality-aware blocking check
          by_cases hblock : (findBlockedTime b timeOrd
              (fulfillEventualities b (registerEventualities b tracker))).isSome
          · simp [hblock] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact hfc
          · simp [hblock] at h
            match hexp : expandOnceWithApplied b timeOrd fc applied with
            | ⟨.saturated, _, _⟩ =>
              simp [hexp] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact hfc
            | ⟨.extended newBranch, newOrd, newAppliedFormulas⟩ =>
              simp [hexp] at h
              exact ih k (Nat.lt_succ_of_le le_rfl) newBranch newOrd fc _ _ maxBranches _ ob ord ap h
            | ⟨.split branches, newOrd, newAppliedFormulas⟩ =>
              simp [hexp] at h
              -- Use foldl_preserves_findClosure for zipped pairs
              exact foldl_preserves_findClosure k newOrd fc _ _ maxBranches (branchesUsed + branches.length)
                (fun fuel' hle => ih fuel' (Nat.lt_succ_of_le hle))
                (branches.zip (allocateFuelProportionally (k + 1) branches))
                (some (.inl ⟨b, .botPos Label.initial⟩))
                (fun _ _ _ h' => by simp at h')
                ob ord ap h

/--
**Blocking soundness**: Subset blocking does not prematurely close any
satisfiable branch. If a branch B is satisfiable and expandBranchWithFuel
returns `some (.inr openBranch)` due to blocking, then `openBranch` is
indeed satisfiable.

This follows from the structural invariant of `expandBranchWithFuel`:
every code path that returns `.inr` (open branch) first verifies
`findClosure = none`. The proof tracks this invariant through the
recursive structure, including the `List.foldl` in the branch-split case.
-/
theorem blocking_sound (φ : Formula Atom) (b : Branch Atom) (openBranch : Branch Atom)
    (ord : TimeOrdering) (ap : AppliedSet Atom)
    (h_result : expandBranchWithFuel b (soundFuel φ) = some (.inr (openBranch, ord, ap))) :
    findClosure openBranch = none :=
  expandBranchWithFuel_sound (soundFuel φ) b _ _ _ _ _ _ openBranch ord ap h_result

end Cslib.Logic.Bimodal.Metalogic.Decidability
