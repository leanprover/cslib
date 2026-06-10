/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Decidability.CountermodelExtraction
public import Cslib.Logics.Bimodal.Metalogic.Decidability.ProofExtraction
public import Cslib.Logics.Bimodal.Metalogic.Decidability.AxiomMatcher

/-!
# Decision Procedure for TM Bimodal Logic

This module provides the main decision procedure for TM bimodal logic validity.
The procedure decides whether a formula is valid, returning either:
- A proof term (`DerivationTree`) if valid
- A countermodel description if invalid

## Main Definitions

- `DecisionResult`: Sum type of proof or countermodel
- `decide`: Main decision function
- `isValid`, `isSatisfiable`: Boolean convenience functions

## Algorithm Overview

1. **Fast path**: Try direct axiom proof (matchAxiom)
2. **Fast path**: Try compositional proof builder
3. **Tableau**: Build tableau for F(φ) (asserting φ is false)
4. **Analysis**:
   - All branches close → φ is valid, extract proof
   - Open saturated branch → φ is invalid, extract countermodel

## Complexity

- Time: O(2^n) where n = formula complexity (PSPACE-complete)
- Space: O(n) for DFS-based tableau expansion
- Typical formulas: Much faster due to pruning and optimization

## References

* Gore, R. (1999). Tableau Methods for Modal and Temporal Logics
* Wu, M. Verified Decision Procedures for Modal Logics

Ported from BimodalLogic/Metalogic/Decidability/DecisionProcedure.lean with
adaptations for universe-polymorphic `Formula Atom`.

Proof extraction functions (`tryAxiomProof`, `buildCompositionalProof`,
`extractProof`, `ProofExtractionResult`) are imported from ProofExtraction.lean.
-/

set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Decidability

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.DerivationTree

variable {Atom : Type u} [DecidableEq Atom] [Hashable Atom]

/-!
## Decision Result Type
-/

/--
Result of the decision procedure for a formula.

- `valid`: Formula is valid, with a proof term
- `invalid`: Formula is invalid, with a countermodel description
- `timeout`: Procedure ran out of resources
-/
inductive DecisionResult (Atom : Type u) [DecidableEq Atom] [Hashable Atom]
    (φ : Formula Atom) : Type u where
  /-- Formula is valid, witnessed by a derivation tree. -/
  | valid (proof : DerivationTree FrameClass.Base ([] : Context Atom) φ)
  /-- Formula is invalid, witnessed by a countermodel description. -/
  | invalid (counter : SimpleCountermodel Atom)
  /-- Decision procedure timed out (fuel exhausted). -/
  | timeout

namespace DecisionResult

variable {φ : Formula Atom}

/-- Check if result indicates validity. -/
def isValid : DecisionResult Atom φ → Bool
  | valid _ => true
  | _ => false

/-- Check if result indicates invalidity. -/
def isInvalid : DecisionResult Atom φ → Bool
  | invalid _ => true
  | _ => false

/-- Check if result timed out. -/
def isTimeout : DecisionResult Atom φ → Bool
  | timeout => true
  | _ => false

/-- Get the proof if valid. -/
def getProof? : DecisionResult Atom φ →
    Option (DerivationTree FrameClass.Base ([] : Context Atom) φ)
  | valid proof => some proof
  | _ => none

/-- Get the countermodel if invalid. -/
def getCountermodel? : DecisionResult Atom φ → Option (SimpleCountermodel Atom)
  | invalid cm => some cm
  | _ => none

/-- Display the decision result as a human-readable string. -/
def display : DecisionResult Atom φ → String
  | valid proof => s!"Valid (proof height: {proof.height})"
  | invalid _ => "Invalid (countermodel found)"
  | timeout => "Timeout (resources exhausted)"

end DecisionResult

/-!
## Main Decision Procedure
-/

/--
Decide validity of a TM bimodal logic formula.

**Algorithm**:
1. Try direct axiom proof (fast path for axiom instances)
2. Try compositional proof builder (fast for structural patterns)
3. Build tableau starting with F(φ)
4. If all branches close: valid, try to extract proof
5. If open branch found: invalid, extract countermodel

**Parameters**:
- `φ`: Formula to decide
- `searchDepth`: Maximum depth for initial proof search (default 10)
- `tableauFuel`: Maximum steps for tableau expansion (default 1000)
- `fc`: Frame class for axiom compatibility (default Base)

**Returns**:
- `valid proof`: Formula is valid with proof term
- `invalid counter`: Formula is invalid with countermodel
- `timeout`: Resources exhausted before decision

**Note on normalization**: In the source BimodalLogic project,
`normalizeFormula` is definitionally the identity since all derived
connectives are `def` abbreviations. In Cslib, derived connectives are
likewise `abbrev`, so normalization is unnecessary and has been removed.
-/
def decide (φ : Formula Atom) (searchDepth : Nat := 10) (tableauFuel : Nat := 1000)
    (fc : FrameClass := .Base) : DecisionResult Atom φ :=
  -- Fast path: direct axiom proof
  match tryAxiomProof φ with
  | some proof => .valid proof
  | none =>
    -- Fast path: compositional proof (identity, weakening, etc.)
    match buildCompositionalProof φ 10 with
    | some proof => .valid proof
    | none =>
    -- Try bounded proof search stub (deferred; returns none)
    match (bounded_search_with_proof_stub ([] : Context Atom) φ searchDepth).1 with
    | some proof => .valid proof
    | none =>
      -- Fall back to tableau method
      match buildTableau φ tableauFuel fc with
      | none => .timeout
      | some tableau =>
          match tableau with
          | .allClosed _ =>
              -- Formula is valid, use extraction pipeline
              match extractProof φ tableau fc with
              | .success proof => .valid proof
              | .incomplete _ =>
                  -- Extraction failed despite validity; genuine resource limitation
                  .timeout
          | .hasOpen openBranch _ord _applied hSat =>
              -- Formula is invalid, extract countermodel
              .invalid (extractCountermodelSimple φ openBranch hSat)

/-!
## Convenience Functions
-/

/--
Simplified decision: just return whether formula is valid.
-/
def isValid (φ : Formula Atom) (fc : FrameClass := .Base) : Bool :=
  (decide φ (fc := fc)).isValid

/--
Check if a formula is satisfiable (its negation is not valid).
-/
def isSatisfiable (φ : Formula Atom) (fc : FrameClass := .Base) : Bool :=
  ¬isValid (Formula.neg φ) fc

/--
Decide with automatic fuel based on FMP-derived sound bound.

Uses `soundFuel` (from subformula closure cardinality) instead of the
ad-hoc `recommendedFuel` heuristic. Combined with subset blocking in
`expandBranchWithFuel`, this ensures termination for all formulas.
-/
def decideAuto (φ : Formula Atom) (fc : FrameClass := .Base) : DecisionResult Atom φ :=
  let fuel := soundFuel φ
  let depth := 5 + φ.complexity / 2
  decide φ depth fuel fc

/--
Check if a formula is a tautology (valid in propositional sense).
For TM logic, this is just validity check.
-/
def isTautology (φ : Formula Atom) (fc : FrameClass := .Base) : Bool := isValid φ fc

/--
Check if a formula is a contradiction (negation is valid).
-/
def isContradiction (φ : Formula Atom) (fc : FrameClass := .Base) : Bool :=
  isValid (Formula.neg φ) fc

/--
Check if a formula is contingent (neither valid nor contradictory).
-/
def isContingent (φ : Formula Atom) (fc : FrameClass := .Base) : Bool :=
  ¬isValid φ fc ∧ ¬isContradiction φ fc

end Cslib.Logic.Bimodal.Metalogic.Decidability
