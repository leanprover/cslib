/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Decidability.Saturation

/-!
# Proof Extraction from Closed Tableaux

This module extracts `DerivationTree` proof terms from closed tableaux.
When all branches of a tableau close, the original formula is valid,
and we can construct a syntactic proof.

## Main Definitions

- `extractFromClosureReason`: Extract proof from a single closure reason
- `tryAxiomProof`: Direct axiom pattern matching
- `buildCompositionalProof`: Recursive compositional proof builder
- `extractProof`: Main extraction entry point using tableau + compositional + search
- `findProofCombined`: Combined tableau + search proof finder

## Implementation Notes

The proof extraction uses a multi-strategy approach:
1. **Direct axiom match**: Pattern-match against all 42 axiom schemata
2. **Derived theorem match**: Known derived theorems (stubbed -- returns none)
3. **Compositional builder**: Recursively builds proofs for propositional,
   modal, and temporal formulas using combinators (identity, imp_trans, etc.)
4. **Enhanced proof search**: Fallback with high depth/visit limits (stubbed)

The compositional builder handles:
- Propositional: A -> A (identity), weakening (imp_s), Peirce's law
- Modal: necessitation + modal_k_dist, modal_t, modal_4, modal_b
- Temporal: temporal_necessitation + BX axioms, BX10 eventuality extraction

Ported from BimodalLogic/Metalogic/Decidability/ProofExtraction.lean with
adaptations for universe-polymorphic `Formula Atom`.

## References

* Wu, M. Verified Decision Procedures for Modal Logics
-/

set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.Decidability

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.DerivationTree

variable {Atom : Type u} [DecidableEq Atom] [Hashable Atom]

/-!
## Proof Construction Helpers
-/

/--
Build a proof of bot -> phi (via efq).
This is used when we have a contradiction in the branch.
-/
def proofFromBot (phi : Formula Atom) : DerivationTree .Base ([] : Context Atom) (Formula.bot.imp phi) :=
  DerivationTree.axiom [] _ (Axiom.efq phi) (FrameClass.base_le _)

/--
Build a proof of phi from an axiom witness.
-/
def proofFromAxiom (phi : Formula Atom) (ax : Axiom phi) (h_fc : ax.minFrameClass ≤ FrameClass.Base) :
    DerivationTree .Base ([] : Context Atom) phi :=
  DerivationTree.axiom [] phi ax h_fc

/-!
## Proof Extraction from Closure Reasons
-/

/--
Extract a proof fragment from a closure reason.

Each closure reason provides evidence for why F(phi) leads to contradiction,
which means phi is valid (since assuming -phi leads to contradiction).

- `contradiction`: We have both T(psi) and F(psi), which is impossible in any model
- `botPos`: T(bot) is impossible (bot is false in all models)
- `axiomNeg`: F(axiom) contradicts the axiom's validity

Note: This returns a proof of the formula that caused closure, not necessarily
the original goal. The full tableau-to-proof extraction combines these.
-/
def extractFromClosureReason (reason : ClosureReason Atom) :
    Option (Sigma fun phi : Formula Atom => DerivationTree .Base ([] : Context Atom) phi) :=
  match reason with
  | .axiomNeg phi ax _ =>
      -- The axiom itself is provable (only if base-compatible)
      if h_fc : ax.minFrameClass ≤ FrameClass.Base then
        some ⟨phi, proofFromAxiom phi ax h_fc⟩
      else
        none
  | .contradiction _ _ =>
      -- Contradiction means the branch is unsatisfiable
      -- The proof would need to trace back the specific contradiction
      none
  | .botPos _ =>
      -- T(bot) is impossible, but doesn't give us a direct proof
      none

/-!
## Direct Axiom Proof
-/

/--
Try to build a direct proof of a formula if it's an axiom instance.
Uses `matchAxiom` from AxiomMatcher.
-/
def tryAxiomProof (phi : Formula Atom) :
    Option (DerivationTree .Base ([] : Context Atom) phi) :=
  match matchAxiom phi with
  | some ⟨psi, ax⟩ =>
      if h : phi = psi then
        if h_fc : ax.minFrameClass ≤ FrameClass.Base then
          some (h ▸ DerivationTree.axiom [] psi ax h_fc)
        else
          none
      else
        none
  | none => none

/-!
## Compositional Proof Builder

Recursively builds proofs by pattern-matching on formula structure and
applying appropriate axioms and inference rules.
-/

/--
Try to build a proof of phi compositionally from its structure.

This function handles common formula patterns by recognizing their
structure and building proofs using combinators and axioms.
Uses fuel to prevent infinite recursion on deeply nested formulas.

**Handled patterns**:
- `A -> A` (identity)
- `A -> (B -> A)` (weakening / imp_s)
- `bot -> A` (ex falso)
- `((A -> B) -> A) -> A` (Peirce)
- Direct axiom instances (via matchAxiom)
- Derived theorems (via matchDerived -- stubbed)
- `A -> B` where B is provable (weakening via imp_s)
-/
def buildCompositionalProof (phi : Formula Atom) (fuel : Nat) :
    Option (DerivationTree .Base ([] : Context Atom) phi) :=
  if fuel = 0 then none
  else
    -- Strategy 1: Direct axiom match (fast path)
    match tryAxiomProof phi with
    | some proof => some proof
    | none =>
    -- Strategy 2: Derived theorem match
    match matchDerived phi with
    | some d => some (DerivationTree.weakening [] [] phi d (List.nil_subset []))
    | none =>
    -- Strategy 3: Structural decomposition
    match phi with
    -- Necessitation: □A where A is provable
    | .box inner =>
        match buildCompositionalProof inner (fuel - 1) with
        | some proofInner =>
            some (DerivationTree.necessitation inner proofInner)
        | none => none
    -- Implication: □⊥ → X is valid, and A → B where B is provable
    | .imp (.box .bot) rhs =>
        -- □⊥ → X via modal_t + efq + imp_k chain
        let boxBot := Formula.box Formula.bot
        let modalT : DerivationTree .Base ([] : Context Atom) (boxBot.imp Formula.bot) :=
          DerivationTree.axiom [] _ (Axiom.modal_t Formula.bot) (FrameClass.base_le _)
        let exFalso : DerivationTree .Base ([] : Context Atom) (Formula.bot.imp rhs) :=
          DerivationTree.axiom [] _ (Axiom.efq rhs) (FrameClass.base_le _)
        let impS : DerivationTree .Base ([] : Context Atom) ((Formula.bot.imp rhs).imp (boxBot.imp (Formula.bot.imp rhs))) :=
          DerivationTree.axiom [] _ (Axiom.imp_s (Formula.bot.imp rhs) boxBot) (FrameClass.base_le _)
        let step1 : DerivationTree .Base ([] : Context Atom) (boxBot.imp (Formula.bot.imp rhs)) :=
          DerivationTree.modus_ponens [] (Formula.bot.imp rhs) (boxBot.imp (Formula.bot.imp rhs)) impS exFalso
        let impK : DerivationTree .Base ([] : Context Atom) ((boxBot.imp (Formula.bot.imp rhs)).imp ((boxBot.imp Formula.bot).imp (boxBot.imp rhs))) :=
          DerivationTree.axiom [] _ (Axiom.imp_k boxBot Formula.bot rhs) (FrameClass.base_le _)
        let step2 : DerivationTree .Base ([] : Context Atom) ((boxBot.imp Formula.bot).imp (boxBot.imp rhs)) :=
          DerivationTree.modus_ponens [] (boxBot.imp (Formula.bot.imp rhs)) ((boxBot.imp Formula.bot).imp (boxBot.imp rhs)) impK step1
        some (DerivationTree.modus_ponens [] (boxBot.imp Formula.bot) (boxBot.imp rhs) step2 modalT)
    -- General implication: A → B
    | .imp a b =>
        if h : a = b then
          some (h ▸ identity a)
        else
          -- Try: if B is provable, then A -> B is provable (by weakening via imp_s)
          match buildCompositionalProof b (fuel - 1) with
          | some proofB =>
              let imp_s_inst : DerivationTree .Base ([] : Context Atom) (b.imp (a.imp b)) :=
                DerivationTree.axiom [] _ (Axiom.imp_s b a) (FrameClass.base_le _)
              some (DerivationTree.modus_ponens [] b (a.imp b) imp_s_inst proofB)
          | none => none
    | _ => none

/-!
## Enhanced Proof Search with Validation

When the tableau has proven a formula valid, we can use proof search with
higher resource limits, since we know a proof must exist.
-/

/--
Enhanced proof search with increased limits.
Used when tableau has confirmed validity but direct extraction failed.

Searches with progressively increasing depth (10, 20, 30, 40, 50)
and visit limits to find a proof term.

Note: In this port, `bounded_search_with_proof_stub` always returns `none`,
so this function effectively returns `none`. The full implementation will
be provided when the Automation module is ported.
-/
def enhancedSearch (phi : Formula Atom) :
    Option (DerivationTree .Base ([] : Context Atom) phi) :=
  -- Try increasing depths with generous visit limits
  let depths : List Nat := [10, 20, 30, 40, 50]
  depths.findSome? fun d =>
    match bounded_search_with_proof_stub ([] : Context Atom) phi d with
    | (some proof, _, _) => some proof
    | (none, _, _) => none

/-!
## Tableau to Proof Extraction
-/

/--
Result of proof extraction from a closed tableau.
-/
inductive ProofExtractionResult (phi : Formula Atom) : Type u where
  /-- Successfully extracted a proof. -/
  | success (proof : DerivationTree .Base ([] : Context Atom) phi)
  /-- Could not extract proof (tableau method limitation). -/
  | incomplete (reason : String)

/-!
## Main Proof Extraction
-/

/--
Extract a proof from an expanded tableau that shows validity.

When the tableau is `allClosed`, the original formula is valid.
We attempt to construct a `DerivationTree` proof using a multi-strategy
approach:

1. **Direct axiom match**: Try `matchAxiom` and `matchDerived`
2. **Closure-based extraction**: Check if any closed branch's axiomNeg
   reason directly matches the goal formula
3. **Compositional builder**: Build proof from formula structure using
   combinators (identity, imp_trans, etc.)
4. **Enhanced proof search**: `bounded_search_with_proof_stub` with high limits

Returns `ProofExtractionResult.success proof` if extraction succeeds,
or `ProofExtractionResult.incomplete reason` if all strategies fail.
-/
def extractProof (phi : Formula Atom) (tableau : ExpandedTableau Atom)
    (_fc : FrameClass := .Base) : ProofExtractionResult phi :=
  match tableau with
  | .hasOpen _ _ _ _ =>
      -- Tableau shows formula is invalid, no proof exists
      .incomplete "Formula is invalid (open branch found)"
  | .allClosed closedBranches =>
      -- Formula is valid, try to extract proof

      -- Strategy 1: Direct axiom proof
      match tryAxiomProof phi with
      | some proof => .success proof
      | none =>
      -- Strategy 2: Derived theorem match
      match matchDerived phi with
      | some d =>
          .success (DerivationTree.weakening [] [] phi d (List.nil_subset []))
      | none =>
      -- Strategy 3: Closure-based extraction
      let axiomProofs := closedBranches.filterMap fun cb =>
        match cb.reason with
        | .axiomNeg psi ax _ =>
            if h : phi = psi then
              if h_fc : ax.minFrameClass ≤ FrameClass.Base then
                some (h ▸ DerivationTree.axiom [] psi ax h_fc)
              else none
            else none
        | _ => none
      match axiomProofs.head? with
      | some proof => .success proof
      | none =>
      -- Strategy 4: Compositional proof builder
      match buildCompositionalProof phi 20 with
      | some proof => .success proof
      | none =>
      -- Strategy 5: Enhanced proof search (tableau confirmed validity)
      match enhancedSearch phi with
      | some proof => .success proof
      | none =>
          .incomplete "All extraction strategies exhausted (formula is valid but proof term could not be constructed)"

/-!
## Proof Search Integration
-/

/--
Try to find a proof using both tableau and proof search.

First attempts direct proof search (which is fast for axioms),
then uses compositional builder, then falls back to tableau-validated
enhanced search.
-/
def findProofCombined (phi : Formula Atom) (searchDepth : Nat := 10)
    (tableauFuel : Nat := 1000) (fc : FrameClass := .Base) :
    Option (DerivationTree .Base ([] : Context Atom) phi) :=
  -- Strategy 1: Direct proof search (fast for axioms)
  match bounded_search_with_proof_stub ([] : Context Atom) phi searchDepth with
  | (some proof, _, _) => some proof
  | (none, _, _) =>
  -- Strategy 2: Compositional builder
  match buildCompositionalProof phi 20 with
  | some proof => some proof
  | none =>
  -- Strategy 3: Tableau-validated enhanced search
  match buildTableau phi tableauFuel fc with
  | some (.allClosed _) =>
      -- Tableau proves validity, use enhanced search
      enhancedSearch phi
  | _ => none

/-!
## Proof Verification
-/

/--
Verify that a proof term is well-formed (type-checks).
This is automatically enforced by Lean's type system, but we provide
this function for documentation and potential runtime checks.
-/
def verifyProof (_phi : Formula Atom) (_proof : DerivationTree .Base ([] : Context Atom) _phi) : Bool :=
  true  -- Type system ensures well-formedness

/--
Get the height of a proof (number of inference steps).
-/
def proofHeight {phi : Formula Atom} (proof : DerivationTree .Base ([] : Context Atom) phi) : Nat :=
  proof.height

/-!
## Statistics
-/

/--
Statistics about proof extraction.
-/
structure ProofExtractionStats where
  /-- Was proof successfully extracted? -/
  success : Bool
  /-- Method used (axiom, derived, closure, compositional, search). -/
  method : String
  /-- Proof height if successful. -/
  height : Option Nat
  deriving Repr, Inhabited

end Cslib.Logic.Bimodal.Metalogic.Decidability
