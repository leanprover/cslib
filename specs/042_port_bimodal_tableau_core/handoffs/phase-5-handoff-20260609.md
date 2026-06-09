# Phase 5 Handoff: CountermodelExtraction

## Status
Phase 5 (CountermodelExtraction) completed successfully.

## What was done
- Ported CountermodelExtraction.lean (1,078 lines) from BimodalLogic source
- All structures: SimpleCountermodel, SemanticCountermodel, CountermodelResult, SemanticCountermodelResult
- All functions: extractTrueAtoms, extractFalseAtoms, extractSimpleCountermodel, extractCountermodelSimple, extractCountermodelFromTableau, branchTruth, signedTruthInModel, buildAtomValuation, extractSemanticCountermodel, findCountermodel, findSemanticCountermodel, extractCountermodelsFromTableau
- All saturation invariants: sat_no_bot_pos, sat_no_contradiction, sat_atom_consistent, sat_imp_neg, sat_box_pos, sat_box_neg, sat_untl_pos, sat_snce_pos, sat_some_future_neg, sat_some_past_neg, sat_untl_neg, sat_snce_neg
- The critical branchTruthLemma theorem (via truthLemma_pos and truthLemma_neg helpers)
- Time ordering helpers: isTimeOrderedBefore, isTimeOrderedAfter, futureTimes, pastTimes, timesBetween

## Key decision: BEq lawfulness
The auto-derived `BEq` on `Formula Atom` (from `deriving BEq`) does not have a `LawfulBEq` instance. The source code's `simp [hg]` approach for proving `(guard == Formula.top) = false` failed because `simp` cannot connect the auto-derived BEq to propositional equality. Solution: proved `Formula.beq_top_false_of_ne` via a general `eq_of_beq` lemma using structural induction with `dsimp [BEq.beq]` + `change` + `cases h` tactics.

## Key decision: findUnexpanded vs findUnexpandedWithApplied
The saturation invariants use `findUnexpanded` (not the applied-set-aware variant) as in the source. The ported `ExpandedTableau.hasOpen` carries `findUnexpandedWithApplied = none`. Integration will need bridging in later phases (6-8).

## Next action
Phase 6: ProofExtraction -- port proof extraction from closed tableaux.

## Build verification
- `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.CountermodelExtraction` passes
- Zero sorry, zero vacuous definitions, zero new axioms
- branchTruthLemma verified: uses only propext, Classical.choice, Quot.sound
