# Implementation Plan: Task #42 -- Port Tableau Decision Procedure

- **Task**: 42 - Port core tableau-based decision procedure to Cslib
- **Status**: [NOT STARTED]
- **Effort**: 20 hours
- **Dependencies**: None (Tasks 4, 7 completed; Task 43 FMP deferred)
- **Research Inputs**: specs/042_port_bimodal_tableau_core/reports/01_tableau-core-research.md
- **Artifacts**: plans/01_tableau-core-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Port the 8-file tableau-based decision procedure (~6,066 lines) from BimodalLogic to Cslib/Logics/Bimodal/Metalogic/Decidability/. The source resides at `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Decidability/` and is sorry-free. The critical transformation is adapting from monomorphic `Formula` (concrete `Atom` struct) to Cslib's universe-polymorphic `Formula Atom` with `{Atom : Type u}`. Additionally, a minimal AxiomMatcher prerequisite must be created to replace the Automation.ProofSearch.Core dependency (~1,195 lines), and TraceCertificate must be ported since Saturation and DecisionProcedure import it. The FMP-dependent theorems in Correctness.lean are deferred to Task 43.

### Research Integration

Key findings from the research report (01_tableau-core-research.md):
- Actual line counts differ significantly from task description estimates (e.g., SignedFormula 935 vs 400, Saturation 1,563 vs 800)
- Three critical missing dependencies: Automation.ProofSearch.Core, SubformulaClosure.Closure, Theorems.Combinators
- The `matchAxiom` function (~390 lines in Core.lean) is the only part of ProofSearch needed for Closure and ProofExtraction
- Normalization.normalizeFormula is definitionally the identity -- trivially replaceable
- TraceCertificate (303 lines) must be ported since Saturation imports it (for traced parallel implementations)
- Source uses `maxHeartbeats 3200000` in Saturation.lean -- heartbeat risk with Lean 4.31
- The `Decidable (ThDerivable phi)` instance uses classical logic (`Classical.em`), not a constructive instance
- Correctness.lean: `decide_sound` and `validity_decidable` are FMP-independent; `fmp_completeness` depends on Task 43

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Port all 8 core decidability files plus TraceCertificate (9 files total)
- Create minimal AxiomMatcher.lean to replace ProofSearch.Core dependency
- Adapt all code to universe-polymorphic `Formula Atom` type
- Achieve zero sorry across all ported files
- Pass `lake build` for the Decidability module
- Produce the classical decidability theorem: `validity_decidable (phi : Formula Atom) : (Valid phi) ∨ ¬(Valid phi)`

**Non-Goals**:
- Port the full Automation/ProofSearch infrastructure (~3,000 lines) -- use minimal stubs
- Port TraceExport.lean (depends on DataExport, optional instrumentation)
- Port FMP module (Task 43 scope)
- Port FMP-dependent theorems in Correctness.lean (`fmp_completeness`, `fmp_incompleteness_witness`, `countermodel_size_bound`)
- Port `#eval` test sections that require concrete atom types
- Achieve a constructive `Decidable` instance (source uses classical logic)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe polymorphism elaboration failures in large match expressions (applyRule, 952 lines) | H | M | Add explicit type annotations; split into helper functions if needed |
| Heartbeat pressure from `maxHeartbeats 3200000` proofs (Saturation, CountermodelExtraction) | H | M | Use `set_option maxHeartbeats 4000000`; refactor large proofs if needed |
| Lean 4.27 -> 4.31 API changes breaking List/Option lemmas | M | M | Use lean_loogle/lean_leansearch to find renamed lemmas |
| matchAxiom extraction difficulty -- tightly coupled to ProofSearch.Core | M | L | The function is self-contained (pattern-matching only); extraction is straightforward |
| BEq/LawfulBEq/Hashable instances missing for `Formula Atom` | M | M | Derive or construct manually; Cslib already has `DecidableEq` and `BEq` |
| TraceCertificate StateM layer complicating Saturation port | L | L | Traced implementations are parallel; port types only, skip traced functions if blocking |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |
| 5 | 6, 7 | 5 |
| 6 | 8 | 6, 7 |

Phases within the same wave can execute in parallel.

---

### Phase 1: SignedFormula -- Foundation Types [COMPLETED]

**Goal**: Port the core type definitions (Sign, SignedFormula, Branch, Label, EventualityTracker, TimeOrdering, BlockingState, subformulaClosure) that all other files depend on.

**Tasks**:
- [x] Create directory `Cslib/Logics/Bimodal/Metalogic/Decidability/`
- [x] Create `SignedFormula.lean` with copyright header and module declaration
- [x] Port `Label` structure (WorldIndex, TimeIndex, Label) with `DecidableEq, BEq, Hashable` instances
- [x] Port `Sign` inductive (`pos`, `neg`) with `Repr, DecidableEq, BEq, Hashable` instances
- [x] Port `SignedFormula` structure with `sign`, `formula`, `label` fields -- parameterize by `{Atom : Type*}` with `[DecidableEq Atom]` and `[Hashable Atom]`
- [x] Port `Branch` type alias (`List (SignedFormula Atom)`) and helper functions (`hasPos`, `hasNeg`, `hasPosAt`, `hasNegAt`)
- [x] Port `Formula.complexity` function (recursive structural complexity measure) *(deviation: altered -- simplified complexity measure without pattern-aware derived-connective cases from source; later phases can add if needed)*
- [x] Port `Formula.subformulas` function (List-based subformula collection)
- [x] Port `subformulaClosure` function (List-based closure used by Saturation for fuel bound)
- [x] Port `EventualityTracker` structure and `TimeOrdering` type
- [x] Port `BlockingState` and subset blocking functions
- [ ] Port `AppliedSet` type (`Std.HashSet`) and helper operations *(deviation: deferred to task Phase 2 -- AppliedSet is defined in Tableau.lean in source, not SignedFormula.lean)*
- [x] Add `Hashable` instance for `Formula Atom` if not already present (required for `AppliedSet`)
- [x] Update namespace from `Bimodal.Metalogic.Decidability` to `Cslib.Logic.Bimodal.Metalogic.Decidability`
- [x] Open correct Cslib namespaces (`Cslib.Logic.Bimodal`)
- [x] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.SignedFormula`

**Timing**: 2.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/SignedFormula.lean` - New file (port ~935 lines)
- `lakefile.lean` or module import file - Add new module to build

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.SignedFormula` succeeds
- Zero sorry in the file
- All types and functions from source are present (Sign, SignedFormula, Branch, Label, etc.)

---

### Phase 2: Tableau Rules + TraceCertificate [COMPLETED]

**Goal**: Port the 28 tableau expansion rules, the rule application engine, and the TraceCertificate types needed by Saturation/DecisionProcedure.

**Tasks**:
- [x] Create `TraceCertificate.lean` with copyright header
- [x] Port `TraceEntry` inductive type (ruleFired, branchCreated, branchClosed, fuelExhausted, blocked)
- [x] Port `CertOutcome` inductive type
- [x] Port `ProofCertificate` structure and `ProofCertificate.empty`
- [x] Port `TraceFailure` and `TraceResult` types
- [x] Port `TraceM` monad abbreviation (`StateM ProofCertificate`)
- [x] Port `TraceM.record`, `TraceM.getCert`, `TraceM.recordRuleFired` helpers
- [x] Adapt all types for universe-polymorphic `Formula Atom`
- [x] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.TraceCertificate`
- [x] Create `Tableau.lean` with copyright header
- [x] Port `TableauRule` inductive (30 rules including diamondPos/diamondNeg) *(deviation: altered -- 30 rules not 28; source has diamond rules as separate constructors)*
- [x] Port `RuleResult` inductive (linear, branching)
- [x] Port formula decomposition helpers used by `applyRule`
- [x] Port `applyRule` function (large match expression ~950 lines) -- no maxHeartbeats needed
- [x] Port `expandOnce` / `expandOnceWithApplied` functions
- [x] Port `findUnexpanded` / `findUnexpandedWithApplied` functions
- [x] Port `findApplicableRule` / `findApplicableRuleWithApplied` functions
- [ ] Port `ClosedBranch` type *(deviation: skipped -- ClosedBranch is defined in Closure.lean in source, not Tableau.lean; deferred to Phase 3)*
- [x] Adapt all to universe-polymorphic `Formula Atom`
- [x] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.Tableau`
- [x] Port `ClosureReason` inductive type in TraceCertificate.lean *(deviation: altered -- moved from Closure.lean to TraceCertificate.lean since TraceCertificate needs it and Closure is Phase 3)*

**Timing**: 3.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/TraceCertificate.lean` - New file (port ~303 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` - New file (port ~1,190 lines)

**Verification**:
- `lake build` for both files succeeds
- Zero sorry
- All 28 tableau rules present in `TableauRule`
- `applyRule` handles all rule cases

---

### Phase 3: AxiomMatcher + Closure [COMPLETED]

**Goal**: Create the minimal AxiomMatcher prerequisite (extracting `matchAxiom` from ProofSearch.Core) and port Closure.lean which depends on it.

**Tasks**:
- [x] Create `AxiomMatcher.lean` with copyright header
- [x] Extract `matchAxiom` function from source ProofSearch/Core.lean (lines 314-660 approx) -- this is a pure pattern-matching function that checks all 42 axiom schemata
- [x] Adapt `matchAxiom` to universe-polymorphic `Formula Atom` -- requires `[DecidableEq Atom]` for structural equality checks *(deviation: altered -- renamed source axiom constructors prop_k->imp_k, prop_s->imp_s, ex_falso->efq to match Cslib naming)*
- [x] Create stub `matchDerived` function that returns `none` (full derived theorem matching deferred)
- [x] Create stub `bounded_search_with_proof` that returns `(none, 0, 0)` (full proof search deferred) *(deviation: altered -- named `bounded_search_with_proof_stub` to avoid name collision with source)*
- [x] Create `identity` combinator (`A -> A` proof from prop_k + prop_s axioms) -- needed by ProofExtraction
- [x] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.AxiomMatcher`
- [x] Create `Closure.lean` with copyright header
- [x] Port `ClosureReason` inductive (contradiction, botPos, axiomNeg) *(deviation: altered -- imported from TraceCertificate.lean instead of redefining, as already ported in Phase 2)*
- [x] Port `checkBotPos`, `checkContradiction`, `checkAxiomNeg` functions
- [x] Port `findClosure` and `isClosed`/`isOpen` functions
- [x] Port `ClosedBranch` structure (if not already in Tableau)
- [x] Port monotonicity lemmas (findClosure subset lemmas)
- [x] Port `axiomNegCount` helper *(deviation: altered -- named `countNegatedAxioms` matching source; also ported `countPotentialContradictions`)*
- [x] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.Closure`

**Timing**: 2.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/AxiomMatcher.lean` - New file (~400 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Closure.lean` - New file (port ~398 lines)

**Verification**:
- `lake build` for both files succeeds
- Zero sorry
- `matchAxiom` correctly matches at least the propositional and modal axiom patterns
- `findClosure` detects contradiction, botPos, and axiomNeg closure reasons

---

### Phase 4: Saturation [COMPLETED]

**Goal**: Port the saturation process -- the core tableau expansion algorithm with fuel-bounded termination, including `expandBranchWithFuel`, `buildTableau`, and the `expandBranchWithFuel_sound` soundness theorem. Skip `#eval` test sections and traced implementations.

**Tasks**:
- [x] Create `Saturation.lean` with copyright header *(completed)*
- [x] Port `ExpandedTableau` inductive (allClosed, hasOpen) with applied-set-aware saturation check *(completed)*
- [x] Port `ExpansionResult` type (if separate from Tableau.lean) *(deviation: skipped -- ExpansionResult already defined in Tableau.lean, not duplicated)*
- [x] Port `allocateFuelProportionally` function and its `allocate_sum_le` termination lemma *(completed)*
- [x] Port `expandBranchWithFuel` function -- the main recursive expansion with `termination_by fuel` *(completed)*
- [x] Port `expandBranchWithFuel_sound` soundness theorem (the largest proof in the file) *(completed)*
- [x] Port `buildTableau` wrapper function *(completed)*
- [x] Port `soundFuel` function (computes adequate fuel from subformula closure size) -- use List-based closure from SignedFormula instead of Finset *(deviation: altered -- uses Formula.subformulaCount instead of Finset.card)*
- [x] Port `blocking_sound` theorem (if present and non-FMP) *(completed)*
- [x] Skip `#eval` test sections (lines ~687-930) -- require concrete atoms *(completed -- skipped as planned)*
- [x] Skip traced implementations (`expandBranchWithFuel_tracedImpl`, `expandOneStep_tracedImpl`) -- parallel implementations not needed for correctness *(completed -- skipped as planned)*
- [x] Handle `maxHeartbeats` for large proofs -- use `set_option maxHeartbeats 4000000` as needed *(deviation: altered -- 3200000 was sufficient, same as source)*
- [x] Adapt all to universe-polymorphic `Formula Atom` *(completed)*
- [x] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.Saturation` *(completed -- zero sorry, build passes)*

**Timing**: 3.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Saturation.lean` - New file (port ~700 lines of proof + skip ~860 lines of tests/traces)

**Verification**:
- `lake build` succeeds
- Zero sorry
- `expandBranchWithFuel` compiles with termination proof
- `buildTableau` returns `Option ExpandedTableau`
- `expandBranchWithFuel_sound` compiles (the critical soundness theorem)

---

### Phase 5: CountermodelExtraction [COMPLETED]

**Goal**: Port the countermodel extraction module that builds finite countermodels from open (saturated) tableau branches, including the `branchTruthLemma` correctness theorem.

**Tasks**:
- [x] Create `CountermodelExtraction.lean` with copyright header *(completed)*
- [x] Port `SimpleCountermodel` structure (atom truth/false tracking) *(completed)*
- [x] Port `extractCountermodelSimple` / `extractSimpleCountermodel` function *(completed)*
- [x] Port `SemanticCountermodel` structure (full finite model with worlds, times, ordering, valuation) *(completed)*
- [x] Port `branchTruth` recursive truth evaluation function *(completed)*
- [x] Port `extractSemanticCountermodel` function *(completed)*
- [x] Port saturation invariants (`sat_no_bot_pos`, `sat_no_contradiction`, `sat_and_pos`, `sat_or_neg`, `sat_imp_neg`, `sat_neg_pos`, `sat_neg_neg`, `sat_box_pos`, `sat_box_neg`, `sat_all_future_pos`, `sat_all_future_neg`, `sat_all_past_pos`, `sat_all_past_neg`, `sat_untl_pos`, `sat_untl_neg`, `sat_snce_pos`, `sat_snce_neg`) *(deviation: altered -- ported the subset of invariants actually present in the source: sat_no_bot_pos, sat_no_contradiction, sat_atom_consistent, sat_imp_neg, sat_box_pos, sat_box_neg, sat_untl_pos, sat_snce_pos, sat_some_future_neg, sat_some_past_neg, sat_untl_neg, sat_snce_neg; the plan listed some invariants (sat_and_pos, sat_or_neg, etc.) that do not exist in the source file)*
- [x] Port `branchTruthLemma` -- the main correctness theorem proving semantic correctness of extracted countermodel *(completed)*
- [x] Handle `maxHeartbeats` for structural induction proofs *(completed -- same maxHeartbeats as source: 1600000 for sat_box_pos, 800000 for untlPos/sncePos not_expanded, 3200000 for sat_some_future_neg/sat_some_past_neg/sat_untl_neg/sat_snce_neg)*
- [x] Adapt all to universe-polymorphic `Formula Atom` *(completed -- required proving Formula.beq_top_false_of_ne helper for BEq lawfulness since auto-derived BEq on Formula Atom lacks LawfulBEq instance)*
- [x] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.CountermodelExtraction` *(completed -- zero sorry, zero axioms, builds clean)*

**Timing**: 3 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean` - New file (port ~1,090 lines)

**Verification**:
- `lake build` succeeds
- Zero sorry
- `branchTruthLemma` compiles (the critical correctness theorem)
- `extractSimpleCountermodel` produces `SimpleCountermodel` from saturated branches

---

### Phase 6: ProofExtraction [NOT STARTED]

**Goal**: Port the proof extraction module that builds `DerivationTree` proof terms from closed tableaux, using the AxiomMatcher stubs for unavailable automation functions.

**Tasks**:
- [ ] Create `ProofExtraction.lean` with copyright header
- [ ] Port `proofFromBot` and `proofFromAxiom` helper functions
- [ ] Port `extractFromClosureReason` function
- [ ] Port `tryAxiomProof` function (uses `matchAxiom`)
- [ ] Port `buildCompositionalProof` function -- uses `matchAxiom`, `matchDerived` (stubbed), and the `identity` combinator
- [ ] Port `ExtractionResult` type (success/incomplete)
- [ ] Port `extractProof` entry point -- the multi-strategy proof extraction using tableau + compositional + search
- [ ] Port `findProofCombined` function -- uses `bounded_search_with_proof` (stubbed) + tableau
- [ ] Replace `open Bimodal.Theorems.Combinators` with inline `identity` construction or import from AxiomMatcher
- [ ] Replace `open Bimodal.Automation` with import of AxiomMatcher
- [ ] Adapt all to universe-polymorphic `Formula Atom`
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.ProofExtraction`

**Timing**: 1.5 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/ProofExtraction.lean` - New file (port ~354 lines)

**Verification**:
- `lake build` succeeds
- Zero sorry
- `extractProof` returns `ExtractionResult` from `ExpandedTableau`
- Proof extraction works for axiom-instance formulas via `tryAxiomProof`

---

### Phase 7: DecisionProcedure [NOT STARTED]

**Goal**: Port the main decision procedure that ties together tableau construction, proof extraction, and countermodel extraction into a single `decide` function.

**Tasks**:
- [ ] Create `DecisionProcedure.lean` with copyright header
- [ ] Port `DecisionResult` inductive (valid, invalid, timeout) parameterized by formula
- [ ] Port `DecisionResult` namespace helpers (isValid, isInvalid, isTimeout, getProof?, getCountermodel?)
- [ ] Port `decide` function -- replace `Automation.Normalization.normalizeFormula` with identity (since Cslib also uses `abbrev` for derived connectives, normalization is definitionally id)
- [ ] Inline the normalization identity: replace `have h_norm : normalizeFormula phi = phi` with `rfl` or equivalent
- [ ] Replace `bounded_search_with_proof` call with stub that returns `(none, 0, 0)` (fast-path search deferred)
- [ ] Port `isValid` and `isSatisfiable` convenience functions
- [ ] Skip `decideOptimized` (depends on `Strategies.search`) and `decideWithTrace` (traced variant)
- [ ] Skip `#eval` test sections
- [ ] Adapt all to universe-polymorphic `Formula Atom`
- [ ] Verify `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.DecisionProcedure`

**Timing**: 1.5 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/DecisionProcedure.lean` - New file (port ~200 lines core, skip ~189 lines traced/optimized)

**Verification**:
- `lake build` succeeds
- Zero sorry
- `decide` function compiles and returns `DecisionResult`
- `DecisionResult` has valid/invalid/timeout constructors

---

### Phase 8: Correctness + Module Integration [NOT STARTED]

**Goal**: Port the non-FMP correctness theorems (`decide_sound`, `validity_decidable`, `decide_result_exclusive`) and integrate all modules into the Cslib build.

**Tasks**:
- [ ] Create `Correctness.lean` with copyright header
- [ ] Port `decide_sound` theorem -- `(phi : Formula Atom) -> (d : Deriv phi) -> Valid phi` using Soundness module
- [ ] Port `decide_sound'` variant (extracts proof from DecisionResult.valid)
- [ ] Port `validity_decidable` theorem using `Classical.em`
- [ ] Port `validity_has_decision_procedure` theorem
- [ ] Port `decide_result_exclusive` theorem
- [ ] Add comment block marking FMP-dependent theorems as deferred to Task 43: `fmp_completeness`, `fmp_incompleteness_witness`, `countermodel_size_bound`
- [ ] Create `Decidability.lean` barrel file importing all sub-modules
- [ ] Update parent module imports (add Decidability to Metalogic module tree)
- [ ] Run full `lake build` to verify all modules compile together
- [ ] Verify zero sorry across all 10 new files (SignedFormula, TraceCertificate, Tableau, AxiomMatcher, Closure, Saturation, CountermodelExtraction, ProofExtraction, DecisionProcedure, Correctness)
- [ ] Verify namespace consistency: all definitions under `Cslib.Logic.Bimodal.Metalogic.Decidability`

**Timing**: 2 hours

**Depends on**: 6, 7

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Correctness.lean` - New file (port ~100 lines, defer ~47 lines FMP-dependent)
- `Cslib/Logics/Bimodal/Metalogic/Decidability.lean` - New barrel file
- Parent module imports (if applicable)

**Verification**:
- `lake build` succeeds for entire project
- Zero sorry across all Decidability files
- `validity_decidable` theorem compiles: `(phi : Formula Atom) : (Valid phi) ∨ ¬(Valid phi)`
- `decide_sound` theorem compiles
- `decide_result_exclusive` theorem compiles

## Testing & Validation

- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.SignedFormula` compiles
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.TraceCertificate` compiles
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.Tableau` compiles
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.AxiomMatcher` compiles
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.Closure` compiles
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.Saturation` compiles
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.CountermodelExtraction` compiles
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.ProofExtraction` compiles
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.DecisionProcedure` compiles
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.Correctness` compiles
- [ ] Full `lake build` succeeds with zero errors
- [ ] `grep -r "sorry" Cslib/Logics/Bimodal/Metalogic/Decidability/` returns empty
- [ ] All key theorems present: `decide_sound`, `validity_decidable`, `decide_result_exclusive`, `branchTruthLemma`, `expandBranchWithFuel_sound`

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/Metalogic/Decidability/SignedFormula.lean` - Foundation types
- `Cslib/Logics/Bimodal/Metalogic/Decidability/TraceCertificate.lean` - Trace instrumentation types
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` - 28 expansion rules
- `Cslib/Logics/Bimodal/Metalogic/Decidability/AxiomMatcher.lean` - Minimal axiom pattern-matching (new)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Closure.lean` - Branch closure detection
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Saturation.lean` - Tableau expansion + soundness
- `Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean` - Countermodel extraction + correctness
- `Cslib/Logics/Bimodal/Metalogic/Decidability/ProofExtraction.lean` - Proof term extraction
- `Cslib/Logics/Bimodal/Metalogic/Decidability/DecisionProcedure.lean` - Main decide function
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Correctness.lean` - Soundness + classical decidability
- `Cslib/Logics/Bimodal/Metalogic/Decidability.lean` - Module barrel file

## Rollback/Contingency

- If universe polymorphism causes intractable elaboration in `applyRule`: split the large match into helper functions per rule category (propositional, modal, temporal)
- If heartbeat limits are exceeded in `expandBranchWithFuel_sound` or `branchTruthLemma`: increase `maxHeartbeats` to 6400000, refactor proof into sub-lemmas if still failing
- If `Hashable (Formula Atom)` cannot be derived cleanly: switch `AppliedSet` from `Std.HashSet` to `List` with dedup (performance regression but functionally correct)
- If TraceCertificate port blocks Saturation: remove the TraceCertificate import and skip all traced implementations (they are parallel to the core algorithm)
- Full rollback: `git checkout -- Cslib/Logics/Bimodal/Metalogic/Decidability/` removes all new files
