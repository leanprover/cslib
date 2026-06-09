# Research Report: Task #42

**Task**: Port the core tableau-based decision procedure from BimodalLogic to Cslib
**Date**: 2026-06-09
**Target**: `Cslib/Logics/Bimodal/Metalogic/Decidability/`

## Summary

The source code resides at `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Decidability/` and comprises 8 core files totaling 6,066 lines (excluding TraceCertificate/TraceExport which are 524 lines of optional instrumentation). All source files are **sorry-free**. The port requires adapting from a concrete `Atom` type (monomorphic) to Cslib's universe-polymorphic `Formula Atom` type, renaming namespaces from `Bimodal.Metalogic.Decidability` to `Cslib.Logic.Bimodal.Metalogic.Decidability`, and handling several external dependencies that do not yet exist in Cslib.

## Source File Analysis

### File Inventory

| File | Lines | Key Definitions | Sorries |
|------|-------|----------------|---------|
| SignedFormula.lean | 935 | Sign, SignedFormula, Branch, Label, EventualityTracker, TimeOrdering, BlockingState, subformulaClosure | 0 |
| Tableau.lean | 1,190 | TableauRule (28 rules), RuleResult, applyRule, expandOnce, AppliedSet | 0 |
| Closure.lean | 398 | ClosureReason, findClosure, isClosed, monotonicity lemmas | 0 |
| Saturation.lean | 1,563 | ExpandedTableau, expandBranchWithFuel, buildTableau, soundFuel, expandBranchWithFuel_sound, blocking_sound, #eval tests | 0 |
| ProofExtraction.lean | 354 | extractProof, tryAxiomProof, buildCompositionalProof, enhancedSearch | 0 |
| CountermodelExtraction.lean | 1,090 | SimpleCountermodel, SemanticCountermodel, branchTruth, branchTruthLemma, saturation invariants | 0 |
| DecisionProcedure.lean | 389 | DecisionResult, decide, decideAuto, decideWithTrace | 0 |
| Correctness.lean | 147 | decide_sound, validity_decidable, fmp_completeness | 0 |
| **Total (core 8)** | **6,066** | | **0** |
| TraceCertificate.lean | 303 | ProofCertificate, TraceEntry, TraceM (optional) | 0 |
| TraceExport.lean | 221 | JSON export (optional, depends on DataExport) | 0 |

### Revised Line Estimates

The task description estimated ~5,700 lines across 8 files. The actual count is 6,066 for the core 8 (6,590 including TraceCertificate/TraceExport). The description's per-file estimates were significantly off in some cases:

| File | Estimated | Actual | Delta |
|------|-----------|--------|-------|
| SignedFormula | ~400 | 935 | +535 |
| Tableau | ~1,800 | 1,190 | -610 |
| Closure | ~600 | 398 | -202 |
| Saturation | ~800 | 1,563 | +763 |
| ProofExtraction | ~600 | 354 | -246 |
| Correctness | ~400 | 147 | -253 |
| DecisionProcedure | ~500 | 389 | -111 |
| CountermodelExtraction | ~600 | 1,090 | +490 |

## Dependency Graph

### Internal Dependencies (within Decidability/)

```
SignedFormula
    |
    v
Tableau
    |
    v
Closure -----> TraceCertificate
    |                |
    v                v
Saturation <--------'
    |          |
    v          v
ProofExtraction   CountermodelExtraction
    |                    |
    v                    v
DecisionProcedure <-----'
    |
    v
Correctness
```

### External Dependencies (outside Decidability/)

Each file's external imports and their Cslib status:

| Source Import | Cslib Equivalent | Status |
|---------------|-----------------|--------|
| `Bimodal.Syntax.Formula` | `Cslib.Logics.Bimodal.Syntax.Formula` | EXISTS |
| `Bimodal.ProofSystem` | `Cslib.Logics.Bimodal.ProofSystem.*` | EXISTS |
| `Bimodal.ProofSystem.Derivation` | `Cslib.Logics.Bimodal.ProofSystem.Derivation` | EXISTS |
| `Bimodal.Semantics` | `Cslib.Logics.Bimodal.Semantics.*` | EXISTS |
| `Bimodal.Metalogic.Soundness` | `Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness` | EXISTS |
| `Bimodal.Syntax.SubformulaClosure.Closure` | -- | **MISSING** (367 lines source) |
| `Bimodal.Automation.ProofSearch.Core` | -- | **MISSING** (1,195 lines source) |
| `Bimodal.Automation.ProofSearch.Strategies` | -- | **MISSING** (379 lines source) |
| `Bimodal.Automation.Normalization` | -- | **MISSING** (1,120 lines source) |
| `Bimodal.Automation.DataExport` | -- | **MISSING** (383 lines, TraceExport only) |
| `Bimodal.Metalogic.Decidability.FMP.FMP` | -- | **MISSING** (Task 43 scope) |
| `Bimodal.Theorems.Combinators` | -- | **MISSING** |

### Critical Missing Dependencies

**1. Automation.ProofSearch.Core** (used by Closure.lean, ProofExtraction.lean, DecisionProcedure.lean):
- Provides `matchAxiom : Formula -> Option (Sigma Axiom)` -- pattern-matches formulas against all 42 axiom schemata
- Provides `bounded_search_with_proof` -- proof search with depth limits
- Provides `matchDerived` -- matches known derived theorems
- Provides `Visited` type for proof search state
- **Impact**: Critical for Closure.lean (axiom negation check) and ProofExtraction/DecisionProcedure (proof term construction)

**2. Automation.ProofSearch.Strategies** (used by DecisionProcedure.lean):
- Provides `search` function with `SearchStrategy.IDDFS` -- iterative deepening search
- **Impact**: Used in `decideOptimized`, but can be deferred/stubbed

**3. Automation.Normalization** (used by DecisionProcedure.lean):
- Provides `normalizeFormula` -- definitionally the identity (all derived operators are `def` abbreviations)
- Provides `normalizeFormula_id` theorem
- **Impact**: Minimal -- can be replaced with a trivial identity since Cslib also uses `abbrev` for derived connectives

**4. Syntax.SubformulaClosure.Closure** (used by Saturation.lean):
- Provides `subformulaClosure : Formula -> Finset Formula` as a `Finset` (not `List`)
- Used in `soundFuel` for cardinality bound
- **Impact**: SignedFormula.lean already defines `Formula.subformulas` as a `List`. The `Finset` version is needed only for `soundFuel` -- can use `List.eraseDups.length` as a workaround

**5. Theorems.Combinators** (used by ProofExtraction.lean):
- Provides `identity : DerivationTree .Base [] (a.imp a)` combinator
- **Impact**: Can be constructed inline from `Axiom.prop_k` + `Axiom.prop_s`

**6. FMP.FMP** (used by Correctness.lean):
- Task 43 scope -- `fmp_contrapositive`, `mcs_finite_model_property`, `FilteredWorld.finite`
- **Impact**: Correctness.lean depends on this. The `decide_sound` and `validity_decidable` theorems do NOT depend on FMP. Only `fmp_completeness` and `fmp_incompleteness_witness` do.

## Namespace and API Changes

### Namespace Mapping

| Source | Target |
|--------|--------|
| `Bimodal.Metalogic.Decidability` | `Cslib.Logic.Bimodal.Metalogic.Decidability` |
| `Bimodal.Syntax` | `Cslib.Logic.Bimodal` |
| `Bimodal.ProofSystem` | `Cslib.Logic.Bimodal` |
| `Bimodal.Semantics` | `Cslib.Logic.Bimodal` |
| `Bimodal.Metalogic` | `Cslib.Logic.Bimodal.Metalogic` |
| `Bimodal.Automation` | (needs new module or inline) |
| `Bimodal.Theorems.Combinators` | (needs inline construction) |

### Type-Level Changes

**Key structural change**: Source uses monomorphic `Formula` (concrete `Atom` type); Cslib uses universe-polymorphic `Formula Atom` with `{Atom : Type u}`.

| Source | Target | Impact |
|--------|--------|--------|
| `Formula` | `Formula Atom` | All definitions need `variable {Atom : Type*}` or explicit parameter |
| `Atom` (concrete struct) | `Atom` (type parameter) | `Atom.mk_base "p"` in `#eval` tests must be removed or replaced |
| `Axiom φ` | `Axiom φ` (same shape) | Universe levels may differ |
| `DerivationTree .Base Γ φ` | `DerivationTree .Base Γ φ` (same shape) | Compatible |
| `⊢ φ` notation | `⊢ φ` notation | Compatible (both defined in ProofSystem) |
| `FrameClass` | `FrameClass` | Compatible (same constructors: Base, Dense, Discrete) |
| `Context` (= `List Formula`) | `Context Atom` (= `List (Formula Atom)`) | Parametric |

### API Differences

1. **BEq/LawfulBEq on Formula**: Source has `BEq Formula`, `LawfulBEq Formula`, `Hashable Formula`. Cslib derives `DecidableEq` and `BEq` but may not have `Hashable` or `LawfulBEq`. Needed for `AppliedSet := Std.HashSet SignedFormula`.

2. **Formula.complexity**: Source defines this in `Formula.lean`. Need to check if Cslib has it or if it needs porting.

3. **`native_decide`**: Used in source for `Sign.ReflBEq` instance. Should work in Cslib but may need verification with the newer Lean version.

4. **`Std.HashSet`**: Used for `AppliedSet`. Available in Lean 4.31 stdlib.

## Porting Risks

### High Risk

1. **Missing Automation.ProofSearch.Core (~1,195 lines)**: This is the most critical missing dependency. Closure.lean uses `matchAxiom` for axiom negation checking, and ProofExtraction/DecisionProcedure use proof search extensively. **Options**:
   - Port the full Automation module as a prerequisite (adds ~3,000 lines)
   - Factor out `matchAxiom` into a standalone file (~400 lines) and stub the rest
   - Rewrite Closure.lean to inline the axiom matching logic

2. **Universe polymorphism**: The source is monomorphic. Making everything universe-polymorphic is mostly mechanical but may trigger unexpected elaboration failures, especially in the large `applyRule` match expression (952 lines).

3. **Heartbeat pressure**: Source uses `maxHeartbeats 3200000` in Saturation.lean and CountermodelExtraction.lean. With Lean 4.31 vs 4.27, elaboration behavior may change. The 28-rule `applyRule` function and the `expandBranchWithFuel_sound` proof are the main risk areas.

### Medium Risk

4. **`#eval` test sections**: The source has extensive `#eval` tests in Saturation.lean (~450 lines) that use concrete atoms (`Atom.mk_base "p"`). These tests are valuable for correctness checking but require a concrete `Atom` type. **Options**:
   - Keep them with a local `Atom := String` specialization
   - Remove them (the proofs provide correctness guarantees)
   - Move them to a separate test file

5. **Correctness.lean depends on FMP (Task 43)**: The `fmp_completeness` and `fmp_incompleteness_witness` theorems require the FMP module. **Options**:
   - Port Correctness.lean partially (sound theorems only) and add FMP-dependent theorems later
   - Mark FMP-dependent theorems with sorry (violates zero-debt policy)
   - Defer Correctness.lean until Task 43 completes

6. **SubformulaClosure as Finset**: `soundFuel` uses `subformulaClosure φ |>.card`. The source defines this in `Syntax/SubformulaClosure/Closure.lean` (367 lines). Can be worked around by using the List-based version already defined in SignedFormula.lean.

### Low Risk

7. **Lean 4.27 -> 4.31 API changes**: Some Mathlib/Std API names may have changed. `List.findSome?_isSome_iff`, `List.find?_eq_none`, etc. are used extensively in proofs and may need updates.

8. **Copyright headers**: All files need the standard Cslib copyright header.

9. **Linter compliance**: Source may not comply with Mathlib linters (line length, style). Cslib uses `set_option linter.style.emptyLine false` and `set_option linter.style.longLine false` in some files.

## Recommended Approach

### Phase Structure

**Phase 1: Foundation types** (SignedFormula.lean, ~1,000 lines)
- Port Sign, SignedFormula, Branch, Label types
- Port eventuality tracking, time ordering, subset blocking
- Port subformula closure (List-based, already in source)
- Key challenge: Universe polymorphism for Formula Atom

**Phase 2: Tableau rules** (Tableau.lean, ~1,200 lines)
- Port TableauRule inductive, RuleResult, formula decomposition helpers
- Port applyRule (the 952-line match expression)
- Port expandOnce, AppliedSet tracking
- Key challenge: Large match expression elaboration, heartbeat pressure

**Phase 3: Closure detection** (Closure.lean, ~400 lines)
- Port ClosureReason, findClosure, monotonicity lemmas
- **Dependency issue**: `matchAxiom` from Automation.ProofSearch.Core
- **Recommended**: Create a minimal `AxiomMatcher.lean` file that provides `matchAxiom` without the full proof search infrastructure, OR defer `checkAxiomNeg` and start with contradiction/botPos only

**Phase 4: Saturation** (Saturation.lean, ~700 lines proof + ~800 lines tests)
- Port ExpandedTableau, expandBranchWithFuel, buildTableau
- Port soundness theorem (expandBranchWithFuel_sound)
- Port `allocateFuelProportionally` and its termination lemma
- Remove or adapt `#eval` test sections
- Key challenge: `maxHeartbeats 3200000` proof, `termination_by fuel`

**Phase 5: Countermodel extraction** (CountermodelExtraction.lean, ~1,090 lines)
- Port SimpleCountermodel, SemanticCountermodel, branchTruth
- Port saturation invariants (sat_no_bot_pos, sat_no_contradiction, etc.)
- Port branchTruthLemma (the main correctness theorem)
- Key challenge: Structural induction proofs with maxHeartbeats

**Phase 6: Proof extraction** (ProofExtraction.lean, ~354 lines)
- Port extractProof, tryAxiomProof, buildCompositionalProof
- **Dependency**: Requires matchAxiom, bounded_search_with_proof, matchDerived
- **Recommended**: Create stubs for unavailable functions, implement what's possible

**Phase 7: Decision procedure** (DecisionProcedure.lean, ~389 lines)
- Port DecisionResult, decide, decideAuto
- **Dependency**: Requires ProofExtraction, CountermodelExtraction, ProofSearch.Strategies
- Normalization is trivially replaceable

**Phase 8: Correctness** (Correctness.lean, ~147 lines)
- Port decide_sound, validity_decidable, decide_result_exclusive
- **Dependency**: fmp_completeness requires FMP (Task 43)
- **Recommended**: Port non-FMP theorems; leave FMP-dependent ones for Task 43

### Handling Missing Dependencies

**Strategy A (Recommended): Minimal AxiomMatcher + stubs**
1. Create `AxiomMatcher.lean` (~300 lines) with `matchAxiom` extracted from ProofSearch.Core
2. Stub `bounded_search_with_proof` and `search` to always return `none`/failure
3. Stub `matchDerived` to always return `none`
4. Replace `Normalization.normalizeFormula` with identity function
5. Use List-based subformula closure instead of Finset

This approach preserves the core decision procedure (tableau expansion, closure, saturation, countermodel extraction) while deferring the proof extraction optimization. The `decide` function will work but may return `.timeout` more often when it cannot extract proof terms. The key `Decidable (ThDerivable φ)` instance can still be established via classical logic.

**Strategy B: Full automation port**
Port ProofSearch.Core (1,195 lines), Strategies (379 lines), and Normalization (1,120 lines) as prerequisites. This adds ~2,700 lines to the task but gives full functionality. Not recommended for Task 42 -- should be a separate task.

### TraceCertificate/TraceExport Decision

TraceCertificate (303 lines) and TraceExport (221 lines) provide debug instrumentation. TraceCertificate is imported by Saturation.lean and DecisionProcedure.lean. However:

- The trace-instrumented versions (`expandBranchWithFuel_tracedImpl`, `decideWithTrace`) are parallel implementations that don't affect the core algorithm
- TraceExport depends on `Bimodal.Automation.DataExport` (another missing dependency)
- **Recommendation**: Port TraceCertificate (it's imported by core files) but skip TraceExport. The trace types are used in type signatures even if the traced implementations are optional.

## Existing Cslib Infrastructure

### Available modules the port will depend on:
- `Cslib.Logics.Bimodal.Syntax.Formula` -- Formula type with all connectives
- `Cslib.Logics.Bimodal.Syntax.Context` -- Context type
- `Cslib.Logics.Bimodal.ProofSystem.Axioms` -- Axiom inductive, FrameClass
- `Cslib.Logics.Bimodal.ProofSystem.Derivation` -- DerivationTree
- `Cslib.Logics.Bimodal.ProofSystem.Derivable` -- Derivable notation
- `Cslib.Logics.Bimodal.Semantics.*` -- Truth, Validity
- `Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness` -- soundness theorem
- `Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree` -- ThDerivable, Deriv

### Missing items that need creation:
- `Cslib.Logics.Bimodal.Metalogic.Decidability/` directory (target)
- `matchAxiom` or equivalent axiom pattern-matching function
- `Formula.complexity` (may exist -- needs verification)
- `Hashable` instance for `Formula Atom` (needed for `AppliedSet`)
- `LawfulBEq` for `Formula Atom` (needed for `contains_iff_mem`)

## Version Compatibility

| Component | Source (BimodalLogic) | Target (Cslib) | Risk |
|-----------|----------------------|----------------|------|
| Lean | 4.27.0-rc1 | 4.31.0-rc1 | Medium -- API changes |
| Mathlib | 4.27.0-rc1 | Latest (via lakefile) | Low -- few Mathlib deps |
| Formula Atom | Monomorphic | Polymorphic | High -- pervasive change |
| Std.HashSet | Available | Available | Low |

## Effort Estimate

| Phase | Lines | Estimated Hours | Notes |
|-------|-------|----------------|-------|
| Phase 1: SignedFormula | ~1,000 | 2-3h | Mostly mechanical; universe polymorphism |
| Phase 2: Tableau | ~1,200 | 3-4h | Large match; heartbeat risk |
| Phase 3: Closure | ~400 | 1-2h | matchAxiom dependency |
| Phase 4: Saturation | ~800 | 3-4h | Proof porting; test adaptation |
| Phase 5: Countermodel | ~1,100 | 3-4h | Truth lemma proofs |
| Phase 6: ProofExtraction | ~350 | 1-2h | Depends on automation stubs |
| Phase 7: DecisionProcedure | ~400 | 1-2h | Integration |
| Phase 8: Correctness | ~150 | 0.5-1h | Partial (no FMP) |
| AxiomMatcher prereq | ~300 | 1-2h | New file |
| TraceCertificate | ~300 | 0.5-1h | Mostly mechanical |
| **Total** | **~6,000** | **16-24h** | |

## Blockers

1. **No hard blockers identified.** All prerequisites (Tasks 4, 7) are completed.
2. The FMP dependency (Task 43) only affects 3 theorems in Correctness.lean -- the rest of the pipeline is independent.
3. The Automation/ProofSearch dependency can be worked around with the minimal AxiomMatcher strategy.

## Key Deliverable Assessment

The task description specifies the key deliverable as `instance : Decidable (ThDerivable φ)`. This requires:
1. A computable `decide` function that terminates on all inputs (via fuel)
2. Connecting the result to `ThDerivable φ`

The source achieves this via classical logic (`Classical.em`), not via a constructive `Decidable` instance. The `validity_decidable` theorem uses `Classical.em (⊨ φ)`. A constructive `Decidable` instance would require:
- Proven termination of `buildTableau` for some fuel level (the `blocking_terminates` theorem was found FALSE in the source)
- Complete proof extraction (currently partial)

**Recommendation**: The deliverable should be rephrased as providing the decision procedure toolkit (decide function, soundness theorem, countermodel extraction with correctness proof, and classical decidability), rather than a constructive `Decidable` instance. The classical `theorem validity_decidable (φ : Formula) : (⊨ φ) ∨ ¬(⊨ φ)` is what the source actually provides.
