# Implementation Plan: Port Bimodal FMP Infrastructure

- **Task**: 43 - Port bimodal finite model property (FMP)
- **Status**: [NOT STARTED]
- **Effort**: 11 hours
- **Dependencies**: Task 42 (core tableau -- completed)
- **Research Inputs**: specs/043_port_bimodal_fmp/reports/01_fmp-port-research.md
- **Artifacts**: plans/01_fmp-port-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Port the Finite Model Property (FMP) infrastructure from BimodalLogic to Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/. The FMP proves that if a bimodal formula is satisfiable, it is satisfiable in a finite model of bounded size (at most 2^|closure(phi)|). The port requires 3 prerequisite files (Subformulas, SubformulaClosure, RestrictedMCS) followed by 7 FMP files (ClosureMCS, Filtration, FiniteModel, TruthPreservation, FMP, DenseFMP, DiscreteFMP), plus barrel imports and visibility fixes. Total scope: ~2,700 lines across 12 files.

### Research Integration

The research report (01_fmp-port-research.md) provided:
- Complete source file inventory with line counts (1,703 lines FMP + 1,249 lines prerequisites)
- Dependency graph: Subformulas -> SubformulaClosure -> RestrictedMCS -> ClosureMCS -> Filtration -> FiniteModel -> TruthPreservation -> FMP -> DenseFMP/DiscreteFMP
- Namespace mapping (BimodalLogic -> Cslib.Logic.Bimodal), axiom renames (prop_s -> imp_s, ex_falso -> efq)
- Three key technical challenges: (1) consistent_chain_union bridge for bimodal SetConsistent, (2) private temp_4_derived/temp_4_past visibility, (3) polymorphic Formula Atom adaptation
- Zero-sorry assessment: all source proofs are complete; port should maintain this

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Bimodal Porting roadmap items:
- Task 9 (expanded) decidability/tableau port -- FMP is the second subtask after Task 42
- PR 8 scope: completing the full Metalogic/Decidability module

## Goals & Non-Goals

**Goals**:
- Port all 7 FMP files from BimodalLogic with zero sorry
- Port 3 prerequisite files (Subformulas, SubformulaClosure, RestrictedMCS) needed by FMP
- Adapt to polymorphic `Formula Atom` type throughout
- Update barrel imports to expose FMP infrastructure
- Achieve clean `lake build` with zero errors and zero sorry

**Non-Goals**:
- Porting the `iter_F`/`iter_P` boundedness theorems from RestrictedMCS (lines 441-653, depend on Bundle/ which is out of scope)
- Porting the NestingDepth module (only needed by iter_F/iter_P)
- Dense/discrete completeness infrastructure (separate tasks 35/36)
- Performance optimization or refactoring of source proofs

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| consistent_chain_union bridge for bimodal SetConsistent fc | H | M | Prove directly for bimodal SetConsistent fc by extracting the chain member containing a finite list; structurally identical to foundation-level proof |
| temp_4_derived/temp_4_past are private in MCSProperties | M | H | Change from `private def` to `protected def` or add public wrappers; one-line change per definition |
| Mathlib API changes in Fintype/Quotient/Powerset | M | L | Verify with lean_local_search during implementation; standard Mathlib APIs are stable |
| Polymorphic Formula Atom cascading through all files | L | H | Mechanical transformation: add `variable {Atom : Type*}` at file top, add `Atom` parameter to type references |
| SubformulaClosure.Closure.lean partial port (skip diamond detection) | L | L | Diamond detection infrastructure is clearly separated in source; only port the Finset-based closure and membership lemmas |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3 |
| 5 | 6 | 4, 5 |
| 6 | 7 | 5, 6 |
| 7 | 8 | 6, 7 |
| 8 | 9 | 7 |
| 9 | 10 | 8 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Prerequisite -- Subformulas.lean [COMPLETED]

**Goal**: Port Formula.subformulas and all membership lemmas to Cslib/Logics/Bimodal/Syntax/Subformulas.lean

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Syntax/Subformulas.lean`
- [ ] Port `Formula.subformulas : Formula Atom -> List (Formula Atom)` (recursive definition over all constructors: atom, bot, imp, box, fut_box, untl, snce, neg)
- [ ] Port `Formula.self_mem_subformulas` and all `mem_subformulas_of_*` lemmas
- [ ] Port `Formula.subformulas_trans` (transitivity of subformula membership)
- [ ] Adapt all definitions from concrete `Formula` to polymorphic `Formula Atom`
- [ ] Add copyright header, namespace `Cslib.Logic.Bimodal.Syntax`
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Syntax.Subformulas`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Syntax/Subformulas.lean` - NEW (~230 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Syntax.Subformulas` succeeds
- Zero sorry in file
- `Formula.self_mem_subformulas` and key membership lemmas type-check

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Syntax/Subformulas.lean` (229 lines)

---

### Phase 2: Prerequisite -- SubformulaClosure.lean [COMPLETED]

**Goal**: Port Finset-based subformula closure, closureWithNeg, and membership lemmas

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Syntax/SubformulaClosure.lean`
- [ ] Port `subformulaClosure : Formula Atom -> Finset (Formula Atom)` (List.toFinset of subformulas)
- [ ] Port `closureWithNeg : Formula Atom -> Finset (Formula Atom)` (closure union with negations)
- [ ] Port `self_mem_subformulaClosure`, `self_mem_closureWithNeg`
- [ ] Port `subformulaClosure_subset_closureWithNeg`, `neg_mem_closureWithNeg`
- [ ] Port all constructor-specific membership lemmas (imp, box, fut_box, untl, snce, neg)
- [ ] Skip diamond detection infrastructure (not needed by FMP)
- [ ] Adapt to polymorphic `Formula Atom` with `[DecidableEq (Formula Atom)]` or `[DecidableEq Atom]`
- [ ] Add copyright header, namespace
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Syntax.SubformulaClosure`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure.lean` - NEW (~300 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Syntax.SubformulaClosure` succeeds
- Zero sorry
- `subformulaClosure`, `closureWithNeg` and membership lemmas available

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Syntax/SubformulaClosure/Closure.lean` (367 lines, partial port)

---

### Phase 3: Prerequisite -- MCSProperties Visibility Fix [COMPLETED]

**Goal**: Make temp_4_derived and temp_4_past accessible from other modules

**Tasks**:
- [ ] In `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean`, change `private def temp_4_derived` to `protected def temp_4_derived` (or remove `private`)
- [ ] Similarly change `private def temp_4_past` to `protected def temp_4_past`
- [ ] Verify existing code in the file still compiles after visibility change
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties`

**Timing**: 0.25 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` - MODIFY (change 2 lines: private -> protected)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties` succeeds
- No downstream breakage from visibility change

**Source**: N/A (target-side fix)

---

### Phase 4: Prerequisite -- RestrictedMCS.lean [COMPLETED]

**Goal**: Port closure-restricted MCS definitions, restricted Lindenbaum, and formula construction (lines 1-440 of source)

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Core/RestrictedMCS.lean`
- [ ] Port `ClosureRestricted`, `RestrictedConsistent`, `RestrictedMCS` definitions
- [ ] Port basic property theorems (restricted_consistent_is_restricted, restricted_mcs_is_consistent, etc.)
- [ ] Port `restricted_mcs_negation_complete` (the main negation completeness proof, ~100 lines)
- [ ] Port `RestrictedConsistentSupersets` and `self_mem_restricted_consistent_supersets`
- [ ] Prove `restricted_consistent_chain_union` -- the key chain union lemma for bimodal `SetConsistent fc`; needs a bridge from the bimodal `SetConsistent fc` to use the finite-list-in-chain-member pattern
- [ ] Port `restricted_lindenbaum` (Zorn's lemma application, ~60 lines)
- [ ] Port `restricted_mcs_exists_containing` and `restricted_mcs_from_formula`
- [ ] Do NOT port lines 441-653 (iter_F/iter_P boundedness -- depends on Bundle/)
- [ ] Omit imports of NestingDepth, Bundle.CanonicalTaskRelation, Bundle.SuccExistence
- [ ] Adapt to polymorphic `Formula Atom` with `variable {Atom : Type*}`
- [ ] Add copyright header, namespace `Cslib.Logic.Bimodal.Metalogic.Core`
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Core.RestrictedMCS`

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/RestrictedMCS.lean` - NEW (~440 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Core.RestrictedMCS` succeeds
- Zero sorry
- `restricted_lindenbaum` and `restricted_mcs_from_formula` type-check
- Chain union lemma works for bimodal `SetConsistent fc`

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Core/RestrictedMCS/Basic.lean` (lines 1-440 of 653)

---

### Phase 5: FMP -- ClosureMCS.lean [COMPLETED]

**Goal**: Port closure MCS infrastructure (thin wrapper over RestrictedMCS for FMP usage)

**Tasks**:
- [ ] Create directory `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/`
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/ClosureMCS.lean`
- [ ] Port re-exports of RestrictedMCS specialized for FMP usage
- [ ] Port projection theorems (full MCS to closure MCS)
- [ ] Port cardinality bounds
- [ ] Adapt to polymorphic `Formula Atom`
- [ ] Add copyright header, namespace
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.ClosureMCS`

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/ClosureMCS.lean` - NEW (~280 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.ClosureMCS` succeeds
- Zero sorry

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/ClosureMCS.lean` (279 lines)

---

### Phase 6: FMP -- Filtration.lean [COMPLETED]

**Goal**: Port filtration equivalence, Setoid, quotient, and filtered frame construction

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/Filtration.lean`
- [ ] Port `MCSFiltrationEquiv` (equivalence relation based on closure membership)
- [ ] Port `ClosureMCSSetoid` (Setoid structure)
- [ ] Port `FilteredWorld` (quotient type)
- [ ] Port `FilteredTaskFrame` / `RefinedFilteredTaskFrame` (frame on filtered worlds)
- [ ] Port `forward_comp`, `converse` proofs for the refined frame
- [ ] Adapt Semantics imports (Validity.lean, Truth.lean -- already ported)
- [ ] Add Mathlib imports: Data.Setoid.Basic, Data.Fintype.Quotient
- [ ] Add copyright header, namespace
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.Filtration`

**Timing**: 1.5 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/Filtration.lean` - NEW (~325 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.Filtration` succeeds
- Zero sorry
- FilteredTaskFrame definition and proofs compile

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/Filtration.lean` (323 lines)

---

### Phase 7: FMP -- FiniteModel.lean [COMPLETED]

**Goal**: Port finiteness theorem via characteristic set injection

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/FiniteModel.lean`
- [ ] Port `FilteredWorld.finite` (filtered world type is finite)
- [ ] Port `FiniteFilteredFrame` (filtered task frame is finite)
- [ ] Port injection from equivalence classes to powerset of closure
- [ ] Verify Mathlib APIs: `Set.instFinite`, `Fintype.Card`, `Fintype.Powerset`
- [ ] Add copyright header, namespace
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.FiniteModel`

**Timing**: 1 hour

**Depends on**: 6

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/FiniteModel.lean` - NEW (~180 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.FiniteModel` succeeds
- Zero sorry
- `FilteredWorld.finite` theorem compiles

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/FiniteModel.lean` (177 lines)

---

### Phase 8: FMP -- TruthPreservation.lean [COMPLETED]

**Goal**: Port MCS truth definition, filtration lemma, and truth preservation for all operators

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/TruthPreservation.lean`
- [ ] Port `mcsTruth` (truth at a closure MCS = membership)
- [ ] Port `filteredMcsTruth` (truth lifted to filtered worlds)
- [ ] Port bot, negation, implication truth preservation lemmas
- [ ] Port box, fut_box (temporal) operator truth preservation
- [ ] Port temporal operator truth preservation (untl, snce)
- [ ] Use `temp_4_derived` and `temp_4_past` from MCSProperties (now accessible via Phase 3 visibility fix)
- [ ] Apply axiom renames: `prop_s -> imp_s`, `ex_falso -> efq`
- [ ] Add copyright header, namespace
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.TruthPreservation`

**Timing**: 2 hours

**Depends on**: 3, 7

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/TruthPreservation.lean` - NEW (~400 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.TruthPreservation` succeeds
- Zero sorry
- Filtration lemma (main truth preservation theorem) compiles

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/TruthPreservation.lean` (400 lines)

---

### Phase 9: FMP -- FMP.lean (Main Theorem) [COMPLETED]

**Goal**: Port the main FMP theorem, contrapositive, and size bound

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/FMP.lean`
- [ ] Port `mcs_finite_model_property`: if phi not provable, there exists a finite model where phi fails
- [ ] Port `fmp_contrapositive`: if phi valid in all finite models, then phi is valid
- [ ] Port `fmp_size_bound`: model size bounded by 2^|closure(phi)|
- [ ] Use `double_negation` from `Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers`
- [ ] Add copyright header, namespace
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.FMP`

**Timing**: 1 hour

**Depends on**: 8

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/FMP.lean` - NEW (~250 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.FMP` succeeds
- Zero sorry
- `fmp_contrapositive` and `mcs_finite_model_property` compile

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Decidability/FMP/FMP.lean` (248 lines)

---

### Phase 10: FMP -- DenseFMP + DiscreteFMP + Barrel Imports [NOT STARTED]

**Goal**: Port Dense/Discrete FMP specializations and wire up barrel imports

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/DenseFMP.lean`
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/DiscreteFMP.lean`
- [ ] Port `dense_fmp` (delegates to base FMP)
- [ ] Port `discrete_mcs_finite_model_property` (delegates to base FMP)
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP.lean` (barrel import re-exporting all 7 FMP files)
- [ ] Update `Cslib/Logics/Bimodal/Metalogic/Decidability.lean` to add import of `FMP` barrel
- [ ] Add copyright headers, namespaces to all new files
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP`
- [ ] Verify: `lake build Cslib.Logics.Bimodal.Metalogic.Decidability`
- [ ] Run full `lake build` to confirm no regressions

**Timing**: 0.75 hours

**Depends on**: 9

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/DenseFMP.lean` - NEW (~115 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/DiscreteFMP.lean` - NEW (~120 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP.lean` - NEW barrel (~50 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability.lean` - MODIFY (add 1 import line)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Decidability` succeeds
- Full `lake build` succeeds with zero errors
- `grep -rn "sorry" Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/` returns empty
- `grep -rn "sorry" Cslib/Logics/Bimodal/Syntax/Subformulas.lean Cslib/Logics/Bimodal/Syntax/SubformulaClosure.lean Cslib/Logics/Bimodal/Metalogic/Core/RestrictedMCS.lean` returns empty

**Source**: DenseFMP (112 lines), DiscreteFMP (117 lines), FMP.lean barrel (47 lines)

## Testing & Validation

- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Decidability` succeeds (full decidability module including FMP)
- [ ] `lake build` (full project) succeeds with zero errors
- [ ] `grep -rn "sorry" Cslib/Logics/Bimodal/Syntax/Subformulas.lean` returns empty
- [ ] `grep -rn "sorry" Cslib/Logics/Bimodal/Syntax/SubformulaClosure.lean` returns empty
- [ ] `grep -rn "sorry" Cslib/Logics/Bimodal/Metalogic/Core/RestrictedMCS.lean` returns empty
- [ ] `grep -rn "sorry" Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/` returns empty
- [ ] Verify key theorems with `lean_verify`:
  - `Cslib.Logic.Bimodal.Metalogic.Decidability.FMP.mcs_finite_model_property`
  - `Cslib.Logic.Bimodal.Metalogic.Decidability.FMP.fmp_contrapositive`
  - `Cslib.Logic.Bimodal.Metalogic.Core.restricted_lindenbaum`
- [ ] Existing decidability tests (Task 42) still pass

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/Syntax/Subformulas.lean` - NEW (~230 lines)
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure.lean` - NEW (~300 lines)
- `Cslib/Logics/Bimodal/Metalogic/Core/RestrictedMCS.lean` - NEW (~440 lines)
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` - MODIFIED (2 lines: private -> protected)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/ClosureMCS.lean` - NEW (~280 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/Filtration.lean` - NEW (~325 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/FiniteModel.lean` - NEW (~180 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/TruthPreservation.lean` - NEW (~400 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/FMP.lean` - NEW (~250 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/DenseFMP.lean` - NEW (~115 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/DiscreteFMP.lean` - NEW (~120 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP.lean` - NEW barrel (~50 lines)
- `Cslib/Logics/Bimodal/Metalogic/Decidability.lean` - MODIFIED (add 1 import)

## Rollback/Contingency

All new files can be deleted without affecting the existing codebase. The only modification to existing code is the visibility change in MCSProperties.lean (private -> protected for temp_4_derived/temp_4_past), which is backward-compatible. If rollback is needed:
1. Delete all new files listed above
2. Revert the MCSProperties.lean visibility change
3. Remove the FMP import from Decidability.lean barrel
4. Run `lake build` to confirm clean state
