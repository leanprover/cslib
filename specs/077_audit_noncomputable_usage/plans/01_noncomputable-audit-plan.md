# Implementation Plan: Noncomputable Usage Audit

- **Task**: 77 - audit_noncomputable_usage
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: specs/077_audit_noncomputable_usage/reports/01_noncomputable-audit.md
- **Artifacts**: plans/01_noncomputable-audit-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

The noncomputable usage audit found 390 occurrences across 99 files, with 86.5% concentrated in Logics/ metalogic modules. Nearly all are genuinely necessary due to classical axiom dependencies inherent to the mathematical domains being formalized. This plan addresses the three actionable improvements identified by research: (1) consolidating 25 duplicated `theorem_in_mcs_fc` / `theorem_in_mcs'` local definitions into shared definitions per logic system, (2) attempting removal of noncomputable from 3-4 potentially removable declarations, and (3) auditing `noncomputable section` blocks for overly broad scope.

### Research Integration

Key findings from the research report (01_noncomputable-audit.md):
- 7 root cause categories identified, with DerivationTree extraction via Classical.choice as the dominant pattern (~220 declarations)
- Only ~5-10 declarations potentially removable, with 3 concrete candidates identified
- 34 duplicated `theorem_in_mcs_fc` definitions across Bimodal and Temporal metalogic modules
- 12 `noncomputable section` blocks assessed as correctly used but worth verifying
- No gratuitous usage found -- the codebase is disciplined about noncomputable annotations

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Consolidate duplicated `theorem_in_mcs_fc` / `theorem_in_mcs'` definitions into shared definitions per logic system (Bimodal and Temporal)
- Attempt removal of `noncomputable` from identified potentially-removable declarations
- Audit `noncomputable section` blocks for definitions that could be computable
- Verify all changes compile cleanly with `lake build`

**Non-Goals**:
- Removing noncomputable annotations that are genuinely necessary (the vast majority)
- Redesigning the InferenceSystem/DerivationTree architecture to avoid Classical.choice
- Making Mathlib types (Measure, PMF, Polynomial) computable
- Adding computable specializations alongside existing noncomputable definitions (deferred for future work)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Consolidating `theorem_in_mcs_fc` breaks downstream proofs | H | M | Build incrementally after each file change; revert individual files if needed |
| Signature variants prevent single shared definition | M | M | Create 2-3 shared variants (with/without FrameClass param) rather than forcing one |
| Removing noncomputable from candidates causes type errors | L | H | These are low-confidence removals; accept that most will fail and document why |
| `noncomputable section` audit finds no issues | L | H | Research already indicated sections are correctly used; this phase is confirmatory |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Consolidate Bimodal `theorem_in_mcs_fc` Definitions [COMPLETED]

**Goal**: Replace 20 private local copies of `theorem_in_mcs_fc` / `theorem_in_mcs_fc'` across Bimodal metalogic modules with shared definitions from a central location.

**Tasks**:
- [x] Examine existing shared definition in `Bimodal/Metalogic/Core/MaximalConsistent.lean` (line 208: `theorem_in_mcs`) and determine if it can serve as the canonical base *(deviation: altered -- shared definition placed in MCSProperties.lean instead, since it uses the fc-parametric SetMaximalConsistent from that module)*
- [x] Create two shared definitions in `Bimodal/Metalogic/Core/MaximalConsistent.lean`:
  - `theorem_in_mcs_fc` (with `fc : FrameClass` parameter, using `SetMaximalConsistent fc`)
  - Keep existing `theorem_in_mcs` (hardcoded to `FrameClass.Base`) for files that use that variant
- [x] Replace local definitions in BXCanonical files (10 files):
  - `BXCanonical/TruthLemma.lean` -- remove local `theorem_in_mcs_fc`, use shared
  - `BXCanonical/Frame.lean` -- remove local `theorem_in_mcs_fc`, use shared
  - `BXCanonical/CanonicalChain.lean` -- remove local `theorem_in_mcs_fc`, use shared
  - `BXCanonical/CanonicalModel.lean` -- remove local `theorem_in_mcs_fc'`, use shared
  - `BXCanonical/OrderedSeedConsistency.lean` -- remove local, use shared
  - `BXCanonical/Quasimodel/Construction.lean` -- remove local, use shared
  - `BXCanonical/Filtration/DefectChain.lean` -- remove local, use shared
  - `BXCanonical/Chronicle/ChronicleTypes.lean` -- remove local (fc variant), use shared
  - `BXCanonical/Chronicle/ChronicleConstruction.lean` -- remove local, use shared
  - `BXCanonical/Chronicle/ChronicleToCountermodel.lean` -- remove local, use shared
  - `BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` -- remove local, use shared
  - `BXCanonical/Completeness/Dense.lean` -- remove local, use shared
- [x] Replace local definitions in Bundle files (6 files):
  - `Bundle/CanonicalFrame.lean` -- remove local, use shared
  - `Bundle/ModalSaturation.lean` -- remove local, use shared
  - `Bundle/SuccRelation.lean` -- remove local `theorem_in_mcs_fc'`, use shared (dead code removal only)
  - `Bundle/TemporalCoherence.lean` -- remove local `theorem_in_mcs_fc''`, use shared
  - `Bundle/TemporalContent.lean` -- remove local, use shared
  - `Bundle/WitnessSeed.lean` -- remove local, use shared
- [x] Replace local definitions in Algebraic files (2 files):
  - `Algebraic/ParametricTruthLemma.lean` -- remove local, use shared
  - `Algebraic/RestrictedParametricTruthLemma.lean` -- remove local, use shared
- [x] Run `lake build Cslib.Logics.Bimodal` to verify all Bimodal modules compile *(deviation: altered -- no top-level Bimodal.lean module file exists; verified each modified module individually)*

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` -- add shared `theorem_in_mcs_fc` definition
- 20 files listed above -- remove private local definitions, update references

**Verification**:
- `lake build Cslib.Logics.Bimodal` succeeds with no errors
- `grep -rn "private noncomputable def theorem_in_mcs_fc" Cslib/Logics/Bimodal/` returns zero results
- All downstream proofs that used the local definition still compile

---

### Phase 2: Consolidate Temporal `theorem_in_mcs'` Definitions [NOT STARTED]

**Goal**: Replace 5 private local copies of `theorem_in_mcs'` across Temporal metalogic modules with a shared definition.

**Tasks**:
- [ ] Examine existing `Temporal/Metalogic/MCS.lean` and determine if `theorem_in_mcs'` should be added there
- [ ] Create shared `theorem_in_mcs'` definition in `Temporal/Metalogic/MCS.lean` (or appropriate location)
- [ ] Replace local definitions in 5 Temporal files:
  - `Temporal/Metalogic/Chronicle/CanonicalChain.lean` -- remove local, use shared
  - `Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` -- remove local, use shared
  - `Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` -- remove local, use shared
  - `Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean` -- remove local, use shared
  - `Temporal/Metalogic/Chronicle/RRelation.lean` -- remove local, use shared
- [ ] Run `lake build Cslib.Logics.Temporal` to verify all Temporal modules compile

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` -- add shared `theorem_in_mcs'` definition
- 5 files listed above -- remove private local definitions, update references

**Verification**:
- `lake build Cslib.Logics.Temporal` succeeds with no errors
- `grep -rn "private noncomputable def theorem_in_mcs'" Cslib/Logics/Temporal/` returns zero results

---

### Phase 3: Attempt Noncomputable Removal on Candidate Declarations [NOT STARTED]

**Goal**: Try removing `noncomputable` from the 3-4 identified candidates and determine which (if any) can actually be made computable.

**Tasks**:
- [ ] Attempt removal from `propositions` in `Cslib/Logics/HML/Basic.lean` (line 183):
  - Remove `noncomputable` keyword
  - If fails: document required `DecidableEq` / `Fintype` constraints and why they are not available
  - If succeeds: verify with `lake build Cslib.Logics.HML`
- [ ] Attempt removal from `chooseEquiv` in `Cslib/Logics/LinearLogic/CLL/Basic.lean` (line 273):
  - Remove `noncomputable` keyword
  - If fails: document that `And` destructuring in `Prop` requires classical extraction
  - If succeeds: verify with `lake build Cslib.Logics.LinearLogic`
- [ ] Attempt removal from `LogicalEquivalence` instance in `Cslib/Logics/LinearLogic/CLL/Basic.lean` (line 653):
  - Check if this depends on `chooseEquiv` -- if so, removal depends on previous task
  - If independent: attempt removal
- [ ] Audit `noncomputable section` blocks (12 occurrences) for overly broad scope:
  - For each `noncomputable section` block, check if any definitions within could omit the annotation
  - If found: narrow the section scope or switch to per-definition annotations
  - Expected outcome: no changes needed (research indicated correct usage)
- [ ] Document results of all removal attempts in a summary comment at the top of the plan

**Timing**: 45 minutes

**Depends on**: 1 (to avoid merge conflicts from parallel file edits -- though technically these are disjoint files, the build system may have cross-dependencies)

**Files to modify**:
- `Cslib/Logics/HML/Basic.lean` -- attempt noncomputable removal (line 183)
- `Cslib/Logics/LinearLogic/CLL/Basic.lean` -- attempt noncomputable removal (lines 273, 653)
- Various files with `noncomputable section` -- audit only, changes unlikely

**Verification**:
- `lake build` on affected modules for any successful removals
- Documentation of why removal failed for unsuccessful attempts

---

### Phase 4: Final Verification and Build [NOT STARTED]

**Goal**: Run full project build to verify all changes are consistent and no regressions were introduced.

**Tasks**:
- [ ] Run `lake build` for the full project
- [ ] Verify noncomputable count reduction: run `grep -rn "noncomputable" --include="*.lean" | wc -l` and compare to baseline (390)
- [ ] Verify duplication reduction: confirm `theorem_in_mcs_fc` / `theorem_in_mcs'` definitions exist only in canonical locations
- [ ] Document final counts and outcomes

**Timing**: 30 minutes

**Depends on**: 2, 3

**Files to modify**:
- None (verification only)

**Verification**:
- `lake build` succeeds with no errors
- Noncomputable count is reduced (expected reduction: ~24 from consolidation, 0-3 from removal attempts)
- No new `sorry` or vacuous definitions introduced

## Testing & Validation

- [ ] `lake build` succeeds after Phase 1 (Bimodal consolidation)
- [ ] `lake build` succeeds after Phase 2 (Temporal consolidation)
- [ ] `lake build` succeeds after Phase 3 (removal attempts)
- [ ] Full `lake build` succeeds after all phases
- [ ] `grep -rn "private noncomputable def theorem_in_mcs" --include="*.lean" | wc -l` returns 0
- [ ] No `sorry` introduced in any modified file

## Artifacts & Outputs

- `specs/077_audit_noncomputable_usage/plans/01_noncomputable-audit-plan.md` (this file)
- `specs/077_audit_noncomputable_usage/summaries/01_noncomputable-audit-summary.md` (post-implementation)

## Rollback/Contingency

All changes are source-level Lean edits that can be individually reverted with `git checkout -- <file>`. If a consolidation breaks downstream proofs that cannot be fixed within the phase time budget, revert that specific file and keep the local definition. The remaining consolidations can proceed independently since each file's local definition is self-contained.
