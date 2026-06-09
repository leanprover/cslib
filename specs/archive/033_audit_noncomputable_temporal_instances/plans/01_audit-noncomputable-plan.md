# Implementation Plan: Audit Noncomputable Temporal Instances

- **Task**: 33 - Audit noncomputable instances in Temporal module
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/033_audit_noncomputable_temporal_instances/reports/01_audit-noncomputable-research.md
- **Artifacts**: plans/01_audit-noncomputable-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Remove all 31 unnecessary `noncomputable` keywords from instance declarations in `Cslib/Logics/Temporal/ProofSystem/Instances.lean`. Research confirmed that every instance only constructs `Nonempty` values or performs small elimination into `Prop`, both of which are computable. None use `Classical.choice` or `Nonempty.some`. An optional stretch phase audits 8 additional files with `noncomputable section` blocks in the theorem layer.

### Research Integration

Key findings from the research report (01_audit-noncomputable-research.md):
- All 31 `noncomputable instance` declarations are unnecessary -- verified via standalone reproduction
- Root cause: the original author confused constructing `Nonempty` (computable) with extracting from it (requires `Classical.choice`)
- Removing `noncomputable` is strictly a relaxation; no downstream breakage possible
- 8 additional files in the theorem layer have `noncomputable section` blocks that are likely also removable

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task is a code quality improvement. No specific ROADMAP.md items are directly addressed, but cleaner computability annotations improve codebase accuracy for downstream proof system work.

## Goals & Non-Goals

**Goals**:
- Remove all 31 unnecessary `noncomputable` markers from Instances.lean
- Verify the build passes after removal
- (Stretch) Audit and remove `noncomputable section` blocks from 8 theorem layer files

**Non-Goals**:
- Modifying genuinely noncomputable definitions (e.g., `DerivableIn.toDerivation` in InferenceSystem.lean)
- Changing any proof logic or definitions
- Touching the `Crypto/` noncomputable sections (these are genuinely needed)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Build failure after removal | M | Very Low | Research verified all 31 compile without `noncomputable`; `lake build` will confirm |
| Downstream elaboration changes | L | Very Low | Removing `noncomputable` is a strict relaxation; any code that worked before continues to work |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Remove noncomputable markers from Instances.lean [COMPLETED]

**Goal**: Remove all 31 `noncomputable` keywords from instance declarations in the target file.

**Tasks**:
- [x] Open `Cslib/Logics/Temporal/ProofSystem/Instances.lean`
- [x] Replace all 31 occurrences of `noncomputable instance` with `instance`
- [x] Verify no other `noncomputable` annotations remain (there should be none besides the 31 instances)

**Timing**: 5 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` - Remove `noncomputable` keyword from all 31 instance declarations

**Verification**:
- `grep -c "noncomputable" Cslib/Logics/Temporal/ProofSystem/Instances.lean` returns 0

---

### Phase 2: Build verification [COMPLETED]

**Goal**: Confirm the project builds cleanly after the changes.

**Tasks**:
- [x] Run `lake build` to verify the full project compiles without errors
- [x] Confirm zero new warnings or errors introduced

**Timing**: 10 minutes (build time)

**Depends on**: 1

**Files to modify**: None (verification only)

**Verification**:
- `lake build` exits with code 0
- No new errors in the Temporal module

---

### Phase 3: (Stretch) Audit theorem layer noncomputable sections [COMPLETED]

**Goal**: Remove unnecessary `noncomputable section` blocks from 8 additional files in the theorem layer, if safe.

**Tasks**:
- [x] Remove `noncomputable section` from `Cslib/Foundations/Logic/Theorems/Combinators.lean`
- [x] Remove `noncomputable section` from `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`
- [x] Remove `noncomputable section` from `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`
- [x] Remove `noncomputable section` from `Cslib/Foundations/Logic/Theorems/Propositional/Reasoning.lean`
- [x] Remove `noncomputable section` from `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean`
- [x] Remove `noncomputable section` from `Cslib/Foundations/Logic/Theorems/Modal/S5.lean`
- [x] Remove `noncomputable section` from `Cslib/Foundations/Logic/Theorems/BigConj.lean`
- [x] Remove `noncomputable section` from `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean`
- [x] Run `lake build` after all removals to verify no breakage

**Timing**: 15 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` - Remove `noncomputable section`
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` - Remove `noncomputable section`
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` - Remove `noncomputable section`
- `Cslib/Foundations/Logic/Theorems/Propositional/Reasoning.lean` - Remove `noncomputable section`
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` - Remove `noncomputable section`
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` - Remove `noncomputable section`
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` - Remove `noncomputable section`
- `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` - Remove `noncomputable section`

**Verification**:
- `grep -r "noncomputable section" Cslib/Foundations/Logic/Theorems/ Cslib/Logics/Temporal/Theorems/` returns empty
- `lake build` exits with code 0

## Testing & Validation

- [x] `lake build` passes with zero errors after Phase 1+2
- [x] No `noncomputable` keywords remain in Instances.lean
- [x] (Stretch) `lake build` passes after Phase 3

## Artifacts & Outputs

- plans/01_audit-noncomputable-plan.md (this file)
- summaries/01_audit-noncomputable-summary.md (after implementation)

## Rollback/Contingency

If any build failures occur after removal, restore `noncomputable` to the specific failing declarations using `git checkout -- <file>`. Since each file can be reverted independently, partial rollback is straightforward.
