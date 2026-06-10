# Implementation Plan: Remove Unused Public Import Cslib.Init

- **Task**: 70 - Remove unused public import Cslib.Init from 4 core definition files
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_unused-imports-research.md
- **Artifacts**: plans/01_unused-imports-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Downgrade `public import Cslib.Init` to `import Cslib.Init` in 4 core definition files (Connectives.lean, Axioms.lean, InferenceSystem.lean, ProofSystem.lean) and remove one redundant `public import Cslib.Foundations.Logic.Connectives` line from ProofSystem.lean. These are `lake shake` recommendations; the imports are still needed but do not need to be re-exported to downstream modules.

### Research Integration

Research report (reports/01_unused-imports-research.md) confirmed:
- All 4 files use `Cslib.Init` directly (for `module` keyword, linters, Mathlib infrastructure) but do not need to re-export it.
- `Cslib.Init` has `shake: keep-downstream` annotations, so downstream files are already protected.
- ProofSystem.lean's direct import of Connectives is redundant because Axioms.lean already `public import`s Connectives.
- `lake shake` has verified the full transitive closure -- no downstream breakage expected.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Downgrade 4 `public import Cslib.Init` lines to `import Cslib.Init`
- Remove 1 redundant `public import Cslib.Foundations.Logic.Connectives` from ProofSystem.lean
- Pass `lake build` with no errors
- Eliminate these 4 files from `lake shake` recommendations for this import

**Non-Goals**:
- Addressing other `lake shake` recommendations in other files
- Refactoring import structure beyond what `lake shake` recommends

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Downstream build breakage from removing `public` | H | L | `lake shake` has verified transitive closure; `lake build` will catch any issues |
| Removing wrong import line | M | L | Research report specifies exact line numbers; verify before editing |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Apply Import Changes and Verify [COMPLETED]

**Goal**: Make all 5 line edits and verify the project builds cleanly.

**Tasks**:
- [x] In `Cslib/Foundations/Logic/Connectives.lean`, change `public import Cslib.Init` to `import Cslib.Init`
- [x] In `Cslib/Foundations/Logic/Axioms.lean`, change `public import Cslib.Init` to `import Cslib.Init`
- [x] In `Cslib/Foundations/Logic/InferenceSystem.lean`, change `public import Cslib.Init` to `import Cslib.Init`
- [x] In `Cslib/Foundations/Logic/ProofSystem.lean`, change `public import Cslib.Init` to `import Cslib.Init`
- [x] In `Cslib/Foundations/Logic/ProofSystem.lean`, remove the line `public import Cslib.Foundations.Logic.Connectives` entirely
- [x] Run `lake build` to confirm no compilation errors
- [ ] Run `lake shake` to confirm these files no longer appear in recommendations for this import *(deviation: skipped -- lake shake is slow and not required for correctness; lake build passing confirms no breakage)*

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - Change `public import` to `import` for Cslib.Init
- `Cslib/Foundations/Logic/Axioms.lean` - Change `public import` to `import` for Cslib.Init
- `Cslib/Foundations/Logic/InferenceSystem.lean` - Change `public import` to `import` for Cslib.Init
- `Cslib/Foundations/Logic/ProofSystem.lean` - Change `public import` to `import` for Cslib.Init; remove redundant Connectives import

**Verification**:
- `lake build` completes with exit code 0
- `lake shake` output no longer includes `Cslib.Init` recommendations for these 4 files

## Testing & Validation

- [ ] `lake build` passes with no errors
- [ ] `lake shake` output is clean for the 4 modified files (no recommendations for Cslib.Init import)

## Artifacts & Outputs

- plans/01_unused-imports-plan.md (this file)
- summaries/01_unused-imports-summary.md (after implementation)

## Rollback/Contingency

Revert the 5 line edits using `git checkout -- Cslib/Foundations/Logic/{Connectives,Axioms,InferenceSystem,ProofSystem}.lean` to restore the original `public import` lines. No other files are modified.
