# Implementation Plan: Add DecidableEq to Modal.Proposition, Resolve LukasiewiczDerived

- **Task**: 16 - Add DecidableEq to Modal.Proposition, resolve LukasiewiczDerived usage
- **Status**: [COMPLETED]
- **Effort**: 0.25 hours
- **Dependencies**: None
- **Research Inputs**: specs/016_formula_type_consistency/reports/01_formula-type-research.md
- **Artifacts**: plans/01_formula-type-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Two small consistency fixes to align Modal.Proposition with sibling formula types and document the intentional status of LukasiewiczDerived. Phase 1 adds `deriving DecidableEq, BEq` to `Modal.Proposition` (a one-line change). Phase 2 expands the docstring on `LukasiewiczDerived` to document its intentionally uninstantiated status. Both changes are zero-risk and under 15 minutes total.

### Research Integration

Research report (01_formula-type-research.md) confirmed:
- Modal.Proposition is the only formula type missing `deriving DecidableEq, BEq` -- PL.Proposition, Temporal.Formula, and Bimodal.Formula all have these instances.
- DecidableEq is a prerequisite for Task 21 (modal proof system) which needs `Finset`-based contexts.
- LukasiewiczDerived is defined but never instantiated; each formula type uses its own `abbrev` definitions instead, which are definitionally equal. Instantiation would add typeclass overhead for no benefit.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task unblocks Task 21 (modal proof system and theorems), which is part of Wave 2 in the porting roadmap. DecidableEq on Modal.Proposition enables `Finset`-based contexts required by Modal.DerivationTree.

## Goals & Non-Goals

**Goals**:
- Add `deriving DecidableEq, BEq` to `Modal.Proposition` for consistency with all sibling formula types
- Document `LukasiewiczDerived` with an expanded docstring explaining its intentionally uninstantiated status

**Non-Goals**:
- Instantiating `LukasiewiczDerived` for any formula type (provides no benefit per research)
- Modifying any downstream files that import Modal.Basic (no changes needed)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `deriving DecidableEq` fails to synthesize | M | L | All constructors use types that already have DecidableEq; research confirmed viability |
| Downstream build breakage | M | L | Adding instances only creates new definitions, never changes existing ones; full `lake build` verification |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Add DecidableEq to Modal.Proposition [COMPLETED]

**Goal**: Add `deriving DecidableEq, BEq` to the `Modal.Proposition` inductive definition, aligning it with PL.Proposition, Temporal.Formula, and Bimodal.Formula.

**Tasks**:
- [x] Add `deriving DecidableEq, BEq` after the `Proposition` inductive closing (after line 54 in `Cslib/Logics/Modal/Basic.lean`)
- [x] Run `lake build Cslib.Logics.Modal.Basic` to verify the change compiles

**Timing**: 5 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` - Add `deriving DecidableEq, BEq` after the inductive definition

**Verification**:
- `lake build Cslib.Logics.Modal.Basic` passes with zero errors
- `lean_hover_info` on `Proposition` confirms `DecidableEq` instance exists

---

### Phase 2: Expand LukasiewiczDerived Docstring [COMPLETED]

**Goal**: Replace the current one-line docstring on `LukasiewiczDerived` with an expanded version that documents its intentionally uninstantiated status and explains why.

**Tasks**:
- [x] Replace docstring on `LukasiewiczDerived` (lines 73-74 of `Cslib/Foundations/Logic/Connectives.lean`) with expanded version explaining: (a) what it provides, (b) that each formula type uses its own `abbrev` definitions instead, (c) that instantiation would add typeclass overhead for no benefit, (d) that it is retained for potential future polymorphic proof system abstractions
- [x] Run `lake build Cslib.Foundations.Logic.Connectives` to verify the change compiles

**Timing**: 5 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - Expand docstring on `LukasiewiczDerived` class

**Verification**:
- `lake build Cslib.Foundations.Logic.Connectives` passes with zero errors

## Testing & Validation

- [x] `lake build Cslib.Logics.Modal.Basic` passes (Phase 1)
- [x] `lake build Cslib.Foundations.Logic.Connectives` passes (Phase 2)
- [x] Full `lake build` passes with zero errors (final verification)
- [x] No new warnings introduced

## Artifacts & Outputs

- `specs/016_formula_type_consistency/plans/01_formula-type-plan.md` (this file)
- `specs/016_formula_type_consistency/summaries/01_formula-type-summary.md` (post-implementation)

## Rollback/Contingency

Both changes are additive and independent. Revert by removing the `deriving` clause (Phase 1) or restoring the original docstring (Phase 2). Neither change affects existing definitions or proofs.
