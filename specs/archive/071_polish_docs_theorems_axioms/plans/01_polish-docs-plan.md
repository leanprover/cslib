# Implementation Plan: Polish Documentation in Theorems.lean and Axioms.lean

- **Task**: 71 - Polish documentation in Theorems.lean and Axioms.lean
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/071_polish_docs_theorems_axioms/reports/01_polish-docs-research.md
- **Artifacts**: plans/01_polish-docs-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

This task addresses two NICE-TO-HAVE quality audit items: (a) adding a missing Temporal subsection to the Theorems.lean module docstring, and (b) extracting 45 repeated `let top`/`let neg`/`let conj`/`let disj` bindings in Axioms.lean into namespace-level abbreviations. Both changes are purely cosmetic and must preserve definitional equality.

### Research Integration

The research report (01_polish-docs-research.md) confirmed:
- Theorems.lean imports `Temporal.TemporalDerived` and `Temporal.FrameConditions` but the docstring only covers Propositional and Modal subsections.
- Axioms.lean has 45 repeated `let` bindings across 22 temporal axiom definitions. The preferred extraction strategy places `protected abbrev` declarations in a new `section Abbreviations` at namespace level (after `variable {F : Type*}`, before `section Propositional`), making them available across all sections.
- Task 68 added `@[expose] public section`, which conflicts with `private abbrev`. The research recommends `protected abbrev` or plain `abbrev`.
- There is a self-reference concern: `conj'` references `neg'`, and if both are `protected`, qualified access may be needed within the definition. This must be verified with `lake build`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No specific ROADMAP.md items directly correspond to this documentation polish task. It is a quality audit fix that improves the Foundations/Logic layer.

## Goals & Non-Goals

**Goals**:
- Add a Temporal subsection to Theorems.lean module docstring documenting TemporalDerived and FrameConditions
- Extract repeated `let` bindings in Axioms.lean into shared abbreviations to reduce visual noise
- Maintain build success (`lake build` passes with no new errors)

**Non-Goals**:
- Changing the semantics or behavior of any axiom definition
- Refactoring axiom definitions beyond `let` extraction
- Modifying files outside Theorems.lean and Axioms.lean
- Adding new axioms or theorems

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `protected abbrev` self-reference fails (conj' referencing neg') | M | M | Fallback to plain `abbrev` within `section Abbreviations` |
| `protected abbrev` conflicts with `@[expose] public section` | M | L | Fallback to plain `abbrev` (matches TemporalDerived.lean precedent) |
| Definitional equality broken by abbrev vs let | H | L | `abbrev` unfolds eagerly like `let`; verify with `lake build` |
| Interaction section top' not in scope (different variable requirements) | L | L | `top'` only needs `[HasBot F] [HasImp F]`, which is a subset; placing in namespace-level section makes it available everywhere |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Add Temporal Subsection to Theorems.lean Docstring [COMPLETED]

**Goal**: Add the missing Temporal subsection to the module docstring so all three import groups (Propositional, Modal, Temporal) are documented.

**Tasks**:
- [ ] Add a `### Temporal` subsection after the Modal subsection (after line 38, before the closing `-/` on line 39)
- [ ] Document `Temporal.TemporalDerived` with key content: BX-system derived theorems
- [ ] Document `Temporal.FrameConditions` with key content: frame condition typeclasses
- [ ] Use typeclass annotation format matching existing subsections: ``(`[TemporalBXHilbert S]`)``

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems.lean` - Add Temporal subsection to module docstring (lines 38-39)

**Verification**:
- Docstring now has three subsections: Propositional, Modal, Temporal
- `lake build Cslib.Foundations.Logic.Theorems` succeeds (docstring-only change)

---

### Phase 2: Extract Repeated let Bindings in Axioms.lean [COMPLETED]

**Goal**: Replace 45 repeated `let top`/`let neg`/`let conj`/`let disj` bindings with namespace-level abbreviations, reducing visual noise while preserving definitional equality.

**Tasks**:
- [ ] Add a `section Abbreviations` block after `variable {F : Type*}` (line 34) and before `/-! ### Propositional Axioms -/` (line 36), containing:
  - `protected abbrev top' : F` (requires `[HasBot F] [HasImp F]`)
  - `protected abbrev neg' (x : F) : F` (requires `[HasBot F] [HasImp F]`)
  - `protected abbrev conj' (a b : F) : F` (requires `[HasBot F] [HasImp F]`)
  - `protected abbrev disj' (a b : F) : F` (requires `[HasBot F] [HasImp F]`)
- [x] Run `lake build Cslib.Foundations.Logic.Axioms` to verify abbreviations compile; if `protected` causes self-reference issues (conj' referencing neg'), switch to plain `abbrev` *(deviation: altered -- `protected abbrev` failed with "Unknown identifier" errors because protected names cannot be accessed without full qualification, even within the same namespace; switched to plain `abbrev` per fallback plan)*
- [ ] Replace `let top := HasImp.imp (HasBot.bot : F) HasBot.bot` with `Cslib.Logic.Axioms.top'` (or short form if in scope) in all 15 temporal/interaction axioms that use it
- [ ] Replace `let neg := fun (x : F) => HasImp.imp x HasBot.bot` with `Cslib.Logic.Axioms.neg'` in all 16 axioms that use it
- [ ] Replace `let conj := fun (a b : F) => ...` with `Cslib.Logic.Axioms.conj'` in all 10 axioms that use it
- [ ] Replace `let disj := fun (a b : F) => ...` with `Cslib.Logic.Axioms.disj'` in all 4 axioms that use it
- [ ] Run `lake build` to verify full project builds cleanly

**Timing**: 50 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Axioms.lean` - Add abbreviations section (after line 34); replace `let` bindings in all temporal and interaction axiom definitions (lines 106-320)

**Verification**:
- No `let top :=`, `let neg :=`, `let conj :=`, or `let disj :=` remains in temporal/interaction sections
- `lake build` passes with no new errors
- All axiom definitions are definitionally equal to their previous versions

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Theorems` passes (Phase 1)
- [ ] `lake build Cslib.Foundations.Logic.Axioms` passes (Phase 2)
- [ ] `lake build` full project passes (final verification)
- [ ] No `sorry` or vacuous definitions introduced
- [ ] grep confirms no remaining `let top :=` / `let neg :=` / `let conj :=` / `let disj :=` in temporal/interaction sections

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Theorems.lean` - Updated module docstring with Temporal subsection
- `Cslib/Foundations/Logic/Axioms.lean` - Extracted abbreviations, cleaned axiom definitions

## Rollback/Contingency

Both files are under version control. If `protected abbrev` causes issues:
1. Try plain `abbrev` within `section Abbreviations` (fallback per research recommendation)
2. If abbreviation extraction causes any downstream build failures, revert Axioms.lean changes entirely via `git checkout -- Cslib/Foundations/Logic/Axioms.lean` and complete only Phase 1
