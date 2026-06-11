# Implementation Plan: PR 1 Decomposition into Smaller Sub-PRs

- **Task**: 124 - Plan PR 1 Decomposition into Smaller PRs
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: Task 123 (add bib references) -- completed
- **Research Inputs**: specs/124_plan_pr1_decomposition_into_smaller_prs/reports/01_pr1-decomposition-research.md
- **Artifacts**: plans/01_pr1-decomposition-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

The `pr1/foundations-logic` branch has 3,729 insertions across 35 Lean files, which the reviewer flagged as too large. This plan decomposes the branch into 11 sub-PRs, each under ~500 lines (with 3 justified exceptions at 514, 555, and 559 lines), submitted in 4 dependency waves. The work is primarily branch extraction and cherry-picking from the existing `pr1/foundations-logic` branch, not writing new code. Each phase corresponds to one sub-PR and covers branch creation, file extraction, CI verification, PR description, and submission.

### Research Integration

The research report (01_pr1-decomposition-research.md) provided the complete file inventory (14 new files, 21 modified files), dependency graph, line counts per sub-PR, and the 4-wave submission plan. Task 123 (bib references) has been completed, adding ChagrovZakharyaschev1997, Prawitz1965, TroelstraVanDalen1988, and HughesCresswell1996 to `references.bib` and updating 15 Lean files with Mathlib-style citations on the `pr1/foundations-logic` branch.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following roadmap components:
- Propositional proof system and metalogic (Foundations/Logic and Logics/Propositional modules)
- Natural deduction framework and ND-Hilbert equivalence
- Modal logical equivalence infrastructure

## Goals & Non-Goals

**Goals**:
- Decompose the monolithic PR 1 into 11 sub-PRs, each under ~500 lines of git diff insertions
- Respect the import dependency graph so each sub-PR builds and passes CI independently
- Submit sub-PRs in 4 waves, maximizing parallel submissions within each wave
- Produce clear PR descriptions following CSLib CONTRIBUTING.md conventions
- Include bib references (from task 123) in relevant sub-PRs

**Non-Goals**:
- Writing new Lean code or proofs (all content exists on `pr1/foundations-logic`)
- Modifying the logical structure of any file (pure extraction)
- Addressing upstream review comments on proof style or naming (handle in future tasks if reviewer requests changes)
- Submitting PR 2 (modal metalogic) -- that is task 60, independent of this work

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Sub-PR 1.1 modifies 12 already-merged files; reviewer may question a pure-refactoring PR | Medium | Medium | Frame as "prerequisite refactoring needed for Int/Min logic extensions" with clear rationale in PR description |
| Three sub-PRs slightly exceed 500 lines (1.5: 555, 1.6: 514, 1.8: 559) | Low | High | Justify in each PR description that the unit is semantically indivisible; request exception from reviewer |
| Cherry-pick conflicts when extracting files from `pr1/foundations-logic` to per-sub-PR branches | Medium | Low | Each sub-PR branch is created from upstream `main` (after prior wave merges), then files are copied/applied from `pr1/foundations-logic`; no actual cherry-pick needed |
| CI failures on sub-PR branches due to missing cross-file dependencies | High | Medium | Follow the dependency graph strictly; run full `lake build` + `lake test` before each PR submission |
| Reviewer turnaround delays cause later waves to drift from upstream main | Low | Medium | Rebase sub-PR branches onto latest upstream main before submission; keep branches small to minimize conflict surface |
| `Cslib.lean` import lines need to be distributed correctly across sub-PRs | Low | Medium | Each sub-PR adds only the import lines for files it introduces; verify with `lake exe mk_all --module --check` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4, 5 | 1 |
| 3 | 6, 7, 8, 9 | 2 and/or 3 |
| 4 | 10, 11 | 9 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Sub-PR 1.1 -- 3-Tier Hilbert Hierarchy Refactoring [NOT STARTED]

**Goal**: Submit the foundational refactoring PR that introduces `MinimalHilbert < IntuitionisticHilbert < ClassicalHilbert`, replacing the flat `PropositionalHilbert`. All subsequent sub-PRs depend on this.

**Tasks**:
- [ ] Create branch `propositional/hilbert-hierarchy-refactor` from upstream `main`
- [ ] Extract the following 12 file modifications from `pr1/foundations-logic`:
  - `Foundations/Logic/ProofSystem.lean` (+35/-17)
  - `Foundations/Logic/Theorems/Propositional/Core.lean` (+94/-72)
  - `Foundations/Logic/Theorems/Propositional/Connectives.lean` (+63/-60)
  - `Foundations/Logic/Theorems.lean` (+15/-4)
  - `Foundations/Logic/Theorems/BigConj.lean` (+2/-2)
  - `Foundations/Logic/Theorems/Combinators.lean` (+2/-2)
  - `Foundations/Logic/Theorems/Temporal/FrameConditions.lean` (+0/-1)
  - `Foundations/Data/ListHelpers.lean` (+7/-4)
  - `Logics/Propositional/Defs.lean` (+4/-0)
  - `Logics/Propositional/ProofSystem/Derivation.lean` (+58/-42)
  - `Logics/Propositional/ProofSystem/Instances.lean` (+5/-5)
  - `Logics/Propositional/Metalogic/DeductionTheorem.lean` (+73/-36)
  - `Logics/Propositional/Metalogic/MCS.lean` (+74/-42)
- [ ] Run full CI checks: `lake build`, `lake test`, `lake lint`, `lake exe lint-style`, `lake exe checkInitImports`, `lake exe mk_all --module --check`, `lake exe shake --add-public --keep-implied --keep-prefix`
- [ ] Verify no `sorry` in modified files
- [ ] Write PR description following CSLib conventions (title, summary, what/why/how, testing)
- [ ] Submit PR to `leanprover/cslib` targeting `main`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**: 12 files (modifications only, ~483 insertions, ~288 deletions)

**Verification**:
- `lake build` exits 0 on the sub-PR branch
- All CI checks pass
- `git diff --stat upstream/main..HEAD` shows ~483 insertions

---

### Phase 2: Sub-PR 1.2 -- Propositional Axiom Extensions + IntMin Instances [NOT STARTED]

**Goal**: Extend the axiom system with `IntPropAxiom` and `MinPropAxiom`, and register `IntuitionisticHilbert` and `MinimalHilbert` instances for propositional logic.

**Tasks**:
- [ ] Create branch `propositional/intmin-instances` from upstream `main` (after 1.1 merges)
- [ ] Extract from `pr1/foundations-logic`:
  - `Logics/Propositional/ProofSystem/Axioms.lean` (+51/-0)
  - `Logics/Propositional/ProofSystem/IntMinInstances.lean` (NEW, 109 lines)
- [ ] Add 1 import line to `Cslib.lean`
- [ ] Run full CI checks
- [ ] Write and submit PR description

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**: 2 Lean files + `Cslib.lean` (~211 insertions)

**Verification**:
- `lake build` exits 0
- `IntPropAxiom` and `MinPropAxiom` are available and instances registered

---

### Phase 3: Sub-PR 1.3 -- Propositional Semantics (Bivalent + Kripke) [NOT STARTED]

**Goal**: Introduce bivalent valuation semantics and Kripke model semantics for propositional logic.

**Tasks**:
- [ ] Create branch `propositional/semantics` from upstream `main` (after 1.1 merges)
- [ ] Extract from `pr1/foundations-logic`:
  - `Logics/Propositional/Semantics/Basic.lean` (NEW, 47 lines)
  - `Logics/Propositional/Semantics/Kripke.lean` (NEW, 134 lines)
- [ ] Add 2 import lines to `Cslib.lean`
- [ ] Run full CI checks
- [ ] Write and submit PR description

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**: 2 new Lean files + `Cslib.lean` (~181 insertions)

**Verification**:
- `lake build` exits 0
- `Valuation`, `Evaluate`, `Tautology`, `KripkeModel`, `IForces`, `IValid`, `MValid` are defined

---

### Phase 4: Sub-PR 1.9 -- ND Derived Connective Rules (Standalone) [NOT STARTED]

**Goal**: Add derived rules for the standalone natural deduction system. This sub-PR depends only on the already-merged `NaturalDeduction/Basic.lean` plus the hierarchy refactoring from 1.1.

**Tasks**:
- [ ] Create branch `propositional/nd-derived-rules` from upstream `main` (after 1.1 merges)
- [ ] Extract from `pr1/foundations-logic`:
  - `Logics/Propositional/NaturalDeduction/DerivedRules.lean` (NEW, 387 lines)
- [ ] Add 1 import line to `Cslib.lean`
- [ ] Run full CI checks
- [ ] Write and submit PR description

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**: 1 new Lean file + `Cslib.lean` (~387 insertions)

**Verification**:
- `lake build` exits 0
- All derived rules typecheck without `sorry`

---

### Phase 5: Sub-PR 1.11 -- Modal Logical Equivalence + Basic Update [NOT STARTED]

**Goal**: Add the `LogicalEquivalence` typeclass instance for modal logic and update `Modal/Basic.lean` for the `MinimalHilbert` rename.

**Tasks**:
- [ ] Create branch `modal/logical-equivalence` from upstream `main` (after 1.1 merges)
- [ ] Extract from `pr1/foundations-logic`:
  - `Logics/Modal/LogicalEquivalence.lean` (NEW, 132 lines)
  - `Logics/Modal/Basic.lean` (+19/-11)
  - `Logics/Modal/Denotation.lean` (+2/-2)
- [ ] Add 1 import line to `Cslib.lean`
- [ ] Run full CI checks
- [ ] Write and submit PR description

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**: 3 Lean files (1 new, 2 modified) + `Cslib.lean` (~151 insertions)

**Verification**:
- `lake build` exits 0
- `LogicalEquivalence` instance for modal formulas is registered

---

### Phase 6: Sub-PR 1.4 -- Classical Soundness + Completeness [NOT STARTED]

**Goal**: Prove classical propositional Hilbert logic is sound and complete with respect to bivalent semantics.

**Tasks**:
- [ ] Create branch `propositional/classical-soundness-completeness` from upstream `main` (after 1.2 and 1.3 merge)
- [ ] Extract from `pr1/foundations-logic`:
  - `Logics/Propositional/Metalogic/Soundness.lean` (NEW, 87 lines)
  - `Logics/Propositional/Metalogic/Completeness.lean` (NEW, 295 lines)
- [ ] Add 2 import lines to `Cslib.lean`
- [ ] Verify bib references from task 123 are present in cited files
- [ ] Run full CI checks
- [ ] Write and submit PR description

**Timing**: 30 minutes

**Depends on**: 2, 3

**Files to modify**: 2 new Lean files + `Cslib.lean` (~382 insertions)

**Verification**:
- `lake build` exits 0
- `Derivable -> Tautology` (soundness) and `Tautology -> Derivable` (completeness) are proven

---

### Phase 7: Sub-PR 1.5 -- Intuitionistic Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for intuitionistic propositional logic via Kripke models. Three files form a single logical unit (555 lines, slightly over the 500-line target).

**Tasks**:
- [ ] Create branch `propositional/intuitionistic-soundness-completeness` from upstream `main` (after 1.3 and 1.4 merge)
- [ ] Extract from `pr1/foundations-logic`:
  - `Logics/Propositional/Metalogic/IntSoundness.lean` (NEW, 103 lines)
  - `Logics/Propositional/Metalogic/IntLindenbaum.lean` (NEW, 325 lines)
  - `Logics/Propositional/Metalogic/IntCompleteness.lean` (NEW, 127 lines)
- [ ] Add 3 import lines to `Cslib.lean`
- [ ] Note in PR description: 555 lines total, semantically indivisible (Lindenbaum extension lemma is required by completeness proof)
- [ ] Run full CI checks
- [ ] Write and submit PR description

**Timing**: 30 minutes

**Depends on**: 3, 6

**Files to modify**: 3 new Lean files + `Cslib.lean` (~555 insertions)

**Verification**:
- `lake build` exits 0
- Intuitionistic soundness and completeness theorems proven without `sorry`

---

### Phase 8: Sub-PR 1.6 -- Minimal Logic Soundness + Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness for minimal propositional logic. Structurally mirrors 1.5 (514 lines, slightly over target).

**Tasks**:
- [ ] Create branch `propositional/minimal-soundness-completeness` from upstream `main` (after 1.3 and 1.4 merge)
- [ ] Extract from `pr1/foundations-logic`:
  - `Logics/Propositional/Metalogic/MinSoundness.lean` (NEW, 96 lines)
  - `Logics/Propositional/Metalogic/MinLindenbaum.lean` (NEW, 275 lines)
  - `Logics/Propositional/Metalogic/MinCompleteness.lean` (NEW, 143 lines)
- [ ] Add 3 import lines to `Cslib.lean`
- [ ] Note in PR description: 514 lines total, semantically indivisible
- [ ] Run full CI checks
- [ ] Write and submit PR description

**Timing**: 30 minutes

**Depends on**: 3, 6

**Files to modify**: 3 new Lean files + `Cslib.lean` (~514 insertions)

**Verification**:
- `lake build` exits 0
- Minimal logic soundness and completeness theorems proven without `sorry`

---

### Phase 9: Sub-PR 1.7 -- ND-Hilbert Bridge Parameterization [NOT STARTED]

**Goal**: Parameterize the existing `FromHilbert.lean` over axiom sets, enabling the ND-Hilbert bridge to work for classical, intuitionistic, and minimal logic.

**Tasks**:
- [ ] Create branch `propositional/fromhilbert-parameterize` from upstream `main` (after 1.2 merges)
- [ ] Extract from `pr1/foundations-logic`:
  - `Logics/Propositional/NaturalDeduction/FromHilbert.lean` (+146/-63)
- [ ] Run full CI checks
- [ ] Write and submit PR description

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**: 1 Lean file (~146 insertions, ~63 deletions)

**Verification**:
- `lake build` exits 0
- `impI_int`, `impI_min` and other parameterized lemmas typecheck

---

### Phase 10: Sub-PR 1.8 -- Hilbert-Style Derived Connective Rules [NOT STARTED]

**Goal**: Add derived rules for all connectives at three logic levels (classical, intuitionistic, minimal), built over `FromHilbert`. Single file at 559 lines (slightly over target, indivisible).

**Tasks**:
- [ ] Create branch `propositional/hilbert-derived-rules` from upstream `main` (after 1.7 merges)
- [ ] Extract from `pr1/foundations-logic`:
  - `Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` (NEW, 559 lines)
- [ ] Add 1 import line to `Cslib.lean`
- [ ] Note in PR description: 559 lines total; covers negation, top, conjunction, disjunction, biconditional at 3 logic levels; splitting by connective would create non-buildable partial files
- [ ] Run full CI checks
- [ ] Write and submit PR description

**Timing**: 30 minutes

**Depends on**: 9

**Files to modify**: 1 new Lean file + `Cslib.lean` (~559 insertions)

**Verification**:
- `lake build` exits 0
- All derived connective rules typecheck without `sorry`

---

### Phase 11: Sub-PR 1.10 -- ND-Hilbert Extensional Equivalence [NOT STARTED]

**Goal**: Prove that Hilbert derivability and ND derivability are extensionally equivalent, with instances for classical, intuitionistic, and minimal logic.

**Tasks**:
- [ ] Create branch `propositional/nd-hilbert-equivalence` from upstream `main` (after 1.7 and 1.9 merge)
- [ ] Extract from `pr1/foundations-logic`:
  - `Logics/Propositional/NaturalDeduction/Equivalence.lean` (NEW, 231 lines)
- [ ] Add 1 import line to `Cslib.lean`
- [ ] Run full CI checks
- [ ] Write and submit PR description

**Timing**: 30 minutes

**Depends on**: 4, 9

**Files to modify**: 1 new Lean file + `Cslib.lean` (~231 insertions)

**Verification**:
- `lake build` exits 0
- Equivalence instances for classical, intuitionistic, and minimal logic are registered

---

## Testing & Validation

- [ ] Each sub-PR branch passes `lake build` independently
- [ ] Each sub-PR branch passes `lake test`
- [ ] Each sub-PR branch passes `lake lint` and `lake exe lint-style`
- [ ] Each sub-PR branch passes `lake exe checkInitImports` and `lake exe mk_all --module --check`
- [ ] `lake exe shake --add-public --keep-implied --keep-prefix` shows no unused imports per sub-PR
- [ ] No `sorry` in any submitted file (`grep -rn "sorry" <files>` returns 0 hits per sub-PR)
- [ ] After all 11 sub-PRs merge, the combined content matches `pr1/foundations-logic` exactly (verify with `git diff`)
- [ ] Bib references from task 123 are present in all metalogic sub-PRs (1.4, 1.5, 1.6)

## Artifacts & Outputs

- 11 sub-PR branches, each targeting `leanprover/cslib` upstream `main`
- 11 PR descriptions following CSLib CONTRIBUTING.md conventions
- This plan file: `specs/124_plan_pr1_decomposition_into_smaller_prs/plans/01_pr1-decomposition-plan.md`

## Sub-PR Summary Table

| Phase | Sub-PR | Title | Lines | Branch | Wave |
|-------|--------|-------|------:|--------|------|
| 1 | 1.1 | 3-tier Hilbert hierarchy refactoring | ~483 | `propositional/hilbert-hierarchy-refactor` | 1 |
| 2 | 1.2 | Axiom extensions + IntMin instances | ~211 | `propositional/intmin-instances` | 2 |
| 3 | 1.3 | Propositional semantics (bivalent + Kripke) | ~181 | `propositional/semantics` | 2 |
| 4 | 1.9 | ND derived connective rules (standalone) | ~387 | `propositional/nd-derived-rules` | 2 |
| 5 | 1.11 | Modal logical equivalence + Basic update | ~151 | `modal/logical-equivalence` | 2 |
| 6 | 1.4 | Classical soundness + completeness | ~382 | `propositional/classical-soundness-completeness` | 3 |
| 7 | 1.5 | Intuitionistic soundness + completeness | ~555 | `propositional/intuitionistic-soundness-completeness` | 3 |
| 8 | 1.6 | Minimal logic soundness + completeness | ~514 | `propositional/minimal-soundness-completeness` | 3 |
| 9 | 1.7 | ND-Hilbert bridge parameterization | ~146 | `propositional/fromhilbert-parameterize` | 3 |
| 10 | 1.8 | Hilbert-style derived connective rules | ~559 | `propositional/hilbert-derived-rules` | 4 |
| 11 | 1.10 | ND-Hilbert extensional equivalence | ~231 | `propositional/nd-hilbert-equivalence` | 4 |

## PR Description Template

Each sub-PR description should follow this structure:

```markdown
## Summary

{1-2 sentence summary of what this sub-PR adds.}

This is sub-PR {X} of 11 in the PR 1 decomposition (see tracking issue/comment for full plan).

## Changes

- {Bullet list of files added/modified with brief description}

## Dependencies

- Requires: {list merged sub-PRs this depends on, or "None"}
- Required by: {list sub-PRs that depend on this}

## Testing

- `lake build` passes
- `lake test` passes
- `lake lint` and `lake exe lint-style` pass
- No `sorry` in any file

## References

{Relevant citations from references.bib, if applicable}
```

## Rollback/Contingency

- Each sub-PR is independent after its dependencies merge; a rejected sub-PR does not block unrelated waves
- If a sub-PR requires changes after reviewer feedback, amend the branch and force-push (standard GitHub PR workflow)
- If the overall decomposition strategy is rejected, fall back to the monolithic `pr1/foundations-logic` branch (still intact, not deleted)
- The original branch `pr1/foundations-logic` is preserved as a reference throughout the process and should not be deleted until all 11 sub-PRs are merged
