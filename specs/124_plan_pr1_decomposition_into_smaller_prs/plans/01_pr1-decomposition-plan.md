# Implementation Plan: PR 1 Decomposition into Smaller Sub-PRs

- **Task**: 124 - Plan PR 1 Decomposition into Smaller PRs
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: Task 123 (add bib references) -- completed
- **Research Inputs**: specs/124_plan_pr1_decomposition_into_smaller_prs/reports/01_pr1-decomposition-research.md
- **Artifacts**: plans/01_pr1-decomposition-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

The `pr1/foundations-logic` branch has 3,729 insertions across 35 Lean files, which the reviewer flagged as too large. The research report identified 11 sub-PRs, each under ~500 lines (with 3 justified exceptions at 514, 555, and 559 lines), submitted in 4 dependency waves. Rather than executing the cherry-picking directly, this plan creates 11 independent tasks -- one per sub-PR -- each with a detailed report artifact that serves as the complete spec for that sub-PR. Each task can then go through its own `/research` -> `/plan` -> `/implement` lifecycle independently.

### Research Integration

The research report (01_pr1-decomposition-research.md) provided the complete file inventory (14 new files, 21 modified files), dependency graph, line counts per sub-PR, and the 4-wave submission plan. Task 123 (bib references) has been completed, adding ChagrovZakharyaschev1997, Prawitz1965, TroelstraVanDalen1988, and HughesCresswell1996 to `references.bib` and updating 15 Lean files with Mathlib-style citations on the `pr1/foundations-logic` branch.

### Prior Plan Reference

Revised from v1 (same filename). Original plan had 11 phases for direct cherry-pick execution; revised to 2 phases for task creation with report artifacts, enabling independent lifecycle management per sub-PR.

### Roadmap Alignment

This plan advances the following roadmap components:
- Propositional proof system and metalogic (Foundations/Logic and Logics/Propositional modules)
- Natural deduction framework and ND-Hilbert equivalence
- Modal logical equivalence infrastructure

## Goals & Non-Goals

**Goals**:
- Create 11 independent tasks (one per sub-PR), each with a detailed report artifact serving as the complete spec
- Each report artifact specifies: exact file list with paths, branch name, PR description text, estimated LOC, dependencies on prior sub-PRs, bib references needed, and extraction instructions
- Declare task dependencies in state.json matching the 4-wave submission order
- Enable each sub-PR task to go through its own `/research` -> `/plan` -> `/implement` lifecycle
- Preserve all 11 sub-PR definitions from the research report exactly

**Non-Goals**:
- Actually executing the cherry-picking or branch creation (deferred to per-task implementation)
- Writing new Lean code or proofs (all content exists on `pr1/foundations-logic`)
- Submitting any PRs during this plan's execution
- Addressing upstream review comments on proof style or naming

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| 11 task creation is a large batch; state.json corruption if interrupted | High | Low | Use atomic jq updates; verify state.json validity after each task creation |
| Report artifacts may drift from actual branch content if upstream main changes | Medium | Medium | Reports reference the `pr1/foundations-logic` branch content as of the research date; implementers should verify file lists against current branch state |
| Dependency graph complexity across 11 tasks may confuse tooling | Low | Medium | Phase 2 explicitly verifies acyclicity and wave ordering |
| Task numbers are not contiguous with sub-PR numbers (tasks 125-135 vs sub-PRs 1.1-1.11) | Low | High | Each report artifact maps task number to sub-PR number clearly in its header |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases are sequential: Phase 2 verifies the tasks created in Phase 1.

---

### Phase 1: Create All 11 Sub-PR Tasks with Report Artifacts [NOT STARTED]

**Goal**: Create 11 tasks in state.json (tasks 125-135), one per sub-PR, each with a detailed report artifact in `specs/{NNN}_{slug}/reports/01_{short-slug}.md` that serves as the complete spec for that sub-PR. Declare inter-task dependencies matching the 4-wave submission plan.

**Tasks**:
- [ ] Create task 125: `subpr_1_1_hilbert_hierarchy_refactoring` (Wave 1, no dependencies)
- [ ] Create task 126: `subpr_1_2_intmin_instances` (Wave 2, depends on 125)
- [ ] Create task 127: `subpr_1_3_propositional_semantics` (Wave 2, depends on 125)
- [ ] Create task 128: `subpr_1_4_nd_derived_rules` (Wave 2, depends on 125)
- [ ] Create task 129: `subpr_1_5_modal_logical_equivalence` (Wave 2, depends on 125)
- [ ] Create task 130: `subpr_1_6_classical_soundness_completeness` (Wave 3, depends on 126, 127)
- [ ] Create task 131: `subpr_1_7_intuitionistic_soundness_completeness` (Wave 3, depends on 127, 130)
- [ ] Create task 132: `subpr_1_8_minimal_soundness_completeness` (Wave 3, depends on 127, 130)
- [ ] Create task 133: `subpr_1_9_fromhilbert_parameterization` (Wave 3, depends on 126)
- [ ] Create task 134: `subpr_1_10_hilbert_derived_rules` (Wave 4, depends on 133)
- [ ] Create task 135: `subpr_1_11_nd_hilbert_equivalence` (Wave 4, depends on 128, 133)
- [ ] For each task, create `specs/{NNN}_{slug}/reports/01_{short-slug}.md` with the detailed report artifact (see Report Artifact Template below)
- [ ] Update state.json with all 11 tasks, dependencies, and `topic: "Submit PRs"`
- [ ] Regenerate TODO.md via `bash .claude/scripts/generate-todo.sh`

**Report Artifact Template** (each of the 11 reports must contain):

```markdown
# Sub-PR Spec: {Sub-PR Number} -- {Title}

## Task Mapping
- **Task**: {task_number} - {task_name}
- **Sub-PR**: 1.{X} of 11
- **Wave**: {wave_number}
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `{branch_name}`
- **Base**: upstream `main` (after dependencies merge)

## Files

| File | Type | Lines | Notes |
|------|------|------:|-------|
| {path} | NEW/MOD | {lines} | {description} |
...
- **Cslib.lean**: +{N} import lines
- **Total**: ~{N} insertions

## Dependencies
- **Requires merged**: {list of sub-PR task numbers that must merge first, or "None"}
- **Required by**: {list of sub-PR task numbers that depend on this}

## Extraction Instructions
{How to extract these files from `pr1/foundations-logic` -- copy new files directly, apply diff for modifications}

## PR Description

{Complete PR description text following CSLib CONTRIBUTING.md conventions, ready to use}

## Bib References
{Which references from task 123 are relevant, or "None"}

## Estimated LOC
- Insertions: ~{N}
- Deletions: ~{N}

## Verification
{CI commands to run before submission}
```

**Detailed Report Content per Task**:

**Task 125 (Sub-PR 1.1): 3-Tier Hilbert Hierarchy Refactoring**
- Branch: `propositional/hilbert-hierarchy-refactor`
- Files: 12 modified files (see research report for full list)
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
- Estimated: ~483 insertions, ~288 deletions
- Dependencies: none
- Required by: all other sub-PRs (125 is the foundation)

**Task 126 (Sub-PR 1.2): IntMin Instances**
- Branch: `propositional/intmin-instances`
- Files:
  - `Logics/Propositional/ProofSystem/Axioms.lean` (+51/-0) -- MOD
  - `Logics/Propositional/ProofSystem/IntMinInstances.lean` (NEW, 109 lines)
  - `Cslib.lean` (+1 import)
- Estimated: ~211 insertions
- Dependencies: 125
- Required by: 130, 131, 132, 133

**Task 127 (Sub-PR 1.3): Propositional Semantics**
- Branch: `propositional/semantics`
- Files:
  - `Logics/Propositional/Semantics/Basic.lean` (NEW, 47 lines)
  - `Logics/Propositional/Semantics/Kripke.lean` (NEW, 134 lines)
  - `Cslib.lean` (+2 imports)
- Estimated: ~181 insertions
- Dependencies: 125
- Required by: 130, 131, 132

**Task 128 (Sub-PR 1.4): ND Derived Rules (Standalone)**
- Branch: `propositional/nd-derived-rules`
- Files:
  - `Logics/Propositional/NaturalDeduction/DerivedRules.lean` (NEW, 387 lines)
  - `Cslib.lean` (+1 import)
- Estimated: ~387 insertions
- Dependencies: 125 (uses upstream NaturalDeduction/Basic.lean, needs MinimalHilbert from 1.1)
- Required by: 135

**Task 129 (Sub-PR 1.5): Modal Logical Equivalence**
- Branch: `modal/logical-equivalence`
- Files:
  - `Logics/Modal/LogicalEquivalence.lean` (NEW, 132 lines)
  - `Logics/Modal/Basic.lean` (+19/-11) -- MOD
  - `Logics/Modal/Denotation.lean` (+2/-2) -- MOD
  - `Cslib.lean` (+1 import)
- Estimated: ~151 insertions
- Dependencies: 125
- Required by: none (independent leaf)

**Task 130 (Sub-PR 1.6): Classical Soundness + Completeness**
- Branch: `propositional/classical-soundness-completeness`
- Files:
  - `Logics/Propositional/Metalogic/Soundness.lean` (NEW, 87 lines)
  - `Logics/Propositional/Metalogic/Completeness.lean` (NEW, 295 lines)
  - `Cslib.lean` (+2 imports)
- Estimated: ~382 insertions
- Dependencies: 126, 127
- Required by: 131, 132
- Bib references: ChagrovZakharyaschev1997

**Task 131 (Sub-PR 1.7): Intuitionistic Soundness + Completeness**
- Branch: `propositional/intuitionistic-soundness-completeness`
- Files:
  - `Logics/Propositional/Metalogic/IntSoundness.lean` (NEW, 103 lines)
  - `Logics/Propositional/Metalogic/IntLindenbaum.lean` (NEW, 325 lines)
  - `Logics/Propositional/Metalogic/IntCompleteness.lean` (NEW, 127 lines)
  - `Cslib.lean` (+3 imports)
- Estimated: ~555 insertions (over 500-line target; semantically indivisible)
- Dependencies: 127, 130
- Required by: none (independent leaf)
- Bib references: ChagrovZakharyaschev1997, TroelstraVanDalen1988

**Task 132 (Sub-PR 1.8): Minimal Soundness + Completeness**
- Branch: `propositional/minimal-soundness-completeness`
- Files:
  - `Logics/Propositional/Metalogic/MinSoundness.lean` (NEW, 96 lines)
  - `Logics/Propositional/Metalogic/MinLindenbaum.lean` (NEW, 275 lines)
  - `Logics/Propositional/Metalogic/MinCompleteness.lean` (NEW, 143 lines)
  - `Cslib.lean` (+3 imports)
- Estimated: ~514 insertions (over 500-line target; semantically indivisible)
- Dependencies: 127, 130
- Required by: none (independent leaf)
- Bib references: ChagrovZakharyaschev1997

**Task 133 (Sub-PR 1.9): ND-Hilbert Bridge Parameterization**
- Branch: `propositional/fromhilbert-parameterize`
- Files:
  - `Logics/Propositional/NaturalDeduction/FromHilbert.lean` (+146/-63) -- MOD
- Estimated: ~146 insertions, ~63 deletions
- Dependencies: 126
- Required by: 134, 135

**Task 134 (Sub-PR 1.10): Hilbert-Style Derived Connective Rules**
- Branch: `propositional/hilbert-derived-rules`
- Files:
  - `Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` (NEW, 559 lines)
  - `Cslib.lean` (+1 import)
- Estimated: ~559 insertions (over 500-line target; indivisible -- covers negation, top, conjunction, disjunction, biconditional at 3 logic levels)
- Dependencies: 133
- Required by: none (independent leaf)

**Task 135 (Sub-PR 1.11): ND-Hilbert Extensional Equivalence**
- Branch: `propositional/nd-hilbert-equivalence`
- Files:
  - `Logics/Propositional/NaturalDeduction/Equivalence.lean` (NEW, 231 lines)
  - `Cslib.lean` (+1 import)
- Estimated: ~231 insertions
- Dependencies: 128, 133
- Required by: none (independent leaf)

**Timing**: 2.5 hours (11 task creations with report artifacts)

**Depends on**: none

---

### Phase 2: Verify Task Dependencies and Ordering [NOT STARTED]

**Goal**: Verify all 11 sub-PR tasks have correct dependencies declared in state.json, confirm the dependency graph is acyclic, and validate that the wave ordering matches the research findings.

**Tasks**:
- [ ] Read state.json and extract dependency graph for tasks 125-135
- [ ] Verify dependency graph is a DAG (no cycles)
- [ ] Verify wave assignment matches research report:
  - Wave 1: 125 (no deps)
  - Wave 2: 126, 127, 128, 129 (all depend on 125 only)
  - Wave 3: 130, 131, 132, 133 (depend on Wave 1-2 tasks)
  - Wave 4: 134, 135 (depend on Wave 2-3 tasks)
- [ ] Verify each report artifact exists and contains all required sections
- [ ] Verify total LOC across all 11 reports sums to ~3,729 insertions
- [ ] Cross-check file lists: every file in the research report appears in exactly one sub-PR report

**Timing**: 30 minutes

**Depends on**: 1

---

## Sub-PR Summary Table

| Task | Sub-PR | Title | ~LOC | Branch | Wave | Dependencies |
|------|--------|-------|-----:|--------|------|-------------|
| 125 | 1.1 | 3-tier Hilbert hierarchy refactoring | 483 | `propositional/hilbert-hierarchy-refactor` | 1 | -- |
| 126 | 1.2 | Axiom extensions + IntMin instances | 211 | `propositional/intmin-instances` | 2 | 125 |
| 127 | 1.3 | Propositional semantics (bivalent + Kripke) | 181 | `propositional/semantics` | 2 | 125 |
| 128 | 1.4 | ND derived connective rules (standalone) | 387 | `propositional/nd-derived-rules` | 2 | 125 |
| 129 | 1.5 | Modal logical equivalence + Basic update | 151 | `modal/logical-equivalence` | 2 | 125 |
| 130 | 1.6 | Classical soundness + completeness | 382 | `propositional/classical-soundness-completeness` | 3 | 126, 127 |
| 131 | 1.7 | Intuitionistic soundness + completeness | 555 | `propositional/intuitionistic-soundness-completeness` | 3 | 127, 130 |
| 132 | 1.8 | Minimal soundness + completeness | 514 | `propositional/minimal-soundness-completeness` | 3 | 127, 130 |
| 133 | 1.9 | ND-Hilbert bridge parameterization | 146 | `propositional/fromhilbert-parameterize` | 3 | 126 |
| 134 | 1.10 | Hilbert-style derived connective rules | 559 | `propositional/hilbert-derived-rules` | 4 | 133 |
| 135 | 1.11 | ND-Hilbert extensional equivalence | 231 | `propositional/nd-hilbert-equivalence` | 4 | 128, 133 |

## PR Description Template

Each sub-PR report artifact should include a PR description following this structure:

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

## Testing & Validation

- [ ] All 11 tasks exist in state.json with correct project_number, project_name, status, task_type, dependencies, and topic
- [ ] All 11 report artifacts exist at `specs/{NNN}_{slug}/reports/01_{short-slug}.md`
- [ ] Each report contains all required sections (Task Mapping, Branch, Files, Dependencies, Extraction Instructions, PR Description, Bib References, Estimated LOC, Verification)
- [ ] Dependency graph across tasks 125-135 is acyclic
- [ ] Wave ordering matches research report (Wave 1: 125; Wave 2: 126-129; Wave 3: 130-133; Wave 4: 134-135)
- [ ] Total insertions across all 11 reports sum to approximately 3,729
- [ ] Every file from the research report's inventory appears in exactly one sub-PR report
- [ ] TODO.md correctly reflects all 11 new tasks with status [NOT STARTED]

## Artifacts & Outputs

- This plan file: `specs/124_plan_pr1_decomposition_into_smaller_prs/plans/01_pr1-decomposition-plan.md`
- 11 task entries in state.json (tasks 125-135)
- 11 report artifacts:
  - `specs/125_subpr_1_1_hilbert_hierarchy_refactoring/reports/01_hilbert-hierarchy-spec.md`
  - `specs/126_subpr_1_2_intmin_instances/reports/01_intmin-instances-spec.md`
  - `specs/127_subpr_1_3_propositional_semantics/reports/01_propositional-semantics-spec.md`
  - `specs/128_subpr_1_4_nd_derived_rules/reports/01_nd-derived-rules-spec.md`
  - `specs/129_subpr_1_5_modal_logical_equivalence/reports/01_modal-logical-equiv-spec.md`
  - `specs/130_subpr_1_6_classical_soundness_completeness/reports/01_classical-soundness-spec.md`
  - `specs/131_subpr_1_7_intuitionistic_soundness_completeness/reports/01_intuitionistic-soundness-spec.md`
  - `specs/132_subpr_1_8_minimal_soundness_completeness/reports/01_minimal-soundness-spec.md`
  - `specs/133_subpr_1_9_fromhilbert_parameterization/reports/01_fromhilbert-param-spec.md`
  - `specs/134_subpr_1_10_hilbert_derived_rules/reports/01_hilbert-derived-rules-spec.md`
  - `specs/135_subpr_1_11_nd_hilbert_equivalence/reports/01_nd-hilbert-equiv-spec.md`

## Rollback/Contingency

- If task creation is interrupted partway, delete any partially-created tasks from state.json and regenerate TODO.md
- If the decomposition strategy is rejected by the reviewer, fall back to the monolithic `pr1/foundations-logic` branch (still intact)
- Individual sub-PR tasks can be abandoned independently without affecting others (except downstream dependencies)
- The original branch `pr1/foundations-logic` is preserved as a reference throughout the process and should not be deleted until all 11 sub-PRs are merged
