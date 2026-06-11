# Implementation Plan: Sub-PR 1.1 Hilbert Hierarchy Extraction Chain

- **Task**: 125 - Sub-PR 1.1: 3-tier Hilbert hierarchy refactoring
- **Status**: [NOT STARTED]
- **Effort**: 10 hours (implementation) + variable wait time (PR review cycles)
- **Dependencies**: None (Wave 1 -- first PR in the chain)
- **Research Inputs**:
  - reports/01_hilbert-hierarchy-spec.md (original 13-file spec from task 124)
  - reports/02_research-report.md (discovery: 21 files needed, not 13; upstream has none of the files)
  - reports/03_feedback-analysis.md (reviewer feedback: must decompose into 5+ PRs under 500 lines each)
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Task 125 was originally scoped as a single sub-PR extracting 13 modified files. Research revealed that (a) upstream has none of these files (they are all new, not modifications), (b) 5 additional dependency files are required, and (c) the resulting ~4,000-line diff is 8x over the reviewer-mandated 500-line limit for new contributors. This plan implements the reviewer-directed re-decomposition: a chain of 5-6 small PRs extracted from local `main` to upstream `main`, preceded by Zulip topic creation for community coordination. Definition of done: all foundation-layer files from the original sub-PR 1.1 scope are merged into upstream via sequential small PRs.

### Research Integration

Three research reports inform this plan:

1. **Report 01** (spec): Identified 13 files for a single sub-PR. Assumed all were modifications to existing upstream files.
2. **Report 02** (round 1): Discovered 5 missing dependency files, upstream has almost none of these files (12/13 are new), `ProofSystem.lean` needs curation (extra modal classes from tasks 92/100), `Theorems.lean` barrel imports cross-PR modal/temporal modules, `NaturalDeduction/Basic.lean` must be updated for the Proposition type change.
3. **Report 03** (round 2 -- feedback analysis): Analyzed 3 reviewer responses, determined that the scope must be reduced to <500 diff lines per PR. Recommended a 5-PR chain starting with a ~300-line Proposition type refactoring. Provided Zulip topic strategy, AI disclosure template, and PR description structure.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the foundational layer of the "Porting BimodalLogic to CSLib" roadmap. Specifically:
- Establishes `Foundations/Logic/Connectives.lean` and `Foundations/Logic/ProofSystem.lean` infrastructure
- Enables all downstream module layers (Modal, Temporal, Bimodal) documented in the roadmap

## Goals & Non-Goals

**Goals**:
- Create Zulip topic presenting the development plan to the CSLib community
- Extract and submit 5-6 PRs (each <500 diff lines) covering all foundation-layer files
- Each PR builds cleanly against upstream `main` (or against the previous PR in the chain)
- Address all 3 reviewer concerns: small PRs (Chris), Zulip coordination (Alexandre), references + AI disclosure (Ching-Tsun)
- Update task 125 state to reflect the new decomposition structure

**Non-Goals**:
- Modal-specific theorem files (`Modal/Basic.lean`, `Modal/S5.lean`) -- belong to task 130 (sub-PR 1.5)
- Temporal-specific derived theorems (`Temporal/TemporalDerived.lean`) -- belong to later sub-PRs
- Bimodal or embedding files -- belong to tasks 131-135
- Getting all PRs merged within this plan's execution window (merge depends on reviewer availability)
- Modifying any files on local `main` (extraction is copy-only)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Lukasiewicz convention rejected by reviewers | H | M | Present rationale on Zulip first; explain reuse benefits across logic types; reference Chagrov & Zakharyaschev |
| NaturalDeduction changes contentious (removes 8 rules, adds 3) | M | M | Explain mathematical equivalence in PR description; reference ongoing EFQ Zulip discussion |
| PR chain creates review bottleneck (each waits for previous merge) | M | M | Work on other tasks (126-135 research/planning) while waiting; keep PRs truly independent where possible |
| ProofSystem.lean curation error (include wrong modal classes) | M | L | Carefully diff against `pr1/foundations-logic`; test build after curation |
| Cslib.lean import additions conflict with concurrent upstream PRs | L | M | Add only imports relevant to each specific sub-PR; regenerate with `lake exe mk_all` |
| references.bib diff includes entries not needed for first PR | L | L | Only include ChagrovZakharyaschev1997 in PR 1.1a; defer Prawitz and Troelstra to later PRs |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 7 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel. Wave 1 has two parallel tasks: Zulip topic creation and state management updates. Waves 2-6 are sequential because each PR depends on its predecessor being merged.

---

### Phase 1: Zulip Topic Creation [NOT STARTED]

**Goal**: Establish community coordination channel before submitting any code, per Alexandre's guidance and CONTRIBUTING.md requirements.

**Tasks**:
- [ ] Draft Zulip topic post with title: "Propositional/Modal/Temporal logic hierarchy: development plan"
- [ ] Include sections: Introduction (background), Design approach (4-layer architecture: connectives -> axioms -> proof system -> instances), Reuse story (polymorphic definitions across logic types), PR plan (5-6 PRs with estimated sizes), Request for feedback (Lukasiewicz convention, connective typeclasses, decomposition)
- [ ] Post to CSLib channel on Zulip at `https://leanprover.zulipchat.com/`
- [ ] Update PR #633 description to reference the Zulip topic and mark as draft with note: "Extracting as a series of smaller PRs. See [Zulip topic link]."
- [ ] Wait 1-2 days for initial reactions before submitting PR 1.1a

**Timing**: 1 hour (drafting) + 1-2 days (waiting for feedback)

**Depends on**: none

**Files to modify**:
- No local files modified (Zulip and GitHub are external)

**Verification**:
- Zulip topic is live and accessible
- PR #633 is marked as draft with Zulip link

---

### Phase 2: PR 1.1a -- Proposition Type to Lukasiewicz Convention [NOT STARTED]

**Goal**: Submit the first PR introducing `Connectives.lean` and refactoring `Proposition` from `and/or/impl` primitives to `bot/imp` primitives with derived connectives. Target: ~302 diff lines across 6 files.

**Tasks**:
- [ ] Create branch from upstream main:
  ```bash
  git fetch upstream
  git checkout -b refactor/proposition-lukasiewicz upstream/main
  ```
- [ ] Copy core files from local `main`:
  ```bash
  git checkout main -- Cslib/Foundations/Logic/Connectives.lean          # NEW, 98 lines
  git checkout main -- Cslib/Logics/Propositional/Defs.lean              # MODIFY, +50/-35
  git checkout main -- Cslib/Logics/Propositional/NaturalDeduction/Basic.lean  # MODIFY, +31/-69
  git checkout main -- Cslib/Foundations/Logic/InferenceSystem.lean       # MODIFY, +3/-3
  ```
- [ ] Add `ChagrovZakharyaschev1997` entry to `references.bib` (only this one entry, not Prawitz or Troelstra)
- [ ] Add import line to `Cslib.lean`: `public import Cslib.Foundations.Logic.Connectives`
- [ ] Verify `Defs.lean` does NOT include bib reference formatting from task 123 (use local `main` version which is clean)
- [ ] Verify `NaturalDeduction/Basic.lean` uses local `main` version (no bib formatting changes)
- [ ] Run `lake build` -- verify clean build
- [ ] Run full CI check suite:
  ```bash
  lake test && lake lint && lake exe lint-style
  lake exe checkInitImports && lake exe mk_all --module --check
  ```
- [ ] Verify no `sorry` in modified files: `grep -rn "sorry" Cslib/Foundations/Logic/Connectives.lean Cslib/Logics/Propositional/Defs.lean Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
- [ ] Draft PR description using template from report 03: summary, context (link Zulip topic + PR #633), test plan, AI disclosure
- [ ] Include reference citation: "References: Chagrov & Zakharyaschev, *Modal Logic* (1997), Chapter 1" in PR description and `Defs.lean` module docstring
- [ ] Submit PR with title: `refactor: Proposition type to Lukasiewicz convention`
- [ ] Post link in Zulip topic

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` -- NEW: connective typeclasses (HasBot, HasImp, etc.)
- `Cslib/Logics/Propositional/Defs.lean` -- MODIFY: Proposition type bot/imp, derived connectives
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- MODIFY: impI/impE/botE replacing 8 rules
- `Cslib/Foundations/Logic/InferenceSystem.lean` -- MODIFY: import visibility, docstring
- `references.bib` -- MODIFY: add ChagrovZakharyaschev1997 entry (+10 lines)
- `Cslib.lean` -- MODIFY: add 1 import line

**Verification**:
- `lake build` passes on the new branch
- `git diff upstream/main --stat` shows <500 diff lines
- PR is open and linked from Zulip topic

---

### Phase 3: PR 1.1b -- Polymorphic Axiom Definitions [NOT STARTED]

**Goal**: After PR 1.1a merges, submit `Axioms.lean` containing polymorphic axiom formulas over connective typeclasses. Target: ~300 diff lines.

**Tasks**:
- [ ] Create branch from upstream main (after 1.1a is merged):
  ```bash
  git fetch upstream
  git checkout -b feat/polymorphic-axiom-definitions upstream/main
  ```
- [ ] Copy `Axioms.lean` from local `main`:
  ```bash
  git checkout main -- Cslib/Foundations/Logic/Axioms.lean    # NEW, 298 lines
  ```
- [ ] Add import line to `Cslib.lean`: `public import Cslib.Foundations.Logic.Axioms`
- [ ] Run `lake build` and full CI suite
- [ ] Verify no `sorry`: `grep -rn "sorry" Cslib/Foundations/Logic/Axioms.lean`
- [ ] Draft PR description: summary (polymorphic axiom abbreviations for ImplyK, ImplyS, EFQ, Peirce, modal K/T/4/B/5/D, temporal BX1-BX13), reference Zulip topic, AI disclosure
- [ ] Submit PR with title: `feat: polymorphic axiom definitions`
- [ ] Post link in Zulip topic

**Timing**: 1 hour

**Depends on**: 2 (PR 1.1a must be merged upstream)

**Files to modify**:
- `Cslib/Foundations/Logic/Axioms.lean` -- NEW: 298 lines of axiom abbreviations
- `Cslib.lean` -- MODIFY: add 1 import line

**Verification**:
- `lake build` passes
- `git diff upstream/main --stat` shows <500 diff lines
- No modal/temporal-specific axioms leak that would belong to later PRs

---

### Phase 4: PR 1.1c -- Hilbert Proof System Typeclass Hierarchy [NOT STARTED]

**Goal**: After PR 1.1b merges, submit `ProofSystem.lean` with the 3-tier propositional hierarchy and modal extensions. Target: ~490 diff lines. Requires curation to handle extra modal classes from tasks 92/100.

**Tasks**:
- [ ] Create branch from upstream main (after 1.1b is merged):
  ```bash
  git fetch upstream
  git checkout -b feat/hilbert-proof-system-hierarchy upstream/main
  ```
- [ ] Copy `ProofSystem.lean` from local `main`:
  ```bash
  git checkout main -- Cslib/Foundations/Logic/ProofSystem.lean   # NEW, 486 lines
  ```
- [ ] **CURATE ProofSystem.lean**: Review content and decide inclusion of extra modal classes (ModalTHilbert, ModalDHilbert, ModalS4Hilbert, etc. from tasks 92/100). Two options:
  - Option A (recommended by report 02): Include all modal classes (~486 lines total). They are purely additive and avoid later merge conflicts.
  - Option B: Strip extra modal classes, keep only propositional 3-tier + original K/S5. Reduces to ~370 lines but creates merge conflict surface.
  - Decision must consider whether 486 lines is close enough to the 500-line limit. If reviewers object, offer to split into propositional-only (~100 lines) + modal (~386 lines).
- [ ] Add import line to `Cslib.lean`: `public import Cslib.Foundations.Logic.ProofSystem`
- [ ] Run `lake build` and full CI suite
- [ ] Verify no `sorry`: `grep -rn "sorry" Cslib/Foundations/Logic/ProofSystem.lean`
- [ ] Draft PR description: summary (3-tier hierarchy: MinimalHilbert < IntuitionisticHilbert < ClassicalHilbert, plus modal/temporal extensions), reference Zulip topic, AI disclosure
- [ ] Submit PR with title: `feat: Hilbert proof system typeclass hierarchy`
- [ ] Post link in Zulip topic

**Timing**: 1.5 hours (extra time for curation)

**Depends on**: 3 (PR 1.1b must be merged upstream)

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` -- NEW: 486 lines (typeclass hierarchy)
- `Cslib.lean` -- MODIFY: add 1 import line

**Verification**:
- `lake build` passes
- `git diff upstream/main --stat` shows <=500 diff lines
- No extra modal typeclasses leak that reference files not yet upstream

---

### Phase 5: PR 1.1d -- Propositional Hilbert Instances and Derivation Trees [NOT STARTED]

**Goal**: After PR 1.1c merges, submit the concrete propositional Hilbert system: axiom inductive, derivation trees, instances, and list helpers. Target: ~430 diff lines.

**Tasks**:
- [ ] Create branch from upstream main (after 1.1c is merged):
  ```bash
  git fetch upstream
  git checkout -b feat/propositional-hilbert-instances upstream/main
  ```
- [ ] Copy files from local `main`:
  ```bash
  git checkout main -- Cslib/Logics/Propositional/ProofSystem/Axioms.lean       # NEW, 106 lines
  git checkout main -- Cslib/Logics/Propositional/ProofSystem/Derivation.lean    # NEW, 163 lines
  git checkout main -- Cslib/Logics/Propositional/ProofSystem/Instances.lean     # NEW, 90 lines
  git checkout main -- Cslib/Foundations/Data/ListHelpers.lean                   # NEW, 74 lines
  ```
- [ ] Add import lines to `Cslib.lean`:
  ```
  public import Cslib.Logics.Propositional.ProofSystem.Axioms
  public import Cslib.Logics.Propositional.ProofSystem.Derivation
  public import Cslib.Logics.Propositional.ProofSystem.Instances
  public import Cslib.Foundations.Data.ListHelpers
  ```
- [ ] Run `lake build` and full CI suite
- [ ] Verify no `sorry` in all 4 new files
- [ ] Draft PR description: summary (concrete propositional axiom inductive, derivation trees, HilbertCl/HilbertInt/HilbertMin instances), reference Zulip topic, AI disclosure
- [ ] Submit PR with title: `feat: propositional Hilbert instances and derivation trees`
- [ ] Post link in Zulip topic

**Timing**: 1 hour

**Depends on**: 4 (PR 1.1c must be merged upstream)

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- NEW: 106 lines (PropositionalAxiom inductive)
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- NEW: 163 lines (DerivationTree)
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` -- NEW: 90 lines (Hilbert instances)
- `Cslib/Foundations/Data/ListHelpers.lean` -- NEW: 74 lines (list utility lemmas)
- `Cslib.lean` -- MODIFY: add 4 import lines

**Verification**:
- `lake build` passes
- `git diff upstream/main --stat` shows <500 diff lines (total ~437)
- Instances correctly reference MinimalHilbert/IntuitionisticHilbert/ClassicalHilbert from ProofSystem.lean

---

### Phase 6: PR 1.1e/f -- Theorem Stratification and Metalogic [NOT STARTED]

**Goal**: After PR 1.1d merges, submit the remaining theorem and metalogic files. This phase covers ~2,150 lines across 10 files and MUST be split into 2-3 sub-PRs. Exact decomposition depends on reviewer feedback from earlier PRs.

**Tasks**:
- [ ] Assess remaining file inventory and sizes:

  | File | Lines | Candidate PR |
  |------|-------|-------------|
  | `Theorems/Propositional/Core.lean` | 311 | 1.1e |
  | `Theorems/Combinators.lean` | 339 | 1.1e |
  | `Theorems/BigConj.lean` | 142 | 1.1e |
  | `Theorems/Temporal/FrameConditions.lean` | 89 | 1.1e |
  | `Theorems.lean` (reduced barrel) | ~45 | 1.1e (if fits) or 1.1f |
  | `Theorems/Propositional/Connectives.lean` | 539 | 1.1f (alone, near limit) |
  | `Metalogic/Consistency.lean` | 278 | 1.1g |
  | `Metalogic/DeductionHelpers.lean` | 120 | 1.1g |
  | `Metalogic/DeductionTheorem.lean` | 217 | 1.1g |
  | `Metalogic/MCS.lean` | 161 | 1.1g |

- [ ] **Proposed split** (subject to revision based on reviewer feedback):
  - **PR 1.1e** (~500 lines): `Core.lean` (311) + `BigConj.lean` (142) + reduced `Theorems.lean` (~45) = ~498
  - **PR 1.1f** (~500 lines): `Connectives.lean` (539, standalone), or `Combinators.lean` (339) + `FrameConditions.lean` (89) = ~428
  - **PR 1.1g** (~500 lines): remaining theorem files + all metalogic files. May itself need splitting.
- [ ] For each sub-PR: create branch, copy files from `main`, update `Cslib.lean`, verify build, submit
- [ ] Create reduced `Theorems.lean` barrel: exclude `Modal.Basic`, `Modal.S5`, `Temporal.TemporalDerived` imports. Include only propositional + BigConj + Combinators + FrameConditions.
- [ ] Ensure `FrameConditions.lean` builds without temporal-specific imports (verify import chain)
- [ ] For metalogic PRs, add `Prawitz1965` and `TroelstraVanDalen1988` to `references.bib` where referenced
- [ ] Each sub-PR gets AI disclosure and Zulip topic link

**Timing**: 3 hours (across 2-3 sub-PRs, each ~1 hour)

**Depends on**: 5 (PR 1.1d must be merged upstream)

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` -- NEW: 311 lines
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` -- NEW: 539 lines
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` -- NEW: 142 lines
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` -- NEW: 339 lines
- `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean` -- NEW: 89 lines
- `Cslib/Foundations/Logic/Theorems.lean` -- NEW: ~45 lines (reduced barrel)
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` -- NEW: 278 lines
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` -- NEW: 120 lines
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` -- NEW: 217 lines
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` -- NEW: 161 lines
- `Cslib.lean` -- MODIFY: add ~9 import lines (split across sub-PRs)
- `references.bib` -- MODIFY: add Prawitz1965, TroelstraVanDalen1988 entries where needed

**Verification**:
- Each sub-PR: `lake build` passes, <500 diff lines, no `sorry`
- Reduced `Theorems.lean` does NOT import modal/temporal-specific modules
- All theorem stratification correctly uses MinimalHilbert/IntuitionisticHilbert/ClassicalHilbert

---

### Phase 7: State Management and Task Updates [NOT STARTED]

**Goal**: Update task 125 state and downstream task descriptions (126-135) to reflect the new decomposition reality.

**Tasks**:
- [ ] Update task 125 description in `state.json` to note the re-decomposition into 5-6+ PRs
- [ ] Review tasks 126-135 dependency specifications: they all depend on task 125, which now represents a chain of PRs rather than a single PR. No change needed unless individual tasks have file-level dependencies on specific sub-PR files.
- [ ] After each PR merges, update task 125 status notes with merge confirmation
- [ ] When all PRs in the chain are merged, mark task 125 as completed with `completion_summary`

**Timing**: 1 hour (spread across the PR chain lifecycle)

**Depends on**: none (can start immediately, runs in parallel with Phase 1)

**Files to modify**:
- `specs/state.json` -- update task 125 metadata
- `specs/TODO.md` -- regenerated from state.json

**Verification**:
- `state.json` reflects accurate task 125 status
- Downstream tasks (126-135) have correct dependency chain

---

## Testing & Validation

- [ ] Each PR branch passes `lake build` against upstream `main` (or the previous merged PR)
- [ ] Each PR passes: `lake test`, `lake lint`, `lake exe lint-style`, `lake exe checkInitImports`, `lake exe mk_all --module --check`
- [ ] No `sorry` in any submitted file
- [ ] Each PR is <500 diff lines (verified with `git diff upstream/main --stat`)
- [ ] AI disclosure is present in every PR description
- [ ] References are cited where used in code (per Ching-Tsun's feedback)
- [ ] Zulip topic exists and all PRs are linked from it

## Artifacts & Outputs

- `specs/125_subpr_1_1_hilbert_hierarchy_refactoring/plans/01_implementation-plan.md` (this plan)
- Zulip topic: "Propositional/Modal/Temporal logic hierarchy: development plan"
- PR 1.1a: `refactor: Proposition type to Lukasiewicz convention` (~302 lines)
- PR 1.1b: `feat: polymorphic axiom definitions` (~300 lines)
- PR 1.1c: `feat: Hilbert proof system typeclass hierarchy` (~490 lines)
- PR 1.1d: `feat: propositional Hilbert instances and derivation trees` (~430 lines)
- PR 1.1e-g: Theorem stratification and metalogic (2-3 PRs, each <500 lines)

## Rollback/Contingency

- **If Lukasiewicz convention is rejected**: The Zulip topic will surface this early. Pivot to keeping upstream's `and/or/impl` primitives and adapt the hierarchy to work with them. This is a significant redesign affecting all downstream files.
- **If a PR breaks upstream CI**: Fix on the PR branch (push new commits, do not force-push). All PRs target upstream `main` directly, so conflicts are isolated.
- **If review bottleneck stalls the chain**: Work on other tasks (126-135 research/planning) while waiting. The chain order is strict for code dependencies but flexible for timing.
- **If ProofSystem.lean is too large**: Split into propositional-only (~100 lines) and modal-extensions (~386 lines) sub-PRs.
- **If reviewer wants different decomposition**: Adapt based on Zulip feedback. The plan's phase 6 is intentionally flexible about exact file groupings.
