# Implementation Plan: Task #12

- **Task**: 12 - Coordinate cslib PR submission for Bimodal Logic integration
- **Status**: [PARTIAL]
- **Effort**: 8 hours (coordination effort spread across PR submission timeline)
- **Dependencies**: None (runs in parallel with porting tasks 2-11, 20-23)
- **Research Inputs**: specs/012_coordinate_cslib_pr_submission_bimodal_logic/reports/01_pr-coordination.md
- **Artifacts**: plans/01_pr-coordination-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Coordinate the submission of 14 PRs to the cslib repository for the modular temporal logic integration. The process begins with a Zulip discussion to get maintainer buy-in and namespace confirmation, followed by CI environment validation, and then wave-by-wave PR submission following the dependency graph: 4 standalone module PRs (Foundations, Modal, Temporal, TempSem) and 10 bimodal porting PRs (tasks 2-11). Each PR requires full CI compliance (lake build, lake shake, linters, zero sorry, Apache 2.0 headers) and reviewer feedback turnaround within 48 hours.

### Research Integration

Key findings from the research report (01_pr-coordination.md):
- cslib is an independent repository at `github.com/leanprover/cslib`, not a Mathlib fork
- Zulip pre-coordination is mandatory for major developments before any PR submission
- There is a namespace inconsistency (`Cslib.Logic.*` vs `Cslib.Logics.*`) that must be resolved with maintainers
- AI usage disclosure is required in every PR description per Mathlib AI policy
- Working group proposal is recommended for a 14-PR effort
- CI requires 8 checks: lake build, lake test, checkInitImports, lake lint, lint-style, lake shake, zero sorry, copyright headers
- PR titles must use conventional commit prefixes (feat:, fix:, etc.)
- Large PRs (tasks 8, 9) may need splitting; completeness sorry requires proactive disclosure

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following ROADMAP.md items:
- Phase 4: Bimodal Porting (Tasks 2-11) -- all PR submissions for bimodal content
- PR pipeline milestone: "PR pipeline complete after Task 12 finalized (all PRs merged to cslib main)"
- Success metric: "PR pipeline complete: all PRs merged to cslib main"

## Goals & Non-Goals

**Goals**:
- Open Zulip discussion and obtain maintainer buy-in for 14-PR modular architecture
- Confirm namespace convention (`Cslib.Logic.*` vs `Cslib.Logics.*`) before any porting work starts
- Submit all 14 PRs in correct dependency order with full CI compliance
- Manage review cycles to maintain momentum (48-hour feedback turnaround)
- Track PR status across all waves and update coordination state

**Non-Goals**:
- Actually porting the code (handled by tasks 2-11, 20-23)
- Fixing CI failures in ported code (handled by individual porting tasks)
- Splitting large PRs proactively (only if maintainers request it)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Namespace rejection after work started | H | M | Confirm namespace via Zulip before task 2 starts (Phase 1 gate) |
| Maintainer requests architectural changes | H | M | Open Zulip thread early; present modular architecture; get buy-in before coding |
| Large PRs (tasks 8, 9) require splitting | M | H | Pre-plan 9a/9b split; discuss with maintainers proactively in Phase 1 |
| Sorry in completeness proof (task 8) blocks merge | H | H | Flag proactively in PR description; track sorry-elimination upstream |
| Review latency stalls dependent PRs | M | M | Submit PRs early; ping Zulip after 1 week without review activity |
| AI use policy creates review friction | L | L | Disclose clearly in every PR description per Mathlib AI policy |
| lakefile.toml linter incompatibilities | M | L | Run full CI suite locally before each PR submission |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Zulip Discussion and Working Group Proposal [PARTIAL]

**Goal**: Obtain maintainer buy-in for the 14-PR modular architecture and confirm the namespace convention before any porting PRs are submitted.

**Tasks**:
- [x] Post working group proposal to Zulip `#CSLib` channel using the draft template from the research report *(completed: draft message created at coordination/zulip-proposal-draft.md — requires human to post)*
- [x] Include in the proposal: TM logic overview, modular architecture diagram (Foundations -> Modal/Temporal -> Bimodal), 14-PR wave plan, estimated scope (~35k lines), AI usage disclosure *(completed: included in draft)*
- [x] Ask the three critical questions: (1) namespace `Cslib.Logic.*` vs `Cslib.Logics.*`, (2) working group with dedicated channel, (3) scope/placement concerns *(completed: included in draft)*
- [ ] Monitor responses from key maintainers: @fmontesi (lead), @kim-em (CI), @eric-wieser (reviewer) *(requires human action: post to Zulip and await responses)*
- [ ] Proactively discuss large PR strategy for tasks 8 (~15k lines) and 9 (~10k lines) -- propose 9a/9b split *(included in draft; requires human follow-up)*
- [x] Record maintainer decisions in a coordination log within this task directory *(completed: coordination/coordination-log.md created)*

**Timing**: 1-2 hours active work + waiting for responses (allow 1-2 weeks for discussion)

**Depends on**: none

**Files to modify**:
- `specs/012_coordinate_cslib_pr_submission_bimodal_logic/` - coordination log file (new)

**Verification**:
- Zulip thread is open with proposal posted
- At least one maintainer has responded
- Namespace question has a clear answer
- No blocking concerns raised about scope/architecture

---

### Phase 2: Namespace Confirmation and CI Validation [PARTIAL]

**Goal**: Lock down the namespace convention and validate that the local CI pipeline produces clean results on the existing cslib codebase.

**Tasks**:
- [ ] Record the confirmed namespace decision from Phase 1 Zulip discussion *(requires human action: await Zulip response)*
- [ ] If namespace differs from current task descriptions: update all porting task descriptions (tasks 2-11, 20-23) in state.json and TODO.md *(requires human action: update after namespace confirmed)*
- [ ] Run the full CI checklist locally on the current cslib codebase to validate the toolchain: *(requires human action: run locally on cslib repo)*
  - [ ] `lake build` -- zero errors
  - [ ] `lake test` -- CslibTests pass
  - [ ] `lake exe checkInitImports` -- all files import Cslib.Init
  - [ ] `lake lint` -- environment linters pass
  - [ ] `lake exe lint-style` -- text linters pass
  - [ ] `lake shake --add-public --keep-implied --keep-prefix` -- imports minimized
- [x] Create a per-file PR submission checklist template for reuse across all 14 PRs *(completed: coordination/ci-checklist-template.md)*
- [x] Prepare the standard PR description template with AI disclosure section *(completed: coordination/pr-description-template.md)*
- [x] Confirm copyright header format matches cslib's CONTRIBUTING.md *(completed: format documented in ci-checklist-template.md and validate-pr-ci.sh)*

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `specs/012_coordinate_cslib_pr_submission_bimodal_logic/` - CI checklist template, PR description template (new files)
- `specs/state.json` - update task descriptions if namespace changed
- `specs/TODO.md` - update task descriptions if namespace changed

**Verification**:
- Namespace decision is documented and unambiguous
- Full CI suite passes locally on current cslib codebase
- PR description template exists with AI disclosure section
- Per-file checklist template ready for use by porting tasks

---

### Phase 3: Standalone Module PR Submission (Waves 1-3) [NOT STARTED]

**Goal**: Submit and shepherd the 4 standalone module PRs through review in the correct dependency order.

**Tasks**:
- [ ] **Wave 1 -- PR-Foundations (Task 20)**: Submit `feat(Foundations/Logic): add Hilbert theorem infrastructure` after task 20 completes
  - [ ] Verify CI passes locally before submission
  - [ ] Write PR description with scope summary, AI disclosure, and dependency context
  - [ ] Monitor review; address feedback within 48 hours
  - [ ] Confirm merge before proceeding to Wave 2
- [ ] **Wave 2 -- PR-Modal (Task 21)**: Submit `feat(Logics/Modal): add Modal proof system and theorems` after task 21 completes and PR-Foundations merged
  - [ ] Same CI + submission protocol
  - [ ] Note dependency on Foundations PR
- [ ] **Wave 2 -- PR-Temporal-Infra (Task 22)**: Submit `feat(Logics/Temporal): add Temporal proof system infrastructure and theorems` after task 22 completes and PR-Foundations merged (parallel with PR-Modal)
  - [ ] Same CI + submission protocol
- [ ] **Wave 3 -- PR-TempSem (Task 23)**: Submit `feat(Logics/Temporal): add Temporal semantics on linear orders` after task 23 completes and PR-Temporal-Infra merged
  - [ ] Same CI + submission protocol
- [ ] Update coordination log with PR URLs, review status, and merge dates for each

**Timing**: 2 hours active coordination (spread across weeks during review cycles)

**Depends on**: 2

**Files to modify**:
- cslib repository (PRs submitted to `leanprover/cslib`)
- `specs/012_coordinate_cslib_pr_submission_bimodal_logic/` - coordination log updates

**Verification**:
- All 4 standalone PRs submitted in correct order
- Each PR passes CI before submission
- All 4 PRs merged to cslib main
- No outstanding review comments

---

### Phase 4: Bimodal PR Submission (Waves 1-6) [NOT STARTED]

**Goal**: Submit and shepherd the 10 bimodal porting PRs through review following the dependency graph.

**Tasks**:
- [ ] **Bimodal Wave 1 -- PR-Syntax (Task 2)**: Submit `feat(Logics/Bimodal): add Syntax module` -- first bimodal PR, establishes review pattern
  - [ ] Verify CI passes, write PR description, monitor review
- [ ] **Bimodal Wave 2 -- PR-Semantics (Task 3)**: Submit after PR-Syntax merged
  - [ ] `feat(Logics/Bimodal): add Semantics module (TaskFrame, WorldHistory, Truth, Validity)`
- [ ] **Bimodal Wave 2 -- PR-ProofSystem (Task 4)**: Submit after PR-Syntax, PR-Foundations, PR-Temporal-Infra merged (parallel with PR-Semantics)
  - [ ] `feat(Logics/Bimodal): add ProofSystem module (42-axiom Axiom, DerivationTree)`
- [ ] **Bimodal Wave 3 -- PR-Perpetuity (Task 5)**: Submit after PR-ProofSystem, PR-Modal, PR-Temporal-Infra merged
  - [ ] `feat(Logics/Bimodal): add Theorems/Perpetuity module`
- [ ] **Bimodal Wave 3 -- PR-FrameConditions (Task 6)**: Submit after PR-Semantics and PR-ProofSystem merged
  - [ ] `feat(Logics/Bimodal): add FrameConditions and Soundness modules`
- [ ] **Bimodal Wave 3 -- PR-ConservativeExt (Task 11)**: Submit after PR-ProofSystem merged (independent of 5-10)
  - [ ] `feat(Logics/Bimodal): add Metalogic/ConservativeExtension module`
- [ ] **Bimodal Wave 4 -- PR-MCS (Task 7)**: Submit after PR-ProofSystem and PR-Perpetuity merged
  - [ ] `feat(Logics/Bimodal): add Metalogic/Core module (DeductionTheorem, MCS)`
- [ ] **Bimodal Wave 5 -- PR-Completeness (Task 8)**: Submit after PR-FrameConditions and PR-MCS merged
  - [ ] `feat(Logics/Bimodal): add Completeness theorem` -- disclose sorry in chronicle construction
  - [ ] Flag sorry proactively in PR description; discuss timeline for elimination
- [ ] **Bimodal Wave 5 -- PR-Decidability (Task 9)**: Submit after PR-ProofSystem and PR-MCS merged
  - [ ] `feat(Logics/Bimodal): add Metalogic/Decidability module (Tableau, FMP)`
  - [ ] If maintainers request split: submit 9a (Core tableau, ~5k) then 9b (FMP, ~4k)
- [ ] **Bimodal Wave 5 -- PR-Separation (Task 10)**: Submit after PR-ProofSystem, PR-Perpetuity, PR-MCS merged
  - [ ] `feat(Logics/Bimodal): add Metalogic/Separation module`
- [ ] Update coordination log after each PR submission, review cycle, and merge

**Timing**: 3 hours active coordination (spread across months during review cycles)

**Depends on**: 2

**Files to modify**:
- cslib repository (PRs submitted to `leanprover/cslib`)
- `specs/012_coordinate_cslib_pr_submission_bimodal_logic/` - coordination log updates

**Verification**:
- All 10 bimodal PRs submitted in correct dependency order
- No PR submitted before its dependencies are merged
- Each PR passes CI before submission
- Sorry in task 8 PR is disclosed and discussed with maintainers
- Large PRs (tasks 8, 9) handled per maintainer guidance (split if requested)

---

### Phase 5: Review Cycle Management and Completion [NOT STARTED]

**Goal**: Track all 14 PRs through to merge completion and close out the coordination task.

**Tasks**:
- [ ] Maintain a PR status tracking table with columns: Task, PR Title, PR URL, Submitted Date, Review Status, Merge Date
- [ ] For any PR under review longer than 1 week: ping on Zulip with a polite follow-up
- [ ] For any reviewer-requested changes: address within 48 hours, push updated branch, re-request review
- [ ] For any CI failures during review: fix locally, push fix, update PR
- [ ] After all 14 PRs merged: post a summary message to the Zulip working group thread
- [ ] Update ROADMAP.md success metrics: mark "PR pipeline complete: all PRs merged to cslib main" as done
- [ ] Close out task 12 with completion summary

**Timing**: 1 hour active work (spread across the full timeline)

**Depends on**: 3, 4

**Files to modify**:
- `specs/012_coordinate_cslib_pr_submission_bimodal_logic/` - final coordination summary
- `specs/ROADMAP.md` - mark PR pipeline milestone complete

**Verification**:
- All 14 PRs have status "merged" in tracking table
- Zulip working group thread has a completion post
- ROADMAP.md PR pipeline milestone marked done
- No outstanding review comments or open PRs

## Testing & Validation

- [ ] Full CI suite (8 checks) passes locally before each PR submission
- [ ] Each PR description includes AI usage disclosure
- [ ] Each PR uses correct conventional commit prefix (`feat:`, etc.)
- [ ] Each file in every PR has Apache 2.0 copyright header
- [ ] No PR submitted before its dependency PRs are merged
- [ ] Review feedback addressed within 48 hours for all PRs

## Artifacts & Outputs

- `specs/012_coordinate_cslib_pr_submission_bimodal_logic/plans/01_pr-coordination-plan.md` (this file)
- `specs/012_coordinate_cslib_pr_submission_bimodal_logic/reports/01_pr-coordination.md` (research report, already exists)
- PR tracking coordination log (created during Phase 1)
- PR description and CI checklist templates (created during Phase 2)
- 14 PRs submitted to `leanprover/cslib` (created during Phases 3-4)

## Rollback/Contingency

- If maintainers reject the modular architecture: revise the PR wave plan to match their preferred structure; this may require revising porting tasks 2-11 and 20-23
- If namespace changes after some PRs merged: open follow-up PRs to rename namespaces in already-merged code
- If a PR is rejected: investigate reason, fix issues, resubmit as new PR (do not force-push to rejected PR branch)
- If review latency exceeds 3 weeks: escalate on Zulip, consider reaching out to @fmontesi directly
- If sorry in task 8 blocks merge: submit completeness PR without the sorry-containing lemma and track sorry elimination as a separate issue
