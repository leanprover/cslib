# Implementation Plan: Task #26

- **Task**: 26 - Revise ROADMAP.md to focus on porting across all four logic levels
- **Status**: [COMPLETED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/026_revise_roadmap_focus_on_porting/reports/01_roadmap-revision-research.md
- **Artifacts**: plans/01_revision-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: markdown
- **Lean Intent**: false

## Overview

Revise `specs/ROADMAP.md` to shift the document's focus from the TM bimodal logic theory to the full four-level porting effort (Propositional, Modal, Temporal, Bimodal). The current ROADMAP opens with ~30 lines of bimodal theory (operators, task semantics, axiom tables) before establishing the porting rationale. The revision reorders the document so the porting mission and modular factoring principle lead, TM background is trimmed to ~10 lines and moved to a later section, the paper link is removed, and the BimodalLogic repository link is corrected. All accurate content (wave tables, component accounting, import hierarchy, success metrics) is preserved.

### Research Integration

The research report (`01_roadmap-revision-research.md`) provides:
- A detailed structural analysis of the current ROADMAP identifying the bimodal-heavy opening as the primary problem (~40% of opening content is TM theory)
- A recommended revised section order that leads with the porting mission
- Specific content changes: remove paper link, fix BimodalLogic repo URL, trim TM background to ~10 lines
- Tone guidance: shift from "here is the bimodal logic we want to port" to "here is a modular porting effort that produces four standalone libraries"
- Confirmation that wave tables, component accounting, import hierarchy, and current-state inventory are accurate and should be preserved

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task directly revises ROADMAP.md itself.

## Goals & Non-Goals

**Goals**:
- Open the ROADMAP with the four-level porting mission (Propositional, Modal, Temporal, Bimodal) as the organizing frame
- Lead with the modular factoring principle ("every component lives at the most general level it can compile at") as the architectural rationale
- Trim TM bimodal logic background to ~10 lines in a later section, linking to the BimodalLogic repository for full detail
- Remove the paper link entirely
- Fix the BimodalLogic repository URL from `https://github.com/benbrastmckie/ProofChecker` to `https://github.com/benbrastmckie/BimodalLogic`
- Treat Propositional, Modal, and Temporal phases as first-class deliverables, not scaffolding for the bimodal port
- Expand success metrics to give equal weight to all four levels

**Non-Goals**:
- Changing the task dependency graph or task descriptions
- Adding new content beyond what the research report recommends
- Modifying any file other than `specs/ROADMAP.md`

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Trimming TM background too aggressively loses context a maintainer needs | M | L | Retain 2-3 sentences about what TM is (S5 modal + Since/Until tense operators) and link to BimodalLogic for the full formal description |
| Losing the useful axiom table | L | M | The axiom table belongs in the BimodalLogic repo README, not in the CSLib ROADMAP; remove it |
| Phase 4 (bimodal, ~30,000 lines) still dominates by volume despite rebalancing | L | H | Frame the phases section with a note that Phase 4 is the largest by volume but Phases 1-3 complete first and unlock it |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Revise ROADMAP.md [COMPLETED]

**Goal**: Restructure and revise `specs/ROADMAP.md` to lead with the four-level porting mission instead of TM bimodal logic theory.

**Tasks**:
- [ ] Rewrite the opening paragraph to immediately name all four levels (Propositional, Modal, Temporal, Bimodal) and frame the document as a porting roadmap
- [ ] Move the modular factoring design section ("every component lives at the most general level it can compile at") to appear early, right after the overview
- [ ] Add a "What CSLib Gains" section (or expand "Why Port to CSLib?") that gives each of the four levels a substantive bullet point, treating each as a first-class deliverable
- [ ] Remove the "What is TM Bimodal Logic?" section from its current leading position
- [ ] Create a new "Background: TM Bimodal Logic" section positioned after the porting mission and design sections, trimmed to ~10 lines: what TM is, pointer to `https://github.com/benbrastmckie/BimodalLogic`
- [ ] Remove the paper link (`possible_worlds.pdf`) entirely
- [ ] Remove the Primitive Connectives table, Task Semantics paragraph, and Axiom Systems table from the ROADMAP (these belong in the BimodalLogic repo README)
- [ ] Fix the BimodalLogic repository link from `https://github.com/benbrastmckie/ProofChecker` to `https://github.com/benbrastmckie/BimodalLogic` wherever it appears
- [ ] Reframe "Porting Phases" so Phases 1-3 read as valuable standalone deliverables, not prerequisites for bimodal porting
- [ ] Preserve the Import Hierarchy diagram as-is
- [ ] Preserve the Current State of CSLib inventory as-is
- [ ] Preserve the Task Dependency Structure wave table as-is
- [ ] Preserve the Component Accounting table as-is
- [ ] Revise Success Metrics to give equal weight to Propositional, Modal, and Temporal milestones alongside bimodal milestones
- [ ] Verify the final document has no remaining `ProofChecker` references or paper links

**Revised Document Structure** (target section order):
```
Title: Porting BimodalLogic to CSLib

[Opening: 2-3 sentences naming all four levels and the modular factoring principle]

## Overview
[The porting mission: extract and organize content from BimodalLogic
into four standalone CSLib modules. Named link to BimodalLogic repo.]

## Modular Factoring Design
[Central principle + component placement table]

## What CSLib Gains
[Each of the four levels as equal deliverables with substantive descriptions]

## Background: TM Bimodal Logic
[~10 lines: what TM is, link to BimodalLogic. NO paper link.]

## Import Hierarchy
[Keep existing diagram]

## Current State of CSLib
[Keep existing inventory]

## Porting Phases
[All four phases as first-class deliverables]

## Task Dependency Structure
[Keep existing wave table]

## Component Accounting
[Keep existing table]

## Success Metrics
[Revised to include all four levels equally]
```

**Key Content to Remove**:
- "What is TM Bimodal Logic?" section in its current leading position and length
- Primitive Connectives table (5 rows)
- Task Semantics paragraph
- Axiom Systems table (Base/Dense/Continuous/Discrete)
- Paper link (`possible_worlds.pdf`)
- `ProofChecker` URL references

**Key Content to Add**:
- Opening paragraph naming all four levels
- "What CSLib Gains" section with per-level bullets
- "Background: TM Bimodal Logic" (~10 lines, positioned later)
- Framing text in Porting Phases treating Phases 1-3 as standalone deliverables

**Key Content to Preserve (verbatim or with minimal edits)**:
- Design Decisions / Component Placement table
- Key Design Decisions (DeductionTheorem, BimodalTMHilbert, Temporal semantics)
- Import Hierarchy diagram
- Current State of CSLib inventory
- Porting Phases content (reframed, not rewritten)
- Task Dependency Structure wave table
- Component Accounting table
- Success Metrics (revised for balance)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `specs/ROADMAP.md` - Restructure and revise as described above

**Verification**:
- No reference to `ProofChecker` URL remains in the document
- No paper link (`possible_worlds.pdf`) remains
- BimodalLogic link is `https://github.com/benbrastmckie/BimodalLogic`
- TM background section is ~10 lines or fewer (excluding blank lines)
- The first substantive section after the title is about the porting mission, not TM theory
- All four levels (Propositional, Modal, Temporal, Bimodal) are named in the opening paragraph
- Wave table, component accounting, import hierarchy, and current-state inventory are preserved
- "Modular factoring" principle appears before any TM theory description

## Testing & Validation

- [ ] No `ProofChecker` URL in the document (grep for `ProofChecker`)
- [ ] No `possible_worlds.pdf` link in the document (grep for `possible_worlds`)
- [ ] BimodalLogic link correct: `https://github.com/benbrastmckie/BimodalLogic`
- [ ] Opening paragraph names all four levels
- [ ] TM background section is ~10 lines, positioned after porting mission
- [ ] Wave table preserved with correct task numbers
- [ ] Component accounting table preserved
- [ ] Import hierarchy diagram preserved

## Artifacts & Outputs

- `specs/ROADMAP.md` - Revised roadmap document
- `specs/026_revise_roadmap_focus_on_porting/plans/01_revision-plan.md` - This plan

## Rollback/Contingency

The previous version of `specs/ROADMAP.md` is in git history (committed as part of task 24). If the revision is unsatisfactory, revert with `git checkout HEAD -- specs/ROADMAP.md` or `git show HEAD:specs/ROADMAP.md > specs/ROADMAP.md`.
