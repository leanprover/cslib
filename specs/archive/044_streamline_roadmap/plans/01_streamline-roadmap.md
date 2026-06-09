# Implementation Plan: Streamline ROADMAP.md

- **Task**: 44 - Streamline ROADMAP.md
- **Status**: [COMPLETED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/044_streamline_roadmap/reports/01_streamline-roadmap.md
- **Artifacts**: plans/01_streamline-roadmap.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: markdown
- **Lean Intent**: false

## Overview

Rewrite specs/ROADMAP.md from ~486 lines down to ~80-100 lines. The current file mixes goal documentation with planning detail, design rationale, directory trees, line-count accounting, and status tracking that belongs in TODO.md or research artifacts. The streamlined version retains only: the goal statement, the modular factoring principle (one sentence), the import hierarchy diagram, simplified completed/remaining tables, and brief phase narrative paragraphs.

### Research Integration

Research report (01_streamline-roadmap.md) provides a detailed content-by-content analysis of what to keep versus remove, along with a proposed new structure. The plan below follows the research recommendations directly.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task directly modifies ROADMAP.md itself. No roadmap items to advance.

## Goals & Non-Goals

**Goals**:
- Reduce ROADMAP.md from ~486 lines to ~80-100 lines
- Preserve the four essential questions: goal, approach, completed, remaining
- Keep the import hierarchy diagram as a compact architectural reference
- Make completed/remaining tables factual (task, component, module) with no line counts

**Non-Goals**:
- Moving removed content to other files (it already exists in research reports and TODO.md)
- Changing any task statuses or TODO.md content
- Updating the import hierarchy diagram itself (it is already correct)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing too much, leaving roadmap too thin | M | L | Keep phase narrative paragraphs and import hierarchy for orientation |
| Completed list diverges from TODO.md over time | L | L | Roadmap list is coarser than TODO.md (tasks only, not phases), reducing drift |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Rewrite ROADMAP.md [COMPLETED]

**Goal**: Replace the current ROADMAP.md with a streamlined version containing only essential content.

**Tasks**:

**Step 1 -- Write the new header and goal statement:**
- [x] Keep the H1 title: `# Project Roadmap: Porting BimodalLogic to CSLib` *(completed)*
- [x] Keep the opening paragraph (lines 3-8 of current file) that describes the porting effort, the four modules, and the modular factoring principle. Trim to 3-4 sentences maximum. Remove the link to TODO.md from this paragraph (it can go in a footer if needed). *(completed)*

**Step 2 -- Write the Approach section:**
- [x] Create `## Approach` section *(completed)*
- [x] Include the one-sentence modular factoring principle: "every component lives at the most general level it can compile at" *(completed)*
- [x] State the four module levels (Propositional, Modal, Temporal, Bimodal) and the import direction in 2-3 sentences *(completed)*
- [x] Do NOT include the "Component Placement" table (lines 36-50 of current file) *(completed)*
- [x] Do NOT include the "Key Design Decisions" subsection (lines 52-81) *(completed)*

**Step 3 -- Keep the Import Hierarchy section:**
- [x] Keep `## Import Hierarchy` section and the ASCII diagram (lines 146-164 of current file) exactly as-is *(completed)*
- [x] Keep the explanatory paragraph below the diagram about enforcement of the hierarchy *(completed)*

**Step 4 -- Write the Completed section:**
- [x] Create `## Completed` section with a simple 3-column table: `Task | Component | Module` *(completed)*
- [x] Populate from the current "What Has Been Completed" table (lines 225-243), dropping the `Lines` column entirely *(completed)*
- [x] Use short component names, not full paths. Example: `Propositional theorems` not `Foundations/Logic/Theorems/ -- propositional Hilbert theorems` *(completed)*
- [x] Include all currently completed tasks: 20, 21, 29, 22, 23, 30, 2, 3, 4, 5, 6, 7, 34, 10, 11, 42, 43 *(completed)*
- [x] The `Module` column should contain the target path (e.g., `Foundations/Logic/Theorems/`) *(completed)*

**Step 5 -- Write the Remaining section:**
- [x] Create `## Remaining` section with a simple 3-column table: `Task | Component | Module` *(completed)*
- [x] Populate from the current "What Remains" table (lines 247-253): tasks 31, 35, 36, 37 *(completed)*
- [x] Also include tasks 38, 39, 40, 41 if they are active remaining tasks (check TODO.md) *(completed: all 4 tasks are active in TODO.md)*
- [x] Drop all line-count estimates *(completed)*
- [x] Drop the "~50,000+ lines completed" summary line *(completed)*

**Step 6 -- Write the Phases section:**
- [x] Create `## Phases` section *(completed)*
- [x] For each of the 5 current phases, write 2-4 sentences describing: what the phase covers, what module it targets, and its current status (completed or in progress) *(completed)*
- [x] Do NOT include component breakdown tables (the per-phase tables with line counts) *(completed)*
- [x] Do NOT include the "Milestone" lines (they are status-tracking content) *(completed)*
- [x] Phase 1 (Propositional): completed, 1-2 sentences *(completed)*
- [x] Phase 2 (Modal + Temporal Modules): completed, 1-2 sentences *(completed)*
- [x] Phase 3 (Temporal Semantics): completed, 1-2 sentences *(completed)*
- [x] Phase 4 (Standalone Metalogic): mostly completed (Tasks 29, 30 done; Task 31 in progress), 2-3 sentences *(completed)*
- [x] Phase 5 (Bimodal Porting): in progress (Task 35 implementing), 2-3 sentences *(completed)*

**Step 7 -- Remove all of the following sections entirely:**
- [x] Remove "Modular Factoring Design" section (lines 30-81) -- design rationale *(completed)*
- [x] Remove "What CSLib Gains" section (lines 84-126) -- planning motivation *(completed)*
- [x] Remove "Background: TM Bimodal Logic" section (lines 129-143) -- domain reference *(completed)*
- [x] Remove "Current State of CSLib" directory tree (lines 167-253) -- stale snapshot. Note: the Completed/Remaining tables embedded in this section are moved to their own sections above *(completed)*
- [x] Remove "Task Dependency Structure" table (lines 406-426) -- duplicates TODO.md *(completed)*
- [x] Remove "Component Accounting" table (lines 430-449) -- planning artifact *(completed)*
- [x] Remove "Success Metrics" checklist (lines 453-486) -- operational tracking *(completed)*

**Step 8 -- Final cleanup:**
- [x] Remove all `~NNN lines` annotations anywhere in the file *(completed)*
- [x] Remove all horizontal rules (`---`) between sections (use only if needed for readability) *(completed)*
- [x] Verify the file is approximately 80-100 lines *(completed: 101 lines)*
- [x] Verify no line-count estimates remain *(completed)*
- [x] Verify no design rationale ("Key Design Decisions") remains *(completed)*
- [x] Verify no directory trees remain *(completed)*
- [x] Verify no wave/dependency tables remain *(completed)*
- [x] Verify no success metrics checklists remain *(completed)*

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `specs/ROADMAP.md` - Complete rewrite from ~486 lines to ~80-100 lines

**Verification**:
- File is between 70-110 lines
- Contains exactly these H2 sections: Approach, Import Hierarchy, Completed, Remaining, Phases
- Completed table has 17 rows (one per completed task)
- Remaining table has tasks 31, 35, 36, 37 (plus 38, 39, 40, 41 if active)
- No occurrences of `~` followed by a number and `lines` (regex: `~\d+.*lines`)
- No occurrences of "Key Design Decision"
- No directory tree blocks (no lines starting with `├──` or `└──`)
- Import hierarchy ASCII diagram is preserved
- `lake build` still passes (ROADMAP.md is not imported by Lean)

## Testing & Validation

- [x] ROADMAP.md is between 70-110 lines *(101 lines)*
- [x] Contains H1 title and H2 sections: Approach, Import Hierarchy, Completed, Remaining, Phases
- [x] No line-count annotations remain (grep for `~\d+.*lines` returns empty)
- [x] No "Key Design Decision" text remains
- [x] No directory tree markup remains
- [x] No "Component Accounting", "Task Dependency Structure", or "Success Metrics" sections remain
- [x] Import hierarchy diagram is present and unchanged
- [x] Completed table lists all 17 completed tasks
- [x] Remaining table lists all active remaining tasks

## Artifacts & Outputs

- `specs/ROADMAP.md` - Streamlined roadmap (~80-100 lines)
- `specs/044_streamline_roadmap/plans/01_streamline-roadmap.md` - This plan

## Rollback/Contingency

The current ROADMAP.md is tracked in git. If the rewrite is unsatisfactory, revert with `git checkout HEAD -- specs/ROADMAP.md`.
