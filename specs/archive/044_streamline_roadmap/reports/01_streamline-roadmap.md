# Research Report: Task #44

**Task**: 44 - Streamline ROADMAP.md
**Started**: 2026-06-09T16:00:00Z
**Completed**: 2026-06-09T16:15:00Z
**Effort**: Small (1-2 hours)
**Dependencies**: None
**Sources/Inputs**: specs/ROADMAP.md (full read), specs/TODO.md, specs/state.json
**Artifacts**: specs/044_streamline_roadmap/reports/01_streamline-roadmap.md
**Standards**: report-format.md

## Executive Summary

- The current ROADMAP.md (~486 lines) mixes goal documentation with extensive planning detail, design rationale, historical commentary, and content that duplicates TODO.md. The target is approximately 80-100 lines.
- Content to keep: the goal/background statement, the modular factoring principle, completed work list, remaining work list, the import hierarchy diagram, and broad phase overview.
- Content to remove: Modular Factoring Design table and Key Design Decisions (design rationale for TODO/research), Phase detail tables (line counts, source files, component breakdowns), Component Accounting table, dependency wave table, the "What CSLib Gains" section (planning rationale), Background/TM section, Current State of CSLib directory tree (snapshot that goes stale), and the Success Metrics checklist (operational tracking).

## Context & Scope

The ROADMAP.md currently serves too many purposes at once: goal statement, architectural design record, planning document, implementation status tracker, and technical reference. The task is to strip it back to a lean reference document that answers four questions:

1. What is the goal?
2. What broad approach is being taken?
3. What has been completed?
4. What remains?

Details about why specific design decisions were made, how many lines each component has, which wave tasks run in parallel, and the full directory tree belong in TODO.md task descriptions or research artifacts — not the roadmap.

## Findings

### Content Analysis: What Belongs

**Goal statement (keep)**
The opening paragraph and Overview section correctly describe the project goal: port BimodalLogic to four standalone CSLib modules guided by a modular factoring principle. This is the core purpose statement and belongs.

**Broad approach / modular factoring principle (keep, brief)**
The one-sentence principle — "every component lives at the most general level it can compile at" — is the organizing idea. A brief statement of the four module levels (Propositional, Modal, Temporal, Bimodal) and their targets belongs.

**Import hierarchy diagram (keep)**
The ASCII import hierarchy (`Foundations → Modal/Temporal → Bimodal`) is a compact, stable architectural reference that belongs in the roadmap. It conveys the approach without detailed planning content.

**Completed work list (keep, table form)**
The "What Has Been Completed" table is the most useful operational section — it lists tasks with status and brief description. Keep as a simple table with task number, component, and status. Drop the line-count column (implementation detail that goes stale).

**Remaining work list (keep, table form)**
The "What Remains" table (tasks 31, 35, 36, 37 plus their brief descriptions) belongs. Keep task number, component name, and brief description. Drop line-count estimates.

### Content Analysis: What to Remove

**"Modular Factoring Design" section (remove)**
The full component placement table (10 rows) and 5 Key Design Decisions are design rationale. They explain *why* decisions were made during research. This belongs in research reports (e.g., specs/009, specs/031 research files), not the roadmap. The roadmap should state the principle, not justify it.

**"What CSLib Gains" section (remove)**
This section (lines 84-126) describes what each phase adds and why it is valuable. This is planning/motivation content from the research phase. It duplicates information already in TODO.md task descriptions and research reports.

**"Background: TM Bimodal Logic" section (remove)**
Background on the TM bimodal logic (lines 129-144) is reference material that belongs either in the BimodalLogic repo itself or a separate domain context document. It is not needed to understand what the roadmap is tracking.

**Phase detail tables within "Porting Phases" (remove the tables, keep phase headers)**
Each phase section has a line-count breakdown table (e.g., Phase 1's 4-row table of combinators/propositional/contextualproofs/bigconj with line estimates). These are planning artifacts. The broad phase structure (Phase 1 propositional, Phase 2 modal+temporal, etc.) belongs; the component tables do not.

**"Current State of CSLib" directory tree (remove)**
The ~50-line directory tree with inline annotations (lines 170-219) is an implementation snapshot that goes stale immediately. The current file structure is visible by running `ls` or checking the actual source tree. It does not belong in a roadmap.

**"Component Accounting" table (remove)**
The task-by-task line count ledger (lines 431-449) is planning/accounting content from research. It belongs in research reports, not the roadmap.

**"Task Dependency Structure" table (remove)**
The wave breakdown table (lines 410-426) duplicates the dependency information in TODO.md and is more current there. The import hierarchy diagram already conveys the dependency structure at the right level of abstraction.

**"Success Metrics" checklist (remove)**
The checked/unchecked milestone list (lines 455-486) is operational tracking that duplicates what TODO.md already tracks by status. The roadmap should not be a status-tracking document — that is TODO.md's job.

**Line counts throughout (remove)**
All `~NNN lines` annotations in section headers and table columns are implementation details that go stale. The roadmap should describe scope at the level of "standalone proof system + theorem library" not "~1,600 lines."

### Proposed New Structure

The streamlined ROADMAP.md should have this structure (~80-100 lines):

```
# Project Roadmap: Porting BimodalLogic to CSLib

[1-paragraph goal statement]

## Approach

[2-3 sentences on modular factoring principle + four module levels + import direction]

## Import Hierarchy

[the ASCII diagram — compact, stable, architectural]

## Completed

[simple table: Task | Component | Module]

## Remaining

[simple table: Task | Component | Module]

## Phases

[one paragraph or short list per phase — name, target, brief scope, no tables]
```

The "Phases" section keeps the broad narrative of what each phase accomplishes (why phases are ordered the way they are) without the detailed line-count breakdowns and component tables.

### Key Principles for Rewrite

1. No line-count estimates anywhere.
2. No "Key Design Decisions" justifications.
3. No directory trees.
4. No wave/dependency tables (those belong in TODO.md).
5. No success metrics checklists (tracked in TODO.md).
6. No planning rationale paragraphs (those belong in research reports).
7. Historical commentary means: commentary about how the plan evolved, design decision rationale, or why things were structured a particular way. None of this belongs in the roadmap.
8. The completed list is purely factual: task N, component name, done. No dates, no line counts.

## Decisions

- Keep the import hierarchy diagram — it is compact and stable enough to belong in the roadmap.
- Keep a Phases section but reduce each phase to 2-4 sentences maximum, dropping all component tables.
- Drop the Background/TM section entirely — it belongs in domain documentation, not a project roadmap.
- The Completed and Remaining tables should have exactly three columns: Task, Component, Module path.

## Risks & Mitigations

- **Risk**: Removing too much makes the roadmap too thin to be useful as orientation.
  **Mitigation**: Keep the phase narrative paragraphs (brief) and the import hierarchy. These give enough context to understand the structure without being planning documents.

- **Risk**: Completed list diverges from TODO.md over time.
  **Mitigation**: The roadmap completed list is deliberately coarser than TODO.md — it lists tasks, not phases or sub-steps. Divergence is less likely at this granularity.

## Context Extension Recommendations

- None. The project already has clear separation between ROADMAP.md (this task's subject), TODO.md (status tracking), and specs/ research artifacts (design rationale). The gap being closed is that ROADMAP.md has absorbed content from the other categories.
