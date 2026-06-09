# Implementation Plan: Improve ROADMAP.md with BimodalLogic Porting Overview

- **Task**: 24 - Improve ROADMAP.md with BimodalLogic porting overview
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: None (task 19 completed, research report available)
- **Research Inputs**: specs/024_improve_roadmap_bimodal_porting/reports/01_roadmap-research.md
- **Artifacts**: plans/01_roadmap-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: markdown
- **Lean Intent**: false

## Overview

Rewrite `specs/ROADMAP.md` from its current terse 4-phase technical plan into a comprehensive document that a CSLib maintainer encountering the project for the first time could read and understand. The research report (01_roadmap-research.md) has synthesized all source material; this phase translates those findings into a well-structured, narrative-driven roadmap document. No code changes -- this is purely a markdown rewrite of one file.

### Research Integration

The research report identified seven gaps in the current ROADMAP.md: (1) no description of what TM bimodal logic is, (2) no explanation of why it belongs in CSLib, (3) no modular factoring rationale, (4) no current state description, (5) no link to TODO.md, (6) no summary of key design decisions, (7) no note on PR coordination. All gaps are addressed in the document structure below.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task directly improves the ROADMAP.md document itself. It does not advance any specific roadmap porting item but improves the navigability and clarity of the roadmap for all future work.

## Goals & Non-Goals

**Goals**:
- Produce a ROADMAP.md that explains the BimodalLogic porting project to a newcomer
- Describe what TM bimodal logic is and why it belongs in CSLib
- Document the modular factoring design decisions from task 19
- Show what CSLib already has and what remains to be ported
- Include the task dependency wave structure with a link to specs/TODO.md
- Keep the document scannable with clear heading hierarchy

**Non-Goals**:
- Changing any code or Lean files
- Modifying task descriptions in TODO.md or state.json (beyond task 24 status)
- Adding new tasks or changing the dependency graph
- Duplicating full task descriptions (those belong in TODO.md)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Document becomes too long and hard to scan | M | M | Use clear heading hierarchy; keep narrative concise; use tables for structured data |
| Task statuses become stale as work proceeds | M | H | Reference TODO.md for current status; keep ROADMAP focused on the plan, not live status |
| Confusion between BimodalLogic source paths and CSLib target paths | M | L | Use a clear source-to-target mapping table |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Rewrite ROADMAP.md [NOT STARTED]

**Goal**: Replace the current ROADMAP.md with a comprehensive, well-structured document following the outline below.

**Tasks**:
- [ ] Write the new ROADMAP.md with the following document structure:

**Section 1: Title and Introduction** (~10 lines)
- Title: "Project Roadmap: Porting BimodalLogic to CSLib"
- 2-3 sentence overview: what is being ported, from where, and why
- Link to the paper: "The Construction of Possible Worlds" (Brast-McKie, 2025)
- Note on scope: ~84,547 lines in BimodalLogic, of which ~6,800 factor into reusable modules and ~30,000+ are inherently bimodal

**Section 2: What is TM Bimodal Logic?** (~20 lines)
- Plain-English description of the Bimodal Logic of Tense and Modality (TM)
- S5 modal operators (necessity/possibility) + Since/Until linear tense operators
- Task semantics: evaluation at both world-history and time point
- 5 primitive connectives: bot, imp, box, until, since
- 4 axiom system variants (Base/Dense/Continuous/Discrete) with their standard models and completeness status
- Metalogical results: soundness, completeness, decidability, separation, conservative extension

**Section 3: Why Port to CSLib?** (~10 lines)
- CSLib as the Lean library for Computer Science
- BimodalLogic is a standalone repository; porting makes it available as a modular library
- Modular factoring enables reuse: propositional theorems usable by all logics, modal theorems standalone, temporal theorems standalone
- Verified decision procedure and completeness proof as library contributions

**Section 4: Design Decisions (Modular Factoring)** (~30 lines)
- Central principle: every component lives at the most general level it can compile at
- Table showing component placement (Foundations vs. Modal vs. Temporal vs. Bimodal) with rationale
- Key decision 1: DeductionTheorem stays per-logic (requires structural induction on concrete DerivationTree)
- Key decision 2: BimodalTMHilbert diamond-avoidance pattern (extends individual HasAxiom* classes directly)
- Key decision 3: Temporal semantics as new infrastructure (standalone on LinearOrder, not from BimodalLogic)
- Credit to task 19 team research as the source of these decisions

**Section 5: Current State** (~20 lines)
- What CSLib already has: Formula types (Bimodal, Temporal, Modal, PL), connective typeclasses, proof system interface typeclasses, embedding functions
- Show the current CSLib logic directory tree (from research report)
- What does NOT yet exist: proof theorems, proof systems, semantics, metalogic
- Note: 0 lines of proof code ported so far

**Section 6: Porting Phases** (~40 lines)
- Retain the 4-phase structure from the current ROADMAP.md but with improved narrative context
- Phase 1: Foundations (Task 20, ~2,400 lines) -- propositional Hilbert theorems as generic lemmas
- Phase 2: Modal and Temporal Modules (Tasks 21-22, ~3,100 lines) -- standalone proof systems and theorems
- Phase 3: Temporal Semantics (Task 23, ~400-600 lines) -- new infrastructure on LinearOrder
- Phase 4: Bimodal Porting (Tasks 2-11, ~30,000+ lines) -- inherently bimodal content
- For each phase: target directory, scope, key components, milestone statement
- Import hierarchy diagram (Foundations -> Modal/Temporal -> Bimodal)

**Section 7: Task Dependency Structure** (~20 lines)
- 6-wave dependency table (from TODO.md Task Order section)
- Foundations-first invariant explanation
- External dependency note (BimodalLogic:291 toolchain upgrade)
- Link to `specs/TODO.md` for full task descriptions and current status
- Note on PR coordination (Task 12)

**Section 8: Component Accounting** (~15 lines)
- Table mapping every extractable component to its task and line count
- Total extractable lines summary
- Note: "No component double-counted; each theorem belongs to exactly one task"

**Section 9: Success Metrics** (~10 lines)
- Retain the success metrics checklist from the current ROADMAP.md
- Add: all standalone modules self-contained, embedding lattice complete

- [ ] Verify the document reads naturally from top to bottom for a newcomer
- [ ] Verify all cross-references to TODO.md use relative paths
- [ ] Verify no task descriptions are duplicated (only task numbers and brief scope)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `specs/ROADMAP.md` -- complete rewrite following the structure above

**Verification**:
- Document has all 9 sections listed above
- Link to specs/TODO.md is present
- Modular factoring design decisions section includes the 3 key decisions
- Current state section accurately reflects what exists vs. what remains
- No task descriptions duplicated from TODO.md
- Document is under 250 lines (concise but comprehensive)

## Testing & Validation

- [ ] All 9 sections present in the final document
- [ ] Link to specs/TODO.md present and using correct relative path
- [ ] Import hierarchy diagram included
- [ ] Component-to-task mapping table present
- [ ] 3 key design decisions documented (DeductionTheorem, diamond-avoidance, temporal semantics)
- [ ] Current CSLib state described (what exists vs. what remains)
- [ ] Document readable top-to-bottom without prior project knowledge

## Artifacts & Outputs

- `specs/ROADMAP.md` -- rewritten roadmap document
- `specs/024_improve_roadmap_bimodal_porting/plans/01_roadmap-plan.md` -- this plan

## Rollback/Contingency

The current ROADMAP.md is tracked in git. If the rewrite is unsatisfactory, revert with `git checkout HEAD -- specs/ROADMAP.md`.
