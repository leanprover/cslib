# Implementation Plan: Burgess Prior Art Seed Research for Tasks 46-49

- **Task**: 50 - Burgess prior art and seed research for tasks 46-49
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None (research already completed)
- **Research Inputs**: specs/050_burgess_prior_art_seed_research/reports/01_team-research.md
- **Artifacts**: plans/01_prior-art-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Task 50 synthesizes the completed team research (4 teammates: literature analysis, infrastructure audit, critic/gaps, abstraction strategy) into actionable deliverables for tasks 46-49. The work consists of (1) updating the TODO.md and state.json descriptions for tasks 46-49 with improved detail from the research findings, and (2) creating seed research reports for each task containing pre-digested literature mappings, infrastructure audit results, and implementation guidance. These seed reports will allow tasks 46-49 to skip or accelerate their research phases and move directly to planning and implementation.

### Research Integration

The team research report (01_team-research.md) and four individual teammate findings are the primary inputs:
- **Teammate A** (Literature): Burgess 1982 Lemmas 2.1-2.11 mapped to tasks, axiom correspondence tables, mathematical definitions
- **Teammate B** (Infrastructure): Per-file transfer analysis of BXCanonical/Chronicle/ (12,096 lines), transfer percentages, Box-entanglement boundaries
- **Teammate C** (Critic): Missing prerequisites (~850-1000 lines of Bundle/ infrastructure unlisted), revised scope estimates, dense/discrete interaction risks
- **Teammate D** (Horizons): Copy-adapt-then-abstract strategy, FrameClass unification opportunity, name alignment principle for task 41

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following roadmap items:
- "Dense temporal completeness" (Remaining: Logics/Temporal/Metalogic/) -- indirectly, by seeding tasks 46-49 which are prerequisites
- The chronicle construction infrastructure (tasks 46-49) fills the final sorry in Temporal/Metalogic/Completeness.lean

## Goals & Non-Goals

**Goals**:
- Update task 46-49 descriptions in TODO.md with revised scope estimates, missing prerequisites, and improved detail from research
- Update state.json descriptions to match TODO.md updates
- Create seed research reports for each of tasks 46-49 containing: literature map, infrastructure audit, implementation guidance, risks
- Ensure each seed report is self-contained enough that the task's research phase can be skipped or drastically shortened

**Non-Goals**:
- Modifying any Lean source code
- Creating implementation plans for tasks 46-49 (that happens during their /plan phases)
- Performing the FrameClass unification or any abstraction work (deferred to task 41)
- Updating roadmap items (no roadmap_flag set)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Seed reports become stale as codebase evolves | M | L | Reports reference specific files and line counts; implementers can re-verify with grep |
| Scope estimates in descriptions prove inaccurate | L | M | Estimates are ranges, not fixed; research provides reasoning behind each range |
| Missing prerequisites missed by research | M | L | Teammate C specifically focused on gaps; cross-reference all 4 teammate reports |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4, 5 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Update Task 46-49 Descriptions [NOT STARTED]

**Goal**: Incorporate research findings into the TODO.md and state.json descriptions for tasks 46-49 so they reflect the true scope, prerequisites, and implementation strategy.

**Tasks**:
- [ ] Update task 46 description: add Phase 0 prerequisite infrastructure (g_content, h_content, witness seeds, DCS, ~850-1000 lines), revised scope 1,200-2,000 lines, reference Bundle/TemporalContent.lean and Bundle/WitnessSeed.lean as sources
- [ ] Update task 47 description: note temporal version eliminates C5b/C6b for box (only temporal C5a/C6a and S-mirrors), add dependency on propositional combinators from task 46 Phase 0
- [ ] Update task 48 description: note [Denumerable (Formula Atom)] instance requirement, note omega-chain enumeration structure is nearly identical to bimodal
- [ ] Update task 49 description: flag ChronicleToCountermodel*.lean as NOT directly adaptable (box-entangled), note temporal countermodel is simpler (chronicle frame directly, no FMCS/BFMCS), revised scope 800-1,800 lines, note interaction with existing Completeness.lean CanonicalWorld infrastructure
- [ ] Update state.json descriptions for tasks 46-49 to match TODO.md changes
- [ ] Add seed research report artifact links to each task's TODO.md entry

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `specs/TODO.md` - Update task 46-49 entries with improved descriptions
- `specs/state.json` - Update task 46-49 description fields

**Verification**:
- Each task entry in TODO.md contains revised scope estimates
- Task 46 mentions Phase 0 prerequisites explicitly
- Task 49 flags box-entanglement in countermodel extraction
- state.json descriptions are consistent with TODO.md

---

### Phase 2: Create Seed Research Report for Task 46 [NOT STARTED]

**Goal**: Produce a self-contained seed research report for task 46 (R-relation and witness infrastructure) that covers the literature map, infrastructure audit, and implementation guidance.

**Tasks**:
- [ ] Create report at specs/046_temporal_r_relation/reports/01_seed-research.md
- [ ] Include Burgess 2.2-2.4 mathematical definitions from teammate-a (r-relation definition, consistency criterion, witness existence, intersection lemma)
- [ ] Include per-file transfer analysis from teammate-b (RRelation.lean 95% transfer, Frame.lean 60%, CanonicalChain.lean 100%, OrderedSeedConsistency.lean 100%)
- [ ] Include missing prerequisites list from teammate-c (g_content/h_content, WitnessSeed, DCS, propositional combinators)
- [ ] Include axiom correspondence for Burgess A1a-A6a and their temporal counterparts
- [ ] Include naming convention guidance from teammate-d (use rRelation, rMaximal, chronicle_defect to align with bimodal for task 41)
- [ ] Include the existing temporal infrastructure available in MCS.lean and Completeness.lean that can be reused

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `specs/046_temporal_r_relation/reports/01_seed-research.md` - New file (seed report)

**Verification**:
- Report contains literature map section with Burgess lemma references
- Report contains infrastructure audit section with transfer percentages
- Report contains prerequisites section listing what must be created before Chronicle port
- Report is self-contained (no external references required to understand scope)

---

### Phase 3: Create Seed Research Report for Task 47 [NOT STARTED]

**Goal**: Produce a self-contained seed research report for task 47 (labeled frame types and point insertion).

**Tasks**:
- [ ] Create report at specs/047_temporal_point_insertion/reports/01_seed-research.md
- [ ] Include Burgess 2.5-2.8 mathematical definitions from teammate-a (chronicle conditions C0-C5, point insertion for negation-delta and U-witness)
- [ ] Include per-file transfer analysis from teammate-b (ChronicleTypes.lean 85%, PointInsertion.lean 90%)
- [ ] Include Xu 1988 C0-C6 formulation as cleaner Lean target from teammate-a
- [ ] Include note that temporal version eliminates C5b/C6b for box (only C5a/C6a + S-mirrors)
- [ ] Include naming convention guidance from teammate-d (same file names, same definition names)
- [ ] Include key proof strategy notes: point insertion lemmas 2.6-2.8 are the heart, A4a-A7a do the heavy lifting

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `specs/047_temporal_point_insertion/reports/01_seed-research.md` - New file (seed report)

**Verification**:
- Report contains chronicle condition definitions (C0-C5 with Xu formulation)
- Report contains point insertion strategy
- Report notes bimodal simplifications (no box conditions)

---

### Phase 4: Create Seed Research Report for Task 48 [NOT STARTED]

**Goal**: Produce a self-contained seed research report for task 48 (counterexample elimination and chronicle construction).

**Tasks**:
- [ ] Create report at specs/048_temporal_chronicle_construction/reports/01_seed-research.md
- [ ] Include Burgess 2.9-2.10 counterexample elimination from teammate-a (induction on interval size for C4a, case analysis for C5a)
- [ ] Include omega construction overview from teammate-a (enumerate defects, iterate insertion, take union)
- [ ] Include per-file transfer analysis from teammate-b (CounterexampleElimination.lean 95%, ChronicleConstruction.lean 95%)
- [ ] Include [Denumerable (Formula Atom)] instance requirement from teammate-c
- [ ] Include note that bimodal sorry stubs (open guard semantics) need verification for temporal transfer
- [ ] Include naming convention guidance from teammate-d

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `specs/048_temporal_chronicle_construction/reports/01_seed-research.md` - New file (seed report)

**Verification**:
- Report contains counterexample elimination strategy (induction proofs for C4a/C5a)
- Report contains omega-chain construction overview
- Report notes Denumerable instance requirement

---

### Phase 5: Create Seed Research Report for Task 49 [NOT STARTED]

**Goal**: Produce a self-contained seed research report for task 49 (truth lemma and completeness assembly), with special attention to the box-entanglement warnings.

**Tasks**:
- [ ] Create report at specs/049_temporal_truth_lemma_completeness/reports/01_seed-research.md
- [ ] Include Burgess 2.11 truth lemma from teammate-a (induction on formula complexity, critical Until case uses C5a/C6a)
- [ ] Include per-file transfer analysis from teammate-b (TruthLemma.lean 70%, ChronicleToCountermodelBasic.lean 50%, ChronicleToCountermodel.lean 20%, CanonicalModel.lean 40%)
- [ ] Include explicit box-entanglement warning from teammate-c: ChronicleToCountermodel*.lean uses dense/discrete box split, FMCS, S5 reasoning -- NOT directly adaptable
- [ ] Include recommended fresh approach: temporal countermodel is simpler (chronicle frame (X, <, V) directly, no modal accessibility)
- [ ] Include interaction with existing Completeness.lean CanonicalWorld infrastructure from teammate-c
- [ ] Include dense/discrete interaction analysis from teammate-c (chronicle produces dense model on Q; discrete completeness uses different machinery)
- [ ] Include revised scope estimate 800-1,800 lines with justification

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `specs/049_temporal_truth_lemma_completeness/reports/01_seed-research.md` - New file (seed report)

**Verification**:
- Report contains explicit WARNING about box-entanglement in countermodel extraction
- Report recommends fresh countermodel approach rather than adaptation
- Report notes interaction with existing Completeness.lean infrastructure
- Report contains revised scope with justification

## Testing & Validation

- [ ] All 4 seed research reports exist in their respective task directories
- [ ] TODO.md task entries for 46-49 contain revised scope estimates
- [ ] state.json descriptions for 46-49 are consistent with TODO.md
- [ ] Each seed report contains: literature map, infrastructure audit, implementation guidance, risks sections
- [ ] Task 46 description explicitly mentions Phase 0 prerequisites
- [ ] Task 49 description explicitly warns about box-entangled countermodel extraction

## Artifacts & Outputs

- `specs/050_burgess_prior_art_seed_research/plans/01_prior-art-plan.md` (this plan)
- `specs/046_temporal_r_relation/reports/01_seed-research.md` (seed report for task 46)
- `specs/047_temporal_point_insertion/reports/01_seed-research.md` (seed report for task 47)
- `specs/048_temporal_chronicle_construction/reports/01_seed-research.md` (seed report for task 48)
- `specs/049_temporal_truth_lemma_completeness/reports/01_seed-research.md` (seed report for task 49)
- Updated `specs/TODO.md` (task 46-49 descriptions)
- Updated `specs/state.json` (task 46-49 descriptions)

## Rollback/Contingency

All changes are to markdown files and JSON state. If any seed report is inaccurate, it can be revised during the task's own research phase. The seed reports are supplements, not replacements -- tasks 46-49 can still run /research if the seed is insufficient. Git revert of the implementation commit would restore all files to pre-implementation state.
