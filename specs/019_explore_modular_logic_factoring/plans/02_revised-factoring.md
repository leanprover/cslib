# Implementation Plan: Revised Modular Logic Factoring -- Task Restructuring

- **Task**: 19 - Explore modular logic factoring
- **Status**: [NOT STARTED]
- **Effort**: 3.5 hours
- **Dependencies**: None (this is a META task that restructures other tasks)
- **Research Inputs**:
  - specs/019_explore_modular_logic_factoring/reports/01_factoring-synthesis.md
  - specs/019_explore_modular_logic_factoring/reports/02_team-research.md
- **Artifacts**: plans/02_revised-factoring.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: meta
- **Lean Intent**: false

## Overview

This plan restructures the cslib task graph based on both the initial research synthesis and the team research findings. The core goal is unchanged from the prior plan: move ~5,000 lines of reusable BimodalLogic content from bimodal-only tasks (2-11) into standalone Propositional, Modal, and Temporal modules via new tasks (20-23). The team research introduced important refinements: DeductionTheorem should stay per-logic (not in Task 20), Task 22 scope must include ~20 HasAxiom* typeclasses and BimodalTMHilbert compatibility, and a new Task 23 for standalone temporal semantics is needed. All changes are edits to specs/state.json, specs/TODO.md, and specs/ROADMAP.md -- no Lean code is written.

This revision adds two new objectives compared to the prior plan version: (1) populating ROADMAP.md with the modular factoring porting plan, milestones, and dependency waves derived from the research; and (2) structuring the Task Order section in TODO.md into natural topic groupings instead of a flat "Uncategorized" section. Task 17's description is also revised since task 19 now handles ROADMAP.md population directly (task 19 has the full research context).

Definition of done: state.json and TODO.md reflect the modular factoring with tasks 20-23 created, tasks 2-7 and 12 revised, the Task Order section restructured into topic groupings, ROADMAP.md populated with the phased porting plan, and task 17 revised to remove ROADMAP.md from its scope. Seed research reports exist for new tasks.

### Research Integration

**Initial synthesis** (01_factoring-synthesis.md):
- Classified ~5,000 BimodalLogic lines into propositional (~2,900), modal (~1,200), and temporal (~920)
- Recommended direct typeclass porting (Option 2) over concrete-then-generalize
- Identified TemporalBXHilbert as essentially empty

**Team research** (02_team-research.md) -- key refinements:
- DeductionTheorem requires structural induction on DerivationTree and cannot be ported generically to Foundations. Keep per-logic. This reduces Task 20 scope by ~500 lines (from ~2,900 to ~2,400).
- TemporalBXHilbert needs ~20 new HasAxiom* typeclasses plus restructuring, not just axiom abbrevs. Task 22 scope is larger than initially estimated.
- BimodalTMHilbert does not extend TemporalBXHilbert. Need diamond-avoidance pattern (mirror BimodalConnectives). This is Task 22 scope.
- Standalone temporal semantics on linear orders is a critical missing piece. Recommend new Task 23.
- Semantics must remain separate per logic (unanimous from 4 teammates). No shared semantic infrastructure.
- Tableau systems are per-logic and out of scope for tasks 20-22.

### Prior Plan Reference

The prior plan version had 4 phases: create tasks 20-23, create seed reports, revise tasks 2-7/12, update task order. This revision preserves the same 4-phase structure but expands Phase 4 to include ROADMAP.md population and topic-grouped Task Order formatting, and adds a task to Phase 3 to revise task 17.

### Roadmap Alignment

ROADMAP.md currently contains only the default empty template. Phase 4 of this plan populates it with the full modular factoring porting plan derived from the research findings.

## Goals & Non-Goals

**Goals**:
- Create tasks 20-23 in state.json and TODO.md with accurate descriptions reflecting team research findings
- Create seed research reports for tasks 20-23 summarizing relevant research findings
- Revise task descriptions for tasks 2-7 to reflect modular factoring (reduced scope, updated dependencies)
- Revise task 12 (PR coordination) to include standalone module PRs
- Revise task 17 to remove ROADMAP.md from its scope (task 19 handles it with full research context)
- Populate ROADMAP.md with the phased porting plan: Foundations, Modal/Temporal, Bimodal waves, milestones, and dependency structure
- Restructure the Task Order section in TODO.md into natural topic groupings (Foundations, Modal Logic, Temporal Logic, Bimodal Porting, Project Management) with dependency trees within each group
- Keep total estimated effort comparable (redistributed across more tasks, not inflated)

**Non-Goals**:
- Writing any Lean code (this is a META task)
- Changing the existing typeclass hierarchy or formula types
- Restructuring tasks 8-11 beyond dependency updates (they remain inherently bimodal)
- Restructuring tasks 15-18 beyond task 17 description update (independent infrastructure/meta tasks)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| state.json and TODO.md desync during multi-task edits | H | M | Write state.json first, then TODO.md. Verify consistency in Phase 4. |
| Task descriptions become too long for TODO.md readability | L | M | Keep TODO.md descriptions concise (1-2 lines); full details in seed research reports. |
| Seed reports reference BimodalLogic line counts that may shift | L | L | Use approximate counts with "~" prefix. Exact counts are determined during actual research/implementation. |
| next_project_number off-by-one | M | L | Set to 24 (one past the highest new task, 23). Verify in Phase 4. |
| ROADMAP.md content diverges from actual task graph | M | L | Generate ROADMAP.md content directly from the dependency graph in state.json. Verify cross-reference in Phase 4. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Create New Tasks 20-23 in state.json and TODO.md [COMPLETED]

**Goal**: Add four new tasks to state.json and TODO.md with descriptions, dependencies, and effort estimates that incorporate team research findings.

**Tasks**:
- [ ] Add Task 20 (Propositional Hilbert Theorems) to state.json:
  - `project_number`: 20, `project_name`: "propositional_hilbert_theorems"
  - `status`: "not_started", `task_type`: "lean4"
  - `dependencies`: [] (typeclass infrastructure exists from task 14)
  - Scope: Combinators (I/B/C/S, ~300 lines), Propositional/{Core,Connectives,Reasoning} (~1,100 lines), ContextualProofs (~500 lines), BigConj generic (~500 lines). All as `[PropositionalHilbert S]` lemmas. Target: `Cslib/Foundations/Logic/Theorems/`. ~2,400 lines.
  - Note: DeductionTheorem excluded (stays per-logic per team research finding).
- [ ] Add Task 21 (Modal Proof System and Theorems) to state.json:
  - `project_number`: 21, `project_name`: "modal_proof_system_theorems"
  - `status`: "not_started", `task_type`: "lean4"
  - `dependencies`: [16, 20]
  - Scope: (a) Modal.DerivationTree with ModalHilbert/ModalS5Hilbert instances (~400 lines), (b) S4/S5 derived theorems + GenNec as `[ModalS5Hilbert S]` lemmas (~1,200 lines), (c) Modal.Proposition.subst + substitution theorem. Target: `Cslib/Logics/Modal/ProofSystem/` + `Cslib/Logics/Modal/Theorems/`. ~1,600 lines.
- [ ] Add Task 22 (Temporal Infrastructure and Theorems) to state.json:
  - `project_number`: 22, `project_name`: "temporal_infrastructure_theorems"
  - `status`: "not_started", `task_type`: "lean4"
  - `dependencies`: [20]
  - Scope expanded per team research: (a) ~20 temporal axiom abbrevs in Axioms.lean, (b) ~20 HasAxiom* typeclasses in ProofSystem.lean, (c) restructure TemporalBXHilbert to extend all temporal HasAxiom* classes, (d) make TemporalNecessitation non-empty with actual derivation rule, (e) BimodalTMHilbert compatibility instance (diamond-avoidance pattern mirroring BimodalConnectives), (f) Temporal.DerivationTree + TemporalBXHilbert instance, (g) TemporalDerived theorems (~790 lines), (h) frame condition typeclasses (~130 lines). Target: Axioms.lean/ProofSystem.lean additions + `Cslib/Logics/Temporal/ProofSystem/` + `Cslib/Logics/Temporal/Theorems/`. ~1,500 lines.
- [ ] Add Task 23 (Temporal Semantics on Linear Orders) to state.json:
  - `project_number`: 23, `project_name`: "temporal_semantics_linear_orders"
  - `status`: "not_started", `task_type`: "lean4"
  - `dependencies`: [22]
  - Scope (new infrastructure, not ported from BimodalLogic): Define Temporal.Model on LinearOrder, Temporal.Satisfies for {atom, bot, imp, untl, snce}, basic validity, frame conditions on linear orders. Enables standalone temporal soundness. Target: `Cslib/Logics/Temporal/Semantics/`. ~400-600 lines.
- [ ] Update `next_project_number` to 24 in state.json
- [ ] Add all four tasks to TODO.md Tasks section (prepend at top)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `specs/state.json` -- add 4 new active_projects entries, update next_project_number to 24
- `specs/TODO.md` -- add 4 new task entries to Tasks section

**Verification**:
- `jq '.active_projects | length' specs/state.json` shows correct count (20 entries)
- Each new task has dependencies that reference only existing tasks
- next_project_number equals 24

---

### Phase 2: Create Seed Research Reports for Tasks 20-23 [NOT STARTED]

**Goal**: Create seed research reports for each new task, extracting relevant findings from the existing research reports (01 and 02) so that each new task can proceed directly to planning without a separate research phase.

**Tasks**:
- [ ] Create directory `specs/020_propositional_hilbert_theorems/reports/`
- [ ] Write `specs/020_propositional_hilbert_theorems/reports/01_seed-research.md`:
  - Extract propositional component classification from 01_factoring-synthesis.md
  - Include team research finding about DeductionTheorem staying per-logic
  - List source files, line counts, target paths, and generic signatures
  - Note that typeclass infrastructure (PropositionalHilbert) already exists
- [ ] Create directory `specs/021_modal_proof_system_theorems/reports/`
- [ ] Write `specs/021_modal_proof_system_theorems/reports/01_seed-research.md`:
  - Extract modal component classification from 01_factoring-synthesis.md
  - Include Modal.DerivationTree design from research
  - Note dependency on Task 16 (DecidableEq) and Task 20 (propositional theorems)
- [ ] Create directory `specs/022_temporal_infrastructure_theorems/reports/`
- [ ] Write `specs/022_temporal_infrastructure_theorems/reports/01_seed-research.md`:
  - Extract temporal component classification from 01_factoring-synthesis.md
  - Include team research findings about TemporalBXHilbert being empty, ~20 HasAxiom* classes needed
  - Include BimodalTMHilbert diamond-avoidance pattern recommendation
  - Note that TemporalNecessitation is currently a marker class
- [ ] Create directory `specs/023_temporal_semantics_linear_orders/reports/`
- [ ] Write `specs/023_temporal_semantics_linear_orders/reports/01_seed-research.md`:
  - Extract team research recommendation for standalone temporal semantics
  - Include the Temporal.Model and Temporal.Satisfies sketches from team research
  - Note that this is new infrastructure, not a port from BimodalLogic
  - Reference LeanLTL (ITP 2025) and FormalizedFormalLogic/Foundation patterns
- [ ] Update state.json for each new task: set `next_artifact_number: 2`, add artifact entry for the seed report

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `specs/020_propositional_hilbert_theorems/reports/01_seed-research.md` (new)
- `specs/021_modal_proof_system_theorems/reports/01_seed-research.md` (new)
- `specs/022_temporal_infrastructure_theorems/reports/01_seed-research.md` (new)
- `specs/023_temporal_semantics_linear_orders/reports/01_seed-research.md` (new)
- `specs/state.json` -- update artifact entries for tasks 20-23

**Verification**:
- Each seed report exists and references the correct source research
- Each seed report covers scope, dependencies, target paths, and key design decisions
- state.json artifact entries match the created files

---

### Phase 3: Revise Existing Tasks 2-7, 12, 17 [NOT STARTED]

**Goal**: Update task descriptions and dependencies for existing tasks to reflect the modular factoring, incorporating team research refinements. Revise task 17 to remove ROADMAP.md population from its scope since task 19 handles it.

**Tasks**:
- [ ] Revise Task 2 (Bimodal Syntax) in state.json and TODO.md:
  - Add clarifying note: generic BigConj/Context live in Task 20 at the typeclass level; Task 2 ports the bimodal-specific versions using all 6 formula constructors
  - Dependencies unchanged (BimodalLogic:291)
- [ ] Revise Task 4 (Bimodal Proof System) in state.json and TODO.md:
  - Update dependencies from `[2, "BimodalLogic:291"]` to `[2, 20, 22]`
  - Remove sub-task about completing temporal axiom abbrevs (now in Task 22)
  - Add note: imports propositional theorems from Task 20 and temporal axiom infrastructure from Task 22
  - Clarify scope: concrete 42-axiom Axiom inductive, DerivationTree (7 rules), Derivable, Substitution, BimodalTMHilbert instance registration
- [ ] Revise Task 5 (Bimodal Derived Theorems) in state.json and TODO.md:
  - Update dependencies from `[4, "BimodalLogic:291", "BimodalLogic:294"]` to `[4, 21, 22]`
  - Remove from scope: Combinators (~300 lines -> Task 20), Propositional/ (~1,100 lines -> Task 20), ContextualProofs (~500 lines -> Task 20), GeneralizedNecessitation (~400 lines -> Task 21), ModalS4/S5 (~800 lines -> Task 21), TemporalDerived (~790 lines -> Task 22)
  - Keep only: Perpetuity/ (~800 lines, inherently bimodal -- uses both modal and temporal operators)
  - Update effort from "Large (10-14 hours)" to "Small (3-5 hours)"
  - Retain BimodalLogic:294 external dependency (Perpetuity has sorry that needs elimination)
- [ ] Revise Task 6 (Bimodal Frame Conditions + Soundness) in state.json and TODO.md:
  - Remove temporal frame condition typeclasses (~130 lines, moved to Task 22)
  - Scope drops from ~2,500 to ~2,370 lines (minor change)
  - Dependencies unchanged: [3, 4]
- [ ] Revise Task 7 (Bimodal MCS/Deduction) in state.json and TODO.md:
  - Note: DeductionTheorem stays in this task (per team research, it requires structural induction on DerivationTree and cannot be ported generically)
  - Scope unchanged at ~2,500 lines (DeductionTheorem remains bimodal-specific)
  - Dependencies unchanged: [4, 5]
- [ ] Revise Task 12 (PR coordination) in TODO.md:
  - Update PR structure to include standalone module PRs:
    - PR-Foundations (Task 20): Propositional Hilbert theorems -- Wave 1
    - PR-Modal (Task 21): Modal proof system + theorems -- after PR-Foundations
    - PR-Temporal (Task 22): Temporal infrastructure + theorems -- after PR-Foundations
    - PR-TempSem (Task 23): Temporal semantics -- after PR-Temporal
    - Existing bimodal PRs (Tasks 2-11): proceed per existing ordering
  - Note: standalone module PRs can overlap with bimodal PRs since they target different directories
- [ ] Revise Task 17 in state.json and TODO.md:
  - Remove ROADMAP.md population from scope (task 19 handles it with full research context)
  - Updated description: "Clean stale task 14 references and verify Task Order consistency"
  - Remaining scope: (1) clean stale task 14 dependency references in TODO.md, (2) verify Task Order section reflects current dependency graph
  - Reduce effort to "Small (<1 hour)" since ROADMAP.md work is removed

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `specs/state.json` -- update dependencies and descriptions for tasks 2, 4, 5, 6, 7, 17
- `specs/TODO.md` -- update task entries for tasks 2, 4, 5, 6, 7, 12, 17

**Verification**:
- No circular dependencies in the task graph
- Task 5 effort reflects reduced scope (~800 lines)
- Task 7 scope is unchanged (DeductionTheorem stays)
- Task 12 PR ordering is consistent with new dependency graph
- Task 17 no longer references ROADMAP.md population

---

### Phase 4: Populate ROADMAP.md, Structure Task Order, Verify Consistency [NOT STARTED]

**Goal**: Populate ROADMAP.md with the phased porting plan, restructure the Task Order section of TODO.md into natural topic groupings, and perform final consistency checks.

**Tasks**:
- [ ] Populate ROADMAP.md with the modular factoring porting plan:
  - **Phase 1: Foundations** -- Task 20 (Propositional Hilbert Theorems): port ~2,400 lines of generic propositional theorems to `Cslib/Foundations/Logic/Theorems/`
  - **Phase 2: Modal and Temporal Modules** -- Tasks 21 (Modal Proof System), 22 (Temporal Infrastructure): port ~1,600 + ~1,500 lines to standalone Modal/ and Temporal/ modules
  - **Phase 3: Temporal Semantics** -- Task 23: define standalone temporal semantics on linear orders (~400-600 lines new infrastructure)
  - **Phase 4: Bimodal Porting** -- Tasks 2-11: port ~30,000+ lines of bimodal-specific content to `Cslib/Logics/Bimodal/`
  - Include milestones: "Foundations complete" (Task 20 done), "Standalone modules complete" (Tasks 21-23 done), "Bimodal integration complete" (Tasks 2-11 done), "PR pipeline complete" (Task 12 finalized)
  - Include dependency wave structure showing the Foundations -> Modal/Temporal -> Bimodal import hierarchy
  - Include success metrics: all ~5,000 extractable lines ported to correct modules, zero sorry in new code, lake build passes, standalone soundness theorems for temporal logic
- [ ] Restructure the Task Order section in TODO.md into topic groupings:
  - Replace the flat "### Uncategorized" section with these topic groups:
  - **### Foundations**: Task 20 (Propositional Hilbert Theorems)
  - **### Modal Logic**: Task 21 (Modal Proof System and Theorems)
  - **### Temporal Logic**: Task 22 (Temporal Infrastructure), Task 23 (Temporal Semantics) -- show 23 indented under 22 (dependency)
  - **### Bimodal Porting**: Tasks 2-11 in dependency order with tree structure (same tree as current, but under this header). Note cross-group dependencies on Tasks 20, 21, 22 where relevant.
  - **### Project Management**: Tasks 12, 15, 16, 17, 18, 19 -- coordination, cleanup, and meta tasks
  - Keep the Dependency Waves table at the top of the Task Order section, updated to reflect the full graph:
    - Wave 1: 2, 12, 15, 16, 17, 18, 20 (no internal logic-task dependencies)
    - Wave 2: 3 (depends on 2), 21 (depends on 16, 20), 22 (depends on 20)
    - Wave 3: 4 (depends on 2, 20, 22), 11 (depends on 4)
    - Wave 4: 5 (depends on 4, 21, 22), 6 (depends on 3, 4), 23 (depends on 22)
    - Wave 5: 7 (depends on 4, 5)
    - Wave 6: 8 (depends on 6, 7), 9 (depends on 4, 7), 10 (depends on 4, 5, 7)
- [ ] Verify consistency between state.json and TODO.md:
  - All tasks present in both files (20 active tasks expected)
  - Dependencies match between files
  - Status markers consistent
  - next_project_number = 24
- [ ] Verify the import hierarchy is enforced by dependencies:
  - Task 20 (Foundations/Propositional) has no logic-task dependencies -- Wave 1
  - Tasks 21 (Modal) and 22 (Temporal) depend on Task 20 -- Wave 2
  - Task 4 (Bimodal proof system) depends on Tasks 2, 20, 22 -- Wave 3
  - Task 5 (Bimodal derived theorems) depends on Tasks 4, 21, 22 -- Wave 4
  - Enforces: Foundations -> Modal/Temporal -> Bimodal
- [ ] Verify no component is double-counted:
  - Combinators: Task 20 only
  - Propositional/{Core,Connectives,Reasoning}: Task 20 only
  - ContextualProofs: Task 20 only
  - BigConj (generic): Task 20 only
  - DeductionTheorem: Task 7 only (bimodal-specific, per team research)
  - S4/S5 derived theorems: Task 21 only
  - GeneralizedNecessitation: Task 21 only
  - TemporalDerived: Task 22 only
  - Temporal frame conditions: Task 22 only
  - Perpetuity/: Task 5 only
- [ ] Verify ROADMAP.md content is consistent with the task graph and dependency waves

**Timing**: 45 minutes

**Depends on**: 2, 3

**Files to modify**:
- `specs/ROADMAP.md` -- replace default template with phased porting plan
- `specs/TODO.md` -- restructure Task Order section into topic groupings

**Verification**:
- ROADMAP.md contains phased plan with milestones and success metrics
- Task Order uses topic headers (Foundations, Modal Logic, Temporal Logic, Bimodal Porting, Project Management)
- Dependency wave table has no cycles
- Every extractable component maps to exactly one task
- state.json and TODO.md are fully synchronized
- Cross-group dependencies noted in Bimodal Porting section (e.g., Task 4 depends on Tasks 20, 22)

---

## Testing & Validation

- [ ] All tasks in state.json have valid `project_number`, `status`, `task_type`, and `dependencies`
- [ ] state.json `next_project_number` equals 24
- [ ] TODO.md Task Order section uses topic groupings (not "Uncategorized")
- [ ] TODO.md Task Order dependency wave table reflects the correct 6-wave dependency graph
- [ ] ROADMAP.md contains the 4-phase porting plan with milestones and success metrics
- [ ] No circular dependencies in the task graph
- [ ] The ~5,000 extractable lines are accounted for: ~2,400 propositional (Task 20) + ~1,200 modal (Task 21) + ~920 temporal (Task 22) + ~800 perpetuity (Task 5) = ~5,320 lines. DeductionTheorem (~500 lines) stays in Task 7.
- [ ] No component appears in both a new task (20-23) and a revised bimodal task (2-11)
- [ ] Task 5 effort estimate reflects reduced scope (~800 lines vs original ~7,300 lines)
- [ ] Seed research reports exist for tasks 20-23 and are referenced in state.json artifacts
- [ ] Task 17 no longer includes ROADMAP.md population in its scope
- [ ] `lake build` still passes (no code changes, only task metadata changes)

## Artifacts & Outputs

- `specs/019_explore_modular_logic_factoring/plans/02_revised-factoring.md` (this plan)
- `specs/state.json` (updated with 4 new tasks + revised existing tasks)
- `specs/TODO.md` (updated with 4 new task entries + revised descriptions + topic-grouped Task Order)
- `specs/ROADMAP.md` (populated with phased porting plan, milestones, and success metrics)
- `specs/020_propositional_hilbert_theorems/reports/01_seed-research.md` (new)
- `specs/021_modal_proof_system_theorems/reports/01_seed-research.md` (new)
- `specs/022_temporal_infrastructure_theorems/reports/01_seed-research.md` (new)
- `specs/023_temporal_semantics_linear_orders/reports/01_seed-research.md` (new)

## Rollback/Contingency

All changes target specs/ files only (state.json, TODO.md, ROADMAP.md, seed research reports). No Lean source files are modified. If the restructuring proves problematic:
1. Revert to the pre-implementation commit: `git checkout HEAD -- specs/state.json specs/TODO.md specs/ROADMAP.md`
2. Remove new task directories: `rm -rf specs/02{0,1,2,3}_*`
3. The original task descriptions are fully recoverable via git history
4. `lake build` is unaffected since no code changes are made
