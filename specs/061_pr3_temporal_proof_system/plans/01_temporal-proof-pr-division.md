# Implementation Plan: PR3 Temporal Proof System Sub-PR Task Creation

- **Task**: 61 - pr3_temporal_proof_system
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: None (meta task -- creates state.json entries only)
- **Research Inputs**: specs/061_pr3_temporal_proof_system/reports/01_temporal-proof-pr-division.md
- **Artifacts**: plans/01_temporal-proof-pr-division.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

This is a meta task that creates 5 sub-PR task entries in state.json (tasks 159-163) for the temporal proof system (PR3), following the decomposition pattern established by task 124 (PR1, 11 sub-PRs) and task 60 (PR2, 14 sub-PRs). The implementation writes state.json entries, creates task directories, marks the parent task 61 as "expanded", and regenerates TODO.md. No Lean code is written.

### Research Integration

The research report (01_temporal-proof-pr-division.md) provides a complete file manifest of 14 temporal logic files totaling 2,129 lines, an internal dependency DAG, and a proposed 5 sub-PR subdivision with detailed descriptions, dependency chains, and LOC estimates. The plan directly uses the report's sub-PR definitions, dependency structure, and proposed task descriptions.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Create 5 sub-PR task entries (159-163) in state.json with correct dependencies, descriptions, and task_type
- Create corresponding task directories under specs/
- Mark task 61 as "expanded" with completion_summary
- Regenerate TODO.md from state.json
- Commit all changes

**Non-Goals**:
- Writing any Lean 4 code
- Creating branches for the sub-PRs
- Submitting actual PRs to upstream
- Creating research reports or implementation plans for the sub-PR tasks

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| next_project_number has changed since research | L | L | Read state.json at implementation time to get current value |
| Dependency numbers incorrect if other tasks created first | M | L | Use atomic state.json update; verify all referenced task numbers exist |
| Task 61 status prevents expansion | M | L | Verify task 61 is in non-terminal status before updating |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Create Sub-PR Task Entries in state.json [COMPLETED]

**Goal**: Add 5 new task entries to state.json for sub-PRs 3.1 through 3.5, and create their task directories.

**Tasks**:
- [ ] Read current state.json to confirm next_project_number (expected: 159)
- [ ] Add task 159: subpr_3_1_temporal_formula
- [ ] Add task 160: subpr_3_2_syntax_utilities
- [ ] Add task 161: subpr_3_3_axioms_derivation
- [ ] Add task 162: subpr_3_4_proof_system_instances
- [ ] Add task 163: subpr_3_5_semantics_embedding
- [ ] Update next_project_number to 164
- [ ] Create task directories: specs/159_subpr_3_1_temporal_formula/ through specs/163_subpr_3_5_semantics_embedding/

**Timing**: 30 minutes

**Depends on**: none

**Exact Task Entries**:

Each entry uses these common fields:
- `status`: `"not_started"`
- `task_type`: `"cslib"`
- `topic`: `"Submit PRs"`
- `created`: current ISO8601 timestamp
- `last_updated`: current ISO8601 timestamp
- `session_id`: `"sess_1781245722_780d58"`
- `next_artifact_number`: 1
- `artifacts`: []

**Task 159** -- subpr_3_1_temporal_formula:
```json
{
  "project_number": 159,
  "project_name": "subpr_3_1_temporal_formula",
  "status": "not_started",
  "task_type": "cslib",
  "topic": "Submit PRs",
  "dependencies": [138],
  "description": "Sub-PR 3.1: Temporal formula type. Introduces Syntax/Formula.lean (549 lines) defining the temporal logic Formula inductive with primitives {atom, bot, imp, untl, snce}, all derived connectives (neg, top, or, and, iff, allFuture/G, someFuture/F, allPast/H, somePast/P), the swapTemporal involution, Encodable/Denumerable instances, and connective typeclass registrations (HasBot, HasImp, HasUntil, HasSince, TemporalConnectives). Gateway PR for all temporal logic. ~549 diff lines. External dependency: Cslib.Foundations.Logic.Connectives (PR1 sub-PR 1.1.1, task 138).",
  "session_id": "sess_1781245722_780d58",
  "next_artifact_number": 1,
  "artifacts": []
}
```

**Task 160** -- subpr_3_2_syntax_utilities:
```json
{
  "project_number": 160,
  "project_name": "subpr_3_2_syntax_utilities",
  "status": "not_started",
  "task_type": "cslib",
  "topic": "Submit PRs",
  "dependencies": [159],
  "description": "Sub-PR 3.2: Temporal syntax utilities. Adds Context.lean (131 lines, Context = List (Formula Atom) with map/membership lemmas), BigConj.lean (52 lines, big conjunction over formula lists), and Subformulas.lean (218 lines, subformula closure with membership and transitivity lemmas). ~401 diff lines across 3 files.",
  "session_id": "sess_1781245722_780d58",
  "next_artifact_number": 1,
  "artifacts": []
}
```

**Task 161** -- subpr_3_3_axioms_derivation:
```json
{
  "project_number": 161,
  "project_name": "subpr_3_3_axioms_derivation",
  "status": "not_started",
  "task_type": "cslib",
  "topic": "Submit PRs",
  "dependencies": [160],
  "description": "Sub-PR 3.3: Temporal axioms and derivation trees. Adds Axioms.lean (235 lines, 26 BX axiom constructors with FrameClass classification: Base/Dense/Discrete), Derivation.lean (98 lines, Type-valued DerivationTree with 6 inference rules: axiom, assumption, modus_ponens, temporal_necessitation, temporal_duality, weakening), and Derivable.lean (99 lines, Prop-valued Nonempty wrapper with constructor-mirroring lemmas). ~432 diff lines across 3 files.",
  "session_id": "sess_1781245722_780d58",
  "next_artifact_number": 1,
  "artifacts": []
}
```

**Task 162** -- subpr_3_4_proof_system_instances:
```json
{
  "project_number": 162,
  "project_name": "subpr_3_4_proof_system_instances",
  "status": "not_started",
  "task_type": "cslib",
  "topic": "Submit PRs",
  "dependencies": [161, 140],
  "description": "Sub-PR 3.4: Temporal proof system instances. Adds Instances.lean (214 lines, registers InferenceSystem, ModusPonens, ClassicalHilbert, TemporalNecessitation, 22 HasAxiom* instances, and TemporalBXHilbert for HilbertBX tag type) and ProofSystem.lean barrel (23 lines). Bridges abstract Foundation typeclass hierarchy to concrete derivation tree. ~237 diff lines across 2 files. External dependency: Cslib.Foundations.Logic.ProofSystem (PR1 sub-PR 1.1.3, task 140).",
  "session_id": "sess_1781245722_780d58",
  "next_artifact_number": 1,
  "artifacts": []
}
```

**Task 163** -- subpr_3_5_semantics_embedding:
```json
{
  "project_number": 163,
  "project_name": "subpr_3_5_semantics_embedding",
  "status": "not_started",
  "task_type": "cslib",
  "topic": "Submit PRs",
  "dependencies": [160, 142],
  "description": "Sub-PR 3.5: Temporal semantics and PL embedding. Adds Model.lean (60 lines, TemporalModel structure on LinearOrder), Satisfies.lean (177 lines, recursive satisfaction relation with Burgess convention), Validity.lean (198 lines, validity hierarchy: Valid/ValidSerial/ValidDense/ValidDiscrete), FromPropositional.lean (56 lines, structural PL -> Temporal embedding with coercion), and Theorems.lean barrel (19 lines, re-exports Foundation temporal derived theorems). ~510 diff lines across 5 files. External dependencies: Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived and FrameConditions (PR1 sub-PRs 1.1.5/1.1.6, tasks 142-143).",
  "session_id": "sess_1781245722_780d58",
  "next_artifact_number": 1,
  "artifacts": []
}
```

**Sub-PR Dependency DAG**:
```
Task 138 (PR1 1.1.1 Connectives) ──┐
                                    v
                              159 (3.1 Formula)
                                    │
                                    v
                              160 (3.2 Syntax Utils)
                               /           \
                              v             v
                        161 (3.3 Axioms)  163 (3.5 Semantics)
                              │                    ^
                              v                    │
Task 140 (PR1 1.1.3) ──> 162 (3.4 Instances)      │
                                         Task 142 (PR1 1.1.5) ──┘
```

**Files to modify**:
- `specs/state.json` - Add 5 task entries, update next_project_number

**Files to create**:
- `specs/159_subpr_3_1_temporal_formula/` (directory)
- `specs/160_subpr_3_2_syntax_utilities/` (directory)
- `specs/161_subpr_3_3_axioms_derivation/` (directory)
- `specs/162_subpr_3_4_proof_system_instances/` (directory)
- `specs/163_subpr_3_5_semantics_embedding/` (directory)

**Verification**:
- `jq '.next_project_number' specs/state.json` returns 164
- `jq '[.active_projects[] | select(.project_number >= 159 and .project_number <= 163)] | length' specs/state.json` returns 5
- All 5 task directories exist under specs/
- Each task entry has correct dependencies, task_type "cslib", and topic "Submit PRs"

---

### Phase 2: Update Parent Task 61 [COMPLETED]

**Goal**: Mark task 61 as "expanded" with completion_summary describing the 5 sub-tasks created.

**Tasks**:
- [ ] Update task 61 status to "expanded" in state.json
- [ ] Set completion_summary: "Expanded into 5 sub-PRs (tasks 159-163) for temporal proof system incremental submission: 3.1 Formula (549 LOC), 3.2 Syntax utilities (401 LOC), 3.3 Axioms/derivation (432 LOC), 3.4 ProofSystem instances (237 LOC), 3.5 Semantics/embedding (510 LOC). Total: 2,129 lines across 14 files."
- [ ] Update last_updated timestamp

**Timing**: 10 minutes

**Depends on**: 1

**Files to modify**:
- `specs/state.json` - Update task 61 entry

**Verification**:
- `jq '.active_projects[] | select(.project_number == 61) | .status' specs/state.json` returns "expanded"
- completion_summary is set

---

### Phase 3: Regenerate TODO.md and Commit [COMPLETED]

**Goal**: Regenerate TODO.md from updated state.json and commit all changes.

**Tasks**:
- [ ] Run `bash .claude/scripts/generate-todo.sh` to regenerate TODO.md
- [ ] Verify TODO.md contains all 5 new sub-PR tasks
- [ ] Verify task 61 shows [EXPANDED] status in TODO.md
- [ ] Stage and commit: `task 61: expand into sub-PRs 159-163`

**Timing**: 10 minutes

**Depends on**: 2

**Files to modify**:
- `specs/TODO.md` - Regenerated from state.json

**Verification**:
- TODO.md contains entries for tasks 159-163
- Task 61 shows [EXPANDED] in TODO.md
- Git commit succeeds

## Testing & Validation

- [ ] state.json is valid JSON after all modifications
- [ ] next_project_number is 164
- [ ] All 5 new tasks have correct project_number, project_name, dependencies, task_type, and description
- [ ] Task 61 status is "expanded" with completion_summary
- [ ] TODO.md is consistent with state.json
- [ ] All 5 task directories exist
- [ ] Dependency chain is acyclic: 159 -> 160 -> 161 -> 162, 160 -> 163 (with external deps on 138, 140, 142)

## Artifacts & Outputs

- `specs/061_pr3_temporal_proof_system/plans/01_temporal-proof-pr-division.md` (this file)
- 5 new task entries in specs/state.json (tasks 159-163)
- 5 new task directories under specs/
- Updated task 61 entry (expanded)
- Regenerated specs/TODO.md

## Rollback/Contingency

If the implementation fails:
1. Revert state.json to the pre-implementation version using `git checkout -- specs/state.json`
2. Remove created directories: `rm -rf specs/159_* specs/160_* specs/161_* specs/162_* specs/163_*`
3. Regenerate TODO.md: `bash .claude/scripts/generate-todo.sh`
