# Research Report: Task #25 — Revise Task Order Topic Assignments

**Task**: 25 - Revise Task Order topic assignments based on ROADMAP.md
**Started**: 2026-06-09T01:10:00Z
**Completed**: 2026-06-09T01:25:00Z
**Effort**: Small (1 hour)
**Dependencies**: None
**Sources/Inputs**: specs/state.json, specs/ROADMAP.md, .claude/scripts/generate-task-order.sh, specs/TODO.md
**Artifacts**: specs/025_revise_task_order_topic_assignments/reports/01_topic-assignments-research.md
**Standards**: report-format.md, subagent-return.md

---

## Executive Summary

- The core problem is that `generate-task-order.sh` renders DFS successor trees per topic, so tasks in one topic that depend on tasks in another topic pull the dependent tasks' entire subtrees into the first topic's section as indented children — even though those successors have their own canonical topic assignment.
- The **existing topic assignments in state.json are nearly correct** for primary ownership. The main issues are (1) Task 21 (Modal Logic) and Task 22 (Temporal Logic) appear redundantly as successors inside the Foundations section because Task 20 owns them as children, and (2) Task 4, 5, 6, 7–11 (all Bimodal Porting) are pulled into earlier sections as children of their dependencies.
- **The root fix is in the rendering logic**, not just the topic fields. The `_print_topic_node` function must skip printing any successor whose topic differs from the current section topic — showing only a "(see Bimodal Porting)" cross-reference annotation rather than recursing into their subtrees. The `(see above)` cross-references are already being emitted at depth > 0, but they are still triggered when a task first appears as a child of a cross-topic dependency, which causes the full subtree to render in the wrong section.
- Two minor topic field corrections are also needed: Task 15 ("Complete embedding lattice") is assigned `"Project Management"` but belongs to `"Foundations"` (it is a Lean 4 implementation task for CSLib foundational embedding code). Task 21 should appear only under `"Modal Logic"` and Task 22 only under `"Temporal Logic"` — their current topic fields are already correct; the problem is the DFS rendering pulling them under the Foundations section.

---

## Context & Scope

This research examines:
1. The current `topic` field values for all active tasks in `state.json`
2. The authoritative topic groupings from `specs/ROADMAP.md`
3. The rendering logic in `.claude/scripts/generate-task-order.sh` to understand why tasks appear under multiple headings

The goal is to identify specific fixes so each task appears exactly once in the Task Order topic-grouped section.

---

## Findings

### Current Topic Assignments (from state.json)

| Task | Title (abbreviated) | Current Topic | Status |
|------|---------------------|---------------|--------|
| 2 | Port Bimodal Syntax | Bimodal Porting | correct |
| 3 | Port Task Frame Semantics | Bimodal Porting | correct |
| 4 | Port Proof System | Bimodal Porting | correct |
| 5 | Port Perpetuity Theorems | Bimodal Porting | correct |
| 6 | Port Frame Conditions + Soundness | Bimodal Porting | correct |
| 7 | Port Deduction + MCS Theory | Bimodal Porting | correct |
| 8 | Port Completeness | Bimodal Porting | correct |
| 9 | Port Decidability + Tableau | Bimodal Porting | correct |
| 10 | Port Separation Theorem | Bimodal Porting | correct |
| 11 | Port Conservative Extension | Bimodal Porting | correct |
| 12 | Coordinate PR Submission | Project Management | correct |
| 15 | Complete Embedding Lattice | **Project Management** | **WRONG — should be Foundations** |
| 16 | Formula Type Consistency | Modal Logic | correct |
| 17 | Project Management Roadmap/TaskOrder | Project Management | correct |
| 18 | Generate Project Overview | Project Management | correct |
| 19 | Explore Modular Logic Factoring | Project Management | correct |
| 20 | Propositional Hilbert Theorems | Foundations | correct |
| 21 | Modal Proof System Theorems | Modal Logic | correct |
| 22 | Temporal Infrastructure Theorems | Temporal Logic | correct |
| 23 | Temporal Semantics Linear Orders | Temporal Logic | correct |
| 24 | Improve ROADMAP.md | Project Management | correct |
| 25 | Revise Task Order Topic Assignments | Project Management | correct |
| 26 | Revise ROADMAP Focus | Project Management | correct |

**Note**: Task 15 is completed and may have been archived already. Tasks 17, 18, 19, 24, 26 are completed. Task 26 is in the active list with status `completed`. The `generate-task-order.sh` filters out `completed`, `abandoned`, and `expanded` tasks before rendering, so completed tasks do not appear in the output. However Task 15 appears in the state.json with `"status": "completed"` and thus is filtered. The wrong topic on Task 15 is cosmetic for the current output.

### ROADMAP.md Authoritative Groupings

From `specs/ROADMAP.md`, the four-phase porting structure maps directly to topic categories:

| ROADMAP Phase | Topic Name | Tasks |
|---------------|------------|-------|
| Phase 1: Propositional | Foundations | 20 |
| Phase 2: Modal Module | Modal Logic | 21 |
| Phase 2: Temporal Module | Temporal Logic | 22 |
| Phase 3: Temporal Semantics | Temporal Logic | 23 |
| Phase 4: Bimodal Porting | Bimodal Porting | 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 |
| Ongoing: PR Coordination | Project Management | 12 |
| Infrastructure/Meta | Project Management | 15, 16, 17, 18, 19, 24, 25, 26 |

**Observation**: The ROADMAP places Task 16 (DecidableEq on Modal.Proposition) in Wave 2 as a dependency for Task 21. It is a modal code fix and thus belongs to `"Modal Logic"` — which matches its current assignment. The ROADMAP does not list Task 16 as a Foundations task.

### Current Rendering Problem: Root Cause Analysis

The `generate-task-order.sh` script builds a **successor tree** (not a predecessor tree): for each task, it prints that task and then recurses into all tasks that **depend on it** (i.e., successors in the dependency graph). This means:

- **Task 20 (Foundations)** is a root task with no active dependencies. Its successors include Tasks 4, 21, and 22 (all of which depend on Task 20).
- When rendering the `### Foundations` section, the script starts with Task 20, then recurses into ALL successors — including Tasks 4 (Bimodal Porting), 21 (Modal Logic), and 22 (Temporal Logic).
- Each of those recursed tasks then recurses into their own successors (Tasks 5, 6, 7, 8, 9, 10, 11, 23), pulling the entire Bimodal Porting subtree into the Foundations section.

The `_globally_visited` tracking prevents tasks from being printed in full twice, but the **first time** a task appears in any section it is printed fully (without the `"(see above)"` annotation). The check at line 479 only triggers the cross-topic annotation when `depth > 0` AND the task has already been globally visited. So the very first encounter of a cross-topic task (even as a deep nested child) renders it fully without annotation.

**Specific current output excerpt (Foundations section)**:
```
### Foundations

20 [NOT STARTED] — ...           <- correct: depth 0, Foundations task
  └─ 4 [NOT STARTED] — ...       <- WRONG: depth 1, Bimodal Porting task, first visit
    └─ 5 [NOT STARTED] — ...     <- WRONG: depth 2, Bimodal Porting task
      └─ 7 [NOT STARTED] — ...   <- WRONG: depth 3
...
  └─ 21 [NOT STARTED] — ...      <- WRONG: depth 1, Modal Logic task, first visit
  └─ 22 [NOT STARTED] — ...      <- WRONG: depth 1, Temporal Logic task, first visit
```

Then in `### Modal Logic`:
```
### Modal Logic

16 [NOT STARTED] — ...          <- correct: depth 0
  └─ 21 [NOT STARTED] — ...    <- "(see above)" because already visited globally
21 [NOT STARTED] — ...         <- printed again as a root since it's a topic_tasks root!
```

This reveals a **second problem**: Task 21 appears twice in the Modal Logic section — once as a successor of Task 16 (with "(see above)") and once as a root task of the section. This is because `topic_tasks` for Modal Logic includes both Task 16 and Task 21, and when iterating roots (tasks with no active deps), Task 16 qualifies. Then in the "remaining unvisited" pass, Task 21 also prints because it was marked globally visited in the Foundations section, but the section re-visit check only suppresses depth > 0 occurrences.

Wait — examining more carefully: in the `### Modal Logic` output, Task 21 appears both as a successor of 16 (annotated `(see above)`) AND as a standalone root line **without** `(see above)`. This is because the "remaining unvisited in this topic" fallback at line 419 checks `_topic_section_visited` (per-section tracking), not `_globally_visited`. Since Task 21 was globally visited in the Foundations pass but NOT in the current Modal Logic topic section, `_topic_section_visited[$21]` is empty, so the fallback loop prints it again.

### Summary of Rendering Logic Bugs

**Bug 1: Cross-topic successors rendered fully in wrong section**

When a task in Topic A has a successor in Topic B, the DFS renderer prints that successor (and its entire subtree) in Topic A's section — because the first encounter triggers a full render.

Fix: In `_print_topic_node`, before recursing into a successor, check if the successor's topic matches `_current_section_topic`. If it differs, print a cross-reference annotation and do NOT recurse.

**Bug 2: Tasks print twice in their own section**

A task can appear both as an annotated successor of another task within its own section AND as a standalone root in the fallback loop — because the fallback loop only checks `_topic_section_visited`, which was never set for this section.

Fix: When a task is already in `_globally_visited` at depth 0, the section fallback should use `_globally_visited` (not just `_topic_section_visited`) to suppress the duplicate.

### Correct Desired Output Structure

After applying the fixes, the sections should look like:

```
### Foundations

20 [NOT STARTED] — Propositional Hilbert theorems
  └─ 4 [Bimodal Porting] (see Bimodal Porting section)
  └─ 21 [Modal Logic] (see Modal Logic section)
  └─ 22 [Temporal Logic] (see Temporal Logic section)

### Modal Logic

16 [NOT STARTED] — Add DecidableEq to Modal.Proposition
  └─ 21 [NOT STARTED] — Modal proof system and theorems
    └─ 5 [Bimodal Porting] (see Bimodal Porting section)

### Temporal Logic

22 [NOT STARTED] — Temporal infrastructure and theorems
  └─ 4 [Bimodal Porting] (see Bimodal Porting section)
  └─ 5 [Bimodal Porting] (see Bimodal Porting section)
  └─ 23 [NOT STARTED] — Temporal semantics on linear orders

### Bimodal Porting

2 [NOT STARTED] — Port Bimodal Syntax
  └─ 3 [NOT STARTED] — Port Task Frame Semantics
    └─ 6 [NOT STARTED] — Port Frame Conditions + Soundness
      └─ 8 [NOT STARTED] — Port Completeness
  └─ 4 [NOT STARTED] — Port Proof System
    └─ 5 [NOT STARTED] — Port Perpetuity Theorems
      └─ 7 [NOT STARTED] — Port Deduction + MCS
        └─ 8 [NOT STARTED] — (see above)
        └─ 9 [NOT STARTED] — Port Decidability + Tableau
        └─ 10 [NOT STARTED] — Port Separation Theorem
    └─ 6 [NOT STARTED] — (see above)
    └─ 7 [NOT STARTED] — (see above)
    └─ 9 [NOT STARTED] — (see above)
    └─ 10 [NOT STARTED] — (see above)
    └─ 11 [NOT STARTED] — Port Conservative Extension
...

### Project Management

12 [PARTIAL] — Coordinate PR Submission
25 [RESEARCHING] — Revise Task Order Topic Assignments
```

---

## Decisions

1. **Do not change topic field values** in state.json for the porting tasks (2–11) or standalone module tasks (20–23). Their assignments already correctly reflect ROADMAP.md ownership.

2. **Fix Topic 15 topic field**: Change `"Project Management"` to `"Foundations"`. Task 15 ("Complete Embedding Lattice") is a Lean 4 implementation task that adds atom simp lemmas and embedding paths for the foundational PL/Modal/Bimodal formula lattice — it is Foundations content. However, since Task 15 is already completed and filtered from the rendered output, this fix is cosmetic and low priority.

3. **Fix the rendering logic in `generate-task-order.sh`**: The two bugs identified above require changes to `_print_topic_node`:
   - **Bug 1 fix**: When iterating successors in `_print_topic_node`, check if each successor's topic matches `_current_section_topic`. If it doesn't match, emit a brief cross-reference line and skip recursing.
   - **Bug 2 fix**: In the fallback "remaining unvisited" loop inside `generate_grouped_section`, check `_globally_visited` in addition to `_topic_section_visited` to suppress duplicate root-level entries.

4. **The `_globally_visited` check at depth 0 for section fallback**: The current code at line 419-422 correctly handles the case where tasks were not printed in the root pass, but it does not check if they were printed in a prior topic section. The fallback should guard against globally visited tasks to prevent them from appearing as fresh entries in their own topic section after being recursed into from a parent in a prior section.

---

## Recommendations

### Fix 1: Correct topic field for Task 15 (low priority, cosmetic)

In `specs/state.json`, change Task 15's `"topic"` from `"Project Management"` to `"Foundations"`. Since Task 15 is completed and filtered from rendering, this only affects display if task 15 is ever un-archived or the filter changes.

### Fix 2: Change rendering logic in generate-task-order.sh (high priority)

In `_print_topic_node`, modify the successor iteration loop to gate cross-topic recursion:

```bash
# Current code (lines ~496-507):
local deps="${task_successors[$task_num]:-}"
if [[ -n "$deps" ]]; then
  sorted_deps=$(echo "$deps" | tr ' ' '\n' | sort -n | tr '\n' ' ')
  read -ra dep_array <<< "$sorted_deps"
  for dep in "${dep_array[@]}"; do
    [[ -z "$dep" ]] && continue
    if [[ -n "${task_status[$dep]+x}" ]]; then
      _print_topic_node "$dep" $((depth + 1))
    fi
  done
fi
```

Change to:
```bash
local deps="${task_successors[$task_num]:-}"
if [[ -n "$deps" ]]; then
  sorted_deps=$(echo "$deps" | tr ' ' '\n' | sort -n | tr '\n' ' ')
  read -ra dep_array <<< "$sorted_deps"
  for dep in "${dep_array[@]}"; do
    [[ -z "$dep" ]] && continue
    if [[ -n "${task_status[$dep]+x}" ]]; then
      local dep_topic="${task_topic[$dep]:-}"
      # Only recurse into same-topic successors; cross-topic gets a reference line
      if [[ -n "$dep_topic" && "$dep_topic" != "$_current_section_topic" ]]; then
        # Cross-topic: emit reference line, do not recurse
        local pad
        pad=$(printf '%*s' $(( depth * 2 )) '')
        local dep_status_display
        dep_status_display=$(format_status "${task_status[$dep]:-not_started}")
        echo "${pad}  └─ ${dep} [${dep_status_display}] — (see ${dep_topic} section)"
        _globally_visited["$dep"]=1
      else
        _print_topic_node "$dep" $((depth + 1))
      fi
    fi
  done
fi
```

### Fix 3: Guard fallback loop against globally visited tasks

In `generate_grouped_section`, modify the "remaining unvisited" fallback:

```bash
# Current code (lines ~417-422):
for tn in "${topic_tasks[@]}"; do
  if [[ -z "${_topic_section_visited[$tn]+x}" ]]; then
    _print_topic_node "$tn" 0
  fi
done
```

Change to:
```bash
for tn in "${topic_tasks[@]}"; do
  if [[ -z "${_topic_section_visited[$tn]+x}" && -z "${_globally_visited[$tn]+x}" ]]; then
    _print_topic_node "$tn" 0
  fi
done
```

---

## Risks & Mitigations

- **Risk**: The cross-topic reference format `"(see ${dep_topic} section)"` may be verbose if many cross-topic references exist. The Bimodal Porting dependencies on Foundations tasks (20) and Temporal/Modal tasks (21, 22) will produce several such lines.
  - **Mitigation**: This is acceptable — it makes the cross-topic structure explicit and users can navigate to the named section. The current duplication is worse.

- **Risk**: If `_current_section_topic` is empty (Uncategorized section), the cross-topic gating may suppress uncategorized tasks from being properly linked.
  - **Mitigation**: Add a guard: only apply the cross-topic check when `_current_section_topic` is non-empty.

- **Risk**: The wave table in the dependency waves section (`generate_wave_table`) still shows all topics per wave (e.g., Wave 1 shows "Foundations, Modal Logic, Bimodal Porting, ..."). This is correct behavior — the wave table is a summary view across all topics.
  - **Mitigation**: No change needed to the wave table.

---

## Context Extension Recommendations

- **Topic**: generate-task-order.sh rendering behavior
- **Gap**: No documented explanation of the DFS successor rendering algorithm and its cross-topic behavior
- **Recommendation**: Add a comment block in `generate-task-order.sh` near `_print_topic_node` explaining the cross-topic gating logic for future maintainers.

---

## Appendix

### Search queries used
- Local codebase: state.json, ROADMAP.md, TODO.md, generate-task-order.sh
- Script execution: `generate-task-order.sh --print` to observe current output

### Key script locations
- `/home/benjamin/Projects/cslib/.claude/scripts/generate-task-order.sh`
- `/home/benjamin/Projects/cslib/specs/state.json`
- `/home/benjamin/Projects/cslib/specs/ROADMAP.md`

### Active topic assignments (post-fix summary)

| Task | Correct Topic | Notes |
|------|---------------|-------|
| 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 | Bimodal Porting | Already correct in state.json |
| 12 | Project Management | Already correct |
| 15 | Foundations | Currently "Project Management" — needs fix (low priority, task completed) |
| 16 | Modal Logic | Already correct |
| 17, 18, 19, 24, 25, 26 | Project Management | Already correct |
| 20 | Foundations | Already correct |
| 21 | Modal Logic | Already correct |
| 22, 23 | Temporal Logic | Already correct |
