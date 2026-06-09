# Implementation Plan: Revise Task Order Topic Assignments

- **Task**: 25 - Revise Task Order topic assignments based on ROADMAP.md
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/025_revise_task_order_topic_assignments/reports/01_topic-assignments-research.md
- **Artifacts**: plans/01_topic-assignment-fixes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: meta
- **Lean Intent**: false

## Overview

The `generate-task-order.sh` script renders topic-grouped dependency trees using DFS successor traversal, but two bugs cause tasks to appear in the wrong topic section or appear duplicated in their own section. Bug 1: `_print_topic_node` recurses into cross-topic successors without checking whether the successor belongs to the current section's topic, pulling entire subtrees (e.g., Bimodal Porting tasks) into earlier sections (e.g., Foundations). Bug 2: the fallback "remaining unvisited" loop only checks `_topic_section_visited`, not `_globally_visited`, so tasks already rendered as children in a prior section re-appear as root entries in their own section. A minor cosmetic fix to Task 15's topic field in state.json is also needed.

### Research Integration

The research report (`01_topic-assignments-research.md`) identified the root cause as rendering logic bugs, not topic field misassignments. All topic values in state.json are correct except Task 15 ("Complete Embedding Lattice"), which is labeled "Project Management" but should be "Foundations". The report provides exact line numbers and proposed code patches for both bugs, along with the desired output format showing cross-topic reference annotations instead of full subtree recursion.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md update required. This is a meta/infrastructure task that fixes the Task Order rendering in TODO.md.

## Goals & Non-Goals

**Goals**:
- Fix `_print_topic_node` to gate cross-topic successor recursion, emitting a cross-reference annotation instead of rendering the full subtree
- Fix the fallback loop in `generate_grouped_section` to check `_globally_visited` in addition to `_topic_section_visited`
- Fix Task 15's topic field in state.json from "Project Management" to "Foundations"
- Regenerate the Task Order section in TODO.md to verify correct output

**Non-Goals**:
- Changing topic assignments for any task other than Task 15
- Modifying the wave table generation logic (it correctly shows cross-topic summaries)
- Altering the Dependency Tree (non-grouped) rendering logic
- Changing the DFS-to-BFS traversal strategy

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Cross-topic gating hides legitimate dependency visibility | M | L | Cross-reference annotation preserves the dependency signal without rendering the full subtree |
| Empty `_current_section_topic` (Uncategorized) causes false gating | M | L | Guard: only apply cross-topic check when `_current_section_topic` is non-empty |
| Marking cross-topic successors as globally visited prevents them from appearing in their own section | H | M | Do NOT mark cross-topic successors as globally visited when emitting a reference line; let them render fully in their own section |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Fix Rendering Logic in generate-task-order.sh [COMPLETED]

**Goal**: Patch the two bugs in the DFS rendering logic so each task appears exactly once under its own topic section, with cross-topic dependencies shown as brief reference annotations.

**Tasks**:
- [x] Fix Bug 1 in `_print_topic_node` (lines ~496-507): Before recursing into each successor, check if the successor's topic differs from `_current_section_topic`. If it differs (and `_current_section_topic` is non-empty), emit a cross-reference annotation line (e.g., `"(see {topic} section)"`) and skip recursion. Do NOT mark the cross-topic successor as `_globally_visited` so it can still render fully in its own section. *(completed)*
- [x] Fix Bug 2 in `generate_grouped_section` fallback loop (lines ~418-422): Change the guard from `_topic_section_visited` to also check `_globally_visited`, so tasks already rendered as children in a prior section do not re-appear as root entries in their own section. *(completed)*
- [x] Add a comment block above the cross-topic gating logic explaining the rationale for future maintainers. *(completed)*
- [x] Fix Task 15's topic field in `specs/state.json`: change `"topic": "Project Management"` to `"topic": "Foundations"`. *(completed)*

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `.claude/scripts/generate-task-order.sh` - Patch `_print_topic_node` successor loop and `generate_grouped_section` fallback loop
- `specs/state.json` - Change Task 15 topic from "Project Management" to "Foundations"

**Verification**:
- Run `bash .claude/scripts/generate-task-order.sh --print` and confirm:
  - Foundations section shows Task 20 with cross-reference annotations for Tasks 4, 21, 22 (not full subtrees)
  - Modal Logic section shows Tasks 16 and 21 rendered fully (not duplicated or "(see above)")
  - Temporal Logic section shows Tasks 22, 23 rendered fully
  - Bimodal Porting section shows Tasks 2-11 rendered fully
  - No task appears in more than one section as a fully-rendered entry

---

### Phase 2: Regenerate TODO.md and Validate [NOT STARTED]

**Goal**: Apply the fixed rendering to TODO.md and verify the output is correct.

**Tasks**:
- [ ] Run `bash .claude/scripts/generate-task-order.sh --update-todo specs/TODO.md specs/state.json` to regenerate the Task Order section in TODO.md
- [ ] Verify the updated Task Order section in TODO.md matches expected structure: each topic section contains only its own tasks, cross-topic dependencies shown as annotations
- [ ] Spot-check that the wave table still renders correctly (it should be unchanged since it uses a separate code path)

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `specs/TODO.md` - Regenerated Task Order section (automated by script)

**Verification**:
- `grep -c "see above" specs/TODO.md` should show minimal occurrences (only within-topic diamond deps)
- No Bimodal Porting tasks (2-11) appear under the Foundations heading
- No task appears as a root entry in a section after being rendered as a child in a prior section

## Testing & Validation

- [ ] Run `bash .claude/scripts/generate-task-order.sh --print` and inspect output for correct topic grouping
- [ ] Verify no task appears under a topic section it does not belong to
- [ ] Verify cross-topic successors show "(see {topic} section)" annotations instead of full subtree rendering
- [ ] Verify the wave table is unchanged (separate code path, no bugs identified)
- [ ] Verify TODO.md Task Order section is updated and well-formed

## Artifacts & Outputs

- `.claude/scripts/generate-task-order.sh` - Patched rendering logic
- `specs/state.json` - Task 15 topic field corrected
- `specs/TODO.md` - Regenerated Task Order section

## Rollback/Contingency

Both modified files are tracked in git. If the changes produce unexpected output:
1. `git checkout -- .claude/scripts/generate-task-order.sh` to revert the script
2. `git checkout -- specs/state.json` to revert the topic field change
3. `git checkout -- specs/TODO.md` to revert the Task Order section
