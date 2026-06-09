# Implementation Plan: Port Frame Semantics to Cslib Bimodal

- **Task**: 3 - Port Frame Semantics (PR 2): TaskFrame, WorldHistory, TaskModel, Truth, Validity to Cslib/Logics/Bimodal/Semantics/
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: Task 2 (Bimodal Syntax, already completed)
- **Research Inputs**: specs/003_port_task_frame_semantics_bimodal/reports/01_frame-semantics-research.md
- **Artifacts**: plans/01_frame-semantics-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Port 5 source files (~1,822 lines) from BimodalLogic/Theories/Bimodal/Semantics/ to Cslib/Logics/Bimodal/Semantics/, plus create a new Context.lean file (~30 lines). The primary transformation is adapting from the source's concrete `Atom` type to cslib's polymorphic `Formula Atom` pattern. All Mathlib dependencies are already available. The dependency chain is strictly linear: TaskFrame -> WorldHistory -> TaskModel -> Truth -> Validity, allowing sequential porting in that order.

### Research Integration

Research report (01_frame-semantics-research.md) findings integrated:
- Atom parametrization is the critical transformation: thread `{Atom : Type*}` through TaskModel, Truth, and Validity
- TaskFrame and WorldHistory have no Formula/Atom dependency -- minimal changes needed (namespace, header, `module` declaration)
- `from_list` helper in TaskModel should be dropped (depends on source's concrete `Atom.base`/`Atom.fresh_index` fields)
- `strong_release_iff` and `strong_trigger_iff` in Truth.lean should be dropped (cslib Bimodal Formula lacks these derived connectives)
- Context.lean must be created before Validity.lean (follows Temporal Context pattern)
- All Mathlib dependencies verified available in cslib

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation required for this plan.

## Goals & Non-Goals

**Goals**:
- Port all 5 source semantics files to cslib with proper Atom parametrization
- Create Bimodal Context.lean mirroring the Temporal Context pattern
- Maintain all theorems and proofs from the source (except noted exclusions)
- Follow cslib conventions: copyright header, `module` declaration, `@[expose] public section`, namespace `Cslib.Logic.Bimodal`
- Ensure `lake build` passes after each phase

**Non-Goals**:
- Port `strong_release`/`strong_trigger` derived connectives to Bimodal Formula.lean (can be added later)
- Port the `from_list` convenience constructor (concrete Atom-dependent)
- Create Semantics root import file (can be done as a follow-up)
- Port metalogic/soundness files (separate task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Atom parametrization causes universe issues in Validity.lean | Medium | Low | Follow source pattern: use `Type` (not `Type*`) for D in `valid`/`semantic_consequence` |
| Proof terms break due to namespace changes | Low | Medium | Incremental port with `lake build` verification after each file |
| `truth_at` recursion with polymorphic Atom | Low | Low | Pattern matching on inductive constructors is structurally identical |
| Missing `strong_release`/`strong_trigger` causes downstream issues | Low | Low | Only used by 2 simp lemmas in Truth.lean, not by core definitions |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Port TaskFrame.lean [COMPLETED]

**Goal**: Port the core frame structure with no Formula/Atom dependency. This is the foundation file that all other semantics files depend on.

**Tasks**:
- [ ] Create directory `Cslib/Logics/Bimodal/Semantics/`
- [ ] Create `Cslib/Logics/Bimodal/Semantics/TaskFrame.lean` with cslib conventions:
  - Apache 2.0 copyright header
  - `module` declaration
  - `@[expose] public section` wrapping
  - Namespace `Cslib.Logic.Bimodal`
- [ ] Port `structure TaskFrame (D : Type*)` with all 3 axioms (nullity_identity, forward_comp, converse)
- [ ] Port `TaskFrame.nullity` derived theorem
- [ ] Port `TaskFrame.backward_comp` derived theorem
- [ ] Port example frames: `trivial_frame`, `identity_frame`, `nat_frame`
- [ ] Port `structure FiniteTaskFrame` with `Coe` instance
- [ ] Update import: `Mathlib.Algebra.Order.Group.Defs` and `Mathlib.Data.Fintype.Basic`
- [ ] Verify with `lake build Cslib.Logics.Bimodal.Semantics.TaskFrame`

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Semantics/TaskFrame.lean` - create new file (~300 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Semantics.TaskFrame` succeeds with no errors or sorry

---

### Phase 2: Port WorldHistory.lean [COMPLETED]

**Goal**: Port world history structure with time-shift construction and all supporting lemmas. No Formula/Atom dependency.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Semantics/WorldHistory.lean` with cslib conventions
- [ ] Update import to `Cslib.Logics.Bimodal.Semantics.TaskFrame`
- [ ] Port `structure WorldHistory` with domain, convex, states, respects_task fields
- [ ] Port example histories: `universal`, `trivial`, `universal_trivialFrame`, `universal_natFrame`
- [ ] Port `state_at` helper
- [ ] Port `time_shift` construction with convexity and respects_task proofs
- [ ] Port time-shift lemmas: `time_shift_domain_iff`, `time_shift_inverse_domain`, `states_eq_of_time_eq`, `time_shift_time_shift_states`, `time_shift_congr`, `time_shift_zero_domain_iff`, `time_shift_time_shift_neg_domain_iff`, `time_shift_time_shift_neg_states`
- [ ] Port order reversal lemmas: `neg_lt_neg_iff`, `neg_le_neg_iff`, `neg_neg_eq`, `neg_injective`
- [ ] Verify with `lake build Cslib.Logics.Bimodal.Semantics.WorldHistory`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Semantics/WorldHistory.lean` - create new file (~410 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Semantics.WorldHistory` succeeds with no errors or sorry

---

### Phase 3: Port TaskModel.lean and create Context.lean [COMPLETED]

**Goal**: Port the model structure (frame + valuation) with Atom parametrization, and create the Bimodal Context type needed by Validity.lean.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Semantics/TaskModel.lean` with cslib conventions
- [ ] Update imports to `Cslib.Logics.Bimodal.Semantics.TaskFrame`, `Cslib.Logics.Bimodal.Semantics.WorldHistory`, `Cslib.Logics.Bimodal.Syntax.Formula`
- [ ] Parametrize `TaskModel` structure by `{Atom : Type*}`: `valuation : F.WorldState -> Atom -> Prop`
- [ ] Port `all_false` and `all_true` trivial models (parametrized by Atom)
- [ ] Drop `from_list` helper (depends on source's concrete `Atom.base`/`Atom.fresh_index`)
- [ ] Port `FiniteTaskModel` abbreviation (parametrized by Atom)
- [ ] Remove `open Bimodal.Syntax` -- use direct `Formula Atom` references
- [ ] Verify with `lake build Cslib.Logics.Bimodal.Semantics.TaskModel`
- [ ] Create `Cslib/Logics/Bimodal/Syntax/Context.lean` following Temporal Context pattern:
  - `abbrev Context (Atom : Type u) := List (Formula Atom)`
  - Port `Context.map`, `isEmpty`, `singleton` and supporting theorems
- [ ] Verify with `lake build Cslib.Logics.Bimodal.Syntax.Context`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Semantics/TaskModel.lean` - create new file (~80 lines)
- `Cslib/Logics/Bimodal/Syntax/Context.lean` - create new file (~120 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Semantics.TaskModel` succeeds
- `lake build Cslib.Logics.Bimodal.Syntax.Context` succeeds

---

### Phase 4: Port Truth.lean [COMPLETED]

**Goal**: Port truth evaluation (the core semantic definition) with Atom parametrization. This is the largest and most complex file.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Semantics/Truth.lean` with cslib conventions
- [ ] Update imports to `Cslib.Logics.Bimodal.Semantics.TaskModel`, `Cslib.Logics.Bimodal.Semantics.WorldHistory`, `Cslib.Logics.Bimodal.Syntax.Formula`
- [ ] Port `def truth_at` with `{Atom : Type*}` parameter threading: recursive definition on 6 formula constructors (atom, bot, imp, box, untl, snce)
- [ ] Port Truth namespace lemmas with Atom parametrization:
  - `bot_false`, `imp_iff`, `atom_iff_of_domain`, `atom_false_of_not_domain`
  - `box_iff`, `some_future_iff`, `some_past_iff`, `future_iff`, `past_iff`
- [ ] Skip `strong_release_iff` and `strong_trigger_iff` (cslib Bimodal Formula lacks these derived connectives)
- [ ] Port `def ShiftClosed` with Atom parametrization
- [ ] Port `Set.univ_shift_closed` theorem
- [ ] Port TimeShift namespace:
  - `truth_history_eq`
  - `truth_double_shift_cancel` (~50 line inductive proof)
  - `time_shift_preserves_truth` (~250 line inductive proof -- the key theorem)
  - `exists_shifted_history` corollary
- [ ] Replace `open Bimodal.Syntax` with appropriate namespace handling
- [ ] Verify with `lake build Cslib.Logics.Bimodal.Semantics.Truth`

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Semantics/Truth.lean` - create new file (~650 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Semantics.Truth` succeeds with no errors or sorry

---

### Phase 5: Port Validity.lean [COMPLETED]

**Goal**: Port validity, semantic consequence, satisfiability definitions and theorems. Complete the semantics module.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Semantics/Validity.lean` with cslib conventions
- [ ] Update imports to `Cslib.Logics.Bimodal.Semantics.Truth`, `Cslib.Logics.Bimodal.Syntax.Context`, `Mathlib.Order.SuccPred.Basic`, `Mathlib.Order.SuccPred.Archimedean`
- [ ] Port core definitions with Atom parametrization:
  - `def valid` -- quantify over `Atom : Type` and `Formula Atom`; preserve `D : Type` (not `Type*`)
  - `def semantic_consequence` -- uses `Context Atom` from new Context.lean
  - `def satisfiable`, `satisfiable_abs`, `formula_satisfiable`
  - `def valid_dense`, `valid_discrete` -- with DenselyOrdered / SuccOrder constraints
- [ ] Port notation: `⊨ φ` for validity, `Γ ⊨ φ` for semantic consequence
- [ ] Port Validity namespace theorems:
  - `valid_implies_valid_dense`, `valid_implies_valid_discrete`
  - `valid_iff_empty_consequence`, `consequence_monotone`, `valid_consequence`
  - `consequence_of_member`, `unsatisfiable_implies_all`, `unsatisfiable_implies_all_fixed`
  - `valid_of_valid_all_future`, `valid_of_valid_all_past`, `valid_of_valid_box`
- [ ] Replace `open Bimodal.Syntax` with appropriate opens
- [ ] Verify with `lake build Cslib.Logics.Bimodal.Semantics.Validity`
- [ ] Run final full verification: `lake build`

**Timing**: 1.25 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Semantics/Validity.lean` - create new file (~310 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Semantics.Validity` succeeds with no errors or sorry
- `lake build` full project succeeds

## Testing & Validation

- [ ] Each file compiles individually with scoped `lake build Module.Name`
- [ ] Full `lake build` passes after all phases complete
- [ ] No `sorry` in any ported file (verified via `lean_verify` or grep)
- [ ] All source theorems are present in target (except `strong_release_iff`, `strong_trigger_iff`, `from_list`)
- [ ] Namespace is consistently `Cslib.Logic.Bimodal` across all files
- [ ] All files have copyright header, `module` declaration, and `@[expose] public section`

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/Semantics/TaskFrame.lean` - Frame structure (~300 lines)
- `Cslib/Logics/Bimodal/Semantics/WorldHistory.lean` - World histories (~410 lines)
- `Cslib/Logics/Bimodal/Semantics/TaskModel.lean` - Models (~80 lines)
- `Cslib/Logics/Bimodal/Semantics/Truth.lean` - Truth evaluation (~650 lines)
- `Cslib/Logics/Bimodal/Semantics/Validity.lean` - Validity (~310 lines)
- `Cslib/Logics/Bimodal/Syntax/Context.lean` - Context type (~120 lines)

## Rollback/Contingency

All files are new creations (no modifications to existing cslib files). Rollback is straightforward:
- Delete `Cslib/Logics/Bimodal/Semantics/` directory
- Delete `Cslib/Logics/Bimodal/Syntax/Context.lean`
- No other files are modified by this task

If a specific proof fails to port (e.g., `time_shift_preserves_truth`), mark that theorem with `sorry` and flag the phase as [PARTIAL] with documentation of the blocker.
