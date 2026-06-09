# Implementation Plan: Port Temporal Syntax (PR 1)

- **Task**: 2 - Port Temporal Syntax (PR 1): Atom, Formula, Context, BigConj, Subformulas
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: BimodalLogic:291 (toolchain upgrade)
- **Research Inputs**: specs/002_port_bimodal_syntax_infrastructure/reports/01_syntax-port-research.md
- **Artifacts**: plans/01_syntax-port-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Port the temporal syntax infrastructure from BimodalLogic to `Cslib/Logics/Temporal/Syntax/`. The existing `Formula.lean` (94 lines) already defines the 5-constructor `Formula` inductive, derived operators, notation, and `TemporalConnectives` instance. This plan extends that file with structural properties (complexity, BEq proofs, swap_temporal, atoms) and creates three new files (Context.lean, BigConj.lean, Subformulas.lean). All content is adapted from BimodalLogic's 6-constructor formula by stripping the `box` constructor and parameterizing over a generic `Atom` type.

### Research Integration

Key findings from the research report integrated into this plan:
- Atom.lean is NOT ported: cslib's `Formula` is already parameterized over generic `Atom : Type u`
- Formula.lean is EXTENDED (appended to), not replaced: 94-line existing file has downstream dependents
- All `box` cases removed: BimodalLogic has 6 constructors, cslib temporal has 5
- `modalDepth` and `predFormulas` are skipped (box-dependent)
- `diamond` is skipped (box-dependent)
- All Mathlib APIs confirmed available in cslib's Mathlib revision
- Namespace convention: file path uses `Logics` (plural), namespace uses `Logic` (singular)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following ROADMAP.md items:
- Phase 4 Task 2: "Bimodal Syntax (Context, BigConj, Subformulas)" (~2,500 lines)
- This is the foundational PR on which all subsequent bimodal porting PRs depend

## Goals & Non-Goals

**Goals**:
- Extend `Cslib/Logics/Temporal/Syntax/Formula.lean` with Countable/Infinite/Denumerable instances, complexity, BEq proofs, swap_temporal, derived operators, atoms function
- Create `Cslib/Logics/Temporal/Syntax/Context.lean` with parameterized Context type and operations
- Create `Cslib/Logics/Temporal/Syntax/BigConj.lean` with finite conjunction folding
- Create `Cslib/Logics/Temporal/Syntax/Subformulas.lean` with subformula closure and membership lemmas
- Register all new modules in `Cslib.lean`
- Pass `lake build` with zero errors and zero sorry

**Non-Goals**:
- Port Atom.lean (cslib uses generic Atom type parameter)
- Port SubformulaClosure/ directory (separate from Subformulas, belongs to decidability)
- Port modalDepth, predFormulas, diamond (box-dependent content)
- Add typeclass constraints (Countable, Infinite) to Atom -- defer to downstream tasks that need them

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| complexity pattern matching differs without box | M | M | Test each pattern; BimodalLogic has working patterns to adapt |
| BEq proof structure changes with 5 vs 6 constructors | L | L | Simpler without box; straightforward deletion of box cases |
| Lean 4.31 tactic behavior differs from 4.27 | M | L | Use lean_goal and lean_multi_attempt to test; fall back to term-mode |
| Existing Formula.lean downstream dependents break | H | L | Append-only changes; do not modify existing 94 lines |
| Countable deriving may not work on parameterized Formula | M | M | If deriving fails, provide manual instance via atom injection |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Extend Formula.lean [COMPLETED]

**Goal**: Add structural properties, derived operators, and utility functions to the existing Formula.lean

**Tasks**:
- [x] Add `Countable`, `Infinite`, `Denumerable` instances for `Formula Atom` *(completed — via Nat.pair encoding injection)*
- [x] Add `Formula.atom_injective` theorem *(completed)*
- [x] Add BEq helper theorems (`beq_imp_eq`, `beq_untl_eq`, `beq_snce_eq`) *(completed)*
- [x] Add `Formula.beq_refl` and `Formula.eq_of_beq` theorems (5 cases, no box) *(completed)*
- [x] Add `ReflBEq Formula` and `LawfulBEq Formula` instances *(completed)*
- [x] Add `Formula.complexity` function *(deviation: altered — complexity patterns adapted for cslib abbrev conventions; always/sometimes/weak_future/weak_past/strong_release/strong_trigger/diamond special patterns omitted since deeply nested abbrev expansions make them fragile; G/H/F/P/next/prev/release/trigger patterns preserved)*
- [x] Add `Formula.temporalDepth` function (5 cases, no box) *(completed)*
- [x] Add `Formula.countImplications` function (5 cases, no box) *(completed)*
- [x] Add derived temporal operators: `always`, `sometimes`, `next`, `prev`, `weak_future`, `weak_past`, `release`, `trigger`, `weak_until`, `weak_since`, `strong_release`, `strong_trigger` *(completed)*
- [x] Add notation for `always` and `sometimes` operators *(completed)*
- [x] Add `Formula.swap_temporal` function and all swap theorems *(completed)*
- [x] Add `Formula.needsPositiveHypotheses` function and simp lemmas (5 cases, no box) *(completed)*
- [x] Add `Formula.atoms` function (5 cases, no box) and `atoms_swap_temporal` theorem *(completed)*
- [x] Verify `lake build Cslib.Logics.Temporal.Syntax.Formula` passes *(completed)*

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Append ~450 lines of new definitions and theorems

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax.Formula` passes with zero errors
- `grep -c sorry Cslib/Logics/Temporal/Syntax/Formula.lean` returns 0
- Existing 94 lines are unmodified (downstream dependents preserved)

---

### Phase 2: Create Context.lean [NOT STARTED]

**Goal**: Create parameterized Context type with operations and theorems

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Syntax/Context.lean` with Apache 2.0 header
- [ ] Add `module` declaration and `public import Cslib.Logics.Temporal.Syntax.Formula`
- [ ] Define `abbrev Context (Atom : Type u) := List (Formula Atom)` in `Cslib.Logic.Temporal` namespace
- [ ] Port `Context.map`, `Context.isEmpty`, `Context.singleton` (parameterized over Atom)
- [ ] Port `map_length`, `map_comp`, `map_id`, `map_nil`, `map_cons`, `map_append` theorems
- [ ] Port `mem_map_iff`, `mem_map_of_mem`, `not_mem_nil`, `mem_singleton_iff` membership theorems
- [ ] Port `isEmpty_iff_eq_nil`, `exists_mem_of_ne_nil` theorems
- [ ] Verify `lake build Cslib.Logics.Temporal.Syntax.Context` passes

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Context.lean` - Create new file (~190 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax.Context` passes with zero errors
- `grep -c sorry Cslib/Logics/Temporal/Syntax/Context.lean` returns 0

---

### Phase 3: Create BigConj.lean [NOT STARTED]

**Goal**: Create finite conjunction folding function with simp lemmas

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Syntax/BigConj.lean` with Apache 2.0 header
- [ ] Add `module` declaration and `public import Cslib.Logics.Temporal.Syntax.Formula`
- [ ] Define `bigconj : List (Formula Atom) -> Formula Atom` (parameterized)
- [ ] Define `neg_bigconj` derived function
- [ ] Add `@[simp]` lemmas: `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`, `neg_bigconj_def`
- [ ] Verify `lake build Cslib.Logics.Temporal.Syntax.BigConj` passes

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/BigConj.lean` - Create new file (~50 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax.BigConj` passes with zero errors
- `grep -c sorry Cslib/Logics/Temporal/Syntax/BigConj.lean` returns 0

---

### Phase 4: Create Subformulas.lean [NOT STARTED]

**Goal**: Create subformula closure function with membership and transitivity lemmas

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Syntax/Subformulas.lean` with Apache 2.0 header
- [ ] Add `module` declaration and `public import Cslib.Logics.Temporal.Syntax.Formula`
- [ ] Define `Formula.subformulas : Formula Atom -> List (Formula Atom)` (5 cases, no box)
- [ ] Define `Formula.subformulaCount` using `eraseDups.length`
- [ ] Port `self_mem_subformulas` theorem
- [ ] Port per-constructor membership: `imp_left_mem_subformulas`, `imp_right_mem_subformulas`, `all_past_inner_mem_subformulas`, `all_future_inner_mem_subformulas`, `untl_left_mem_subformulas`, `untl_right_mem_subformulas`, `snce_left_mem_subformulas`, `snce_right_mem_subformulas`
- [ ] Port `subformulas_trans` (transitivity, 5-case induction, no box case)
- [ ] Port direct membership lemmas: `mem_subformulas_of_imp_left`, `_imp_right`, `_all_past`, `_all_future`, `_untl_left`, `_untl_right`, `_snce_left`, `_snce_right`
- [ ] Skip `mem_subformulas_of_box` and `box_inner_mem_subformulas` (box-dependent)
- [ ] Verify `lake build Cslib.Logics.Temporal.Syntax.Subformulas` passes

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Subformulas.lean` - Create new file (~200 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax.Subformulas` passes with zero errors
- `grep -c sorry Cslib/Logics/Temporal/Syntax/Subformulas.lean` returns 0

---

### Phase 5: Integration and Verification [NOT STARTED]

**Goal**: Register new modules and verify full build

**Tasks**:
- [ ] Add `public import Cslib.Logics.Temporal.Syntax.Context` to `Cslib.lean`
- [ ] Add `public import Cslib.Logics.Temporal.Syntax.BigConj` to `Cslib.lean`
- [ ] Add `public import Cslib.Logics.Temporal.Syntax.Subformulas` to `Cslib.lean`
- [ ] Run `lake build` to verify full project compiles
- [ ] Run `lake env lean --run Cslib/Logics/Temporal/Syntax/Formula.lean` or equivalent to confirm no issues
- [ ] Verify `grep -r sorry Cslib/Logics/Temporal/Syntax/` returns nothing
- [ ] Verify existing `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` still compiles (imports Formula.lean)

**Timing**: 30 minutes

**Depends on**: 1, 2, 3, 4

**Files to modify**:
- `Cslib.lean` - Add 3 new import lines

**Verification**:
- `lake build` passes with zero errors (full project)
- `grep -r sorry Cslib/Logics/Temporal/Syntax/` returns no results
- All 4 temporal syntax files compile independently

## Testing & Validation

- [ ] `lake build Cslib.Logics.Temporal.Syntax.Formula` -- extended file compiles
- [ ] `lake build Cslib.Logics.Temporal.Syntax.Context` -- new file compiles
- [ ] `lake build Cslib.Logics.Temporal.Syntax.BigConj` -- new file compiles
- [ ] `lake build Cslib.Logics.Temporal.Syntax.Subformulas` -- new file compiles
- [ ] `lake build` -- full project compiles with zero errors
- [ ] `grep -r sorry Cslib/Logics/Temporal/Syntax/` -- zero sorry occurrences
- [ ] `TemporalEmbedding.lean` continues to compile (existing downstream dependent)
- [ ] Existing Formula.lean API preserved (first 94 lines unchanged)

## Artifacts & Outputs

- `Cslib/Logics/Temporal/Syntax/Formula.lean` -- Extended with ~450 lines
- `Cslib/Logics/Temporal/Syntax/Context.lean` -- New file (~190 lines)
- `Cslib/Logics/Temporal/Syntax/BigConj.lean` -- New file (~50 lines)
- `Cslib/Logics/Temporal/Syntax/Subformulas.lean` -- New file (~200 lines)
- `Cslib.lean` -- 3 new import lines added
- `specs/002_port_bimodal_syntax_infrastructure/plans/01_syntax-port-plan.md` -- This plan

## Rollback/Contingency

If the implementation fails:
1. Revert Formula.lean to its original 94 lines (the appended content is the only modification)
2. Delete newly created files: Context.lean, BigConj.lean, Subformulas.lean
3. Remove the 3 added import lines from Cslib.lean
4. All changes are additive, so `git checkout -- Cslib/Logics/Temporal/Syntax/Formula.lean Cslib.lean` plus deletion of new files restores the original state
