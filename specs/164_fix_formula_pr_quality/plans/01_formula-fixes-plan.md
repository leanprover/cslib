# Implementation Plan: Fix 7 PR Quality Issues in Formula.lean

- **Task**: 164 - Fix 7 PR quality issues in Formula.lean
- **Status**: [COMPLETED]
- **Effort**: 2.5 hours
- **Dependencies**: Branch pr3/temporal-formula must exist (based on pr1/foundations-logic)
- **Research Inputs**: specs/164_fix_formula_pr_quality/reports/01_formula-pr-review.md
- **Artifacts**: plans/01_formula-fixes-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Fix 7 issues identified during PR quality review of `Cslib/Logics/Temporal/Syntax/Formula.lean` on the `pr3/temporal-formula` branch. The highest-priority fix is a doc/code argument order mismatch for derived temporal operators (U/S) that would cause semantic bugs when semantics are added. Other fixes include adding missing references, an `iff` connective, Unicode temporal notation, Bot/Top instances, expanding the `@[expose] public section`, and removing a redundant `open`. After all fixes pass CI on the branch, merge into `main`.

### Research Integration

The research report (01_formula-pr-review.md) provides exact line numbers, comparison evidence from peer files (Propositional/Defs.lean, Modal/Basic.lean), and recommended fix approaches for all 7 issues. Option A (swap derived operator arguments to match docs and standard LTL conventions) is recommended for Issue 1.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Temporal Syntax infrastructure completed item in ROADMAP.md by improving the quality of `Logics/Temporal/Syntax/Formula.lean` to meet PR standards consistent with peer files.

## Goals & Non-Goals

**Goals**:
- Fix all 7 identified PR quality issues in Formula.lean
- Ensure all derived temporal operators match standard LTL argument order conventions
- Achieve consistency with peer files (Propositional/Defs.lean, Modal/Basic.lean)
- Pass full CI pipeline: lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake
- Merge fixed branch back to main

**Non-Goals**:
- Adding semantic evaluation (future sub-PRs)
- Refactoring the encoding/countability proofs
- Submitting a GitHub PR (explicitly deferred)
- Modifying any files outside Formula.lean

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Argument order swap breaks swapTemporal proofs | H | M | Proofs are structural (simp-based); re-check each after swap and fix if needed |
| Complexity pattern matches become incorrect after arg swap | H | H | Update all complexity patterns in same phase as arg swap |
| Unicode notation F/G/P/H conflicts with existing code | M | L | Use scoped notation; check for uses in downstream files |
| Bot/Top instances conflict with TemporalConnectives | M | L | Check for overlap; Propositional/Defs.lean already has both without conflict |
| Merge conflicts when merging pr3 into main | M | L | Branch is recent; resolve any conflicts manually |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Cosmetic and Structural Fixes (Issues 7, 6, 2, 5) [COMPLETED]

**Goal**: Apply the lower-risk, independent fixes first to establish a clean baseline.

**Tasks**:
- [ ] Checkout `pr3/temporal-formula` branch
- [ ] **Issue 7 (COSMETIC)**: Remove the redundant `open Cslib.Logic.Temporal` on line 111 (the `namespace` on line 113 already opens it)
- [ ] **Issue 6 (LOW)**: Wrap the second half of the file (after line 96, from `/-! ## Structural Properties...` onward) in an `@[expose] public section ... end` block so all definitions are publicly exported, matching the Propositional/Defs.lean pattern
- [ ] **Issue 2 (MEDIUM)**: Add a `## References` section to the module doc (after the `## Derived Temporal Operators` section, before `@[expose] public section`), citing Kamp 1968 and Gabbay-Pnueli-Shelah-Stavi 1980 in Mathlib BibTeX format
- [ ] **Issue 5 (LOW)**: Add `instance : Bot (Formula Atom) := ...` and `instance : Top (Formula Atom) := ...` inside the first `@[expose] public section` block, before `end Cslib.Logic.Temporal`
- [ ] Run `lake build` to verify no regressions

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Remove redundant open, add public section wrapper, add references, add Bot/Top instances

**Verification**:
- `lake build` succeeds
- The redundant `open` line is gone
- All definitions after line 96 are inside a public section
- Module doc includes `## References` with two citations
- `Bot` and `Top` instances exist for `Formula Atom`

---

### Phase 2: Argument Order Fix and Notation (Issues 1, 3, 4) [COMPLETED]

**Goal**: Fix the critical argument order mismatch, add the missing `iff` connective, and switch temporal notation from bare ASCII to Unicode.

**Tasks**:
- [ ] **Issue 1 (HIGH)**: Swap derived operator arguments to match docs and standard LTL:
  - `Formula.someFuture`: `.untl φ .top` to `.untl .top φ`
  - `Formula.somePast`: `.snce φ .top` to `.snce .top φ`
  - `Formula.next`: `.untl φ .bot` to `.untl .bot φ`
  - `Formula.prev`: `.snce φ .bot` to `.snce .bot φ`
  - `Formula.release`: `untl (neg ψ) (neg φ)` to `untl (neg φ) (neg ψ)`
  - `Formula.trigger`: `snce (neg ψ) (neg φ)` to `snce (neg φ) (neg ψ)`
  - `Formula.strongRelease`: `untl (and ψ φ) ψ` to `untl ψ (and ψ φ)`
  - `Formula.strongTrigger`: `snce (and ψ φ) ψ` to `snce ψ (and ψ φ)`
- [ ] Update `complexity` pattern matches to reflect swapped argument order:
  - F(phi): change `untl φ (.imp .bot .bot)` to `untl (.imp .bot .bot) φ`
  - P(phi): change `snce φ (.imp .bot .bot)` to `snce (.imp .bot .bot) φ`
  - next(phi): change `untl φ .bot` to `untl .bot φ`
  - prev(phi): change `snce φ .bot` to `snce .bot φ`
  - G(phi)/H(phi) patterns: swap within the neg-untl/neg-snce subpatterns
  - R/T patterns: swap within the neg-untl/neg-snce subpatterns
- [ ] Re-verify swapTemporal theorems compile after argument swap (proofs may need adjustment since simp unfolds abbrevs)
- [ ] **Issue 3 (LOW-MEDIUM)**: Add `Formula.iff` abbreviation and `@[inherit_doc] scoped infix:30 " ↔ " => Formula.iff` notation after `Formula.and`
- [ ] **Issue 4 (MEDIUM)**: Replace bare-letter notation with Unicode mathematical bold:
  - `"F"` to `"𝐅"`
  - `"G"` to `"𝐆"`
  - `"P"` to `"𝐏"`
  - `"H"` to `"𝐇"`
- [ ] Run `lake build` to verify all changes compile

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Swap arguments in 8 derived operators, update 10+ complexity patterns, add iff, change notation to Unicode

**Verification**:
- `lake build` succeeds
- All swapTemporal theorems still compile
- `Formula.iff` exists with correct definition
- Temporal notation uses Unicode bold letters
- Doc comments match code behavior for all derived operators

---

### Phase 3: CI Verification and Merge [COMPLETED]

**Goal**: Run the full CI pipeline, fix any remaining issues, and merge the branch into main.

**Tasks**:
- [ ] Run `lake build` (full build)
- [ ] Run `lake test` (CslibTests suite)
- [ ] Run `lake exe checkInitImports` (import verification)
- [ ] Run `lake exe lint-style` (style linting)
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (dependency analysis)
- [ ] Fix any CI failures
- [ ] Merge `pr3/temporal-formula` into `main` (resolving any conflicts)
- [ ] Verify `lake build` passes on `main` after merge

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Any CI-driven fixes
- Potential merge conflict resolution in other files

**Verification**:
- All 5 CI commands pass on pr3/temporal-formula before merge
- Merge into main succeeds
- `lake build` passes on main after merge
- Both branches exist and are in sync

## Testing & Validation

- [ ] `lake build` passes (no compilation errors)
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes (Cslib.Init imports)
- [ ] `lake exe lint-style` passes (style conformance)
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (clean dependencies)
- [ ] All 7 issues from the research report are addressed
- [ ] Doc comments for derived operators match code argument order
- [ ] `Formula.iff` is defined and has notation
- [ ] Temporal notation uses Unicode bold (no bare F/G/P/H)
- [ ] Bot/Top instances exist
- [ ] All definitions are within public sections
- [ ] Module doc includes References section

## Artifacts & Outputs

- `specs/164_fix_formula_pr_quality/plans/01_formula-fixes-plan.md` (this plan)
- `specs/164_fix_formula_pr_quality/summaries/01_formula-fixes-summary.md` (post-implementation)
- `Cslib/Logics/Temporal/Syntax/Formula.lean` (modified file)

## Rollback/Contingency

- Git revert: `git revert HEAD` on main to undo the merge commit
- Branch preservation: the `pr3/temporal-formula` branch is preserved; if issues arise post-merge, the branch can be reset to pre-fix state via `git reflog`
- Individual fixes are independent enough that any single fix can be reverted by reverting just the relevant Edit operations
