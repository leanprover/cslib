# Implementation Plan: Fix Propositional CI Check Failures

- **Task**: 122 - Fix all CONTRIBUTING.md CI check failures in propositional metalogic files
- **Status**: [COMPLETED]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: specs/122_fix_propositional_ci_checks/reports/01_fix-propositional-ci.md
- **Artifacts**: plans/01_fix-propositional-ci.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Fix four categories of CONTRIBUTING.md CI check failures across 14 propositional files: 8 `defsWithUnderscore` lint violations (rename snake_case defs/fields to lowerCamelCase), 1 `simpNF` violation (remove redundant `@[simp]`), 9 import fixes from `lake shake`, and 1 unused `DecidableEq` build warning. All fixes are code-level only -- no CI pipeline or linter configuration changes. Fixes are applied on `main` first, verified with the full CI suite, then cherry-picked to `pr1/foundations-logic`.

### Research Integration

Research report `01_fix-propositional-ci.md` provided complete rename maps with line numbers, call site inventories for all 8 underscore violations (~50 rename operations), detailed import change map for all 9 files, root cause analysis for the `simpNF` violation (abbrev transparency), and confirmation that propositional files are identical on both branches (zero diff), enabling clean cherry-pick.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the overall porting effort by ensuring propositional metalogic files pass the CSLib community CI checks (CONTRIBUTING.md standards). Clean CI is a prerequisite for merging the `pr1/foundations-logic` pull request.

## Goals & Non-Goals

**Goals**:
- Eliminate all 8 `defsWithUnderscore` lint violations in propositional files
- Fix the `simpNF` violation in Equivalence.lean
- Fix all 9 `lake shake` import issues
- Remove unused `DecidableEq` parameters from FromHilbert.lean
- Pass the full CI suite (`lake build`, `lake test`, `lake lint`, `lake exe lint-style`, `lake exe checkInitImports`, `lake exe mk_all --module`, `lake shake`) on `main`
- Propagate all fixes to `pr1/foundations-logic` and pass CI there

**Non-Goals**:
- Modifying CI pipeline configuration, linter settings, or `lakefile.lean`
- Renaming `theorem`/`lemma` declarations (not flagged by `defsWithUnderscore`)
- Renaming local parameter names (not flagged by the linter)
- Fixing issues outside the propositional directory

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Rename breaks proof that pattern-matches on field name | H | L | Run `lake build` after each rename group; revert if broken |
| `bot_forces` structure field rename cascades to unexpected consumers | H | M | Research confirmed no external references; verify with `lake build` after rename |
| Import change causes transitive dependency issues | M | M | Apply imports incrementally; `lake build` after each change |
| Cherry-pick to pr1 has merge conflicts | M | L | Research confirmed files are identical on both branches; fall back to manual apply if needed |
| BVDecide.Normalize import path incorrect | L | M | Verify with `lake shake --fix` output; adjust path as needed |
| Additional linter violations exposed after fixing these | L | L | Address only the 4 documented categories; note any new findings |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- |
| 2 | 5 | 1, 2, 3, 4 |
| 3 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Rename snake_case definitions to lowerCamelCase [COMPLETED]

**Goal**: Eliminate all 8 `defsWithUnderscore` lint violations by renaming definitions and their call sites.

**Tasks**:
- [ ] Rename `bot_forces` to `botForces` in `Kripke.lean` (structure field at line 63, docstring at line 62, `bf_upward_closed` field reference at line 67)
- [ ] Verify `lake build Cslib.Logics.Propositional.Semantics.Kripke` succeeds after `bot_forces` field rename
- [ ] Rename `int_canonical_val` to `intCanonicalVal` in `IntCompleteness.lean` (def at line 54, call sites at lines 60, 72, 111, 113, 114, docstring at line 66)
- [ ] Rename `int_neg_phi_imp_psi` to `intNegPhiImpPsi` in `IntLindenbaum.lean` (def at line 79, call site at line 99)
- [ ] Rename `int_deductive_closure` to `intDeductiveClosure` in `IntLindenbaum.lean` (def at line 203, call sites at lines 210, 218, 220, 226, 235, 259)
- [ ] Rename `min_canonical_val` to `minCanonicalVal` in `MinCompleteness.lean` (def at line 61, call sites at lines 67, 83, 90, 125, 127, 128)
- [ ] Rename `min_bot_forces` to `minBotForces` in `MinCompleteness.lean` (def at line 71, call sites at lines 77, 83, 90, 125, 127, 128, 130)
- [ ] Rename `min_deductive_closure` to `minDeductiveClosure` in `MinLindenbaum.lean` (def at line 186, call sites at lines 193, 200, 217)
- [ ] Rename `lift_min_to_cl` to `liftMinToCl` in `MinLindenbaum.lean` (def at line 233, recursive calls at lines 240, 242, call site at line 251)
- [ ] Run `lake build` on all affected modules to verify no breakage

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` - Rename `bot_forces` structure field to `botForces`
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` - Rename `int_canonical_val` to `intCanonicalVal`
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - Rename `int_neg_phi_imp_psi` and `int_deductive_closure`
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` - Rename `min_canonical_val` and `min_bot_forces`
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` - Rename `min_deductive_closure` and `lift_min_to_cl`

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Kripke` succeeds
- `lake build Cslib.Logics.Propositional.Metalogic.IntCompleteness` succeeds
- `lake build Cslib.Logics.Propositional.Metalogic.IntLindenbaum` succeeds
- `lake build Cslib.Logics.Propositional.Metalogic.MinCompleteness` succeeds
- `lake build Cslib.Logics.Propositional.Metalogic.MinLindenbaum` succeeds

---

### Phase 2: Fix simpNF violation [COMPLETED]

**Goal**: Remove the redundant `@[simp]` attribute from `mem_hilbertAxiomTheory` in Equivalence.lean.

**Tasks**:
- [ ] Remove `@[simp]` annotation (line 74) from `mem_hilbertAxiomTheory` in `Equivalence.lean`
- [ ] Verify `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` succeeds

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - Remove `@[simp]` from line 74

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` succeeds
- `lake lint Cslib.Logics.Propositional.NaturalDeduction.Equivalence` reports no `simpNF` violations

---

### Phase 3: Fix imports (lake shake issues) [COMPLETED]

**Goal**: Fix all 9 import issues identified by `lake shake`.

**Tasks**:
- [ ] In `Derivation.lean`: Replace `public import Cslib.Logics.Propositional.ProofSystem.Axioms` with `public import Cslib.Logics.Propositional.Defs`
- [ ] In `DeductionTheorem.lean`: Add `public import Cslib.Logics.Propositional.ProofSystem.Axioms`
- [ ] In `Soundness.lean`: Add `public import Cslib.Logics.Propositional.ProofSystem.Axioms`
- [ ] In `IntSoundness.lean`: Add `public import Cslib.Logics.Propositional.ProofSystem.Axioms`
- [ ] In `MinSoundness.lean`: Add `public import Cslib.Logics.Propositional.ProofSystem.Axioms`
- [ ] In `Instances.lean`: Add `public import Cslib.Logics.Propositional.ProofSystem.Axioms`
- [ ] In `IntMinInstances.lean`: Add `public import Cslib.Logics.Propositional.ProofSystem.Axioms`
- [ ] In `MinLindenbaum.lean`: Remove `public import Cslib.Logics.Propositional.Metalogic.MCS`
- [ ] In `DerivedRules.lean`: Add `public import Std.Tactic.BVDecide.Normalize` (verify exact path with `lake shake` output)
- [ ] Run `lake build` on all affected modules

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` - Replace Axioms import with Defs
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - Add Axioms import
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` - Add Axioms import
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` - Add Axioms import
- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` - Add Axioms import
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` - Add Axioms import
- `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` - Add Axioms import
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` - Remove MCS import
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` - Add BVDecide.Normalize import

**Verification**:
- `lake build` succeeds for all modified modules
- `lake shake --add-public --keep-implied --keep-prefix` reports no propositional issues

---

### Phase 4: Remove unused DecidableEq from FromHilbert.lean [COMPLETED]

**Goal**: Remove the unused `[DecidableEq Atom']` type class parameter from both `hilbertSubstitution` and `hilbertSubstitutionDeriv`.

**Tasks**:
- [ ] Remove `[DecidableEq Atom']` from `hilbertSubstitution` signature (line 269)
- [ ] Remove `[DecidableEq Atom']` from `hilbertSubstitutionDeriv` signature (line 291)
- [ ] Verify `lake build Cslib.Logics.Propositional.NaturalDeduction.FromHilbert` succeeds

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` - Remove `[DecidableEq Atom']` from lines 269 and 291

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.FromHilbert` succeeds with no warnings about unused variables

---

### Phase 5: Full CI verification on main [COMPLETED]

**Goal**: Run the complete CI check suite on `main` to confirm all 4 issue categories are resolved and no regressions introduced.

**Tasks**:
- [ ] Run `lake build` (full project build, no warnings)
- [ ] Run `lake test` (all tests pass)
- [ ] Run `lake lint` (no `defsWithUnderscore` or `simpNF` violations in propositional files)
- [ ] Run `lake exe lint-style` (style lint passes)
- [ ] Run `lake exe checkInitImports` (init imports correct)
- [ ] Run `lake exe mk_all --module` (module list up to date)
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (no unnecessary imports)
- [ ] If any check fails, fix the issue and re-run the failing check
- [ ] Commit all fixes on `main`

**Timing**: 45 minutes

**Depends on**: 1, 2, 3, 4

**Files to modify**:
- No new files; this phase validates prior phases and commits

**Verification**:
- All 7 CI commands exit with status 0
- No propositional files appear in any lint/shake output

---

### Phase 6: Propagate fixes to pr1/foundations-logic [COMPLETED]

**Goal**: Apply all fixes to `pr1/foundations-logic` branch and verify CI passes there.

**Tasks**:
- [ ] Cherry-pick the fix commit(s) from `main` to `pr1/foundations-logic`
- [ ] If cherry-pick fails (unlikely per research), manually apply the same edits
- [ ] Run `lake build` on `pr1/foundations-logic`
- [ ] Run `lake lint` on `pr1/foundations-logic`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` on `pr1/foundations-logic`
- [ ] Run remaining CI checks (`lake test`, `lake exe lint-style`, `lake exe checkInitImports`, `lake exe mk_all --module`)
- [ ] If any check fails, diagnose and fix (pr1 has additional files that may introduce new issues)
- [ ] Commit and verify on `pr1/foundations-logic`

**Timing**: 45 minutes

**Depends on**: 5

**Files to modify**:
- Same 14 files as phases 1-4, applied via cherry-pick on `pr1/foundations-logic`

**Verification**:
- Cherry-pick applies cleanly
- All 7 CI commands pass on `pr1/foundations-logic`
- `git diff main..pr1/foundations-logic -- Cslib/Logics/Propositional/` shows only pr1-specific additions, not divergent fixes

## Testing & Validation

- [ ] `lake build` passes with no warnings on `main`
- [ ] `lake build` passes with no warnings on `pr1/foundations-logic`
- [ ] `lake lint` reports zero `defsWithUnderscore` violations in propositional files on both branches
- [ ] `lake lint` reports zero `simpNF` violations in propositional files on both branches
- [ ] `lake shake` reports no propositional import issues on both branches
- [ ] `lake test` passes on both branches
- [ ] `lake exe lint-style` passes on both branches
- [ ] No CI pipeline files (`.github/workflows/`, `lakefile.lean`, `lean-toolchain`) were modified

## Artifacts & Outputs

- `specs/122_fix_propositional_ci_checks/reports/01_fix-propositional-ci.md` - Research report (input)
- `specs/122_fix_propositional_ci_checks/plans/01_fix-propositional-ci.md` - This plan
- `specs/122_fix_propositional_ci_checks/summaries/01_fix-propositional-ci-summary.md` - Implementation summary (output)
- Git commit(s) on `main` with all fixes
- Cherry-pick commit(s) on `pr1/foundations-logic`

## Rollback/Contingency

- Each phase modifies independent files (phases 1-4), so partial rollback is possible via `git checkout -- <file>` for individual files
- If `lake build` fails after a rename, revert just that rename group and investigate
- If cherry-pick to pr1 fails, manually apply edits by reading the diff from the main commit
- If new lint violations are discovered after fixing these, document them as a follow-up task rather than blocking this task
- Full rollback: `git revert <commit>` on either branch to undo all changes atomically
