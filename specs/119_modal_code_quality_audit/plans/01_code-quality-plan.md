# Implementation Plan: Task #119

- **Task**: 119 - Modal Code Quality Audit
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Dependencies**: None
- **Research Inputs**: specs/119_modal_code_quality_audit/reports/01_team-research.md
- **Artifacts**: plans/01_code-quality-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Audit and improve the Cslib/Logics/Modal/ directory (33 Metalogic files, Instances.lean, Basic.lean, Cube.lean, Metalogic.lean -- ~7,450 lines total). The codebase is mathematically correct (zero sorry, zero spurious axioms) but carries structural debt: ~300-600 lines of duplicated proof boilerplate, 51 active linter warnings, misleading module headers, a namespace collision bug, and inconsistent naming/style. This plan addresses all high and medium priority findings from team research, plus selected low priority items, organized into 5 phases by dependency and risk level.

### Research Integration

Integrated findings from `01_team-research.md` (4-teammate synthesis):
- H1: h_cons duplication across 10 completeness files (highest-impact deduplication target)
- H2: Propositional case block duplicated across 13 soundness files
- H3: MCS.lean namespace collision (Modal.Modal.SetConsistent)
- H4: Cube.lean--Metalogic disconnect (no bridge theorems) -- deferred to separate task
- M1: 51 active linter warnings (unused variables, flexible simp, etc.)
- M2: Stale/misleading module headers in Completeness.lean and Soundness.lean
- M3: Relation.Serial vs lambda inconsistency -- deferred (requires design decision)
- M4: S5 asymmetry (no dedicated S5Soundness.lean)
- M5: Universe polymorphism constraint undocumented
- L1-L5: Various low-priority cosmetic and documentation items

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Eliminate duplicated proof boilerplate (h_cons blocks, propositional axiom cases)
- Fix all 51 linter warnings (unused variables, flexible simp, dead simp_wf, deprecated push_neg)
- Fix the MCS.lean namespace collision bug
- Update misleading module headers to reflect actual scope
- Create S5Soundness.lean for architectural symmetry
- Standardize section headers across soundness files
- Fix docstring placement in Metalogic.lean
- Add universe polymorphism documentation
- Verify build passes after each phase

**Non-Goals**:
- Bridge theorems connecting Cube.lean to Metalogic (H4 -- separate task, significant scope)
- Unifying axiom schemata via NormalModalBase (A2 -- risky refactor, do after this audit)
- Standardizing frame condition style across Metalogic (M3 -- requires design decision and broader refactor)
- Completing Cube.lean inclusion lattice (L4 -- separate task)
- Adding test coverage (L5 -- separate task)
- GL/Grz preparedness (A5 -- strategic, future work)
- Reducing Instances.lean ModusPonens/Necessitation boilerplate (L1 -- requires macros)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Extracting h_cons breaks downstream proofs | H | L | Extract as a new theorem, keep old code until verified; run lake build after |
| simp only replacement changes proof behavior | M | M | Use simp? to get exact lemma lists; verify each file builds after replacement |
| Namespace fix in MCS.lean breaks imports elsewhere | M | L | Grep for all uses of Modal.SetConsistent before changing; update all call sites |
| S5Soundness.lean extraction breaks existing imports | M | L | Keep re-export in Soundness.lean initially; verify no downstream breakage |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Quick Fixes -- Linter Warnings and Cosmetic Issues [COMPLETED]

**Goal**: Eliminate all 51 linter warnings and fix cosmetic issues that require no architectural changes. This is the lowest-risk, highest-confidence phase and establishes a clean baseline for subsequent refactoring.

**Tasks**:
- [x] Fix unused variable warnings in all soundness wrapper theorems: replace `fun ψ h_ax w => ...` with `fun _ h_ax w => ...` across ~10 sites in 8+ soundness files (BSoundness, K4Soundness, K5Soundness, K45Soundness, KB5Soundness, TBSoundness, D4Soundness, D5Soundness, D45Soundness, DBSoundness, KSoundness, TSoundness, DSoundness, S4Soundness)
- [x] Remove dead `simp_wf` calls in DeductionTheorem.lean (lines ~116 and ~183)
- [x] Replace `push_neg` with `push Not` in Basic.lean (line ~115)
- [x] Fix `show` tactic misuse sites in Basic.lean (~10 sites): replace with `unfold` or `simp only` as appropriate *(deviation: altered -- used `change` instead of `unfold`/`simp only` since `change` is the proper replacement for definitional unfolding)*
- [x] Fix docstring placement in Metalogic.lean: move `/-! ... -/` block to before imports or immediately precede `@[expose] public section` per codebase convention *(deviation: skipped -- docstring already in correct position before `@[expose]`)*
- [x] Standardize section headers in soundness files: pick canonical form ("Soundness Wrappers" or "Soundness Theorems") and apply consistently across all 13+ soundness files
- [x] Update Completeness.lean module header: change "S5 Modal Logic" to accurately describe scope (parameterized canonical model infrastructure for all normal modal logics)
- [x] Update Soundness.lean module header: change "S5 Axiom Soundness" to accurately describe scope (parameterized soundness infrastructure for all normal modal logics)
- [x] Add universe polymorphism comment in Completeness.lean noting the `universe u` constraint (worlds and atoms at same universe)
- [x] Run `lake build Cslib.Logics.Modal.Metalogic` to verify zero warnings *(deviation: altered -- remaining warnings are flexible simp (Phase 2) and MCS namespace (Phase 2), which are expected at this stage)*

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` -- remove simp_wf
- `Cslib/Logics/Modal/Basic.lean` -- push_neg fix, show tactic fixes
- `Cslib/Logics/Modal/Metalogic.lean` -- docstring placement
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- header update, universe comment
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` -- header update
- All 13+ `*Soundness.lean` files -- unused variable fixes, section header standardization

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic` produces zero warnings
- `grep -rn "fun ψ h_ax" Cslib/Logics/Modal/Metalogic/` returns no matches
- `grep -rn "simp_wf" Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` returns no matches
- `grep -rn "push_neg" Cslib/Logics/Modal/Basic.lean` returns no matches

---

### Phase 2: Fix Flexible simp and MCS Namespace [COMPLETED]

**Goal**: Convert all flexible `simp` calls to `simp only [...]` using `simp?` output, and fix the MCS.lean namespace collision. These changes are isolated and testable per-file.

**Tasks**:
- [x] In DeductionTheorem.lean: use `simp?` at each flexible `simp` site, replace with `simp only [...]`
- [x] In MCS.lean: use `simp?` at each flexible `simp` site, replace with `simp only [...]`
- [x] In MCS.lean: fix namespace collision -- move `Modal.SetConsistent` and `Modal.SetMaximalConsistent` abbrevs out of `namespace Cslib.Logic.Modal` (declare in `namespace Cslib.Logic` instead, or drop `Modal.` prefix from abbrev name) *(deviation: altered -- dropped `Modal.` prefix from abbrev names instead of moving to different namespace; updated all call sites across 20+ files)*
- [x] Grep for all references to `Modal.SetConsistent` and `Modal.SetMaximalConsistent` across the codebase; update any affected call sites
- [x] In Completeness.lean: use `simp?` at each flexible `simp` site, replace with `simp only [...]`
- [x] In remaining completeness files with flexible simp (KCompleteness, TCompleteness, DCompleteness, S4Completeness, K4Completeness, D45Completeness): use `simp?` and replace *(deviation: altered -- also fixed all 15 other completeness files that had the same `simp at this` pattern)*
- [x] Run `lake build Cslib.Logics.Modal.Metalogic` to verify zero warnings from simp and namespace

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` -- simp only conversion
- `Cslib/Logics/Modal/Metalogic/MCS.lean` -- simp only + namespace fix
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- simp only conversion
- `Cslib/Logics/Modal/Metalogic/KCompleteness.lean` -- simp only conversion
- `Cslib/Logics/Modal/Metalogic/TCompleteness.lean` -- simp only conversion
- `Cslib/Logics/Modal/Metalogic/DCompleteness.lean` -- simp only conversion
- `Cslib/Logics/Modal/Metalogic/S4Completeness.lean` -- simp only conversion
- `Cslib/Logics/Modal/Metalogic/K4Completeness.lean` -- simp only conversion
- `Cslib/Logics/Modal/Metalogic/D45Completeness.lean` -- simp only conversion
- Any files referencing `Modal.SetConsistent` or `Modal.SetMaximalConsistent`

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic` produces zero flexible simp warnings
- `grep -rn "Modal.Modal." Cslib/Logics/Modal/` returns no matches (namespace collision gone)
- All completeness theorems still type-check

---

### Phase 3: Extract neg_consistent_of_not_derivable (H1 Deduplication) [COMPLETED]

**Goal**: Extract the duplicated ~30-line `h_cons` block into a shared lemma `neg_consistent_of_not_derivable` in Completeness.lean, then replace all 10 copy-pasted instances with a single call. This is the highest-impact deduplication, eliminating 300-600 lines.

**Tasks**:
- [x] Study the h_cons block in KCompleteness.lean to identify exact proof text and hypotheses needed
- [x] Compare h_cons blocks across BCompleteness, K4Completeness, K5Completeness, K45Completeness, TBCompleteness, D4Completeness, D5Completeness, D45Completeness, DBCompleteness to confirm they are identical (modulo naming)
- [x] Create `neg_consistent_of_not_derivable` theorem in Completeness.lean, parameterized over axiom predicate with hypotheses for implyK, implyS, efq, peirce (modal K should already be available via the axiom predicate)
- [x] Replace h_cons block in KCompleteness.lean with call to `neg_consistent_of_not_derivable`; verify builds
- [x] Replace h_cons block in all 9 remaining completeness files (BCompleteness, K4Completeness, K5Completeness, K45Completeness, TBCompleteness, D4Completeness, D5Completeness, D45Completeness, DBCompleteness) *(deviation: altered -- also replaced h_cons in S5 Completeness.lean, TCompleteness, DCompleteness, S4Completeness, KB5Completeness -- 15 files total)*
- [x] Run `lake build Cslib.Logics.Modal.Metalogic` to verify all completeness theorems pass

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- add shared lemma
- `Cslib/Logics/Modal/Metalogic/KCompleteness.lean` -- replace h_cons block
- `Cslib/Logics/Modal/Metalogic/BCompleteness.lean` -- replace h_cons block
- `Cslib/Logics/Modal/Metalogic/K4Completeness.lean` -- replace h_cons block
- `Cslib/Logics/Modal/Metalogic/K5Completeness.lean` -- replace h_cons block
- `Cslib/Logics/Modal/Metalogic/K45Completeness.lean` -- replace h_cons block
- `Cslib/Logics/Modal/Metalogic/TBCompleteness.lean` -- replace h_cons block
- `Cslib/Logics/Modal/Metalogic/D4Completeness.lean` -- replace h_cons block
- `Cslib/Logics/Modal/Metalogic/D5Completeness.lean` -- replace h_cons block
- `Cslib/Logics/Modal/Metalogic/D45Completeness.lean` -- replace h_cons block
- `Cslib/Logics/Modal/Metalogic/DBCompleteness.lean` -- replace h_cons block

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic` passes with zero errors
- `grep -c "h_cons" Cslib/Logics/Modal/Metalogic/*Completeness.lean` shows reduced count (only single-line references remain, not 30-line blocks)
- Each completeness theorem still type-checks with correct types

---

### Phase 4: Extract Shared Soundness Cases and Create S5Soundness.lean [NOT STARTED]

**Goal**: Extract the 5 shared propositional axiom cases into a helper lemma for soundness, and create a dedicated S5Soundness.lean for architectural symmetry. This addresses H2 and M4.

**Tasks**:
- [ ] Study the propositional case block in KSoundness.lean: identify the 5 shared cases (implyK, implyS, efq, peirce, modalK) and their exact proof structure
- [ ] Create `shared_axiom_sound` (or similar) in Soundness.lean that proves validity for any axiom satisfying the 5 base predicates, parameterized over the model
- [ ] Update KSoundness.lean to delegate 5 shared cases to the helper; verify builds
- [ ] Update all remaining 12 soundness files to delegate shared cases
- [ ] Create S5Soundness.lean: move `s5_soundness` and `s5_soundness_derivable` from Soundness.lean into the new file
- [ ] Update Soundness.lean to be purely parameterized infrastructure (remove S5-specific wrappers)
- [ ] Update Metalogic.lean imports: add `public import Cslib.Logics.Modal.Metalogic.S5Soundness`
- [ ] Create S5Completeness.lean: move S5-specific `completeness` and `completeness_derivable` from Completeness.lean into a dedicated file (parallel to S5Soundness.lean)
- [ ] Update Completeness.lean to be purely parameterized infrastructure
- [ ] Update Metalogic.lean imports: add `public import Cslib.Logics.Modal.Metalogic.S5Completeness`
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic` to verify everything passes

**Timing**: 2 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` -- add shared helper, remove S5 wrappers
- `Cslib/Logics/Modal/Metalogic/S5Soundness.lean` -- new file
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- remove S5 wrappers
- `Cslib/Logics/Modal/Metalogic/S5Completeness.lean` -- new file
- `Cslib/Logics/Modal/Metalogic.lean` -- add S5Soundness and S5Completeness imports
- All 13 `*Soundness.lean` files -- delegate shared cases to helper

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic` passes with zero errors
- `ls Cslib/Logics/Modal/Metalogic/S5Soundness.lean Cslib/Logics/Modal/Metalogic/S5Completeness.lean` confirms new files exist
- Soundness.lean and Completeness.lean contain only parameterized infrastructure (no S5-specific wrappers)

---

### Phase 5: Final Verification and Documentation [NOT STARTED]

**Goal**: Full project build verification, add centralized documentation for the truth lemma families and canonical model architecture, and confirm all research findings have been addressed.

**Tasks**:
- [ ] Run full `lake build` to verify entire project passes
- [ ] Add a documentation section in Completeness.lean (or a new `Metalogic/README.md` comment block) explaining the three truth lemma families (truth_lemma for T-based, k_truth_lemma for K-based, truth_lemma_d for D-based) and which logics use which
- [ ] Document the canonical model reuse pattern: all logics share the same canonical model definition, differing only in which frame properties are proved
- [ ] Verify zero sorry: `grep -rn "sorry" Cslib/Logics/Modal/` returns nothing
- [ ] Verify zero linter warnings: `lake build Cslib.Logics.Modal.Metalogic` is clean
- [ ] Review Metalogic.lean import ordering: confirm imports follow a consistent convention (infrastructure first, then alphabetical by logic name, then Instances)
- [ ] Verify line count reduction: compare total lines before and after audit

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- add truth lemma documentation
- `Cslib/Logics/Modal/Metalogic.lean` -- verify/fix import ordering if needed

**Verification**:
- `lake build` passes with zero errors across entire project
- `grep -rn "sorry" Cslib/Logics/Modal/` returns empty
- `lake build Cslib.Logics.Modal.Metalogic` produces zero warnings
- All findings from research report marked as addressed or explicitly deferred

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic` passes with zero errors after each phase
- [ ] `lake build` (full project) passes after Phase 5
- [ ] Zero `sorry` occurrences in Cslib/Logics/Modal/
- [ ] Zero linter warnings from modal metalogic build
- [ ] All 15 completeness theorems type-check correctly
- [ ] All 15 soundness theorems type-check correctly
- [ ] No regressions in downstream modules (Cube.lean, FromPropositional.lean)

## Artifacts & Outputs

- `specs/119_modal_code_quality_audit/plans/01_code-quality-plan.md` (this file)
- `specs/119_modal_code_quality_audit/summaries/01_code-quality-summary.md` (post-implementation)
- New files: `Cslib/Logics/Modal/Metalogic/S5Soundness.lean`, `Cslib/Logics/Modal/Metalogic/S5Completeness.lean`
- Modified files: ~35 files across Cslib/Logics/Modal/

## Rollback/Contingency

All changes are to existing Lean files in a git-tracked repository. If any phase introduces a build failure that cannot be resolved:
1. `git stash` or `git checkout -- Cslib/Logics/Modal/` to revert to pre-phase state
2. Mark the phase as [BLOCKED] with the specific error
3. Proceed to subsequent phases if they are independent

For Phase 3 (h_cons extraction) specifically: if the shared lemma signature does not unify cleanly with all 10 files, fall back to extracting it for the subset where it works and documenting the exceptions.

For Phase 4 (S5Soundness/S5Completeness extraction): if moving S5 wrappers causes import cycles, keep them in the original files and add a comment explaining the asymmetry.
