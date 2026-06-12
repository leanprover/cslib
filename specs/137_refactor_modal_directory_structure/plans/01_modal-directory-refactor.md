# Implementation Plan: Refactor Modal/ Directory Structure

- **Task**: 137 - Refactor Modal/ directory structure for the modal cube
- **Status**: [IMPLEMENTING]
- **Effort**: 8 hours
- **Dependencies**: None
- **Research Inputs**: specs/137_refactor_modal_directory_structure/reports/01_directory-structure-research.md
- **Artifacts**: plans/01_modal-directory-refactor.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Reorganize `Cslib/Logics/Modal/` to make its architecture self-documenting while respecting the upstream/fork boundary. The monolithic `ProofSystem/Instances.lean` (1531 lines) is split into 15 per-system files. The flat `Metalogic/` directory (30 files) is reorganized into `Metalogic/Systems/{K,T,D,...}/` subdirectories. Additionally, `LogicalEquivalence.lean` is written from scratch for the fork's `Proposition` type (which uses `atom, bot, imp, box` as primitive constructors), defining a one-hole `Context` inductive and proving that logical equivalence is a congruence. Definition of done: `lake build` passes after each phase, and the final tree matches the proposed structure with full CI green.

### Research Integration

Key findings from the research report:
- 4 upstream files (Basic, Cube, Denotation, LogicalEquivalence -- last one missing from fork), 37 fork-only files
- `ProofSystem/Instances.lean` at 1531 lines is the primary maintenance burden
- All 28 system-specific Metalogic files import `Cslib.Logics.Modal.ProofSystem.Instances`
- Import graph is strictly hierarchical (no cycles) -- safe to restructure
- `Metalogic.lean` barrel file already aggregates all imports (simplifies migration)
- External consumers: only `Bimodal/Embedding/` imports `Modal/Basic.lean` and `Modal/FromPropositional.lean` (unaffected)

### Revision Notes (v2)

Phases 1-4 completed successfully. Phases 5-6 were blocked because upstream `LogicalEquivalence.lean` uses `Proposition.not` as a primitive constructor, while the fork uses `bot+imp` primitives with `neg` defined as `.imp phi .bot`. The revised plan replaces the blocked phases with new phases that write `LogicalEquivalence.lean` from scratch for the fork's `Proposition` type and run final CI verification.

### Roadmap Alignment

This task advances the "Logics / Modal" module organization described in the project roadmap. A cleaner directory structure supports future modal logic extensions (decidability, model theory) and maintains clean PR boundaries with upstream CSLib.

## Goals & Non-Goals

**Goals**:
- Split `ProofSystem/Instances.lean` (1531 lines) into 15 per-system files with a barrel aggregator
- Group 28 system-specific Metalogic files into `Metalogic/Systems/{System}/` directories
- Maintain backward-compatible imports via barrel files
- Write `LogicalEquivalence.lean` from scratch for the fork's `Proposition` primitives (atom, bot, imp, box)
- Define `Proposition.Context` with constructors `hole`, `impL`, `impR`, `box`
- Prove logical equivalence is a congruence over all contexts
- Pass full CI after each structural change

**Non-Goals**:
- Refactor or reduce boilerplate within the axiom predicates (future task)
- Rename/split `Basic.lean` (too much import churn for minimal benefit)
- Change namespace structure (`Cslib.Logics.Modal` stays as-is)
- Resolve the B/KB naming inconsistency (future task)
- Extract S5-specific code from `DerivationTree.lean` (future task)
- Port upstream's `not`-based `Context` (incompatible with fork primitives)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Import path changes break downstream files | H | M | Use barrel files for backward compat; run `lake build` after each move batch |
| Fork's `Context.fill` congruence proof is non-trivial | M | M | Use structural induction on `Context`; each case reduces to `Iff.intro` on `imp`/`box` |
| `Satisfies` definition incompatible with congruence proof | M | L | Verify `Satisfies` supports `iff` reasoning via existing lemmas in `Basic.lean` |
| Lean module caching confused by moves | M | L | Run `lake clean` if incremental build fails |
| Git history lost on file moves | L | M | Use `git mv` for trackable moves; verify with `git log --follow` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Split Instances.lean into Per-System Files [COMPLETED]

**Goal**: Break the 1531-line monolith into 15 focused files plus a barrel aggregator.

**Tasks**:
- [x] Create directory `Cslib/Logics/Modal/ProofSystem/Instances/`
- [x] Extract `KAxiom` inductive + K instance registrations into `Instances/K.lean`
- [x] Extract `TAxiom` inductive + T instance registrations into `Instances/T.lean`
- [x] Extract `DAxiom` inductive + D instance registrations into `Instances/D.lean`
- [x] Extract `BAxiom` inductive + KB instance registrations into `Instances/B.lean`
- [x] Extract `K4Axiom` inductive + K4 instances into `Instances/K4.lean`
- [x] Extract `K5Axiom` inductive + K5 instances into `Instances/K5.lean`
- [x] Extract `K45Axiom` inductive + K45 instances into `Instances/K45.lean`
- [x] Extract `S4Axiom` inductive + S4 instances into `Instances/S4.lean`
- [x] Extract `S5Axiom` (= `ModalAxiom`) + S5 instances into `Instances/S5.lean`
- [x] Extract `TBAxiom` inductive + TB instances into `Instances/TB.lean`
- [x] Extract `KB5Axiom` inductive + KB5 instances into `Instances/KB5.lean`
- [x] Extract `D4Axiom` inductive + D4 instances into `Instances/D4.lean`
- [x] Extract `D5Axiom` inductive + D5 instances into `Instances/D5.lean`
- [x] Extract `D45Axiom` inductive + D45 instances into `Instances/D45.lean`
- [x] Extract `DBAxiom` inductive + DB instances into `Instances/DB.lean`
- [x] Convert original `Instances.lean` into barrel file importing all 15 sub-files
- [x] Each sub-file imports `Cslib.Logics.Modal.Metalogic.DerivationTree` and `Cslib.Foundations.Logic.ProofSystem`
- [x] Verify `lake build Cslib.Logics.Modal.ProofSystem.Instances` passes

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` - Convert to barrel aggregator
- `Cslib/Logics/Modal/ProofSystem/Instances/K.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/T.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/D.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/B.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/K4.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/K5.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/K45.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/S4.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/S5.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/TB.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/KB5.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/D4.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/D5.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/D45.lean` - New file
- `Cslib/Logics/Modal/ProofSystem/Instances/DB.lean` - New file

**Verification**:
- `lake build Cslib.Logics.Modal.ProofSystem.Instances` passes
- All 15 sub-files compile individually
- No file exceeds 200 lines

---

### Phase 2: Move Metalogic System-Specific Files into Systems/ Directories [COMPLETED]

**Goal**: Reorganize the 28 system-specific soundness/completeness files into per-system subdirectories.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Metalogic/Systems/` directory
- [x] Create subdirectories: `K/`, `T/`, `D/`, `B/`, `K4/`, `K5/`, `K45/`, `S4/`, `S5/`, `TB/`, `KB5/`, `D4/`, `D5/`, `D45/`, `DB/`
- [x] Move `KSoundness.lean` to `Systems/K/Soundness.lean` (update module header and imports)
- [x] Move `KCompleteness.lean` to `Systems/K/Completeness.lean`
- [x] Move `TSoundness.lean` to `Systems/T/Soundness.lean`
- [x] Move `TCompleteness.lean` to `Systems/T/Completeness.lean`
- [x] Move `DSoundness.lean` to `Systems/D/Soundness.lean`
- [x] Move `DCompleteness.lean` to `Systems/D/Completeness.lean`
- [x] Move `BSoundness.lean` to `Systems/B/Soundness.lean`
- [x] Move `BCompleteness.lean` to `Systems/B/Completeness.lean`
- [x] Move `K4Soundness.lean` to `Systems/K4/Soundness.lean`
- [x] Move `K4Completeness.lean` to `Systems/K4/Completeness.lean`
- [x] Move `K5Soundness.lean` to `Systems/K5/Soundness.lean`
- [x] Move `K5Completeness.lean` to `Systems/K5/Completeness.lean`
- [x] Move `K45Soundness.lean` to `Systems/K45/Soundness.lean`
- [x] Move `K45Completeness.lean` to `Systems/K45/Completeness.lean`
- [x] Move `S4Soundness.lean` to `Systems/S4/Soundness.lean`
- [x] Move `S4Completeness.lean` to `Systems/S4/Completeness.lean`
- [x] Move `S5Soundness.lean` to `Systems/S5/Soundness.lean`
- [x] Move `S5Completeness.lean` to `Systems/S5/Completeness.lean`
- [x] Move `TBSoundness.lean` to `Systems/TB/Soundness.lean`
- [x] Move `TBCompleteness.lean` to `Systems/TB/Completeness.lean`
- [x] Move `KB5Soundness.lean` to `Systems/KB5/Soundness.lean`
- [x] Move `KB5Completeness.lean` to `Systems/KB5/Completeness.lean`
- [x] Move `D4Soundness.lean` to `Systems/D4/Soundness.lean`
- [x] Move `D4Completeness.lean` to `Systems/D4/Completeness.lean`
- [x] Move `D5Soundness.lean` to `Systems/D5/Soundness.lean`
- [x] Move `D5Completeness.lean` to `Systems/D5/Completeness.lean`
- [x] Move `D45Soundness.lean` to `Systems/D45/Soundness.lean`
- [x] Move `D45Completeness.lean` to `Systems/D45/Completeness.lean`
- [x] Move `DBSoundness.lean` to `Systems/DB/Soundness.lean`
- [x] Move `DBCompleteness.lean` to `Systems/DB/Completeness.lean`
- [x] Update `module` declaration in each moved file to match new path
- [x] Update internal cross-references (e.g., `DCompleteness` imports `DSoundness` -- now `Systems.D.Soundness`)
- [x] Verify `lake build Cslib.Logics.Modal.Metalogic.Systems.K.Soundness` passes (spot check)

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- 28 files moved from `Metalogic/` to `Metalogic/Systems/{System}/`
- Internal import paths updated in each file (e.g., `Cslib.Logics.Modal.Metalogic.KSoundness` becomes `Cslib.Logics.Modal.Metalogic.Systems.K.Soundness`)

**Verification**:
- Spot-check 3 systems with `lake build` on their module paths
- No files remain in `Metalogic/` with system-prefix names (K*, T*, B*, D*, S4*, S5*, KB5*, TB*)

---

### Phase 3: Update Barrel Files and Cross-References [COMPLETED]

**Goal**: Update `Metalogic.lean` barrel, internal cross-references between system files, and `Cslib.lean`.

**Tasks**:
- [x] Rewrite `Metalogic.lean` barrel to import from new `Systems/` paths (30 import lines change)
- [x] Update any system file that imports another system file (e.g., `D4Completeness` imports `DCompleteness` -- now `Systems.D.Completeness`)
- [x] Update system-specific Instances imports: each `Systems/{X}/Soundness.lean` imports `Cslib.Logics.Modal.ProofSystem.Instances` (this path is unchanged due to Phase 1 barrel -- verify no change needed)
- [x] Run `lake exe mk_all --module` to regenerate `Cslib.lean`
- [x] Run `lake build` to verify full project compiles

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` - Update all system-specific import paths
- `Cslib.lean` - Regenerated by `lake exe mk_all --module`
- System files with cross-system imports (D4, D5, D45, DB completeness files import D completeness; K4, K5, K45, KB5, B completeness files import K completeness)

**Verification**:
- `lake build` passes (full project)
- `lake exe checkInitImports` passes
- `grep -r "Cslib.Logics.Modal.Metalogic.KSoundness" Cslib/` returns zero hits (old paths gone)

---

### Phase 4: CI Verification and PR 1 Preparation [COMPLETED]

**Goal**: Run the full CSLib CI pipeline and prepare the fork-only PR.

**Tasks**:
- [x] Run `lake build` (full project build)
- [x] Run `lake exe checkInitImports`
- [x] Run `lake lint`
- [x] Run `lake exe lint-style`
- [x] Run `lake test`
- [x] Run `lake shake --add-public --keep-implied --keep-prefix` (import minimization check)
- [x] Fix any lint or style issues introduced by the refactoring
- [x] Verify no `sorry` or vacuous definitions were introduced

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- Any files flagged by linters (style fixes only)

**Verification**:
- All CI commands pass without errors
- Git status shows only the intended file moves and barrel updates
- No upstream files (Basic.lean, Cube.lean, Denotation.lean) appear in the diff

---

### Phase 5: Write LogicalEquivalence.lean for Fork Primitives [COMPLETED]

**Goal**: Create `LogicalEquivalence.lean` from scratch, defining a one-hole `Context` inductive matching the fork's `Proposition` constructors (atom, bot, imp, box), a `fill` operation, logical equivalence, and a congruence theorem proving that equivalent propositions remain equivalent in any context.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/LogicalEquivalence.lean`
- [x] Add required imports: `import Cslib.Logics.Modal.Basic` (for `Proposition`, `Satisfies`, `Frame`, `Model`)
- [x] Define `Proposition.Context` inductive with constructors:
  - `hole` -- the position to substitute
  - `impL (c : Context Atom) (phi : Proposition Atom)` -- context in left argument of `imp`
  - `impR (phi : Proposition Atom) (c : Context Atom)` -- context in right argument of `imp`
  - `box (c : Context Atom)` -- context under `box`
- [x] Define `Context.fill (c : Context Atom) (phi : Proposition Atom) : Proposition Atom` by structural recursion on `c`
- [x] Define `LogicallyEquivalent (phi psi : Proposition Atom) : Prop` as: for all frames F, models M, and worlds w, `Satisfies F M w phi <-> Satisfies F M w psi` *(deviation: altered -- quantifies over World type explicitly rather than using implicit Frame/Model split since this fork has no separate Frame type)*
- [ ] Prove `fill_satisfies` lemma: `Satisfies F M w (c.fill phi) <-> ...` decomposing by context structure (auxiliary lemma for congruence) *(deviation: skipped -- congruence proof handles decomposition inline via simp without a separate auxiliary lemma)*
- [x] Prove `congruence` theorem: `LogicallyEquivalent phi psi -> LogicallyEquivalent (c.fill phi) (c.fill psi)` for all contexts `c`
  - Proof strategy: structural induction on `c`; `hole` case is trivial; `impL`/`impR` cases use iff-congruence on implication; `box` case uses universal quantification over accessible worlds
- [x] Ensure the file uses `import Cslib.Init` (CSLib convention)
- [x] Verify no `sorry` or vacuous placeholders
- [x] Run `lake exe mk_all --module` to add file to `Cslib.lean` barrel
- [x] Run `lake build Cslib.Logics.Modal.LogicalEquivalence` to verify compilation

**Timing**: 3 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/LogicalEquivalence.lean` - New file (written from scratch)
- `Cslib.lean` - Regenerated to include new file

**Verification**:
- `lake build Cslib.Logics.Modal.LogicalEquivalence` passes
- No `sorry` in file: `grep -c "sorry" Cslib/Logics/Modal/LogicalEquivalence.lean` returns 0
- `lake exe checkInitImports` passes
- `Context` has exactly 4 constructors matching fork's `Proposition` structure

**Design Notes**:
- The `Context` constructors deliberately mirror the fork's `Proposition` constructors (minus `atom` and `bot`, which are leaves and cannot contain sub-propositions)
- `atom` and `bot` are excluded from `Context` because they have no sub-proposition positions (they are ground terms)
- The congruence proof does NOT need derived connectives (`neg`, `and`, `or`, `diamond`) because those are abbreviations over `imp`, `bot`, and `box` -- congruence for them follows automatically
- The `bot+imp` convention is maintained universally: negation is `.imp phi .bot`, never a primitive constructor

---

### Phase 6: CI Verification and Final Cleanup [NOT STARTED]

**Goal**: Run the full CI pipeline, ensure everything passes, and verify the final directory structure.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake exe checkInitImports`
- [ ] Run `lake lint`
- [ ] Run `lake exe lint-style`
- [ ] Run `lake test`
- [ ] Fix any lint or style issues in `LogicalEquivalence.lean`
- [ ] Verify the overall directory structure matches the target layout
- [ ] Confirm no upstream files were modified (Basic.lean, Cube.lean, Denotation.lean unchanged)
- [ ] Verify external consumers (`Bimodal/Embedding/`) unaffected

**Timing**: 30 minutes

**Depends on**: 5

**Files to modify**:
- Any files flagged by linters (style fixes only in `LogicalEquivalence.lean`)

**Verification**:
- Full CI passes (build, checkInitImports, lint, lint-style, test)
- `LogicalEquivalence.lean` exists and compiles without `sorry`
- Directory tree shows reorganized structure with per-system Instances and Metalogic/Systems

## Testing & Validation

- [x] `lake build` passes after each phase (incremental verification)
- [x] `lake exe checkInitImports` passes (all files import `Cslib.Init`)
- [x] `lake lint` passes (no new linting errors introduced)
- [x] `lake exe lint-style` passes (style conformance)
- [x] `lake test` passes (CslibTests suite unaffected)
- [ ] `LogicalEquivalence.lean` compiles without `sorry`
- [ ] `Context` inductive matches fork's `Proposition` structure (impL, impR, box -- no `not`, `andL`, `andR`, `diamond`)
- [ ] Congruence theorem is stated and proved for all context constructors
- [ ] External consumers (`Bimodal/Embedding/`) unaffected (import paths unchanged)
- [ ] Barrel imports (`Metalogic.lean`, `Instances.lean`) re-export everything for backward compat

## Artifacts & Outputs

- `specs/137_refactor_modal_directory_structure/plans/01_modal-directory-refactor.md` (this plan)
- Reorganized `Cslib/Logics/Modal/ProofSystem/Instances/` directory (15 per-system files + barrel)
- Reorganized `Cslib/Logics/Modal/Metalogic/Systems/` directory (per-system subdirectories)
- `Cslib/Logics/Modal/LogicalEquivalence.lean` (new file, fork-native implementation)
- Updated `Cslib.lean` barrel (auto-generated)
- Updated `Metalogic.lean` barrel (manual)

## Rollback/Contingency

- **Phase 1-4 rollback**: Already completed and committed; would require `git revert` of those commits.
- **Phase 5 rollback**: If the congruence proof is intractable, remove `LogicalEquivalence.lean` and regenerate `Cslib.lean`. The file is self-contained with no downstream dependents, so removal has zero cascading impact.
- **Build failure during Phase 5**: The file is additive (new file only). Deleting it restores the pre-phase-5 state immediately.
- **lake clean**: If Lean module caching causes stale errors, run `lake clean && lake build` to rebuild from scratch.
