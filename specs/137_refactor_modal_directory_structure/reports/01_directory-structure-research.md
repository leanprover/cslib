# Task 137: Modal Directory Structure Research Report

**Session**: sess_1781221805_7d8c5d
**Date**: 2026-06-11

## 1. Current Directory Tree with File Descriptions

```
Cslib/Logics/Modal/
├── Basic.lean                      (394 lines) -- Core definitions: Model, Proposition, Satisfies,
│                                                   Judgement, axiom validity proofs (K, T, B, 4, 5, D)
├── Cube.lean                       (140 lines) -- Modal cube: 15 logics (K, D, T, B, S4, S5, etc.),
│                                                   ordering theorems, validity examples
├── Denotation.lean                  (85 lines) -- Denotational semantics (set-theoretic), characterisation
│                                                   theorem linking Satisfies to denotation
├── FromPropositional.lean          (103 lines) -- Embedding PL into Modal: toModal, coercion, preservation
├── Metalogic.lean                   (55 lines) -- Barrel import aggregator for all Metalogic/* files
├── Metalogic/
│   ├── DerivationTree.lean         (218 lines) -- Parameterized proof system: ModalAxiom (S5 axioms),
│   │                                              DerivationTree, Deriv, Derivable, modalDerivationSystem
│   ├── DeductionTheorem.lean       (215 lines) -- Deduction theorem parameterized over Axioms
│   ├── MCS.lean                    (392 lines) -- Maximal consistent sets (parameterized)
│   ├── Soundness.lean               (84 lines) -- Parameterized soundness theorem + S5 wrapper
│   ├── Completeness.lean           (475 lines) -- Parameterized canonical model + truth lemma + S5 wrapper
│   ├── KSoundness.lean              (82 lines) -- K-specific soundness
│   ├── KCompleteness.lean          (301 lines) -- K-specific completeness (K-specific existence lemma)
│   ├── TSoundness.lean              (89 lines) -- T-specific soundness
│   ├── TCompleteness.lean          (105 lines) -- T-specific completeness
│   ├── BSoundness.lean              (90 lines) -- B-specific soundness (KB system)
│   ├── BCompleteness.lean           (98 lines) -- B-specific completeness (KB system)
│   ├── DSoundness.lean              (90 lines) -- D-specific soundness
│   ├── DCompleteness.lean          (428 lines) -- D-specific completeness (D-specific existence lemma)
│   ├── K4Soundness.lean             (97 lines) -- K4-specific soundness
│   ├── K4Completeness.lean         (107 lines) -- K4-specific completeness
│   ├── K5Soundness.lean             (91 lines) -- K5-specific soundness
│   ├── K5Completeness.lean          (93 lines) -- K5-specific completeness
│   ├── K45Soundness.lean          (109 lines) -- K45-specific soundness
│   ├── K45Completeness.lean        (117 lines) -- K45-specific completeness
│   ├── KB5Soundness.lean           (116 lines) -- KB5-specific soundness
│   ├── KB5Completeness.lean        (121 lines) -- KB5-specific completeness
│   ├── S4Soundness.lean            (106 lines) -- S4-specific soundness
│   ├── S4Completeness.lean         (115 lines) -- S4-specific completeness
│   ├── S5Soundness.lean            (103 lines) -- S5-specific soundness
│   ├── S5Completeness.lean          (94 lines) -- S5-specific completeness
│   ├── TBSoundness.lean            (107 lines) -- TB-specific soundness
│   ├── TBCompleteness.lean         (129 lines) -- TB-specific completeness
│   ├── D4Soundness.lean            (103 lines) -- D4-specific soundness
│   ├── D4Completeness.lean         (118 lines) -- D4-specific completeness
│   ├── D5Soundness.lean            (104 lines) -- D5-specific soundness
│   ├── D5Completeness.lean         (119 lines) -- D5-specific completeness
│   ├── D45Soundness.lean           (115 lines) -- D45-specific soundness
│   ├── D45Completeness.lean        (130 lines) -- D45-specific completeness
│   ├── DBSoundness.lean            (103 lines) -- DB-specific soundness
│   └── DBCompleteness.lean         (119 lines) -- DB-specific completeness
└── ProofSystem/
    └── Instances.lean             (1531 lines) -- Axiom predicates (KAxiom, TAxiom, etc.) +
                                                    typeclass instance registrations for all 15 systems
```

**Total**: 41 files, approximately 7,500 lines of Lean code.

## 2. Upstream vs Fork-Only Classification

### Upstream Files (from leanprover/cslib)

These files exist on `upstream/main` and were introduced via merged PRs:

| File | Upstream PR | Authors |
|------|------------|---------|
| `Basic.lean` | #528 (feat: Modal Logic) | Montesi, Girlando, Brast-McKie |
| `Cube.lean` | #528 (feat: Modal Logic) | Montesi, Girlando |
| `Denotation.lean` | #528 (feat: Modal Logic) | Montesi, Brast-McKie |
| `LogicalEquivalence.lean` | #535 (feat: logical equivalence) | Montesi |

**Note**: `LogicalEquivalence.lean` exists on `upstream/main` but is **missing from the fork's `main` branch**. It exists only on the `pr1/foundations-logic` feature branch. This is a divergence point to resolve.

### Fork-Only Files

All files below were created by fork-specific tasks and have never been in upstream:

| File | Created By |
|------|-----------|
| `FromPropositional.lean` | task 73, task 118 |
| `Metalogic.lean` (barrel) | Created as aggregator |
| `Metalogic/DerivationTree.lean` | task 30, task 92 |
| `Metalogic/DeductionTheorem.lean` | fork task |
| `Metalogic/MCS.lean` | task 30 |
| `Metalogic/Soundness.lean` | fork (task 92) |
| `Metalogic/Completeness.lean` | fork (task 92, 100, 119) |
| `Metalogic/{K,T,B,D,...}Soundness.lean` (14 files) | tasks 95-119 |
| `Metalogic/{K,T,B,D,...}Completeness.lean` (14 files) | tasks 95-119 |
| `ProofSystem/Instances.lean` | task 93, task 100 |

**Summary**: 4 upstream files (3 on disk + 1 missing), 37 fork-only files.

## 3. Import Dependency Graph

### Core dependency chain (upstream files)

```
Basic.lean
├── Cube.lean
├── Denotation.lean
├── [LogicalEquivalence.lean -- upstream only, missing on fork]
└── FromPropositional.lean (also depends on Propositional/)
```

### Fork metalogic dependency chain

```
Basic.lean
└── DerivationTree.lean (also depends on Foundations/Logic/Metalogic/Consistency)
    └── DeductionTheorem.lean (also depends on Foundations/Data/ListHelpers,
    │                          Foundations/Logic/Metalogic/DeductionHelpers)
    │   └── MCS.lean
    │       └── Completeness.lean (also depends on Soundness.lean)
    │           ├── S5Completeness.lean (also depends on Instances.lean)
    │           ├── TCompleteness.lean (also depends on Instances.lean, MCS.lean, Soundness.lean)
    │           ├── S4Completeness.lean (also depends on Instances.lean)
    │           ├── TBCompleteness.lean (also depends on Instances.lean)
    │           ├── DCompleteness.lean (also depends on DSoundness.lean)
    │           │   ├── D4Completeness.lean
    │           │   ├── D5Completeness.lean
    │           │   ├── D45Completeness.lean
    │           │   └── DBCompleteness.lean
    │           ├── KCompleteness.lean (also depends on MCS.lean, Soundness.lean, Instances.lean)
    │           │   ├── K4Completeness.lean (also depends on Instances.lean)
    │           │   ├── K5Completeness.lean
    │           │   ├── K45Completeness.lean (also depends on Instances.lean)
    │           │   ├── KB5Completeness.lean (also depends on Instances.lean)
    │           │   └── BCompleteness.lean (also depends on Instances.lean)
    │           └── ...
    └── Soundness.lean
        ├── KSoundness.lean (also depends on Instances.lean)
        ├── TSoundness.lean (also depends on Instances.lean)
        ├── BSoundness.lean (also depends on Instances.lean)
        ├── DSoundness.lean (also depends on Instances.lean)
        ├── ... (all *Soundness.lean follow same pattern)
        └── Completeness.lean (also depends on MCS.lean)
```

### Instances.lean dependencies
```
DerivationTree.lean
└── Instances.lean (also depends on Foundations/Logic/ProofSystem)
```

### External consumers of Modal/
```
Bimodal/Embedding/ModalEmbedding.lean --> imports Modal/Basic.lean
Bimodal/Embedding/PropositionalEmbedding.lean --> imports Modal/FromPropositional.lean
Cslib.lean (barrel) --> imports all 41 files
```

## 4. Problems with Current Structure

### Problem 1: Flat Metalogic Directory (30 files, no sub-organization)

The `Metalogic/` directory contains 30 files in a flat list. Files for 15 different modal systems are mixed together. Finding files for a specific system requires scanning the entire directory. The naming convention (prefix system name) helps but does not provide visual grouping.

### Problem 2: Monolithic Instances.lean (1531 lines)

`ProofSystem/Instances.lean` is the largest file at 1531 lines. It contains:
- 15 separate axiom predicates (inductive types): `KAxiom`, `TAxiom`, `DAxiom`, `S4Axiom`, `BAxiom`, `K4Axiom`, `K5Axiom`, `K45Axiom`, `TBAxiom`, `KB5Axiom`, `D4Axiom`, `D5Axiom`, `D45Axiom`, `DBAxiom`
- 15 sets of typeclass instance registrations (each ~50 lines of boilerplate)

The massive boilerplate repetition (every axiom predicate repeats the same 4 propositional axiom constructors) makes the file hard to navigate and maintain.

### Problem 3: Naming inconsistency in Metalogic files

- The "generic" soundness/completeness files (`Soundness.lean`, `Completeness.lean`) contain S5-specific wrappers alongside the parameterized theorems
- `DerivationTree.lean` contains both the generic `DerivationTree` and `ModalAxiom` (S5-specific) in the same file
- System-specific files are named inconsistently: the `B` prefix means "KB" system (not just B axiom)

### Problem 4: Missing upstream file

`LogicalEquivalence.lean` exists on upstream/main but is absent from the fork's main branch. This needs to be resolved to keep clean mergeability.

### Problem 5: Lack of directory hierarchy for related concerns

The Metalogic directory mixes:
- Infrastructure (DerivationTree, DeductionTheorem, MCS)
- Generic metatheory (parameterized Soundness, Completeness)
- 15 system-specific files (each with Soundness + Completeness)

There is no per-system grouping or per-concern grouping.

## 5. The Modal Cube: Systems Represented

All 15 systems of the standard modal cube are present:

| System | Relation Properties | Axioms (beyond K) |
|--------|--------------------|--------------------|
| K | none | (base) |
| D | serial | D: Box phi -> Diamond phi |
| T | reflexive | T: Box phi -> phi |
| KB | symmetric | B: phi -> Box Diamond phi |
| K4 | transitive | 4: Box phi -> Box Box phi |
| K5 | Euclidean | 5: Diamond phi -> Box Diamond phi |
| K45 | transitive + Euclidean | 4 + 5 |
| DB | serial + symmetric | D + B |
| D4 | serial + transitive | D + 4 |
| D5 | serial + Euclidean | D + 5 |
| D45 | serial + transitive + Euclidean | D + 4 + 5 |
| TB | reflexive + symmetric | T + B |
| S4 | reflexive + transitive (= preorder) | T + 4 |
| KB5 | symmetric + Euclidean | B + 5 |
| S5 | reflexive + transitive + symmetric (= equivalence) | T + 4 + B |

The cube is organized by three axes: seriality/reflexivity (D/T), symmetry (B), and transitivity/Euclideanness (4/5).

## 6. Proposed Restructuring

### PR 1: Fork-Only Files (Hilbert/, Metalogic/Systems/, split Instances.lean)

This PR restructures only fork-created files, minimizing upstream merge conflicts.

#### 6a. Split Instances.lean into per-system files

**Current**: `ProofSystem/Instances.lean` (1531 lines, all 15 systems)

**Proposed**: Create `ProofSystem/Instances/` directory with one file per system:

```
ProofSystem/
├── Instances.lean              -- Barrel import (aggregator only)
└── Instances/
    ├── K.lean                  -- KAxiom + K instances
    ├── T.lean                  -- TAxiom + T instances
    ├── D.lean                  -- DAxiom + D instances
    ├── B.lean                  -- BAxiom + KB instances
    ├── K4.lean                 -- K4Axiom + K4 instances
    ├── K5.lean                 -- K5Axiom + K5 instances
    ├── K45.lean                -- K45Axiom + K45 instances
    ├── S4.lean                 -- S4Axiom + S4 instances
    ├── S5.lean                 -- S5Axiom (= ModalAxiom) + S5 instances
    ├── TB.lean                 -- TBAxiom + TB instances
    ├── KB5.lean                -- KB5Axiom + KB5 instances
    ├── D4.lean                 -- D4Axiom + D4 instances
    ├── D5.lean                 -- D5Axiom + D5 instances
    ├── D45.lean                -- D45Axiom + D45 instances
    └── DB.lean                 -- DBAxiom + DB instances
```

**Import impact**: All files that currently import `Cslib.Logics.Modal.ProofSystem.Instances` continue to do so via the barrel file. The barrel re-exports everything. System-specific soundness/completeness files could optionally import only the system they need.

#### 6b. Group Metalogic by system

**Current**: `Metalogic/` with 30+ files flat

**Proposed**: Create `Metalogic/Systems/` with per-system directories:

```
Metalogic/
├── DerivationTree.lean         -- (unchanged) Generic proof system
├── DeductionTheorem.lean       -- (unchanged) Generic deduction theorem
├── MCS.lean                    -- (unchanged) Generic MCS
├── Soundness.lean              -- (unchanged) Parameterized soundness
├── Completeness.lean           -- (unchanged) Parameterized completeness + canonical model
├── Systems/
│   ├── K/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── T/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── D/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── B/                      -- Note: this is KB system
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── K4/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── K5/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── K45/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── S4/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── S5/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── TB/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── KB5/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── D4/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── D5/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   ├── D45/
│   │   ├── Soundness.lean
│   │   └── Completeness.lean
│   └── DB/
│       ├── Soundness.lean
│       └── Completeness.lean
```

**Alternative to per-system directories**: Keep flat `Metalogic/Systems/` with the existing `{System}Soundness.lean` / `{System}Completeness.lean` naming. This is simpler but less self-documenting.

**Recommendation**: The per-system directory approach is better because:
1. Each directory becomes a complete unit (soundness + completeness for one system)
2. It mirrors the ProofSystem/Instances split
3. Future files per system (e.g., decidability, model theory) slot in naturally

### PR 2: Upstream-Originating Files (Syntax.lean, Semantics/)

This PR restructures the 4 upstream files. **This requires upstream coordination** since it changes import paths for files that upstream maintains.

#### Option A: Rename Basic.lean to split Syntax/Semantics

```
Modal/
├── Syntax.lean                 -- Proposition type, derived connectives, notation
├── Semantics/
│   ├── Basic.lean              -- Model, Satisfies, Judgement, axiom validity
│   ├── Denotation.lean         -- Denotational semantics (moved from top-level)
│   └── LogicalEquivalence.lean -- (restore from upstream)
├── Cube.lean                   -- Modal cube definitions + ordering (unchanged)
├── FromPropositional.lean      -- PL embedding (unchanged, already fork-only)
```

#### Option B: Minimal upstream change

```
Modal/
├── Basic.lean                  -- (unchanged, keep for upstream compatibility)
├── Cube.lean                   -- (unchanged)
├── Denotation.lean             -- (unchanged)
├── LogicalEquivalence.lean     -- (restore from upstream)
├── FromPropositional.lean      -- (unchanged)
```

**Recommendation**: Option B is safer for PR 2. Restructuring `Basic.lean` (the most foundational file) would change every import across the entire codebase and upstream. Since `Basic.lean` at 394 lines is not excessively large, the benefit of splitting does not justify the import churn. The primary action for PR 2 should be restoring `LogicalEquivalence.lean`.

## 7. Risk Analysis

### Low Risk

| Action | Risk | Mitigation |
|--------|------|------------|
| Split `Instances.lean` into per-system files | Import path changes for `Cslib.Logics.Modal.ProofSystem.Instances` | Keep barrel file re-exporting everything |
| Add `Metalogic/Systems/` subdirectories | Import path changes for all Metalogic files | Update barrel `Metalogic.lean` |
| Restore `LogicalEquivalence.lean` | None -- adding a file | Cherry-pick from upstream |

### Medium Risk

| Action | Risk | Mitigation |
|--------|------|------------|
| Move system-specific Metalogic files | 30 import paths change across the codebase | `Cslib.lean` barrel must be regenerated with `lake exe mk_all --module` |
| System-specific Instances files changing import paths | Soundness/Completeness files import Instances | Each file imports specific Instances subfile |

### High Risk

| Action | Risk | Mitigation |
|--------|------|------------|
| Rename/split `Basic.lean` | 37 direct/transitive importers break | NOT RECOMMENDED for PR 2 |
| Change namespace structure (`Cslib.Logic.Modal` -> `Cslib.Logics.Modal`) | Breaks all downstream references | NOT RECOMMENDED |

### Cross-cutting Risks

1. **Build time impact**: Splitting files may increase build time if Lean cannot parallelize as well. However, the current monolithic `Instances.lean` (1531 lines) is likely a build bottleneck.

2. **Import cycle risk**: None -- the dependency graph is strictly hierarchical (no cycles exist today, and the restructuring preserves this).

3. **Bimodal dependency**: `Bimodal/Embedding/ModalEmbedding.lean` imports `Modal/Basic.lean`. As long as `Basic.lean` path is unchanged (PR 1) or a barrel redirect exists (PR 2 Option A), this is safe.

## 8. Recommendations

### Priority 1: PR 1 (fork-only, safe to merge immediately)

1. **Split `Instances.lean`** into `ProofSystem/Instances/{K,T,D,...}.lean` with barrel aggregator
2. **Create `Metalogic/Systems/`** with per-system directories for the 15 system-specific soundness/completeness files
3. **Update `Metalogic.lean`** barrel to import from new paths
4. **Regenerate `Cslib.lean`** with `lake exe mk_all --module`
5. **Run full CI**: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake test`

### Priority 2: PR 2 (upstream coordination needed)

1. **Restore `LogicalEquivalence.lean`** from upstream/main (cherry-pick or merge)
2. **Keep `Basic.lean` unchanged** -- do NOT split into Syntax/Semantics
3. **Consider moving `Denotation.lean` into a `Semantics/` subdirectory** only if upstream agrees

### Priority 3: Future improvements (out of scope for this task)

1. **Reduce boilerplate**: Extract shared propositional axiom constructors into a base predicate, composing system axiom predicates via extension/embedding. This would dramatically shrink the axiom inductive types.
2. **Naming audit**: Resolve the `B` vs `KB` naming inconsistency (file named `BSoundness` but system is KB).
3. **Extract S5-specific code** from `DerivationTree.lean` into `Systems/S5/` or a separate file.

### Import Path Migration Checklist

For each moved file, the following must be updated:
- [ ] `import` statements in files that reference the old path
- [ ] `Metalogic.lean` barrel file
- [ ] `Cslib.lean` barrel file (via `lake exe mk_all --module`)
- [ ] Any documentation references

### Estimated Scope

| Component | Files Moved | Files Modified (imports) | Lines Changed |
|-----------|-------------|------------------------|---------------|
| Split Instances.lean | 1 -> 15+1 | ~30 (all Soundness/Completeness) | ~1700 (mostly move) |
| Move Metalogic Systems | 28 -> 28 | ~30 (cross-references) + 2 barrels | ~200 (import lines) |
| Restore LogicalEquivalence | 0 -> 1 | 1 (Cslib.lean barrel) | ~130 (new file) |
| **Total** | ~45 files touched | ~35 files modified | ~2000 lines |
