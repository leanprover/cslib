# Teammate A Findings: Implementation-Level Code Quality

**Task**: 65 — Audit repo for pre-PR cleanup
**Focus**: sorry instances, dead code, debugging artifacts, commented-out blocks
**Date**: 2026-06-09

## Key Findings

### 1. Sorry Instances — 26 stubs across 8 files (HIGH PRIORITY)

All sorry instances are in the logic library (Logics/Bimodal and Logics/Temporal). None exist outside the logic subsystem.

| File | Count | Nature |
|------|-------|--------|
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 12 | Discrete pipeline stubs (task 36 dependency) |
| `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` | 7 | MCS temporal content lemmas |
| `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` | 2 | Until/Since coherence proofs |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` | 1 | `bx_le_refl` (reflexivity under irreflexive semantics) |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Completeness/Dense.lean` | 1 | Universe mismatch in `countermodel_dense_enriched` |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` | 1 | Universe level issue |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` | 1 | Documentation note (sorry in comment context) |
| `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` | 1 | `t_le_refl` (same reflexivity issue as bimodal) |

**Category breakdown**:
- **Task 36 blocked** (discrete pipeline): ~14 sorry stubs depend on porting discrete completeness from BimodalLogic
- **Semantic design** (reflexivity): 2 sorry stubs in Frame.lean files — both `bx_le_refl` and `t_le_refl` are sorry'd due to irreflexive semantics design issue
- **Universe mismatches**: 2 sorry stubs in Completeness/Dense.lean and ChronicleToCountermodelBasic.lean
- **Missing MCS lemmas**: 9 sorry stubs in Bundle/SuccRelation.lean and UntilSinceCoherence.lean

### 2. Commented-Out Code Blocks — 740 lines across 19 files

Large commented-out blocks suggest incomplete refactoring or abandoned proof strategies.

**Worst offenders (PR-relevant logic files)**:
| File | Commented Lines | Nature |
|------|----------------|--------|
| `Cslib/Logics/Temporal/Metalogic/MCS.lean` | 193 | Old proof strategies and scratch work (85-line and 45-line blocks) |
| `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` | 167 | Old proof attempts |
| `Cslib/Logics/Modal/Metalogic/Completeness.lean` | 144 | Legacy code |
| `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` | 57 | Abandoned approaches |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` | 47 | Abandoned approaches |

### 3. Debugging Artifacts — Minimal

- `#check` statements in `Cslib/Foundations/Data/HasFresh.lean:123-135` — these are inside a doc comment (markdown code block), so they are **documentation, not debugging artifacts**. No cleanup needed.
- All `#check`/`#eval` in `CslibTests/` files are intentional test assertions. No issues.

### 4. Linter Suppressions — 377 `set_option` directives

| Suppression | Count | Risk |
|-------------|-------|------|
| `linter.style.emptyLine false` | 97 | Low — cosmetic |
| `linter.style.longLine false` | 94 | Low — cosmetic |
| `maxHeartbeats` (elevated) | 50 | Medium — performance concern |
| `linter.tacticAnalysis.verifyGrindOnly` | 36 | Low — tool-specific |
| `linter.flexible false` | 25 | Low |
| `linter.unusedDecidableInType` | 24 | Low |

**High heartbeat files** (>= 1,600,000 = 8x default): 34 files. The worst is `CounterexampleElimination.lean` at 6,400,000 (32x default). These indicate proofs that may need optimization for CI performance.

### 5. TODO/FIXME Comments — 22 instances

Most TODO comments are in non-logic files (Computability, Crypto, Languages, LinearLogic). Within the PR-relevant logic files:
- 3 TODOs in `ChronicleToCountermodel.lean` (all task 36 dependencies)
- These are correctly documented and linked to existing tasks

### 6. Missing Module Docstrings — 5 barrel files

| File | Type |
|------|------|
| `Cslib/Logics/Bimodal/Metalogic/Algebraic/Algebraic.lean` | Barrel import |
| `Cslib/Logics/Bimodal/Metalogic/Bundle/Bundle.lean` | Barrel import |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/BXCanonical.lean` | Barrel import |
| `Cslib/Logics/Bimodal/Metalogic/Separation.lean` | Has copyright but no `/-!` docstring |
| `Cslib/Logics/Temporal/Metalogic.lean` | Barrel import |

These barrel files use plain `--` comments instead of `/-! ... -/` module docstrings.

### 7. Large Files — Potential split candidates

| File | Lines |
|------|-------|
| `BXCanonical/Chronicle/PointInsertion.lean` | 3,556 |
| `BXCanonical/Chronicle/CounterexampleElimination.lean` | 3,529 |
| `Temporal/Chronicle/CounterexampleElimination.lean` | 3,297 |
| `Temporal/Chronicle/PointInsertion.lean` | 2,888 |

Files over 2,000 lines are unusual for Lean libraries and may cause slow builds. However, splitting complex proof files carries risk and may not be worth it for a first PR.

### 8. Naming Convention Mix

- **snake_case** declarations: 1,917
- **camelCase** declarations: 711

Lean 4/Mathlib convention is `snake_case` for theorems/lemmas and `CamelCase` for types/structures. The 711 camelCase declarations include type definitions (correct) but may also include some theorem names that don't follow convention. This needs a targeted audit.

### 9. Duplicate Definition Names Between Bimodal and Temporal — 270 shared names

This is expected due to parallel structure (both implement MCS, chronicles, etc.) but indicates potential for shared abstractions (addressed by task 41).

## Recommended Approach

**Priority 1 (PR blockers)**:
1. Resolve or document all 26 sorry instances — determine which block PRs and which can be excluded from PR scope
2. Remove 740 lines of commented-out code (particularly MCS.lean's 193 lines)

**Priority 2 (PR quality)**:
3. Add `/-!` module docstrings to 5 barrel files
4. Review and potentially reduce maxHeartbeats settings in 34 files

**Priority 3 (Nice-to-have)**:
5. Audit camelCase theorem names against Mathlib conventions
6. Consider factoring shared abstractions (task 41)

## Evidence/Examples

**Sorry stubs example** (`SuccRelation.lean:259`):
```lean
theorem until_unfold_in_mcs (...) :
    Formula.untl (Formula.or ψ (Formula.and φ (Formula.untl ψ φ))) (Formula.bot) ∈ M := by
  sorry
```
This and 6 neighboring theorems are all sorry'd — they form a coherent group of MCS temporal content lemmas.

**Commented-out code example** (`Temporal/Metalogic/MCS.lean:192-276`):
85 consecutive lines of commented-out proof strategy notes — appears to be scratch work exploring proof approaches for contrapositive derivation. Should be removed.

**Reflexivity sorry** (`BXCanonical/Frame.lean:154-155`):
```lean
theorem bx_le_refl (w : BXPoint Atom) : bx_le w w := by
  sorry
```
Identical pattern in `Temporal/Metalogic/Chronicle/Frame.lean:104-105`. Both are sorry'd due to a semantic design question about reflexivity under irreflexive semantics.

## Confidence Level

- **Sorry instances**: **High** — comprehensive grep, all instances found
- **Commented-out code**: **High** — automated scan with 5+ consecutive line threshold
- **Debugging artifacts**: **High** — no actual issues found (only doc examples)
- **Linter suppressions**: **High** — exact counts from grep
- **Naming conventions**: **Medium** — needs deeper analysis to distinguish type names from theorem names
- **Unused imports**: **Low** — not checked in detail (requires build-level analysis or tooling)
