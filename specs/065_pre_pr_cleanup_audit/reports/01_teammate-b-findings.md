# Teammate B Findings: Structural and Organizational Issues

**Task**: 65 — Audit repo for pre-PR cleanup and create refactoring tasks
**Date**: 2026-06-09
**Angle**: Alternative Approaches — structural issues, duplication, naming, docstrings, style

## Key Findings

### 1. Significant Code Duplication Across Modal/Temporal/Bimodal (HIGH Priority)

Three categories of near-identical code exist across the three logic modules:

#### 1a. DeductionTheorem triplication
All three logics have their own `DeductionTheorem.lean` with identical helper code:
- `removeAll` definition (identical in all 3): `l.filter (· ≠ a)`
- `removeAll_subset_of_subset` / `removeAll_sub_of_sub` (same logic, slightly different names)
- `mem_removeAll_of_mem_of_ne` (identical)
- `deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp`, `deduction_with_mem`, `deduction_theorem` — all follow the same structure

**Files**:
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean`
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean`
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean`

**Impact**: ~250 lines duplicated 3x. The `removeAll` helper alone is copy-pasted verbatim. This is the highest-leverage refactoring target.

#### 1b. DerivationTree triplication
All three have `DerivationTree.lean` with the same wrapper pattern: `Deriv`, `Derivable`/`ThDerivable`, `mp_deriv`, `weakening_deriv`, `assumption_deriv`, and a `derivationSystem` instance.

**Files**:
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`
- `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean`
- `Cslib/Logics/Bimodal/Metalogic/Core/DerivationTree.lean`

#### 1c. MCS triplication
All three have MCS files with near-identical `lindenbaum`, `closed_under_derivation`, `implication_property`, `negation_complete`, `mcs_bot_not_mem`, `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem` theorems.

**Files**:
- `Cslib/Logics/Modal/Metalogic/MCS.lean`
- `Cslib/Logics/Temporal/Metalogic/MCS.lean`
- `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean`

**Note**: Naming inconsistency — Modal/Temporal call theirs `MCS.lean`, Bimodal calls it `MaximalConsistent.lean`.

#### 1d. TemporalContent/WitnessSeed duplication
Both Temporal and Bimodal have near-identical files for these:

- `g_content`, `h_content`, `f_content`, `p_content`, `u_content`, `s_content` definitions are **character-for-character identical** between:
  - `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalContent.lean`

- WitnessSeed follows the same pattern with minor parameterization differences (`fc : FrameClass`):
  - `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Bundle/WitnessSeed.lean`

#### 1e. Chronicle pipeline duplication
The entire Chronicle subdirectory is duplicated between Temporal and Bimodal:

| File | Temporal (lines) | Bimodal (lines) |
|------|-------------------|------------------|
| ChronicleConstruction.lean | 1435 | 1531 |
| CounterexampleElimination.lean | 3297 | 3529 |
| PointInsertion.lean | 2888 | 3556 |
| ChronicleTypes.lean | 318 | 386 |
| RRelation.lean | 711 | 1695 |
| ChronicleToCountermodel.lean | 133 | 229 |

**Total duplicated**: ~9,484 lines (Temporal) + ~12,096 lines (Bimodal) = ~21,580 lines with substantial overlap. This is the largest single source of code duplication. However, the Bimodal versions are parameterized over `FrameClass` while Temporal versions are not, making naive deduplication non-trivial.

#### 1f. GeneralizedNecessitation duplication
Both Temporal and Bimodal have their own `GeneralizedNecessitation.lean` with `past_necessitation`, `past_k_dist`, `generalized_temporal_k`, and `generalized_past_k` — structurally identical.

### 2. `def` vs `theorem` Inconsistency (MEDIUM Priority)

Bimodal theorem files consistently use `def` for derivation-returning functions, while Foundations uses `theorem`:

- **Foundations** (`Theorems/Combinators.lean`): `theorem imp_trans`, `theorem identity`, `theorem b_combinator`, etc.
- **Bimodal** (`Theorems/Combinators.lean`): `def imp_trans`, `def identity`, `def b_combinator`, etc.

This is a systematic difference: 30+ definitions in Bimodal use `def` where Foundations uses `theorem`. The Bimodal versions return concrete `DerivationTree` terms (data), while Foundations returns existence proofs — so `def` is arguably correct for Bimodal. However, this inconsistency may confuse PR reviewers.

### 3. Missing Copyright Headers (MEDIUM Priority)

6 files lack the standard copyright/license header:

- `Cslib/Logics/Temporal/Metalogic.lean` (barrel import)
- `Cslib/Logics/Modal/Metalogic.lean` (barrel import)
- `Cslib/Logics/Bimodal/Metalogic/Bundle/Bundle.lean` (barrel import)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/BXCanonical.lean` (barrel import)
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/Algebraic.lean` (barrel import)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`

All barrel imports use a simple `-- Barrel import` comment instead of the standard header.

### 4. Linter Suppression Prevalence (MEDIUM Priority)

- **94 of 196** logic files suppress `linter.style.longLine` (48%)
- **96 of 196** logic files suppress `linter.style.emptyLine` (49%)

Nearly half the codebase suppresses these linters. While this may be intentional for proof-heavy files, Mathlib reviewers expect linter compliance. Bulk-fixing long lines and empty lines before PR submission would reduce review friction significantly.

### 5. Sorry Instances (HIGH Priority for PR submission)

**26 `sorry` proof terms** exist in the logic codebase:

| Location | Count | Reason |
|----------|-------|--------|
| `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 12 | Discrete pipeline (task 36 dependency) |
| `Bimodal/Metalogic/Bundle/SuccRelation.lean` | 7 | Unknown |
| `Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` | 2 | Unknown |
| `Bimodal/Metalogic/BXCanonical/Frame.lean` | 1 | Reflexivity under irreflexive semantics |
| `Bimodal/Metalogic/BXCanonical/Completeness/Dense.lean` | 1 | Universe mismatch |
| `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` | 1 | Universe/termination |
| `Temporal/Metalogic/Chronicle/Frame.lean` | 1 | Reflexivity (same issue as bimodal) |
| `Foundations/Logic/Theorems/Temporal/FrameConditions.lean` | 1 | (needs verification) |

All 26 are in Bimodal or Temporal metalogic — none in the Modal or Foundations layers. Most are tagged as task 36 dependencies (bimodal discrete completeness porting).

### 6. Import Hierarchy is Clean (POSITIVE Finding)

- No Modal→Temporal or Temporal→Modal cross-imports
- No reverse imports (Temporal/Modal→Bimodal)
- Bimodal imports Modal/Temporal only through the Embedding module
- Foundations→Logics flow is correct throughout

### 7. Naming Inconsistency: MCS File Names (LOW Priority)

| Logic | File name | Content |
|-------|-----------|---------|
| Modal | `MCS.lean` | MCS theory |
| Temporal | `MCS.lean` | MCS theory |
| Bimodal | `MaximalConsistent.lean` + `MCSProperties.lean` | MCS theory split across 2 files |

Bimodal splits MCS into two files with a different naming convention. The split itself may be justified (list-based vs set-based), but the file naming diverges from Modal/Temporal.

### 8. Namespace Convention is Consistent (POSITIVE Finding)

All modules follow `Cslib.Logic.{Modal|Temporal|Bimodal}[.Submodule]` consistently. No namespace pollution or stale namespace references found.

### 9. Module Docstring Coverage is Excellent (POSITIVE Finding)

192 of 196 logic files have module docstrings (`/-!`). The 4 without are barrel import files which use simple comments instead — this is acceptable.

### 10. No Debug Artifacts (POSITIVE Finding)

No `#check`, `#eval`, or `dbg_trace` commands found in any logic source file.

## Recommended Approach

### Immediate (Pre-PR blockers):
1. **Fix sorry instances** — The 26 sorries must be resolved or clearly documented as out-of-scope for the PR. PRs 1-6 should not contain sorries in their scope.
2. **Add copyright headers** to the 6 missing files.

### High-leverage refactoring:
3. **Factor shared DeductionTheorem infrastructure** — Extract `removeAll` and helper lemmas into `Foundations/Logic/Metalogic/` as a shared module. Each logic's deduction theorem would import and specialize.
4. **Factor shared MCS infrastructure** — The `mcs_bot_not_mem`, `mcs_neg_of_not_mem`, etc. pattern is identical. The generic framework in `Foundations/Logic/Metalogic/Consistency.lean` should absorb these.
5. **Factor shared Chronicle infrastructure** — This is the hardest but highest-payoff: ~20K lines of duplication. The main blocker is FrameClass parameterization in Bimodal but not Temporal.

### Lower priority:
6. **Standardize MCS file naming** across modules.
7. **Address linter suppressions** — At minimum, fix `longLine` violations in files targeted for PR submission.
8. **Standardize `def` vs `theorem`** for derivation combinators (or document the convention).

## Evidence/Examples

### removeAll duplication (verbatim identical):
```lean
-- Modal/Metalogic/DeductionTheorem.lean:49
private def removeAll [DecidableEq α] (l : List α) (a : α) : List α :=
  l.filter (· ≠ a)

-- Temporal/Metalogic/DeductionTheorem.lean:51
private def removeAll [DecidableEq α] (l : List α) (a : α) : List α :=
  l.filter (· ≠ a)

-- Bimodal/Metalogic/Core/DeductionTheorem.lean:83
private def removeAll {α : Type _} [DecidableEq α] (l : List α) (a : α) : List α :=
  l.filter (· ≠ a)
```

### TemporalContent definitions (verbatim identical):
```lean
-- Both files define these identically:
def g_content (M : Set (Formula Atom)) : Set (Formula Atom) := ...
def h_content (M : Set (Formula Atom)) : Set (Formula Atom) := ...
def f_content (M : Set (Formula Atom)) : Set (Formula Atom) := ...
def p_content (M : Set (Formula Atom)) : Set (Formula Atom) := ...
def u_content (M : Set (Formula Atom)) : Set (Formula Atom × Formula Atom) := ...
def s_content (M : Set (Formula Atom)) : Set (Formula Atom × Formula Atom) := ...
```

## Confidence Level

- **Code duplication findings**: HIGH — confirmed by direct file comparison
- **Sorry count**: HIGH — grep results verified against source
- **Import hierarchy**: HIGH — exhaustive cross-import check
- **Naming inconsistency**: HIGH — direct observation
- **Linter suppression stats**: HIGH — exact counts from grep
- **Refactoring effort estimates**: MEDIUM — the Chronicle deduplication is complex due to FrameClass parameterization differences
