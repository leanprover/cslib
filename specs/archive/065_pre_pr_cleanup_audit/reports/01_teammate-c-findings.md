# Teammate C (Critic) Findings: Pre-PR Audit Blind Spots

**Task**: 65 — Audit repo for pre-PR cleanup
**Date**: 2026-06-09
**Role**: Critic — identifying gaps other teammates are likely missing

## Key Findings

### 1. Copyright Headers Missing on 2 Barrel Files (CRITICAL for CI)

The `lint-style-action` CI step enforces Mathlib-style copyright headers. Two barrel files are missing headers entirely:

- `Cslib/Logics/Modal/Metalogic.lean` — no copyright header, just import statements
- `Cslib/Logics/Temporal/Metalogic.lean` — same issue

These will fail the lint-style CI check. All other files in PR-relevant modules have proper headers.

### 2. PR1 File Count is Wrong — 16 Files, Not 9 (HIGH)

Task 59 claims PR1 contains "9 Foundations/Logic files" but there are actually **16 `.lean` files** in `Cslib/Foundations/Logic/`:

- **Listed (9)**: Combinators, BigConj, Propositional/{Core, Connectives, Reasoning}, Modal/{Basic, S5}, Metalogic/Consistency, plus barrel
- **Unlisted but required (7)**: `Axioms.lean`, `Connectives.lean`, `InferenceSystem.lean`, `LogicalEquivalence.lean`, `ProofSystem.lean`, `Theorems/Temporal/TemporalDerived.lean`, `Theorems/Temporal/FrameConditions.lean`

The unlisted files are **transitive dependencies** — `Combinators.lean` imports `ProofSystem.lean`, which is a `module` file that re-exports `Connectives.lean`. The Temporal files in Foundations are imported by `Theorems.lean` (barrel). The PR will not compile without them.

**Impact**: The PR description needs updating. The line count (~3,319) is also understated.

### 3. Temporal Metalogic Barrel Missing 2 Imports (MEDIUM)

`Cslib/Logics/Temporal/Metalogic.lean` is missing imports for:
- `Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleConstruction`
- `Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination`

These files exist in the Chronicle/ directory but are not re-exported by the barrel. The `lake exe mk_all --check --module` CI step may or may not catch this depending on whether `Cslib.lean` imports them directly (it does — so CI passes, but the barrel is incomplete and misleading).

### 4. One `sorry` Remains in Temporal Chronicle (HIGH for PR5/PR6)

`Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean:105` has a `sorry` in `t_le_refl`:
```lean
theorem t_le_refl (w : TPoint Atom) : t_le w w := by
  sorry
```
Comment says "sorry'd -- same issue as bimodal". This is in PR5 (Chronicle infrastructure) scope. A `sorry` will likely **block PR approval** — CSLib CI builds with `--wfail` which treats warnings as errors, and `sorry` generates a warning.

### 5. Extensive Linter Suppression (61 overrides) (MEDIUM-HIGH)

Across PR-relevant modules there are **61 `set_option linter.*` overrides**:
- `longLine`: 22 instances
- `emptyLine`: 14 instances  
- `setOption`: 7 instances (meta — suppressing the "you're suppressing a linter" warning)
- `flexible`: 7 instances
- `unreachableTactic`: 6 instances
- `dupNamespace`: 5 instances

PR reviewers will likely push back on blanket `set_option linter.style.longLine false` at file scope. CSLib convention is to fix the long lines, not suppress the linter. The `linter.unreachableTactic false` overrides suggest proof terms with unreachable branches that could be simplified.

### 6. No Test Coverage for Modal/Temporal/Bimodal Logic (MEDIUM)

`CslibTests/` has 13 test files covering Bisimulation, CCS, CLL, DFA, FreeMonad, HML, LTS, LambdaCalculus, MLL, etc. — but **zero tests for Modal, Temporal, or Bimodal logic**. While theorem provers are self-verifying (compilation = correctness), PR reviewers may ask for:
- Example computations (e.g., decidability procedure on concrete formulas)
- `#check`/`#eval` demonstrations that key theorems have the expected types
- Integration tests verifying the main completeness theorems can be applied

### 7. `lake shake` is Commented Out in CI (LOW-MEDIUM)

The CI workflow has `lake shake` commented out:
```yaml
#- name: "lake shake"
#  run: |
#    set -e
#    lake shake --add-public --keep-implied --keep-prefix Cslib
```
This means import minimization is not enforced. PRs submitted with redundant imports will pass CI. Running `lake shake` locally before submission would pre-empt reviewer comments about unnecessary imports.

### 8. CODEOWNERS Has No Logic Module Owners (LOW)

The `.github/CODEOWNERS` file defines ownership for:
- `*` → @fmontesi @chenson2018 (global)
- `/Cslib/Languages/LambdaCalculus/` → @chenson2018
- `/.github/workflows` and `/scripts` → @kim-em @fmontesi @chenson2018

But there are **no specific owners for `Foundations/Logic/`, `Logics/Modal/`, `Logics/Temporal/`, or `Logics/Bimodal/`**. This means PRs will go to global maintainers by default. Not a blocker, but adding a CODEOWNERS entry for the logic modules would help route reviews.

### 9. PR Sequence Feasibility — Generally Sound (VALIDATION)

The import analysis confirms the PR sequence is feasible:
- **Modal ↮ Temporal**: No cross-imports — PR2 and PR3 can be parallel ✓
- **Foundations → Modal/Temporal**: Clean dependency — PR1 must land first ✓
- **No upward imports**: Bimodal doesn't leak into Modal/Temporal/Foundations ✓

**However**, the Foundations/Logic/Theorems/Temporal/ files create a subtle coupling: PR1 must include temporal-generic theorems (FrameConditions, TemporalDerived) even though they conceptually belong to the temporal logic domain. This is architecturally correct (they use generic typeclasses, not temporal-specific syntax) but the PR title/description should explain why temporal theorems appear in a "Foundations" PR.

## Recommended Approach

**Priority order for cleanup:**

1. **Fix the `sorry`** in Chronicle/Frame.lean — this is a hard blocker for CI
2. **Add copyright headers** to the 2 barrel files
3. **Fix or justify linter suppressions** — at minimum, fix `longLine` violations (22 instances) and remove the `set_option` overrides
4. **Update PR1 task description** to list all 16 files and correct the line count
5. **Complete the Temporal Metalogic barrel** — add missing Chronicle imports
6. **Run `lake shake` locally** and fix any redundant imports before PR submission
7. **Add basic test coverage** for at least one logic module (e.g., Modal decidability)
8. **Consider CODEOWNERS** entry for logic modules

## Evidence/Examples

- Copyright check: `head -3 Cslib/Logics/Modal/Metalogic.lean` shows `import` with no preceding header
- Sorry: `grep -rn sorry Cslib/Logics/Temporal/` → `Chronicle/Frame.lean:105`
- Missing barrel imports: `diff` of Chronicle directory vs Metalogic.lean imports
- CI config: `lean_action_ci.yml` shows `--wfail --iofail` build flags and commented-out `lake shake`
- Linter overrides: `grep -rn "set_option linter" | wc -l` → 61 in PR-relevant modules

## Confidence Level

- **High** on findings 1-5 (verified by direct file inspection and CI config review)
- **Medium** on findings 6-8 (based on CSLib conventions and typical Mathlib-adjacent PR review norms)
- **High** on finding 9 (verified by import graph analysis)
