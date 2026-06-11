# Teammate C (Critic) Findings — Task 60: PR2 Modal Metalogic

**Date**: 2026-06-10
**Role**: Critic — gaps, shortcomings, and PR blockers

---

## Key Findings (by severity)

### SEVERITY: HIGH — Structural / Scope Issues

#### 1. Modal Logic Covers S5 Only — Other Cube Systems Lack Proof Systems

The `Modal/Cube.lean` defines all 15 modal logics semantically (K, T, B, D, 4, 5, S4, S5, D4, D5, D45, DB, TB, KB5, K45), but the Hilbert proof system (`Modal/Metalogic/DerivationTree.lean`) is hardcoded to S5 axioms only (K + T + 4 + B). Completeness and soundness are proved exclusively for S5 frames (reflexive, transitive, Euclidean).

**Impact**: The PR provides completeness for exactly 1 of 15 cube systems. This is not a blocker — S5 is the natural starting point — but should be clearly documented as the scope.

**Recommendation**: Add a note in the module docstring of `Metalogic.lean` or `Completeness.lean` stating that only S5 completeness is currently proven, and that extending to K, T, S4, etc. via parametric axiom systems is future work.

#### 2. Modal Metalogic Uses Concrete DerivationTree, Not Typeclass Instances

Unlike Temporal and Bimodal (which register `InferenceSystem`, `ClassicalHilbert`, `HasAxiom*` instances), Modal's metalogic uses a concrete `modalDerivationSystem : DerivationSystem (Proposition Atom)` that connects to the generic `Consistency.lean` framework directly. This works but means Modal can't plug into the `InferenceSystem` typeclass hierarchy that Temporal and Bimodal use.

**Impact**: Architectural inconsistency across the logics. Not a PR blocker, but a reviewer familiar with the Temporal/Bimodal pattern may question why Modal diverges.

**Recommendation**: Document this as a known design choice. A future task could align Modal with the typeclass pattern (adding `ProofSystem/Instances.lean` like Temporal and Bimodal have).

### SEVERITY: MEDIUM — Sorry Audit Results

#### 3. No Sorries in Propositional, Modal, or Temporal

All files under `Cslib/Logics/Propositional/`, `Cslib/Logics/Modal/`, and `Cslib/Logics/Temporal/` are **completely sorry-free**. This is excellent for PR quality.

#### 4. Bimodal Has 25 Actual Sorries — All Documented and Scoped

All 25 `sorry` instances in Bimodal are:
- **BXCanonical/Chronicle/ChronicleToCountermodel.lean** (12): blocked on task 36 (discrete pipeline)
- **Bundle/SuccRelation.lean** (7): blocked on task 37
- **Bundle/UntilSinceCoherence.lean** (2): blocked on task 37
- **BXCanonical/Frame.lean** (1): blocked on task 36
- **BXCanonical/Completeness/Dense.lean** (1): blocked on task 36
- **BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean** (1): blocked on task 36
- **BXCanonical/Chronicle/PointInsertion.lean** (1): comment mentions sorry stubs

All are documented with blocking task references. These are in the BXCanonical (advanced) and Bundle (successor relation) modules, which appear to be ongoing work for dense/discrete completeness — not the core modal metalogic PR scope.

**Recommendation**: If the PR scope includes Bimodal, clearly mark these modules as WIP with a comment at the top of each file, or exclude them from the PR entirely.

### SEVERITY: MEDIUM — Untracked File

#### 5. HilbertDerivedRules.lean Is Untracked and Unimported

`Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` (447 lines):
- **Sorry-free**: No `sorry` found.
- **Not imported**: No file in the codebase imports it.
- **Content**: Provides derived intro/elim rules (`hilbertNegI`, `hilbertNegE`, `hilbertTopI`, `hilbertAndI`, `hilbertAndE1`, `hilbertAndE2`, `hilbertOrI1`, `hilbertOrI2`, `hilbertOrE`, `hilbertDne`, `hilbertIffI`, `hilbertIffE1`, `hilbertIffE2`) for Lukasiewicz-encoded connectives in the Hilbert proof system.

**Impact**: This file provides useful infrastructure but is currently dead code. If included in the PR, it should be imported somewhere (perhaps from a barrel import or a test file). If excluded, it should be gitignored or removed.

**Decision needed**: Include in PR (and add import) or exclude (and .gitignore).

### SEVERITY: LOW — Naming Conventions

#### 6. Namespace Consistency Is Good Across Logics

- Propositional: `Cslib.Logic.PL`
- Modal: `Cslib.Logic.Modal`
- Temporal: `Cslib.Logic.Temporal`
- Bimodal: `Cslib.Logic.Bimodal` (with deeper nesting: `.Metalogic.Core`, `.Metalogic.BXCanonical`, etc.)

This is clean and consistent. The deeper nesting in Bimodal reflects its larger scope (51K lines vs 1.8K for Modal).

#### 7. Modal Naming Follows Consistent Patterns

- Theorems: `truth_lemma`, `completeness`, `soundness`, `axiom_sound`
- MCS helpers: `mcs_box_closure`, `mcs_box_box`, `mcs_box_witness`, `mcs_neg_of_not_mem`
- Derivation types: `DerivationTree`, `Deriv`, `Derivable`

The `mcs_` prefix convention is consistent across Modal and is paralleled by `SetMaximalConsistent.` methods in Bimodal.

### SEVERITY: LOW — Documentation

#### 8. Module Documentation Is Thorough

Every file in `Cslib/Logics/Modal/Metalogic/` has comprehensive module docstrings with:
- `Main Results` section
- `Design` section
- `References` section

This exceeds typical Lean/Mathlib documentation standards. No action needed.

### SEVERITY: INFO — Codebase Scale

#### 9. Line Counts by Logic

| Logic | Files | Lines |
|-------|-------|-------|
| Propositional | 11 | 2,329 |
| Modal | 10 | 1,802 |
| Temporal | 35 | 13,783 |
| Bimodal | 127 | 51,185 |

Modal is the smallest logic by far. For a PR focused on "modal metalogic," the scope is tight and reviewable.

---

## Completeness Coverage Summary

| Logic | System | Soundness | Completeness | Sorries |
|-------|--------|-----------|--------------|---------|
| Propositional | Classical Hilbert | N/A (no semantics) | MCS framework | 0 |
| Modal | S5 | Yes (sorry-free) | Yes (sorry-free) | 0 |
| Temporal | BX (serial linear) | Yes (sorry-free) | Yes (sorry-free) | 0 |
| Bimodal | TM (tense+modal) | Yes (sorry-free) | Partial (BXCanonical has sorries) | 25 |

**Modal cube systems without completeness**: K, T, B, D, 4, 5, S4, D4, D5, D45, DB, TB, KB5, K45 (14 of 15).

---

## Recommended Approach

1. **PR scope clarity**: The PR should clearly state it covers S5 modal completeness, not the full modal cube. Document this limitation prominently.

2. **HilbertDerivedRules decision**: Either include and import, or exclude from PR. Don't leave it untracked.

3. **Bimodal sorries**: If Bimodal is in scope, add `/-! ## Status: Work in Progress -/` headers to files with sorries. If not in scope, exclude Bimodal entirely from the PR.

4. **No test files**: The only "test"-like file is `ExampleEventuallyZero.lean` (in Computability, not Logics). Consider adding a small example file demonstrating Modal S5 derivations (e.g., deriving `□p → p` from the axioms).

5. **No build verification was possible in this review**. A full `lake build` should be run before PR submission to catch unused imports, linter warnings, and universe issues.

---

## Evidence/Examples

### Sorry-free Modal Completeness (proof sketch)
The `completeness` theorem in `Modal/Metalogic/Completeness.lean` proves:
```
If φ is valid over all S5 frames, then Derivable φ
```
via contrapositive using Lindenbaum's lemma + canonical model + truth lemma. All helper lemmas (`canonical_refl`, `canonical_trans`, `canonical_eucl`, `truth_lemma`) are fully proven. No `sorry` anywhere in the proof chain.

### BXCanonical Sorry Pattern
All 15 sorries in BXCanonical reference tasks 36/37:
```lean
sorry  -- sorry: blocked on task 36 (discrete_embed_strictMono)
sorry  -- sorry: blocked on task 37
```
These are disciplined sorry-stubs with clear documentation, not abandoned proofs.

---

## Confidence Level

**High** — This review is based on direct grep/read of all source files. The sorry audit is exhaustive (no false negatives). The architectural observations are based on comparing file structures across all four logics.
