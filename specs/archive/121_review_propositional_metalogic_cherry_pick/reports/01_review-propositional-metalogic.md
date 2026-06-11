# Research Report: Propositional Hilbert Metalogic and ND Equivalence Review

Session: sess_1781192410_b56b66

## 1. File Inventory

### 1.1 Propositional Hilbert System Files (on main)

**Proof System Infrastructure** (core definitions):
| File | Lines | Purpose |
|------|-------|---------|
| `Logics/Propositional/Defs.lean` | ~60 | Formula type (`atom \| bot \| imp`), abbreviations |
| `Logics/Propositional/ProofSystem/Axioms.lean` | 106 | `PropositionalAxiom`, `IntPropAxiom`, `MinPropAxiom`, subsumption |
| `Logics/Propositional/ProofSystem/Derivation.lean` | 163 | `DerivationTree Axioms`, `Deriv`, `Derivable`, `propDerivationSystem` |
| `Logics/Propositional/ProofSystem/Instances.lean` | 89 | `ClassicalHilbert` instance for `HilbertCl` |
| `Logics/Propositional/ProofSystem/IntMinInstances.lean` | 108 | `IntuitionisticHilbert`/`MinimalHilbert` instances for `HilbertInt`/`HilbertMin` |

**Metalogic** (soundness, completeness, deduction theorem, MCS):
| File | Lines | Purpose |
|------|-------|---------|
| `Logics/Propositional/Metalogic/DeductionTheorem.lean` | 216 | Parameterized deduction theorem (well-founded recursion on height) |
| `Logics/Propositional/Metalogic/MCS.lean` | 161 | Parameterized MCS properties (Lindenbaum, closed-under-derivation, etc.) |
| `Logics/Propositional/Metalogic/Soundness.lean` | 86 | Classical soundness: `Derivable PropositionalAxiom phi -> Tautology phi` |
| `Logics/Propositional/Metalogic/Completeness.lean` | 295 | Classical completeness via canonical model construction |
| `Logics/Propositional/Metalogic/IntSoundness.lean` | 102 | Intuitionistic soundness: `Derivable IntPropAxiom phi -> IValid phi` |
| `Logics/Propositional/Metalogic/IntLindenbaum.lean` | 325 | DCCS extension lemma + implication witness for intuitionistic logic |
| `Logics/Propositional/Metalogic/IntCompleteness.lean` | 127 | Intuitionistic completeness via canonical Kripke model |
| `Logics/Propositional/Metalogic/MinSoundness.lean` | 95 | Minimal soundness: `Derivable MinPropAxiom phi -> MValid phi` |
| `Logics/Propositional/Metalogic/MinLindenbaum.lean` | 276 | DCCS extension for minimal logic |
| `Logics/Propositional/Metalogic/MinCompleteness.lean` | 143 | Minimal completeness via canonical Kripke model |

**Semantics**:
| File | Lines | Purpose |
|------|-------|---------|
| `Logics/Propositional/Semantics/Basic.lean` | 47 | `Valuation`, `Evaluate`, `Tautology` (bivalent) |
| `Logics/Propositional/Semantics/Kripke.lean` | 134 | `KripkeModel`, `IForces`, `IValid`, `MValid`, persistence |

### 1.2 Natural Deduction Equivalence Files

| File | Lines | Purpose |
|------|-------|---------|
| `Logics/Propositional/NaturalDeduction/Basic.lean` | 345 | Standalone ND system (sequent-style, `Theory.Derivation`) |
| `Logics/Propositional/NaturalDeduction/FromHilbert.lean` | 302 | ND-flavored wrappers over Hilbert (`impI`, `impE`, `botE`, etc.) |
| `Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` | 559 | Derived connective rules in Hilbert (neg, top, and, or, iff) |
| `Logics/Propositional/NaturalDeduction/DerivedRules.lean` | 386 | Derived rules in standalone ND system |
| `Logics/Propositional/NaturalDeduction/Equivalence.lean` | 232 | Extensional equivalence: `hilbert_iff_nd`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl` |

### 1.3 Cross-Logic Embedding Files

| File | Lines | Purpose |
|------|-------|---------|
| `Logics/Modal/FromPropositional.lean` | 103 | `toModal` embedding + semantic coherence theorem |
| `Logics/Temporal/FromPropositional.lean` | 56 | `toTemporal` embedding (structural only) |

### 1.4 Shared Foundation Files (modified)

| File | Relevant Changes |
|------|-----------------|
| `Foundations/Logic/ProofSystem.lean` | Tag types `HilbertInt`, `HilbertMin` (propositional); also modal bundled classes (out of scope) |
| `Foundations/Logic/Theorems/Propositional/Core.lean` | Stratified to `MinimalHilbert` base (task 88) |
| `Foundations/Logic/Theorems/Propositional/Connectives.lean` | Stratified to `MinimalHilbert` base (task 88) |
| `Foundations/Data/ListHelpers.lean` | `removeAll` helpers used by deduction theorem |

**Total propositional-specific code**: ~4,300 lines across 22 Lean files.

## 2. Quality Review Against CONTRIBUTING.md

### 2.1 Style and Documentation

**Positive findings:**
- All files have proper copyright headers (Apache 2.0)
- All files use `module` keyword (ensuring `Cslib.Init` linting)
- All definitions and theorems have `/--` docstrings
- Module headers use `/-! ... -/` format with sections listing main results and references
- Variable names are domain-appropriate (phi, psi, chi for formulas; S, M for sets; v for valuations)
- Proofs are readable: structural recursion, well-named intermediate steps
- No `sorry` found in any file
- No double blank lines
- References to CZ (Chagrov-Zakharyaschev) textbook are included where appropriate

**Minor style observations (non-blocking):**
- The `private def h_implyK` / `h_implyS` pattern in `Completeness.lean` and `IntLindenbaum.lean` is repeated; could be a shared pattern but is acceptable as-is
- Some files use `by` tactic blocks where term-mode might be slightly more concise, but this follows the "readable proofs" guideline

### 2.2 Design Principles (Reuse)

**Excellent reuse patterns:**
- `DerivationTree` is parameterized over `Axioms : PL.Proposition Atom -> Prop`, enabling reuse across classical, intuitionistic, and minimal systems
- `propDerivationSystem Axioms` provides a generic `DerivationSystem` instance
- `deductionTheorem` takes explicit `h_implyK`/`h_implyS` witnesses rather than requiring a specific axiom type
- MCS properties (`prop_lindenbaum`, `prop_closed_under_derivation`, etc.) are all parameterized
- The ND equivalence `hilbert_iff_nd` requires K, S, and EFQ witnesses, correctly excluding minimal logic
- Kripke semantics `IForces` is parameterized by `bot_forces`, unifying intuitionistic and minimal interpretations

**Architecture follows the modal pattern:**
- The propositional metalogic mirrors the modal metalogic structure (DerivationTree, DeductionTheorem, MCS, Soundness, Completeness)
- This is consistent with CSLib's reuse philosophy

### 2.3 Imports

- All files use `public import` correctly
- Import chains are clean: `Axioms -> Derivation -> DeductionTheorem -> MCS -> Soundness/Completeness`
- No circular dependencies detected
- `Semantics/Kripke.lean` correctly imports from Mathlib (`Order.Defs.PartialOrder`, `Order.Defs.Unbundled`)

### 2.4 Minimal Logic ND Exclusion

The task specification states: "Minimal logic has no ND equivalent and is excluded from the ND equivalence."

This is correctly implemented:
- `hilbert_iff_nd` requires three witnesses: `h_K`, `h_S`, `h_EFQ`
- `MinPropAxiom` only provides `implyK` and `implyS` (no `efq`)
- Only `hilbert_iff_nd_int` (intuitionistic) and `hilbert_iff_nd_cl` (classical) instantiations exist
- No `hilbert_iff_nd_min` is defined, as intended

### 2.5 Potential Issues

**Issue 1: `@[expose]` attribute usage**
All propositional files use `@[expose] public section`. This is consistent with the existing codebase pattern (modal, temporal, bimodal files all use it). Not a problem per se, but worth noting for the PR description since upstream reviewers may have preferences.

**Issue 2: `attribute [local instance] Classical.propDecidable`**
Used in `DeductionTheorem.lean`, `IntLindenbaum.lean`, and `MinLindenbaum.lean`. This is standard for classical reasoning in `by_cases` and is consistent with the modal metalogic pattern. Acceptable.

**Issue 3: `noncomputable` usage**
Several definitions (`deductionWithMem`, `deductionTheorem`, `impI`, ND-to-Hilbert translations) are marked `noncomputable` due to `Classical.propDecidable`. This is expected and consistent with the modal pattern.

## 3. Branch State Analysis

### 3.1 Current State of `pr1/foundations-logic`

The branch has 4 custom commits on top of a merged upstream base:

1. `2d5ea2c6` -- **Squashed commit** containing tasks 85-89 content:
   - Hilbert-ND equivalence (task 87)
   - ND derived rules and Hilbert derived rules (task 89)
   - Intuitionistic hierarchy stratification (task 88)
   - Lint fixes (task 86)
   - `Proposition.iff` (task 89)

2. `d48cb841` -- Remove unused `DecidableEq` parameter from `FromHilbert.lean`
3. `f72a6696` -- Reorder `Cslib.lean` imports per `mk_all` canonical order
4. `53ba7106` -- Merge of `upstream/main` (brings in modal logical equivalence + CODEOWNERS)

### 3.2 What Is Missing from the Branch

**11 NEW files** not on the branch (exist only on main):
1. `Logics/Propositional/Semantics/Basic.lean` (bivalent semantics)
2. `Logics/Propositional/Semantics/Kripke.lean` (Kripke semantics)
3. `Logics/Propositional/ProofSystem/IntMinInstances.lean` (Int/Min instances)
4. `Logics/Propositional/Metalogic/Soundness.lean` (classical)
5. `Logics/Propositional/Metalogic/Completeness.lean` (classical)
6. `Logics/Propositional/Metalogic/IntSoundness.lean` (intuitionistic)
7. `Logics/Propositional/Metalogic/IntLindenbaum.lean` (intuitionistic)
8. `Logics/Propositional/Metalogic/IntCompleteness.lean` (intuitionistic)
9. `Logics/Propositional/Metalogic/MinSoundness.lean` (minimal)
10. `Logics/Propositional/Metalogic/MinLindenbaum.lean` (minimal)
11. `Logics/Propositional/Metalogic/MinCompleteness.lean` (minimal)

**2 NEW cross-logic files**:
12. `Logics/Modal/FromPropositional.lean` (embedding + semantic coherence)
13. `Logics/Temporal/FromPropositional.lean` (embedding)

**8 MODIFIED files** (branch version is behind main):
1. `Logics/Propositional/ProofSystem/Axioms.lean` -- needs `IntPropAxiom`, `MinPropAxiom`, subsumption theorems
2. `Logics/Propositional/ProofSystem/Derivation.lean` -- parameterized `DerivationTree`, `Deriv`, `Derivable`
3. `Logics/Propositional/ProofSystem/Instances.lean` -- minor updates
4. `Logics/Propositional/Metalogic/DeductionTheorem.lean` -- parameterized over Axioms
5. `Logics/Propositional/Metalogic/MCS.lean` -- parameterized MCS properties
6. `Logics/Propositional/NaturalDeduction/FromHilbert.lean` -- parameterized over Axioms
7. `Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` -- parameterized, split into intuitionistic/classical layers
8. `Logics/Propositional/NaturalDeduction/Equivalence.lean` -- parameterized `hilbert_iff_nd`

**1 MODIFIED shared file** (out-of-scope changes mixed in):
- `Foundations/Logic/ProofSystem.lean` -- has modal bundled class additions (tasks 92, 100) mixed with propositional tag types (task 113)

**Cslib.lean** needs 17 additional import lines for propositional files.

### 3.3 Task Provenance

The missing work comes from these tasks on main:
| Task | Description | Files |
|------|-------------|-------|
| 113 | Core parameterization of proof system over Axioms | Axioms, Derivation, DeductionTheorem, MCS, Instances, IntMinInstances |
| 114 | Classical semantics and soundness/completeness | Semantics/Basic, Soundness, Completeness, MCS updates |
| 115 | (Kripke semantics -- folded into 114-118 integration) | Semantics/Kripke |
| 116 | Intuitionistic soundness/completeness | IntSoundness, IntLindenbaum, IntCompleteness |
| 117 | Minimal soundness/completeness | MinSoundness, MinLindenbaum, MinCompleteness |
| 118 | Integration: Cslib.lean imports + FromPropositional embeddings | Modal/FromPropositional, Temporal/FromPropositional |
| 120 | Parameterize ND equivalence over Axioms | FromHilbert, HilbertDerivedRules, Equivalence |

## 4. Cherry-Pick Strategy

### 4.1 Why Individual Cherry-Picks Won't Work Cleanly

The branch already has a **squashed commit** (`2d5ea2c6`) containing tasks 85-89 content. On main, these same changes exist as individual commits. Tasks 113 and 120 then modified the same files further (parameterization). Cherry-picking tasks 113 and 120 from main would conflict with the squashed commit because the base state differs.

Additionally, `Foundations/Logic/ProofSystem.lean` has modal class additions (tasks 92, 100) interleaved with propositional tag types -- cherry-picking these commits would bring modal content that is out of scope for the propositional PR.

### 4.2 Recommended Approach: Diff-Based File Copy

**Strategy**: Copy the current state of each propositional file from `main` to `pr1/foundations-logic`, rather than cherry-picking individual commits. This avoids conflicts and produces the exact intended state.

**Step-by-step plan**:

**Phase 1: Add new files** (no conflicts possible)
Copy these 13 files from main to the branch:
- All 11 new propositional files (Semantics, Metalogic, IntMinInstances)
- `Logics/Modal/FromPropositional.lean`
- `Logics/Temporal/FromPropositional.lean`

**Phase 2: Update modified files** (overwrite branch versions with main versions)
Replace these 8 files on the branch with their main versions:
- `ProofSystem/Axioms.lean`, `Derivation.lean`, `Instances.lean`
- `Metalogic/DeductionTheorem.lean`, `MCS.lean`
- `NaturalDeduction/FromHilbert.lean`, `HilbertDerivedRules.lean`, `Equivalence.lean`

**Phase 3: Selectively update shared files**
- `Foundations/Logic/ProofSystem.lean`: Add ONLY the propositional tag types (`HilbertInt`, `HilbertMin`) without the modal bundled classes. The propositional files do not depend on modal classes.
- `Foundations/Data/ListHelpers.lean`: Copy from main (minor changes only)

**Phase 4: Update Cslib.lean**
Add the 17 missing propositional import lines. Use `lake exe mk_all --module` to verify.

**Phase 5: Verification**
- Run `lake build` on the branch to verify everything compiles
- Run `lake exe checkInitImports` to verify Init imports
- Run `lake shake --add-public --keep-implied --keep-prefix` to verify minimized imports
- Run `lake exe lint-style` for text linting

### 4.3 Scope Boundaries

**IN SCOPE** (propositional Hilbert metalogic + ND equivalence):
- All files under `Logics/Propositional/`
- `Logics/Modal/FromPropositional.lean`
- `Logics/Temporal/FromPropositional.lean`
- Propositional tag types in `Foundations/Logic/ProofSystem.lean`

**OUT OF SCOPE** (should NOT be cherry-picked):
- Modal bundled classes in `Foundations/Logic/ProofSystem.lean` (tasks 92, 100)
- Modal metalogic files (tasks 100-111, 119)
- Bimodal propositional embedding files (`Bimodal/Embedding/PropositionalEmbedding.lean`, etc.)
- `Temporal/Metalogic/PropositionalHelpers.lean` (temporal-specific, not propositional metalogic)
- Any `specs/` task artifacts

### 4.4 Commit Strategy for the Branch

Recommended: Create 2-3 well-organized commits on `pr1/foundations-logic`:

1. **`feat(Logics/Propositional): parameterized proof system and classical/int/min metalogic`**
   - All new and modified proof system files
   - Semantics files
   - All metalogic files (soundness, completeness for all three logics)

2. **`feat(Logics/Propositional): parameterized ND equivalence with intuitionistic/classical corollaries`**
   - Updated NaturalDeduction files (FromHilbert, HilbertDerivedRules, Equivalence)

3. **`feat(Logics): propositional-to-modal/temporal embedding and integration`**
   - FromPropositional embedding files
   - Cslib.lean import updates
   - ProofSystem.lean tag type additions

## 5. PR Readiness Assessment

### 5.1 What Is Ready

- All propositional metalogic proofs compile on main (verified by CI)
- No `sorry` in any file
- Documentation is thorough with module headers, docstrings, and references
- The three-logic hierarchy (minimal < intuitionistic < classical) is clean:
  - Axiom subsumption theorems prove the containment
  - Shared parameterized infrastructure avoids code duplication
  - ND equivalence correctly excludes minimal logic
- Kripke semantics properly distinguishes intuitionistic (`bot_forces = fun _ => False`) from minimal (arbitrary upward-closed `bot_forces`)

### 5.2 Potential PR Review Concerns

1. **PR scope**: ~4,300 lines of new propositional code. May need to be split for review. Consider proposing the proof system infrastructure + classical metalogic as a first PR, with int/min as follow-ups.

2. **`@[expose]` attribute**: Used throughout but may not be standard in upstream CSLib. Check with maintainers.

3. **Propositional tag types in ProofSystem.lean**: Adding `HilbertInt` and `HilbertMin` tag types to the shared Foundations file is architecturally sound but changes a widely-imported file. Reviewers may want these in a separate propositional file.

4. **AI disclosure**: Per CONTRIBUTING.md, the PR description should note that AI tools were used.

### 5.3 Recommended PR Title

```
feat(Logics/Propositional): Hilbert system metalogic, Kripke semantics, and ND equivalence
```
