# Teammate A Findings: Conventions, Naming, and Style Alignment

**Task**: 82 — Systematic codebase review of Logics/ and Foundations/ for publication quality
**Angle**: Conventions, naming, and style alignment with CSLib norms
**Date**: 2026-06-10

## Key Findings

### 1. Namespace vs Directory Path Mismatch (HIGH severity)

All files in `Cslib/Foundations/Logic/` use namespace `Cslib.Logic.*` rather than `Cslib.Foundations.Logic.*`. Meanwhile, files in `Cslib/Logics/` also use namespace `Cslib.Logic.*`. This means the physical directory structure diverges from the namespace structure.

**Evidence**:
- `Cslib/Foundations/Logic/Axioms.lean` → `namespace Cslib.Logic.Axioms`
- `Cslib/Foundations/Logic/ProofSystem.lean` → `namespace Cslib.Logic`
- `Cslib/Foundations/Logic/InferenceSystem.lean` → `namespace Cslib.Logic`
- `Cslib/Logics/Modal/Basic.lean` → `namespace Cslib.Logic.Modal`
- `Cslib/Logics/Propositional/Defs.lean` → `namespace Cslib.Logic.PL`

The `Cslib.Logic` namespace is shared between files in two different top-level directories (`Foundations/Logic/` and `Logics/`), which may confuse contributors and maintainers.

**ORGANISATION.md alignment**: ORGANISATION.md shows `Cslib.Logic` at the top level under `Cslib` (not under `Cslib.Foundations`). However, the actual directory layout uses `Cslib/Foundations/Logic/` for shared infrastructure and `Cslib/Logics/` for specific logics. The ORGANISATION.md may need updating to reflect this split, or the directories should be reorganized.

**Confidence**: High

### 2. snake_case Theorem Names (MEDIUM severity)

Theorem and definition names across Foundations/Logic/ and Logics/ consistently use `snake_case`, which follows Mathlib convention. However, there is inconsistency within some files where `camelCase` appears mixed with `snake_case`.

**Consistent snake_case examples** (Mathlib-conformant):
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`: `efq_axiom`, `peirce_axiom`, `double_negation`, `efq_neg`, `lce_imp`, `rce_imp`
- `Cslib/Foundations/Logic/Theorems/Combinators.lean`: `imp_trans`, `b_combinator`, `combine_imp_conj`
- `Cslib/Logics/Modal/Metalogic/MCS.lean`: `modal_lindenbaum`, `modal_closed_under_derivation`, `mcs_mp_axiom`
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean`: `deduction_theorem`, `deduction_with_mem`

**Inconsistent mixing** (within Modal/Basic.lean):
- `five_rightEuclidean` — uses camelCase `rightEuclidean` after snake_case prefix
- `not_theoryEq_satisfies` — mixes snake_case with camelCase `theoryEq`
- `theoryEq_satisfies` — camelCase internal word

**Recommended approach**: If CSLib follows Mathlib convention strictly, `snake_case` for theorems is correct. The mixed instances (`rightEuclidean`, `theoryEq`) should be standardized. If CSLib is moving toward Lean 4 core `lowerCamelCase`, a systematic rename would be needed, but this conflicts with Mathlib norms.

**Confidence**: High (the inconsistency is real; the correct direction depends on project policy)

### 3. Missing Section Ends (MEDIUM severity)

9 files have `@[expose] public section` without matching `end` statements:

| File | Issue |
|------|-------|
| `Cslib/Logics/Bimodal/Metalogic/Separation.lean` | Missing `end` |
| `Cslib/Logics/Bimodal/Metalogic/Core.lean` | Missing `end` |
| `Cslib/Logics/Bimodal/Metalogic/Decidability.lean` | Missing `end` |
| `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP.lean` | Missing `end` |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Completeness.lean` | Missing `end` |
| `Cslib/Logics/Temporal/ProofSystem.lean` | Missing `end` |
| `Cslib/Logics/Bimodal/Metalogic/Bundle/FMCS.lean` | Missing `end` |
| `Cslib/Logics/Temporal/Theorems.lean` | Missing `end` |
| `Cslib/Logics/Modal/Metalogic.lean` | Missing `end` |

With the `module` keyword, the `@[expose] public section` is file-scoped and doesn't strictly require an `end`. However, for consistency and explicit scope control, matching section/end pairs are preferable.

**Confidence**: Medium (may be intentional with `module` keyword behavior)

### 4. Module Docstring Coverage (LOW severity)

Module docstrings (`/-! # Title ... -/`) are well-covered in Foundations/Logic/. Only one file in the Logics/ area lacks them:

- `Cslib/Logics/Temporal/Metalogic.lean` — missing module docstring

All other sampled files in Modal/, Propositional/, and Temporal/ have appropriate module docstrings.

**Confidence**: High

### 5. Line Length Violations (LOW severity)

Minor violations of the 100-character line limit (Mathlib convention):

- `Cslib/Logics/Modal/Metalogic/Soundness.lean`: 1 line
- `Cslib/Logics/Modal/Metalogic/MCS.lean`: 1 line
- `Cslib/Logics/Modal/Metalogic/Completeness.lean`: 2 lines

No violations found in Foundations/Logic/ or Propositional/ files.

**Confidence**: High

### 6. Comment Density and Style (LOW severity)

The Foundations/Logic/Theorems files have extensive inline comments explaining proof steps (e.g., `Theorems/Propositional/Core.lean` lines 83-109, `Theorems/Modal/S5.lean` throughout). This is generally good for publication quality and follows CONTRIBUTING.md's guidance to "make proofs easy to follow."

However, some comments use informal abbreviations:
- `-- Abbreviations from Axioms: neg' φ = φ → ⊥, conj' φ ψ = ...` (S5.lean:65-66)
- `-- Abbreviations for readability` (Core.lean:53)

These could be formalized as proper doc comments or removed if the naming is self-explanatory.

**Confidence**: Medium

### 7. Import Patterns (LOW severity)

All files use `public import` consistently. The `module` keyword is used uniformly across all 203 Lean files. No instances of `import` without `public` were found in the reviewed files, which is consistent with the `module` keyword pattern.

Some files import Mathlib modules:
- `Cslib/Logics/Modal/Basic.lean` imports 4 Mathlib modules (`Data.Set.Basic`, `Order.Defs.Unbundled`, `Data.Relation`, `Logic.Nonempty`)
- `Cslib/Logics/Propositional/Defs.lean` imports 3 Mathlib modules

These seem appropriate and not excessive. Running `lake shake` would confirm minimality.

**Confidence**: Medium (would need `lake shake` to confirm no unused imports)

### 8. `@[expose] public section` Pattern (INFORMATIONAL)

The `@[expose] public section` pattern is used in ~20+ files across both Foundations/Logic/ and Logics/. This appears to be a CSLib-specific convention not found in Mathlib. It is used consistently and appears to mark all definitions as public/exported.

This is not a violation but worth noting as a CSLib-specific convention that new contributors should be aware of.

**Confidence**: High

## Recommended Approach

### Priority 1: Decide on naming convention direction
The most impactful decision is whether to standardize on:
- **snake_case** (Mathlib convention, current majority pattern) — minimal change
- **lowerCamelCase** (Lean 4 core convention, user's stated preference) — large rename effort

If choosing camelCase, a systematic rename script could handle most cases. The inconsistent mixing (e.g., `five_rightEuclidean` vs `t_refl`) should be resolved either way.

### Priority 2: Add missing section ends
Quick fix for 9 files. Low risk, improves consistency.

### Priority 3: Address namespace/directory mismatch
This requires a policy decision:
- Option A: Update ORGANISATION.md to document the current split
- Option B: Restructure directories to match namespaces (risky, breaks imports)
- Option C: Update namespaces to match directory paths (also breaks imports)

### Priority 4: Minor cleanup
- Fix 4 line-length violations
- Add module docstring to `Temporal/Metalogic.lean`
- Standardize comment style in theorem proof blocks

## Evidence/Examples

### snake_case vs camelCase examples (current state)

| File | Identifier | Style | Suggested camelCase |
|------|-----------|-------|-------------------|
| Combinators.lean:53 | `imp_trans` | snake | `impTrans` |
| Combinators.lean:80 | `b_combinator` | snake | `bCombinator` |
| Core.lean:59 | `efq_axiom` | snake | `efqAxiom` |
| Core.lean:78 | `double_negation` | snake | `doubleNegation` |
| Core.lean:209 | `lce_imp` | snake | `lceImp` |
| MCS.lean:59 | `modal_lindenbaum` | snake | `modalLindenbaum` |
| MCS.lean:110 | `mcs_box_closure` | snake | `mcsBoxClosure` |
| Modal/Basic.lean:329 | `five_rightEuclidean` | **mixed** | `fiveRightEuclidean` |
| Modal/Basic.lean:215 | `not_theoryEq_satisfies` | **mixed** | `notTheoryEqSatisfies` |

### Namespace mismatch examples

| File Path | Namespace Used | Expected from Path |
|-----------|---------------|-------------------|
| `Cslib/Foundations/Logic/Axioms.lean` | `Cslib.Logic.Axioms` | `Cslib.Foundations.Logic.Axioms` |
| `Cslib/Foundations/Logic/ProofSystem.lean` | `Cslib.Logic` | `Cslib.Foundations.Logic` |
| `Cslib/Logics/Modal/Basic.lean` | `Cslib.Logic.Modal` | `Cslib.Logics.Modal` |
| `Cslib/Logics/Propositional/Defs.lean` | `Cslib.Logic.PL` | `Cslib.Logics.Propositional` |

## Confidence Level

- Naming convention findings: **High** — verified across multiple files
- Missing section ends: **High** — mechanically checked
- Namespace mismatch: **High** — verified by grep
- Import analysis: **Medium** — visual inspection only, not verified with `lake shake`
- Comment style: **Medium** — subjective assessment
