# Research Report: Sub-PR 1.1 Hilbert Hierarchy Refactoring

- **Task**: 125 - Sub-PR 1.1: 3-tier Hilbert hierarchy refactoring
- **Started**: 2026-06-11T23:10:00Z
- **Completed**: 2026-06-11T23:55:00Z
- **Effort**: ~45 minutes
- **Dependencies**: Task 124 (PR 1 decomposition, completed)
- **Sources/Inputs**:
  - `specs/125_subpr_1_1_hilbert_hierarchy_refactoring/reports/01_hilbert-hierarchy-spec.md`
  - `pr1/foundations-logic` branch (source of changes)
  - `main` branch (local, all hierarchy changes already merged)
  - `upstream/main` (leanprover/cslib, target for sub-PR)
  - PR #633 on leanprover/cslib (open monolithic PR)
- **Artifacts**:
  - `specs/125_subpr_1_1_hilbert_hierarchy_refactoring/reports/02_research-report.md` (this file)
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- **11 of the 13 spec files are already identical** between local `main` and `pr1/foundations-logic`; only `ProofSystem.lean` (main has extra modal classes) and `Defs.lean` (PR branch has bib reference) differ. The extraction strategy of "copy from PR branch" is equivalent to "copy from local main" for most files.
- **12 of 13 spec files are NEW to upstream/main** (do not exist there). The spec's claim that these are "modifications to files already in upstream main" is incorrect. Only `Defs.lean` exists upstream, and even that file requires a fundamental refactoring (Proposition type primitives change from `and/or/impl` to `bot/imp`).
- **5 additional dependency files** not listed in the spec are required for the build to succeed: `Connectives.lean`, `Axioms.lean`, `Consistency.lean`, `DeductionHelpers.lean`, and `ProofSystem/Axioms.lean`.
- **`Theorems.lean` (barrel file) cannot be included as-is** because it imports `Modal.Basic`, `Modal.S5`, and `Temporal.TemporalDerived` which belong to other sub-PRs.
- **`Defs.lean` changes break `NaturalDeduction/Basic.lean`** upstream (removes `and`/`or`/`impl` constructors, adds `bot`/`imp`), requiring `NaturalDeduction/Basic.lean` modifications in this sub-PR.
- **Recommended approach**: Redefine sub-PR 1.1 scope as the full foundation layer needed for all subsequent sub-PRs. Use local `main` as the source (not `pr1/foundations-logic`). Exclude modal/temporal-specific content.

## Context and Scope

### Branch Topology

```
upstream/main (leanprover/cslib)
    |
    +-- pr1/foundations-logic (forked before tasks 92, 100)
    |       |-- 39 files changed vs upstream
    |       `-- PR #633 (open, monolithic)
    |
    +-- main (local, origin/main)
            |-- All pr1 changes merged (via tasks 85-122)
            |-- Additional modal classes (tasks 92, 100)
            `-- Task 124 created sub-PR specs
```

### Key Discovery: What Upstream Actually Has

The spec was written relative to local `main`, which already contains all the hierarchy
changes. But upstream (`leanprover/cslib`) has none of this author's foundation logic work.

| File Category | On upstream/main? | On local main? | On pr1/foundations-logic? |
|---------------|-------------------|----------------|--------------------------|
| `Foundations/Logic/ProofSystem.lean` | NO | YES (w/ extra modal) | YES |
| `Foundations/Logic/Theorems/*.lean` | NO | YES | YES (identical) |
| `Foundations/Data/ListHelpers.lean` | NO | YES | YES (identical) |
| `Logics/Propositional/Defs.lean` | YES (old version) | YES (refactored) | YES (refactored + bib) |
| `Logics/Propositional/ProofSystem/*.lean` | NO | YES | YES (identical) |
| `Logics/Propositional/Metalogic/*.lean` | NO | YES | YES (identical) |
| `Foundations/Logic/Connectives.lean` | NO | YES | YES (identical) |
| `Foundations/Logic/Axioms.lean` | NO | YES | YES (identical) |
| `Foundations/Logic/Metalogic/*.lean` | NO | YES | YES (identical) |

## Findings

### Finding 1: The Proposition Type Refactoring

Upstream `Proposition` type (PR #89):
```
inductive Proposition
  | atom | and | or | impl
```

Local main `Proposition` type (since task 85):
```
inductive Proposition
  | atom | bot | imp
-- and, or, neg, top, iff are derived abbreviations
```

This is a fundamental breaking change. All downstream files (Axioms.lean, DerivationTree, etc.)
use `.imp` and `.bot` which do not exist in the upstream `Proposition` type.

**Impact**: `NaturalDeduction/Basic.lean` on upstream uses `andI`, `andE1`, `orI1`, `orE`,
`implI`, `implE` constructors. These are removed on local main and replaced with `impI`,
`impE`, `botE`.

### Finding 2: 3-Tier Hierarchy Already on Local Main

The MinimalHilbert/IntuitionisticHilbert/ClassicalHilbert hierarchy was introduced by
tasks 88 and later, and is fully present on local `main`:

```lean
class MinimalHilbert extends ModusPonens, HasAxiomImplyK, HasAxiomImplyS
class IntuitionisticHilbert extends MinimalHilbert, HasAxiomEFQ
class ClassicalHilbert extends IntuitionisticHilbert, HasAxiomPeirce
```

Tag types `Propositional.HilbertMin`, `Propositional.HilbertInt`, `Propositional.HilbertCl`
are all present. The `HasAxiomDNE` class was removed (DNE is derived in `Core.lean`).

All theorem stratification (minimal/intuitionistic/classical sections) is present in `Core.lean`
and `Connectives.lean`. The `BigConj.lean` uses `ClassicalHilbert`, `Combinators.lean` uses
`MinimalHilbert`.

### Finding 3: ProofSystem.lean -- Main Has More Than PR Branch

Local `main` has additional modal Hilbert classes not on `pr1/foundations-logic`:
- `ModalTHilbert`, `ModalDHilbert`, `ModalS4Hilbert`, `ModalBHilbert`
- `ModalK4Hilbert`, `ModalK5Hilbert`, `ModalK45Hilbert`, `ModalTBHilbert`
- `ModalKB5Hilbert`, `ModalD4Hilbert`, `ModalD5Hilbert`, `ModalD45Hilbert`, `ModalDBHilbert`
- Corresponding tag types for each

These were added by tasks 92 and 100 after the PR branch was forked. For sub-PR 1.1, these
modal classes should be EXCLUDED (they belong to sub-PR 1.5 or the modal logic PRs). The
sub-PR should include the 3-tier propositional hierarchy but NOT the extended modal hierarchy.

**Implication**: Cannot blindly copy `ProofSystem.lean` from either local main or pr1 branch.
Must curate the content to include only what's in scope for sub-PR 1.1.

### Finding 4: Theorems.lean Barrel Has Cross-PR Imports

The barrel file `Theorems.lean` imports:
```lean
public import Cslib.Foundations.Logic.Theorems.Modal.Basic
public import Cslib.Foundations.Logic.Theorems.Modal.S5
public import Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived
public import Cslib.Foundations.Logic.Theorems.Temporal.FrameConditions
```

`Modal.Basic`, `Modal.S5`, and `Temporal.TemporalDerived` belong to other sub-PRs. Including
`Theorems.lean` as-is will cause build failure. No other file in the sub-PR 1.1 scope imports
`Theorems.lean`.

**Options**:
1. Exclude `Theorems.lean` entirely (add it in a later sub-PR)
2. Include a reduced version importing only propositional modules
3. Include `FrameConditions.lean` stand-alone without the barrel

Recommendation: Option 2 -- include a reduced `Theorems.lean` that omits modal/temporal imports.

### Finding 5: Defs.lean Bib Reference

`pr1/foundations-logic` has a bib reference added to `Defs.lean`:
```
## References
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Chapter 1
```

This is NOT on local `main` and was added by task 123 (bib references). Per the spec:
"No new bib citations needed for this refactoring PR." This bib reference should NOT be
included in sub-PR 1.1.

### Finding 6: Missing Dependency Files

The 13 spec files have transitive imports on files not listed in the spec:

| Missing Dependency | Lines | Required By |
|--------------------|-------|-------------|
| `Foundations/Logic/Connectives.lean` | 98 | Defs.lean, Axioms.lean, Consistency.lean, DeductionHelpers.lean |
| `Foundations/Logic/Axioms.lean` | 298 | ProofSystem.lean |
| `Foundations/Logic/Metalogic/Consistency.lean` | 278 | Derivation.lean |
| `Foundations/Logic/Metalogic/DeductionHelpers.lean` | 120 | DeductionTheorem.lean |
| `Logics/Propositional/ProofSystem/Axioms.lean` | 106 | Instances.lean, DeductionTheorem.lean |

All 5 are identical between local `main` and `pr1/foundations-logic`. They are NEW to upstream.

### Finding 7: NaturalDeduction/Basic.lean Must Be Updated

Because `Defs.lean` changes the `Proposition` type (removing `and`/`or`/`impl` constructors,
adding `bot`/`imp`), the existing `NaturalDeduction/Basic.lean` on upstream will break.

Changes needed in `NaturalDeduction/Basic.lean`:
- Remove `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE` constructors
- Rename `implI` to `impI`, `implE` to `impE`
- Add `botE` constructor (ex falso quodlibet)
- Update docstrings and examples

This file is identical between local `main` and `pr1/foundations-logic` except for bib
reference formatting (task 123 difference, exclude from sub-PR 1.1).

### Finding 8: Cslib.lean Needs Import Additions

Upstream `Cslib.lean` has only 2 `Foundations.Logic` imports:
```lean
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.LogicalEquivalence
```

Sub-PR 1.1 would need to add imports for all new modules being added.

### Finding 9: InferenceSystem.lean Minor Diff

`InferenceSystem.lean` has a minor difference between upstream and local main:
- `public import Cslib.Init` changed to `import Cslib.Init`
- Empty docstring `/-! -/` changed to `/-! # Inference System Typeclass -/`

This is cosmetic but should be included to keep the branch consistent.

## Extraction Strategy

### Recommended Approach: Copy from Local Main with Curation

Since local `main` has all the changes already applied and verified, use it as the source
rather than `pr1/foundations-logic`. This avoids issues with the PR branch's bib references
and stale modal logic content.

### Phase 1: Branch Creation

```bash
git fetch upstream
git checkout -b propositional/hilbert-hierarchy-refactor upstream/main
```

### Phase 2: Copy Files from Local Main

**Core files (13 from spec, minus Theorems.lean):**
```bash
# Foundations layer
git checkout main -- Cslib/Foundations/Logic/ProofSystem.lean  # NEEDS CURATION - see below
git checkout main -- Cslib/Foundations/Logic/Theorems/Propositional/Core.lean
git checkout main -- Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean
git checkout main -- Cslib/Foundations/Logic/Theorems/BigConj.lean
git checkout main -- Cslib/Foundations/Logic/Theorems/Combinators.lean
git checkout main -- Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean
git checkout main -- Cslib/Foundations/Data/ListHelpers.lean

# Propositional layer
git checkout main -- Cslib/Logics/Propositional/Defs.lean  # Use main version (no bib ref)
git checkout main -- Cslib/Logics/Propositional/ProofSystem/Derivation.lean
git checkout main -- Cslib/Logics/Propositional/ProofSystem/Instances.lean
git checkout main -- Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean
git checkout main -- Cslib/Logics/Propositional/Metalogic/MCS.lean
```

**Additional dependency files (5):**
```bash
git checkout main -- Cslib/Foundations/Logic/Connectives.lean
git checkout main -- Cslib/Foundations/Logic/Axioms.lean
git checkout main -- Cslib/Foundations/Logic/Metalogic/Consistency.lean
git checkout main -- Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean
git checkout main -- Cslib/Logics/Propositional/ProofSystem/Axioms.lean
```

**NaturalDeduction/Basic.lean (must update for Defs.lean compat):**
```bash
git checkout main -- Cslib/Logics/Propositional/NaturalDeduction/Basic.lean
```

**InferenceSystem.lean (minor update):**
```bash
git checkout main -- Cslib/Foundations/Logic/InferenceSystem.lean
```

### Phase 3: Curate ProofSystem.lean

`ProofSystem.lean` from local main has extra modal classes (ModalT, ModalD, ModalS4, etc.)
added by tasks 92 and 100. These belong to other sub-PRs.

**Two options:**
1. **Include all modal classes**: Simpler, avoids breaking downstream sub-PRs, but
   makes sub-PR 1.1 larger than intended and leaks content from other sub-PRs.
2. **Strip extra modal classes**: Keep only the original K/S5 classes from `pr1/foundations-logic`
   plus the new 3-tier hierarchy. More faithful to the sub-PR scope.

Recommendation: **Option 1** -- Include the extra modal classes. Reasons:
- They are purely additive (new typeclasses, no conflicts)
- They don't have external dependencies (all extend ClassicalHilbert which is in scope)
- Stripping them creates unnecessary merge conflict potential with later sub-PRs
- The tag types are also purely additive
- The total addition is ~120 lines of simple typeclass definitions

### Phase 4: Create Reduced Theorems.lean

Create a version of `Theorems.lean` that only imports available modules:
```lean
public import Cslib.Foundations.Logic.Theorems.Combinators
public import Cslib.Foundations.Logic.Theorems.Propositional.Core
public import Cslib.Foundations.Logic.Theorems.Propositional.Connectives
public import Cslib.Foundations.Logic.Theorems.BigConj
public import Cslib.Foundations.Logic.Theorems.Temporal.FrameConditions
-- Modal and Temporal theorem imports added in later sub-PRs
```

The module docstring should also be included but without the modal/temporal sections.

### Phase 5: Update Cslib.lean

Add imports for all new modules to `Cslib.lean`.

### Phase 6: Build and Verify

```bash
lake build
lake test
grep -rn "sorry" <modified-files>
```

## Per-File Analysis

### Files Identical Between Main and PR Branch (Copy from Main)

| File | Lines | Action |
|------|-------|--------|
| `Theorems/Propositional/Core.lean` | ~320 | Copy from main |
| `Theorems/Propositional/Connectives.lean` | ~540 | Copy from main |
| `Theorems/BigConj.lean` | ~165 | Copy from main |
| `Theorems/Combinators.lean` | ~125 | Copy from main |
| `Theorems/Temporal/FrameConditions.lean` | ~70 | Copy from main |
| `Foundations/Data/ListHelpers.lean` | ~105 | Copy from main |
| `ProofSystem/Derivation.lean` | ~163 | Copy from main |
| `ProofSystem/Instances.lean` | ~90 | Copy from main |
| `Metalogic/DeductionTheorem.lean` | ~185 | Copy from main |
| `Metalogic/MCS.lean` | ~175 | Copy from main |

### Files Requiring Curation

| File | Issue | Action |
|------|-------|--------|
| `ProofSystem.lean` | Main has extra modal classes from tasks 92/100 | Include all (additive, no conflicts) |
| `Defs.lean` | PR branch has bib ref; upstream has old Proposition type | Copy from main (no bib ref needed) |
| `Theorems.lean` | Imports modal/temporal modules from other sub-PRs | Create reduced version |

### Additional Files Not in Spec

| File | Lines | Reason |
|------|-------|--------|
| `Connectives.lean` | 98 | Imported by Defs.lean, Axioms.lean, Consistency.lean |
| `Axioms.lean` | 298 | Imported by ProofSystem.lean |
| `Consistency.lean` | 278 | Imported by Derivation.lean |
| `DeductionHelpers.lean` | 120 | Imported by DeductionTheorem.lean |
| `ProofSystem/Axioms.lean` | 106 | Imported by Instances.lean, DeductionTheorem.lean |
| `NaturalDeduction/Basic.lean` | ~260 | Must update for Defs.lean compatibility |
| `InferenceSystem.lean` | existing | Minor update (docstring, import visibility) |

### Files to Exclude

| File | Reason |
|------|--------|
| `Theorems/Modal/Basic.lean` | Belongs to sub-PR 1.5 (modal equivalence) |
| `Theorems/Modal/S5.lean` | Belongs to sub-PR 1.5 (modal equivalence) |
| `Theorems/Temporal/TemporalDerived.lean` | Belongs to temporal sub-PR |

## Build Verification Plan

### Step 1: Compile Check
```bash
lake build
```

### Step 2: Lint Checks
```bash
lake lint
lake exe lint-style
lake exe checkInitImports
lake exe mk_all --module --check
```

### Step 3: Import Completeness
```bash
lake exe shake --add-public --keep-implied --keep-prefix
```

### Step 4: No Sorry Check
```bash
grep -rn "sorry" Cslib/Foundations/Logic/ Cslib/Logics/Propositional/ \
  Cslib/Foundations/Data/ListHelpers.lean
```

### Step 5: Existing Tests
```bash
lake test
```

## Risks and Mitigations

### Risk 1: Upstream Proposition Type Incompatibility (HIGH)
- **Risk**: Changing `Proposition` from `and/or/impl` primitives to `bot/imp` primitives
  is a breaking change for any upstream code using the old constructors.
- **Mitigation**: Include `NaturalDeduction/Basic.lean` modifications. Verify no other
  upstream files reference old constructors.
- **Status**: Verified -- only `NaturalDeduction/Basic.lean` uses old constructors on upstream.

### Risk 2: Scope Expansion vs. Spec Mismatch (MEDIUM)
- **Risk**: Sub-PR 1.1 is much larger than the spec anticipated (20+ files vs. 13). This
  may affect review time and conflict surface area.
- **Mitigation**: The additional files are all transitive dependencies that MUST be present.
  Document clearly in PR description. Consider whether the spec should be updated.

### Risk 3: ProofSystem.lean Extra Modal Classes (LOW)
- **Risk**: Including extra modal classes (from tasks 92/100) may cause merge conflicts
  if later sub-PRs (1.5) also touch ProofSystem.lean.
- **Mitigation**: The modal classes are purely additive (new definitions, no modifications
  to existing content). Later sub-PRs should not need to modify these.

### Risk 4: Bib References (LOW)
- **Risk**: `references.bib` has been modified on local main (status: M in git status).
  Care needed not to include bib changes in this sub-PR.
- **Mitigation**: Do NOT checkout `references.bib`. The bib entries exist upstream already.

### Risk 5: NaturalDeduction/Basic.lean Bib Formatting (LOW)
- **Risk**: `pr1/foundations-logic` has bib reference formatting changes in Basic.lean that
  differ from local main. Using the wrong version could include task 123 bib changes.
- **Mitigation**: Use local main version (no bib formatting changes). The bib references
  in Basic.lean on main match upstream's structure.

## Decisions

- Use local `main` as source instead of `pr1/foundations-logic` (11/13 files identical, main is more up-to-date)
- Include the 5 transitive dependency files in the sub-PR scope
- Include `NaturalDeduction/Basic.lean` modifications for `Defs.lean` compatibility
- Include extra modal classes from ProofSystem.lean (additive, no conflicts)
- Create reduced `Theorems.lean` barrel without modal/temporal imports
- Exclude bib references from `Defs.lean` per spec guidance
- Include minor `InferenceSystem.lean` update for consistency

## Recommendations

### R1: Expand the Spec File List (Priority: Critical)
The implementation plan must account for the actual file count (~20 files, not 13).
Update the spec's file table to include the 5 dependency files, `NaturalDeduction/Basic.lean`,
`InferenceSystem.lean`, and the curated `Theorems.lean`.

### R2: Use Local Main as Source (Priority: High)
All files on local main are identical to or more complete than `pr1/foundations-logic`.
Using `git checkout main -- <file>` is safer and simpler than using the PR branch.

### R3: Curate ProofSystem.lean Content (Priority: Medium)
Decide whether to include the extended modal hierarchy (tasks 92/100). Recommendation is
to include it for simplicity, but the alternative is to copy from `pr1/foundations-logic`
for just the propositional portion and manually add only `MinimalHilbert/IntuitionisticHilbert/ClassicalHilbert`.

### R4: Create Reduced Theorems.lean (Priority: High)
The barrel file must exclude modal and temporal theorem imports. Either create a stripped
version or exclude `Theorems.lean` entirely from this sub-PR.

### R5: Verify Build Against Upstream Main (Priority: Critical)
After creating the branch, `lake build` must pass. This is the definitive test that all
dependencies are included and no cross-sub-PR imports exist.

### R6: Update PR Description (Priority: Medium)
The PR description from the spec needs updating to reflect the actual scope (Proposition
type refactoring, NaturalDeduction update, dependency files).

## Appendix: Complete File List for Sub-PR 1.1

### From Spec (12 files, Theorems.lean handled separately)
1. `Cslib/Foundations/Logic/ProofSystem.lean` -- 3-tier hierarchy (curated)
2. `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` -- theorem stratification
3. `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` -- connective stratification
4. `Cslib/Foundations/Logic/Theorems.lean` -- barrel (REDUCED version)
5. `Cslib/Foundations/Logic/Theorems/BigConj.lean` -- ClassicalHilbert rename
6. `Cslib/Foundations/Logic/Theorems/Combinators.lean` -- MinimalHilbert rename
7. `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean` -- import cleanup
8. `Cslib/Foundations/Data/ListHelpers.lean` -- simp only lint fixes
9. `Cslib/Logics/Propositional/Defs.lean` -- Proposition type refactoring + iff abbreviation
10. `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- parameterized DerivationTree
11. `Cslib/Logics/Propositional/ProofSystem/Instances.lean` -- ClassicalHilbert rename
12. `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` -- parameterized deduction theorem
13. `Cslib/Logics/Propositional/Metalogic/MCS.lean` -- parameterized MCS

### Additional Dependencies (5 files)
14. `Cslib/Foundations/Logic/Connectives.lean` -- connective typeclasses
15. `Cslib/Foundations/Logic/Axioms.lean` -- axiom schema typeclasses
16. `Cslib/Foundations/Logic/Metalogic/Consistency.lean` -- generic MCS framework
17. `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` -- deduction helpers
18. `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- PropositionalAxiom inductive

### Compatibility Updates (2 files)
19. `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- update for Defs.lean changes
20. `Cslib/Foundations/Logic/InferenceSystem.lean` -- minor docstring update

### Root Barrel Update (1 file)
21. `Cslib.lean` -- add imports for new modules
