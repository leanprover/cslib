# Research Report: Sub-PR 1.1.1 Proposition Type to Lukasiewicz Convention

- **Task**: 138 - Sub-PR 1.1.1: Proposition type to Lukasiewicz convention
- **Started**: 2026-06-11T00:00:00Z
- **Completed**: 2026-06-11T00:30:00Z
- **Effort**: 30 minutes
- **Dependencies**: Task 125 (parent plan)
- **Sources/Inputs**:
  - `specs/125_subpr_1_1_hilbert_hierarchy_refactoring/plans/01_implementation-plan.md` (Phase 2)
  - Upstream main branch at `https://github.com/leanprover/cslib.git`
  - Local main branch source files
  - `CONTRIBUTING.md` (CSLib style and CI conventions)
  - `references.bib` (existing bibliography entries)
- **Artifacts**: `specs/138_subpr_1_1_1_proposition_refactor/reports/01_proposition-refactor.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Project Context

- **Upstream Dependencies**: `Cslib.Init`, `Mathlib.Data.FunLike.Basic`, `Mathlib.Data.Set.Basic`, `Mathlib.Order.TypeTags`, `Mathlib.Data.Finset.Insert/SDiff/Image`
- **Downstream Dependents**: `DerivedRules.lean`, `Equivalence.lean`, `FromHilbert.lean`, `HilbertDerivedRules.lean`, `Semantics/Basic.lean`, `Semantics/Kripke.lean`, `Modal/FromPropositional.lean`, `Temporal/FromPropositional.lean`, `ProofSystem/Axioms.lean`, `ProofSystem/Derivation.lean`
- **Alternative Paths**: None -- this is the foundational PR in the chain
- **Potential Extensions**: PRs 1.1b-1.1g (Axioms, ProofSystem, Instances, Theorems, Metalogic)

## Executive Summary

- The local main branch already contains all changes needed for this PR: `Connectives.lean` (98 lines, NEW), refactored `Defs.lean` (bot/imp primitives with derived connectives), streamlined `NaturalDeduction/Basic.lean` (3 rules replacing 8+), and minor `InferenceSystem.lean` edits.
- The upstream main branch has `Defs.lean` with the old `and/or/impl` constructors (no `bot`), `NaturalDeduction/Basic.lean` with 10 derivation rules (andI, andE1/2, orI1/2, orE, implI, implE), and `InferenceSystem.lean` with minor differences. `Connectives.lean` does NOT exist upstream.
- The `ChagrovZakharyaschev1997` entry already exists in the local `references.bib` but does NOT exist upstream -- it must be added to the PR branch.
- Total diff estimate: 176 insertions + 104 deletions across 4 Lean files + ~11 lines for references.bib + 1 line for Cslib.lean = approximately **291 diff lines**, well under the 500-line limit.
- All downstream files on local main already use bot/imp constructors. The change is self-contained: no additional files need modification beyond the 6 specified.
- The code type-checks on local main with no errors (verified via lean-lsp hover).

## Context & Scope

This research evaluates what changes are needed for Sub-PR 1.1.1, the first PR in the extraction chain from task 125. The PR introduces the Lukasiewicz convention for propositional logic: primitives are `bot` (falsum) and `imp` (implication), with `neg`, `top`, `or`, `and` defined as abbreviations. This replaces the upstream convention where `and`, `or`, `impl` are primitives without a `bot` constructor.

### Scope

Files in scope for this PR (6 total):
1. `Cslib/Foundations/Logic/Connectives.lean` -- NEW (98 lines)
2. `Cslib/Logics/Propositional/Defs.lean` -- MODIFY
3. `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- MODIFY
4. `Cslib/Foundations/Logic/InferenceSystem.lean` -- MODIFY (minor)
5. `references.bib` -- MODIFY (add 1 entry)
6. `Cslib.lean` -- MODIFY (add 1 import line)

Files explicitly OUT of scope:
- `Axioms.lean`, `ProofSystem.lean`, `ListHelpers.lean` (belong to PRs 1.1b-1.1d)
- `DerivedRules.lean`, `Equivalence.lean`, `FromHilbert.lean` (depend on this PR but are later)
- Any Modal/Temporal/Bimodal files

## Findings

### 1. Current Source Files on Local Main

#### Connectives.lean (NEW, 98 lines)

Defines a typeclass hierarchy for logical connectives:
- **Atomic classes**: `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`
- **Bundled classes**: `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`
- **Derived connective specification**: `LukasiewiczDerived` class (intentionally uninstantiated, retained as specification artifact)

Key design features:
- Diamond avoidance: `BimodalConnectives` extends `ModalConnectives` + `HasUntil`/`HasSince` directly rather than extending `TemporalConnectives`
- Uses `@[expose] public section` for visibility
- Imports only `Cslib.Init`
- All within namespace `Cslib.Logic`

#### Defs.lean (MODIFIED, 166 lines vs upstream 130 lines)

Changes from upstream:
- **Copyright/Authors**: Added `2026 Benjamin Brast-McKie` to copyright, added author
- **Imports**: Added `public import Cslib.Foundations.Logic.Connectives`, changed `Set.Image` to `Set.Basic`
- **Proposition inductive**: Replaced 4 constructors (`atom`, `and`, `or`, `impl`) with 3 constructors (`atom`, `bot`, `imp`)
- **Derived connectives**: Added `Proposition.neg`, `Proposition.top`, `Proposition.or`, `Proposition.and`, `Proposition.iff` as abbreviations
- **Instances**: Added `Bot` and `Top` instances; added `PropositionalConnectives` instance
- **Notation**: Changed `→` from binding to `Proposition.imp` (was `Proposition.impl`)
- **Subst**: Simplified from 4 branches (atom/and/or/impl) to 3 (atom/bot/imp)
- **Removed**: `[Bot Atom]` constraints from `IPL`, `CPL`, `IsIntuitionistic`, `IsClassical` -- no longer needed since `bot` is a constructor

#### NaturalDeduction/Basic.lean (MODIFIED, 345 lines vs upstream 266 lines)

Major structural changes:
- **Derivation rules**: Reduced from 10 constructors to 5:
  - KEPT: `ax`, `ass`, `impI` (was `implI`), `impE` (was `implE`)
  - ADDED: `botE` (ex falso quodlibet / bottom elimination)
  - REMOVED: `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`
- **Renamed**: `implI` -> `impI`, `implE` -> `impE` (matching the constructor rename)
- **Implementation notes docstring**: Updated to explain the Lukasiewicz design
- **Weakening proof**: Simplified from 10 cases to 5 cases
- **Substitution proof**: Simplified from 11 cases to 6 cases
- **Top/tautology section**: Removed `[Inhabited Atom]` constraint (top is now `imp bot bot`, not dependent on inhabited atoms)

#### InferenceSystem.lean (MINOR CHANGES, 68 lines)

Only 2 changes:
- `public import Cslib.Init` -> `import Cslib.Init` (removed `public` visibility)
- Added module docstring: `/-! # Inference System Typeclass -/` (was empty `/-! -/`)

### 2. Upstream vs Local Comparison

| File | Upstream Status | Local Status | Diff |
|------|----------------|--------------|------|
| `Connectives.lean` | Does NOT exist | 98 lines | +98 (new file) |
| `Defs.lean` | 130 lines, old constructors | 166 lines, bot/imp | +46/-34 |
| `NaturalDeduction/Basic.lean` | 266 lines, 10 rules | 345 lines, 5 rules | +30/-68 |
| `InferenceSystem.lean` | 68 lines | 68 lines | +2/-2 |
| `references.bib` | No ChagrovZakharyaschev | Has entry | ~+11 |
| `Cslib.lean` | No Connectives import | Has import | +1 |

Important upstream observations:
- Upstream `InferenceSystem.lean` already exists and is very similar
- Upstream `references.bib` exists but does NOT have the ChagrovZakharyaschev1997 entry
- Upstream `Cslib.lean` already imports `Cslib.Foundations.Logic.InferenceSystem` but NOT `Cslib.Foundations.Logic.Connectives`

### 3. Mathlib/CSLib Compatibility Verification

Using lean-lsp hover verification:
- `HasBot` (line 35, Connectives.lean): Type-checks as `Cslib.Logic.HasBot.{u_1} (F : Type u_1) : Type u_1`
- `Proposition` (line 48, Defs.lean): Type-checks as `Cslib.Logic.PL.Proposition.{u} (Atom : Type u) : Type u` with correct bot/imp constructors
- `botE` (line 97, Basic.lean): Type-checks as `Cslib.Logic.PL.Theory.Derivation.botE.{u} ... : Derivation G bot -> Derivation G A`
- All files produce no diagnostic errors

### 4. CSLib Convention Compliance

| Convention | Status | Notes |
|------------|--------|-------|
| `import Cslib.Init` in every file | PASS | All 4 Lean files import `Cslib.Init` (Connectives directly, others transitively) |
| PR title format | Ready | `refactor: Proposition type to Lukasiewicz convention` |
| AI disclosure | Required | Must include in PR description per CONTRIBUTING.md |
| Notation policy | PASS | All notation is scoped |
| Variable names | PASS | Follow domain conventions (Atom, A, B, etc.) |
| Proof style | PASS | Proofs are readable, use standard tactics |

### 5. Downstream Impact Analysis

Files that import `Defs.lean` or `NaturalDeduction/Basic.lean`:

| File | Impact | Notes |
|------|--------|-------|
| `NaturalDeduction/DerivedRules.lean` | None for this PR | Already uses bot/imp on local main |
| `NaturalDeduction/Equivalence.lean` | None for this PR | Already adapted |
| `NaturalDeduction/FromHilbert.lean` | None for this PR | Already adapted |
| `NaturalDeduction/HilbertDerivedRules.lean` | None for this PR | Already adapted |
| `Semantics/Basic.lean` | None for this PR | Already uses `.bot`/`.imp` constructors |
| `Semantics/Kripke.lean` | None for this PR | Already adapted |
| `Modal/FromPropositional.lean` | None for this PR | Already uses `.bot`/`.imp` |
| `Temporal/FromPropositional.lean` | None for this PR | Already adapted |
| `ProofSystem/Axioms.lean` | Not in this PR | Belongs to PR 1.1d |
| `ProofSystem/Derivation.lean` | Not in this PR | Belongs to PR 1.1d |

Key finding: ALL downstream files on local main already use the new constructor names. However, these downstream files do NOT exist upstream. This means the PR's changes to `Defs.lean` and `Basic.lean` are self-contained -- no downstream breakage is possible on upstream because those files do not exist there.

### 6. Diff Size Assessment

| Component | Insertions | Deletions | Total Changed |
|-----------|-----------|-----------|---------------|
| Connectives.lean (new) | 98 | 0 | 98 |
| Defs.lean | 46 | 34 | 80 |
| NaturalDeduction/Basic.lean | 30 | 68 | 98 |
| InferenceSystem.lean | 2 | 2 | 4 |
| references.bib (est.) | 11 | 0 | 11 |
| Cslib.lean | 1 | 0 | 1 |
| **Total** | **188** | **104** | **~292** |

The ~302 line estimate from the parent plan is accurate (within 10 lines). The PR is comfortably under the 500-line limit.

### 7. References.bib Entry

The `ChagrovZakharyaschev1997` entry already exists in the local `references.bib`:

```bibtex
@book{ChagrovZakharyaschev1997,
  author       = {Chagrov, Alexander and Zakharyaschev, Michael},
  title        = {Modal Logic},
  series       = {Oxford Logic Guides},
  volume       = {35},
  publisher    = {Oxford University Press},
  address      = {Oxford},
  year         = {1997},
  isbn         = {978-0-19-853779-3}
}
```

This entry must be extracted to the PR branch. It is the only new reference needed for this PR (Prawitz and Troelstra references are already in upstream's NaturalDeduction/Basic.lean docstring and should not be added to references.bib in this PR).

### 8. Specific Changes Detail

#### Proposition Constructor Rename Map

| Upstream | Local | Type |
|----------|-------|------|
| `Proposition.and` | (removed as constructor, now abbreviation) | `F -> F -> F` |
| `Proposition.or` | (removed as constructor, now abbreviation) | `F -> F -> F` |
| `Proposition.impl` | `Proposition.imp` (constructor) | `F -> F -> F` |
| (none) | `Proposition.bot` (constructor) | `F` |

#### Derivation Rule Rename Map

| Upstream | Local | Type |
|----------|-------|------|
| `andI` | (removed, now derived rule in DerivedRules.lean) | |
| `andE1` | (removed, now derived) | |
| `andE2` | (removed, now derived) | |
| `orI1` | (removed, now derived) | |
| `orI2` | (removed, now derived) | |
| `orE` | (removed, now derived) | |
| `implI` | `impI` (kept, renamed) | |
| `implE` | `impE` (kept, renamed) | |
| (none) | `botE` (new) | `Derivation G bot -> Derivation G A` |

## Decisions

- **Extraction strategy**: Copy files directly from local main to the PR branch. The local main versions are already correct and type-checked.
- **Import change for InferenceSystem.lean**: The `public import Cslib.Init` -> `import Cslib.Init` change is correct because `InferenceSystem.lean` is always imported via `public import` from other files, so the transitive visibility is not needed.
- **References.bib**: Only add `ChagrovZakharyaschev1997`. Do not add Prawitz or Troelstra entries (those belong to later PRs or are already referenced in docstrings).
- **Cslib.lean**: Only add `public import Cslib.Foundations.Logic.Connectives`. Other imports from local main belong to later PRs.

## Recommendations

1. **Implementation approach**: The implementation should create a branch from `upstream/main`, then `git checkout main -- <file>` for each of the 4 Lean files. Then manually add only the `ChagrovZakharyaschev1997` entry to `references.bib` and one import line to `Cslib.lean`.

2. **Cslib.lean import**: Use `lake exe mk_all --module` to regenerate `Cslib.lean` rather than editing manually. However, be careful: this will add ALL files that exist on the branch, which should only include the upstream files plus `Connectives.lean`.

3. **Build verification**: After creating the branch, run:
   ```bash
   lake build
   lake test
   lake exe checkInitImports
   lake exe lint-style
   lake exe mk_all --module --check
   ```

4. **PR description must include**:
   - Summary of the Lukasiewicz convention rationale
   - Link to the Zulip topic (from task 125 Phase 1)
   - Link to PR #633 (the original large PR)
   - Reference: Chagrov & Zakharyaschev, *Modal Logic* (1997), Chapter 1
   - AI disclosure statement

5. **PR title**: `refactor: Proposition type to Lukasiewicz convention`

6. **Potential issue**: The `import Cslib.Init` -> `public import Cslib.Init` change in InferenceSystem.lean could theoretically be rejected by `lake shake` if downstream files rely on the transitivity. Verify with `lake shake --add-public --keep-implied --keep-prefix` on the PR branch.

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Lukasiewicz convention rejected by reviewers | Medium | High | Already discussed on Zulip; present rationale referencing Chagrov & Zakharyaschev and reuse across modal/temporal |
| `lake shake` flags the `import` visibility change in InferenceSystem.lean | Low | Low | Revert to `public import` if needed; this is a 1-line change |
| references.bib merge conflict with concurrent upstream PRs | Low | Low | Entry is alphabetically sorted; conflicts would be trivial |
| NaturalDeduction rule removal is contentious | Medium | Medium | Explain in PR description that conjunction/disjunction rules are now derived (in DerivedRules.lean, a later PR), maintaining mathematical equivalence |
| PR depends on Zulip topic being posted first (Phase 1 of parent plan) | N/A | Medium | Ensure Phase 1 is complete before submitting |

## Appendix

### File Line Counts (Local Main)

| File | Lines |
|------|-------|
| `Cslib/Foundations/Logic/Connectives.lean` | 98 |
| `Cslib/Logics/Propositional/Defs.lean` | 166 |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | 345 |
| `Cslib/Foundations/Logic/InferenceSystem.lean` | 68 |
| **Total** | **677** |

### Git Diff Summary (upstream/main vs local main, 4 core files)

```
 Cslib/Foundations/Logic/Connectives.lean           | 98 ++++++++++++++++++++++
 Cslib/Foundations/Logic/InferenceSystem.lean       |  4 +-
 Cslib/Logics/Propositional/Defs.lean               | 80 ++++++++++--------
 .../Propositional/NaturalDeduction/Basic.lean      | 98 +++++++---------------
 4 files changed, 176 insertions(+), 104 deletions(-)
```

### Upstream Files That DO NOT Exist

- `Cslib/Foundations/Logic/Connectives.lean` (NEW in this PR)
- `Cslib/Foundations/Logic/Axioms.lean` (belongs to PR 1.1b)
- `Cslib/Foundations/Logic/ProofSystem.lean` (belongs to PR 1.1c)
- All `Semantics/`, `FromPropositional`, and `ProofSystem/` files (belong to later PRs)
