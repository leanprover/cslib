# Teammate D Findings: Strategic Alignment and Long-Term Vision

**Task**: 82 — Systematic codebase review of Logics/ and Foundations/ for publication quality
**Angle**: Horizons — strategic alignment, publication readiness, and long-term positioning
**Date**: 2026-06-10

## Key Findings

### 1. Namespace Convention Gap: Directory vs Namespace Mismatch

The most significant strategic issue for publication. Files live under `Cslib/Foundations/Logic/` but use `namespace Cslib.Logic.*` (dropping `Foundations` from the namespace). This is consistent internally — all 16 Foundations/Logic files do it — but it creates a mismatch with CSLib convention where directory structure and namespace should align (e.g., `Cslib/Foundations/Data/Relation.lean` uses `namespace Relation` under the file's module).

This is not necessarily wrong (Mathlib frequently uses namespace != directory), but it should be a conscious documented decision. The ORGANISATION.md lists `Cslib.Logic` as a top-level namespace with submodules like `HoareLogic`, `LinearLogic`, etc. This suggests the `Cslib.Logic` namespace was originally intended for these files, which now live in `Foundations/Logic/`. The question is: should the namespace follow the directory, or does `Cslib.Logic` remain the canonical logic namespace regardless of file location?

**Recommendation**: Document the convention. The `Cslib.Logic` namespace spanning both `Foundations/Logic/` (infrastructure) and future `Logic/` (specific logics) is defensible — it mirrors how `Cslib.Foundations.Semantics` provides infrastructure used by `Cslib.Languages.CCS` etc. But this should be explicit in module-level docstrings.

### 2. PR 1 vs Task 81 vs Task 82 Scope Overlap

Three concurrent workstreams touch the same files:
- **PR 1** (`specs/059_pr1_foundations_logic/pr-description.md`): The actual submission covering 15 Foundations/Logic files
- **Task 81**: Code review plan with 6 phases of specific fixes (renames, formatting, imports, abbreviations)
- **Task 82** (this task): Broader systematic review

Task 81's plan is well-scoped and actionable. Task 82 should focus on issues that task 81 does NOT cover — namely:
- Cross-domain consistency between Foundations/Logic and Logics/{Modal,Temporal,Bimodal}
- Alignment with broader CSLib norms (as seen in Foundations/Data, Foundations/Syntax, etc.)
- Documentation depth for an external audience
- Structural/organizational improvements beyond the PR 1 file set

### 3. Documentation Gap: Theorems Lack Docstrings

CONTRIBUTING.md states: "Document your definitions and theorems to ease both use and reviewing." Currently, most theorems in Foundations/Logic/Theorems/ have good docstrings (e.g., Combinators.lean has descriptive `/-- ... -/` for each theorem). However, several files have inconsistent documentation:

- `Theorems/Propositional/Core.lean`: 9 theorems, NONE have `/-- -/` docstrings (only module-level `/-! -/`)
- `Theorems/BigConj.lean`: Several theorems lack docstrings
- `Theorems/Temporal/TemporalDerived.lean`: Most theorems lack docstrings

In contrast, `Theorems/Modal/Basic.lean` and `Theorems/Modal/S5.lean` have thorough documentation. For publication review, a Mathlib-style reviewer would flag undocumented public theorems as needing attention.

### 4. Naming Consistency: snake_case Is Correct for Lean/Mathlib

The task description mentions "camelCase instead of snake_case" as a concern. Looking at the codebase:
- **Lean 4 / Mathlib convention**: `snake_case` for theorems and lemmas, `CamelCase` for types and classes
- **Foundations/Logic files**: Follow this correctly — `imp_trans`, `box_mono`, `diamond_mono`, `efq_axiom` etc.
- **Type/class names**: Also correct — `PropositionalHilbert`, `ModalS5Hilbert`, `HasBox`, `HasImp`

One exception: `BigConj` is used as both a type name and in theorem names like `bigconj_nil`. This is fine — Mathlib uses the same pattern (e.g., `Finset.sum_empty`).

**The existing naming is aligned with Lean/Mathlib norms.** No systematic rename needed. The concerns in the task description about camelCase may have been about ensuring consistency rather than changing conventions.

### 5. `@[expose] public section` Pattern Is Non-Standard

Every Foundations/Logic file uses `@[expose] public section` as a top-level wrapper. This is part of the `module` keyword migration (task 68/76). Looking at other CSLib files:
- `Foundations/Data/Relation.lean` uses `@[expose] public section` ✓
- `Foundations/Syntax/HasSubstitution.lean` uses `public section` (no `@[expose]`) 
- `Logics/Modal/Basic.lean` does NOT use `@[expose]`
- `Logics/Propositional/Defs.lean` does NOT use `@[expose]`

The `@[expose]` attribute and `public section` are part of the module keyword system. Not all CSLib files have migrated yet (task 76 is for module keyword migration). This is not a bug — it's a migration in progress. For PR 1, the Foundations/Logic files should be consistent with themselves, which they are.

### 6. Import Verbosity: Qualified vs Opened Namespaces

Some files open very long namespace chains:
```
open Cslib.Logic.Theorems.Propositional.Core
open Cslib.Logic.Theorems.Propositional.Connectives
open Cslib.Logic.Theorems.Modal.Basic
```

This is functional but verbose. In Mathlib style, you'd typically see `open ... in` for localized opens, or use `open Cslib.Logic.Theorems` with selective access. However, the current approach is explicit and safe — it's a stylistic preference, not a correctness issue.

### 7. Proof Style: Term-Mode vs Tactic Proofs

Looking at how proofs are written:
- Combinators.lean: Heavy term-mode proofs (appropriate for combinator-style derivations)
- Core.lean, Connectives.lean: Term-mode with `exact`/`apply` tactics mixed in
- Modal/Basic.lean: Mix of term-mode and tactic proofs
- Other CSLib files (e.g., Relation.lean): Heavy use of `grind`, `simp`, `omega`

The Foundations/Logic files avoid automation (`grind`, `simp`, `omega`) because they're proving syntactic derivability in a Hilbert system — there's no semantic interpretation for automation to exploit. This is architecturally correct and well-motivated. No change needed here.

### 8. Roadmap Alignment: Task 82 Can Advance PR Submission Strategy

The ROADMAP.md shows 6 planned PRs:
1. PR 1: Foundations/Logic (this PR) — ready except for task 81 cleanup
2. PR 2: Modal metalogic
3. PR 3: Temporal proof system
4. PR 4: Temporal metalogic core
5. PR 5: Chronicle infrastructure
6. PR 6: Completeness theorem

**Strategic opportunity**: Task 82's cleanup should ensure that the patterns established in PR 1 (naming, documentation, structure) are ones that PRs 2-6 can follow. If we discover conventions in Foundations/Logic that conflict with what Logics/ files need, better to fix them now in PR 1 than to discover the conflict during PR 2 review.

Specifically:
- The `Cslib.Logic` namespace convention should be validated against how `Logics/Modal/` and `Logics/Temporal/` use it
- Documentation templates set in Foundations/Logic will become the standard for downstream PRs
- Any `@[simp]`/`@[grind]` tagging conventions decided here carry through

### 9. CONTRIBUTING.md References: Publication Quality Checklist

The CONTRIBUTING.md provides a concrete checklist for PR quality:
- [ ] PR title format: `feat|fix|doc|style|refactor|test|chore|perf: description`
- [ ] All files import `Cslib.Init`
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake lint` passes (environment linters)
- [ ] `lake exe lint-style` passes (text linters, fixable with `--fix`)
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (minimized imports)
- [ ] `lake exe mk_all --module` up to date

These are CI checks that will run on the PR. **Task 82 should verify all of these pass**, not just `lake build`. The `lake shake` check is particularly important — task 81's Phase 3 trims imports manually, but `lake shake` is the authoritative tool.

### 10. Cslib.Logic.PL vs Cslib.Logic Namespace Tension

Propositional logic uses namespace `Cslib.Logic.PL` while Foundations/Logic uses `Cslib.Logic`. Modal logic uses `Cslib.Logic.Modal`. This creates an implicit hierarchy:
```
Cslib.Logic           (Foundations/Logic — infrastructure)
Cslib.Logic.PL        (Logics/Propositional — specific logic)
Cslib.Logic.Modal     (Logics/Modal — specific logic)
Cslib.Logic.Temporal  (Logics/Temporal — specific logic)
```

This is coherent and well-designed. `Cslib.Logic` at the Foundations level provides generic infrastructure; `Cslib.Logic.{PL,Modal,Temporal}` at the Logics level provides specific instantiations. A reviewer should find this clear.

## Recommended Approach

1. **Scope task 82 to complement task 81**: Focus on cross-cutting consistency, documentation gaps in non-PR1 files (Logics/Modal, Logics/Temporal, Logics/Propositional), and CI readiness rather than duplicating task 81's specific fixes.

2. **Run CI checks as part of task 82**: `lake lint`, `lake exe lint-style`, `lake shake`, `lake exe checkInitImports` — these are what actual PR reviewers will see. Fix any failures.

3. **Add docstrings to undocumented theorems in Propositional/Core.lean and TemporalDerived.lean**: These are in the PR 1 scope and a reviewer would flag them.

4. **Document the namespace convention**: Add a note to the module-level docstrings explaining why `Cslib.Logic` (not `Cslib.Foundations.Logic`) is the namespace.

5. **Validate that patterns in Logics/ mirror Foundations/Logic norms**: Check that similar constructs (e.g., `DeductionTheorem` across 4 domains) use the same naming, documentation, and section structure.

6. **Check for `sorry` in all touched files**: `grep -rn "sorry" Cslib/Logics/ Cslib/Foundations/` — any `sorry` in the PR scope would be a blocker.

## Evidence/Examples

**Documentation gap example** (Propositional/Core.lean):
```lean
-- No docstring before this theorem
theorem efq_axiom {φ : F} :
    InferenceSystem.DerivableIn S (neg' (neg' φ) ⊃ φ) := ...
```

Compare with good documentation (Combinators.lean):
```lean
/-- Transitivity of implication: if `⊢ φ → ψ` and `⊢ ψ → χ` then
    derive `⊢ φ → χ`. -/
theorem imp_trans {φ ψ χ : F} ...
```

**Namespace convention evidence**:
- All 16 `Foundations/Logic/` files use `Cslib.Logic.*` namespace (not `Cslib.Foundations.Logic.*`)
- All `Logics/Modal/` files use `Cslib.Logic.Modal` namespace
- All `Logics/Propositional/` files use `Cslib.Logic.PL` namespace
- Consistent pattern: `Cslib.Logic` is the root namespace for ALL logic-related code

**CI readiness concern**:
- CONTRIBUTING.md mandates `lake shake` for import minimization
- Task 81 manually trims imports (Phase 3) but doesn't mention running `lake shake`
- If `lake shake` disagrees with manual trimming, the PR will fail CI

## Confidence Level

**High** for findings 1-6 (namespace conventions, documentation gaps, naming, CI checks) — these are directly observable from the codebase and CONTRIBUTING.md.

**Medium** for findings 7-10 (proof style, roadmap alignment, namespace hierarchy) — these involve architectural judgments that depend on reviewer preferences and future plans.

**Key uncertainty**: Whether CSLib maintainers (beyond Benjamin) have specific style preferences that aren't documented in CONTRIBUTING.md. The Zulip channel might have additional norms. The CONTRIBUTING.md explicitly says "We generally follow the mathlib style" which is our strongest guide.
