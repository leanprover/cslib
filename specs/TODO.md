---
next_project_number: 86
---

# Tasks

## Task Order

*Updated 2026-06-10. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,38,60,61,76,84 | -- | Temporal Logic, Bimodal Porting, Clean Up, ... |
| 2 | 39,40,62 | 36,37,61 | Temporal Logic, Submit PRs |
| 3 | 41,63 | 38,39,40,62 | Foundations, Submit PRs |
| 4 | 64 | 63 | Submit PRs |

**Grouped by Topic** (indented = depends on parent):

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and  (dep: 38, 39, 40)

### Temporal Logic

38 [NOT STARTED] — Dense temporal completeness: prove that every formula valid on al
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on (dep: 36)
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic (dep: 37)

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T

### Clean Up

76 [NOT STARTED] — module_keyword_migration

### Submit PRs

60 [NOT STARTED] — pr2_modal_metalogic
61 [NOT STARTED] — pr3_temporal_proof_system
  └─ 62 [NOT STARTED] — pr4_temporal_metalogic_core
    └─ 63 [NOT STARTED] — pr5_chronicle_infrastructure
      └─ 64 [NOT STARTED] — pr6_completeness_theorem

### Uncategorized

84 [COMPLETED] — resolve_public_import_cslib_init

## Tasks

### 87. Derive natural deduction from Hilbert system or prove extensional equivalence
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: lean4

**Description**: The two propositional proof systems — the Hilbert-style `DerivationTree` and the independent natural deduction `Derivation` in `NaturalDeduction/Basic.lean` — are currently unconnected. This task aims to formally relate them.

**Primary goal**: Derive the natural deduction rules as theorems from the Hilbert derivation tree, showing that every ND derivation can be translated to a Hilbert derivation (and vice versa). Concretely, construct functions:
- `Derivation T (Γ ⊢ φ) → DerivationTree Γ.toList φ` (or a suitable context conversion)
- `DerivationTree Γ φ → Derivation T (Γ.toFinset ⊢ φ)` (with appropriate theory parameter)

**Fallback**: If full structural translation is impractical due to the different context representations (`Finset` vs `List`) or the theory parameter in ND, prove extensional equivalence at the `Prop` level instead — i.e., that the two systems derive the same formulas from the empty context.

**Key challenges**:
- Context representation mismatch: ND uses `Finset (Proposition Atom)`, Hilbert uses `List (Proposition Atom)`
- The ND system is parameterized over a `Theory T`, while the Hilbert system bakes axioms into `PropositionalAxiom`
- The ND system has `imp_intro`/`imp_elim`/`bot_elim` as primitive constructors; the Hilbert system has `ax`/`assumption`/`modus_ponens`/`weakening`

### 86. Systematic lint and quality audit of all pr1/foundations-logic additions
- **Effort**: medium
- **Status**: [NOT STARTED]
- **Task Type**: lean4

**Description**: Run the full CSLib CI lint suite (`lake lint`, `lake shake`, `lake exe lint-style`, `lake exe checkInitImports`, `lake exe mk_all --module --check`) across all 25 files changed on the `pr1/foundations-logic` branch and fix every issue found. Known recurring patterns to check systematically:

1. **`defLemma` lint**: `def` used for Prop-valued results (`Deriv`, `Nonempty`) that should be `theorem` — found and fixed in 6 places in `FromHilbert.lean`, likely recurs in Modal/Temporal/Bimodal analogues
2. **`topNamespace` lint**: instances declared in `section` without an enclosing `namespace` — found and fixed in `Instances.lean`, likely recurs in other `ProofSystem/Instances.lean` files
3. **Redundant `noncomputable`**: `noncomputable` on theorems is an error in current Lean — found on 2 `def`→`theorem` conversions
4. **Non-minimal imports**: `lake shake` found `Set.Image` → `Set.Basic` in `Defs.lean` — check all 25 files for similar
5. **`flexible` simp warnings**: `simp` used where `simp only [...]` is preferred — multiple instances in `DeductionTheorem.lean` and `MCS.lean`
6. **`unusedTactic` / `multiGoal` warnings**: tactics that do nothing or operate on wrong goal count — found in `DeductionTheorem.lean`

**Files in scope** (all files changed on `pr1/foundations-logic` vs `upstream/main`):
- `Cslib/Foundations/Data/ListHelpers.lean`
- `Cslib/Foundations/Logic/Axioms.lean`
- `Cslib/Foundations/Logic/Connectives.lean`
- `Cslib/Foundations/Logic/InferenceSystem.lean`
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean`
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean`
- `Cslib/Foundations/Logic/ProofSystem.lean`
- `Cslib/Foundations/Logic/Theorems.lean`
- `Cslib/Foundations/Logic/Theorems/BigConj.lean`
- `Cslib/Foundations/Logic/Theorems/Combinators.lean`
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean`
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean`
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`
- `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean`
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean`
- `Cslib/Logics/Propositional/Defs.lean`
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
- `Cslib/Logics/Propositional/Metalogic/MCS.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean`
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean`
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean`
- `Cslib.lean`

All work must be done on the `pr1/foundations-logic` branch. Final verification: all 6 CI checks pass with zero errors and zero warnings in the changed files.

### 85. Include Logics/Propositional/ changes in PR 1 feature branch
- **Effort**: small
- **Status**: [COMPLETED]
- **Task Type**: lean4

**Description**: Add the 6 new files and 2 modified files from Cslib/Logics/Propositional/ to the pr1/foundations-logic branch: ProofSystem/Axioms.lean, ProofSystem/Derivation.lean, ProofSystem/Instances.lean, Metalogic/DeductionTheorem.lean, Metalogic/MCS.lean, NaturalDeduction/FromHilbert.lean (new), plus Defs.lean and NaturalDeduction/Basic.lean (modified). Also update Cslib.lean with the corresponding imports. Verify build, linters, and tests pass after adding.

### 84. Resolve public import Cslib.Init in Foundations/Logic files
- **Effort**: small
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Clean Up
- **Research**: [specs/084_resolve_public_import_cslib_init/reports/01_public-import-analysis.md]
- **Plan**: [specs/084_resolve_public_import_cslib_init/plans/01_implementation-plan.md]
- **Summary**: [specs/084_resolve_public_import_cslib_init/summaries/01_implementation-summary.md]

**Description**: Investigate whether public import Cslib.Init can be downgraded to non-public or removed in Connectives.lean, InferenceSystem.lean, and FrameConditions.lean without breaking the transitive import chain for downstream theorem files. If not possible, document the rationale clearly in the affected files

### 82. Systematic codebase review of Logics/ and Foundations/ for publication quality
- **Effort**: large
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Research**: [082_systematic_codebase_review_logics_foundations/reports/01_team-research.md]
- **Plan**: [082_systematic_codebase_review_logics_foundations/plans/01_codebase-review-plan.md]
- **Summary**: [082_systematic_codebase_review_logics_foundations/summaries/01_codebase-review-summary.md]

**Description**: Whereas task 81's plan is focused on preparing PR 1, review all files touched in Logics/ and Foundations/ for other systematic improvements to the codebase including infrastructure, organization, quality of the proofs, comments, conventions (matching CSLib norms), camelCase instead of snake_case, imports, sections, etc., in order to produce the highest quality most consistent and uniform result for publication

### 83. Review changes since task 74 to update PR 1 description and roadmap
- **Effort**: medium
- **Status**: [RESEARCHED]
- **Task Type**: general
- **Research**: [specs/083_update_pr1_description_and_roadmap/reports/01_pr-description-update.md]

**Description**: Review all changes made since completing task 74 (including tasks 75-81) to update and improve specs/059_pr1_foundations_logic/pr-description.md for PR 1 submission, and update specs/ROADMAP.md as appropriate

### 81. Review PR 1 Foundations Logic code quality for infrastructure, organization, naming, and proof improvements
- **Effort**: large
- **Status**: [COMPLETED]
- **Task Type**: lean4

**Description**: Review the files covered by specs/059_pr1_foundations_logic/pr-description.md for PR 1, examining code quality across infrastructure, organization, naming conventions (aligned with CSLib norms), comments, and proofs to identify systematic improvements for the highest quality results before submission

### 79. Systematic deduplication audit and consolidation across Logics/
- **Effort**: Large (8-16 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 78
- **Research**: [specs/079_deduplicate_shared_helpers/reports/01_deduplication-survey.md]
- **Plan**: [specs/079_deduplicate_shared_helpers/plans/01_deduplication-plan.md]
- **Summary**: [specs/079_deduplicate_shared_helpers/summaries/01_deduplication-summary.md]

**Description**: Conduct a systematic survey of all code duplication across the Logics/ directory tree (Propositional, Modal, Temporal, Bimodal) and Foundations/Logic/, then consolidate duplicated definitions into shared locations. Task 78 removed `private` from definitions to enable the `module` keyword migration, but left duplication in place. This task aims for highest code quality by eliminating all unnecessary repetition.

**Phase 1 — Comprehensive duplication survey**: Systematically scan all Logics/ and Foundations/Logic/ files to identify every instance of duplicated or near-duplicated code. This includes but is not limited to: identical definitions, structurally parallel proofs that differ only in type parameters, duplicated helper lemmas, repeated proof patterns, and similar namespace structures across logic domains. The survey should produce a categorized inventory with: (a) exact duplicates (identical code), (b) structural duplicates (same proof shape, different types), (c) near-duplicates (minor variations that could be generalized), and (d) intentional parallels (structurally similar but genuinely domain-specific). For each finding, assess whether deduplication is feasible and beneficial, or whether the duplication is justified by domain-specific differences.

**Phase 2 — Consolidation**: Based on the survey findings, consolidate duplicated code into shared locations following the existing Foundations → Propositional → {Modal, Temporal} → Bimodal import hierarchy. Prioritize deduplication opportunities by impact (number of duplicate sites × lines saved) and safety (pure extractions before refactors that change proof structure).

**Known duplication targets** (from task 78 research — survey should confirm and extend these):

**(A) DeductionTheorem infrastructure** — 4 files with near-identical structure:
- `Propositional/Metalogic/DeductionTheorem.lean`
- `Modal/Metalogic/DeductionTheorem.lean`
- `Temporal/Metalogic/DeductionTheorem.lean`
- `Bimodal/Metalogic/Core/DeductionTheorem.lean`

Each contains: `removeAll` (identical one-liner: `l.filter (· ≠ a)`), `removeAll_subset_of_subset` / `mem_removeAll_of_mem_of_ne` / `removeAll_subset_removeAll` (identical list lemmas), `deduction_axiom`, `deduction_imp_self`, `deduction_assumption_other`, `deduction_mp`, `deduction_with_mem`, `deduction_theorem` (structurally identical proofs parameterized over different formula/axiom types). The Bimodal variant additionally has `weaken_under_imp` and `weaken_under_imp_ctx`. Investigate whether a generic proof can be written once over the `HasDeductionTheorem` typeclass or the `DerivationSystem` abstraction already in `Foundations/Logic/`, with each logic domain providing only the instance.

**(B) PointInsertion helpers** — 2 files with duplicated seed definitions:
- `Temporal/Metalogic/Chronicle/PointInsertion.lean`: `lemma_2_7_seed`, `lemma_2_7_since_seed`
- `Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean`: same names, nearly identical bodies (Bimodal adds a `FrameClass` parameter)

**(C) Theorem helper abbreviations** — within Bimodal only, not cross-domain:
- `unwrap` in `Theorems/Combinators.lean` and `Theorems/Propositional/Core.lean`
- `wrap`/`unwrap` in `Theorems/Perpetuity/Helpers.lean`
- `wrap'`/`unwrap'` in `Theorems/Propositional/Connectives.lean`

These are Bimodal-internal and may have different type signatures despite similar names. Audit whether consolidation is warranted.

**Quality criteria**: The survey should be exhaustive — no category of duplication should be missed. After consolidation, each shared definition should exist in exactly one location. Domain-specific files should import the shared definition rather than redefining it. The full `lake build` must pass with zero errors. No behavioral changes — this is purely structural cleanup.

---

### 80. Generic DeductionTheorem interface across all logic domains
- **Effort**: Medium (3-4 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 79
- **Research**: [specs/080_generic_deduction_theorem/reports/01_team-research.md]
- **Plan**: [080_generic_deduction_theorem/plans/01_generic-deduction.md]
- **Summary**: [080_generic_deduction_theorem/summaries/01_generic-deduction-summary.md]

**Description**: Design and implement a shared `HasDerivationTree` typeclass in Foundations/Logic/ that exposes `height`, constructor accessors (`ax`, `assumption`, `mp`, `weakening`), and height-related lemmas, enabling a single generic deduction theorem proof to serve all 4 logic domains (Propositional, Modal, Temporal, Bimodal). Currently each domain has its own ~200-line deduction theorem proof in its `DeductionTheorem.lean` file, all following identical structure: base cases for axiom and assumption (split into same vs. other), inductive case for modus ponens, weakening reduction, and domain-specific "empty-context-only" constructors (e.g., necessitation, temporal_necessity, temporal_duality) which are all discharged by `simp at hA`. The generic proof should handle the 4 common constructors, with each logic providing a dispatch mechanism for its extra constructors. After implementation, each domain's `DeductionTheorem.lean` should contain only a `HasDerivationTree` instance and a one-line invocation of the generic proof, eliminating ~600 lines of duplicated proof code across the 3 non-canonical domains.

---

### 77. Audit and clean up noncomputable usage across logic files
- **Effort**: Medium (2-4 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4

**Description**: Review and clean up `noncomputable` usage across Foundations/Logic/ and Logics/ (Modal, Temporal, Bimodal, Propositional). Audit every `noncomputable` annotation to determine whether it is actually required by the Lean compiler or was added unnecessarily. Remove any that are not needed. For those that are needed, verify the reason (e.g., Classical.choice, Decidable instances via classical logic, infinite constructions) and add a brief comment if the reason is non-obvious. Check for cases where making definitions computable would be straightforward (e.g., by providing DecidableEq instances or using pattern matching instead of Classical.em). Ensure consistency with Mathlib conventions for noncomputable usage.

---

### 78. Systematic module keyword and private declaration audit across Logics/
- **Effort**: Large (16-24 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 76
- **Research**: [specs/078_module_keyword_and_private_audit/reports/01_module-keyword-audit.md]
- **Plan**: [specs/078_module_keyword_and_private_audit/plans/01_module-keyword-audit.md]
- **Summary**: [specs/078_module_keyword_and_private_audit/summaries/01_module-keyword-audit-summary.md]

**Description**: Systematically audit and fix all Logics/ files (Modal, Temporal, Bimodal, Propositional) to properly support the Lean 4 `module` keyword. Task 76 added `module` + `public import` + `@[expose] public section` to 145 files but broke the build because `private` declarations inside `@[expose] public section` in `module` files become invisible to later code in the same file. The fix requires a holistic approach: (1) Inventory all `private` declarations across every `module` file. (2) For each one, determine if `private` is needed for name-collision avoidance (e.g., `theorem_in_mcs_fc` is defined identically in 18+ files) or is merely conventional. (3) Where `private` was only conventional (helpers used within a single proof), rename to unique namespace-qualified names (e.g., `deduction_axiom` → `DeductionTheorem.axiom_case`) and remove `private`. (4) Where `private` prevents genuine name collisions across files that import each other, either deduplicate into a shared utility module or use unique names per file. (5) Verify the full `lake build` passes with zero errors after all changes. (6) Re-apply task 76's `module` + `public import` + `@[expose] public section` migration on top of the cleaned codebase. This supersedes task 76 which has been reverted.

---

### 76. Systematic module keyword migration across remaining Logics/ files
- **Effort**: Small (reverted)
- **Status**: [COMPLETED]
- **Task Type**: lean4

**Description**: Systematically add `module` keyword, `public import`, and `@[expose] public section` to all non-module .lean files across Logics/ (Bimodal, Modal, Temporal, Propositional) that are imported by Cslib.lean. Task 74 phase (d) identified the root cause: Cslib.lean has `module` but 145 of its imported Logics/ files did not, causing "cannot import non-module from module" build failure. Migrated 145 files following the same pattern established by task 68 for Foundations/Logic (15 files). This brings the Logics/ directories into conformance with the module convention used throughout the rest of the codebase.

---

### 75. Develop propositional Hilbert proof system and derive natural deduction rules
- **Effort**: Large (16-24 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4

**Description**: Develop a propositional Hilbert proof system in Logics/Propositional/ and derive natural deduction rules as syntactic sugar. Create a Hilbert-style proof system for propositional logic (ProofSystem/, DeductionTheorem, MCS, etc.) following the same pattern as Modal/, Temporal/, and Bimodal/. Derive the natural deduction rules (→I via deduction theorem, →E via modus ponens, ⊥E via ex falso axiom, assumption via context membership) as lemmas with natural-deduction-flavored names. Derive cut, weakening, and substitution within the Hilbert framework. Refactor NaturalDeduction/Basic.lean so its rules are syntactic sugar over the Hilbert infrastructure rather than a standalone inductive type. Modal/, Temporal/, and Bimodal/ should import from the propositional Hilbert system where appropriate, reusing shared propositional proof infrastructure instead of duplicating it. This extends the Foundations → Propositional → {Modal, Temporal} → Bimodal hierarchy by making Propositional a genuine proof-theoretic foundation, not just a formula-type foundation.

---

### 74. Polish PR1 code quality and update pr-description.md for publication
- **Effort**: Medium (2-3 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Tasks 68, 69, 71
- **Topic**: Submit PRs
- **Research**: [specs/074_polish_pr1_quality_and_description/reports/01_polish-pr1-research.md]
- **Plan**: [specs/074_polish_pr1_quality_and_description/plans/01_polish-pr1-plan.md]
- **Summary**: [specs/074_polish_pr1_quality_and_description/summaries/01_implementation-summary.md]

**Description**: Five sub-issues: (a) Fix double blank lines left by sed in Combinators.lean:42-43, Propositional/Core.lean:43-44, and Modal/Basic.lean:44-45. (b) Scope `set_option linter.style.longLine false` in S5.lean and TemporalDerived.lean from file-scoped to per-theorem using `set_option ... in theorem ...` syntax; use `let` abbreviations to shorten long theorem signatures where possible. (c) Deduplicate `top'`/`neg'` abbreviations — TemporalDerived.lean redefines these identically to Axioms.lean; import from Axioms instead. (d) Fix top-level `lake build` by adding `module` keyword to `Cslib/Logics/Bimodal/FrameConditions/Compatibility.lean` (non-module file imported from module Cslib.lean). (e) Update `specs/059_pr1_foundations_logic/pr-description.md`: fix all stale per-file line counts in the File Inventory table, add a new section explaining the Embedding/ relocation (tasks 72-73) — why Propositional/Embedding.lean was moved to Bimodal/Embedding/PropositionalEmbedding.lean and Modal/FromPropositional.lean + Temporal/FromPropositional.lean were created to establish the clean import hierarchy Propositional/ → {Modal/, Temporal/} → Bimodal/, and document the module keyword migration (task 68) where all 15 files now have `module` and `@[expose] public section`.

---

### 73. Make Propositional a shared sub-logic for Modal and Temporal
- **Effort**: Large (8-16 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Research**: [specs/073_propositional_shared_sublogic/reports/01_shared-sublogic-research.md]
- **Plan**: [specs/073_propositional_shared_sublogic/plans/01_shared-sublogic-plan.md]

**Description**: Make Propositional a shared sub-logic that Modal and Temporal build on. Currently Modal and Temporal each define their own formula types independently from Foundations, with no imports from Logics/Propositional/. Refactor so that Modal/ and Temporal/ import from Propositional/ and reuse its definitions where appropriate (e.g. propositional connectives, natural deduction infrastructure). This would establish Propositional as a genuine intermediate layer: Foundations → Propositional → {Modal, Temporal} → Bimodal. Research what content from Propositional/Defs.lean and Propositional/NaturalDeduction/ could be shared, and what structural changes to Modal and Temporal formula types would be needed to build on Propositional rather than duplicating its primitives.

---

### 72. Relocate Propositional/Embedding to fix dependency inversion
- **Effort**: Medium (2-4 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Research**: [specs/072_relocate_propositional_embedding/reports/01_embedding-relocation.md]

**Description**: Currently Logics/Propositional/Embedding.lean imports from Modal.Basic and Temporal.Syntax.Formula, creating a backwards dependency where the simpler logic imports from more complex ones. Restructure so that each logic's embedding lives in the appropriate place — either in the target logic (Modal/, Temporal/) or in the consumer (Bimodal/Embedding/) — so that Logics/Propositional/ only imports from Foundations/. This should maintain a consistent pattern across the codebase where imports flow downward: Foundations → {Propositional, Modal, Temporal} → Bimodal. Update the ROADMAP.md flowchart after restructuring.

---

### 71. Polish documentation in Theorems.lean and Axioms.lean
- **Effort**: Small (0.5 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 68
- **Topic**: Submit PRs
- specs/071_polish_docs_theorems_axioms/reports/01_polish-docs-research.md: [Research]
- specs/071_polish_docs_theorems_axioms/plans/01_polish-docs-plan.md: [Plan]
- specs/071_polish_docs_theorems_axioms/summaries/01_execution-summary.md: [Summary]

**Description**: NICE-TO-HAVE quality audit fixes. (a) Theorems.lean aggregator docstring is missing the Temporal subsection -- add entries for Temporal.TemporalDerived and Temporal.FrameConditions. (b) Axioms.lean temporal section (lines 112-295) has repeated `let top` and `let neg` blocks in nearly every temporal axiom definition -- extract as section-scoped `private abbrev top'` and `private abbrev neg'` to reduce visual noise. Purely cosmetic; verify `lake build` passes after changes.

---

### 70. Remove unused public import Cslib.Init from 4 core definition files
- **Effort**: Small (0.5 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 68
- **Topic**: Submit PRs
- specs/070_remove_unused_cslib_init_imports/reports/01_unused-imports-research.md: [Research]
- specs/070_remove_unused_cslib_init_imports/plans/01_unused-imports-plan.md: [Plan]
- specs/070_remove_unused_cslib_init_imports/summaries/01_unused-imports-summary.md: [Summary]

**Description**: `lake shake` flags unused `public import Cslib.Init` in Connectives.lean, Axioms.lean, InferenceSystem.lean, and ProofSystem.lean. Remove the unused imports, then run `lake build` and `lake shake` to confirm clean output. Should be done after task 68 (module keyword addition) since changing import declarations may affect what `lake shake` reports.

---

### 69. Fix linter warnings in Foundations/Logic theorem files
- **Effort**: Medium (2 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 68
- **Topic**: Submit PRs
- specs/069_fix_linter_warnings_foundations/reports/01_linter-warnings-research.md: [Research]
- specs/069_fix_linter_warnings_foundations/plans/01_linter-warnings-plan.md: [Plan]
- specs/069_fix_linter_warnings_foundations/summaries/01_execution-summary.md: [Summary]

**Description**: SHOULD-FIX quality audit items. Four sub-issues: (a) BigConj.lean has 6 flexible `simp` warnings -- replace bare `simp [bigconj]` with `simp only [...]` using compiler-suggested replacements. (b) Propositional/Connectives.lean has 2 empty-line-in-command style warnings at lines 357 and 368 -- remove blank lines or replace with comment lines. (c) 5 files (Combinators, Core, Prop/Connectives, Modal/Basic, S5) suppress `set_option linter.unreachableTactic false` at file scope -- scope to specific proofs using `set_option ... in theorem ...`. (d) S5.lean and TemporalDerived.lean suppress `set_option linter.style.longLine false` at file scope -- use `let` abbreviations in theorem statements and scope suppression to specific theorems only.

---

### 68. Add module keyword to 10 Foundations/Logic theorem files
- **Effort**: Medium (1.5 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 59
- **Topic**: Submit PRs
- specs/068_add_module_keyword_theorem_files/reports/01_module-keyword-research.md: [Research]
- specs/068_add_module_keyword_theorem_files/plans/01_module-keyword-plan.md: [Plan]
- specs/068_add_module_keyword_theorem_files/summaries/01_execution-summary.md: [Summary]

**Description**: MUST-FIX from quality audit. 10 of 15 files in Cslib/Foundations/Logic/ are missing the `module` keyword, preventing them from being imported from `Cslib.lean` (which is a `module` file). Affected files: Theorems/Combinators.lean, Theorems/Propositional/Core.lean, Theorems/Propositional/Connectives.lean, Theorems/BigConj.lean, Theorems/Modal/Basic.lean, Theorems/Modal/S5.lean, Theorems/Temporal/TemporalDerived.lean, Theorems/Temporal/FrameConditions.lean, Metalogic/Consistency.lean, Theorems.lean. For each file: add `module` after copyright header, change `import` to `public import`, follow the pattern used by the 5 core definition files (InferenceSystem, Connectives, Axioms, ProofSystem, LogicalEquivalence). Run `lake build` and `lake exe mk_all` to update Cslib.lean after all changes.

---

### 67. Fix simp linter warnings in PR-scope files
- **Effort**: Small (0.5 hours)
- **Status**: [COMPLETED]
- **Research**: [067_fix_simp_linter_warnings/reports/01_simp-linter-research.md]
- **Plan**: [067_fix_simp_linter_warnings/plans/01_fix-simp-warnings.md]
- **Summary**: [067_fix_simp_linter_warnings/summaries/01_execution-summary.md]
- **Task Type**: lean4
- **Topic**: Submit PRs

**Description**: Fix 7 @[simp] linter warnings in PR-scope files. 5 in Temporal/Semantics/Satisfies.lean (neg_iff, some_future_iff, some_past_iff, all_future_iff, all_past_iff - LHS simplifies from / simp can prove). 2 in Propositional/Embedding.lean (toModal_neg, toTemporal_neg - LHS simplifies from). Either remove @[simp] attribute or restructure the lemma so LHS is in canonical simp form.

---

### 66. Fix lint naming conventions in PR-scope files
- **Effort**: Medium (3 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Research**: [specs/066_fix_lint_naming_conventions/reports/01_lint-naming-research.md]
- **Plan**: [066_fix_lint_naming_conventions/plans/01_fix-lint-naming.md]
- **Summary**: [066_fix_lint_naming_conventions/summaries/01_fix-lint-naming-summary.md]

**Description**: Rename 19 snake_case identifiers to lowerCamelCase in PR-scope files (Temporal/Propositional). 12 in Temporal/Syntax/Formula.lean (some_future, all_future, some_past, all_past, weak_future, weak_past, weak_until, weak_since, strong_release, strong_trigger, swap_temporal), 1 in Temporal/Syntax/BigConj.lean (neg_bigconj), plus downstream references. Requires lake build verification after each rename.

---

### 64. PR 6: Submit Temporal completeness theorem
- **Effort**: Small (2 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 63
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing the final 3 files: ChronicleToCountermodel.lean, TruthLemma.lean, Completeness.lean (~492 lines). PR title: `feat(Logics/Temporal): BX completeness theorem via Burgess chronicle countermodel`. Run CI checks (lake build, shake, lint, checkInitImports, mk_all). Add `public import` lines to Cslib.lean. See task 56 plan Phase 8 for full details.

---

### 63. PR 5: Submit Temporal chronicle infrastructure
- **Effort**: Medium (2.5 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 62
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing 8 Chronicle construction files: ChronicleTypes, Frame, CanonicalChain, OrderedSeedConsistency, RRelation, PointInsertion, CounterexampleElimination, ChronicleConstruction (~7,117 lines). PR title: `feat(Logics/Temporal): Burgess chronicle construction infrastructure`. If reviewers request split, offer: (5a) types+frame+chain+consistency+RRelation (~1,497 lines), (5b) insertion+elimination+construction (~7,620 lines). Run CI checks. See task 56 plan Phase 7.

---

### 62. PR 4: Submit Temporal metalogic core
- **Effort**: Medium (2.5 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Tasks 59, 61
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing 10 non-Chronicle Temporal Metalogic files: DerivationTree, DeductionTheorem, MCS, TemporalContent, GeneralizedNecessitation, PropositionalHelpers, WitnessSeed, Soundness, CompletenessHelpers, barrel (~2,790 lines). PR title: `feat(Logics/Temporal): temporal metalogic -- deduction theorem, MCS saturation, and soundness`. Run CI checks. See task 56 plan Phase 6.

---

### 61. PR 3: Submit Temporal semantics, proof system, and theorems
- **Effort**: Small (2 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 59
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing 11 non-metalogic Temporal files: Semantics (Model, Satisfies, Validity), ProofSystem (Axioms, Derivation, Derivable, Instances, barrel), Theorems (TemporalDerived, FrameConditions, barrel) (~2,358 lines). Can be submitted in parallel with PR 2 (task 60). PR title: `feat(Logics/Temporal): BX temporal logic semantics, proof system, and derived theorems`. Run CI checks. See task 56 plan Phase 5.

---

### 60. PR 2: Submit Modal metalogic (soundness and completeness)
- **Effort**: Small (2 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 59
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing 6 Modal Metalogic files: DerivationTree, DeductionTheorem, MCS, Soundness, Completeness, barrel (~1,449 lines). Can be submitted in parallel with PR 3 (task 61). PR title: `feat(Logics/Modal): Kripke semantics deduction theorem, MCS theory, soundness and completeness for S5`. Run CI checks. See task 56 plan Phase 4.

---

### 59. PR 1: Submit Foundations/Logic theorems and MCS foundations
- **Effort**: Small (2 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Tasks 58, 66, 67
- **Topic**: Submit PRs
- **Research**: [059_pr1_foundations_logic/reports/01_primitive-connectives-justification.md]
- **Plan**: [059_pr1_foundations_logic/plans/01_pr-submission-plan.md]

**Description**: Create feature branch and submit PR containing all 16 Foundations/Logic files: core definitions (ProofSystem, InferenceSystem, Connectives, LogicalEquivalence, Axioms), Theorems (Combinators, BigConj, barrel), Propositional (Core, Connectives, Reasoning), Modal (Basic, S5), Temporal (TemporalDerived, FrameConditions), Metalogic/Consistency (~3,666 lines). This must be the first PR because Temporal and Modal metalogic import Consistency. PR title: `feat(Foundations/Logic): propositional theorems, modal S5 theorems, and MCS consistency foundations`. Run CI checks. See task 56 plan Phase 3.

---

### 40. Continuous temporal completeness
- **Effort**: TBD
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Dependencies**: Tasks 31, 37

**Description**: Completeness for temporal logic over Dedekind-complete (continuous) linear orders (e.g., the reals). Define a Continuous frame class extending Dense, add any required axioms, prove soundness and completeness.

**Blocker**: Research needed on whether continuous frames require additional axioms beyond density. The standard result (Burgess 1982) is that Until/Since temporal logic over the reals has the same theorems as over the rationals — density suffices — which would make this a transfer theorem rather than a new completeness proof. But this equivalence itself needs to be formalized.

---

### 39. Discrete temporal completeness
- **Effort**: Medium (8-12 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Tasks 31, 36

**Description**: Prove that every formula valid on all discrete serial linear orders is derivable in the Discrete temporal proof system. New development (not a port).

**Scope**:
1. Add discrete-specific axioms to `Temporal.Axiom`: `prior_UZ` (F(φ) → U(φ,¬φ)), `prior_SZ` (P(φ) → S(φ,¬φ)), `z1` (G(Gφ→φ) → (F(Gφ)→Gφ)), and discrete uniformity axioms (`discrete_symm_fwd/bwd`, `discrete_propagate_fwd/bwd`), gated to `FrameClass.Discrete` via `minFrameClass`.
2. Prove discrete soundness: each discrete axiom valid on `SuccOrder + PredOrder + IsSuccArchimedean`.
3. Prove discrete completeness via contrapositive + MCS + canonical model on `Int`. The non-discrete branch is eliminated by deriving `U(⊤,⊥)` as a Discrete theorem.

**Target**: `Cslib/Logics/Temporal/Metalogic/DiscreteCompleteness.lean` + axiom additions to `Axioms.lean`
**Estimated scope**: ~500-700 lines

---

### 38. Dense temporal completeness
- **Effort**: Medium (6-10 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 31, 49

**Description**: Prove that every formula valid on all dense serial linear orders is derivable in the Dense temporal proof system. New development (not a port).

**Scope**:
1. Add dense-specific axioms to `Temporal.Axiom`: `density` (G(Gφ) → Gφ) and `dense_indicator` (¬U(⊤,⊥)), gated to `FrameClass.Dense` via `minFrameClass`.
2. Prove dense soundness: density axiom valid on `DenselyOrdered` (between any two points there's another, so G(Gφ) → Gφ); `dense_indicator` valid on `DenselyOrdered` (no immediate successor, so U(⊤,⊥) is false).
3. Prove dense completeness via contrapositive + MCS + canonical model on `Rat`. The non-dense branch is eliminated by deriving `¬U(⊤,⊥)` as a Dense theorem, so its necessitation is in every Dense-MCS.

**Target**: `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` + axiom additions to `Axioms.lean`
**Estimated scope**: ~400-600 lines

---

### 41. Abstract shared completeness infrastructure
- **Effort**: Medium (8-12 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Tasks 38, 39, 40

**Description**: Abstract shared completeness infrastructure between temporal and bimodal logic, extending the generic MCS framework (Task 29) in `Cslib/Foundations/Logic/Metalogic/`. To be done after concrete completeness proofs are finished for both logics.

**Candidate abstractions** (to be confirmed once concrete implementations exist):
1. **Generic `neg_consistent_of_not_derivable`**: if φ is not derivable then {¬φ} is consistent — identical structure in both logics, parameterized over `DerivationSystem`
2. **Completeness contrapositive skeleton**: not derivable → consistent → Lindenbaum → MCS → canonical model → countermodel — shared proof shape
3. **Dense/discrete case split pattern**: the three-way split on indicator formulas (□(F'T) / □(U(T,⊥)) bimodal, G(F'T) / G(U(T,⊥)) temporal) follows the same structure
4. **Dense indicator elimination**: both dense completeness proofs eliminate the non-dense branch by showing the dense indicator axiom is a theorem — identical pattern
5. **Canonical order construction patterns**: both define canonical_lt via G-sets (temporal) or box-sets (bimodal); linearity/irreflexivity/transitivity proofs follow parallel structures

**Scope**: Identify which abstractions yield genuine code savings vs. premature generalization, implement those that do, refactor both temporal and bimodal completeness to use the shared infrastructure.

**Target**: `Cslib/Foundations/Logic/Metalogic/Completeness.lean` (or similar)

---

### 12. Coordinate cslib PR submission for Bimodal Logic integration
- **Effort**: Ongoing (tracked separately)
- **Status**: [EXPANDED]
- **Task Type**: general
- **Dependencies**: Task 41
- **Subtasks**: 51, 52, 53, 54 (abandoned — superseded by tasks 58-64)

**Description**: Coordinate the cslib PR submission process for the modular logic integration (standalone modules + bimodal). This task runs in parallel with porting tasks and handles maintainer communication, namespace decisions, and CI compliance.

**Standalone Module PRs** (can proceed in parallel with bimodal PRs since they target different directories):
- PR-Foundations (Task 20): Propositional Hilbert theorems to `Cslib/Foundations/Logic/Theorems/` -- Wave 1, no dependencies
- PR-Modal (Task 21): Modal proof system + theorems to `Cslib/Logics/Modal/ProofSystem/` + `Theorems/` -- after PR-Foundations
- PR-Temporal-Infra (Task 22): Temporal infrastructure + theorems to `Cslib/Logics/Temporal/ProofSystem/` + `Theorems/` -- after PR-Foundations
- PR-TempSem (Task 23): Temporal semantics to `Cslib/Logics/Temporal/Semantics/` -- after PR-Temporal-Infra

**Bimodal PRs** (in dependency order):
- PR 1 (Bimodal Syntax, task 2): submit first, establish review pattern
- PR 2 (Semantics, task 3) and PR 3 (ProofSystem, task 4): after PR 1 merged, can overlap
- PR 4 (Perpetuity Theorems, task 5): after PRs 3, PR-Modal, PR-Temporal-Infra merged
- PR 5 (FrameConditions+Soundness, task 6): after PRs 2+3 merged
- PR 6 (MCS/Deduction, task 7): after PRs 3+4 merged
- PR 7 (Completeness, tasks 34+35): after PRs 5+6 merged; discrete (task 36) and continuous (task 37) follow separately
- PR 8 (Decidability, task 9): after PRs 3+6 merged (largest PR, ~10k lines)
- PR 9 (Separation, task 10): after PRs 3+4+6 merged
- PR 10 (ConservativeExtension, task 11): after PR 3 merged (independent of 5-9)

**Coordination Workflow**:

1. **Open Zulip Discussion** (first step): propose modular architecture (standalone Foundations/Modal/Temporal modules + Bimodal), PR strategy (4 standalone PRs + 10 bimodal PRs)
2. **Namespace Decision**: confirm before starting task 2
3. **CI Checks** (before each PR): lake build, lake shake, linter.all, zero sorry, Apache 2.0 headers
4. **Review Cycle**: keep PRs small (max ~3,500 lines); address feedback within 48 hours

---

### 37. Port continuous extension completeness
- **Effort**: TBD
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Dependencies**: Upstream BimodalLogic continuous extension development
- **Parent**: Task 8 (expanded)

**Description**: Port continuous extension completeness once developed upstream. The continuous case (FrameClass for continuous/real-valued time) has not been started in BimodalLogic.

**Blocker**: Upstream BimodalLogic continuous extension development has not begun.

---

### 36. Port discrete completeness
- **Effort**: Medium (6-8 hours)
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Dependencies**: Upstream BimodalLogic discrete sorry elimination
- **Parent**: Task 8 (expanded)

**Description**: Port discrete completeness (`completeness_discrete` theorem) and `WeakCanonical/IntegerModel/` infrastructure (~6 files). The discrete branch constructs countermodels on `Int` via the Reynolds pipeline.

**Source**: `BimodalLogic/Theories/Bimodal/Metalogic/WeakCanonical/IntegerModel/` (~6 files), discrete branch of `BXCanonical/Completeness.lean`

**Blocker**: Upstream BimodalLogic has `sorryAx` tracing through `chronicle_gap_contradiction` → `succ_cofinal` → `limitDomSubtype_isSuccArchimedean` → `succ_embed_surjective` (36 sorries across IntegerModel/).

---



