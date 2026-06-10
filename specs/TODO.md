---
next_project_number: 75
---

# Tasks

## Task Order

*Updated 2026-06-10. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,38,60,61,74 | -- | Temporal Logic, Bimodal Porting, Submit PRs |
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

### Submit PRs

60 [NOT STARTED] — pr2_modal_metalogic
61 [NOT STARTED] — pr3_temporal_proof_system
  └─ 62 [NOT STARTED] — pr4_temporal_metalogic_core
    └─ 63 [NOT STARTED] — pr5_chronicle_infrastructure
      └─ 64 [NOT STARTED] — pr6_completeness_theorem
74 [NOT STARTED] — polish_pr1_quality_and_description

## Tasks

### 74. Polish PR1 code quality and update pr-description.md for publication
- **Effort**: Medium (2-3 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 68, 69, 71
- **Topic**: Submit PRs

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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 63
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing the final 3 files: ChronicleToCountermodel.lean, TruthLemma.lean, Completeness.lean (~492 lines). PR title: `feat(Logics/Temporal): BX completeness theorem via Burgess chronicle countermodel`. Run CI checks (lake build, shake, lint, checkInitImports, mk_all). Add `public import` lines to Cslib.lean. See task 56 plan Phase 8 for full details.

---

### 63. PR 5: Submit Temporal chronicle infrastructure
- **Effort**: Medium (2.5 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 62
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing 8 Chronicle construction files: ChronicleTypes, Frame, CanonicalChain, OrderedSeedConsistency, RRelation, PointInsertion, CounterexampleElimination, ChronicleConstruction (~7,117 lines). PR title: `feat(Logics/Temporal): Burgess chronicle construction infrastructure`. If reviewers request split, offer: (5a) types+frame+chain+consistency+RRelation (~1,497 lines), (5b) insertion+elimination+construction (~7,620 lines). Run CI checks. See task 56 plan Phase 7.

---

### 62. PR 4: Submit Temporal metalogic core
- **Effort**: Medium (2.5 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 59, 61
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing 10 non-Chronicle Temporal Metalogic files: DerivationTree, DeductionTheorem, MCS, TemporalContent, GeneralizedNecessitation, PropositionalHelpers, WitnessSeed, Soundness, CompletenessHelpers, barrel (~2,790 lines). PR title: `feat(Logics/Temporal): temporal metalogic -- deduction theorem, MCS saturation, and soundness`. Run CI checks. See task 56 plan Phase 6.

---

### 61. PR 3: Submit Temporal semantics, proof system, and theorems
- **Effort**: Small (2 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 59
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing 11 non-metalogic Temporal files: Semantics (Model, Satisfies, Validity), ProofSystem (Axioms, Derivation, Derivable, Instances, barrel), Theorems (TemporalDerived, FrameConditions, barrel) (~2,358 lines). Can be submitted in parallel with PR 2 (task 60). PR title: `feat(Logics/Temporal): BX temporal logic semantics, proof system, and derived theorems`. Run CI checks. See task 56 plan Phase 5.

---

### 60. PR 2: Submit Modal metalogic (soundness and completeness)
- **Effort**: Small (2 hours)
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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



