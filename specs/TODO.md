---
next_project_number: 90
---

# Tasks

## Task Order

*Updated 2026-06-10. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,38,60,61,88 | -- | Temporal Logic, Bimodal Porting, Submit PRs |
| 2 | 39,40,62 | 36,37,61 | Temporal Logic, Submit PRs |
| 3 | 41,63 | 38,39,40,62 | Submit PRs, Foundations |
| 4 | 64 | 63 | Submit PRs |

**Grouped by Topic** (indented = depends on parent):

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

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and  (dep: 38, 39, 40)

### Uncategorized

88 [COMPLETED] — refactor_propositional_hilbert_intuitionistic_base
89 [PLANNED] — derived_connective_rules

## Tasks

### 89. Derived intro/elim rules for defined propositional connectives in ND and Hilbert
- **Effort**: medium
- **Status**: [RESEARCHED]
- **Task Type**: lean4

**Description**: Add derived intro/elim rules for the defined propositional connectives (`∧ₚ`, `∨ₚ`, `¬ₚ`, `↔ₚ`, `⊤ₚ`) in both proof systems so that both are equally versatile. Connectives are already `abbrev` definitions reducing to `→`/`⊥` via Łukasiewicz encodings in `Defs.lean`. Follow the existing pattern used for temporal defined operators: `abbrev` + notation + standalone theorems with definitional unfolding.

**Rules to derive** (in both ND `NaturalDeduction/Basic.lean` and Hilbert `FromHilbert.lean`):
- `andI`, `andE₁`, `andE₂` — conjunction intro/elim
- `orI₁`, `orI₂`, `orE` — disjunction intro/elim
- `negI`, `negE` — negation intro/elim
- `dne` — double negation elimination
- `iffI`, `iffE₁`, `iffE₂` — biconditional intro/elim
- `topI` — top introduction
- Prop-level (`Deriv`/`DerivableIn`) versions of each

**Approach**: These should be syntactic sugar — thin wrappers that unfold the `abbrev` definitions and compose existing `→`/`⊥` rules. Reference temporal defined operators in `Temporal/` for the uniform pattern. Both systems should end up with matching interfaces.

### 88. Refactor propositional Hilbert system to intuitionistic base with uniform extension architecture
- **Effort**: large
- **Status**: [COMPLETED]
- **Task Type**: formal
- **Research**: [specs/088_refactor_propositional_hilbert_intuitionistic_base/reports/01_team-research.md]
- **Plan**: [088_refactor_propositional_hilbert_intuitionistic_base/plans/01_intuitionistic-base-plan.md]
- **Summary**: [specs/088_refactor_propositional_hilbert_intuitionistic_base/summaries/01_intuitionistic-base-summary.md]

**Description**: Instead of a single classical propositional Hilbert system, refactor to an intuitionistic propositional Hilbert system with a classical extension. This should follow the same uniform patterns for logic extensions (e.g., where a base modal logic K is extended to D, T, B, 4, KT, KT4, etc., or where the base tense logic is extended to include axioms for discreteness, density, or continuity). Research and implement a design with the best architecture to sustain the elaboration of many extensions of a given logic within a common language.

### 87. Derive natural deduction from Hilbert system or prove extensional equivalence
- **Effort**: medium
- **Status**: [COMPLETED]
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
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Research**: [specs/086_pr1_lint_quality_audit/reports/01_lint-quality-audit.md]
- **Plan**: [specs/086_pr1_lint_quality_audit/plans/01_lint-quality-audit.md]
- **Summary**: [specs/086_pr1_lint_quality_audit/summaries/01_lint-quality-audit-summary.md]

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

### 64. PR 6: Submit Temporal completeness theorem
- **Effort**: Small (2 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Task 63
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing the final 3 files: ChronicleToCountermodel.lean, TruthLemma.lean, Completeness.lean (~492 lines). PR title: `feat(Logics/Temporal): BX completeness theorem via Burgess chronicle countermodel`. Run CI checks (lake build, shake, lint, checkInitImports, mk_all). Add `public import` lines to Cslib.lean. See task 56 plan Phase 8 for full details.

---

### 63. PR 5: Submit Temporal chronicle infrastructure
- **Effort**: Medium (2.5 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Task 62
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing 8 Chronicle construction files: ChronicleTypes, Frame, CanonicalChain, OrderedSeedConsistency, RRelation, PointInsertion, CounterexampleElimination, ChronicleConstruction (~7,117 lines). PR title: `feat(Logics/Temporal): Burgess chronicle construction infrastructure`. If reviewers request split, offer: (5a) types+frame+chain+consistency+RRelation (~1,497 lines), (5b) insertion+elimination+construction (~7,620 lines). Run CI checks. See task 56 plan Phase 7.

---

### 62. PR 4: Submit Temporal metalogic core
- **Effort**: Medium (2.5 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Tasks 59, 61
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing 10 non-Chronicle Temporal Metalogic files: DerivationTree, DeductionTheorem, MCS, TemporalContent, GeneralizedNecessitation, PropositionalHelpers, WitnessSeed, Soundness, CompletenessHelpers, barrel (~2,790 lines). PR title: `feat(Logics/Temporal): temporal metalogic -- deduction theorem, MCS saturation, and soundness`. Run CI checks. See task 56 plan Phase 6.

---

### 61. PR 3: Submit Temporal semantics, proof system, and theorems
- **Effort**: Small (2 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Task 59
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing 11 non-metalogic Temporal files: Semantics (Model, Satisfies, Validity), ProofSystem (Axioms, Derivation, Derivable, Instances, barrel), Theorems (TemporalDerived, FrameConditions, barrel) (~2,358 lines). Can be submitted in parallel with PR 2 (task 60). PR title: `feat(Logics/Temporal): BX temporal logic semantics, proof system, and derived theorems`. Run CI checks. See task 56 plan Phase 5.

---

### 60. PR 2: Submit Modal metalogic (soundness and completeness)
- **Effort**: Small (2 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Task 59
- **Topic**: Submit PRs

**Description**: Create feature branch and submit PR containing 6 Modal Metalogic files: DerivationTree, DeductionTheorem, MCS, Soundness, Completeness, barrel (~1,449 lines). Can be submitted in parallel with PR 3 (task 61). PR title: `feat(Logics/Modal): Kripke semantics deduction theorem, MCS theory, soundness and completeness for S5`. Run CI checks. See task 56 plan Phase 4.

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
- **Status**: [RESEARCHED]
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
- **Status**: [RESEARCHED]
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
- **Status**: [RESEARCHED]
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
