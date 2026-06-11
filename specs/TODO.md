---
next_project_number: 123
---

# TODO

## Task Order

*Updated 2026-06-11. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,38,60,61,122 | -- | Temporal Logic, Bimodal Porting, Submit PRs, ... |
| 2 | 39,40,62 | 36,37,61 | Temporal Logic, Submit PRs |
| 3 | 41,63 | 38,39,40,62 | Submit PRs, Foundations |
| 4 | 64 | 63 | Submit PRs |

**Grouped by Topic** (indented = depends on parent):

### Temporal Logic

38 [NOT STARTED] — Dense temporal completeness: prove that every formula valid on al
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T

### Submit PRs

60 [RESEARCHED] — pr2_modal_metalogic
61 [NOT STARTED] — pr3_temporal_proof_system
  └─ 62 [NOT STARTED] — pr4_temporal_metalogic_core
    └─ 63 [NOT STARTED] — pr5_chronicle_infrastructure
      └─ 64 [NOT STARTED] — pr6_completeness_theorem

### Propositional Logic

122 [NOT STARTED] — Fix all CONTRIBUTING.md CI check failures in propositional metalo

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

## Tasks

### 122. Fix propositional ci checks
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Fix all CONTRIBUTING.md CI check failures in propositional metalogic files on both main and pr1/foundations-logic. Issues: (1) lake lint: 8 defsWithUnderscore violations — rename int_canonical_val, int_neg_phi_imp_psi, int_deductive_closure, min_canonical_val, min_bot_forces, min_deductive_closure, lift_min_to_cl, bot_forces to lowerCamelCase in IntCompleteness.lean, IntLindenbaum.lean, MinCompleteness.lean, MinLindenbaum.lean, Kripke.lean and all call sites; (2) lake lint: 1 simpNF violation — mem_hilbertAxiomTheory in Equivalence.lean (simp can already prove it via mem_axiomTheory, so either remove the @[simp] tag or deduplicate); (3) lake shake: propositional import fixes — Derivation.lean remove Axioms/add Defs, DeductionTheorem.lean add Axioms, Soundness.lean add Axioms, IntSoundness.lean add Axioms, MinSoundness.lean add Axioms, MinLindenbaum.lean remove MCS, DerivedRules.lean add BVDecide.Normalize, Instances.lean add Axioms, IntMinInstances.lean add Axioms; (4) lake build warning: hilbertSubstitutionDeriv unused DecidableEq hypothesis in FromHilbert.lean:289. Fix all on main first, then update pr1/foundations-logic branch to match. Run full CI checks (lake build, lake test, lake lint, lake exe lint-style, lake exe checkInitImports, lake exe mk_all --module, lake shake) to verify

---

### 121. Review propositional metalogic cherry pick
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Review all propositional Hilbert system metalogic and parameterized ND equivalence work for quality and consistency, following CONTRIBUTING.md closely. Then cherry-pick these changes to the pr1/foundations-logic branch so that the branch contents form a coherent package ready for PR submission. Minimal logic has no ND equivalent and is excluded from the ND equivalence. The task should not submit the PR itself — only prepare the branch

---

### 112. Propositional hilbert soundness completeness
- **Status**: [EXPANDED]
- **Task Type**: lean4
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [112_propositional_hilbert_soundness_completeness/reports/01_team-research.md]
  - [112_propositional_hilbert_soundness_completeness/reports/02_team-research.md]
- **Plan**: [112_propositional_hilbert_soundness_completeness/plans/02_expansion-plan.md]

**Description**: Establish soundness and completeness for the propositional Hilbert proof systems. This is a meta-task that should be expanded into the appropriate number of sub-tasks covering: (1) propositional semantics definitions (valuations, evaluation, validity), (2) soundness theorem (axiom validity + induction on derivation trees), and (3) completeness theorem (canonical valuation from MCS, truth lemma, top-level completeness). The MCS/Lindenbaum infrastructure already exists in Metalogic/MCS.lean and Metalogic/DeductionTheorem.lean. Modal logic already has analogous results in Cslib/Logics/Modal/Metalogic/ (Soundness.lean, Completeness.lean, etc.) which can serve as a pattern. New files should go under Cslib/Logics/Propositional/Semantics/ and Cslib/Logics/Propositional/Metalogic/. Task type: lean4.

---

### 99. Complete modal cube hilbert systems
- **Status**: [EXPANDED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [099_complete_modal_cube_hilbert_systems/reports/01_team-research.md]
- **Plan**: [099_complete_modal_cube_hilbert_systems/plans/01_modal-cube-completion.md]

---

### 90. Expand modal cube proof systems metalogic
- **Status**: [EXPANDED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [090_expand_modal_cube_proof_systems_metalogic/reports/01_modal-cube-expansion.md]
- **Plan**:
  - [090_expand_modal_cube_proof_systems_metalogic/plans/01_modal-cube-expansion.md]
  - [090_expand_modal_cube_proof_systems_metalogic/plans/01_modal-cube-expansion.md]
- **Summary**: [090_expand_modal_cube_proof_systems_metalogic/summaries/01_modal-cube-expansion-summary.md]

---

### 64. Pr6 completeness theorem
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 63

---

### 63. Pr5 chronicle infrastructure
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 62

---

### 62. Pr4 temporal metalogic core
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 59, Task 61

---

### 61. Pr3 temporal proof system
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 59

---

### 60. Pr2 modal metalogic
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 59
- **Research**: [060_pr2_modal_metalogic/reports/01_team-research.md]

---

### 41. Abstract completeness infrastructure
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Foundations
- **Dependencies**: Task 38, Task 39, Task 40

**Description**: Abstract shared completeness infrastructure between temporal and bimodal logic once concrete completeness proofs are finished for both.

The temporal (tasks 31, 38, 39) and bimodal (tasks 34, 35) completeness proofs share structural patterns that can be factored into a generic completeness scaffold in Cslib/Foundations/Logic/Metalogic/, extending the existing generic MCS framework (Task 29).

Candidate abstractions (to be confirmed once concrete implementations exist):
1. Generic neg_consistent_of_not_derivable: if φ is not derivable then {¬φ} is consistent — identical structure in both logics, parameterized over DerivationSystem
2. Generic completeness contrapositive skeleton: not derivable → consistent → Lindenbaum → MCS → canonical model → countermodel — the overall proof shape is shared
3. Dense/discrete case split pattern: the three-way case split on □(F'T) / □(U(T,⊥)) / mixed is structurally similar (temporal uses G/H instead of □)
4. Canonical order construction patterns: both define canonical_lt via G-sets (temporal) or box-sets (bimodal); the linearity/irreflexivity/transitivity proofs follow parallel structures
5. Dense indicator elimination: both dense completeness proofs eliminate the non-dense branch by showing the dense indicator axiom is a theorem — identical pattern

Scope: Identify which abstractions yield genuine code savings vs. premature generalization, implement those that do, and refactor both temporal and bimodal completeness to use the shared infrastructure.

Target: Cslib/Foundations/Logic/Metalogic/Completeness.lean (or similar)
Depends on: Tasks 35 (dense bimodal), 38 (dense temporal), 39 (discrete temporal) — transitively includes 31 (base temporal) and 34 (base bimodal MCS)

---

### 40. Temporal continuous completeness
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Temporal Logic
- **Dependencies**: Task 31, Task 37

**Description**: Continuous temporal completeness: completeness for temporal logic over Dedekind-complete (continuous) linear orders, e.g. the reals.

Scope: Define a Continuous frame class extending Dense, add any required axioms (e.g., Dedekind completeness schema or equivalent), prove soundness over conditionally complete linear orders, prove completeness via canonical model on Real or equivalent.

Blocked: The continuous case has not been developed for either the temporal or bimodal logic upstream. Requires foundational research into which additional axioms (if any) are needed beyond density to characterize continuous time. The standard result (Burgess 1982) is that the Until/Since temporal logic over the reals has the same theorems as over the rationals (density suffices), which would make this task trivial — but this equivalence itself needs to be formalized.

Target: Cslib/Logics/Temporal/Metalogic/ContinuousCompleteness.lean
Blocker: Research needed on whether continuous frames require additional axioms beyond density

---

### 39. Temporal discrete completeness
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Temporal Logic
- **Dependencies**: Task 31, Task 36

**Description**: Discrete temporal completeness: prove that every formula valid on all discrete serial linear orders is derivable in the Discrete temporal proof system.

Scope:
1. Add discrete-specific axioms to Temporal.Axiom: `prior_UZ` (F(φ) → U(φ,¬φ)), `prior_SZ` (P(φ) → S(φ,¬φ)), `z1` (G(Gφ→φ) → (F(Gφ)→Gφ)), and discrete uniformity axioms (discrete_symm_fwd/bwd, discrete_propagate_fwd/bwd), gated to FrameClass.Discrete via minFrameClass.
2. Prove discrete soundness: each discrete axiom valid on SuccOrder+PredOrder+IsSuccArchimedean.
3. Prove discrete completeness via contrapositive + MCS + canonical model on Int. The non-discrete branch is eliminated by deriving U(⊤,⊥) as a Discrete theorem.

New development (not a port). The canonical model specializes the base temporal canonical order to Int. The discrete uniformity axioms (minus discrete_box_necessity which is bimodal-only) ensure U(⊤,⊥) propagates uniformly.

Target: Cslib/Logics/Temporal/Metalogic/DiscreteCompleteness.lean + axiom additions to Axioms.lean
Estimated scope: ~500-700 lines (new axioms + discrete soundness + discrete completeness)

---

### 38. Temporal dense completeness
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Temporal Logic
- **Dependencies**: Task 31, Task 49

**Description**: Dense temporal completeness: prove that every formula valid on all dense serial linear orders is derivable in the Dense temporal proof system.

Scope:
1. Add dense-specific axioms to Temporal.Axiom: `density` (G(G φ) → G φ) and `dense_indicator` (¬U(⊤,⊥)), gated to FrameClass.Dense via minFrameClass.
2. Prove dense soundness: density axiom valid on DenselyOrdered, dense_indicator valid on DenselyOrdered (no immediate successor).
3. Prove dense completeness via contrapositive + MCS + canonical model on Rat. The dense case eliminates the non-dense branch by deriving ¬U(⊤,⊥) as a Dense theorem, so □(¬U(⊤,⊥)) is in every Dense-MCS.

New development (not a port), following the pattern established by bimodal completeness_dense. The canonical model construction reuses the base temporal canonical order from task 31, specialized to Rat (DenselyOrdered).

Target: Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean + axiom additions to Axioms.lean
Estimated scope: ~400-600 lines (new axioms + dense soundness + dense completeness)

---

### 37. Port continuous completeness bimodal
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Bimodal Porting
- **Dependencies**: Task 35, Task BimodalLogic:continuous_extension

**Description**: Port continuous extension completeness once developed upstream. The continuous case (FrameClass for continuous/real-valued time) has not been started in BimodalLogic. This task is blocked pending upstream development of continuous frame completeness.

**Source**: Not yet developed in BimodalLogic
**Target**: Cslib/Logics/Bimodal/Metalogic/
**Blocker**: Upstream BimodalLogic continuous extension development
**Parent task**: 8 (expanded)

---

### 36. Port discrete completeness bimodal
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Bimodal Porting
- **Dependencies**: Task 35, Task BimodalLogic:discrete_sorry_elimination

**Description**: Port discrete completeness (completeness_discrete theorem) and WeakCanonical/IntegerModel/ infrastructure (~6 files). The discrete branch constructs countermodels on Int via the Reynolds pipeline. Currently blocked: upstream BimodalLogic has sorryAx tracing through chronicle_gap_contradiction → succ_cofinal → limitDomSubtype_isSuccArchimedean → succ_embed_surjective. Port after upstream sorry elimination completes.

**Source**: BimodalLogic/Theories/Bimodal/Metalogic/WeakCanonical/IntegerModel/ (~6 files), discrete branch of BXCanonical/Completeness.lean
**Target**: Cslib/Logics/Bimodal/Metalogic/
**Blocker**: Upstream BimodalLogic discrete completeness sorry elimination (36 sorries across IntegerModel/)
**Parent task**: 8 (expanded)

---

### 31. Temporal metalogic
- **Status**: [EXPANDED]
- **Task Type**: lean4
- **Topic**: Temporal Logic
- **Dependencies**: Task 49

**Description**: Expanded into tasks 46 (R-relation), 47 (point insertion), 48 (chronicle construction), 49 (truth lemma + completeness). Phases 1-5 completed: DeductionTheorem, MCS, Soundness, helper lemmas. Phase 6 (Completeness) requires Burgess point-insertion method (~4K-7K lines), too large for a single task.

---

### 12. Coordinate cslib pr submission bimodal logic
- **Status**: [EXPANDED]
- **Task Type**: general
- **Topic**: Project Management
- **Dependencies**: Task 41

**Description**: Coordinate the cslib PR submission process for the modular logic integration (standalone modules + bimodal). This task runs in parallel with porting tasks and handles maintainer communication, namespace decisions, and CI compliance.

**Standalone Module PRs** (can proceed in parallel with bimodal PRs since they target different directories):
- PR-Foundations (Task 20): Propositional Hilbert theorems to Cslib/Foundations/Logic/Theorems/ -- Wave 1, no dependencies
- PR-Modal (Task 21): Modal proof system + theorems to Cslib/Logics/Modal/ProofSystem/ + Theorems/ -- after PR-Foundations
- PR-Temporal-Infra (Task 22): Temporal infrastructure + theorems to Cslib/Logics/Temporal/ProofSystem/ + Theorems/ -- after PR-Foundations
- PR-TempSem (Task 23): Temporal semantics to Cslib/Logics/Temporal/Semantics/ -- after PR-Temporal-Infra

**Bimodal PRs** (in dependency order):
- PR 1 (Bimodal Syntax, task 2): submit first, establish review pattern
- PR 2 (Semantics, task 3) and PR 3 (ProofSystem, task 4): after PR 1 merged, can overlap
- PR 4 (Perpetuity Theorems, task 5): after PRs 3, PR-Modal, PR-Temporal-Infra merged
- PR 5 (FrameConditions+Soundness, task 6): after PRs 2+3 merged
- PR 6 (MCS/Deduction, task 7): after PRs 3+4 merged
- PR 7 (Completeness, task 8): after PRs 5+6 merged
- PR 8 (Decidability, task 9): after PRs 3+6 merged (largest PR, ~10k lines)
- PR 9 (Separation, task 10): after PRs 3+4+6 merged
- PR 10 (ConservativeExtension, task 11): after PR 3 merged (independent of 5-9)

**Coordination Workflow**:

1. **Open Zulip Discussion** (first step): propose modular architecture (standalone Foundations/Modal/Temporal modules + Bimodal), PR strategy (4 standalone PRs + 10 bimodal PRs)
2. **Namespace Decision**: confirm before starting task 2
3. **CI Checks** (before each PR): lake build, lake shake, linter.all, zero sorry, Apache 2.0 headers
4. **Review Cycle**: keep PRs small (max ~3,500 lines); address feedback within 48 hours

---

### 9. Port decidability tableau bimodal
- **Status**: [EXPANDED]
- **Task Type**: lean4
- **Topic**: Bimodal Porting
- **Dependencies**: Task 4, Task 7
- **Research**: [009_port_decidability_tableau_bimodal/reports/01_team-research.md]

**Description**: Port Decidability and Tableau (PR 8): SignedFormula, Tableau, Closure, Saturation, ProofExtraction, Correctness, DecisionProcedure, CountermodelExtraction, FMP/* to Cslib/Logics/Bimodal/Metalogic/Decidability/. This is the largest PR (~10k lines) covering the full tableau-based decision procedure for TM logic.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/Decidability/):
- SignedFormula.lean (~400 lines): signed formula type for tableau
- Tableau.lean (~1,800 lines): main tableau expansion rules (28 rules), termination proof
- Closure.lean (~600 lines): closure conditions, saturation definition
- Saturation.lean (~800 lines): saturation lemmas, model extraction framework
- ProofExtraction.lean (~600 lines): extract DerivationTree from closed tableau branch
- Correctness.lean (~400 lines): tableau soundness (closed = provable) and completeness (non-closed = satisfiable)
- DecisionProcedure.lean (~500 lines): decide function, decidability instance
- CountermodelExtraction.lean (~600 lines): extract countermodel from open saturated tableau
- FMP/*.lean (~4 files, ~3,000 lines): finite model property (closure MCS construction, bounded model size)

**Target path**: Cslib/Logics/Bimodal/Metalogic/Decidability/

**Estimated scope**: ~10,000 lines across 18+ files

**PR title**: feat(Logics/Bimodal): add Metalogic/Decidability module (Tableau, FMP, DecisionProcedure)

**Note**: This PR may benefit from splitting into two sub-tasks: (9a) Core tableau/decision procedure (~5k lines) and (9b) FMP (~4k lines). Consider splitting if review burden is too high.

**Dependencies**: Tasks 4 (ProofSystem) and 7 (MCS/Deduction) must be merged first.

**Porting Checklist (apply to every file in this PR)**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Bimodal
- [ ] Add module declaration at top: namespace Cslib.Logics.Bimodal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)
