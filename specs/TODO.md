---
next_project_number: 99
---

# TODO

## Task Order

*Updated 2026-06-11. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,38,60,61,91,98 | -- | Temporal Logic, Bimodal Porting, Submit PRs, ... |
| 2 | 39,40,62 | 36,37,61 | Temporal Logic, Submit PRs |
| 3 | 41,63 | 38,39,40,62 | Submit PRs, Foundations |
| 4 | 64 | 63 | Submit PRs |

**Grouped by Topic** (indented = depends on parent):

### Temporal Logic

38 [NOT STARTED] — Dense temporal completeness: prove that every formula valid on al
  └─ 41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
  └─ 41 [NOT STARTED] — (Foundations: Abstract shared completeness infrastruct) (see above)
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic
  └─ 41 [NOT STARTED] — (Foundations: Abstract shared completeness infrastruct) (see above)

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
  └─ 39 [NOT STARTED] — (Temporal Logic: Discrete temporal completeness: prove th) (see above)
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 40 [BLOCKED] — (Temporal Logic: Continuous temporal completeness: comple) (see above)

### Submit PRs

60 [RESEARCHED] — pr2_modal_metalogic
61 [NOT STARTED] — pr3_temporal_proof_system
  └─ 62 [NOT STARTED] — pr4_temporal_metalogic_core
    └─ 63 [NOT STARTED] — pr5_chronicle_infrastructure
      └─ 64 [NOT STARTED] — pr6_completeness_theorem
91 [PLANNED] — Create feature branch and submit PR 1.5 containing the propositio

### Modal Logic

98 [NOT STARTED] — Phase 7 of modal cube expansion: Final integration and verificati

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

## Tasks

### 98. Modal cube final integration
- **Effort**: small
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: Task 95, Task 96, Task 97

**Description**: Phase 7 of modal cube expansion: Final integration and verification. Create or update Modal/ProofSystem.lean aggregator to import Instances.lean. Update Modal/Metalogic.lean aggregator to import per-system soundness/completeness files. Verify original S5 Soundness.lean and Completeness.lean compile alongside new per-system files. Verify Bimodal/ProofSystem/Instances.lean still compiles. Verify Foundations/Logic/Theorems/Modal/S5.lean works with refactored ModalS5Hilbert. Update Metalogic.lean module docstring to reflect multi-system support. Full lake build with zero errors.

Files to modify: Modal/Metalogic.lean, Modal/ProofSystem.lean, various documentation strings.

Estimated: ~1.5 hours.

---

### 97. Modal s4 soundness completeness
- **Effort**: medium
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: Task 93
- **Plan**: [097_modal_s4_soundness_completeness/plans/02_s4-soundness-completeness.md]

**Description**: Phase 6 of modal cube expansion: Establish soundness and completeness for modal logic S4 (reflexive + transitive frames) with sorry-free proofs.

**RESEARCH REQUIREMENT — Literature First**: The canonical model completeness proof for S4 is entirely standard. The research phase MUST:
1. Search for and download a PDF source containing the full canonical model completeness proof for S4 (e.g., Blackburn/de Rijke/Venema "Modal Logic" Ch. 4, Chellas "Modal Logic: An Introduction", or high-quality lecture notes covering completeness for S4 via canonical models with reflexive + transitive frame conditions).
2. Convert the relevant PDF pages to markdown reference files stored in the task directory (specs/097_.../references/).
3. The research report must include verbatim theorem statements, proof structure (especially the transitivity argument from axiom 4), and key lemma dependencies extracted from the source material.

**Planning and implementation** must draw directly on the converted reference files.

**Proof targets**:
- S4 soundness: combining T soundness (reflexivity) and 4 soundness (transitivity, ~70 lines)
- S4 completeness: canonical model is reflexive (from axiom T) AND transitive (from axiom 4). Reuse canonical_refl from T, canonical_trans from S5. Box witness identical to T case (~220 lines)

New files: Metalogic/Soundness/S4.lean, Metalogic/Completeness/S4.lean.

Estimated: ~3 hours. Parallelizable with phases 4 and 5.

---

### 96. Modal d soundness completeness
- **Effort**: medium
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: Task 93
- **Research**: [096_modal_d_soundness_completeness/reports/01_d-soundness-completeness.md]
- **Plan**: [096_modal_d_soundness_completeness/plans/02_d-soundness-completeness.md]

**Description**: Phase 5 of modal cube expansion: Establish soundness and completeness for modal logic D (serial frames) with sorry-free proofs.

**RESEARCH REQUIREMENT — Literature First**: The canonical model completeness proof for D is entirely standard. The research phase MUST:
1. Search for and download a PDF source containing the full canonical model completeness proof for D / serial frames (e.g., Blackburn/de Rijke/Venema "Modal Logic" Ch. 4, Chellas "Modal Logic: An Introduction", or high-quality lecture notes on completeness for normal modal logics including the seriality condition).
2. Convert the relevant PDF pages to markdown reference files stored in the task directory (specs/096_.../references/).
3. The research report must include verbatim theorem statements, proof structure (especially the seriality argument for the canonical model), and key lemma dependencies extracted from the source material.

**Planning and implementation** must draw directly on the converted reference files.

**Proof targets**:
- D soundness: using Relation.Serial (~60 lines)
- D completeness: canonical model is serial. Seriality proof: inconsistency of {psi | box psi in S} implies box(bot) in S, then D gives diamond(bot), combined with box(top) in S yields bot in S, contradiction. Box witness uses K-style argument (~250 lines)

New files: Metalogic/Soundness/D.lean, Metalogic/Completeness/D.lean.

Estimated: ~3 hours. Parallelizable with phases 4 and 6.

---

### 95. Modal k t soundness completeness
- **Effort**: large
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: Task 93

**Description**: Phase 4 of modal cube expansion: Establish soundness and completeness for modal logics K and T with sorry-free proofs.

**RESEARCH REQUIREMENT — Literature First**: The canonical model completeness proofs for K and T are entirely standard. The research phase MUST:
1. Search for and download a PDF source containing the full canonical model completeness proofs for K and T (e.g., Blackburn/de Rijke/Venema "Modal Logic" Ch. 4, Chellas "Modal Logic: An Introduction" Ch. 5-6, Hughes & Cresswell "A New Introduction to Modal Logic", or high-quality lecture notes covering Henkin-style completeness for normal modal logics).
2. Convert the relevant PDF pages to markdown reference files stored in the task directory (specs/095_.../references/).
3. The research report must include verbatim theorem statements, proof structure, and key lemma dependencies extracted from the source material — not reinvented from scratch.

**Planning and implementation** must draw directly on the converted reference files to ensure proofs follow the standard textbook structure rather than ad-hoc reconstruction.

**Proof targets**:
- K soundness: propositional + K distribution axioms valid on all frames (~80 lines)
- K completeness: canonical model with no frame property requirements, box witness via K-specific argument (~250 lines)
- T soundness: reflexive frames (~60 lines)
- T completeness: canonical model is reflexive from axiom T / mcs_box_closure (~200 lines)

New files: Metalogic/Soundness/K.lean, Metalogic/Completeness/K.lean, Metalogic/Soundness/T.lean, Metalogic/Completeness/T.lean.

Estimated: ~5 hours. Parallelizable with phases 5 and 6.

---

### 94. Modal integrate hilbert derived rules
- **Effort**: small
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: Task 92

**Description**: Phase 3 of modal cube expansion: Add the untracked HilbertDerivedRules.lean (447 lines, already sorry-free) to the build by importing it into the module graph. Determine appropriate import point (NaturalDeduction aggregator or Equivalence.lean). Add public import to chosen aggregator. Verify the file compiles in CI context and lake build passes.

Files: Cslib/Logics/Propositional/NaturalDeduction.lean or equivalent aggregator (add import). HilbertDerivedRules.lean itself needs no changes.

Estimated: ~30 minutes.

---

### 93. Modal s5 preservation instances
- **Effort**: medium
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: Task 92
- **Summary**: [093_modal_s5_preservation_instances/summaries/01_modal-system-instances-summary.md]

**Description**: Phase 2 of modal cube expansion: Create Modal/ProofSystem/Instances.lean registering typeclass instances for all modal systems (K, T, D, S4, S5), following the Temporal pattern. Register InferenceSystem, ModusPonens, Necessitation instances for each tag type. Register propositional axiom instances (HasAxiomImplyK, HasAxiomImplyS, HasAxiomEFQ, HasAxiomPeirce) and modal axiom instances (HasAxiomK, HasAxiomT, HasAxiom4, HasAxiomB, HasAxiomD as appropriate). Register bundled class instances (ModalHilbert for K, ModalTHilbert for T, ModalDHilbert for D, ModalS4Hilbert for S4, ModalS5Hilbert for S5). Verify Soundness.lean and Completeness.lean still compile with S5 parameterization. Update Metalogic.lean aggregator to import Instances.lean.

Files: NEW Cslib/Logics/Modal/ProofSystem/Instances.lean (~400 lines), Modal/Metalogic.lean, possibly Soundness.lean and Completeness.lean adaptations.

Estimated: ~3 hours.

---

### 92. Modal infrastructure parameterize derivation tree
- **Effort**: large
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Phase 1 of modal cube expansion: Parameterize DerivationTree over an axiom predicate so it works for any normal modal logic. Define per-system axiom inductive types (AxiomK, AxiomT, AxiomD, AxiomS4) alongside existing ModalAxiom. Parameterize DerivationTree, height function, Deriv, Derivable, and modalDerivationSystem over Axioms : Proposition Atom -> Prop. Create type alias so ModalAxiom becomes the S5 axiom set for backward compatibility. Generalize DeductionTheorem.lean (mechanical, DT never inspects axiom payload). Generalize MCS.lean: parameterize modal-specific properties, keep S5-specific lemmas under explicit axiom assumptions. Add ModalTHilbert, ModalDHilbert, ModalS4Hilbert bundled classes and Modal.HilbertT, Modal.HilbertD, Modal.HilbertS4 tag types to ProofSystem.lean. Refactor ModalS5Hilbert to extend ModalS4Hilbert with HasAxiomB. Verify full project builds with zero regressions.

Files to modify: Metalogic/DerivationTree.lean, Metalogic/DeductionTheorem.lean, Metalogic/MCS.lean, Foundations/Logic/ProofSystem.lean, Bimodal/ProofSystem/Instances.lean (if needed).

Estimated: ~5 hours, highest-risk phase. Fallback: if parameterization proves infeasible, create separate DerivationTree types per system.

---

### 91. Pr 1 5 propositional hilbert submission
- **Status**: [PLANNED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 59
- **Research**: [091_pr_1_5_propositional_hilbert_submission/reports/01_pr-scope-review.md]
- **Plan**: [091_pr_1_5_propositional_hilbert_submission/plans/01_pr-submission-plan.md]

**Description**: Create feature branch and submit PR 1.5 containing the propositional Hilbert system additions developed since PR 1 (tasks 87, 88, 89). This PR adds ~1,200 new lines across 3 new files and updates to 11 existing files in Logics/Propositional/ and Foundations/Logic/.

**New files**:
- NaturalDeduction/Equivalence.lean (168 lines): extensional equivalence between Hilbert and ND proof systems (hilbert_iff_nd theorem)
- NaturalDeduction/DerivedRules.lean (386 lines): 13 derived intro/elim rules for Łukasiewicz-encoded connectives (and, or, neg, iff, top, dne) in the ND system
- NaturalDeduction/HilbertDerivedRules.lean (447 lines): matching Hilbert system derived rules

**Modified files** (Foundations/Logic/ typeclass refactor):
- ProofSystem.lean: three-level Hilbert typeclass hierarchy (MinimalHilbert → IntuitionisticHilbert → ClassicalHilbert)
- Theorems/Propositional/Core.lean + Connectives.lean: theorems stratified across the hierarchy
- Theorems/Combinators.lean, Theorems.lean, BigConj.lean: weakened to MinimalHilbert
- ProofSystem/Instances.lean: updated for new hierarchy
- Defs.lean: added Proposition.iff
- Metalogic/DeductionTheorem.lean, MCS.lean: minor updates

**PR title**: `feat(Logics/Propositional): Hilbert-ND equivalence, derived connective rules, and intuitionistic base hierarchy`

**Workflow**: Create branch pr1.5/propositional-hilbert from main, cherry-pick or rebase the relevant commits (tasks 87-89 changes), run CI checks (lake build, lake shake, linter.all, zero sorry, Apache 2.0 headers), prepare PR description, push and open PR.

**Dependencies**: PR 1 (task 59, Foundations/Logic) should be merged first since PR 1.5 modifies files from PR 1. If PR 1 is still in review, coordinate with maintainers about stacking.

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

### 89. Derived connective rules
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: None

**Description**: Add derived intro/elim rules for defined propositional connectives (∧ₚ, ∨ₚ, ¬ₚ, ↔ₚ, ⊤ₚ) in both the standalone ND system (NaturalDeduction/Basic.lean) and the Hilbert system (FromHilbert.lean wrappers). Connectives are already defined as abbrevs reducing to →/⊥ in Defs.lean (Łukasiewicz encodings). Follow the existing pattern: abbrev + notation + standalone theorems with definitional unfolding. For each connective, provide standard intro/elim rules at both the type level (DerivationTree / Theory.Derivation) and the Prop level (Deriv / DerivableIn). Rules needed: andI, andE₁, andE₂, orI₁, orI₂, orE, negI, negE, dne (double negation elimination), iffI, iffE₁, iffE₂, topI. Both systems should end up equally versatile. Reference temporal defined operators in Temporal/ for the uniform approach.

---

### 88. Refactor propositional hilbert intuitionistic base
- **Status**: [COMPLETED]
- **Task Type**: formal
- **Dependencies**: None
- **Plan**: [088_refactor_propositional_hilbert_intuitionistic_base/plans/01_intuitionistic-base-plan.md]
- **Summary**: [088_refactor_propositional_hilbert_intuitionistic_base/summaries/01_intuitionistic-base-summary.md]

---

### 87. Derive nd from hilbert
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: None

---

### 86. Pr1 lint quality audit
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: None

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
