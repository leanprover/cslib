---
next_project_number: 121
---

# TODO

## Task Order

*Updated 2026-06-11. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,38,60,61 | -- | Temporal Logic, Bimodal Porting, Submit PRs |
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

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

## Tasks

### 120. Parameterize natural deduction equivalence
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 113
- **Research_report**: [120_parameterize_natural_deduction_equivalence/reports/01_nd-parameterization.md]
- **Plan**: [120_parameterize_natural_deduction_equivalence/plans/01_nd-parameterization.md]
- **Summary**: [120_parameterize_natural_deduction_equivalence/summaries/01_nd-parameterization-summary.md]

**Description**: Refactor NaturalDeduction files to eliminate backward-compat aliases and parameterize the Hilbert-ND equivalence by logic subsystem. Split HilbertDerivedRules.lean into an intuitionistic layer (negI, negE, topI, andI, orI1, orI2, iffI) and a classical layer (dne, andE1, andE2, orE, iffE1, iffE2). Parameterize FromHilbert.lean and Equivalence.lean over any Axioms that include K, S, and EFQ, covering both intuitionistic and classical as special cases. The ND system (Theory.Derivation) has botE as a primitive constructor so it is inherently at least intuitionistic; minimal logic ND equivalence is out of scope. Research report: specs/113_refactor_derivation_tree_axiom_types/reports/02_natded-refactor-research.md. Files to modify: NaturalDeduction/FromHilbert.lean, NaturalDeduction/HilbertDerivedRules.lean, NaturalDeduction/Equivalence.lean. Files already generic (no changes needed): NaturalDeduction/Basic.lean, NaturalDeduction/DerivedRules.lean. Risk: LOW — NaturalDeduction files are leaf modules (nothing imports them).

---

### 119. Modal code quality audit
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [119_modal_code_quality_audit/reports/01_team-research.md]
- **Plan**: [119_modal_code_quality_audit/plans/01_code-quality-plan.md]
- **Summary**: [119_modal_code_quality_audit/summaries/01_implementation-summary.md]

**Description**: Review and improve the Cslib/Logics/Modal/ directory: audit all 20+ new soundness/completeness files (B, K4, K5, K45, KB5, TB, D4, D5, D45, DB) and the modified infrastructure files (ProofSystem.lean, Instances.lean, Completeness.lean) for code quality improvements. Look for: (1) duplicated proof patterns that could be factored into shared lemmas, (2) linter warnings (flexible simp, unused variables) that should be cleaned up, (3) inconsistent naming or style across files, (4) opportunities to simplify proofs using existing Mathlib/cslib automation, (5) missing or incorrect docstrings, (6) any sorry or vacuous definitions that slipped through, (7) whether the Metalogic.lean import ordering follows a consistent convention

---

### 118. Propositional completeness integration
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Propositional Logic
- **Dependencies**: Task 113, Task 114, Task 115, Task 116, Task 117

**Description**: Update Cslib.lean imports to include all new propositional metalogic modules (Semantics/Basic, Semantics/Kripke, Soundness, Completeness, IntSoundness, IntLindenbaum, IntCompleteness, MinSoundness, MinCompleteness, IntMinInstances). Prove semantic coherence theorem for FromPropositional.lean connecting propositional tautology to modal validity for propositional formulas (~20-30 lines). Run full lake build and lean_verify on prop_completeness, int_completeness, min_completeness to confirm no sorry and no non-standard axioms. Parent task: 112 (Phase 6). Depends on: tasks 113, 114, 115, 116, 117. Task type: lean4.

---

### 117. Minimal propositional soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Propositional Logic
- **Dependencies**: Task 113, Task 115, Task 116

**Description**: Prove soundness and completeness of HilbertMin with respect to minimal Kripke semantics. Reuses intuitionistic infrastructure from task 116 with different bot_forces instantiation: bot_forces w = (Proposition.bot in w) instead of fun _ => False. Create Metalogic/MinSoundness.lean with min_axiom_sound (2 cases: K, S only) and min_soundness. Create Metalogic/MinCompleteness.lean with adapted canonical model where bot can be forced at some worlds (upward-closed), min_truth_lemma, min_completeness. Literature: Minimal logic (Johansson 1937) treats bot as a propositional atom with upward-closed valuation. Parent task: 112 (Phase 5). Depends on: tasks 113, 115, 116. Task type: lean4.

---

### 116. Intuitionistic propositional soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Propositional Logic
- **Dependencies**: Task 113, Task 115

**Description**: Prove soundness and completeness of HilbertInt with respect to intuitionistic Kripke semantics. Create Metalogic/IntSoundness.lean with int_axiom_sound (3 cases: K, S, EFQ) and int_soundness by induction on DerivationTree. Create Metalogic/IntLindenbaum.lean with prime theory definition (deductively closed, consistent, disjunction property expressed via imp/bot primitives), int_lindenbaum (every consistent set extends to a prime deductively-closed theory, adapting Zorn pattern from Consistency.lean). Create Metalogic/IntCompleteness.lean with canonical Kripke model (worlds = prime theories, accessibility = set inclusion, valuation = atom membership), int_truth_lemma (imp case uses universal quantification over accessible worlds and deduction theorem), int_completeness. Literature: CZ Section 2.6 Theorem 2.43 (specs/literature/modal_logic.md lines 2353-2412) for completeness of Int. CZ Section 5.1 (lines 5832-5910) for Lindenbaum pattern. Parent task: 112 (Phase 4). Depends on: tasks 113, 115. Task type: lean4.

---

### 115. Propositional kripke semantics
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Propositional Logic
- **Dependencies**: Task 113

**Description**: Define propositional Kripke semantics with a parameterized forcing function reusing Modal.Model with partial-order and persistence constraints as hypotheses. Create Semantics/Kripke.lean with IForces parameterized by bot_forces : World -> Prop (intuitionistic instantiates with fun _ => False, minimal with upward-closed valuation). Prove iforces_persistence by structural induction on formulas. Define IValid (validity over all intuitionistic frames) and MValid (validity over all minimal frames). Literature: CZ Section 2.2 (specs/literature/modal_logic.md lines 1564-1642) for intuitionistic Kripke frames, valuations, forcing. CZ Proposition 2.1 (lines 1627-1630) for persistence. Parent task: 112 (Phase 3). Depends on: task 113. Task type: lean4.

---

### 114. Classical propositional soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Define bivalent truth-value semantics and prove soundness and completeness for classical propositional logic (HilbertCl). Create Semantics/Basic.lean with Valuation (Atom -> Prop), Evaluate, and Tautology. Create Metalogic/Soundness.lean with prop_axiom_sound (4 cases: K, S, EFQ, Peirce) and prop_soundness by induction on DerivationTree. Create Metalogic/Completeness.lean with canonicalValuation from MCS, prop_truth_lemma, and prop_completeness. Direct simplification of modal K completeness in KCompleteness.lean lines 168-323. Literature: CZ Chapter 5 Section 5.1 (specs/literature/modal_logic.md lines 5832-5910) for Henkin/canonical model construction. Parent task: 112 (Phase 2). Task type: lean4.

---

### 113. Refactor derivation tree axiom types
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Refactor propositional DerivationTree to be parameterized over an axiom predicate (uniform with Modal/Temporal/Bimodal pattern). Change signature from DerivationTree Gamma phi to DerivationTree (Axioms : PL.Proposition Atom -> Prop) Gamma phi. Update all downstream files: Derivation.lean, DeductionTheorem.lean, MCS.lean, Instances.lean. Create IntPropAxiom (implyK, implyS, efq) and MinPropAxiom (implyK, implyS) inductive types in Axioms.lean. Register IntuitionisticHilbert HilbertInt and MinimalHilbert HilbertMin instances in new IntMinInstances.lean. Literature: CZ Chapter 1 axiom schemata. Parent task: 112 (Phase 1). Task type: lean4.

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

### 111. Modal cube integration
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Update Metalogic.lean module aggregator with all 20 new imports. Verify lake build passes for the full module and project. Confirm no sorry or axioms in any new theorem via lean_verify.

---

### 110. Modal db soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prove soundness and completeness for modal logic DB (K + D + B) over serial + symmetric frames. Soundness via Satisfies.d + Satisfies.b; completeness via truth_lemma_d + canonical_serial + canonical_symm. Create DBSoundness.lean and DBCompleteness.lean.

---

### 109. Modal d45 soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prove soundness and completeness for modal logic D45 (K + D + 4 + 5) over serial + transitive + Euclidean frames. Soundness via Satisfies.d + Satisfies.four + Satisfies.five; completeness via truth_lemma_d + canonical_serial + canonical_trans + canonical_eucl_from_5. Create D45Soundness.lean and D45Completeness.lean.

---

### 108. Modal d5 soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prove soundness and completeness for modal logic D5 (K + D + 5) over serial + Euclidean frames. Soundness via Satisfies.d + Satisfies.five; completeness via truth_lemma_d + canonical_serial + canonical_eucl_from_5. Create D5Soundness.lean and D5Completeness.lean.

---

### 107. Modal d4 soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prove soundness and completeness for modal logic D4 (K + D + 4) over serial + transitive frames. Soundness via Satisfies.d + Satisfies.four; completeness via truth_lemma_d + canonical_serial + canonical_trans. Create D4Soundness.lean and D4Completeness.lean.

---

### 106. Modal kb5 soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prove soundness and completeness for modal logic KB5 (K + B + 5) over symmetric + Euclidean frames. Soundness via Satisfies.b + Satisfies.five; completeness via k_truth_lemma + canonical_symm + canonical_eucl_from_5. Create KB5Soundness.lean and KB5Completeness.lean. First logic using both new canonical lemmas together.

---

### 105. Modal tb soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prove soundness and completeness for modal logic TB (K + T + B) over reflexive + symmetric frames. Soundness via Satisfies.t + Satisfies.b; completeness via truth_lemma (T-based) + canonical_refl + canonical_symm. Create TBSoundness.lean and TBCompleteness.lean.

---

### 104. Modal k45 soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prove soundness and completeness for modal logic K45 (K + 4 + 5) over transitive + Euclidean frames. Soundness via Satisfies.four + Satisfies.five; completeness via k_truth_lemma + canonical_trans + canonical_eucl_from_5. Create K45Soundness.lean and K45Completeness.lean.

---

### 103. Modal k5 soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prove soundness and completeness for modal logic K5 (K + axiom 5) over Euclidean frames. Soundness via Satisfies.five; completeness via k_truth_lemma + canonical_eucl_from_5. Create K5Soundness.lean and K5Completeness.lean.

---

### 102. Modal k4 soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prove soundness and completeness for modal logic K4 (K + axiom 4) over transitive frames. Soundness via Satisfies.four; completeness via k_truth_lemma + canonical_trans. Create K4Soundness.lean and K4Completeness.lean.

---

### 101. Modal b soundness completeness
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prove soundness and completeness for modal logic B (K + axiom B) over symmetric frames. Soundness via Satisfies.b; completeness via k_truth_lemma + canonical_symm. Create BSoundness.lean and BCompleteness.lean.

---

### 100. Modal cube shared infrastructure
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prove canonical_symm (symmetry from axiom B alone) and canonical_eucl_from_5 (Euclideanness from axiom 5 alone). Add 10 new tag types and bundled classes to ProofSystem.lean. Define 10 axiom predicates and register all typeclass instances in Instances.lean. This is the critical infrastructure phase that unblocks all other modal cube tasks.

---

### 99. Complete modal cube hilbert systems
- **Status**: [EXPANDED]
- **Task Type**: lean4
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [099_complete_modal_cube_hilbert_systems/reports/01_team-research.md]
- **Plan**: [099_complete_modal_cube_hilbert_systems/plans/01_modal-cube-completion.md]

---

### 91. Pr 1 5 propositional hilbert submission
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: Submit PRs
- **Dependencies**: Task 59
- **Research**: [091_pr_1_5_propositional_hilbert_submission/reports/01_pr-scope-review.md]
- **Plan**:
  - [091_pr_1_5_propositional_hilbert_submission/plans/01_pr-submission-plan.md]
  - [091_pr_1_5_propositional_hilbert_submission/plans/02_combined-pr-submission.md]
- **Summary**: [091_pr_1_5_propositional_hilbert_submission/summaries/02_combined-pr-summary.md]

**Description**: Combined PR 1+1.5 submission: close PR #629, update pr1/foundations-logic with PR 1.5 additions (tasks 86-89), run full CI suite, and resubmit as a single PR covering the complete Foundations/Logic + Propositional Hilbert system.

Phase 1: Apply 16 files from main onto pr1/foundations-logic (git checkout main -- <files> + 3 Cslib.lean imports)
Phase 2: Code quality review (sorry check, lint, DecidableEq fix, documentation)
Phase 3: Full CI suite (lake build, test, checkInitImports, lint, lint-style, mk_all, shake)
Phase 4: Close #629, force-push updated branch, submit new PR

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
