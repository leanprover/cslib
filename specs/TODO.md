---
next_project_number: 51
---

# Tasks

## Task Order

*Updated 2026-06-09. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,38,46,50 | -- | Temporal Logic, Bimodal Porting |
| 2 | 39,40,47 | 36,37,46 | Temporal Logic |
| 3 | 41,48 | 38,39,40,47 | Foundations, Temporal Logic |
| 4 | 12,49 | 41,48 | Temporal Logic, Project Management |

**Grouped by Topic** (indented = depends on parent):

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and  (dep: 38, 39, 40)

### Temporal Logic

38 [NOT STARTED] — Dense temporal completeness: prove that every formula valid on al
46 [NOT STARTED] — Define the Burgess R-relation r(A, beta, C) and prove its key pro
  └─ 47 [NOT STARTED] — Define the labeled frame type (Burgess K-elements) and prove that
    └─ 48 [NOT STARTED] — Build the omega-step construction that enumerates all C5/C6 count
      └─ 49 [NOT STARTED] — Prove the truth lemma on the constructed chronicle frame and clos
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on (dep: 36)
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic (dep: 37)

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T

### Project Management

12 [PARTIAL] — Coordinate the cslib PR submission process for the modular logic  (dep: 41)

### Uncategorized

50 [NOT STARTED] — burgess_prior_art_seed_research

## Tasks


### 50. Research Burgess prior art and seed research for tasks 46-49
- **Effort**: large
- **Status**: [NOT STARTED]
- **Task Type**: lean4

**Description**: Research the relevant prior art in /home/benjamin/Projects/BimodalLogic/literature/ that can help with the Burgess-style completeness (tasks 46-49, 31) and carefully review what infrastructure exists in the Bimodal/ metalogic in this repo that can either be abstracted or adapted since these elements came from the same literature sources. The aim is to improve the descriptions and create seed research reports with relevant findings for tasks 46-49 in order to streamline their research, planning, and implementation going forward.

---

### 31. Temporal metalogic [EXPANDED]
- **Status**: [EXPANDED] — split into tasks 46, 47, 48, 49
- **Research**: [specs/031_temporal_metalogic/reports/03_completeness-blockers.md]

Phases 1-5 completed (DeductionTheorem, MCS, Soundness, helper lemmas). Phase 6 (Completeness) requires the Burgess point-insertion method (~4K-7K lines), expanded into 4 sub-tasks following the bimodal Chronicle template (14,944 lines in BXCanonical/).

---

### 46. Temporal R-relation and witness infrastructure
- **Effort**: Large (10-15 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: None
- **Parent**: Task 31 (expanded)

**Description**: Define the Burgess R-relation `r(A, beta, C)` and prove its key properties (Lemmas 2.2-2.4) for temporal MCS, plus ordered seed consistency and canonical chain lemmas.

**Literature**: Burgess 1982 Section 2 Lemmas 2.2-2.4 (`BimodalLogic/literature/Burgess_1982_Axioms_for_tense_logic_Since_and_Until.md`)

**Bimodal prior art to adapt**:
- `BXCanonical/Chronicle/RRelation.lean` (1695 lines): r_relation, R_maximal, witness existence
- `BXCanonical/CanonicalChain.lean` (95 lines): BX12/BX6 at MCS level
- `BXCanonical/OrderedSeedConsistency.lean` (151 lines): ordered seed consistency
- `BXCanonical/Frame.lean` (464 lines): BXPoint, bx_le, G/H propagation, eventuality resolution

**Target**: `Cslib/Logics/Temporal/Metalogic/Chronicle/` (RRelation.lean, Frame.lean, CanonicalChain.lean, OrderedSeedConsistency.lean)
**Estimated scope**: 800-1500 lines

---

### 47. Temporal labeled frame types and point insertion
- **Effort**: Large (15-20 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 46
- **Parent**: Task 31 (expanded)

**Description**: Define the labeled frame type (Burgess K-elements) and prove that counterexamples to conditions C5a/C6a/C5b/C6b can be eliminated by point insertion (Burgess Lemmas 2.6-2.7).

**Literature**: Burgess 1982 Definition 2.5, Lemmas 2.6-2.7; Xu 1988 Definition 2.5 (`BimodalLogic/literature/`)

**Bimodal prior art to adapt**:
- `BXCanonical/Chronicle/ChronicleTypes.lean` (386 lines): Chronicle data types (labeled frames)
- `BXCanonical/Chronicle/PointInsertion.lean` (3556 lines): Core point-insertion proofs for C5a/C6a defect elimination

**Target**: `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean`, `PointInsertion.lean`
**Estimated scope**: 1500-2800 lines

---

### 48. Temporal counterexample elimination and chronicle construction
- **Effort**: Large (15-20 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 47
- **Parent**: Task 31 (expanded)

**Description**: Build the omega-step construction that enumerates all C5/C6 counterexamples and iteratively inserts points (Burgess Theorem 2.8, construction part). Assemble the chronicle as the union of all finite stages.

**Literature**: Burgess 1982 Theorem 2.8 (construction); Xu 1988 Theorem 2.8 (`BimodalLogic/literature/`)

**Bimodal prior art to adapt**:
- `BXCanonical/Chronicle/CounterexampleElimination.lean` (3529 lines): Defect enumeration and elimination
- `BXCanonical/Chronicle/ChronicleConstruction.lean` (1531 lines): Chronicle assembly as directed limit

**Target**: `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean`, `ChronicleConstruction.lean`
**Estimated scope**: 1500-3000 lines

---

### 49. Temporal truth lemma and completeness assembly
- **Effort**: Medium (8-12 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 48
- **Parent**: Task 31 (expanded)

**Description**: Prove the truth lemma on the constructed chronicle frame and close the temporal completeness theorem, removing the final sorry.

**Literature**: Burgess 1982 Theorem 2.8 (truth lemma); Blackburn/de Rijke/Venema 2002 Theorem 7.15 (`BimodalLogic/literature/`)

**Bimodal prior art to adapt**:
- `BXCanonical/TruthLemma.lean` (223 lines): MCS truth properties (remove box case, keep atom/bot/imp/untl/snce)
- `BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` (1170 lines): Extract countermodel from chronicle
- `BXCanonical/Chronicle/ChronicleToCountermodel.lean` (229 lines): Final countermodel assembly
- `BXCanonical/CanonicalModel.lean` (771 lines): Z-chain MCS propagation (reference for G/H truth lemma)

**Target**: `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean`, `ChronicleToCountermodel.lean`, update `Completeness.lean`
**Estimated scope**: 500-1200 lines

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
- **Dependencies**: Task 31

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
- **Status**: [PARTIAL]
- **Task Type**: general
- **Dependencies**: Task 41

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

### 8. Port Completeness to Bimodal module [EXPANDED]
- **Status**: [EXPANDED] — split into tasks 34, 35, 36, 37

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



