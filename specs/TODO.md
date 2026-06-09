---
next_project_number: 46
---

# Tasks

## Task Order

*Updated 2026-06-09. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 35 | -- | Bimodal Porting |
| 2 | 36,37 | 35 | Bimodal Porting |
| 3 | 31 | 35,36,37 | Temporal Logic |
| 4 | 38,39 | 31 | Temporal Logic |
| 5 | 40,41 | 35,38,39 | Foundations, Temporal Logic |
| 6 | 12 | 31,35,36,37,38,39,40,41 | Project Management |

**Grouped by Topic** (indented = depends on parent):

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 
  └─ 12 [PARTIAL] — Coordinate the cslib PR submission proce (see Project Management section)

### Temporal Logic

31 [PARTIAL] — Build standalone temporal metalogic (~1,500 lines, new developmen
  └─ 12 [PARTIAL] — Coordinate the cslib PR submission proce (see Project Management section)
  └─ 38 [NOT STARTED] — Dense temporal completeness: prove that every formula valid on al
    └─ 12 [PARTIAL] — Coordinate the cslib PR submission proce (see Project Management section)
    └─ 40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic
      └─ 12 [PARTIAL] — Coordinate the cslib PR submission proce (see Project Management section)
    └─ 41 [NOT STARTED] — Abstract shared completeness infrastruct (see Foundations section)
  └─ 39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
    └─ 12 [PARTIAL] — Coordinate the cslib PR submission proce (see Project Management section)
    └─ 40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic (see above)
    └─ 41 [NOT STARTED] — Abstract shared completeness infrastruct (see Foundations section)

### Bimodal Porting

35 [IMPLEMENTING] — Port dense completeness infrastructure and completeness_dense the
  └─ 12 [PARTIAL] — Coordinate the cslib PR submission proce (see Project Management section)
  └─ 31 [PARTIAL] — Build standalone temporal metalogic (~1, (see Temporal Logic section)
  └─ 36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
    └─ 12 [PARTIAL] — Coordinate the cslib PR submission proce (see Project Management section)
    └─ 31 [PARTIAL] — Build standalone temporal metalogic (~1, (see Temporal Logic section)
  └─ 37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
    └─ 12 [PARTIAL] — Coordinate the cslib PR submission proce (see Project Management section)
    └─ 31 [PARTIAL] — Build standalone temporal metalogic (~1, (see Temporal Logic section)
  └─ 41 [NOT STARTED] — Abstract shared completeness infrastruct (see Foundations section)

### Project Management

12 [PARTIAL] — Coordinate the cslib PR submission process for the modular logic 

## Tasks

### 45. Improve ROADMAP.md diagram and structure
- **Effort**: Small (1-2 hours)
- **Status**: [COMPLETED]
- **Task Type**: markdown
- specs/045_improve_roadmap_diagram_and_structure/reports/01_roadmap-improvement.md: [Report]
- specs/045_improve_roadmap_diagram_and_structure/plans/01_roadmap-improvement.md: [Plan]
- specs/045_improve_roadmap_diagram_and_structure/summaries/01_roadmap-improvement-summary.md: [Summary]

**Description**: Improve ROADMAP.md: replace the Import Hierarchy section with an accurately labeled mermaid diagram, remove all task references throughout the file (readers should see TODO.md for tasks), remove the Phases section entirely, and add a file tree showing the current project structure focused on the aims of the roadmap.

---

### 44. Streamline ROADMAP.md
- **Effort**: Small (1-2 hours)
- **Status**: [COMPLETED]
- **Task Type**: markdown
- **Report**: [specs/044_streamline_roadmap/reports/01_streamline-roadmap.md]
- **Plan**: [specs/044_streamline_roadmap/plans/01_streamline-roadmap.md]
- **Summary**: [specs/044_streamline_roadmap/summaries/01_streamline-roadmap-summary.md]

**Description**: Streamline ROADMAP.md to focus on goal, completed work, remaining work, and broad approach. Remove historical commentary, detailed planning content, and design rationale that belongs in TODO.md or research artifacts. The roadmap should record what the goal is, what has been done, what remains, and the broad approach — leaving details to TODO.md with no historical commentary besides the list of what is completed.

---

### 31. Temporal metalogic
- **Effort**: Large (18 hours)
- **Status**: [IMPLEMENTING]
- **Plan**: [specs/031_temporal_metalogic/plans/01_temporal-metalogic-plan.md]
- **Task Type**: lean4
- **Dependencies**: Tasks 22, 23, 29, 35, 36, 37

**Description**: Build standalone temporal metalogic (~1,500 lines, new development not ported from BimodalLogic). Scope: (a) Temporal.DeductionTheorem via structural induction on ~6-constructor Temporal.DerivationTree (~300 lines), (b) Temporal.MCS importing generic SetConsistent/SetMaximalConsistent from Task 29 and adding temporal-specific witness conditions for Until/Since operators (~400 lines), (c) Temporal.Soundness over linear orders from Task 23 semantics (~350 lines), (d) Temporal.Completeness via canonical linear model construction (~450 lines). Target: `Cslib/Logics/Temporal/Metalogic/`.

---

### 40. Continuous temporal completeness
- **Effort**: TBD
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Dependencies**: Tasks 38, 39

**Description**: Completeness for temporal logic over Dedekind-complete (continuous) linear orders (e.g., the reals). Define a Continuous frame class extending Dense, add any required axioms, prove soundness and completeness.

**Blocker**: Research needed on whether continuous frames require additional axioms beyond density. The standard result (Burgess 1982) is that Until/Since temporal logic over the reals has the same theorems as over the rationals — density suffices — which would make this a transfer theorem rather than a new completeness proof. But this equivalence itself needs to be formalized.

---

### 39. Discrete temporal completeness
- **Effort**: Medium (8-12 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: Task 31

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
- **Dependencies**: Tasks 35, 38, 39

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
- **Dependencies**: Tasks 35, 36, 37, 31, 38, 39, 40, 41

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
- **Dependencies**: Task 35; upstream BimodalLogic continuous extension development
- **Parent**: Task 8 (expanded)

**Description**: Port continuous extension completeness once developed upstream. The continuous case (FrameClass for continuous/real-valued time) has not been started in BimodalLogic.

**Blocker**: Upstream BimodalLogic continuous extension development has not begun.

---

### 36. Port discrete completeness
- **Effort**: Medium (6-8 hours)
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Dependencies**: Task 35; upstream BimodalLogic discrete sorry elimination
- **Parent**: Task 8 (expanded)

**Description**: Port discrete completeness (`completeness_discrete` theorem) and `WeakCanonical/IntegerModel/` infrastructure (~6 files). The discrete branch constructs countermodels on `Int` via the Reynolds pipeline.

**Source**: `BimodalLogic/Theories/Bimodal/Metalogic/WeakCanonical/IntegerModel/` (~6 files), discrete branch of `BXCanonical/Completeness.lean`

**Blocker**: Upstream BimodalLogic has `sorryAx` tracing through `chronicle_gap_contradiction` → `succ_cofinal` → `limitDomSubtype_isSuccArchimedean` → `succ_embed_surjective` (36 sorries across IntegerModel/).

---

### 35. Port dense completeness infrastructure
- **Effort**: X-Large (28 hours)
- **Status**: [IMPLEMENTING]
- **Task Type**: lean4
- **Dependencies**: Task 34
- **Parent**: Task 8 (expanded)
- **Research**: [specs/035_port_dense_completeness_bimodal/reports/01_dense-completeness-research.md]
- **Plan**: [specs/035_port_dense_completeness_bimodal/plans/01_dense-completeness-plan.md]

**Description**: Port dense completeness infrastructure and `completeness_dense` theorem. Includes shared infrastructure (Algebraic/ ~11 files, Bundle/ ~14 files, BXCanonical/ non-Chronicle files) and dense-specific Chronicle/ pipeline (~7 files). The `completeness_dense` theorem constructs countermodels on `Rat` via the Burgess 1982 chronicle construction. Has leaf sorries in Chronicle modules (FMCS coherence, chronicle construction) — port with sorries as-is.

**Source**: `BimodalLogic/Theories/Bimodal/Metalogic/{Algebraic/,Bundle/,BXCanonical/}` (~40 files, ~15,000 lines)
**Target**: `Cslib/Logics/Bimodal/Metalogic/`

---


