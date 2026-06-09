---
next_project_number: 38
---

# Tasks

## Task Order

*Updated 2026-06-09. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 5,6,11,12,31 | -- | Temporal Logic, Bimodal Porting, Project Management |
| 2 | 7 | 5 | Bimodal Porting |
| 3 | 9,10,34 | 6,7 | Bimodal Porting |
| 4 | 35 | 34 | Bimodal Porting |
| 5 | 36,37 | 35 + upstream | Bimodal Porting (blocked on upstream) |

**Grouped by Topic** (indented = depends on parent):

### Temporal Logic

31 [PLANNED] — Build standalone temporal metalogic (~1,500 lines, new development)

### Bimodal Porting

5 [RESEARCHED] — Port Perpetuity theorems to Cslib/Logics/Bimodal/Theorems/Perpetuity/
  └─ 7 [RESEARCHED] — Port Deduction Infrastructure and MCS Theory (PR 6)
    └─ 34 [NOT STARTED] — Port base MCS completeness properties (~520 lines)
      └─ 35 [NOT STARTED] — Port dense completeness infrastructure (~15k lines)
        └─ 36 [BLOCKED] — Port discrete completeness (upstream sorry elimination)
        └─ 37 [BLOCKED] — Port continuous extension completeness (upstream development)
    └─ 9 [RESEARCHED] — Port Decidability and Tableau (PR 8)
    └─ 10 [RESEARCHED] — Port Separation Theorem (PR 9)
  └─ 10 [RESEARCHED] — Port Separation Theorem (PR 9) (see above)
6 [PLANNED] — Port Frame Conditions and Soundness (PR 5)
  └─ 34 [NOT STARTED] — Port base MCS completeness properties (see above)
11 [RESEARCHED] — Port Conservative Extension (PR 10)

### Project Management

12 [PARTIAL] — Coordinate the cslib PR submission process for the modular logic

## Tasks

### 31. Temporal metalogic
- **Effort**: Large (18 hours)
- **Status**: [PLANNED]
- **Plan**: [specs/031_temporal_metalogic/plans/01_temporal-metalogic-plan.md]
- **Task Type**: lean4
- **Dependencies**: Task 22, Task 23, Task 29

**Description**: Build standalone temporal metalogic (~1,500 lines, new development not ported from BimodalLogic). Scope: (a) Temporal.DeductionTheorem via structural induction on ~6-constructor Temporal.DerivationTree (~300 lines), (b) Temporal.MCS importing generic SetConsistent/SetMaximalConsistent from Task 29 and adding temporal-specific witness conditions for Until/Since operators (~400 lines), (c) Temporal.Soundness over linear orders from Task 23 semantics (~350 lines), (d) Temporal.Completeness via canonical linear model construction (~450 lines). Target: `Cslib/Logics/Temporal/Metalogic/`.

---

### 12. Coordinate cslib PR submission for Bimodal Logic integration
- **Effort**: Ongoing (tracked separately)
- **Status**: [PARTIAL]
- **Task Type**: general

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

### 11. Port Conservative Extension to Bimodal module
- **Effort**: Medium (6-10 hours)
- **Status**: [COMPLETED]
- **Summary**: [specs/011_port_conservative_extension_bimodal/summaries/01_conservative-extension-summary.md]
- **Task Type**: lean4
- **Dependencies**: Task 4 (ProofSystem)

**Description**: Port conservative extension results from BimodalLogic to `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/`. This result shows that the BX extension preserves all theorems of the base logic. The ported code operates on `Bimodal.Formula` (all 6 constructors) and must adapt imports to use cslib's formula type and typeclass infrastructure in `Cslib/Logics/Bimodal/Syntax/Basic.lean`.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/ConservativeExtension/):
- ExtFormula.lean (~400 lines): extended formula type with additional connectives
- ExtDerivation.lean (~400 lines): derivation rules for extended language
- Substitution.lean (~350 lines): substitution theorem for conservative extension
- Lifting.lean (~350 lines): lifting theorems between base and extended language

**Target path**: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/`

**Adaptation notes**: ExtFormula extends the bimodal formula type. Since `Bimodal.Formula` already exists in `Cslib/Logics/Bimodal/Syntax/Basic.lean`, ExtFormula must build on it rather than on BimodalLogic's original Formula type. Imports change from `Bimodal.Syntax.Formula` to `Cslib.Logics.Bimodal.Syntax.Formula`.

**Estimated scope**: ~1,500 lines across 4 files

**Porting Checklist**:
- [ ] Rename namespace: Bimodal.Metalogic -> Cslib.Logic.Bimodal.Metalogic
- [ ] Adapt formula references to use `Cslib.Logic.Bimodal.Formula`
- [ ] Add Apache 2.0 copyright header
- [ ] Run lake shake to identify unused imports
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences

---

### 10. Port Separation Theorem to Bimodal module
- **Effort**: Large (10-14 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 5, 7 (ProofSystem, Perpetuity Theorems, MCS/Deduction)

**Description**: Port the separation theorem from BimodalLogic to `Cslib/Logics/Bimodal/Metalogic/Separation/`. The separation theorem proves that TM is conservative over its temporal and modal fragments separately — it is inherently a bimodal result that references the embedding functions (`Modal.Formula.toBimodal`, `Temporal.Formula.toBimodal`) from `Cslib/Logics/Bimodal/Embedding/`. This is one of the key results that connects the separate formula types in the modular architecture.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/WeakCanonical/Separation/):
- Defs.lean, FormulaOps.lean, NormalForm.lean, KampTranslation.lean
- Eliminations.lean, DualEliminations.lean, Distributivity.lean, Duality.lean
- NegationEquiv.lean, TemporalClosure.lean, SemanticBridge.lean, SeparationThm.lean
- IntHelpers.lean, DedekindZ/ (Cases.lean, QLemma.lean)
- Hierarchy/ (HierarchyDefs.lean, HierarchyInduction.lean, HierarchyCaseSep.lean, HierarchyCompletion.lean)

**Target path**: `Cslib/Logics/Bimodal/Metalogic/Separation/`

**Adaptation notes**: The separation theorem explicitly characterizes which bimodal formulas are equivalent to pure modal or pure temporal formulas. The Kamp translation and formula operations must reference `Bimodal.Formula` from `Cslib/Logics/Bimodal/Syntax/Basic.lean`. The result should connect to the embedding functions to state: if `φ : Bimodal.Formula` is in the modal fragment, then there exists `ψ : Modal.Formula` with `ψ.toBimodal` equivalent to `φ`.

**Estimated scope**: ~3,500 lines across 20+ files

---

### 9. Port Decidability and Tableau to Bimodal module
- **Effort**: X-Large (20-30 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 7 (ProofSystem, MCS/Deduction)

**Description**: Port the tableau-based decision procedure from BimodalLogic to `Cslib/Logics/Bimodal/Metalogic/Decidability/`. This is the largest port (~10k lines) covering the full decision procedure for TM logic. The tableau operates on `Bimodal.Formula` (all 6 constructors) with rules for both modal and temporal operators. It is inherently bimodal and cannot be factored into separate modal/temporal components.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/Decidability/):
- SignedFormula.lean (~400 lines): signed formula type for tableau
- Tableau.lean (~1,800 lines): main tableau expansion rules (28 rules), termination proof
- Closure.lean (~600 lines): closure conditions, saturation definition
- Saturation.lean (~800 lines): saturation lemmas, model extraction framework
- ProofExtraction.lean (~600 lines): extract DerivationTree from closed tableau branch
- Correctness.lean (~400 lines): tableau soundness and completeness
- DecisionProcedure.lean (~500 lines): decide function, decidability instance
- CountermodelExtraction.lean (~600 lines): extract countermodel from open saturated tableau
- TraceCertificate.lean, TraceExport.lean: trace infrastructure
- FMP/*.lean (~6 files, ~3,000 lines): finite model property

**Target path**: `Cslib/Logics/Bimodal/Metalogic/Decidability/`

**Adaptation notes**: SignedFormula and Tableau must reference `Bimodal.Formula` from `Cslib/Logics/Bimodal/Syntax/Basic.lean` instead of BimodalLogic's original Formula. The decision procedure should provide an `InferenceSystem` instance for `Bimodal.HilbertTM` once DerivationTree is available (from task 4). SubformulaClosure (used by tableau) ports alongside this task.

**Estimated scope**: ~10,000 lines across 18+ files

**Note**: Consider splitting into (9a) Core tableau/decision procedure (~5k lines) and (9b) FMP (~4k lines) if review burden is too high.

---

### 8. Port Completeness to Bimodal module [EXPANDED]
- **Status**: [EXPANDED] — split into tasks 34, 35, 36, 37
- **Task Type**: lean4

Expanded into:
- **34**: Port base MCS completeness properties (~520 lines, sorry-free)
- **35**: Port dense completeness infrastructure + theorem (~15,000 lines, has leaf sorries)
- **36**: Port discrete completeness (blocked on upstream sorry elimination)
- **37**: Port continuous extension completeness (blocked on upstream development)

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
- **Effort**: Large (10-14 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 34
- **Parent**: Task 8 (expanded)

**Description**: Port dense completeness infrastructure and `completeness_dense` theorem. Includes shared infrastructure (Algebraic/ ~11 files, Bundle/ ~14 files, BXCanonical/ non-Chronicle files) and dense-specific Chronicle/ pipeline (~7 files). The `completeness_dense` theorem constructs countermodels on `Rat` via the Burgess 1982 chronicle construction. Has leaf sorries in Chronicle modules (FMCS coherence, chronicle construction) — port with sorries as-is.

**Source**: `BimodalLogic/Theories/Bimodal/Metalogic/{Algebraic/,Bundle/,BXCanonical/}` (~40 files, ~15,000 lines)
**Target**: `Cslib/Logics/Bimodal/Metalogic/`

---

### 34. Port base MCS completeness properties
- **Effort**: Small (3-4 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 6, 7 (FrameConditions+Soundness, MCS/Deduction)
- **Parent**: Task 8 (expanded)

**Description**: Port base MCS completeness properties from `Completeness.lean` (~520 lines) to `Cslib/Logics/Bimodal/Metalogic/Completeness.lean`. All proofs are sorry-free.

**Includes**: `disjunction_intro/elim/iff`, `conjunction_intro/elim/iff`, `box_closure` (Modal T), `box_box` (Modal 4), diamond-box duality (`neg_box_implies_diamond_neg`, `diamond_neg_implies_neg_box`, `diamond_box_duality`).

**Source**: `BimodalLogic/Theories/Bimodal/Metalogic/Completeness.lean` (~520 lines)
**Target**: `Cslib/Logics/Bimodal/Metalogic/Completeness.lean`

---

### 7. Port Deduction Infrastructure and MCS Theory to Bimodal module
- **Effort**: Large (10-14 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 5, 29 (ProofSystem, Perpetuity Theorems, Generic MCS Foundations)

**Description**: Port deduction theorem and maximal consistent set theory from BimodalLogic to `Cslib/Logics/Bimodal/Metalogic/Core/`. This establishes the core metalogical infrastructure for completeness.

**Note on DeductionTheorem**: The DeductionTheorem stays in this task (bimodal-specific). Per team research finding #7, it requires structural induction on the bimodal `DerivationTree` and cannot be ported generically to Foundations. Scope is unchanged at ~2,500 lines.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/Core/):
- Core.lean: module aggregator
- DeductionTheorem.lean (~500 lines): deduction theorem for TM proof system (structural induction on bimodal DerivationTree)
- MaximalConsistent.lean (~600 lines): MCS definition and basic properties
- MCSProperties.lean (~700 lines): Lindenbaum lemma, MCS enumeration, closure properties
- RestrictedMCS/Basic.lean (~400 lines): restricted MCS for frame-specific completeness
- RestrictedMCS/Deferral.lean: MCS deferral properties

**Target path**: `Cslib/Logics/Bimodal/Metalogic/Core/`

**Estimated scope**: ~2,500 lines across 6 files

---

### 6. Port Frame Conditions and Soundness to Bimodal module
- **Effort**: Large (12 hours)
- **Status**: [PLANNED]
- **Plan**: [specs/006_port_frame_conditions_soundness_bimodal/plans/01_frame-soundness-plan.md]
- **Task Type**: lean4
- **Dependencies**: Tasks 3, 4 (Semantics, ProofSystem)

**Description**: Port bimodal frame conditions and soundness to `Cslib/Logics/Bimodal/FrameConditions/` and `Cslib/Logics/Bimodal/Metalogic/Soundness/`. The soundness proof is inherently bimodal — the interaction axiom MF requires both task frame semantics and modal quantification over world histories. The `FrameClass` type (Base/Dense/Discrete) and `minFrameClass` gating pattern should be preserved.

**Modular factoring note**: Standalone temporal frame condition typeclasses (LinearTemporalFrame, DenseTemporalFrame, DiscreteTemporalFrame as abstract typeclasses) moved to Task 22. This task ports the bimodal-specific frame conditions and soundness proofs (~2,370 lines).

**Source files**:
- FrameConditions/ (4 files, ~790 lines): FrameClass.lean, Validity.lean, Soundness.lean, Compatibility.lean
- Metalogic/Soundness.lean (~400 lines): main soundness theorem
- Metalogic/SoundnessLemmas/ (3 files): Core.lean, DenseValidity.lean, FrameClassVariants.lean
- Metalogic/DenseSoundness.lean (~300 lines)
- Metalogic/DiscreteSoundness.lean (~300 lines)

**Target paths**:
- `Cslib/Logics/Bimodal/FrameConditions/`
- `Cslib/Logics/Bimodal/Metalogic/Soundness/`

**Estimated scope**: ~2,370 lines across 10 files

---

### 5. Port Perpetuity theorems to Bimodal module
- **Effort**: Small (3-5 hours)
- **Status**: [PLANNED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 21, 22 (ProofSystem, Modal Theorems, Temporal Infrastructure)
- **External Dependencies**: BimodalLogic task 294 (sorry elimination in Perpetuity/)
- **Plan**: [specs/005_port_derived_theorems_bimodal/plans/01_perpetuity-port-plan.md]

**Description**: Port Perpetuity theorems to `Cslib/Logics/Bimodal/Theorems/Perpetuity/`. Scope reduced to ~800 lines (Perpetuity/ only — inherently bimodal, uses both modal box and temporal until/since operators together).

**Modular factoring note**: Components moved to standalone modules:
- Combinators (~300 lines) -> Task 20 (Foundations/Logic/Theorems/)
- Propositional/{Core,Connectives,Reasoning} (~1,100 lines) -> Task 20
- ContextualProofs (~500 lines) -> Task 20
- GeneralizedNecessitation + ModalS4/S5 (~1,200 lines) -> Task 21 (Modal/Theorems/)
- TemporalDerived (~790 lines) -> Task 22 (Temporal/Theorems/)

**Source files** (from BimodalLogic Theories/Bimodal/Theorems/Perpetuity/):
- Bridge.lean, Helpers.lean, Principles.lean (~800 lines total): perpetuity fixed-point theorems using both modal and temporal operators

**Target path**: `Cslib/Logics/Bimodal/Theorems/Perpetuity/`

**Estimated scope**: ~800 lines across 3 files

---


