---
next_project_number: 34
---

# Tasks

## Task Order

*Updated 2026-06-09. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 12,29,32 | -- | Foundations, Temporal Logic, Project Management |
| 2 | 4,23,30 | 29,32 | Modal Logic, Temporal Logic, Bimodal Porting |
| 3 | 5,6,11,31 | 4,23,29,32 | Temporal Logic, Bimodal Porting |
| 4 | 7 | 4,5,29 | Bimodal Porting |
| 5 | 8,9,10 | 4,5,6,7 | Bimodal Porting |

**Grouped by Topic** (indented = depends on parent):

### Foundations

29 [NOT STARTED] — Create generic MCS (maximal consistent set) foundations parameter
  └─ 7 [NOT STARTED] — Port Deduction Infrastructure and MCS Th (see Bimodal Porting section)
  └─ 30 [NOT STARTED] — Build standalone modal metalogic (~1,500 (see Modal Logic section)
  └─ 31 [NOT STARTED] — Build standalone temporal metalogic (~1, (see Temporal Logic section)

### Modal Logic

30 [NOT STARTED] — Build standalone modal metalogic (~1,500 lines, new development n

### Temporal Logic

32 [COMPLETED] — Fix untl/snce argument order across cslib to match standard liter
  └─ 4 [NOT STARTED] — Port the Bimodal Hilbert-style proof sys (see Bimodal Porting section)
  └─ 5 [NOT STARTED] — Port Perpetuity theorems to Cslib/Logics (see Bimodal Porting section)
  └─ 6 [NOT STARTED] — Port Frame Conditions and Soundness (PR  (see Bimodal Porting section)
  └─ 23 [NOT STARTED] — Define standalone temporal semantics on linear orders (~400-600 l
    └─ 31 [NOT STARTED] — Build standalone temporal metalogic (~1,500 lines, new developmen
  └─ 31 [NOT STARTED] — Build standalone temporal metalogic (~1,500 lines, new developmen (see above)

### Bimodal Porting

4 [NOT STARTED] — Port the Bimodal Hilbert-style proof system to Cslib/Logics/Bimod
  └─ 5 [NOT STARTED] — Port Perpetuity theorems to Cslib/Logics/Bimodal/Theorems/Perpetu
    └─ 7 [NOT STARTED] — Port Deduction Infrastructure and MCS Theory (PR 6): DeductionThe
      └─ 8 [NOT STARTED] — Port Strong Completeness (PR 7): Completeness.lean to Cslib/Logic
      └─ 9 [NOT STARTED] — Port Decidability and Tableau (PR 8): SignedFormula, Tableau, Clo
      └─ 10 [NOT STARTED] — Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 fi
    └─ 10 [NOT STARTED] — Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 fi (see above)
  └─ 6 [NOT STARTED] — Port Frame Conditions and Soundness (PR 5): FrameClass, Validity,
    └─ 8 [NOT STARTED] — Port Strong Completeness (PR 7): Completeness.lean to Cslib/Logic (see above)
  └─ 7 [NOT STARTED] — Port Deduction Infrastructure and MCS Theory (PR 6): DeductionThe (see above)
  └─ 9 [NOT STARTED] — Port Decidability and Tableau (PR 8): SignedFormula, Tableau, Clo (see above)
  └─ 10 [NOT STARTED] — Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 fi (see above)
  └─ 11 [NOT STARTED] — Port Conservative Extension (PR 10): ExtFormula, ExtDerivation, S

### Project Management

12 [PARTIAL] — Coordinate the cslib PR submission process for the modular logic 

## Tasks

### 33. Audit noncomputable instances in Temporal module
- **Effort**: Small (<1 hour)
- **Status**: [PLANNED]
- **Task Type**: lean4
- **Dependencies**: None
- specs/033_audit_noncomputable_temporal_instances/reports/01_audit-noncomputable-research.md: [Research report]
- specs/033_audit_noncomputable_temporal_instances/plans/01_audit-noncomputable-plan.md: [Implementation plan]

**Description**: Audit 35 noncomputable instances in Temporal/ProofSystem/Instances.lean. Verify all are necessary (Nonempty-based DerivableIn likely requires noncomputable). Document rationale or remove unnecessary noncomputable markers.

---

### 32. Fix untl/snce argument order to match standard literature convention
- **Effort**: Medium (2-4 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: 22, 3
- **Research**: [specs/032_fix_untl_argument_order_convention/reports/01_untl-argument-order.md]
- **Plan**: [specs/032_fix_untl_argument_order_convention/plans/01_untl-argument-fix.md]
- **Summary**: [specs/032_fix_untl_argument_order_convention/summaries/01_untl-argument-fix-summary.md]

**Description**: Fix untl/snce argument order across cslib to match standard literature convention (Burgess 1982). Currently cslib uses untl(guard, event) but the literature and BimodalLogic source use untl(event, guard). This causes 6+ temporal axioms to be provably unsound under cslib's semantics, with concrete countermodels. Change all Formula definitions (Temporal and Bimodal), Truth semantics, axiom abbreviations, and derived theorems to use untl(event, guard). Affects ~10 files across Temporal and Bimodal modules. Must be completed before any soundness proofs (Task 6) or further temporal work.

### 31. Temporal metalogic
- **Effort**: Large (20-30 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Task 22 (Temporal Infrastructure), Task 23 (Temporal Semantics), Task 29 (Generic MCS Foundations)

**Description**: Build standalone temporal metalogic (~1,500 lines, new development not ported from BimodalLogic). Scope: (a) Temporal.DeductionTheorem via structural induction on ~6-constructor Temporal.DerivationTree (~300 lines), (b) Temporal.MCS importing generic SetConsistent/SetMaximalConsistent from Task 29 and adding temporal-specific witness conditions for Until/Since operators (~400 lines), (c) Temporal.Soundness over linear orders from Task 23 semantics (~350 lines), (d) Temporal.Completeness via canonical linear model construction (~450 lines). Target: `Cslib/Logics/Temporal/Metalogic/`.

---

### 30. Modal metalogic
- **Effort**: Large (20-30 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Task 21 (Modal Proof System), Task 29 (Generic MCS Foundations)
- specs/030_modal_metalogic/reports/01_modal-metalogic-research.md: [Research report]

**Description**: Build standalone modal metalogic (~1,500 lines, new development not ported from BimodalLogic). Scope: (a) Modal.DeductionTheorem via structural induction on ~5-constructor Modal.DerivationTree (~300 lines), (b) Modal.MCS importing generic SetConsistent/SetMaximalConsistent from Task 29 and adding modal-specific witness conditions like box_closure (~400 lines), (c) Modal.Soundness over Kripke frames/models from Modal/Basic.lean (~350 lines), (d) Modal.Completeness via canonical Kripke model construction for S5 (~450 lines). Target: `Cslib/Logics/Modal/Metalogic/`.

---

### 29. Generic MCS foundations
- **Effort**: Small (2-4 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: None
- specs/029_generic_mcs_foundations/reports/01_mcs-foundations-research.md: [Research report]
- specs/029_generic_mcs_foundations/plans/01_mcs-foundations-plan.md: [Implementation plan]
- specs/029_generic_mcs_foundations/summaries/01_mcs-foundations-summary.md: [Execution summary]

**Description**: Create generic MCS (maximal consistent set) foundations parameterized over an abstract derivation relation (~200-300 lines). Scope: SetConsistent definition, SetMaximalConsistent definition, Lindenbaum lemma skeleton (Zorn-based), consistent_chain_union, closed_under_derivation, implication_property. These are the ~60% of MCS theory that do not depend on per-logic deduction theorems. Target: `Cslib/Foundations/Logic/Metalogic/Consistency.lean`. Modal and Temporal metalogic tasks (30, 31) import from here.

---

### 28. Structure metalogic across Propositional, Modal, Temporal, and Bimodal systems
- **Effort**: Large (1-2 days)
- **Status**: [COMPLETED]
- **Task Type**: formal
- **Research**: [specs/028_structure_metalogic_across_systems/reports/01_team-research.md]
- **Plan**: [028_structure_metalogic_across_systems/plans/01_metalogic-structure-plan.md]
- **Summary**: [028_structure_metalogic_across_systems/summaries/01_metalogic-structure-summary.md]

**Description**: Much of /home/benjamin/Projects/BimodalLogic/ is devoted to metalogic for the bimodal system. When porting over to CSLib, clearly and cleanly include appropriate metalogic for Propositional/, Modal/, Temporal/, and Bimodal/. Although the semantics for each of these logics differs, look for opportunities for importing between them. Revise existing tasks or add additional tasks as appropriate to structure the metalogic for each system correctly.

### 27. Systematically review all documentation and standards, ensuring tasks and ROADMAP.md are in alignment
- **Effort**: Medium (2-4 hours)
- **Status**: [COMPLETED]
- **Task Type**: general
- **Research**: [specs/027_review_docs_roadmap_alignment/reports/01_docs-roadmap-alignment.md]
- **Plan**: [specs/027_review_docs_roadmap_alignment/plans/01_alignment-plan.md]
- **Summary**: [specs/027_review_docs_roadmap_alignment/summaries/01_alignment-summary.md]

**Description**: Systematically review all documentation and standards in this repo, making sure the tasks and ROADMAP.md are all in alignment, making any changes that are needed while making no unneeded changes.

---

### 23. Temporal semantics on linear orders
- **Effort**: Medium (4-6 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Task 22 (Temporal Infrastructure)

**Description**: Define standalone temporal semantics on linear orders (~400-600 lines, new infrastructure not ported from BimodalLogic). Define `Temporal.Model` on `LinearOrder`, `Temporal.Satisfies` for `{atom, bot, imp, untl, snce}`, basic validity, and frame conditions on linear orders. Enables standalone temporal soundness proofs. Target: `Cslib/Logics/Temporal/Semantics/`.

---

### 22. Temporal infrastructure and theorems
- **Effort**: Medium (6-10 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Task 20 (Propositional Hilbert Theorems)

**Description**: Build temporal proof system infrastructure and port temporal theorems (~1,500 lines). Scope: ~20 temporal axiom abbrevs, ~20 HasAxiom* typeclasses, restructure TemporalBXHilbert, make TemporalNecessitation non-empty, BimodalTMHilbert compatibility instance (diamond-avoidance pattern), Temporal.DerivationTree, TemporalDerived theorems (~790 lines), frame condition typeclasses (~130 lines). Target: Axioms.lean/ProofSystem.lean additions + `Cslib/Logics/Temporal/ProofSystem/` + `Cslib/Logics/Temporal/Theorems/`.

---

### 21. Modal proof system and theorems
- **Effort**: Medium (6-10 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Tasks 16 (DecidableEq), 20 (Propositional Theorems)

**Description**: Port modal proof system and theorems (~1,600 lines from BimodalLogic). Scope: (a) Modal.DerivationTree with ModalHilbert/ModalS5Hilbert instances (~400), (b) S4/S5 derived theorems + GeneralizedNecessitation as `[ModalS5Hilbert S]` lemmas (~1,200). Target: `Cslib/Logics/Modal/ProofSystem/` + `Cslib/Logics/Modal/Theorems/`.

---

### 20. Propositional Hilbert theorems
- **Effort**: Medium (6-10 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Research**: [020_propositional_hilbert_theorems/reports/01_hilbert-theorems-research.md]
- **Plan**: [020_propositional_hilbert_theorems/plans/01_hilbert-theorems-plan.md]
- **Summary**: [020_propositional_hilbert_theorems/summaries/01_hilbert-theorems-summary.md]

**Description**: Port propositional Hilbert-style theorems to `Cslib/Foundations/Logic/Theorems/` as generic `[PropositionalHilbert S]` lemmas (~2,400 lines from BimodalLogic). Scope: Combinators (I/B/C/S, ~300), Propositional/{Core,Connectives,Reasoning} (~1,100), ContextualProofs (~500), BigConj generic (~500). Note: DeductionTheorem stays per-logic (requires structural induction on DerivationTree, per team research finding).

---

### 16. Add DecidableEq to Modal.Proposition, resolve LukasiewiczDerived
- **Effort**: Small (<1 hour)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Research**: [specs/016_formula_type_consistency/reports/01_formula-type-research.md]
- **Plan**: [specs/016_formula_type_consistency/plans/01_formula-type-plan.md]
- **Summary**: [specs/016_formula_type_consistency/summaries/01_formula-type-summary.md]

**Description**: Formula type consistency fixes from code review:
1. Add `deriving DecidableEq, BEq` to `Modal.Proposition` in `Cslib/Logics/Modal/Basic.lean` for consistency with `Bimodal.Formula` and `Temporal.Formula`
2. Either instantiate `LukasiewiczDerived` for existing formula types or add docstring noting it's for future use in `Cslib/Foundations/Logic/Connectives.lean`

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

### 11. Port Conservative Extension to Bimodal module
- **Effort**: Medium (6-10 hours)
- **Status**: [RESEARCHED]
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

### 8. Port Completeness to Bimodal module
- **Effort**: Large (10-16 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Tasks 6, 7 (FrameConditions+Soundness, MCS/Deduction)

**Description**: Port completeness results from BimodalLogic to `Cslib/Logics/Bimodal/Metalogic/`. This includes the main completeness theorem (every valid formula is derivable in TM), the BXCanonical construction (chronicle-based canonical model), and the algebraic completeness path. The completeness proof is inherently bimodal — the MCS construction closes under all 42 axiom constructors, and the Burgess-Xu chronicle construction requires the interaction axiom MF.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/):
- Completeness.lean (~520 lines): main completeness theorem
- BXCanonical/ (~15 files): canonical chain, canonical model, chronicle construction, filtration, quasimodel, truth lemma, completeness proof
- Algebraic/ (~11 files): D-parametric algebraic completeness, Lindenbaum quotient, interior operators, parametric truth lemma
- Bundle/ (~14 files): BFMCS/FMCS construction, canonical frame, modal saturation, temporal coherence

**Target path**: `Cslib/Logics/Bimodal/Metalogic/`

**Adaptation notes**: All files reference the full 6-constructor formula type. Port to use `Bimodal.Formula` from `Cslib/Logics/Bimodal/Syntax/Basic.lean`. The canonical model construction uses `DerivationTree` from task 4 and MCS theory from task 7. The completeness theorem currently has sorry (chronicle construction); port the sorry as-is and track separately.

**Estimated scope**: ~520 lines for the main theorem, plus ~40 files of supporting infrastructure (~15,000 lines total including BXCanonical, Algebraic, Bundle)

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
- **Effort**: Large (10-14 hours)
- **Status**: [RESEARCHED]
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
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 21, 22 (ProofSystem, Modal Theorems, Temporal Infrastructure)
- **External Dependencies**: BimodalLogic task 294 (sorry elimination in Perpetuity/)

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

### 4. Port Proof System to Bimodal module
- **Effort**: Large (8-12 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Tasks 2, 20, 22 (Syntax, Propositional Theorems, Temporal Infrastructure)

**Description**: Port the Bimodal Hilbert-style proof system to `Cslib/Logics/Bimodal/ProofSystem/`. Scope: concrete 42-axiom Axiom inductive (propositional + S5 modal + BX temporal + interaction MF/TF), DerivationTree (7 rules), Derivable, Substitution, and BimodalTMHilbert instance registration.

**Note**: Temporal axiom abbrevs and HasAxiom* typeclasses are completed in Task 22 (not this task). Task 20 provides propositional theorems. This task focuses on the concrete bimodal 42-constructor Axiom inductive and the full DerivationTree.

**Source files** (from BimodalLogic Theories/Bimodal/ProofSystem/):
- Axioms.lean (~400 lines): 42 axiom schemata with `minFrameClass` gating
- Derivation.lean (~600 lines): `DerivationTree` inductive (7 rules), `FrameClass` parameterization
- Derivable.lean (~300 lines): `Derivable` predicate, basic properties
- Substitution.lean (~500 lines): uniform substitution theorem
- LinearityDerivedFacts.lean (~200 lines): linearity-specific derived facts

**Target path**: `Cslib/Logics/Bimodal/ProofSystem/`

**Estimated scope**: ~2,000 lines across 5 files

---

### 3. Port Task Frame Semantics to Bimodal module
- **Effort**: Large (8-12 hours)
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Dependencies**: Task 2 (Bimodal Syntax)

**Description**: Port task frame semantics from BimodalLogic to `Cslib/Logics/Bimodal/Semantics/`. Task frame semantics is inherently bimodal: `□φ` quantifies over world histories in a shift-closed set (implicit S5), while temporal operators (G, H) quantify over time points within a history. This is fundamentally different from cslib's existing Kripke semantics for modal logic (`Model World Atom` with accessibility relation) — the two semantic frameworks coexist at different logic levels.

**Source files** (from BimodalLogic Theories/Bimodal/Semantics/):
- TaskFrame.lean (~500 lines): `TaskFrame T` with task_rel, nullity, compositionality
- WorldHistory.lean (~400 lines): `WorldHistory F` with convex time domains, shift-closure
- TaskModel.lean (~400 lines): model = frame + valuation
- Truth.lean (~600 lines): recursive `truth_at M τ t ht φ` for all 6 constructors
- Validity.lean (~300 lines): validity polymorphic over temporal type `T`

**Target path**: `Cslib/Logics/Bimodal/Semantics/`

**Adaptation notes**: `Truth.lean` evaluates `Bimodal.Formula` (all 6 constructors). Port to use `Cslib.Logics.Bimodal.Syntax.Formula` from `Cslib/Logics/Bimodal/Syntax/Basic.lean`. The `truth_at` function must match the constructor names in the new formula type. Consider providing an `InferenceSystem` instance for semantic derivation (as cslib's Modal module does with `HasInferenceSystem (Judgement World Atom)`).

**Estimated scope**: ~2,200 lines across 5 files

---

### 2. Port Bimodal Syntax infrastructure (Context, BigConj, Subformulas)
- **Effort**: Medium (6-10 hours)
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Dependencies**: BimodalLogic:291 (toolchain upgrade)
- **Research**: [specs/002_port_bimodal_syntax_infrastructure/reports/01_syntax-port-research.md]
- **Plan**: [specs/002_port_bimodal_syntax_infrastructure/plans/01_syntax-port-plan.md]
- **Summary**: [specs/002_port_bimodal_syntax_infrastructure/summaries/01_syntax-port-summary.md]

**Description**: Port the syntax infrastructure from BimodalLogic to `Cslib/Logics/Bimodal/Syntax/`. `Bimodal.Formula` with `{atom, bot, imp, box, untl, snce}` already exists in `Cslib/Logics/Bimodal/Syntax/Basic.lean`. This task ports the remaining syntax components that operate on the full bimodal formula type: Context (proof assumptions), BigConj (finite conjunction), Subformulas, and SubformulaClosure — all using all 6 formula constructors.

**Note on modular factoring**: Generic `BigConj` and `Context` at the typeclass level (`[PropositionalHilbert S]`) live in Task 20 (Foundations). This task ports the bimodal-specific versions that use all 6 formula constructors and cannot be generalized.

**Note on Formula.lean**: BimodalLogic's `Syntax/Formula.lean` (~800 lines) contains not just the inductive type but also `complexity`, `atomSet`, `swap_temporal`, `Countable`/`Denumerable`/`Infinite` instances, and many structural lemmas. The inductive type already exists in `Cslib/Logics/Bimodal/Syntax/Basic.lean`, but these additional properties need porting.

**Source files** (from BimodalLogic Theories/Bimodal/Syntax/):
- Formula.lean (~800 lines): complexity, atomSet, swap_temporal, Countable instances (the inductive type portion already present in `Cslib/Logics/Bimodal/Syntax/Basic.lean` — port remaining ~500 lines of properties)
- Atom.lean (~300 lines): PropAtom type, decidable equality — may not be needed if cslib uses a generic `Atom` parameter
- Context.lean (~400 lines): `Context := List Formula`, context operations, membership, subset
- BigConj.lean (~500 lines): finite conjunction folding, BigConj properties
- Subformulas.lean (~500 lines): subformula relation, subformula lemmas
- SubformulaClosure/ (3 files, ~800 lines): Closure.lean, NestingDepth.lean, TemporalFormulas.lean

**Target path**: `Cslib/Logics/Bimodal/Syntax/`

**Adaptation notes**: All files reference `Formula` with 6 constructors — matches `Bimodal.Formula` already present in `Cslib/Logics/Bimodal/Syntax/Basic.lean`. Adapt imports from `Bimodal.Syntax.Formula` to `Cslib.Logics.Bimodal.Syntax.Formula`. The `Atom` type in BimodalLogic is a concrete `PropAtom`; cslib's formula types use a generic `Atom` parameter — this is the main adaptation needed.

**Estimated scope**: ~2,500 lines across 7 files (after excluding the already-ported inductive type)

---

