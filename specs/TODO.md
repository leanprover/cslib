---
next_project_number: 25
---

# Tasks

## Task Order

*Updated 2026-06-09. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 2,12,15,16,17,18,20,24 | -- | Foundations, Modal Logic, Bimodal Porting, ... |
| 2 | 3,21,22 | 2,16,20 | Modal Logic, Temporal Logic, Bimodal Porting |
| 3 | 4,23 | 2,20,22 | Temporal Logic, Bimodal Porting |
| 4 | 5,6,11 | 3,4,21,22 | Bimodal Porting |
| 5 | 7 | 4,5 | Bimodal Porting |
| 6 | 8,9,10 | 4,5,6,7 | Bimodal Porting |

**Grouped by Topic** (indented = depends on parent):

### Foundations

20 [NOT STARTED] — Port propositional Hilbert-style theorems to Cslib/Foundations/Lo
  └─ 4 [NOT STARTED] — Port the Bimodal Hilbert-style proof system to Cslib/Logics/Bimod
    └─ 5 [NOT STARTED] — Port Perpetuity theorems to Cslib/Logics/Bimodal/Theorems/Perpetu
      └─ 7 [NOT STARTED] — Port Deduction Infrastructure and MCS Theory (PR 6): DeductionThe
        └─ 8 [NOT STARTED] — Port Strong Completeness (PR 7): Completeness.lean to Cslib/Logic
        └─ 9 [NOT STARTED] — Port Decidability and Tableau (PR 8): SignedFormula, Tableau, Clo
        └─ 10 [NOT STARTED] — Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 fi
      └─ 10 [NOT STARTED] — (Bimodal Porting: Port Separation Theorem (PR 9): WeakCano) (see above)
    └─ 6 [NOT STARTED] — Port Frame Conditions and Soundness (PR 5): FrameClass, Validity,
      └─ 8 [NOT STARTED] — (Bimodal Porting: Port Strong Completeness (PR 7): Complet) (see above)
    └─ 7 [NOT STARTED] — (Bimodal Porting: Port Deduction Infrastructure and MCS Th) (see above)
    └─ 9 [NOT STARTED] — (Bimodal Porting: Port Decidability and Tableau (PR 8): Si) (see above)
    └─ 10 [NOT STARTED] — (Bimodal Porting: Port Separation Theorem (PR 9): WeakCano) (see above)
    └─ 11 [NOT STARTED] — Port Conservative Extension (PR 10): ExtFormula, ExtDerivation, S
  └─ 21 [NOT STARTED] — Port modal proof system and theorems to Cslib/Logics/Modal/ProofS
    └─ 5 [NOT STARTED] — (Bimodal Porting: Port Perpetuity theorems to Cslib/Logics) (see above)
  └─ 22 [NOT STARTED] — Build temporal proof system infrastructure and port temporal theo
    └─ 4 [NOT STARTED] — (Bimodal Porting: Port the Bimodal Hilbert-style proof sys) (see above)
    └─ 5 [NOT STARTED] — (Bimodal Porting: Port Perpetuity theorems to Cslib/Logics) (see above)
    └─ 23 [NOT STARTED] — Define standalone temporal semantics on linear orders (~400-600 l

### Modal Logic

16 [NOT STARTED] — Add DecidableEq to Modal.Proposition, resolve LukasiewiczDerived 
  └─ 21 [NOT STARTED] — Port modal proof system and theorems to Cslib/Logics/Modal/ProofS (see above)
21 [NOT STARTED] — Port modal proof system and theorems to Cslib/Logics/Modal/ProofS
  └─ 5 [NOT STARTED] — (Bimodal Porting: Port Perpetuity theorems to Cslib/Logics) (see above)

### Temporal Logic

22 [NOT STARTED] — Build temporal proof system infrastructure and port temporal theo
  └─ 4 [NOT STARTED] — (Bimodal Porting: Port the Bimodal Hilbert-style proof sys) (see above)
  └─ 5 [NOT STARTED] — (Bimodal Porting: Port Perpetuity theorems to Cslib/Logics) (see above)
  └─ 23 [NOT STARTED] — Define standalone temporal semantics on linear orders (~400-600 l (see above)
23 [NOT STARTED] — Define standalone temporal semantics on linear orders (~400-600 l

### Bimodal Porting

2 [NOT STARTED] — Port Temporal Syntax (PR 1): Atom, Formula, Context, BigConj, Sub
  └─ 3 [NOT STARTED] — Port Frame Semantics (PR 2): TaskFrame, WorldHistory, TaskModel, 
    └─ 6 [NOT STARTED] — Port Frame Conditions and Soundness (PR 5): FrameClass, Validity, (see above)
  └─ 4 [NOT STARTED] — Port the Bimodal Hilbert-style proof system to Cslib/Logics/Bimod (see above)
4 [NOT STARTED] — Port the Bimodal Hilbert-style proof system to Cslib/Logics/Bimod
  └─ 5 [NOT STARTED] — Port Perpetuity theorems to Cslib/Logics/Bimodal/Theorems/Perpetu (see above)
  └─ 6 [NOT STARTED] — Port Frame Conditions and Soundness (PR 5): FrameClass, Validity, (see above)
  └─ 7 [NOT STARTED] — Port Deduction Infrastructure and MCS Theory (PR 6): DeductionThe (see above)
  └─ 9 [NOT STARTED] — Port Decidability and Tableau (PR 8): SignedFormula, Tableau, Clo (see above)
  └─ 10 [NOT STARTED] — Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 fi (see above)
  └─ 11 [NOT STARTED] — Port Conservative Extension (PR 10): ExtFormula, ExtDerivation, S (see above)
5 [NOT STARTED] — Port Perpetuity theorems to Cslib/Logics/Bimodal/Theorems/Perpetu
  └─ 7 [NOT STARTED] — Port Deduction Infrastructure and MCS Theory (PR 6): DeductionThe (see above)
  └─ 10 [NOT STARTED] — Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 fi (see above)
6 [NOT STARTED] — Port Frame Conditions and Soundness (PR 5): FrameClass, Validity,
  └─ 8 [NOT STARTED] — Port Strong Completeness (PR 7): Completeness.lean to Cslib/Logic (see above)
7 [NOT STARTED] — Port Deduction Infrastructure and MCS Theory (PR 6): DeductionThe
  └─ 8 [NOT STARTED] — Port Strong Completeness (PR 7): Completeness.lean to Cslib/Logic (see above)
  └─ 9 [NOT STARTED] — Port Decidability and Tableau (PR 8): SignedFormula, Tableau, Clo (see above)
  └─ 10 [NOT STARTED] — Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 fi (see above)
8 [NOT STARTED] — Port Strong Completeness (PR 7): Completeness.lean to Cslib/Logic
9 [NOT STARTED] — Port Decidability and Tableau (PR 8): SignedFormula, Tableau, Clo
10 [NOT STARTED] — Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 fi
11 [NOT STARTED] — Port Conservative Extension (PR 10): ExtFormula, ExtDerivation, S

### Project Management

12 [PLANNED] — Coordinate the cslib PR submission process for the Temporal Logic
15 [RESEARCHED] — Complete embedding lattice: add atom simp lemmas, PL.toBimodal pa
17 [PLANNED] — Clean stale task 14 references and verify Task Order consistency.
18 [RESEARCHED] — Generate project-overview.md for this repository
24 [RESEARCHED] — improve roadmap bimodal porting

## Tasks

### 24. Improve ROADMAP.md with BimodalLogic porting overview
- **Effort**: Medium (3-5 hours)
- **Status**: [RESEARCHED]
- **Task Type**: markdown
- **Research**: [024_improve_roadmap_bimodal_porting/reports/01_roadmap-research.md]

**Description**: Improve specs/ROADMAP.md to clearly introduce and describe the ambition to port BimodalLogic/ over to CSLib, populating Propositional/, Modal/, Temporal/, and Bimodal/ as appropriate, outlining the design decisions, the tasks along with a link to specs/TODO.md, creating a document that is easy for the maintainer of CSLib to take in and understand the current state of the project

### 23. Temporal semantics on linear orders
- **Effort**: Medium (4-6 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 22 (Temporal Infrastructure)

**Description**: Define standalone temporal semantics on linear orders (~400-600 lines, new infrastructure not ported from BimodalLogic). Define `Temporal.Model` on `LinearOrder`, `Temporal.Satisfies` for `{atom, bot, imp, untl, snce}`, basic validity, and frame conditions on linear orders. Enables standalone temporal soundness proofs. Target: `Cslib/Logics/Temporal/Semantics/`.

---

### 22. Temporal infrastructure and theorems
- **Effort**: Medium (6-10 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 20 (Propositional Hilbert Theorems)

**Description**: Build temporal proof system infrastructure and port temporal theorems (~1,500 lines). Scope: ~20 temporal axiom abbrevs, ~20 HasAxiom* typeclasses, restructure TemporalBXHilbert, make TemporalNecessitation non-empty, BimodalTMHilbert compatibility instance (diamond-avoidance pattern), Temporal.DerivationTree, TemporalDerived theorems (~790 lines), frame condition typeclasses (~130 lines). Target: Axioms.lean/ProofSystem.lean additions + `Cslib/Logics/Temporal/ProofSystem/` + `Cslib/Logics/Temporal/Theorems/`.

---

### 21. Modal proof system and theorems
- **Effort**: Medium (6-10 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 16 (DecidableEq), 20 (Propositional Theorems)

**Description**: Port modal proof system and theorems (~1,600 lines from BimodalLogic). Scope: (a) Modal.DerivationTree with ModalHilbert/ModalS5Hilbert instances (~400), (b) S4/S5 derived theorems + GeneralizedNecessitation as `[ModalS5Hilbert S]` lemmas (~1,200). Target: `Cslib/Logics/Modal/ProofSystem/` + `Cslib/Logics/Modal/Theorems/`.

---

### 20. Propositional Hilbert theorems
- **Effort**: Medium (6-10 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4

**Description**: Port propositional Hilbert-style theorems to `Cslib/Foundations/Logic/Theorems/` as generic `[PropositionalHilbert S]` lemmas (~2,400 lines from BimodalLogic). Scope: Combinators (I/B/C/S, ~300), Propositional/{Core,Connectives,Reasoning} (~1,100), ContextualProofs (~500), BigConj generic (~500). Note: DeductionTheorem stays per-logic (requires structural induction on DerivationTree, per team research finding).

---

### 19. Explore modular logic factoring: determine which BimodalLogic components belong in Propositional/, Modal/, and Temporal/ rather than Bimodal/, and revise tasks 2-11 accordingly
- **Effort**: Large
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Research**:
  - [019_explore_modular_logic_factoring/reports/01_factoring-synthesis.md]
  - [019_explore_modular_logic_factoring/reports/02_team-research.md]
- **Plan**:
  - [019_explore_modular_logic_factoring/plans/01_modular-factoring.md]
  - [019_explore_modular_logic_factoring/plans/02_revised-factoring.md]
- **Summary**: [019_explore_modular_logic_factoring/summaries/02_implementation-summary.md]

**Description**: Explore modular logic factoring: determine which BimodalLogic components belong in Propositional/, Modal/, and Temporal/ rather than Bimodal/, and revise tasks 2-11 accordingly. Analyze the BimodalLogic source to identify components that are purely propositional, purely modal, or purely temporal and can be developed in those standalone theories before being imported by the Bimodal/ theory. Revise the existing porting tasks (2-11) to reflect the proper factoring, ensuring each component lives at the most general level possible.

---

### 18. Generate project-overview.md for this repository
- **Effort**: Small (1-2 hours)
- **Status**: [RESEARCHING]
- **Task Type**: meta

**Description**: Generate project-overview.md for this repository. The current file contains the generic template placeholder. Run `/project-overview` to interactively scan the repository and create project-specific context.

---

### 17. Clean stale task 14 references and verify Task Order consistency
- **Effort**: Small (<1 hour)
- **Status**: [RESEARCHING]
- **Task Type**: meta

**Description**: Two project management cleanup tasks:
1. Clean stale task 14 dependency references in TODO.md task descriptions (task 14 is completed and archived)
2. Verify Task Order section reflects current dependency graph

**Note**: ROADMAP.md population is handled by task 19 (has full research context). This task focuses on cleanup only.

---

### 16. Add DecidableEq to Modal.Proposition, resolve LukasiewiczDerived
- **Effort**: Small (<1 hour)
- **Status**: [NOT STARTED]
- **Task Type**: lean4

**Description**: Formula type consistency fixes from code review:
1. Add `deriving DecidableEq, BEq` to `Modal.Proposition` in `Cslib/Logics/Modal/Basic.lean` for consistency with `Bimodal.Formula` and `Temporal.Formula`
2. Either instantiate `LukasiewiczDerived` for existing formula types or add docstring noting it's for future use in `Cslib/Foundations/Logic/Connectives.lean`

---

### 15. Complete embedding lattice: atom simp lemmas, PL.toBimodal, triangle-commutes
- **Effort**: Small (1-2 hours)
- **Status**: [RESEARCHING]
- **Task Type**: lean4

**Description**: Embedding completeness fixes from code review:
1. Add `@[simp]` lemmas for the `atom` case in `ModalEmbedding.lean`, `TemporalEmbedding.lean`, and `Propositional/Embedding.lean`
2. Add `PL.Proposition.toBimodal` function with `Coe` instance in `Propositional/Embedding.lean`
3. Add triangle-commutes lemma proving `PL.toModal.toBimodal = PL.toTemporal.toBimodal`

---

### 12. Coordinate cslib PR submission for Bimodal Logic integration
- **Effort**: Ongoing (tracked separately)
- **Status**: [RESEARCHING]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 5 (ProofSystem, Perpetuity Theorems)

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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
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
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: BimodalLogic:291 (toolchain upgrade)

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

