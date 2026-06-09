---
next_project_number: 24
---

# Tasks

## Task Order

*Updated 2026-06-08. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 2,12,15,16,17,18,19 | -- | -- |
| 2 | 3,4 | 2 | -- |
| 3 | 5,6,11 | 3,4 | -- |
| 4 | 7 | 4,5 | -- |
| 5 | 8,9,10 | 4,5,6,7 | -- |

**Grouped by Topic** (indented = depends on parent):

### Uncategorized

2 [NOT STARTED] — Port Temporal Syntax (PR 1): Atom, Formula, Context, BigConj, Sub
  └─ 3 [NOT STARTED] — Port Frame Semantics (PR 2): TaskFrame, WorldHistory, TaskModel, 
    └─ 6 [NOT STARTED] — Port Frame Conditions and Soundness (PR 5): FrameClass, Validity,
      └─ 8 [NOT STARTED] — Port Strong Completeness (PR 7): Completeness.lean to Cslib/Logic
  └─ 4 [NOT STARTED] — Port Proof System (PR 3): Axioms, Derivation, Derivable, Substitu
    └─ 5 [NOT STARTED] — Port Derived Theorems (PR 4): Combinators, Propositional/*, Conte
      └─ 7 [NOT STARTED] — Port Deduction Infrastructure and MCS Theory (PR 6): DeductionThe
        └─ 8 [NOT STARTED] — Port Strong Completeness (PR 7): Completeness.lean to Cslib/Logic (see above)
        └─ 9 [NOT STARTED] — Port Decidability and Tableau (PR 8): SignedFormula, Tableau, Clo
        └─ 10 [NOT STARTED] — Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 fi
      └─ 10 [NOT STARTED] — Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 fi (see above)
    └─ 6 [NOT STARTED] — Port Frame Conditions and Soundness (PR 5): FrameClass, Validity, (see above)
    └─ 7 [NOT STARTED] — Port Deduction Infrastructure and MCS Theory (PR 6): DeductionThe (see above)
    └─ 9 [NOT STARTED] — Port Decidability and Tableau (PR 8): SignedFormula, Tableau, Clo (see above)
    └─ 10 [NOT STARTED] — Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 fi (see above)
    └─ 11 [NOT STARTED] — Port Conservative Extension (PR 10): ExtFormula, ExtDerivation, S
12 [NOT STARTED] — Coordinate the cslib PR submission process for the Temporal Logic
15 [NOT STARTED] — Complete embedding lattice: add atom simp lemmas, PL.toBimodal pa
16 [NOT STARTED] — Add DecidableEq to Modal.Proposition, resolve LukasiewiczDerived 
17 [NOT STARTED] — Populate ROADMAP.md with porting plan, generate Task Order sectio
18 [NOT STARTED] — Generate project-overview.md for this repository
19 [RESEARCHED] — explore modular logic factoring

## Tasks

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
- **Status**: [PLANNED]
- **Task Type**: lean4
- **Research**:
  - [019_explore_modular_logic_factoring/reports/01_factoring-synthesis.md]
  - [019_explore_modular_logic_factoring/reports/02_team-research.md]
- **Plan**:
  - [019_explore_modular_logic_factoring/plans/01_modular-factoring.md]
  - [019_explore_modular_logic_factoring/plans/02_revised-factoring.md]

**Description**: Explore modular logic factoring: determine which BimodalLogic components belong in Propositional/, Modal/, and Temporal/ rather than Bimodal/, and revise tasks 2-11 accordingly. Analyze the BimodalLogic source to identify components that are purely propositional, purely modal, or purely temporal and can be developed in those standalone theories before being imported by the Bimodal/ theory. Revise the existing porting tasks (2-11) to reflect the proper factoring, ensuring each component lives at the most general level possible.

---

### 18. Generate project-overview.md for this repository
- **Effort**: Small (1-2 hours)
- **Status**: [NOT STARTED]
- **Task Type**: meta

**Description**: Generate project-overview.md for this repository. The current file contains the generic template placeholder. Run `/project-overview` to interactively scan the repository and create project-specific context.

---

### 17. Populate ROADMAP.md, generate Task Order, clean stale refs
- **Effort**: Small (1-2 hours)
- **Status**: [NOT STARTED]
- **Task Type**: meta

**Description**: Three project management improvements from code review:
1. Populate `specs/ROADMAP.md` with the 10-PR porting plan phases and milestones (currently empty default template)
2. Clean stale task 14 dependency references in TODO.md task descriptions (task 14 is now completed and archived)
3. Verify Task Order section reflects current dependency graph

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
- **Status**: [NOT STARTED]
- **Task Type**: lean4

**Description**: Embedding completeness fixes from code review:
1. Add `@[simp]` lemmas for the `atom` case in `ModalEmbedding.lean`, `TemporalEmbedding.lean`, and `Propositional/Embedding.lean`
2. Add `PL.Proposition.toBimodal` function with `Coe` instance in `Propositional/Embedding.lean`
3. Add triangle-commutes lemma proving `PL.toModal.toBimodal = PL.toTemporal.toBimodal`

---

### 12. Coordinate cslib PR submission for Bimodal Logic integration
- **Effort**: Ongoing (tracked separately)
- **Status**: [NOT STARTED]
- **Task Type**: general
- **Dependencies**: Task 14 (modular architecture must be complete first)

**Description**: Coordinate the cslib PR submission process for the Bimodal Logic integration. This task runs in parallel with porting tasks (2-11) and handles maintainer communication, namespace decisions, and CI compliance before each submission. Updated to reflect the modular architecture from task 14: content now spans `Cslib.Logics.Bimodal/` (primary, for the combined TM system) and `Cslib.Logics.Temporal/` (standalone temporal logic).

**Coordination Workflow**:

1. **Open Zulip Discussion** (first step, before any PR submission):
   - Open a thread on leanprover.zulipchat.com in the appropriate cslib channel
   - Propose integrating bimodal temporal logic TM to cslib under `Cslib.Logics.Bimodal/` with standalone temporal logic under `Cslib.Logics.Temporal/`
   - Include: overview of TM logic (bimodal: S5 box + temporal Until/Since over task frames), modular architecture (separate formula types per logic with typeclass hierarchy), motivation (verified decision procedure, completeness proof, ~30k lines Lean 4), PR strategy (10 modular PRs in dependency order)
   - Ask: namespace decision, PR review process, any style requirements for logic contributions
   - Note: `Cslib.Logics.Modal/` and `Cslib.Logics.Propositional/` have already been refactored to align primitives (task 14)

2. **Namespace Decision** (follow from Zulip discussion):
   - If maintainers prefer different namespaces: update all porting task descriptions accordingly
   - Confirm before starting task 2, as all subsequent PRs inherit the namespace decision
   - Current proposal: `Cslib.Logics.Bimodal` (combined TM) + `Cslib.Logics.Temporal` (standalone)

3. **PR Submission Order** (follow dependency graph):
   - PR 1 (Bimodal Syntax, task 2): submit first, establish review pattern
   - PR 2 (Semantics, task 3) and PR 3 (ProofSystem, task 4): after PR 1 merged, can overlap
   - PR 4 (Theorems, task 5): after PR 3 merged
   - PR 5 (FrameConditions+Soundness, task 6): after PRs 2+3 merged
   - PR 6 (MCS/Deduction, task 7): after PRs 3+4 merged
   - PR 7 (Completeness, task 8): after PRs 5+6 merged
   - PR 8 (Decidability, task 9): after PRs 3+6 merged (largest PR, ~10k lines)
   - PR 9 (Separation, task 10): after PRs 3+4+6 merged
   - PR 10 (ConservativeExtension, task 11): after PR 3 merged (independent of 5-9)

4. **CI Checks** (before each PR submission):
   - Run: lake build (must pass with zero errors)
   - Run: lake shake (must show no unused imports)
   - Run: set_option linter.all true in each file (must show no linter warnings)
   - Confirm: zero sorry in submitted files
   - Confirm: all files have Apache 2.0 copyright headers

5. **Review Cycle Management**:
   - Keep PRs small and self-contained (max ~3,500 lines per PR except task 9)
   - Address reviewer feedback within 48 hours to maintain momentum
   - For PR 8 (Decidability, ~10k lines): consider splitting into 8a+8b if reviewer requests

---

### 11. Port Conservative Extension to Bimodal module
- **Effort**: Medium (6-10 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 14 (ProofSystem and modular architecture must be complete)

**Description**: Port conservative extension results from BimodalLogic to `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/`. This result shows that the BX extension preserves all theorems of the base logic. The ported code operates on `Bimodal.Formula` (all 6 constructors) and must adapt imports to use cslib's formula type and typeclass infrastructure from task 14.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/ConservativeExtension/):
- ExtFormula.lean (~400 lines): extended formula type with additional connectives
- ExtDerivation.lean (~400 lines): derivation rules for extended language
- Substitution.lean (~350 lines): substitution theorem for conservative extension
- Lifting.lean (~350 lines): lifting theorems between base and extended language

**Target path**: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/`

**Adaptation notes**: ExtFormula extends the bimodal formula type. Since `Bimodal.Formula` already exists from task 14, ExtFormula must build on it rather than on BimodalLogic's original Formula type. Imports change from `Bimodal.Syntax.Formula` to `Cslib.Logics.Bimodal.Syntax.Formula`.

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
- **Dependencies**: Tasks 4, 5, 7, 14 (ProofSystem, Theorems, MCS/Deduction, and modular architecture)

**Description**: Port the separation theorem from BimodalLogic to `Cslib/Logics/Bimodal/Metalogic/Separation/`. The separation theorem proves that TM is conservative over its temporal and modal fragments separately — it is inherently a bimodal result that references the embedding functions from task 14 (`Modal.Formula.toBimodal`, `Temporal.Formula.toBimodal`). This is one of the key results that connects the separate formula types in the modular architecture.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/WeakCanonical/Separation/):
- Defs.lean, FormulaOps.lean, NormalForm.lean, KampTranslation.lean
- Eliminations.lean, DualEliminations.lean, Distributivity.lean, Duality.lean
- NegationEquiv.lean, TemporalClosure.lean, SemanticBridge.lean, SeparationThm.lean
- IntHelpers.lean, DedekindZ/ (Cases.lean, QLemma.lean)
- Hierarchy/ (HierarchyDefs.lean, HierarchyInduction.lean, HierarchyCaseSep.lean, HierarchyCompletion.lean)

**Target path**: `Cslib/Logics/Bimodal/Metalogic/Separation/`

**Adaptation notes**: The separation theorem explicitly characterizes which bimodal formulas are equivalent to pure modal or pure temporal formulas. The Kamp translation and formula operations must reference `Bimodal.Formula` from task 14. The result should connect to the embedding functions to state: if `φ : Bimodal.Formula` is in the modal fragment, then there exists `ψ : Modal.Formula` with `ψ.toBimodal` equivalent to `φ`.

**Estimated scope**: ~3,500 lines across 20+ files

---

### 9. Port Decidability and Tableau to Bimodal module
- **Effort**: X-Large (20-30 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 7, 14 (ProofSystem, MCS/Deduction, and modular architecture)

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

**Adaptation notes**: SignedFormula and Tableau must reference `Bimodal.Formula` from task 14 instead of BimodalLogic's original Formula. The decision procedure should provide an `InferenceSystem` instance for `Bimodal.HilbertTM` once DerivationTree is available (from task 4). SubformulaClosure (used by tableau) ports alongside this task.

**Estimated scope**: ~10,000 lines across 18+ files

**Note**: Consider splitting into (9a) Core tableau/decision procedure (~5k lines) and (9b) FMP (~4k lines) if review burden is too high.

---

### 8. Port Completeness to Bimodal module
- **Effort**: Large (10-16 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 6, 7, 14 (FrameConditions+Soundness, MCS/Deduction, and modular architecture)

**Description**: Port completeness results from BimodalLogic to `Cslib/Logics/Bimodal/Metalogic/`. This includes the main completeness theorem (every valid formula is derivable in TM), the BXCanonical construction (chronicle-based canonical model), and the algebraic completeness path. The completeness proof is inherently bimodal — the MCS construction closes under all 42 axiom constructors, and the Burgess-Xu chronicle construction requires the interaction axiom MF.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/):
- Completeness.lean (~520 lines): main completeness theorem
- BXCanonical/ (~15 files): canonical chain, canonical model, chronicle construction, filtration, quasimodel, truth lemma, completeness proof
- Algebraic/ (~11 files): D-parametric algebraic completeness, Lindenbaum quotient, interior operators, parametric truth lemma
- Bundle/ (~14 files): BFMCS/FMCS construction, canonical frame, modal saturation, temporal coherence

**Target path**: `Cslib/Logics/Bimodal/Metalogic/`

**Adaptation notes**: All files reference the full 6-constructor formula type. Port to use `Bimodal.Formula` from task 14. The canonical model construction uses `DerivationTree` from task 4 and MCS theory from task 7. The completeness theorem currently has sorry (chronicle construction); port the sorry as-is and track separately.

**Estimated scope**: ~520 lines for the main theorem, plus ~40 files of supporting infrastructure (~15,000 lines total including BXCanonical, Algebraic, Bundle)

---

### 7. Port Deduction Infrastructure and MCS Theory to Bimodal module
- **Effort**: Large (10-14 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 5, 14 (ProofSystem, Theorems, and modular architecture)

**Description**: Port deduction theorem and maximal consistent set theory from BimodalLogic to `Cslib/Logics/Bimodal/Metalogic/Core/`. This establishes the core metalogical infrastructure for completeness. The deduction theorem and MCS construction operate on the full bimodal proof system (all 42 axioms) and cannot be factored into separate modal/temporal components.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/Core/):
- Core.lean: module aggregator
- DeductionTheorem.lean (~500 lines): deduction theorem for TM proof system
- MaximalConsistent.lean (~600 lines): MCS definition and basic properties
- MCSProperties.lean (~700 lines): Lindenbaum lemma, MCS enumeration, closure properties
- RestrictedMCS/Basic.lean (~400 lines): restricted MCS for frame-specific completeness
- RestrictedMCS/Deferral.lean: MCS deferral properties

**Target path**: `Cslib/Logics/Bimodal/Metalogic/Core/`

**Adaptation notes**: MCS construction references Context and DerivationTree which must use `Bimodal.Formula`. The deduction theorem depends on the full axiom set from task 4.

**Estimated scope**: ~2,500 lines across 6 files

---

### 6. Port Frame Conditions and Soundness to Bimodal module
- **Effort**: Large (10-14 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 3, 4, 14 (Semantics, ProofSystem, and modular architecture)

**Description**: Port frame conditions and soundness from BimodalLogic to `Cslib/Logics/Bimodal/FrameConditions/` and `Cslib/Logics/Bimodal/Metalogic/Soundness/`. The soundness proof is inherently bimodal — the interaction axiom MF's soundness requires both task frame semantics and modal quantification over world histories simultaneously. The `FrameClass` type (Base/Dense/Discrete) and `minFrameClass` gating pattern should be preserved.

**Source files**:
- FrameConditions/ (4 files, ~790 lines): FrameClass.lean, Validity.lean, Soundness.lean, Compatibility.lean
- Metalogic/Soundness.lean (~400 lines): main soundness theorem
- Metalogic/SoundnessLemmas/ (3 files): Core.lean, DenseValidity.lean, FrameClassVariants.lean
- Metalogic/DenseSoundness.lean (~300 lines)
- Metalogic/DiscreteSoundness.lean (~300 lines)

**Target paths**:
- `Cslib/Logics/Bimodal/FrameConditions/`
- `Cslib/Logics/Bimodal/Metalogic/Soundness/`

**Adaptation notes**: FrameClass typeclass hierarchy (`LinearTemporalFrame`, `DenseTemporalFrame`, `DiscreteTemporalFrame`) should integrate with task 14's proof system typeclasses. Consider providing `HasAxiomDensity` and `HasAxiomDiscreteness` instances gated by frame class.

**Estimated scope**: ~2,500 lines across 10 files

---

### 5. Port Derived Theorems to Bimodal module
- **Effort**: Large (10-14 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 14 (ProofSystem and modular architecture)
- **External Dependencies**: BimodalLogic task 294 (sorry elimination in ModalS5/Perpetuity)

**Description**: Port derived theorem library from BimodalLogic to `Cslib/Logics/Bimodal/Theorems/`. These theorems are proved using the full TM proof system (DerivationTree) and include propositional, modal S5, temporal, and perpetuity results. The propositional and modal-only theorems (Combinators, Propositional/) could in principle be stated at the typeclass level (`[PropositionalHilbert S]`, `[ModalS5Hilbert S]`) for reuse, but the pragmatic approach is to port them first and generalize later.

**Source files** (from BimodalLogic Theories/Bimodal/Theorems/):
- Combinators.lean (~300 lines): identity, composition, flip, pair
- Propositional/Core.lean, Propositional/Connectives.lean, Propositional/Reasoning.lean (~1,100 lines total)
- ContextualProofs.lean (~500 lines): weakening, cut, contextual rules
- GeneralizedNecessitation.lean (~400 lines): necessitation generalization
- ModalS4.lean, ModalS5.lean (~800 lines): S4/S5 derived theorems
- TemporalDerived.lean: temporal-specific derived theorems
- Perpetuity/ (Bridge.lean, Helpers.lean, Principles.lean, ~800 lines): perpetuity fixed-point theorems

**Target path**: `Cslib/Logics/Bimodal/Theorems/`

**Adaptation notes**: All theorems reference `DerivationTree` and `Bimodal.Formula`. Port to use cslib's formula type. Where possible, also provide typeclass-level versions (e.g., `[PropositionalHilbert S] → S ⊢ ImplyK φ ψ`) but this is optional and can be a follow-up.

**Estimated scope**: ~7,300 lines across 13 files

---

### 4. Port Proof System to Bimodal module
- **Effort**: Large (8-12 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 2, 14 (Syntax and modular architecture)

**Description**: Port the Hilbert-style axiom system from BimodalLogic to `Cslib/Logics/Bimodal/ProofSystem/`. This is the concrete proof system with all 42 axiom schemata (propositional + S5 modal + BX temporal + interaction MF/TF) and the FrameClass-parameterized DerivationTree with 7 inference rules. Task 14 already defined the polymorphic axiom `abbrev`s and `HasAxiom*` typeclasses in `Cslib.Foundations.Logic.Axioms` and `Cslib.Foundations.Logic.ProofSystem`; this task provides the concrete `Axiom` inductive, `DerivationTree`, and `Derivable` predicate, then registers `InferenceSystem` and `BimodalTMHilbert` instances for the `Bimodal.HilbertTM` tag.

**Source files** (from BimodalLogic Theories/Bimodal/ProofSystem/):
- Axioms.lean (~400 lines): 42 axiom schemata with `minFrameClass` gating
- Derivation.lean (~600 lines): `DerivationTree` inductive (7 rules), `FrameClass` parameterization
- Derivable.lean (~300 lines): `Derivable` predicate, basic properties
- Substitution.lean (~500 lines): uniform substitution theorem
- LinearityDerivedFacts.lean (~200 lines): linearity-specific derived facts

**Target path**: `Cslib/Logics/Bimodal/ProofSystem/`

**Integration with task 14 infrastructure**:
- Complete the temporal axiom `abbrev`s in `Cslib.Foundations.Logic.Axioms` (currently only `SerialFuture` and `SerialPast`; need TK, T4, TT-F/P, TA, TL, Lin, and all BX axioms)
- Register `InferenceSystem Bimodal.HilbertTM (Bimodal.Judgement)` instance mapping to `DerivationTree`
- Register `BimodalTMHilbert Bimodal.HilbertTM` instance providing all `HasAxiom*` instances from the concrete `Axiom` inductive
- Align `Derivable` with `InferenceSystem.DerivableIn` via the tag type

**Estimated scope**: ~2,000 lines across 5 files plus ~200 lines of axiom `abbrev` additions to Axioms.lean

---

### 3. Port Task Frame Semantics to Bimodal module
- **Effort**: Large (8-12 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 2, 14 (Syntax and modular architecture)

**Description**: Port task frame semantics from BimodalLogic to `Cslib/Logics/Bimodal/Semantics/`. Task frame semantics is inherently bimodal: `□φ` quantifies over world histories in a shift-closed set (implicit S5), while temporal operators (G, H) quantify over time points within a history. This is fundamentally different from cslib's existing Kripke semantics for modal logic (`Model World Atom` with accessibility relation) — the two semantic frameworks coexist at different logic levels.

**Source files** (from BimodalLogic Theories/Bimodal/Semantics/):
- TaskFrame.lean (~500 lines): `TaskFrame T` with task_rel, nullity, compositionality
- WorldHistory.lean (~400 lines): `WorldHistory F` with convex time domains, shift-closure
- TaskModel.lean (~400 lines): model = frame + valuation
- Truth.lean (~600 lines): recursive `truth_at M τ t ht φ` for all 6 constructors
- Validity.lean (~300 lines): validity polymorphic over temporal type `T`

**Target path**: `Cslib/Logics/Bimodal/Semantics/`

**Adaptation notes**: `Truth.lean` evaluates `Bimodal.Formula` (all 6 constructors). Port to use `Cslib.Logic.Bimodal.Formula` from task 14. The `truth_at` function must match the constructor names in the new formula type. Consider providing an `InferenceSystem` instance for semantic derivation (as cslib's Modal module does with `HasInferenceSystem (Judgement World Atom)`).

**Estimated scope**: ~2,200 lines across 5 files

---

### 2. Port Bimodal Syntax infrastructure (Context, BigConj, Subformulas)
- **Effort**: Medium (6-10 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 14 (modular architecture — formula types already exist)

**Description**: Port the syntax infrastructure from BimodalLogic to `Cslib/Logics/Bimodal/Syntax/`. Task 14 already created `Bimodal.Formula` with `{atom, bot, imp, box, untl, snce}` and `Temporal.Formula` with `{atom, bot, imp, untl, snce}`. This task ports the remaining syntax components that operate on the formula type: Context (proof assumptions), BigConj (finite conjunction), Subformulas, and SubformulaClosure. These are ported against `Bimodal.Formula` since BimodalLogic's originals use all 6 constructors.

**Note on Formula.lean**: BimodalLogic's `Syntax/Formula.lean` (~800 lines) contains not just the inductive type but also `complexity`, `atomSet`, `swap_temporal`, `Countable`/`Denumerable`/`Infinite` instances, and many structural lemmas. The inductive type already exists from task 14, but these additional properties need porting.

**Source files** (from BimodalLogic Theories/Bimodal/Syntax/):
- Formula.lean (~800 lines): complexity, atomSet, swap_temporal, Countable instances (the inductive type portion already done in task 14 — port remaining ~500 lines of properties)
- Atom.lean (~300 lines): PropAtom type, decidable equality — may not be needed if cslib uses a generic `Atom` parameter
- Context.lean (~400 lines): `Context := List Formula`, context operations, membership, subset
- BigConj.lean (~500 lines): finite conjunction folding, BigConj properties
- Subformulas.lean (~500 lines): subformula relation, subformula lemmas
- SubformulaClosure/ (3 files, ~800 lines): Closure.lean, NestingDepth.lean, TemporalFormulas.lean

**Target path**: `Cslib/Logics/Bimodal/Syntax/`

**Adaptation notes**: All files reference `Formula` with 6 constructors — matches `Bimodal.Formula` from task 14. Adapt imports from `Bimodal.Syntax.Formula` to `Cslib.Logics.Bimodal.Syntax.Formula`. The `Atom` type in BimodalLogic is a concrete `PropAtom`; cslib's formula types use a generic `Atom` parameter — this is the main adaptation needed.

**Estimated scope**: ~2,500 lines across 7 files (after excluding the already-ported inductive type)

---

