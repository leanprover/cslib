---
next_project_number: 15
---

# Tasks

## Tasks

### 14. Design modular logic architecture for composable modal, temporal, and bimodal syntax and proof systems
- **Effort**: Large
- **Status**: [PLANNED]
- **Task Type**: lean4
- **Research**: [014_design_modular_logic_architecture/reports/01_team-research.md]
- **Plan**: [014_design_modular_logic_architecture/plans/01_modular-logic-arch.md]

**Description**: Explore how to design a modular architecture so that modal syntax and proof theory, temporal syntax and proof theory, and bimodal syntax and proof theory can each be imported independently and composed together. Currently BimodalLogic defines a monolithic `Formula` type with all six constructors (atom, bot, imp, box, untl, snce), but cslib already has a separate `Cslib.Logics.Modal` module with its own `Proposition` type. The goal is to determine how best to factor the syntax and proof systems so that: (1) the existing modal foundations in cslib can be reused or extended rather than duplicated, (2) a standalone temporal logic module (Until/Since over linear orders) can exist independently, (3) the bimodal TM logic can be defined as a composition of modal and temporal components with any necessary interaction axioms, and (4) the metalogic results (soundness, completeness, decidability) can be stated and proved at the appropriate level of generality. This may require changes to `Cslib.Logics.Modal` to make it more composable (e.g., parameterizing over formula types, using typeclasses for proof systems, or adopting cslib's `InferenceSystem` framework). Research should examine: existing patterns in cslib's `Foundations.Logic.InferenceSystem`, how Mathlib handles composable algebraic structures as a model, approaches to multi-modal logics in the literature, and whether BimodalLogic's monolithic proofs can be cleanly factored or whether the interaction between modalities makes decomposition impractical for certain results

---

### 13. Proof-of-concept port of Syntax module to validate porting approach
- **Effort**: Medium (4-8 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: none (but should be done before tasks 2-11 to derisk)
- **External Dependencies**: BimodalLogic task 291 (toolchain upgrade must complete first)

**Description**: Proof-of-concept port of the Syntax module to cslib to validate the porting approach and estimate per-file effort before committing to the full 10-PR integration. This derisking task should be done early -- before implementing tasks 2-11 -- to discover any unexpected porting challenges.

**Scope**: Port the 5 Syntax files from BimodalLogic to Cslib/Logics/Temporal/Syntax/:
- Atom.lean (~300 lines): PropAtom type, decidable equality
- Formula.lean (~800 lines): Formula inductive type with all operators
- Context.lean (~400 lines): proof context
- BigConj.lean (~500 lines): finite conjunction
- Subformulas.lean (~500 lines): subformula closure

**What to document** (in task summary):
- Which namespace rename patterns are mechanical vs require case-by-case judgment
- Which Mathlib imports break (API changes from v4.27 to v4.31)
- Which sorry-free proofs require adjustments due to tactic changes
- Actual effort per file (minutes/hours per 100 lines)
- Any style issues non-trivial to fix

**Porting Checklist**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Temporal
- [ ] Add module declaration at top: namespace Cslib.Logics.Temporal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)

**Output**: A working Cslib/Logics/Temporal/Syntax/ directory in cslib that can serve as the actual PR 1 submission, plus a written effort estimate for tasks 2-11.

---

### 12. Coordinate cslib PR submission for Temporal Logic integration
- **Effort**: Ongoing (tracked separately)
- **Status**: [NOT STARTED]
- **Task Type**: general
- **Dependencies**: none (ongoing coordination; start immediately in parallel with preparation)

**Description**: Coordinate the cslib PR submission process for the Temporal Logic integration. This task runs in parallel with all 10 porting tasks (2-11) and handles maintainer communication, namespace decisions, and CI compliance before each submission.

**Coordination Workflow**:

1. **Open Zulip Discussion** (first step, before any PR submission):
   - Open a thread on leanprover.zulipchat.com in #mathlib4 or appropriate channel
   - Propose integrating bimodal temporal logic TM to cslib under Cslib.Logics.Temporal
   - Include: overview of TM logic (bimodal: S5 box + temporal Until/Since over task frames), motivation (verified decision procedure, completeness proof, ~30k lines Lean 4), PR strategy (10 modular PRs in dependency order)
   - Ask: namespace decision, PR review process, any style requirements for logic contributions

2. **Namespace Decision** (follow from Zulip discussion):
   - If maintainers prefer different namespace: update all porting task descriptions via sed-based rename
   - Confirm before starting task 2 (Syntax port), as all subsequent PRs inherit the namespace decision
   - Current proposal: Cslib.Logics.Temporal (mirrors Cslib.Logics.Modal, Cslib.Logics.Linear patterns)

3. **PR Submission Order** (follow dependency graph):
   - PR 1 (Syntax, task 2): submit first, establish review pattern
   - PR 2 (Semantics, task 3) and PR 3 (ProofSystem, task 4): after PR 1 merged, can overlap in review
   - PR 10 (ConservativeExtension, task 11): independent of PRs 2-9, can submit early
   - PR 4 (Theorems, task 5): after PR 3 merged and BimodalLogic task 294 complete
   - PR 5 (FrameConditions+Soundness, task 6): after PRs 2+3 merged
   - PR 6 (MCS/Deduction, task 7): after PRs 3+4 merged
   - PR 7 (Completeness, task 8): after PRs 5+6 merged
   - PR 8 (Decidability, task 9): after PRs 3+6 merged (largest PR, ~10k lines)
   - PR 9 (Separation, task 10): after PRs 3+4+6 merged

4. **CI Checks** (before each PR submission):
   - Run: lake build (must pass with zero errors)
   - Run: lake shake (must show no unused imports)
   - Run: set_option linter.all true in each file (must show no linter warnings)
   - Confirm: zero sorry in submitted files (grep -rn sorry Cslib/Logics/Temporal/)
   - Confirm: all files have Apache 2.0 copyright headers

5. **Review Cycle Management**:
   - Keep PRs small and self-contained (max ~3,500 lines per PR except task 9)
   - Address reviewer feedback within 48 hours to maintain momentum
   - For PR 8 (Decidability, ~10k lines): consider splitting into 8a+8b if reviewer requests

---

### 11. Port Conservative Extension (PR 10)
- **Effort**: Medium (6-10 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 4 (ProofSystem must be merged first; independent of tasks 5-10)
- **External Dependencies**: BimodalLogic task 291 (toolchain upgrade)

**Description**: Port Conservative Extension (PR 10): ExtFormula, ExtDerivation, Substitution, Lifting to Cslib/Logics/Temporal/Metalogic/ConservativeExtension/. The conservative extension result shows that the BX extension of the temporal base logic preserves all theorems of the base logic.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/ConservativeExtension/):
- ExtFormula.lean (~400 lines): extended formula type with additional connectives
- ExtDerivation.lean (~400 lines): derivation rules for extended language
- Substitution.lean (~350 lines): substitution theorem for conservative extension
- Lifting.lean (~350 lines): lifting theorems between base and extended language

**Target path**: Cslib/Logics/Temporal/Metalogic/ConservativeExtension/

**Estimated scope**: ~1,500 lines across 4 files

**PR title**: feat(Logics/Temporal): add Metalogic/ConservativeExtension module

**Porting Checklist (apply to every file in this PR)**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Temporal
- [ ] Add module declaration at top: namespace Cslib.Logics.Temporal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)

---

### 10. Port Separation Theorem (PR 9)
- **Effort**: Large (10-14 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 5, 7 (ProofSystem, Theorems, and MCS/Deduction must all be merged first)
- **External Dependencies**: BimodalLogic task 291 (toolchain upgrade)

**Description**: Port Separation Theorem (PR 9): WeakCanonical/Separation/* (16 files) to Cslib/Logics/Temporal/Metalogic/Separation/. The separation theorem proves that TM is conservative over its temporal and modal fragments separately.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/WeakCanonical/Separation/ and related):
- Separation/*.lean (~16 files, ~3,500 lines): weak canonical model construction, chronicle structures, separation between temporal and modal components
- Key files: SeparationTheorem.lean (main result), ChronicleCanonical.lean, WeakCanonicalModel.lean, TemporalSeparation.lean, ModalSeparation.lean

**Target path**: Cslib/Logics/Temporal/Metalogic/Separation/

**Estimated scope**: ~3,500 lines across 16 files

**PR title**: feat(Logics/Temporal): add Metalogic/Separation module (Separation Theorem)

**Porting Checklist (apply to every file in this PR)**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Temporal
- [ ] Add module declaration at top: namespace Cslib.Logics.Temporal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)

---

### 9. Port Decidability and Tableau (PR 8)
- **Effort**: X-Large (20-30 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 7 (ProofSystem and MCS/Deduction must be merged first)
- **External Dependencies**: BimodalLogic task 291 (toolchain upgrade)

**Description**: Port Decidability and Tableau (PR 8): SignedFormula, Tableau, Closure, Saturation, ProofExtraction, Correctness, DecisionProcedure, CountermodelExtraction, FMP/* to Cslib/Logics/Temporal/Metalogic/Decidability/. This is the largest PR (~10k lines) covering the full tableau-based decision procedure for TM logic.

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

**Target path**: Cslib/Logics/Temporal/Metalogic/Decidability/

**Estimated scope**: ~10,000 lines across 18+ files

**PR title**: feat(Logics/Temporal): add Metalogic/Decidability module (Tableau, FMP, DecisionProcedure)

**Note**: This PR may benefit from splitting into two sub-tasks: (9a) Core tableau/decision procedure (~5k lines) and (9b) FMP (~4k lines). Consider splitting if review burden is too high.

**Porting Checklist (apply to every file in this PR)**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Temporal
- [ ] Add module declaration at top: namespace Cslib.Logics.Temporal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)

---

### 8. Port Strong Completeness (PR 7)
- **Effort**: Medium (4-6 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 6, 7 (FrameConditions+Soundness and MCS/Deduction must both be merged first)
- **External Dependencies**: BimodalLogic task 291 (toolchain upgrade)

**Description**: Port Strong Completeness (PR 7): Completeness.lean to Cslib/Logics/Temporal/Metalogic/. This is the main completeness theorem: every valid formula is derivable in the BX/TM axiom system.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/):
- Completeness.lean (~520 lines): main completeness theorem for BX logic (bx_completeness), canonical model construction, truth lemma

**Target path**: Cslib/Logics/Temporal/Metalogic/

**Estimated scope**: ~520 lines, 1 file

**PR title**: feat(Logics/Temporal): add Completeness theorem (bx_completeness)

**Porting Checklist (apply to every file in this PR)**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Temporal
- [ ] Add module declaration at top: namespace Cslib.Logics.Temporal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)

---

### 7. Port Deduction Infrastructure and MCS Theory (PR 6)
- **Effort**: Large (10-14 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 4, 5 (ProofSystem and Theorems must be merged first)
- **External Dependencies**: BimodalLogic task 291 (toolchain upgrade)

**Description**: Port Deduction Infrastructure and MCS Theory (PR 6): DeductionTheorem, MaximalConsistent, MCSProperties, RestrictedMCS to Cslib/Logics/Temporal/Metalogic/Core/. This PR establishes the core metalogical infrastructure for completeness: deduction theorem and maximal consistent set theory.

**Source files** (from BimodalLogic Theories/Bimodal/Metalogic/Core/):
- DeductionTheorem.lean (~500 lines): deduction theorem for BX/TM proof system
- MaximalConsistent.lean (~600 lines): definition and basic properties of maximal consistent sets (MCS)
- MCSProperties.lean (~700 lines): Lindenbaum lemma, MCS enumeration, key MCS closure properties
- RestrictedMCS.lean (~400 lines): restricted MCS for density/discreteness frame-specific completeness
- DualMCS.lean (~300 lines): dual MCS properties (past accessibility reconstruction)

**Target path**: Cslib/Logics/Temporal/Metalogic/Core/

**Estimated scope**: ~2,500 lines across 6 files

**PR title**: feat(Logics/Temporal): add Metalogic/Core module (DeductionTheorem, MaximalConsistent, MCS)

**Porting Checklist (apply to every file in this PR)**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Temporal
- [ ] Add module declaration at top: namespace Cslib.Logics.Temporal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)

---

### 6. Port Frame Conditions and Soundness (PR 5)
- **Effort**: Large (10-14 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Tasks 3, 4 (Semantics and ProofSystem must be merged first)
- **External Dependencies**: BimodalLogic task 291 (toolchain upgrade)

**Description**: Port Frame Conditions and Soundness (PR 5): FrameClass, Validity, Soundness, SoundnessLemmas, DenseSoundness, DiscreteSoundness to Cslib/Logics/Temporal/FrameConditions/ and Cslib/Logics/Temporal/Metalogic/Soundness/. This PR establishes the soundness of the BX/TM axiom system with respect to various frame classes.

**Source files** (from BimodalLogic Theories/Bimodal/FrameConditions/ and Metalogic/):
- FrameConditions/*.lean (~5 files, ~2,000 lines): frame condition predicates (density, discreteness, linearity, convergence), FrameClass type
- Metalogic/Soundness.lean (~400 lines): main soundness theorem for BX axiom system
- Metalogic/SoundnessLemmas.lean (~500 lines): supporting lemmas for soundness proof
- Metalogic/DenseSoundness.lean (~300 lines): soundness for dense frame class
- Metalogic/DiscreteSoundness.lean (~300 lines): soundness for discrete frame class

**Target paths**:
- Cslib/Logics/Temporal/FrameConditions/ (frame condition files)
- Cslib/Logics/Temporal/Metalogic/Soundness/ (soundness proof files)

**Estimated scope**: ~3,500 lines across 10+ files

**PR title**: feat(Logics/Temporal): add FrameConditions and Soundness modules

**Porting Checklist (apply to every file in this PR)**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Temporal
- [ ] Add module declaration at top: namespace Cslib.Logics.Temporal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)

---

### 5. Port Derived Theorems (PR 4)
- **Effort**: Large (10-14 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 4 (ProofSystem must be merged first)
- **External Dependencies**: BimodalLogic tasks 291 (toolchain upgrade) and 294 (sorry elimination in ModalS5/Perpetuity)

**Description**: Port Derived Theorems (PR 4): Combinators, Propositional/*, ContextualProofs, GeneralizedNecessitation to Cslib/Logics/Temporal/Theorems/. This PR ports the derived theorem library built on top of the Hilbert-style proof system.

**Source files** (from BimodalLogic Theories/Bimodal/Theorems/):
- Combinators.lean (~300 lines): fundamental combinators (identity, composition, flip, pair)
- Propositional/Basic.lean (~400 lines): propositional derived theorems (ex falso, disjunction introduction, etc.)
- Propositional/Extras.lean (~300 lines): additional propositional laws
- ContextualProofs.lean (~500 lines): proof rules in context, weakening, cut
- GeneralizedNecessitation.lean (~400 lines): necessitation generalization for modal operators
- ModalS5.lean (requires BimodalLogic task 294: sorry elimination) -- S5 derived theorems
- Perpetuity/Principles.lean (requires BimodalLogic task 294: sorry elimination) -- perpetuity fixed-point theorems

**Target path**: Cslib/Logics/Temporal/Theorems/

**Estimated scope**: ~3,000 lines across 6+ files

**PR title**: feat(Logics/Temporal): add Theorems module (Combinators, Propositional, ContextualProofs, GeneralizedNecessitation)

**Porting Checklist (apply to every file in this PR)**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Temporal
- [ ] Add module declaration at top: namespace Cslib.Logics.Temporal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)

---

### 4. Port Proof System (PR 3)
- **Effort**: Large (8-12 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 2 (Syntax must be merged first)
- **External Dependencies**: BimodalLogic task 291 (toolchain upgrade)

**Description**: Port Proof System (PR 3): Axioms, Derivation, Derivable, Substitution, LinearityDerivedFacts to Cslib/Logics/Temporal/ProofSystem/. Defines the Hilbert-style axiom system for TM bimodal logic.

**Source files** (from BimodalLogic Theories/Bimodal/ProofSystem/):
- Axioms.lean (~400 lines): all 42 axiom schemata for BX/TM (including temporal Until/Since axioms, S5 box axioms, Barcan formula variants)
- Derivation.lean (~600 lines): DerivationTree inductive type with 7 rules (assumption, modus ponens, necessitation, temporal necessitation, temporal duality, axiom instantiation, weakening)
- Derivable.lean (~300 lines): Derivable predicate, basic properties
- Substitution.lean (~500 lines): uniform substitution theorem, substitution lemmas
- LinearityDerivedFacts.lean (~200 lines): derived theorems specific to linear temporal frames

**Target path**: Cslib/Logics/Temporal/ProofSystem/

**Estimated scope**: ~2,000 lines across 5 files

**PR title**: feat(Logics/Temporal): add ProofSystem module (Axioms, Derivation, Derivable, Substitution)

**Porting Checklist (apply to every file in this PR)**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Temporal
- [ ] Add module declaration at top: namespace Cslib.Logics.Temporal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)

---

### 3. Port Frame Semantics (PR 2)
- **Effort**: Large (8-12 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: Task 2 (Syntax must be merged first)
- **External Dependencies**: BimodalLogic task 291 (toolchain upgrade)

**Description**: Port Frame Semantics (PR 2): TaskFrame, WorldHistory, TaskModel, Truth, Validity to Cslib/Logics/Temporal/Semantics/. Defines the Kripke-style semantic framework for bimodal temporal logic.

**Source files** (from BimodalLogic Theories/Bimodal/Semantics/):
- TaskFrame.lean (~500 lines): frame record with temporal and modal accessibility relations
- WorldHistory.lean (~400 lines): world history type, cofinal subsets, orderings
- TaskModel.lean (~400 lines): model = frame + valuation, canonical naming
- Truth.lean (~600 lines): inductive truth definition for all formula constructors
- Validity.lean (~300 lines): validity, satisfiability, frame class validity

**Target path**: Cslib/Logics/Temporal/Semantics/

**Estimated scope**: ~2,200 lines across 5 files

**PR title**: feat(Logics/Temporal): add Semantics module (TaskFrame, WorldHistory, TaskModel, Truth, Validity)

**Porting Checklist (apply to every file in this PR)**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Temporal
- [ ] Add module declaration at top: namespace Cslib.Logics.Temporal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)

---

### 2. Port Temporal Syntax (PR 1)
- **Effort**: Large (8-12 hours)
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Dependencies**: none (first PR in the chain)
- **External Dependencies**: BimodalLogic task 291 (toolchain upgrade must complete first)

**Description**: Port Temporal Syntax (PR 1): Atom, Formula, Context, BigConj, Subformulas to Cslib/Logics/Temporal/Syntax/. This is the foundational PR -- all subsequent PRs depend on it.

**Source files** (from BimodalLogic Theories/Bimodal/Syntax/):
- Atom.lean (~300 lines): PropAtom type, decidable equality, atom manipulation
- Formula.lean (~800 lines): Formula inductive type, complexity, connectives, derived operators
- Context.lean (~400 lines): proof context (list of formulas), context operations
- BigConj.lean (~500 lines): finite conjunction folding, BigConj properties
- Subformulas.lean (~500 lines): subformula closure, subformula lemmas

**Target path**: Cslib/Logics/Temporal/Syntax/

**Estimated scope**: ~2,500 lines across 5 files

**PR title**: feat(Logics/Temporal): add Syntax module (Atom, Formula, Context, BigConj, Subformulas)

**Porting Checklist (apply to every file in this PR)**:
- [ ] Rename namespace: Bimodal/Theories -> Cslib.Logics.Temporal
- [ ] Add module declaration at top: namespace Cslib.Logics.Temporal
- [ ] Replace import Mathlib.* with import Cslib.Init (and specific Mathlib)
- [ ] Add Apache 2.0 copyright header (see cslib CONTRIBUTING.md for format)
- [ ] Run lake shake to identify unused imports
- [ ] Run Mathlib linter: set_option linter.all true
- [ ] Verify lake build passes with zero errors
- [ ] Confirm zero sorry occurrences (grep -r sorry src/)

---

