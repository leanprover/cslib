---
next_project_number: 14
---

# Tasks

## Tasks

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

### 1. Integrate BimodalLogic results into cslib
- **Effort**: Large
- **Status**: [IMPLEMENTING]
- **Task Type**: lean4
- **Plan**: [001_integrate_bimodal_logic_results/plans/01_integration-plan.md]

**Description**: Integrate the results from /home/benjamin/Projects/BimodalLogic/ into the appropriate places in this repo which was forked to submit as PRs. Review both repos and create a plan to do so. The aim is to integrate elements in a modular and standalone way when possible
