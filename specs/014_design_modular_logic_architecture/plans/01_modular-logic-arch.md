# Implementation Plan: Task #14

- **Task**: 14 - Design modular logic architecture for composable modal, temporal, and bimodal syntax and proof systems
- **Status**: [NOT STARTED]
- **Effort**: 18 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_team-research.md, reports/02_formula-composition.md, reports/02_proof-system-composition.md
- **Artifacts**: plans/01_modular-logic-arch.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

This plan implements a modular logic architecture in cslib for four composable logic levels: Propositional, Modal, Temporal, and Bimodal (TM). Each logic defines its own `Formula` inductive type with duplicated shared constructors (the established Lean 4 pattern from FormalizedFormalLogic/Foundation). Composition is achieved through a shared typeclass hierarchy for connectives, embedding functions with `Coe` instances, polymorphic axiom definitions, and typeclass-gated proof system classes. The existing cslib `Modal` and `Propositional` modules are refactored to align their primitives with BimodalLogic's convention (`{atom, bot, imp}` for propositional, `{atom, bot, imp, box}` for modal). The bimodal metalogic (soundness, completeness, decidability) remains monolithic because the interaction axiom MF prevents cross-logic decomposition. The plan is complete when all four formula types compile with typeclass instances, embedding functions are defined with `Coe`, and the proof system typeclass hierarchy is established.

### Research Integration

Three research reports inform this plan:

- **01_team-research.md**: Synthesized findings from 4 teammates confirming separate formula types per logic, shared typeclass layer, cslib's `InferenceSystem` for proof system abstraction, and monolithic metalogic per logic. Resolved conflict: existing cslib `Modal` module uses `{atom, neg, and, diamond}` primitives that will be refactored to `{atom, bot, imp, box}`.
- **02_formula-composition.md**: Detailed Foundation pattern analysis -- three-layer architecture (atomic notation classes, bundled connective classes, concrete formula types). Provided concrete Lean 4 code for all four formula types, embedding functions, and notation patterns.
- **02_proof-system-composition.md**: Foundation pattern for proof system composition -- polymorphic axiom `abbrev`s, `HasAxiom*` typeclasses per axiom, bundled proof system classes (`PropositionalHilbert` -> `ModalS5Hilbert` / `TemporalBXHilbert` -> `BimodalTMHilbert`), separate `DerivationTree` per logic.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

ROADMAP.md exists but contains no specific items. This task establishes the foundational modular architecture that all future logic formalization tasks will build upon.

## Goals & Non-Goals

**Goals**:
- Define a connective typeclass hierarchy (`HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince` -> `PropositionalConnectives` -> `ModalConnectives` / `TemporalConnectives` -> `BimodalConnectives`)
- Refactor cslib's `PL.Proposition` from `{atom, and, or, impl}` to `{atom, bot, imp}` with `and`, `or`, `neg` as derived connectives
- Refactor cslib's `Modal.Proposition` from `{atom, neg, and, diamond}` to `{atom, bot, imp, box}` with `neg`, `and`, `or`, `diamond` as derived connectives
- Define new `Temporal.Formula` with `{atom, bot, imp, untl, snce}`
- Define new `Bimodal.Formula` with `{atom, bot, imp, box, untl, snce}`
- Register all formula types as instances of the appropriate connective typeclasses
- Define embedding functions (`Propositional -> Modal`, `Propositional -> Temporal`, `Modal -> Bimodal`, `Temporal -> Bimodal`) with `Coe` instances
- Define polymorphic axiom `abbrev`s and `HasAxiom*` typeclasses for the proof system hierarchy
- Define bundled proof system classes (`PropositionalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`)
- Verify all files compile with `lake build`

**Non-Goals**:
- Porting BimodalLogic's `DerivationTree`, `Axiom` inductive (42 constructors), or metalogic proofs -- that is future implementation work
- Providing concrete `InferenceSystem` instances for the new proof system tags -- requires `DerivationTree` types not yet ported
- Defining semantics (Kripke, linear order, task frame) for any logic level
- Proving conservative extension theorems or embedding injectivity -- these require derivation trees
- Porting BimodalLogic's automation, subformula closure, or `FrameClass` parameterization

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Refactoring Propositional breaks Natural Deduction module | H | H | Phase 2 dedicates time to updating `NaturalDeduction/Basic.lean` after formula refactor; the ND module uses `and`, `or`, `impl` rules that must be re-derived |
| Refactoring Modal breaks `grind`-based proofs in Cube.lean | M | H | Phase 3 rewrites all `Satisfies` and axiom proofs for the new primitives; module is ~140 lines total |
| Typeclass diamond in `BimodalConnectives extends ModalConnectives, HasUntil, HasSince` vs `TemporalConnectives` | M | L | `BimodalConnectives extends ModalConnectives, HasUntil, HasSince` avoids the diamond by not extending `TemporalConnectives` directly; test that Lean resolves instances without ambiguity |
| Compilation time increase from typeclass-heavy design | L | M | Keep typeclass hierarchy shallow (max depth 3); defer `instance` registration to individual formula modules |
| `expose`/`module` interaction with scoped typeclass instances | M | M | Test early in Phase 1; cslib uses `@[expose] public section` extensively; if issues arise, use namespace-scoped instances instead |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Connective Typeclass Hierarchy [NOT STARTED]

**Goal**: Define the shared typeclass infrastructure that all formula types will instantiate.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Connectives.lean` with atomic connective classes (`HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`)
- [ ] Define bundled connective classes: `PropositionalConnectives extends HasBot, HasImp`; `ModalConnectives extends PropositionalConnectives, HasBox`; `TemporalConnectives extends PropositionalConnectives, HasUntil, HasSince`; `BimodalConnectives extends ModalConnectives, HasUntil, HasSince`
- [ ] Define `LukasiewiczDerived` class for derived connectives (`neg`, `top`, `or`, `and`) from `bot`/`imp`
- [ ] Add the new file to the lakefile/import tree
- [ ] Verify compilation with `lake build Cslib.Foundations.Logic.Connectives`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` -- NEW: typeclass hierarchy
- `Cslib.lean` or root import -- add import for new module

**Verification**:
- `lake build Cslib.Foundations.Logic.Connectives` succeeds
- Typeclass instances for all connective classes can be manually tested with `#check` commands

---

### Phase 2: Refactor Propositional Formula and Natural Deduction [NOT STARTED]

**Goal**: Refactor `PL.Proposition` from `{atom, and, or, impl}` to `{atom, bot, imp}` and update the Natural Deduction module.

**Tasks**:
- [ ] Refactor `Cslib/Logics/Propositional/Defs.lean`: change `Proposition` inductive from `| atom | and | or | impl` to `| atom | bot | imp`
- [ ] Define derived connectives as `abbrev`: `neg` (already exists as `impl . bot`), `top` (as `imp bot bot`), `and`, `or`
- [ ] Remove the existing `Bot` instance via `[Bot Atom]` -- `bot` is now a constructor, not dependent on atom type
- [ ] Update `Theory`, `IPL`, `CPL`, `IsIntuitionistic`, `IsClassical` to use new primitives
- [ ] Register `PropositionalConnectives` instance for `Proposition Atom`
- [ ] Refactor `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`: update `Theory.Derivation` to have rules for `imp` intro/elim and `bot` (ex falso), with `and` and `or` rules re-expressed through derived connectives or added as derived rules
- [ ] Update all notation: `scoped infix:30 " -> " => Proposition.imp`, `scoped notation "bot" => Proposition.bot`, etc.
- [ ] Verify all proofs in `Defs.lean` and `NaturalDeduction/Basic.lean` compile

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` -- REFACTOR: change inductive definition and derived connectives
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- REFACTOR: update derivation rules and proofs

**Verification**:
- `lake build Cslib.Logics.Propositional.Defs` succeeds
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` succeeds
- `#check @Cslib.Logic.PL.Proposition.bot` resolves
- `#check (inferInstance : PropositionalConnectives (PL.Proposition Atom))` resolves

---

### Phase 3: Refactor Modal Formula, Satisfies, and Cube [NOT STARTED]

**Goal**: Refactor `Modal.Proposition` from `{atom, neg, and, diamond}` to `{atom, bot, imp, box}` and update all downstream files.

**Tasks**:
- [ ] Refactor `Cslib/Logics/Modal/Basic.lean`: change `Proposition` inductive from `| atom | neg | and | diamond` to `| atom | bot | imp | box`
- [ ] Define derived connectives as `abbrev`: `neg` (imp . bot), `top` (imp bot bot), `and`, `or`, `diamond` (neg (box (neg .))), `impl` (as alias for imp), `iff`
- [ ] Update `Satisfies` definition: add cases for `bot` and `imp` directly, derive `neg`, `and`, `or`, `diamond` satisfaction from the primitives
- [ ] Update all `@[scoped grind =]` characterization theorems (`neg_satisfies`, `or_iff_or`, `impl_iff_impl`, `box_iff_forall`) -- most become consequences of the primitive cases
- [ ] Register `ModalConnectives` instance for `Modal.Proposition Atom`
- [ ] Update `Cslib/Logics/Modal/Cube.lean`: re-prove all logic inclusions and validity theorems with new primitives
- [ ] Update `Cslib/Logics/Modal/Denotation.lean`: adapt denotation function to new constructors
- [ ] Update notation to use `box` as primitive prefix, `diamond` as derived

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- REFACTOR: change inductive, update Satisfies and proofs
- `Cslib/Logics/Modal/Cube.lean` -- REFACTOR: re-prove logic ordering and validity theorems
- `Cslib/Logics/Modal/Denotation.lean` -- REFACTOR: adapt to new constructors

**Verification**:
- `lake build Cslib.Logics.Modal.Basic` succeeds
- `lake build Cslib.Logics.Modal.Cube` succeeds
- `lake build Cslib.Logics.Modal.Denotation` succeeds
- `#check (inferInstance : ModalConnectives (Modal.Proposition Atom))` resolves

---

### Phase 4: New Temporal and Bimodal Formula Types [NOT STARTED]

**Goal**: Define standalone `Temporal.Formula` and `Bimodal.Formula` types with typeclass instances and derived connectives.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Syntax/Formula.lean` with `Temporal.Formula Atom` inductive: `| atom | bot | imp | untl | snce`, `deriving DecidableEq, BEq`
- [ ] Define derived connectives for Temporal: `neg`, `top`, `and`, `or`, `some_future`, `some_past`, `all_future`, `all_past`
- [ ] Register `TemporalConnectives` instance for `Temporal.Formula Atom`
- [ ] Create `Cslib/Logics/Bimodal/Syntax/Formula.lean` with `Bimodal.Formula Atom` inductive: `| atom | bot | imp | box | untl | snce`, `deriving DecidableEq, BEq`
- [ ] Define derived connectives for Bimodal: all of Modal's + all of Temporal's
- [ ] Register `BimodalConnectives` instance for `Bimodal.Formula Atom`
- [ ] Add scoped notation for temporal operators (`G`, `H`, `F`, `P`) and bimodal combined notation
- [ ] Add new modules to the lakefile/import tree
- [ ] Verify compilation of both new modules

**Timing**: 2 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` -- NEW: temporal formula type
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` -- NEW: bimodal formula type
- `Cslib.lean` or root import -- add imports for new modules

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax.Formula` succeeds
- `lake build Cslib.Logics.Bimodal.Syntax.Formula` succeeds
- `#check (inferInstance : TemporalConnectives (Temporal.Formula Atom))` resolves
- `#check (inferInstance : BimodalConnectives (Bimodal.Formula Atom))` resolves

---

### Phase 5: Embedding Functions and Coercions [NOT STARTED]

**Goal**: Define structural embedding functions between formula types and register `Coe` instances.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` with `Modal.Proposition.toBimodal : Modal.Proposition Atom -> Bimodal.Formula Atom` (structural recursion on 4 constructors)
- [ ] Create `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` with `Temporal.Formula.toBimodal : Temporal.Formula Atom -> Bimodal.Formula Atom` (structural recursion on 5 constructors)
- [ ] Define `Propositional.Proposition.toModal : PL.Proposition Atom -> Modal.Proposition Atom` and `Propositional.Proposition.toTemporal : PL.Proposition Atom -> Temporal.Formula Atom` in appropriate files
- [ ] Register `Coe` instances for all four embeddings
- [ ] Prove embedding preserves derived connectives (`toBimodal_neg`, `toBimodal_and`, etc.) -- basic `simp` lemmas
- [ ] Add new modules to import tree
- [ ] Verify compilation

**Timing**: 2 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` -- NEW: Modal -> Bimodal embedding
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` -- NEW: Temporal -> Bimodal embedding
- `Cslib/Logics/Propositional/Embedding.lean` -- NEW: Propositional -> Modal and Propositional -> Temporal embeddings

**Verification**:
- `lake build Cslib.Logics.Bimodal.Embedding.ModalEmbedding` succeeds
- `lake build Cslib.Logics.Bimodal.Embedding.TemporalEmbedding` succeeds
- `lake build Cslib.Logics.Propositional.Embedding` succeeds
- Coercions work: `#check (show Modal.Proposition Atom from default : Bimodal.Formula Atom)` resolves

---

### Phase 6: Proof System Typeclass Hierarchy [NOT STARTED]

**Goal**: Define polymorphic axiom formulas and the proof system typeclass hierarchy, establishing the foundation for future `InferenceSystem` instances.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Axioms.lean` with polymorphic axiom `abbrev`s parameterized over connective typeclasses: `ImplyK`, `ImplyS`, `EFQ`, `Peirce` (propositional); `AxiomK`, `AxiomT`, `Axiom4`, `AxiomB`, `Axiom5` (modal); temporal axioms (`SerialFuture`, `ConnectFuture`, etc.); `ModalFuture` (interaction, requires both `HasBox` and `HasUntil`)
- [ ] Create `Cslib/Foundations/Logic/ProofSystem.lean` with `HasAxiom*` typeclasses per axiom (e.g., `HasAxiomImplyK`, `HasAxiomK`, `HasAxiomT`, `HasAxiomMF`), `ModusPonens`, `Necessitation`, `TemporalNecessitation`, `TemporalDuality` rule typeclasses
- [ ] Define bundled proof system classes: `PropositionalHilbert extends ModusPonens, HasAxiomImplyK, HasAxiomImplyS, HasAxiomEFQ, HasAxiomPeirce`; `ModalHilbert extends PropositionalHilbert, Necessitation, HasAxiomK`; `ModalS5Hilbert extends ModalHilbert, HasAxiomT, HasAxiom4, HasAxiomB`; `TemporalBXHilbert extends PropositionalHilbert, TemporalNecessitation, TemporalDuality, ...`; `BimodalTMHilbert extends ModalS5Hilbert, TemporalBXHilbert, HasAxiomMF`
- [ ] Define opaque tag types: `Propositional.HilbertCl`, `Modal.HilbertK`, `Modal.HilbertS5`, `Temporal.HilbertBX`, `Bimodal.HilbertTM`
- [ ] Add new modules to import tree
- [ ] Verify full project compilation with `lake build`

**Timing**: 3 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Foundations/Logic/Axioms.lean` -- NEW: polymorphic axiom definitions
- `Cslib/Foundations/Logic/ProofSystem.lean` -- NEW: proof system typeclasses and bundled classes
- `Cslib.lean` or root import -- add imports

**Verification**:
- `lake build Cslib.Foundations.Logic.Axioms` succeeds
- `lake build Cslib.Foundations.Logic.ProofSystem` succeeds
- `lake build` (full project) succeeds
- `#check @Cslib.Logic.BimodalTMHilbert` resolves with correct `extends` chain

## Testing & Validation

- [ ] `lake build` succeeds with zero errors across the full project
- [ ] All existing tests pass (no regressions in HML, Linear Logic, or other unrelated modules)
- [ ] Each formula type derives `DecidableEq` and `BEq` successfully
- [ ] Typeclass resolution works: `inferInstance` succeeds for all connective class instances on all four formula types
- [ ] Embedding `Coe` instances work in both directions (upcasting via `Coe`, explicit function call)
- [ ] Derived connectives unfold correctly via `simp` on all formula types
- [ ] Scoped notation does not conflict across logic namespaces (open one at a time, verify no ambiguity)
- [ ] Proof system typeclass hierarchy resolves without diamonds or ambiguity

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Connectives.lean` -- connective typeclass hierarchy
- `Cslib/Foundations/Logic/Axioms.lean` -- polymorphic axiom definitions
- `Cslib/Foundations/Logic/ProofSystem.lean` -- proof system typeclasses
- `Cslib/Logics/Propositional/Defs.lean` -- refactored propositional formula
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- updated ND module
- `Cslib/Logics/Propositional/Embedding.lean` -- propositional embeddings
- `Cslib/Logics/Modal/Basic.lean` -- refactored modal formula and semantics
- `Cslib/Logics/Modal/Cube.lean` -- re-proved modal cube
- `Cslib/Logics/Modal/Denotation.lean` -- updated denotation
- `Cslib/Logics/Temporal/Syntax/Formula.lean` -- new temporal formula type
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` -- new bimodal formula type
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` -- modal to bimodal embedding
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` -- temporal to bimodal embedding

## Rollback/Contingency

The refactoring of Propositional and Modal formula types (Phases 2-3) is a committed design decision. There is no fallback to maintaining the old primitives alongside the new ones. If proofs break during refactoring, they must be fixed in place — the architectural unity of a shared `{atom, bot, imp}` propositional core across all four logic levels is a hard requirement. Each phase must compile before proceeding to the next.
