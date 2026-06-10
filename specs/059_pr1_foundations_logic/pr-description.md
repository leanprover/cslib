# feat(Foundations/Logic): propositional theorems, modal S5 theorems, and MCS consistency foundations

**Base branch**: `main`

## Summary

Adds the `Cslib/Foundations/Logic/` module hierarchy and the `Cslib/Logics/Propositional/` proof system: 25 files, 5,120 lines total. This provides the Hilbert-style proof system infrastructure and concrete propositional logic that all downstream PRs (modal metalogic, temporal semantics, temporal metalogic, bimodal completeness) depend on.

The contribution includes:
- **Core definitions** (5 files, `Foundations/Logic/`): `InferenceSystem` typeclass, `HasBot`/`HasImp` connective classes, polymorphic axiom `abbrev`s, bundled proof system typeclasses (`PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`), and `LogicalEquivalence`
- **Theorem libraries** (9 files, `Foundations/Logic/Theorems/`): SKI/BCC combinators, propositional core (LEM, DNE, RAA), derived connective theorems (De Morgan, contraposition, iff), big conjunction, K-level modal theorems, S5-level modal theorems, temporal derived theorems, and frame conditions
- **Metalogic foundations** (2 files, `Foundations/Logic/Metalogic/`): `DerivationSystem` typeclass with Lindenbaum's lemma via Zorn's lemma, maximal consistent set (MCS) construction; `HasHilbertTree` typeclass with generic deduction theorem helpers
- **Propositional logic** (8 files, `Logics/Propositional/`): Concrete `Proposition` inductive type with `{atom, bot, imp}` primitives, Hilbert-style derivation trees, propositional axiom schemas, `InferenceSystem`/`PropositionalHilbert` instance registration, deduction theorem, MCS instantiation, and natural deduction wrappers
- **Shared utilities** (1 file, `Foundations/Data/`): `ListHelpers` with `removeAll` and supporting lemmas used by deduction theorem files across all logic domains

## Design: Primitive Connective Choice

The connective hierarchy takes `bot` (falsum, `HasBot`) and `imp` (implication, `HasImp`) as the two primitive connectives. Negation, disjunction, conjunction, and biconditional are all derived via the classical Lukasiewicz encoding:

```
neg phi     := imp phi bot            -- "phi implies contradiction"
top         := imp bot bot            -- trivially provable
disj phi psi := imp (imp phi bot) psi  -- "if phi is false, then psi"
conj phi psi := imp (imp phi (imp psi bot)) bot  -- "phi -> not-psi is refuted"
```

This choice is grounded in six considerations:

### 1. Historical basis (Church 1956, Tarski-Bernays-Wajsberg)

The `{bot, imp}` primitive basis has a long and authoritative history in formal logic. Church's *Introduction to Mathematical Logic* (1956) presents classical propositional logic with implication and falsum as primitives. The Tarski-Bernays-Wajsberg system uses the same basis with four axiom schemas including EFQ and Peirce's law. Gentzen (1935) defines intuitionistic logic with `neg A := A -> bot` as the standard abbreviation. This is not a novel encoding -- it is the textbook approach.

### 2. Clean classical/intuitionistic separation via single Peirce axiom

The classical/intuitionistic boundary is drawn by a single axiom schema:

| System | Axioms | Typeclass |
|--------|--------|-----------|
| Minimal logic | `{ImplyK, ImplyS}` | (subsumed) |
| Intuitionistic logic | `{ImplyK, ImplyS, EFQ}` | (subsumed) |
| Classical logic | `{ImplyK, ImplyS, EFQ, Peirce}` | `PropositionalHilbert` |

Adding `Peirce` (or equivalently `DNE`) is the only difference between intuitionistic and classical. This separation is documented in `Axioms.lean` and realized in `ProofSystem.lean`.

### 3. Curry-Howard alignment

The primitive basis `{bot, imp}` aligns naturally with Lean 4's type theory:

| Logic | Type Theory |
|-------|-------------|
| `phi -> psi` (implication) | `phi -> psi` (function type) |
| `bot` (falsum) | `Empty` (uninhabited type) |
| `neg phi = phi -> bot` | `phi -> Empty` (refutation) |
| modus ponens | function application |
| `ImplyK` | K combinator |
| `ImplyS` | S combinator |

The K and S axiom schemas correspond directly to the K and S combinators, as realized in `Theorems/Combinators.lean` (338 lines of combinator infrastructure).

### 4. Polymorphic `abbrev` design avoiding typeclass diamonds

All axiom schemas are defined once as polymorphic `abbrev`s over `[HasBot F] [HasImp F]` and are instantiated at any formula type (propositional, modal, temporal, bimodal) via typeclass resolution. Derived connectives (negation, conjunction, disjunction) are `abbrev`s rather than typeclass instances, eliminating the `HasNeg`/`HasAnd`/`HasOr` classes that would create resolution overhead and potential diamond conflicts in the multi-modal hierarchy. The `BimodalConnectives` class extends `ModalConnectives` and adds `HasUntil`/`HasSince` directly rather than extending `TemporalConnectives`, to avoid a typeclass diamond.

### 5. Lukasiewicz-derived connectives get definitional equality

Because negation, conjunction, and disjunction are `abbrev`s over `{bot, imp}`, Lean's kernel handles all coercions via definitional equality. No explicit rewrite lemmas are needed to convert between `neg phi` and `imp phi bot`. This eliminates an entire class of proof obligations that would arise with separate primitive connectives.

### 6. MCS foundations parameterized over minimal `{bot, imp}` interface

The `Metalogic/Consistency.lean` module provides a logic-agnostic framework for maximal consistent sets. Lindenbaum's lemma is proved via Zorn's lemma, parameterized over `DerivationSystem F` for any formula type with `[HasBot F] [HasImp F]`. Consistency is defined as non-derivability of `bot`. This module is included in this PR because it is imported by both the modal and temporal metalogic files (PRs 2-4).

## Design: Hilbert Primitive, Natural Deduction Derived

The metalogic is built on Hilbert-style derivation trees, following the standard approach for canonical model completeness proofs. The MCS/Lindenbaum construction needs derivability as a flat relation closed under modus ponens, which Hilbert systems provide directly. This also extends modularly to modal, temporal, and bimodal logics by adding axiom schemas — each corresponding to a frame condition — without changing the proof structure or metatheory.

The pre-existing independent natural deduction system (`NaturalDeduction/Basic.lean`, from PR #91) is preserved. A new `FromHilbert.lean` module provides ND-flavored convenience names (`impI`, `impE`, `botE`) as thin wrappers over the Hilbert derivation tree.

## Design: Propositional Proof System Architecture

The `Logics/Propositional/` module provides the concrete instantiation of the abstract `Foundations/Logic/` infrastructure for classical propositional logic.

### Proposition type

The `Proposition` inductive has three constructors: `atom`, `bot`, and `imp`. All other connectives are derived `abbrev`s following the Lukasiewicz encoding from the Foundations layer. The type registers as a `PropositionalConnectives` instance, gaining the full notation suite (`⊥ ⊤ ∧ ∨ → ¬`).

### Derivation trees

`DerivationTree Γ φ` is a concrete inductive proof witness with four constructors: `ax` (axiom schema), `assumption` (context membership), `modus_ponens`, and `weakening`. The `Deriv Γ φ := Nonempty (DerivationTree Γ φ)` wrapper provides a `Prop`-level interface.

### Instance registration

`ProofSystem/Instances.lean` registers `InferenceSystem`, `ModusPonens`, and all `HasAxiom*` instances for `Propositional.HilbertCl`, connecting the abstract typeclass hierarchy to the concrete derivation tree. This enables all generic theorems from `Foundations/Logic/Theorems/` to apply to propositional logic via typeclass resolution.

### Deduction theorem and MCS

`Metalogic/DeductionTheorem.lean` proves the deduction theorem for propositional derivation trees by structural induction on derivation height. `Metalogic/MCS.lean` instantiates the generic `DerivationSystem` framework from `Foundations/Logic/Metalogic/Consistency.lean` for propositional logic, providing maximal consistent set construction.

### Natural deduction interface

Two complementary modules provide ND-style reasoning:
- `NaturalDeduction/Basic.lean`: Standalone natural deduction system with its own inductive type
- `NaturalDeduction/FromHilbert.lean`: ND-flavored wrappers (`impI`, `impE`, `botE`, cut, weakening, substitution) over the Hilbert derivation tree

## File Inventory

### Foundations/Logic/ (16 files, 3,722 lines)

| File | Lines | Role |
|------|------:|------|
| `InferenceSystem.lean` | 68 | `InferenceSystem` typeclass + `DerivableIn` |
| `Connectives.lean` | 98 | Atomic classes `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`; bundled classes; `LukasiewiczDerived` |
| `Axioms.lean` | 298 | Polymorphic axiom `abbrev`s: `ImplyK`, `ImplyS`, `EFQ`, `Peirce`, `DNE`, all modal/temporal axioms; shared `top'`/`neg'`/`conj'`/`disj'` abbreviations |
| `ProofSystem.lean` | 353 | `ModusPonens`, `Necessitation`, `HasAxiom*` typeclasses; bundled `PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert` |
| `LogicalEquivalence.lean` | 35 | `LogicalEquivalence` typeclass for context-based congruence |
| `Theorems/Combinators.lean` | 339 | I, B, C combinators; `imp_trans`, `pairing`, `dni`, `combine_imp_conj`; `flip`, `app1`, `app2` |
| `Theorems/Propositional/Core.lean` | 289 | LEM, DNE, RAA, `efq_neg`, `rcp`, `lce_imp`, `rce_imp` |
| `Theorems/Propositional/Connectives.lean` | 536 | `classical_merge`, `iff_intro`, `contrapose_imp`, De Morgan laws |
| `Theorems/BigConj.lean` | 142 | `BigConj` syntax and derivability lemmas |
| `Theorems/Modal/Basic.lean` | 203 | K-level: `box_mono`, `diamond_mono`, `k_dist_diamond`, modal duality |
| `Theorems/Modal/S5.lean` | 533 | S5-level: Axiom 5 derivation, collapse theorems; abbreviation refactoring reduced duplicated `abbrev`s |
| `Theorems/Temporal/TemporalDerived.lean` | 292 | Temporal operator lemmas |
| `Theorems/Temporal/FrameConditions.lean` | 90 | Frame condition marker typeclasses |
| `Metalogic/Consistency.lean` | 278 | `DerivationSystem`, Lindenbaum's lemma, MCS foundations |
| `Metalogic/DeductionHelpers.lean` | 120 | `HasHilbertTree` typeclass; `deductionAxiom`, `deductionImpSelf`, `deductionAssumptionOther`, `deductionMpUnderImp` generic helpers |
| `Theorems.lean` | 48 | Barrel aggregator (with Propositional, Modal, and Temporal subsection docs) |

### Logics/Propositional/ (8 files, 1,327 lines)

| File | Lines | Role |
|------|------:|------|
| `Defs.lean` | 162 | `Proposition` inductive (`atom`/`bot`/`imp`), derived connectives, `Theory`, `IsIntuitionistic`/`IsClassical`, substitution monad |
| `ProofSystem/Axioms.lean` | 55 | `PropositionalAxiom` inductive: `implyK`, `implyS`, `efq`, `peirce` |
| `ProofSystem/Derivation.lean` | 147 | `DerivationTree` inductive proof witness, `Deriv` `Prop`-wrapper, height function |
| `ProofSystem/Instances.lean` | 90 | `InferenceSystem`, `ModusPonens`, `HasAxiom*`, `PropositionalHilbert` instance registration |
| `Metalogic/DeductionTheorem.lean` | 180 | Deduction theorem by structural induction on derivation height |
| `Metalogic/MCS.lean` | 129 | `DerivationSystem` instantiation for propositional logic, MCS construction |
| `NaturalDeduction/Basic.lean` | 345 | Standalone natural deduction system |
| `NaturalDeduction/FromHilbert.lean` | 219 | ND wrappers over Hilbert: `impI`/`impE`/`botE`, cut, weakening, substitution |

### Foundations/Data/ (1 file, 71 lines)

| File | Lines | Role |
|------|------:|------|
| `ListHelpers.lean` | 71 | `removeAll` definition and supporting lemmas for deduction theorem files |

### Total: 25 files, 5,120 lines

## Dependency Graph

```
InferenceSystem
    +-- Connectives
        +-- Axioms
            +-- ProofSystem
                +-- Theorems/Combinators
                    |-- Theorems/Propositional/Core
                    |   |-- Theorems/Propositional/Connectives
                    |   |-- Theorems/Modal/Basic
                    |   |   +-- Theorems/Modal/S5
                    |   +-- Theorems/Temporal/TemporalDerived
                    |       +-- Theorems/Temporal/FrameConditions
                    +-- Theorems/BigConj
Metalogic/Consistency        (imports Connectives only; no ProofSystem dependency)
Metalogic/DeductionHelpers   (imports Connectives only; imported by all DeductionTheorem files)
LogicalEquivalence           (imports InferenceSystem only)
Theorems.lean                (barrel import of all Theorems/* submodules)

Foundations/Data/ListHelpers  (imports Cslib.Init only)

Logics/Propositional/Defs                      (imports Connectives)
    +-- ProofSystem/Axioms                     (imports Defs)
        +-- ProofSystem/Derivation             (imports Axioms + Metalogic/Consistency)
            +-- ProofSystem/Instances          (imports Derivation + ProofSystem)
    +-- Metalogic/DeductionTheorem             (imports Derivation + ListHelpers + DeductionHelpers)
        +-- Metalogic/MCS                      (imports DeductionTheorem)
        +-- NaturalDeduction/FromHilbert       (imports DeductionTheorem)
    +-- NaturalDeduction/Basic                 (imports Defs)
```

## Embedding Relocation

The propositional embedding infrastructure was relocated to establish a clean import hierarchy:

- **Task 72**: `Propositional/Embedding.lean` merged into `Bimodal/Embedding/PropositionalEmbedding.lean`. This fixed a dependency inversion where `Propositional/` imported from `Bimodal/`. After the move, `Propositional/` imports only from `Foundations/`.
- **Task 73**: Created `Modal/FromPropositional.lean` and `Temporal/FromPropositional.lean` with PL embedding functions, establishing Propositional as a shared sub-logic for both Modal and Temporal.

The resulting import hierarchy is:

```
Foundations/Logic/  (primitive connectives, axioms, proof systems)
    +-- Propositional/  (propositional theorems, PL definitions)
        +-- Modal/  (modal theorems, FromPropositional embedding)
        +-- Temporal/  (temporal theorems, FromPropositional embedding)
            +-- Bimodal/  (combined system, PropositionalEmbedding)
```

These files are outside `Foundations/Logic/` scope but establish the dependency structure that the theorem files rely on.

## Module Keyword Migration (Task 68)

All files now use the Lean 4 `module` keyword:
- Each file begins with `module` after the copyright header
- All imports converted to `public import` for transitive visibility
- All files wrapped in `@[expose] public section` for downstream accessibility
- All files registered in `Cslib.lean` with `public import`

This was required for Lean 4 module system compliance and ensures that the files compose correctly with the rest of the library.

## Verification

- `lake build` for all modules exits 0
- `grep -rn "sorry"` across all 25 files returns zero hits
- All 25 files have correct Apache 2.0 headers
- All 25 files use the `module` keyword and are registered in `Cslib.lean`
- CI validation suite passed: `lake test`, `lake shake`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake exe mk_all --module`

## Known Issues

- **Public imports**: `public import Cslib.Init` remains in `Connectives.lean`, `InferenceSystem.lean`, and `FrameConditions.lean`. Downgrading to non-public breaks the transitive import chain for downstream theorem files.

## References

- Blackburn, P., de Rijke, M. and Venema, Y. (2001). *Modal Logic*. Cambridge University Press.
- Chellas, B.F. (1980). *Modal Logic: An Introduction*. Cambridge University Press.
- Church, A. (1956). *Introduction to Mathematical Logic, Vol. I*. Princeton University Press.
- Curry, H.B. and Feys, R. (1958). *Combinatory Logic, Vol. I*. North-Holland.
- Griffin, T.G. (1990). "A Formulae-as-Types Notion of Control". *POPL 1990*.
- Howard, W.A. (1969/1980). "The Formulae-as-Types Notion of Construction".
