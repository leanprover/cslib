# feat(Foundations/Logic): propositional theorems, modal S5 theorems, and MCS consistency foundations

**Base branch**: `main`

## Summary

Adds the `Cslib/Foundations/Logic/` module hierarchy: 15 files, 3,621 lines total. This provides the Hilbert-style proof system infrastructure that all downstream PRs (modal metalogic, temporal semantics, temporal metalogic, bimodal completeness) depend on.

The contribution includes:
- **Core definitions** (5 files): `InferenceSystem` typeclass, `HasBot`/`HasImp` connective classes, polymorphic axiom `abbrev`s, bundled proof system typeclasses (`PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`), and `LogicalEquivalence`
- **Theorem libraries** (9 files): SKI/BCC combinators, propositional core (LEM, DNE, RAA), derived connective theorems (De Morgan, contraposition, iff), big conjunction, K-level modal theorems, S5-level modal theorems, temporal derived theorems, and frame conditions
- **Metalogic foundations** (1 file): `DerivationSystem` typeclass with Lindenbaum's lemma via Zorn's lemma, maximal consistent set (MCS) construction

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

The K and S axiom schemas correspond directly to the K and S combinators, as realized in `Theorems/Combinators.lean` (330 lines of combinator infrastructure).

### 4. Polymorphic `abbrev` design avoiding typeclass diamonds

All axiom schemas are defined once as polymorphic `abbrev`s over `[HasBot F] [HasImp F]` and are instantiated at any formula type (propositional, modal, temporal, bimodal) via typeclass resolution. Derived connectives (negation, conjunction, disjunction) are `abbrev`s rather than typeclass instances, eliminating the `HasNeg`/`HasAnd`/`HasOr` classes that would create resolution overhead and potential diamond conflicts in the multi-modal hierarchy. The `BimodalConnectives` class extends `ModalConnectives` and adds `HasUntil`/`HasSince` directly rather than extending `TemporalConnectives`, to avoid a typeclass diamond.

### 5. Lukasiewicz-derived connectives get definitional equality

Because negation, conjunction, and disjunction are `abbrev`s over `{bot, imp}`, Lean's kernel handles all coercions via definitional equality. No explicit rewrite lemmas are needed to convert between `neg phi` and `imp phi bot`. This eliminates an entire class of proof obligations that would arise with separate primitive connectives.

### 6. MCS foundations parameterized over minimal `{bot, imp}` interface

The `Metalogic/Consistency.lean` module provides a logic-agnostic framework for maximal consistent sets. Lindenbaum's lemma is proved via Zorn's lemma, parameterized over `DerivationSystem F` for any formula type with `[HasBot F] [HasImp F]`. Consistency is defined as non-derivability of `bot`. This module is included in this PR because it is imported by both the modal and temporal metalogic files (PRs 2-4).

## File Inventory

| File | Lines | Role |
|------|------:|------|
| `InferenceSystem.lean` | 68 | `InferenceSystem` typeclass + `DerivableIn` |
| `Connectives.lean` | 98 | Atomic classes `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`; bundled classes; `LukasiewiczDerived` |
| `Axioms.lean` | 322 | Polymorphic axiom `abbrev`s: `ImplyK`, `ImplyS`, `EFQ`, `Peirce`, `DNE`, all modal/temporal axioms |
| `ProofSystem.lean` | 354 | `ModusPonens`, `Necessitation`, `HasAxiom*` typeclasses; bundled `PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert` |
| `LogicalEquivalence.lean` | 35 | `LogicalEquivalence` typeclass for context-based congruence |
| `Theorems/Combinators.lean` | 330 | I, B, C combinators; `imp_trans`, `pairing`, `dni`, `combine_imp_conj` |
| `Theorems/Propositional/Core.lean` | 285 | LEM, DNE, RAA, `efq_neg`, `rcp`, `lce_imp`, `rce_imp` |
| `Theorems/Propositional/Connectives.lean` | 545 | `classical_merge`, `iff_intro`, `contrapose_imp`, De Morgan laws |
| `Theorems/BigConj.lean` | 136 | `BigConj` syntax and derivability lemmas |
| `Theorems/Modal/Basic.lean` | 200 | K-level: `box_mono`, `diamond_mono`, `k_dist_diamond`, modal duality |
| `Theorems/Modal/S5.lean` | 585 | S5-level: Axiom 5 derivation, collapse theorems |
| `Theorems/Temporal/TemporalDerived.lean` | 270 | Temporal operator lemmas |
| `Theorems/Temporal/FrameConditions.lean` | 84 | Frame condition marker typeclasses |
| `Metalogic/Consistency.lean` | 273 | `DerivationSystem`, Lindenbaum's lemma, MCS foundations |
| `Theorems.lean` | 36 | Barrel aggregator |
| **Total** | **3,621** | |

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
Metalogic/Consistency  (imports Connectives only; no ProofSystem dependency)
LogicalEquivalence     (imports InferenceSystem only)
Theorems.lean          (barrel import of all Theorems/* submodules)
```

## Verification

- `lake build` exits 0 (2,906 jobs, zero errors)
- `grep -rn "sorry" Cslib/Foundations/Logic/` returns zero hits
- All 15 files have correct Apache 2.0 headers
- `lake shake` identifies unused imports in 5 core module files (cosmetic; can be addressed in follow-up)

## Known Issues

- **Unused imports**: `lake shake` flags unused `public import Cslib.Init` in Connectives, Axioms, InferenceSystem, and ProofSystem. These are harmless re-exports but could be cleaned up.
- **Linter warnings**: `BigConj.lean` has flexible `simp` tactic warnings (could use `simp only`). `Connectives.lean` has empty-line-in-command style warnings. These are non-blocking.
- **Module registration**: Only the 5 core definition files (InferenceSystem, Connectives, Axioms, ProofSystem, LogicalEquivalence) are registered in `Cslib.lean` as `public import` lines. The 10 theorem and metalogic files are non-`module` files and cannot be imported from the `module` root file. They are imported directly by consumers. Future migration to `module` declarations for all files would enable full registration.

## References

- Church, A. (1956). *Introduction to Mathematical Logic, Vol. I*. Princeton University Press.
- Gentzen, G. (1935). "Untersuchungen uber das logische Schliessen". *Mathematische Zeitschrift* 39.
- Curry, H.B. and Feys, R. (1958). *Combinatory Logic, Vol. I*. North-Holland.
- Howard, W.A. (1969/1980). "The Formulae-as-Types Notion of Construction".
- Griffin, T.G. (1990). "A Formulae-as-Types Notion of Control". *POPL 1990*.
