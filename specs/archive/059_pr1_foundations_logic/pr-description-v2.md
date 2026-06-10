# feat(Foundations/Logic): propositional theorems, modal S5 theorems, and MCS consistency foundations

## Summary

Adds the `Cslib/Foundations/Logic/` module hierarchy and the `Cslib/Logics/Propositional/` proof system: 25 files, ~5,100 lines. This provides the Hilbert-style proof system infrastructure and concrete propositional logic that all downstream PRs (modal metalogic, temporal semantics, temporal metalogic, bimodal completeness) depend on.

- **Core definitions** (`Foundations/Logic/`): `InferenceSystem` typeclass, `HasBot`/`HasImp` connective classes, polymorphic axiom `abbrev`s, bundled proof system typeclasses (`PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`), and `LogicalEquivalence`
- **Theorem libraries** (`Foundations/Logic/Theorems/`): SKI/BCC combinators, propositional core (LEM, DNE, RAA), derived connective theorems (De Morgan, contraposition, iff), big conjunction, K-level modal theorems, S5-level theorems, temporal derived theorems, and frame conditions
- **Metalogic foundations** (`Foundations/Logic/Metalogic/`): `DerivationSystem` typeclass with Lindenbaum's lemma via Zorn's lemma, MCS construction; generic deduction theorem helpers
- **Propositional logic** (`Logics/Propositional/`): Concrete `Proposition` inductive with `{atom, bot, imp}` primitives, Hilbert-style derivation trees, axiom schemas, instance registration, deduction theorem, MCS instantiation, and natural deduction wrappers
- **Shared utilities** (`Foundations/Data/`): `ListHelpers` with `removeAll` and supporting lemmas used by deduction theorem files

## Design

### Primitive connectives

The connective hierarchy takes `bot` and `imp` as primitives, following Church (1956) and the Tarski-Bernays-Wajsberg system. All other connectives are derived via the Lukasiewicz encoding (`neg φ := imp φ bot`, etc.) and defined as `abbrev`s, so Lean handles conversions by definitional equality. Axiom schemas are polymorphic `abbrev`s over `[HasBot F] [HasImp F]`, instantiated at any formula type via typeclass resolution. The classical/intuitionistic boundary is drawn by a single axiom: adding Peirce's law to `{ImplyK, ImplyS, EFQ}`.

### Hilbert system

The metalogic is built on Hilbert-style derivation trees, following the standard approach for canonical model completeness proofs. The MCS/Lindenbaum construction needs derivability as a flat relation closed under modus ponens, which Hilbert systems provide directly. This extends modularly to modal, temporal, and bimodal logics by adding axiom schemas — each corresponding to a frame condition — without changing the proof structure or metatheory.

The pre-existing independent natural deduction system (`NaturalDeduction/Basic.lean`, from PR #91) is preserved. A new `FromHilbert.lean` module provides ND-flavored convenience names (`impI`, `impE`, `botE`) as thin wrappers over the Hilbert derivation tree.

### Import hierarchy

All files use the Lean 4 `module` keyword with `public import` for transitive visibility.

```
Foundations/Logic/  →  Propositional/  →  Modal/
                                       →  Temporal/  →  Bimodal/
```

## File Inventory

### Foundations/Logic/ (16 files)

| File | Role |
|------|------|
| `InferenceSystem.lean` | `InferenceSystem` typeclass + `DerivableIn` |
| `Connectives.lean` | `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`; bundled connective classes |
| `Axioms.lean` | Polymorphic axiom `abbrev`s: `ImplyK`, `ImplyS`, `EFQ`, `Peirce`, `DNE`, modal/temporal axioms |
| `ProofSystem.lean` | `ModusPonens`, `Necessitation`, `HasAxiom*`; bundled `PropositionalHilbert` through `BimodalTMHilbert` |
| `LogicalEquivalence.lean` | `LogicalEquivalence` typeclass |
| `Theorems/Combinators.lean` | I, B, C combinators; `imp_trans`, `pairing`, `dni`, `flip` |
| `Theorems/Propositional/Core.lean` | LEM, DNE, RAA, `efq_neg`, `rcp` |
| `Theorems/Propositional/Connectives.lean` | `iff_intro`, `contrapose_imp`, De Morgan laws |
| `Theorems/BigConj.lean` | `BigConj` syntax and derivability lemmas |
| `Theorems/Modal/Basic.lean` | K-level: `box_mono`, `diamond_mono`, modal duality |
| `Theorems/Modal/S5.lean` | Axiom 5 derivation, collapse theorems |
| `Theorems/Temporal/TemporalDerived.lean` | Temporal operator lemmas |
| `Theorems/Temporal/FrameConditions.lean` | Frame condition marker typeclasses |
| `Metalogic/Consistency.lean` | `DerivationSystem`, Lindenbaum's lemma, MCS foundations |
| `Metalogic/DeductionHelpers.lean` | `HasHilbertTree` typeclass; generic deduction theorem helpers |
| `Theorems.lean` | Barrel aggregator |

### Logics/Propositional/ (8 files)

| File | Role |
|------|------|
| `Defs.lean` | `Proposition` inductive, derived connectives, `Theory`, `IsIntuitionistic`/`IsClassical` |
| `ProofSystem/Axioms.lean` | `PropositionalAxiom` inductive: `implyK`, `implyS`, `efq`, `peirce` |
| `ProofSystem/Derivation.lean` | `DerivationTree` proof witness, `Deriv` wrapper, height function |
| `ProofSystem/Instances.lean` | `InferenceSystem`/`PropositionalHilbert` instance registration |
| `Metalogic/DeductionTheorem.lean` | Deduction theorem by induction on derivation height |
| `Metalogic/MCS.lean` | `DerivationSystem` instantiation, MCS construction |
| `NaturalDeduction/Basic.lean` | Independent sequent-style ND system (from PR #91) |
| `NaturalDeduction/FromHilbert.lean` | ND wrappers over Hilbert: `impI`/`impE`/`botE`, cut, weakening, substitution |

### Foundations/Data/ (1 file)

| File | Role |
|------|------|
| `ListHelpers.lean` | `removeAll` and supporting lemmas for deduction theorem files |

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
Metalogic/Consistency        (imports Connectives only)
Metalogic/DeductionHelpers   (imports Connectives only)

Logics/Propositional/Defs                      (imports Connectives)
    +-- ProofSystem/Axioms
        +-- ProofSystem/Derivation             (+ Metalogic/Consistency)
            +-- ProofSystem/Instances          (+ ProofSystem)
    +-- Metalogic/DeductionTheorem             (+ Derivation, ListHelpers, DeductionHelpers)
        +-- Metalogic/MCS
        +-- NaturalDeduction/FromHilbert
    +-- NaturalDeduction/Basic                 (independent)
```

## Verification

- `lake build`: 0 errors
- `lake test`: pass
- `lake lint`: 0 errors
- `lake exe lint-style`: pass
- `lake exe checkInitImports`: pass
- `lake exe mk_all --module --check`: no update necessary
- `lake shake --add-public --keep-implied --keep-prefix`: no issues in contributed files
- `grep -rn "sorry"`: 0 hits across all 25 files

## References

- Blackburn, P., de Rijke, M. and Venema, Y. (2001). *Modal Logic*. Cambridge University Press.
- Chellas, B.F. (1980). *Modal Logic: An Introduction*. Cambridge University Press.
- Church, A. (1956). *Introduction to Mathematical Logic, Vol. I*. Princeton University Press.
- Curry, H.B. and Feys, R. (1958). *Combinatory Logic, Vol. I*. North-Holland.
- Griffin, T.G. (1990). "A Formulae-as-Types Notion of Control". *POPL 1990*.
- Howard, W.A. (1969/1980). "The Formulae-as-Types Notion of Construction".
