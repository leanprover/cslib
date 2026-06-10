# Implementation Summary: ND-Hilbert Extensional Equivalence

- **Task**: 87 - Derive natural deduction from Hilbert system or prove extensional equivalence
- **Status**: Implemented
- **Duration**: ~30 minutes
- **Plan**: specs/087_derive_nd_from_hilbert/plans/01_nd-hilbert-equivalence.md

## What Was Implemented

Created `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` proving the extensional equivalence between the Hilbert-style proof system (`DerivationTree`, `Deriv`, `Derivable`) and the standalone natural deduction system (`Theory.Derivation`, `DerivableIn`).

### Key Definitions

| Definition | Type | Purpose |
|-----------|------|---------|
| `HilbertAxiomTheory` | `Theory Atom` | ND theory wrapping all Hilbert axiom schemata |
| `mem_hilbertAxiomTheory` | `@[simp]` theorem | Membership iff `PropositionalAxiom` |
| `finset_insert_toList_mem_cons` | theorem | Bridge: `(insert A Gamma).toList` to `A :: Gamma.toList` |
| `list_cons_mem_finset_insert_toList` | theorem | Bridge: `A :: Gamma.toList` to `(insert A Gamma).toList` |
| `hilbertToND` | `def` | Structural translation Hilbert -> ND |
| `hilbert_to_nd_deriv` | theorem | Prop-level wrapper for Hilbert -> ND |
| `ndToHilbert` | `noncomputable def` | Structural translation ND -> Hilbert |
| `nd_to_hilbert_deriv` | theorem | Prop-level wrapper for ND -> Hilbert |
| `hilbert_iff_nd` | theorem | Extensional equivalence for closed derivability |

### Translation Details

**Hilbert to ND** (`hilbertToND`): Computable, maps each Hilbert constructor directly:
- `ax` -> `Theory.Derivation.ax` via `mem_hilbertAxiomTheory`
- `assumption` -> `Theory.Derivation.ass` via `List.mem_toFinset`
- `modus_ponens` -> `Theory.Derivation.impE`
- `weakening` -> `Theory.Derivation.weakCtx`

**ND to Hilbert** (`ndToHilbert`): Noncomputable (inherits from `deductionTheorem`), handles:
- `ax` -> `DerivationTree.ax` via `mem_hilbertAxiomTheory`
- `ass` -> `DerivationTree.assumption` via `Finset.mem_toList`
- `impE` -> `DerivationTree.modus_ponens`
- `botE` -> `PL.botE` (EFQ axiom + modus ponens)
- `impI` -> `deductionTheorem` after weakening via bridge lemma (key case)

## Plan Deviations

- **Task 1.1**: Altered -- also imports `FromHilbert` for the `botE` combinator, in addition to `Basic` and `DeductionTheorem`
- **Task 1.3/1.4**: Altered -- combined two separate membership lemmas into a single iff (`mem_hilbertAxiomTheory`)
- **Task 3.5**: Altered -- used existing `PL.botE` from `FromHilbert.lean` instead of inlining the EFQ axiom + modus ponens construction
- **Task 4.2**: Altered -- `Finset.toList` is noncomputable so `(empty).toList = []` is not definitionally true; used membership-based weakening with vacuous proof (`simp [Finset.mem_toList]`) instead

## Verification

- `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` -- passes
- `lake build` (full project) -- passes (2913 jobs, no new warnings)
- `lean_verify` on all 5 key declarations -- only standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
- Zero sorries, zero vacuous definitions, zero new axioms

## Files Changed

- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` -- NEW (162 lines)
