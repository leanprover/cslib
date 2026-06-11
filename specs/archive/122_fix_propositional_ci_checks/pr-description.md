# PR Title

feat(Foundations/Logic, Logics/Propositional): Hilbert proof systems, metalogic, ND equivalence, and Kripke semantics

# PR Body

## Summary

Adds reusable Hilbert-style proof system infrastructure (`Foundations/Logic/`) and a complete propositional logic development (`Logics/Propositional/`): 39 files, ~7,800 lines. The propositional logic includes soundness and completeness for classical, intuitionistic, and minimal systems, natural deduction equivalence, and Kripke semantics. The generic infrastructure is designed to extend modularly to modal, temporal, and bimodal logics in follow-up PRs.

This supersedes the closed PR #630, extending it with:
- **Kripke semantics** (`Semantics/`): Boolean and Kripke valuations with soundness and completeness for all three propositional systems
- **Metalogic for three systems**: soundness, Lindenbaum's lemma, and completeness for classical, intuitionistic (Kripke), and minimal (Kripke) logic
- **Axiom parameterization** (`IntMinInstances.lean`): proof system and ND equivalence parameterized over axiom predicates, enabling a single codebase to serve all three logics
- **CI compliance**: all `lake lint`, `lake shake`, `lake test`, and `lint-style` checks pass cleanly

### What's new vs PR #630

| Addition | Files |
|----------|-------|
| Kripke semantics (frames, models, forcing) | `Semantics/Basic.lean`, `Semantics/Kripke.lean` |
| Classical soundness and completeness | `Metalogic/Soundness.lean`, `Metalogic/Completeness.lean` |
| Intuitionistic soundness, Lindenbaum, completeness | `Metalogic/IntSoundness.lean`, `IntLindenbaum.lean`, `IntCompleteness.lean` |
| Minimal soundness, Lindenbaum, completeness | `Metalogic/MinSoundness.lean`, `MinLindenbaum.lean`, `MinCompleteness.lean` |
| Intuitionistic/minimal proof system instances | `ProofSystem/IntMinInstances.lean` |
| Full CI compliance (lint, shake, style) | All files |

## Design

### Primitive connectives

The connective hierarchy takes `bot` and `imp` as primitives, following Church (1956) and the Tarski-Bernays-Wajsberg system. All other connectives are derived via the Lukasiewicz encoding (`neg φ := imp φ bot`, etc.) and defined as `abbrev`s, so Lean handles conversions by definitional equality. Axiom schemas are polymorphic `abbrev`s over `[HasBot F] [HasImp F]`, instantiated at any formula type via typeclass resolution.

### Three-level proof system hierarchy

The classical/intuitionistic/minimal boundary is drawn by axiom selection:

```
MinimalHilbert             -- ImplyK + ImplyS + ModusPonens
  ├── IntuitionisticHilbert  -- + EFQ
  │     └── ClassicalHilbert       -- + Peirce
  ├── ModalHilbert           -- + BoxK + Necessitation
  │     └── ModalS5Hilbert         -- + BoxT + Axiom5
  └── ...
```

The `PropositionalAxiom` inductive and `Axioms` predicate are parameterized so that `Instances.lean` registers a `ClassicalHilbert` (all four axioms), while `IntMinInstances.lean` registers `IntuitionisticHilbert` (no Peirce) and `MinimalHilbert` (no Peirce, no EFQ) instances over the same formula type.

### Metalogic: soundness and completeness

Each of the three systems has its own soundness and completeness proof:

| System | Semantics | Soundness | Completeness |
|--------|-----------|-----------|--------------|
| Classical | Boolean valuations | Direct induction on derivation trees | Lindenbaum + MCS canonical model |
| Intuitionistic | Kripke frames (preorder, monotone, hereditary `⊥`) | Induction on forcing relation | Prime theory canonical model |
| Minimal | Kripke frames (preorder, monotone, explicit `⊥`-forcing) | Induction on forcing relation | Prime theory canonical model with `botForces` |

The Lindenbaum constructions use Zorn's lemma. The intuitionistic and minimal completeness proofs build canonical Kripke models whose worlds are prime/maximal consistent sets.

### ND-Hilbert equivalence

The extensional equivalence between ND and Hilbert (`Equivalence.lean`) proves that `⊢_ND Γ ⊢ φ ↔ ⊢_H Γ ⊢ φ` for classical propositional logic. Minimal logic has no ND equivalent (it lacks EFQ, which ND assumes) and is excluded. This enables using whichever proof system is more convenient while maintaining a single metalogic.

### Import hierarchy

All files use the Lean 4 `module` keyword with `public import` for transitive visibility.

```
Foundations/Logic/  →  Logics/Propositional/  →  Modal/  (future PR)
                                              →  Temporal/  →  Bimodal/  (future PRs)
```

## File inventory (39 files)

### Foundations/Logic/ (16 new files)

| File | Role |
|------|------|
| `Connectives.lean` | `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`; bundled connective classes |
| `Axioms.lean` | Polymorphic axiom `abbrev`s: `ImplyK`, `ImplyS`, `EFQ`, `Peirce`, `DNE`, modal/temporal axioms |
| `ProofSystem.lean` | `ModusPonens`, `Necessitation`, `HasAxiom*`; bundled `MinimalHilbert` through `BimodalTMHilbert` |
| `Theorems/Combinators.lean` | I, B, C combinators; `imp_trans`, `pairing`, `dni`, `flip` |
| `Theorems/Propositional/Core.lean` | LEM, DNE, RAA, `efq_neg`, `rcp` |
| `Theorems/Propositional/Connectives.lean` | `iff_intro`, `contrapose_imp`, De Morgan laws |
| `Theorems/BigConj.lean` | `BigConj` syntax and derivability lemmas |
| `Theorems/Modal/Basic.lean` | K-level: `box_mono`, `diamond_mono`, modal duality |
| `Theorems/Modal/S5.lean` | Axiom 5 derivation, collapse theorems |
| `Theorems/Temporal/TemporalDerived.lean` | Temporal operator lemmas |
| `Theorems/Temporal/FrameConditions.lean` | Frame condition marker typeclasses |
| `Theorems.lean` | Barrel aggregator |
| `Metalogic/Consistency.lean` | `DerivationSystem`, Lindenbaum's lemma, MCS foundations |
| `Metalogic/DeductionHelpers.lean` | `HasHilbertTree` typeclass; generic deduction theorem helpers |

### Logics/Propositional/ (18 new files)

| File | Role |
|------|------|
| `ProofSystem/Axioms.lean` | `PropositionalAxiom` inductive: `implyK`, `implyS`, `efq`, `peirce` |
| `ProofSystem/Derivation.lean` | `DerivationTree` proof witness, `Deriv` wrapper, height function |
| `ProofSystem/Instances.lean` | Classical `InferenceSystem`/`PropositionalHilbert` instance registration |
| `ProofSystem/IntMinInstances.lean` | Intuitionistic and minimal `InferenceSystem` instance registration |
| `Metalogic/DeductionTheorem.lean` | Deduction theorem by induction on derivation height |
| `Metalogic/MCS.lean` | `DerivationSystem` instantiation, MCS construction |
| `Metalogic/Soundness.lean` | Classical soundness (Boolean valuations) |
| `Metalogic/Completeness.lean` | Classical completeness (Lindenbaum + canonical model) |
| `Metalogic/IntSoundness.lean` | Intuitionistic soundness (Kripke) |
| `Metalogic/IntLindenbaum.lean` | Intuitionistic Lindenbaum's lemma (prime theories) |
| `Metalogic/IntCompleteness.lean` | Intuitionistic completeness (canonical Kripke model) |
| `Metalogic/MinSoundness.lean` | Minimal soundness (Kripke with explicit `⊥`-forcing) |
| `Metalogic/MinLindenbaum.lean` | Minimal Lindenbaum's lemma |
| `Metalogic/MinCompleteness.lean` | Minimal completeness (canonical Kripke model) |
| `Semantics/Basic.lean` | Boolean valuations and classical satisfaction |
| `Semantics/Kripke.lean` | Kripke frames, models, forcing relation |
| `NaturalDeduction/FromHilbert.lean` | ND wrappers over Hilbert: `impI`/`impE`/`botE`, cut, weakening, substitution |
| `NaturalDeduction/DerivedRules.lean` | ND derived rules for conjunction, disjunction, negation, biconditional |
| `NaturalDeduction/Equivalence.lean` | Extensional equivalence proof between ND and Hilbert systems |
| `NaturalDeduction/HilbertDerivedRules.lean` | Hilbert derived rules via ND transport |

### Other (1 new file, 4 modified files)

| File | Role |
|------|------|
| `Foundations/Data/ListHelpers.lean` | **New**: `removeAll` and supporting lemmas for deduction theorem files |
| `Foundations/Logic/InferenceSystem.lean` | **Modified**: minor adjustment for `DerivableIn` |
| `Logics/Propositional/Defs.lean` | **Modified**: parameterized `Theory`, added `IsIntuitionistic`/`IsClassical` |
| `Logics/Propositional/NaturalDeduction/Basic.lean` | **Modified**: align with parameterized axiom infrastructure |
| `Cslib.lean` | **Modified**: 35 new import lines |

## Verification

- `lake build`: 0 errors (2754 jobs)
- `lake test`: pass (8758 jobs)
- `lake lint`: 0 errors
- `lake exe lint-style`: pass
- `lake exe checkInitImports`: pass
- `lake exe mk_all --module --check`: no update necessary
- `lake shake --add-public --keep-implied --keep-prefix`: no issues in contributed files
- `grep -rn "sorry"`: 0 hits across all contributed files

## References

- Blackburn, P., de Rijke, M. and Venema, Y. (2001). *Modal Logic*. Cambridge University Press.
- Chellas, B.F. (1980). *Modal Logic: An Introduction*. Cambridge University Press.
- Church, A. (1956). *Introduction to Mathematical Logic, Vol. I*. Princeton University Press.
- Curry, H.B. and Feys, R. (1958). *Combinatory Logic, Vol. I*. North-Holland.
- Griffin, T.G. (1990). "A Formulae-as-Types Notion of Control". *POPL 1990*.
- Howard, W.A. (1969/1980). "The Formulae-as-Types Notion of Construction".
- Kripke, S. (1963). "Semantical Analysis of Modal Logic I". *Zeitschrift für mathematische Logik und Grundlagen der Mathematik*, 9:67-96.
- Troelstra, A.S. and Schwichtenberg, H. (2000). *Basic Proof Theory*. 2nd edition. Cambridge University Press.

---

> **AI Disclosure**: This contribution was developed with assistance from Claude (Anthropic). All proofs have been reviewed and machine-verified by the Lean 4 type checker.
