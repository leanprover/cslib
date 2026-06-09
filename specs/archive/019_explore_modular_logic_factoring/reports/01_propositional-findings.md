# Propositional Logic Factoring Analysis

**Task**: 19 — Explore modular logic factoring
**Focus**: Propositional components in BimodalLogic that belong in Propositional/ or Foundations/Logic/
**Date**: 2026-06-08

---

## (a) What Currently Exists in cslib's Propositional Module

### Formula type (`Defs.lean`)
- `PL.Proposition Atom` inductive with `{atom, bot, imp}`, plus derived `neg`, `top`, `or`, `and`
- `PropositionalConnectives` instance
- `Theory` = `Set (Proposition Atom)`, with `MPL`, `IPL`, `CPL` theories
- `IsIntuitionistic`, `IsClassical` typeclasses on theories
- `Proposition.subst` (substitution / monad instance)

### Natural deduction (`NaturalDeduction/Basic.lean`)
- `Theory.Derivation` inductive (ax, ass, impI, impE, botE) — a natural deduction system
- `InferenceSystem` instance for both `Sequent` and `Proposition`
- Full treatment: weakening, cut, substitution, equivalence (refl/symm/trans)
- This is a *semantic/natural deduction* system, NOT a Hilbert-style axiom system

### Embeddings (`Embedding.lean`)
- `PL.Proposition.toModal` and `PL.Proposition.toTemporal` with `Coe` instances
- Simp lemmas for bot, imp, neg (missing: atom)
- No `PL.Proposition.toBimodal`

### Foundations layer (`Foundations/Logic/`)
- **Connectives.lean**: Typeclass hierarchy (`HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`, plus bundled `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`). Also `LukasiewiczDerived` (uninstantiated).
- **Axioms.lean**: Polymorphic axiom abbrevs — propositional (`ImplyK`, `ImplyS`, `EFQ`, `Peirce`, `DNE`), modal (`AxiomK`, `AxiomT`, `Axiom4`, `AxiomB`, `Axiom5`, `AxiomD`), temporal (`SerialFuture`, `SerialPast`), interaction (`ModalFuture`).
- **ProofSystem.lean**: `ModusPonens`, `Necessitation`, `TemporalNecessitation` rule classes. `HasAxiom*` classes for each axiom. Bundled classes: `PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`. Tag types for each.
- **InferenceSystem.lean**: Generic `InferenceSystem S α` typeclass with `DerivableIn`.
- **LogicalEquivalence.lean**: Generic logical equivalence typeclass.

---

## (b) BimodalLogic Components That Are Purely Propositional

### Combinators.lean (~300 lines)
Identity `I`, composition `B`, flip `C`, pair `S` — combinatory logic combinators for the Hilbert system. Depend ONLY on modus ponens and the K/S axiom schemas. Statement: `[PropositionalHilbert S] → DerivableIn S (ImplyI φ)` etc.

### Propositional/Core.lean, Connectives.lean, Reasoning.lean (~1,100 lines)
Derived propositional theorems — ex falso, disjunction introduction/elimination, conjunction, double negation, contraposition, etc. All stated using only `→` and `⊥`. Statement: `[PropositionalHilbert S] → DerivableIn S (EFQ φ)` etc.

### ContextualProofs.lean (~500 lines)
Weakening, cut, contextual proof rules for a Hilbert system. About `Context := List F` and derivability from contexts. The operations (membership, subset, append) are generic on the formula type. Statement: for any `[PropositionalHilbert S]`, weakening/cut hold.

### BigConj.lean (~500 lines)
Finite conjunction over a list of formulas. Uses only `and` (derived from `imp` and `bot`). Completely generic: works for any type with `PropositionalConnectives`.

### Deduction theorem (DeductionTheorem.lean, ~500 lines)
The deduction theorem (`Γ, φ ⊢ ψ → Γ ⊢ φ → ψ`) is a propositional result. In BimodalLogic it's stated for the full TM system, but the proof only uses modus ponens, weakening, and the K/S axioms. It can be stated generically: `[PropositionalHilbert S] → ...`.

### Context.lean (~400 lines)
`Context := List F` with operations. Completely generic — works for any formula type.

### Subformulas.lean + SubformulaClosure/ (~1,300 lines)
Subformula relation and closure. The definition is specific to each formula type's constructors, but the *properties* could be stated via a typeclass.

### Substitution.lean (~500 lines)
Uniform substitution theorem. Constructor-specific implementation, but the *theorem* could be stated generically.

---

## (c) What Could Be Factored Out

### Tier 1: Strong candidates — generic over `[PropositionalHilbert S]`

| Component | ~Lines | Target Location | Signature Shape |
|-----------|--------|-----------------|-----------------|
| Combinators (I, B, C, S) | ~300 | `Foundations/Logic/Theorems/Combinators.lean` | `[PropositionalHilbert S] → DerivableIn S (ImplyI φ)` |
| Propositional derived theorems | ~1,100 | `Foundations/Logic/Theorems/Propositional/` | `[PropositionalHilbert S] → DerivableIn S (EFQ φ)` |
| Contextual proofs (weakening, cut) | ~500 | `Foundations/Logic/Theorems/ContextualProofs.lean` | `[PropositionalHilbert S] → ...` |
| BigConj | ~500 | `Foundations/Logic/Theorems/BigConj.lean` | `[PropositionalConnectives F] [PropositionalHilbert S] → ...` |
| Deduction theorem | ~500 | `Foundations/Logic/Theorems/DeductionTheorem.lean` | `[PropositionalHilbert S] → (Γ, φ ⊢ ψ) → (Γ ⊢ φ → ψ)` |

**Total: ~2,900 lines** that would not need to go into `Bimodal/` at all.

**Key requirement**: These need the Hilbert-style `DerivableIn S` machinery, not the natural deduction `Theory.Derivation` that PL currently has. The existing PL module uses natural deduction (sequent-style); the BimodalLogic components use Hilbert-style axiom systems. The generic typeclass versions would use `InferenceSystem S F` + `PropositionalHilbert S` + `DerivableIn S`.

### Tier 4: Formula-specific but could be typeclass-generic

| Component | ~Lines | Note |
|-----------|--------|------|
| `Context := List F` | ~400 | Generic via `variable (F : Type*) [PropositionalConnectives F]` |
| Subformula relation | ~500 | Could use a `HasSubformula` typeclass |
| SubformulaClosure | ~800 | Mostly specific to constructor set |
| `complexity` | ~100 | Constructor-specific |
| `Countable`/`Denumerable` instances | ~100 | Constructor-specific |

### Impact on Existing Tasks

**Task 5 (Port Derived Theorems)**: Currently plans to port everything into `Bimodal/Theorems/`. Instead:
- Combinators + Propositional/ + ContextualProofs (~1,900 lines) → `Foundations/Logic/Theorems/` with `[PropositionalHilbert S]` signatures

**Task 7 (Port MCS/Deduction)**: The deduction theorem (~500 lines) is propositional. It could go in Foundations with a `[PropositionalHilbert S]` signature. The MCS theory is inherently bimodal.

**Net effect**: ~2,900 lines would move from `Bimodal/` to `Foundations/Logic/`, reusable by Modal, Temporal, and Bimodal.
