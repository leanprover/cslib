# Modular Logic Factoring: Research Synthesis

**Task**: 19 — Explore modular logic factoring
**Date**: 2026-06-08
**Sources**: Parallel analysis of Propositional, Modal, and Temporal dimensions

---

## Current State

cslib's logic modules vary widely in maturity:

| Module | Syntax | Semantics | Proof System | Derived Theorems |
|--------|--------|-----------|-------------|-----------------|
| **Propositional** | Complete | Theory-based | Natural deduction | Weakening, cut, substitution |
| **Modal** | Complete | Kripke + frame correspondence (K/T/B/4/5/D) | None (Hilbert classes exist, no instances) | None |
| **Temporal** | Complete | None | None (`TemporalBXHilbert` is empty) | None |
| **Bimodal** | Complete | None | None | None |
| **Foundations** | Connective typeclasses | — | `PropositionalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert` (all uninstantiated) | — |

The Foundations layer defines the typeclass hierarchy but nothing instantiates it yet. The gap between the generic infrastructure and concrete proof systems is the main architectural opportunity.

---

## BimodalLogic Component Classification

Direct inspection of BimodalLogic source files for operator usage yields a clean three-way split:

### Purely Propositional (~2,900 lines)

Uses only `atom`, `bot`, `imp` — no `box`, `untl`, or `snce`:

| Component | Lines | Generic Signature |
|-----------|-------|-------------------|
| Combinators (I, B, C, S) | ~300 | `[PropositionalHilbert S]` |
| Propositional/{Core,Connectives,Reasoning} | ~1,100 | `[PropositionalHilbert S]` |
| ContextualProofs (weakening, cut) | ~500 | `[PropositionalHilbert S]` |
| BigConj (finite conjunction) | ~500 | `[PropositionalConnectives F] [PropositionalHilbert S]` |
| DeductionTheorem | ~500 | `[PropositionalHilbert S]` |

**Target**: `Cslib.Foundations.Logic.Theorems/` — reusable by all four logics.

### Purely Modal (~1,200 lines)

Uses `box` but never `untl`/`snce`:

| Component | Lines | Generic Signature |
|-----------|-------|-------------------|
| S4 derived theorems | ~400 | `[ModalHilbert S]` |
| S5 derived theorems | ~400 | `[ModalS5Hilbert S]` |
| Generalized necessitation | ~400 | `[Necessitation S]` |

**Target**: `Cslib.Logics.Modal.Theorems/` — reusable by Modal and Bimodal.

### Purely Temporal (~920 lines)

Uses `untl`/`snce` but never `box`:

| Component | Lines | Generic Signature |
|-----------|-------|-------------------|
| TemporalDerived (temporal K, temporal 4, connectedness, Until/Since lemmas) | ~790 | `[TemporalBXHilbert S]` |
| Frame condition typeclasses (linear, dense, discrete) | ~130 | Standalone |

**Target**: `Cslib.Logics.Temporal/` — reusable by Temporal and Bimodal.

### Structurally Generic (~1,800 lines)

Zero modal or temporal references — operate on abstract formula types:

| Component | Lines | Note |
|-----------|-------|------|
| MaximalConsistent + MCSProperties | ~1,300 | Uses only `Countable F`, `Context`, `Derivable` |
| Context (`List F` operations) | ~400 | Generic over any formula type |
| Substitution theorem | ~500 | Theorem generic, implementation per-type |

These could live in Foundations with appropriate typeclasses, but the effort-to-payoff ratio is lower since MCS theory is only used by completeness proofs.

### Inherently Bimodal (~30,000+ lines)

Requires all six constructors or modal-temporal interaction:

- **42-axiom inductive** with interaction axioms (MF, TF)
- **DerivationTree** with both necessitation rules
- **Task frame semantics** (`□` quantifies over world histories)
- **Perpetuity theorems** (modal fixed-point + temporal operators)
- **Soundness, Completeness, Decidability, Separation**

---

## What's Missing for Standalone Modules

### Foundations/Logic/ needs:

1. **Hilbert-style derived theorems** (~2,900 lines from BimodalLogic). The existing PL natural deduction and the Hilbert typeclass hierarchy are disjoint — nothing bridges them yet. Porting the propositional theorems as `[PropositionalHilbert S]` lemmas fills this gap.

### Modal/ needs:

1. **Hilbert-style proof system** — concrete `Modal.DerivationTree` with `ModalHilbert`/`ModalS5Hilbert` instances (currently only semantic infrastructure exists)
2. **Derived theorems** (~1,200 lines from BimodalLogic)
3. **Substitution** — `Modal.Proposition.subst` and the substitution theorem
4. **DecidableEq** on `Modal.Proposition` (task 16)

### Temporal/ needs:

1. **Axiom definitions** — expand from 2 to ~22 temporal axiom `abbrev`s in `Axioms.lean`
2. **HasAxiom\* classes** — fill out `TemporalBXHilbert` with temporal axiom requirements
3. **Proof system** — `Temporal.DerivationTree` (5 rules, 31 axioms — drop modal necessitation and 6 modal/interaction axioms)
4. **Derived theorems** (~790 lines from BimodalLogic)
5. **Frame conditions** (~130 lines from BimodalLogic)
6. **Semantics** — truth on linear orders without world histories (**new**, not from BimodalLogic)

---

## Recommended Factoring of Existing Tasks

### Current task structure (tasks 2-11)

All 10 porting tasks target `Bimodal/` exclusively. This conflates ~4,900 lines of reusable propositional/modal/temporal material with the genuinely bimodal content.

### Proposed changes

**Task 4 (Port Proof System)** — split into:
- **Foundations work**: Complete temporal axiom `abbrev`s (~20 definitions) and `HasAxiom*` classes in `Axioms.lean`/`ProofSystem.lean`. This is prerequisite infrastructure.
- **Bimodal-specific**: Concrete `Axiom` inductive (42 constructors), `DerivationTree`, `Derivable`, `InferenceSystem` instance — stays in `Bimodal/ProofSystem/`.

**Task 5 (Port Derived Theorems)** — split into three targets:
- **Foundations** (~1,900 lines): Combinators + Propositional theorems + ContextualProofs → `Foundations/Logic/Theorems/` with `[PropositionalHilbert S]`
- **Modal** (~1,200 lines): S4 + S5 + GenNec → `Modal/Theorems/` with `[ModalS5Hilbert S]`
- **Temporal** (~790 lines): TemporalDerived → `Temporal/Theorems/` with `[TemporalBXHilbert S]`
- **Bimodal** (~800 lines): Perpetuity/ → stays in `Bimodal/Theorems/`

**Task 7 (Port MCS/Deduction)** — extract:
- **Foundations** (~500 lines): Deduction theorem → `Foundations/Logic/Theorems/` with `[PropositionalHilbert S]`
- **Bimodal** (~2,000 lines): MCS theory — stays in `Bimodal/Metalogic/Core/`

**Task 6 (Port Frame Conditions)** — extract:
- **Temporal** (~130 lines): Frame condition typeclasses → `Temporal/FrameConditions/`
- **Bimodal** (~2,370 lines): Soundness proofs using interaction axiom — stays in `Bimodal/`

**Tasks 2, 3, 8, 9, 10, 11** — minimal changes needed. These are either inherently bimodal (completeness, decidability, separation) or syntax infrastructure that is constructor-specific.

### Key architectural decision

The propositional and modal theorems can be ported in two ways:

1. **Port concrete, then generalize**: Port BimodalLogic's concrete `DerivationTree`-based proofs into `Bimodal/`, then refactor to typeclass-generic versions in `Foundations/` and `Modal/`. Lower risk, higher total effort.

2. **Port directly to typeclasses**: Rewrite the proofs using `[PropositionalHilbert S]` / `[ModalS5Hilbert S]` from the start. Higher upfront effort, but avoids duplicating 4,900 lines. The proofs only use modus ponens, axiom instantiation, and (for modal) necessitation — all of which have typeclass representations already.

**Recommendation**: Option 2. The typeclass infrastructure already exists. The proofs are structurally simple (combinatory constructions using MP and axioms). Porting directly to the generic level avoids creating bimodal-specific versions that would immediately need refactoring.

---

## Impact Summary

| Lines | Current Target | Proposed Target | Reusable By |
|-------|---------------|-----------------|-------------|
| ~2,900 | Bimodal/ | Foundations/Logic/Theorems/ | PL, Modal, Temporal, Bimodal |
| ~1,200 | Bimodal/ | Modal/Theorems/ | Modal, Bimodal |
| ~920 | Bimodal/ | Temporal/ | Temporal, Bimodal |
| ~30,000+ | Bimodal/ | Bimodal/ (unchanged) | Bimodal only |

**~5,000 lines** (~14% of BimodalLogic) would move to reusable locations. The remaining ~30,000 lines are genuinely bimodal and stay where planned.
