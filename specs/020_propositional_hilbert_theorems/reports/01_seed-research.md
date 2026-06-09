# Seed Research Report: Task #20 — Propositional Hilbert Theorems

**Task**: 20 — Port propositional Hilbert-style theorems to Foundations
**Date**: 2026-06-08
**Sources**: Task 19 research synthesis (01_factoring-synthesis.md, 02_team-research.md)

---

## Overview

This seed report captures the relevant findings from Task 19's research for Task 20. No additional research is needed — proceed directly to planning and implementation.

Task 20 ports ~2,400 lines of purely propositional theorems from BimodalLogic to `Cslib/Foundations/Logic/Theorems/` as generic `[PropositionalHilbert S]` lemmas. The typeclass infrastructure (`PropositionalHilbert` with modus ponens and propositional axiom requirements) already exists from task 14.

---

## Component Classification

These components from BimodalLogic use only `atom`, `bot`, `imp` — no `box`, `untl`, or `snce`. They can be stated at the `[PropositionalHilbert S]` typeclass level and are reusable by all four logics (Propositional, Modal, Temporal, Bimodal).

| Component | Source File | Lines | Generic Signature |
|-----------|-------------|-------|-------------------|
| Combinators (I, B, C, S) | `Theories/Bimodal/Theorems/Combinators.lean` | ~300 | `[PropositionalHilbert S]` |
| Propositional/Core | `Theories/Bimodal/Theorems/Propositional/Core.lean` | ~400 | `[PropositionalHilbert S]` |
| Propositional/Connectives | `Theories/Bimodal/Theorems/Propositional/Connectives.lean` | ~350 | `[PropositionalHilbert S]` |
| Propositional/Reasoning | `Theories/Bimodal/Theorems/Propositional/Reasoning.lean` | ~350 | `[PropositionalHilbert S]` |
| ContextualProofs | `Theories/Bimodal/Theorems/ContextualProofs.lean` | ~500 | `[PropositionalHilbert S]` |
| BigConj (generic) | `Theories/Bimodal/Syntax/BigConj.lean` | ~500 | `[PropositionalConnectives F] [PropositionalHilbert S]` |

**Total scope**: ~2,400 lines

**Excluded**: DeductionTheorem (~500 lines) — stays per-logic. See team research finding below.

---

## Key Design Decisions

### Typeclass Infrastructure Already Exists

`Cslib/Foundations/Logic/ProofSystem.lean` already defines:
- `PropositionalHilbert`: extends `HasModusPonens`, `HasAxiomK`, `HasAxiomS`, etc.
- All propositional `HasAxiom*` typeclasses

Nothing needs to be added to the typeclass hierarchy for this task. Theorems can use existing `[PropositionalHilbert S]` constraints.

### DeductionTheorem Stays Per-Logic (Team Research Finding)

The DeductionTheorem requires structural induction on `DerivationTree` (inspecting proof structure). This cannot be done at the generic `DerivableIn` (Prop-valued) level. Options considered:
1. Axiomatize as typeclass method — pragmatic but sidesteps proof structure
2. Create generic `DerivationTree` in Foundations — major new infrastructure
3. Keep per-logic where concrete derivation trees exist

**Decision**: Keep DeductionTheorem per-logic (option 3). It is the one propositional theorem that resists generic porting. This reduces Task 20 scope from ~2,900 to ~2,400 lines.

### Direct Typeclass Porting (Not Concrete-then-Generalize)

Research recommended Option 2: port directly to typeclass-generic level. The proofs only use modus ponens, axiom instantiation — all have typeclass representations. Avoids creating bimodal-specific versions that would immediately need refactoring.

---

## Target Structure

```
Cslib/Foundations/Logic/Theorems/
├── Combinators.lean           -- I, B, C, S combinators as [PropositionalHilbert S] lemmas
├── Propositional/
│   ├── Core.lean              -- ex falso, double negation, etc.
│   ├── Connectives.lean       -- disjunction, conjunction derived
│   └── Reasoning.lean         -- transitivity, contraposition, etc.
├── ContextualProofs.lean      -- weakening, cut, contextual rules
└── BigConj.lean               -- finite conjunction: [PropositionalConnectives F] [PropositionalHilbert S]
```

---

## Dependencies

- **Task 14** (done): Provides `PropositionalHilbert` and all `HasAxiom*` typeclasses
- **No other logic-task dependencies**: Task 20 is Wave 1 — can proceed immediately

---

## Relationship to Other Tasks

After Task 20 completes:
- **Task 21** (Modal theorems) imports and extends these propositional lemmas
- **Task 22** (Temporal infrastructure) imports propositional lemmas
- **Task 4** (Bimodal proof system) imports from Task 20 after Tasks 20 and 22 complete

---

## References

- Research synthesis: `specs/019_explore_modular_logic_factoring/reports/01_factoring-synthesis.md`
- Team research: `specs/019_explore_modular_logic_factoring/reports/02_team-research.md`
- Typeclass hierarchy: `Cslib/Foundations/Logic/ProofSystem.lean`
- BimodalLogic source: `Theories/Bimodal/Theorems/` (Combinators, Propositional/, ContextualProofs)
