# Seed Research Report: Task #22 — Temporal Infrastructure and Theorems

**Task**: 22 — Build temporal proof system infrastructure and port temporal theorems
**Date**: 2026-06-08
**Sources**: Task 19 research synthesis (01_factoring-synthesis.md, 02_team-research.md)

---

## Overview

This seed report captures the relevant findings from Task 19's research for Task 22. No additional research is needed — proceed directly to planning and implementation.

Task 22 is substantially larger than the initial estimate suggested. The team research (02_team-research.md, finding #5) identified that `TemporalBXHilbert` is currently a shell with zero temporal axiom requirements, and filling it requires approximately twice the originally estimated work. This task creates the complete temporal proof system infrastructure (~1,500 lines) and ports temporal theorems from BimodalLogic.

---

## Current State of Temporal/ in cslib

| Component | Status |
|-----------|--------|
| `Temporal.Formula` (formula type) | Complete — `{atom, bot, imp, untl, snce}` |
| Semantics | Missing — Task 23 adds this |
| `TemporalBXHilbert` typeclass | Exists but is a shell (extends PropositionalHilbert + empty TemporalNecessitation) |
| `TemporalNecessitation` | Marker class only — no derivation rule |
| Temporal axiom abbrevs in Axioms.lean | Only 2 exist: `SerialFuture`, `SerialPast` |
| `HasAxiom*` typeclasses for temporal axioms | Missing (~20 needed) |
| Concrete `DerivationTree` | Missing |
| Derived theorems | Missing |
| Frame condition typeclasses | Missing (~130 lines) |

**Critical finding**: `TemporalBXHilbert` has zero temporal axiom requirements. Any instance trivially satisfies it by providing only PropositionalHilbert infrastructure. This is architecturally incomplete.

---

## Component Classification: Work Required

### New Infrastructure (not ported from BimodalLogic)

| Component | Lines | Description |
|-----------|-------|-------------|
| Temporal axiom abbrevs in Axioms.lean | ~100 | ~20 new abbrevs: TK, T4, TT-F/P, TA, TL, Lin, and all BX temporal axioms. Currently only SerialFuture, SerialPast exist. |
| HasAxiom* typeclasses in ProofSystem.lean | ~200 | ~20 new typeclasses: HasAxiomTK, HasAxiomT4, HasAxiomTTF, HasAxiomTTP, etc. |
| TemporalBXHilbert restructuring | ~50 | Extend all temporal HasAxiom* classes (currently extends only PropositionalHilbert + marker) |
| TemporalNecessitation non-empty | ~50 | Add actual derivation rule (currently just a marker class) |
| BimodalTMHilbert compatibility | ~100 | Instance deriving TemporalBXHilbert from BimodalTMHilbert (diamond-avoidance) |

### Ported from BimodalLogic

| Component | Source File | Lines | Generic Signature |
|-----------|-------------|-------|-------------------|
| Temporal.DerivationTree | (based on BimodalLogic pattern, drop modal rules) | ~200 | `Temporal.DerivationTree`, instance: `TemporalBXHilbert Temporal.HilbertBX` |
| TemporalDerived theorems | `Theories/Bimodal/Theorems/TemporalDerived.lean` | ~790 | `[TemporalBXHilbert S]` |
| Frame condition typeclasses | `Theories/Bimodal/FrameConditions/` (temporal subset) | ~130 | Standalone: LinearTemporalFrame, DenseTemporalFrame, DiscreteTemporalFrame |

**Total scope**: ~1,500 lines

---

## BimodalTMHilbert Diamond-Avoidance Pattern

**Critical design decision** (team research finding #6):

`BimodalTMHilbert` currently extends `ModalS5Hilbert` + `TemporalNecessitation` + `HasAxiomMF`, but does NOT extend `TemporalBXHilbert`. Once Task 22 fills `TemporalBXHilbert` with ~20 `HasAxiom*` classes, theorems at `[TemporalBXHilbert S]` won't directly apply in `[BimodalTMHilbert S]` contexts.

**Recommended solution**: Mirror the `BimodalConnectives` pattern:
- `BimodalTMHilbert` directly extends the individual temporal `HasAxiom*` classes (e.g., `HasAxiomTK`, `HasAxiomT4`, etc.), just as `BimodalConnectives` directly extends `HasUntil`/`HasSince` rather than extending `TemporalConnectives`
- Provide a manual instance: `instance [BimodalTMHilbert S] : TemporalBXHilbert S := { ... }`
- This avoids the diamond inheritance problem with `PropositionalHilbert` at the base

This instance should be provided in `Cslib/Foundations/Logic/ProofSystem.lean` or a new `Cslib/Logics/Temporal/ProofSystem/BimodalCompat.lean`.

---

## Temporal Axiom System

The BX temporal axioms (from `Theories/Bimodal/ProofSystem/Axioms.lean`):

**Propositional base**: Already covered by `PropositionalHilbert` (K, S, axiom schema)

**Temporal axioms** (all ~22, currently only SerialFuture/SerialPast exist as abbrevs):
- TK-F, TK-P (temporal distribution)
- T4-F, T4-P (transitivity/4-axiom for Until/Since)
- TT-F, TT-P (truth conditions for temporal operators)
- TA-F, TA-P (temporal axiom A)
- TL-F, TL-P (linearity axioms)
- Lin (linearity)
- Serial-F, Serial-Past (already exist)
- And more...

---

## Target Structure

```
Cslib/Foundations/Logic/
├── Axioms.lean                -- Add ~20 temporal axiom abbrevs (TK, T4, TT-F/P, TA, TL, etc.)
└── ProofSystem.lean           -- Add ~20 HasAxiom* typeclasses, restructure TemporalBXHilbert

Cslib/Logics/Temporal/
├── ProofSystem/
│   ├── DerivationTree.lean    -- Temporal.DerivationTree (5 rules, ~22 temporal axioms)
│   ├── Derivable.lean         -- Derivable predicate, InferenceSystem instance
│   └── BimodalCompat.lean     -- [BimodalTMHilbert S] -> TemporalBXHilbert S instance
├── Theorems/
│   └── TemporalDerived.lean   -- ~790 lines: temporal K, temporal 4, Until/Since lemmas
└── FrameConditions/
    └── FrameClasses.lean      -- LinearTemporalFrame, DenseTemporalFrame, DiscreteTemporalFrame
```

---

## Relationship to Other Tasks

- **Task 20** (Propositional Theorems): Task 22 can import propositional lemmas for use in temporal proofs
- **Task 4** (Bimodal Proof System): After Task 22 provides `HasAxiom*` typeclasses + BimodalTMHilbert compat, Task 4 can focus on the concrete 42-axiom bimodal Axiom inductive and DerivationTree
- **Task 6** (Bimodal Frame Conditions): Bimodal frame conditions (FrameClass, DenseSoundness, etc.) remain in Task 6; temporal frame condition typeclasses (linear/dense/discrete standalone) move to Task 22
- **Task 23** (Temporal Semantics): Builds on the `TemporalBXHilbert` proof system from Task 22

---

## References

- Research synthesis: `specs/019_explore_modular_logic_factoring/reports/01_factoring-synthesis.md`
- Team research (finding #5, #6): `specs/019_explore_modular_logic_factoring/reports/02_team-research.md`
- Current typeclass hierarchy: `Cslib/Foundations/Logic/ProofSystem.lean`, `Axioms.lean`
- BimodalLogic temporal axioms: `Theories/Bimodal/ProofSystem/Axioms.lean`
- BimodalLogic temporal theorems: `Theories/Bimodal/Theorems/TemporalDerived.lean`
- BimodalConnectives pattern reference: `Cslib/Foundations/Logic/Connectives.lean`
