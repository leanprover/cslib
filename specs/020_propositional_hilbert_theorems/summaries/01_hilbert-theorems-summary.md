# Implementation Summary: Task #20

- **Task**: 20 - Port propositional Hilbert-style theorems
- **Status**: Implemented
- **Plan**: plans/01_hilbert-theorems-plan.md
- **Session**: sess_1780968264_f709a2

## Overview

Ported propositional Hilbert-style theorems from BimodalLogic to
`Cslib/Foundations/Logic/Theorems/` as generic `[PropositionalHilbert S]` lemmas.
All theorems use raw `HasImp.imp`/`HasBot.bot` encoding rather than
`LukasiewiczDerived` to avoid typeclass unification issues.

## Phases Completed

### Phase 1: Combinators
- Created `Cslib/Foundations/Logic/Theorems/Combinators.lean`
- Ported: imp_trans, identity, b_combinator, theorem_flip, theorem_app1,
  theorem_app2, pairing, dni, combine_imp_conj, combine_imp_conj_3
- All proofs are pure combinator constructions using ImplyK, ImplyS, and MP

### Phase 2: Propositional Core
- Created `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`
- Ported: efq_axiom, peirce_axiom, double_negation, raa, efq_neg, rcp, lem
- Novel DT-free proofs: lce_imp (via efq_neg + Peirce), rce_imp (via efq_neg +
  ImplyK + Peirce)
- double_negation derived from EFQ + Peirce + B-combinator

### Phase 3: Propositional Connectives
- Created `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`
- Ported: contrapose_imp, contraposition, classical_merge, iff_intro,
  contrapose_iff, iff_neg_intro
- De Morgan laws: demorgan_conj_neg_forward, demorgan_conj_neg_backward,
  demorgan_conj_neg, demorgan_disj_neg_forward, demorgan_disj_neg_backward,
  demorgan_disj_neg
- classical_merge proved DT-free via contraposition + Peirce

### Phase 4: Reasoning and BigConj
- Created `Cslib/Foundations/Logic/Theorems/Propositional/Reasoning.lean`
- Ported: bi_imp (biconditional introduction via pairing)
- Created `Cslib/Foundations/Logic/Theorems/BigConj.lean`
- Defined: bigconj, neg_bigconj with simp lemmas
- Proved: bigconj_mem_derivable, bigconj_derivable_intro

### Phase 5: Module Aggregator
- Created `Cslib/Foundations/Logic/Theorems.lean` as aggregator
- Full `lake build` passes with zero errors
- Zero sorry, zero vacuous definitions, zero new axioms

## Key Design Decisions

1. **Raw encoding over LukasiewiczDerived**: All theorems use raw
   `HasImp.imp`/`HasBot.bot` encoding rather than `LukasiewiczDerived.and/neg/or`.
   This avoids typeclass unification issues since `LukasiewiczDerived` is an open
   typeclass whose instances may override the default definitions.

2. **DT-free proofs for lce_imp, rce_imp, classical_merge**: These theorems in
   BimodalLogic use the deduction theorem. We derived them without DT using:
   - lce_imp: efq_neg + Peirce composition
   - rce_imp: efq_neg + ImplyK + B-combinator + Peirce
   - classical_merge: contraposition + B-combinator + Peirce

3. **Naming inversion applied**: BimodalLogic's `prop_s` (weakening) mapped to
   cslib's `ImplyK`, and `prop_k` (distribution) to `ImplyS`, throughout.

4. **ContextualProofs skipped**: All context-based theorems (ecq, ldi, rdi, lce,
   rce, ni, ne, de, or_elim_neg_neg) are per-logic and were correctly excluded.

## Plan Deviations

- **Task 1.4 (mp helper)**: Skipped -- `ModusPonens.mp` suffices directly, no
  wrapper needed.
- **LukasiewiczDerived usage**: Altered -- plan assumed `LukasiewiczDerived` would
  work for theorem statements, but the open typeclass prevents definitional equality.
  All theorems use raw encoding instead.

## Files Created

| File | Lines | Content |
|------|-------|---------|
| `Cslib/Foundations/Logic/Theorems/Combinators.lean` | ~335 | I/B/C/S combinators |
| `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` | ~290 | LEM, DNE, lce/rce_imp |
| `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` | ~550 | classical_merge, De Morgan |
| `Cslib/Foundations/Logic/Theorems/Propositional/Reasoning.lean` | ~50 | bi_imp |
| `Cslib/Foundations/Logic/Theorems/BigConj.lean` | ~140 | bigconj + derivability |
| `Cslib/Foundations/Logic/Theorems.lean` | ~28 | Module aggregator |

## Verification

- `lake build`: PASS (full project, 2739 jobs)
- Sorry count: 0
- Vacuous definitions: 0
- New axioms: 0
- All 34 planned theorems/definitions present
