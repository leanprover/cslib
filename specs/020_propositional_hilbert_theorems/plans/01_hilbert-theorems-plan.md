# Implementation Plan: Task #20

- **Task**: 20 - Port propositional Hilbert-style theorems
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Dependencies**: None (PropositionalHilbert typeclass already exists from task 14)
- **Research Inputs**: specs/020_propositional_hilbert_theorems/reports/01_hilbert-theorems-research.md
- **Artifacts**: plans/01_hilbert-theorems-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Port propositional Hilbert-style theorems from BimodalLogic to `Cslib/Foundations/Logic/Theorems/` as generic `[PropositionalHilbert S]` lemmas. The research report identified ~1,000-1,200 portable lines (revised down from the original ~2,400 estimate) across Combinators, Propositional/{Core,Connectives,Reasoning}, and BigConj. ContextualProofs is entirely per-logic and is skipped. Three theorems (lce_imp, rce_imp, classical_merge) currently use the deduction theorem and require novel DT-free combinator proofs.

### Research Integration

Key findings from the research report (01_hilbert-theorems-research.md):

1. **CRITICAL naming inversion**: BimodalLogic's `Axiom.prop_s` (weakening) maps to cslib's `HasAxiomImplyK.implyK`, and `Axiom.prop_k` (distribution) maps to `HasAxiomImplyS.implyS`. This systematic renaming must be applied throughout.
2. **Translation pattern**: `DerivationTree fc [] phi` becomes `InferenceSystem.DerivableIn S phi`. Axiom access changes from `DerivationTree.axiom` constructors to typeclass methods (`implyK`, `implyS`, `efq`, `peirce`). Modus ponens changes from `DerivationTree.modus_ponens` to `ModusPonens.mp`.
3. **Noncomputability**: `DerivableIn` is `Prop`-valued (`Nonempty`), so ported proofs will be `noncomputable` since they compose existential witnesses.
4. **LukasiewiczDerived**: Derived connectives (neg, and, or, top) must be handled via `[LukasiewiczDerived F]` typeclass constraint. Default implementations match BimodalLogic definitions.
5. **ContextualProofs (451 lines) skipped entirely**: These are context-based (`[A, B] |- C` form) with no counterpart in the `DerivableIn` framework.
6. **DT-free proof strategies identified**: lce_imp via Peirce + efq_neg composition; rce_imp similarly; classical_merge via contraposition + Peirce.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following ROADMAP.md items:
- Phase 1 (Propositional -- Hilbert Theorems): Task 20 is the entirety of Phase 1
- Success Metric: "Propositional theorems ported: all ~2,400 lines in Foundations/Logic/Theorems/"
- Milestone: "All four logics can import propositional theorems without bimodal dependency"

## Goals & Non-Goals

**Goals**:
- Create `Cslib/Foundations/Logic/Theorems/` directory with all portable propositional theorems
- Port I/B/C/S combinators, imp_trans, pairing, dni from Combinators.lean
- Port LEM, double_negation, raa, efq_neg, rcp from Propositional/Core.lean
- Derive lce_imp, rce_imp without deduction theorem using Peirce + EFQ
- Port classical_merge, iff operations, contraposition, De Morgan laws from Connectives.lean
- Port bi_imp from Reasoning.lean
- Create generic BigConj syntax and basic derivability lemmas
- All theorems generic over `[PropositionalHilbert S]` with `[LukasiewiczDerived F]`
- `lake build` passes with zero errors after each phase

**Non-Goals**:
- Port ContextualProofs (per-logic, context-based)
- Port DeductionTheorem (per-logic, requires structural induction on DerivationTree)
- Port modal-specific theorems (temp_future_derived, etc.)
- Port context-based theorems (ecq, ldi, rdi, lce, rce, ni, ne, de, or_elim_neg_neg)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| DT-free proofs for lce_imp/rce_imp harder than expected | H | M | Research identified concrete proof strategies using Peirce + efq_neg; fallback: mark sorry and track separately |
| LukasiewiczDerived unfolding issues | M | L | Test unfolding early in Phase 1; fallback: work with raw HasImp.imp patterns instead |
| classical_merge DT-free proof complexity | M | M | Research identified contraposition + Peirce strategy; Phase 3 defers to after lce_imp/rce_imp available |
| Naming confusion from K/S inversion | L | M | Document mapping at top of each file; use cslib naming consistently |
| `noncomputable` annotations cause unexpected issues | L | L | Pattern is well-established in Mathlib; use `Nonempty.intro`/`Classical.choice` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Combinators [COMPLETED]

**Goal**: Port the fundamental I/B/C/S combinators that form the foundation for all subsequent propositional theorems.

**Tasks**:
- [ ] Create directory `Cslib/Foundations/Logic/Theorems/`
- [ ] Create `Cslib/Foundations/Logic/Theorems/Combinators.lean` with module header, imports (`Cslib.Foundations.Logic.ProofSystem`), and variable block
- [ ] Port `imp_trans`: transitivity of implication (hypothetical syllogism)
- [ ] Port `mp` helper: modus ponens wrapper (may be unnecessary if `ModusPonens.mp` suffices)
- [ ] Port `identity`: I combinator (SKK construction), `DerivableIn S (imp phi phi)`
- [ ] Port `b_combinator`: B combinator (function composition)
- [ ] Port `theorem_flip`: C combinator (argument flip) -- largest single proof (~120 lines in source)
- [ ] Port `theorem_app1`: single application lemma
- [ ] Port `theorem_app2`: double application lemma (Vireo combinator)
- [ ] Port `pairing`: conjunction introduction combinator
- [ ] Port `dni`: double negation introduction
- [ ] Port `combine_imp_conj`: combine two implications into conjunction
- [ ] Port `combine_imp_conj_3`: combine three implications into nested conjunction
- [ ] Verify `lake build Cslib.Foundations.Logic.Theorems.Combinators` passes

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` - new file, all combinator proofs

**Verification**:
- `lake build Cslib.Foundations.Logic.Theorems.Combinators` passes with zero errors
- All theorems are generic over `[PropositionalHilbert S]`
- No `sorry` occurrences

---

### Phase 2: Propositional Core [COMPLETED]

**Goal**: Port the core propositional theorems including LEM, double negation elimination, and the critical DT-free proofs of lce_imp and rce_imp.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` with imports from Combinators
- [ ] Port `lem`: Law of Excluded Middle (unfolds to `identity neg_phi`)
- [ ] Port `efq_axiom`: EFQ wrapper (`bot -> phi`)
- [ ] Port `peirce_axiom`: Peirce's law wrapper
- [ ] Port `double_negation`: DNE derived from EFQ + Peirce + b_combinator
- [ ] Port `raa`: reductio ad absurdum (`A -> (neg A -> B)`)
- [ ] Port `efq_neg`: ex falso for negation (`neg A -> (A -> B)`)
- [ ] Port `rcp`: reverse contraposition (`(neg A -> neg B) -> (B -> A)`)
- [ ] Derive `lce_imp` without deduction theorem: `(A and B) -> A` using Peirce + efq_neg composition
- [ ] Derive `rce_imp` without deduction theorem: `(A and B) -> B` using similar strategy
- [ ] Verify `lake build Cslib.Foundations.Logic.Theorems.Propositional.Core` passes

**Timing**: 2.5 hours (extra time for DT-free lce_imp/rce_imp proofs)

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` - new file, core propositional theorems

**Verification**:
- `lake build Cslib.Foundations.Logic.Theorems.Propositional.Core` passes with zero errors
- lce_imp and rce_imp proved without deduction theorem (no sorry)
- All theorems generic over `[PropositionalHilbert S]` with `[LukasiewiczDerived F]`

---

### Phase 3: Propositional Connectives [COMPLETED]

**Goal**: Port theorems about derived connectives: classical_merge, iff operations, contraposition, and De Morgan laws.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` with imports from Core
- [ ] Derive `classical_merge` without deduction theorem: `(P -> Q) -> ((neg P -> Q) -> Q)` using contraposition + Peirce
- [ ] Port `iff_intro`: from `A -> B` and `B -> A`, derive `A iff B` (uses pairing)
- [ ] Port `contrapose_imp`: `(A -> B) -> (neg B -> neg A)`
- [ ] Port `contraposition` (meta): from `A -> B`, derive `neg B -> neg A`
- [ ] Port `contrapose_iff`: from `A iff B`, derive `neg A iff neg B` (uses lce_imp/rce_imp)
- [ ] Port `iff_neg_intro`: direct iff_intro for negated formulas
- [ ] Port `demorgan_conj_neg_forward`: `neg(A and B) -> (neg A or neg B)`
- [ ] Port `demorgan_conj_neg_backward`: `(neg A or neg B) -> neg(A and B)` (uses lce_imp/rce_imp)
- [ ] Port `demorgan_conj_neg`: biconditional of above
- [ ] Port `demorgan_disj_neg_forward`: `neg(A or B) -> (neg A and neg B)`
- [ ] Port `demorgan_disj_neg_backward`: `(neg A and neg B) -> neg(A or B)`
- [ ] Port `demorgan_disj_neg`: biconditional of above
- [ ] Verify `lake build Cslib.Foundations.Logic.Theorems.Propositional.Connectives` passes

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` - new file, connective theorems

**Verification**:
- `lake build Cslib.Foundations.Logic.Theorems.Propositional.Connectives` passes with zero errors
- classical_merge proved without deduction theorem
- All De Morgan laws proved

---

### Phase 4: Reasoning and BigConj [COMPLETED]

**Goal**: Port the remaining Reasoning theorem (bi_imp) and create the generic BigConj definition with basic derivability lemmas.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Theorems/Propositional/Reasoning.lean` with imports from Connectives
- [ ] Port `bi_imp`: `(A -> B) -> ((B -> A) -> (A iff B))` (essentially pairing applied)
- [ ] Create `Cslib/Foundations/Logic/Theorems/BigConj.lean`
- [ ] Define `bigconj : {F : Type*} -> [HasBot F] -> [HasImp F] -> [LukasiewiczDerived F] -> List F -> F`
- [ ] Add simp lemmas: `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`
- [ ] Define `neg_bigconj` and its simp lemma
- [ ] Prove `bigconj_mem_derivable`: if `phi in L` and `DerivableIn S (bigconj L)`, then `DerivableIn S phi` (uses lce_imp/rce_imp)
- [ ] Prove `bigconj_derivable_intro`: if all members of L are derivable, then `bigconj L` is derivable (uses pairing)
- [ ] Verify `lake build` for both files passes

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Propositional/Reasoning.lean` - new file, bi_imp
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` - new file, BigConj syntax + derivability

**Verification**:
- `lake build Cslib.Foundations.Logic.Theorems.Propositional.Reasoning` passes
- `lake build Cslib.Foundations.Logic.Theorems.BigConj` passes
- BigConj generic over `[PropositionalHilbert S]` with `[LukasiewiczDerived F]`

---

### Phase 5: Module Aggregator and Final Verification [IN PROGRESS]

**Goal**: Create module aggregator file, verify full build, and confirm zero sorry.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Theorems.lean` as module aggregator importing all Theorems submodules
- [ ] Ensure `Cslib/Foundations/Logic/Theorems.lean` re-exports all submodules via `public import`
- [ ] Run `lake build` (full project) to verify no regressions
- [ ] Run `grep -r sorry Cslib/Foundations/Logic/Theorems/` to confirm zero sorry
- [ ] Verify all theorems use cslib naming (ImplyK, ImplyS) not BimodalLogic naming (prop_s, prop_k)
- [ ] Verify all theorem variable blocks follow the pattern: `variable {F : Type*} [HasBot F] [HasImp F] {S : Type*} [InferenceSystem S F] [PropositionalHilbert S]`

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems.lean` - new file, module aggregator

**Verification**:
- `lake build` (full project) passes with zero errors
- `grep -r sorry Cslib/Foundations/Logic/Theorems/` returns empty
- All files have Apache 2.0 copyright headers
- Module structure matches target layout from research report

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Theorems.Combinators` -- Phase 1
- [ ] `lake build Cslib.Foundations.Logic.Theorems.Propositional.Core` -- Phase 2
- [ ] `lake build Cslib.Foundations.Logic.Theorems.Propositional.Connectives` -- Phase 3
- [ ] `lake build Cslib.Foundations.Logic.Theorems.Propositional.Reasoning` -- Phase 4
- [ ] `lake build Cslib.Foundations.Logic.Theorems.BigConj` -- Phase 4
- [ ] `lake build` (full project) -- Phase 5
- [ ] Zero `sorry` in all Theorems files
- [ ] All theorems generic over `[PropositionalHilbert S]`
- [ ] LukasiewiczDerived unfolding works correctly for neg, and, or definitions
- [ ] lce_imp, rce_imp, classical_merge proved without deduction theorem

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Theorems/Combinators.lean` -- I/B/C/S combinators, imp_trans, pairing, dni
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` -- LEM, DNE, raa, efq_neg, rcp, lce_imp, rce_imp
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` -- classical_merge, iff ops, contraposition, De Morgan
- `Cslib/Foundations/Logic/Theorems/Propositional/Reasoning.lean` -- bi_imp
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` -- bigconj syntax + derivability lemmas
- `Cslib/Foundations/Logic/Theorems.lean` -- module aggregator

## Rollback/Contingency

All changes are additive (new files only). No existing files are modified. Rollback is simply deleting the `Cslib/Foundations/Logic/Theorems/` directory and `Cslib/Foundations/Logic/Theorems.lean`. If DT-free proofs for lce_imp/rce_imp prove infeasible, they can be marked as `sorry` with a tracking comment and addressed when the per-logic deduction theorem becomes available (Task 7). Downstream theorems depending on them (contrapose_iff, demorgan_conj_neg_backward) would similarly carry sorry.
