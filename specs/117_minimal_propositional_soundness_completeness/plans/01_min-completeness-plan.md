# Implementation Plan: Task #117

- **Task**: 117 - Minimal propositional soundness and completeness
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: Task 116 (intuitionistic infrastructure)
- **Research Inputs**: specs/117_minimal_propositional_soundness_completeness/reports/01_min-completeness-research.md
- **Artifacts**: plans/01_min-completeness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Prove soundness and completeness of `MinPropAxiom` (Hilbert system with only implyK and implyS, no EFQ) with respect to minimal Kripke semantics (`MValid`). The canonical model uses deductively closed sets (MinTheory) rather than deductively closed consistent sets (IntDCCS), since minimal logic permits worlds where bot is forced. The three files -- MinSoundness, MinLindenbaum, MinCompleteness -- follow the architecture of their intuitionistic counterparts but with structurally simpler proofs throughout (2 axiom cases instead of 3, no EFQ composition, no consistency sub-proof in the implication witness, trivial bot case in truth lemma).

### Research Integration

The research report (01_min-completeness-research.md) identifies the key structural difference: MinTheory drops the consistency requirement from IntDCCS, making `bot_forces w = (Proposition.bot in w.val)` a genuine predicate rather than trivially False. This simplifies the implication witness (no need to prove `S union {phi}` is consistent) and the bot case of the truth lemma (becomes `Iff.rfl`). The report also confirms that `iforces_persistence`, `prop_has_deduction_theorem`, `deductionTheorem`, and `deductionWithMem` from existing infrastructure are already parameterized and can be called directly with Min-specific axiom hypotheses.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No specific ROADMAP.md items mention minimal propositional completeness. This task is part of the propositional completeness expansion (task 112 -> subtasks 113-118) building the foundations for propositional-level metalogic across classical, intuitionistic, and minimal systems.

## Goals & Non-Goals

**Goals**:
- Prove `min_soundness`: every MinPropAxiom-derivable formula is MValid
- Define `MinTheory` as deductively closed sets without consistency requirement
- Prove `min_imp_witness`: implication witness lemma for MinTheory (no EFQ needed)
- Prove `min_truth_lemma`: canonical model truth lemma with trivial bot case
- Prove `min_completeness`: MValid implies Derivable MinPropAxiom
- Prove `min_soundness_completeness`: biconditional equivalence

**Non-Goals**:
- Refactoring IntLindenbaum to be parameterized over axiom systems (would be a separate task)
- Proving relationships between MValid and IValid beyond what already exists in Kripke.lean
- Natural deduction systems for minimal logic

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe polymorphism issues in completeness | H | M | Follow int_completeness pattern exactly with `MValid.{u, u}` |
| min_deriv_imp_of_union proof complexity | M | M | Direct adaptation of int_deriv_imp_of_union with MinPropAxiom substituted |
| Consistency proof for MinPropAxiom | M | L | Lift to IntPropAxiom via MinPropAxiom.toIntProp, reuse int_consistent |
| Import cycle risks | L | L | Clean dependency chain: DT -> MinLindenbaum -> MinCompleteness |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: MinSoundness [COMPLETED]

**Goal**: Prove that every MinPropAxiom-derivable formula is minimally valid (MValid).

**Tasks**:
- [ ] Create `MinSoundness.lean` with module header, imports (Kripke, Derivation)
- [ ] Implement `min_axiom_sound`: 2 axiom cases (implyK uses `iforces_persistence` with both `v_uc` and `bf_uc`; implyS uses `le_trans`)
- [ ] Implement `min_soundness`: 4-case match on DerivationTree (ax, assumption, modus_ponens, weakening) with `val` and `bot_forces` as explicit parameters
- [ ] Implement `min_soundness_derivable`: wrapper from `Derivable MinPropAxiom phi` to `MValid phi`
- [ ] Verify with `lake build Cslib.Logics.Propositional.Metalogic.MinSoundness`

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` - Create new file (~80 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.MinSoundness` succeeds with no errors or sorries
- `lean_verify` confirms no axiom usage beyond Lean core

---

### Phase 2: MinLindenbaum [COMPLETED]

**Goal**: Define MinTheory (deductively closed sets without consistency) and prove the implication witness lemma, the compilation/cut lemma, and consistency of MinPropAxiom.

**Tasks**:
- [ ] Create `MinLindenbaum.lean` with module header, imports (DeductionTheorem, MCS for PropSetConsistent)
- [ ] Define `min_h_implyK` and `min_h_implyS` helper hypotheses for MinPropAxiom
- [ ] Define `MinTheory S` as deductively closed set (no consistency requirement): `forall L phi, (forall x in L, x in S) -> Deriv MinPropAxiom L phi -> phi in S`
- [ ] Prove `min_theory_imp_property`: MP closure for MinTheory (if `phi -> psi in S` and `phi in S` then `psi in S`)
- [ ] Prove `min_deriv_from_closure_to_S`: compilation lemma (adapt from int_deriv_from_closure_to_S with MinPropAxiom)
- [ ] Prove `min_deriv_imp_of_union`: cut lemma (adapt from int_deriv_imp_of_union with MinPropAxiom)
- [ ] Define `min_deductive_closure` and prove `min_subset_deductive_closure`, `min_deductive_closure_is_theory`
- [ ] Prove `min_imp_witness`: given MinTheory S with `phi -> psi not in S`, produce T with `S subset T`, `MinTheory T`, `phi in T`, `psi not in T` -- no consistency sub-proof needed
- [x] Implement `lift_min_to_int`: lift MinPropAxiom derivations to IntPropAxiom via `MinPropAxiom.toIntProp` *(deviation: altered -- lifted directly to PropositionalAxiom via `lift_min_to_cl` to avoid IntLindenbaum import)*
- [x] Prove `min_consistent`: `not (Derivable MinPropAxiom bot)` via lifting + int_consistent *(deviation: altered -- uses `prop_soundness` directly instead of `int_consistent`)*
- [ ] Prove `min_theorems_theory`: `{psi | Derivable MinPropAxiom psi}` is a MinTheory
- [ ] Verify with `lake build Cslib.Logics.Propositional.Metalogic.MinLindenbaum`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` - Create new file (~250 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.MinLindenbaum` succeeds with no errors or sorries
- MinTheory definition does NOT include any consistency requirement
- min_imp_witness proof does NOT reference EFQ or int_neg_phi_imp_psi

---

### Phase 3: MinCompleteness [NOT STARTED]

**Goal**: Build the canonical Kripke model from MinTheory worlds, prove the truth lemma, and derive the completeness theorem and biconditional.

**Tasks**:
- [ ] Create `MinCompleteness.lean` with module header, imports (Kripke, MinSoundness, MinLindenbaum)
- [ ] Define `MinCanonicalWorld Atom` as subtype of MinTheory
- [ ] Define `Preorder` instance on MinCanonicalWorld via set inclusion
- [ ] Define `min_canonical_val w p := Proposition.atom p in w.val` and prove `min_canonical_val_upward_closed`
- [ ] Define `min_bot_forces w := Proposition.bot in w.val` and prove `min_bot_forces_upward_closed`
- [ ] Prove `min_truth_lemma` by structural induction on phi (3 cases):
  - atom: `Iff.rfl` (identical to intuitionistic)
  - bot: `Iff.rfl` (trivial -- the key simplification vs intuitionistic)
  - imp: forward uses `min_imp_witness`; backward uses `min_theory_imp_property`
- [ ] Prove `min_completeness`: by_contra, construct W0 from min_theorems_theory, derive contradiction via min_truth_lemma. Use `MValid.{u, u}` for universe matching
- [ ] Prove `min_soundness_completeness`: biconditional wrapping min_completeness and min_soundness_derivable
- [ ] Verify with `lake build Cslib.Logics.Propositional.Metalogic.MinCompleteness`

**Timing**: 1.25 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` - Create new file (~120 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.MinCompleteness` succeeds with no errors or sorries
- bot case of min_truth_lemma is `Iff.rfl` (not a multi-step proof)
- min_completeness uses `MValid.{u, u}` to match canonical model universes
- `lean_verify` on `min_soundness_completeness` confirms no axiom usage beyond Lean core

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Metalogic.MinSoundness` -- no errors
- [ ] `lake build Cslib.Logics.Propositional.Metalogic.MinLindenbaum` -- no errors
- [ ] `lake build Cslib.Logics.Propositional.Metalogic.MinCompleteness` -- no errors
- [ ] Full `lake build` passes with no regressions in existing modules
- [ ] No `sorry` in any of the three files
- [ ] `lean_verify` on `min_soundness_completeness` confirms axiom safety

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` -- Soundness theorem (~80 lines)
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` -- MinTheory + implication witness (~250 lines)
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` -- Canonical model + completeness (~120 lines)

## Rollback/Contingency

All three files are new additions with no modifications to existing files. Rollback is simply deleting the three new files. If individual phases encounter blockers:
- Phase 1 blocked: unlikely given 2-case simplification of existing 3-case proof
- Phase 2 blocked: most likely at min_imp_witness or min_deriv_imp_of_union; fall back to closer adaptation of Int proofs
- Phase 3 blocked: most likely at universe issues in min_completeness; follow int_completeness pattern exactly
