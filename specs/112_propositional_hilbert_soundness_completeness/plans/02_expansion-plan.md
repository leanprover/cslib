# Implementation Plan: Task #112 (Expansion)

- **Task**: 112 - Establish soundness and completeness for propositional Hilbert proof systems
- **Status**: [NOT STARTED]
- **Effort**: 12 hours (across 6 sub-tasks)
- **Dependencies**: None (existing MCS and modal infrastructure sufficient)
- **Research Inputs**: specs/112_propositional_hilbert_soundness_completeness/reports/02_team-research.md
- **Artifacts**: plans/02_expansion-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

This is an expansion plan for meta-task 112. Each phase corresponds to a new sub-task to be created. The goal is to establish soundness and completeness for all three propositional Hilbert systems: classical (HilbertCl), intuitionistic (HilbertInt), and minimal (HilbertMin). The work requires refactoring the propositional `DerivationTree` to be parameterized over axiom predicates (matching the modal pattern), defining classical bivalent semantics, building propositional Kripke semantics with a parameterized forcing function, constructing prime-theory-based canonical models for intuitionistic completeness, adapting the canonical model for minimal logic with a different bottom-forcing clause, and integrating all modules. Definition of done: `lake build` succeeds with all three soundness and completeness theorems proven without `sorry`.

### Research Integration

The team research report (Round 2, 4 teammates) established:
- Classical completeness is a direct simplification of modal K completeness (~250 lines, all MCS infrastructure exists).
- The propositional `DerivationTree` must be parameterized to support multiple axiom sets (user design decision: uniform with modal pattern).
- Intuitionistic/minimal completeness requires prime theories (not MCS) and a new Kripke forcing relation.
- The forcing function should be parameterized with a `bot_forces` parameter to handle both intuitionistic and minimal semantics uniformly.
- The deduction theorem uses only K+S axioms, so it is compatible with all three levels without modification.
- Estimated total: 750-1050 lines across 8-10 new files.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Parameterize `DerivationTree` over axiom predicates, creating `IntPropAxiom` and `MinPropAxiom` types
- Register `IntuitionisticHilbert HilbertInt` and `MinimalHilbert HilbertMin` instances
- Prove classical soundness and completeness with respect to bivalent truth-value semantics
- Define propositional Kripke semantics with parameterized forcing (reusing `Modal.Model`)
- Prove intuitionistic soundness and completeness via prime-theory canonical model
- Prove minimal soundness and completeness with different bottom-forcing clause
- Integrate all new modules into `Cslib.lean`

**Non-Goals**:
- Natural deduction unification (Hilbert systems only)
- Hintikka system formalization (using prime theory approach instead)
- Godel translation connecting intuitionistic and modal S4
- Decidability results
- Disjunction property for intuitionistic logic

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| DerivationTree refactor breaks downstream code | H | M | Phase 1 includes updating all 4 affected files; run `lake build` after each file change |
| Prime theory Lindenbaum lemma is harder than estimated | M | M | The generic `set_lindenbaum` in Consistency.lean provides the Zorn pattern; adapt rather than build from scratch |
| Intuitionistic Truth Lemma imp case requires complex universal quantification | H | M | Follow CZ Chapter 5 canonical model method step-by-step; the modal Truth Lemma provides structural template |
| Parameterized forcing function creates typeclass resolution issues | M | L | Use explicit hypothesis parameters rather than typeclasses for Kripke model constraints |
| DeductionTheorem.lean height proofs break after DerivationTree refactor | M | M | The deduction theorem only uses K+S axioms; refactored tree should work if height structure is preserved |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |
| 3 | 4 | 1, 3 |
| 4 | 5 | 1, 3, 4 |
| 5 | 6 | 1, 2, 3, 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Refactor DerivationTree and Create Axiom Types [NOT STARTED]

**Goal**: Parameterize the propositional `DerivationTree` over an axiom predicate (matching the modal `DerivationTree Axioms Gamma phi` pattern), create `IntPropAxiom` and `MinPropAxiom` inductive types, and register `HilbertInt`/`HilbertMin` instances. This is prerequisite infrastructure for all subsequent phases.

**Tasks**:
- [ ] Parameterize `DerivationTree` in `Derivation.lean`: change signature from `DerivationTree : List (PL.Proposition Atom) -> PL.Proposition Atom -> Type` to `DerivationTree (Axioms : PL.Proposition Atom -> Prop) : List (PL.Proposition Atom) -> PL.Proposition Atom -> Type`
- [ ] Update the `ax` constructor to take `(h : Axioms phi)` instead of `(h : PropositionalAxiom phi)`
- [ ] Parameterize `Deriv`, `Derivable`, `propDerivationSystem` over `Axioms`
- [ ] Update all combinators (`mp_deriv`, `weakening_deriv`, `assumption_deriv`) to carry the `Axioms` parameter
- [ ] Update `DeductionTheorem.lean`: parameterize `HasHilbertTree` instance, `deductionWithMem`, `deductionTheorem`, and `prop_has_deduction_theorem` over `Axioms`
- [ ] Update `MCS.lean`: parameterize abbreviations (`PropSetConsistent`, `PropSetMaximalConsistent`) and all theorems over `Axioms` and the corresponding `propDerivationSystem Axioms`
- [ ] Update `Instances.lean`: update `HilbertCl` instances to use `DerivationTree PropositionalAxiom` (the refactored parameterized tree instantiated at the classical axiom set)
- [ ] Create `IntPropAxiom` inductive type in `Axioms.lean` (constructors: `implyK`, `implyS`, `efq` -- no `peirce`)
- [ ] Create `MinPropAxiom` inductive type in `Axioms.lean` (constructors: `implyK`, `implyS` -- no `efq`, no `peirce`)
- [ ] Create `IntMinInstances.lean` with `InferenceSystem`, `ModusPonens`, `HasAxiom*`, `IntuitionisticHilbert HilbertInt`, and `MinimalHilbert HilbertMin` instance registrations
- [ ] Run `lake build` to verify no regressions

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- add `IntPropAxiom`, `MinPropAxiom`
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- parameterize `DerivationTree`
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` -- update to parameterized tree
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` -- update to parameterized tree
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` -- update `HilbertCl` instances
- `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` -- new file for `HilbertInt`/`HilbertMin`

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.Instances` succeeds (existing classical path)
- `lake build Cslib.Logics.Propositional.ProofSystem.IntMinInstances` succeeds (new instances)
- `lake build Cslib.Logics.Propositional.Metalogic.MCS` succeeds (MCS still works)
- Full `lake build` passes with no sorry

---

### Phase 2: Classical Soundness and Completeness [NOT STARTED]

**Goal**: Define bivalent truth-value semantics for classical propositional logic and prove soundness and completeness of `HilbertCl` with respect to tautologies. This is a direct simplification of the existing modal K completeness proof.

**Tasks**:
- [ ] Create `Semantics/Basic.lean` with `Valuation` type (`Atom -> Prop`), `Evaluate` recursive function, `Tautology` definition (`forall v, Evaluate v phi`)
- [ ] Prove basic evaluation lemmas: `eval_bot`, `eval_imp`, `eval_atom`
- [ ] Create `Metalogic/Soundness.lean` with `prop_axiom_sound` (4 cases: K, S, EFQ, Peirce -- all trivial by unfolding) and `prop_soundness` (by induction on derivation tree)
- [ ] Create `Metalogic/Completeness.lean` with `canonicalValuation` mapping MCS to valuations, `prop_truth_lemma` (by structural induction on formulas; imp case uses `prop_implication_property` and `prop_closed_under_derivation`), and `prop_completeness` theorem
- [ ] Run `lake build` on new modules

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Basic.lean` -- new file
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` -- new file
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` -- new file

**Verification**:
- `prop_soundness : Derivable PropositionalAxiom phi -> Tautology phi` proven
- `prop_completeness : Tautology phi -> Derivable PropositionalAxiom phi` proven
- `lake build Cslib.Logics.Propositional.Metalogic.Completeness` succeeds
- No sorry in any file

---

### Phase 3: Propositional Kripke Semantics [NOT STARTED]

**Goal**: Define propositional Kripke semantics with a parameterized forcing function using `Modal.Model` structure with partial-order and persistence constraints as hypotheses. This provides the semantic foundation for intuitionistic and minimal completeness.

**Tasks**:
- [ ] Create `Semantics/Kripke.lean` with propositional Kripke model definition reusing `Modal.Model` (World, Atom types with accessibility relation `r` and valuation `v`)
- [ ] Define `IForces` (intuitionistic forcing) parameterized by `bot_forces : World -> Prop`:
  - `IForces bot_forces m w (atom p) = m.v w p`
  - `IForces bot_forces m w bot = bot_forces w`
  - `IForces bot_forces m w (imp phi psi) = forall w', m.r w w' -> IForces bot_forces m w' phi -> IForces bot_forces m w' psi`
- [ ] State persistence hypotheses: partial order on `r` (reflexive + transitive) and monotonicity of `v` (if `m.v w p` and `m.r w w'` then `m.v w' p`) and upward-closure of `bot_forces`
- [ ] Prove `iforces_persistence`: for all formulas, if `IForces bot_forces m w phi` and `m.r w w'`, then `IForces bot_forces m w' phi` (by structural induction on formulas, given persistence hypotheses)
- [ ] Define `IValid phi` = validity over all intuitionistic frames (instantiated with `bot_forces = fun _ => False`)
- [ ] Define `MValid phi` = validity over all minimal frames (instantiated with upward-closed `bot_forces`)

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` -- new file

**Verification**:
- `iforces_persistence` proven for all formula constructors
- `IValid` and `MValid` definitions type-check
- `lake build Cslib.Logics.Propositional.Semantics.Kripke` succeeds
- No sorry

---

### Phase 4: Intuitionistic Soundness and Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness of `HilbertInt` with respect to intuitionistic Kripke semantics. This is the most complex phase, requiring a prime theory Lindenbaum lemma, canonical Kripke model construction, and an intuitionistic Truth Lemma.

**Tasks**:
- [ ] Create `Metalogic/IntSoundness.lean`:
  - Prove `int_axiom_sound` for `IntPropAxiom` (3 cases: K, S, EFQ -- all valid in intuitionistic Kripke models)
  - Prove `int_soundness : Derivable IntPropAxiom phi -> IValid phi` by induction on derivation tree (no necessitation case)
- [ ] Create `Metalogic/IntLindenbaum.lean`:
  - Define `PrimeTheory` predicate: deductively closed, consistent, has disjunction property (if `phi \/ psi in S` then `phi in S` or `psi in S`, expressed via the implication encoding)
  - Prove `int_lindenbaum`: every consistent set extends to a prime deductively-closed theory (adapting the Zorn pattern from `Consistency.lean` but targeting the disjunction property instead of negation completeness)
  - Prove key prime theory properties: `prime_closed_under_derivation`, `prime_implication_property`
- [ ] Create `Metalogic/IntCompleteness.lean`:
  - Construct canonical Kripke model: worlds = prime theories, accessibility = set inclusion, valuation = atom membership
  - Verify canonical model satisfies persistence hypotheses (monotonicity follows from set inclusion)
  - Prove `int_truth_lemma : phi in w <-> IForces bot_forces m w phi` by structural induction on formulas
    - `atom` case: by definition
    - `bot` case: by consistency of prime theories (bot not in any prime theory)
    - `imp` case: forward direction uses universal quantification over accessible worlds and deductive closure; backward direction uses prime theory Lindenbaum and deduction theorem
  - Prove `int_completeness : IValid phi -> Derivable IntPropAxiom phi` by contradiction using canonical model

**Timing**: 3.5 hours

**Depends on**: 1, 3

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` -- new file
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` -- new file
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` -- new file

**Verification**:
- `int_soundness : Derivable IntPropAxiom phi -> IValid phi` proven
- `int_completeness : IValid phi -> Derivable IntPropAxiom phi` proven
- `lake build Cslib.Logics.Propositional.Metalogic.IntCompleteness` succeeds
- No sorry

---

### Phase 5: Minimal Soundness and Completeness [NOT STARTED]

**Goal**: Prove soundness and completeness of `HilbertMin` with respect to minimal Kripke semantics. This reuses the intuitionistic infrastructure from Phase 4 with a different `bot_forces` instantiation (upward-closed valuation instead of `fun _ => False`).

**Tasks**:
- [ ] Create `Metalogic/MinSoundness.lean`:
  - Prove `min_axiom_sound` for `MinPropAxiom` (2 cases: K, S only -- no EFQ, no Peirce)
  - Prove `min_soundness : Derivable MinPropAxiom phi -> MValid phi` by induction on derivation tree
- [ ] Create `Metalogic/MinCompleteness.lean`:
  - Adapt canonical Kripke model from Phase 4: worlds = prime theories, same accessibility, but `bot_forces w = (Proposition.bot in w)` (bot can be forced at some worlds)
  - Verify upward-closure of `bot_forces` (follows from set inclusion accessibility and deductive closure)
  - Prove `min_truth_lemma`: same structure as intuitionistic Truth Lemma but with different bot case (bot in w iff bot_forces w, which is true by definition)
  - Prove `min_completeness : MValid phi -> Derivable MinPropAxiom phi` by contradiction using canonical model

**Timing**: 1.5 hours

**Depends on**: 1, 3, 4

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` -- new file
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` -- new file

**Verification**:
- `min_soundness : Derivable MinPropAxiom phi -> MValid phi` proven
- `min_completeness : MValid phi -> Derivable MinPropAxiom phi` proven
- `lake build Cslib.Logics.Propositional.Metalogic.MinCompleteness` succeeds
- No sorry

---

### Phase 6: Module Integration [NOT STARTED]

**Goal**: Update `Cslib.lean` imports to include all new modules, prove a semantic coherence theorem connecting propositional and modal semantics via `FromPropositional.lean`, and verify the full project builds.

**Tasks**:
- [ ] Update `Cslib.lean` to import all new modules:
  - `Cslib.Logics.Propositional.ProofSystem.IntMinInstances`
  - `Cslib.Logics.Propositional.Semantics.Basic`
  - `Cslib.Logics.Propositional.Semantics.Kripke`
  - `Cslib.Logics.Propositional.Metalogic.Soundness`
  - `Cslib.Logics.Propositional.Metalogic.Completeness`
  - `Cslib.Logics.Propositional.Metalogic.IntSoundness`
  - `Cslib.Logics.Propositional.Metalogic.IntLindenbaum`
  - `Cslib.Logics.Propositional.Metalogic.IntCompleteness`
  - `Cslib.Logics.Propositional.Metalogic.MinSoundness`
  - `Cslib.Logics.Propositional.Metalogic.MinCompleteness`
- [ ] Add semantic coherence theorem in `FromPropositional.lean` (or a new companion file): propositional tautology implies modal validity for propositional formulas (~20-30 lines)
- [ ] Run full `lake build` and verify no sorry in any new file
- [ ] Run `lean_verify` on key theorems: `prop_completeness`, `int_completeness`, `min_completeness`

**Timing**: 1.5 hours

**Depends on**: 1, 2, 3, 4, 5

**Files to modify**:
- `Cslib.lean` -- add imports
- `Cslib/Logics/Modal/FromPropositional.lean` -- add coherence theorem (or new companion file)

**Verification**:
- Full `lake build` succeeds
- All six main theorems verified: `prop_soundness`, `prop_completeness`, `int_soundness`, `int_completeness`, `min_soundness`, `min_completeness`
- No sorry in any file across the project
- `lean_verify` confirms no axiom usage beyond standard Lean axioms

## Testing & Validation

- [ ] `lake build` passes after Phase 1 (refactor introduces no regressions)
- [ ] Each soundness theorem type-checks: derivability implies validity for the appropriate semantics
- [ ] Each completeness theorem type-checks: validity implies derivability
- [ ] Intuitionistic Truth Lemma correctly handles the `imp` case with universal quantification
- [ ] Minimal Truth Lemma correctly handles the `bot` case with upward-closed `bot_forces`
- [ ] Persistence lemma holds for all formula constructors under both intuitionistic and minimal forcing
- [ ] Full `lake build` succeeds at end of Phase 6 with zero sorry
- [ ] `lean_verify` on all six main theorems shows no non-standard axiom usage

## Artifacts & Outputs

- `specs/112_propositional_hilbert_soundness_completeness/plans/02_expansion-plan.md` (this file)
- Sub-tasks to be created (6 new tasks) via `/task --expand 112`
- New Lean files (across sub-tasks):
  - `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean`
  - `Cslib/Logics/Propositional/Semantics/Basic.lean`
  - `Cslib/Logics/Propositional/Semantics/Kripke.lean`
  - `Cslib/Logics/Propositional/Metalogic/Soundness.lean`
  - `Cslib/Logics/Propositional/Metalogic/Completeness.lean`
  - `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean`
  - `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean`
  - `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean`
  - `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean`
  - `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean`
- Modified Lean files: `Axioms.lean`, `Derivation.lean`, `DeductionTheorem.lean`, `MCS.lean`, `Instances.lean`, `Cslib.lean`, `FromPropositional.lean`

## Rollback/Contingency

- Phase 1 (refactor) is the highest-risk phase. If the parameterization breaks downstream modal code, revert to creating separate `IntDerivationTree`/`MinDerivationTree` types rather than parameterizing the existing one. This is more code duplication but avoids touching existing files.
- If the prime theory Lindenbaum lemma (Phase 4) proves too difficult, fall back to the Hintikka system approach from CZ Chapter 2, which is more complex but better documented in the literature.
- If minimal completeness (Phase 5) has issues with `bot_forces` upward-closure, fall back to defining a separate `MinModel` type with an explicit `bot_val` field rather than parameterizing `IForces`.
- Each phase is independently committable. If any phase is blocked, mark it `[BLOCKED]` and proceed with non-dependent phases.
