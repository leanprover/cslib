# Implementation Plan: Propositional Kripke Semantics

- **Task**: 115 - Propositional Kripke semantics
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: Task 113 (completed -- refactored DerivationTree with axiom predicates)
- **Research Inputs**: specs/115_propositional_kripke_semantics/reports/01_kripke-semantics-research.md
- **Artifacts**: plans/01_kripke-semantics-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Create `Cslib/Logics/Propositional/Semantics/Kripke.lean` defining propositional Kripke semantics with a forcing function parameterized by `bot_forces : World -> Prop`. The file defines a `KripkeModel` structure bundling valuation and upward-closure proofs, an unbundled `IForces` recursive forcing relation on `PL.Proposition`, the `iforces_persistence` theorem by structural induction (CZ Proposition 2.1), and validity predicates `IValid` (intuitionistic) and `MValid` (minimal). The file is standalone -- it does not reuse `Modal.Model` because intuitionistic implication requires universal quantification over accessible worlds, which is incompatible with `Modal.Satisfies`.

### Research Integration

Key findings from the research report integrated into this plan:
- **Standalone structure**: Modal.Satisfies interprets imp locally; intuitionistic forcing interprets imp universally over R-successors. A standalone `IForces` is required.
- **Preorder, not PartialOrder**: Antisymmetry is never used in persistence or downstream proofs. `Preorder World` suffices and is strictly more general.
- **3-case recursion**: `PL.Proposition` has only `atom | bot | imp`; derived connectives (and/or/neg) reduce automatically via abbreviations.
- **Concrete upward-closure hypotheses**: Use `forall w w' p, w <= w' -> v w p -> v w' p` form rather than `IsUpperSet` for easier proof automation. `IsUpperSet`-based lemmas can be added later if needed.
- **imp persistence is automatic**: The imp case of persistence follows directly from transitivity of the preorder -- no inductive hypothesis is needed.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the propositional completeness initiative (parent task 112, Phase 3). It establishes the semantic foundations that tasks 116 (intuitionistic soundness/completeness) and 117 (minimal soundness/completeness) depend on.

## Goals & Non-Goals

**Goals**:
- Define `KripkeModel` structure with valuation, `bot_forces`, and upward-closure proofs
- Define `IForces` forcing relation parameterized by `bot_forces` with 3-case recursion on `PL.Proposition`
- Prove `iforces_persistence` by structural induction (CZ Proposition 2.1)
- Define `IValid` (validity over all intuitionistic Kripke models) and `MValid` (validity over all minimal Kripke models)

**Non-Goals**:
- Soundness or completeness proofs (tasks 116-117)
- Semantic coherence with bivalent `Evaluate` (task 118)
- Derived connective convenience lemmas (and_iff, or_iff, neg_iff) -- these can be added when needed downstream
- Reusing or integrating with `Modal.Model` or `Modal.Satisfies`

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Import resolution for Preorder/IsUpperSet | M | L | Research identified needed imports; verify with `lake build` |
| `IForces` termination checker issue | H | L | Structural recursion on `PL.Proposition` is standard; Lean handles it automatically |
| Namespace collision with existing definitions | L | L | Use `Cslib.Logic.PL` namespace consistent with `Semantics/Basic.lean` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Core Definitions [IN PROGRESS]

**Goal**: Create `Kripke.lean` with KripkeModel structure, IForces forcing relation, IValid, and MValid validity predicates.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Semantics/Kripke.lean` with module header and imports
- [ ] Define `KripkeModel` structure bundling `World` type, `Preorder` instance, valuation `v`, `bot_forces`, and upward-closure proofs
- [ ] Define `IForces` recursive function with 3 cases: atom (valuation lookup), bot (bot_forces), imp (universal quantification over successors)
- [ ] Define `IValid` quantifying over all Preorder worlds, upward-closed valuations, with `bot_forces = fun _ => False`
- [ ] Define `MValid` quantifying over all Preorder worlds, upward-closed valuations, and upward-closed `bot_forces`
- [ ] Verify definitions compile with `lake build Cslib.Logics.Propositional.Semantics.Kripke`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` - create new file (~60-70 lines for definitions)

**Verification**:
- File compiles without errors via `lake build Cslib.Logics.Propositional.Semantics.Kripke`
- `IForces` accepts `PL.Proposition Atom` and produces `Prop`
- `IValid` and `MValid` have the expected types

---

### Phase 2: Persistence Proof and Final Verification [NOT STARTED]

**Goal**: Prove `iforces_persistence` by structural induction on formulas and verify the complete file builds.

**Tasks**:
- [ ] State `iforces_persistence` theorem with hypotheses: valuation upward-closure (`v_uc`), bot_forces upward-closure (`bf_uc`), `w <= w'`, `IForces v bf w phi`
- [ ] Prove atom case: apply `v_uc` directly
- [ ] Prove bot case: apply `bf_uc` directly
- [ ] Prove imp case: introduce successor `u` with `w' <= u`, use `le_trans` to get `w <= u`, apply original hypothesis
- [ ] Add convenience theorem `mvalid_implies_ivalid` showing `MValid phi -> IValid phi` (instantiate `bot_forces` with `fun _ => False`)
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Kripke` to verify complete file
- [ ] Run `lean_verify` on key theorems to check for sorry/axiom usage

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` - add persistence proof and convenience lemma (~30-50 additional lines)

**Verification**:
- `iforces_persistence` compiles without sorry
- `mvalid_implies_ivalid` compiles without sorry
- `lake build Cslib.Logics.Propositional.Semantics.Kripke` succeeds
- `lean_verify` confirms no sorry or non-standard axioms

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Kripke` compiles without errors
- [ ] `lean_verify` on `iforces_persistence` confirms no sorry
- [ ] `lean_verify` on `mvalid_implies_ivalid` confirms no sorry
- [ ] Type signatures match research report specifications (IForces, IValid, MValid)
- [ ] Full project build `lake build` passes (no regressions)

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Kripke.lean` - Propositional Kripke semantics module
- `specs/115_propositional_kripke_semantics/plans/01_kripke-semantics-plan.md` - This plan

## Rollback/Contingency

The implementation creates a single new file with no modifications to existing files. Rollback is trivial: delete `Cslib/Logics/Propositional/Semantics/Kripke.lean`. No downstream files depend on this module until tasks 116-118 are implemented.
