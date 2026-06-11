# Implementation Plan: S4 Soundness and Completeness

- **Task**: 97 - Establish soundness and completeness for modal logic S4
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: Task 93 (S5 soundness/completeness infrastructure)
- **Research Inputs**: specs/097_modal_s4_soundness_completeness/reports/01_s4-soundness-completeness.md
- **Artifacts**: plans/01_s4-soundness-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Establish sorry-free soundness and completeness theorems for S4 modal logic (reflexive + transitive frames) by creating two new Lean files that reuse the existing parameterized infrastructure. The S4 proofs are a strict subset of the S5 proofs: soundness drops the modalB case and removes the Euclidean frame condition; completeness drops the `canonical_eucl` call and takes only reflexivity + transitivity hypotheses. The existing `S4Axiom` inductive type, `canonical_refl`, `canonical_trans`, and `truth_lemma` are all already parameterized and ready for direct instantiation.

### Research Integration

Key findings from the research report (01_s4-soundness-completeness.md):

1. **S4Axiom** already defined in `Instances.lean:130-153` with 7 constructors (implyK, implyS, efq, peirce, modalK, modalT, modalFour) -- identical to ModalAxiom minus modalB.
2. **All canonical model infrastructure is parameterized**: `canonical_refl` requires h_implyK, h_implyS, h_T; `canonical_trans` requires h_implyK, h_implyS, h_4; `truth_lemma` requires h_implyK, h_implyS, h_efq, h_peirce, h_K, h_T.
3. **Minimal delta from S5**: `s4_axiom_sound` has 7 cases (drops modalB), `s4_completeness` removes the Euclidean condition from `h_valid` and omits the `canonical_eucl` call.
4. **Flat naming recommended**: `S4Soundness.lean` and `S4Completeness.lean` in `Metalogic/` to avoid disrupting existing imports.
5. **No new tactics needed** -- same structural proof techniques as S5.

### Literature References

The plan follows the standard textbook proof structure documented in `specs/097_modal_s4_soundness_completeness/references/s4-canonical-model-completeness.md`, drawn from Hebert (2020), Platzer (2010), and Sergot (2008). Key proof steps:

- **Canonical reflexivity** (from axiom T): Box(A) in S implies A in S via MCS closure -- exactly `mcs_box_closure`
- **Canonical transitivity** (from axiom 4): Box(A) in S implies Box(Box(A)) in S via axiom 4, then chain through accessibility -- exactly `canonical_trans` using `mcs_box_box`
- **Completeness contrapositive**: not-derivable implies {neg(phi)} consistent, Lindenbaum extends to MCS, canonical model is reflexive+transitive, Truth Lemma gives countermodel

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the "Modal metalogic" completed items in ROADMAP.md by extending soundness and completeness from S5 to S4. It falls within the broader modal cube expansion effort (parent task 90).

## Goals & Non-Goals

**Goals**:
- Create `S4Soundness.lean` with sorry-free `s4_axiom_sound`, `s4_soundness`, and `s4_soundness_derivable`
- Create `S4Completeness.lean` with sorry-free `s4_completeness`
- Update `Metalogic.lean` aggregator imports
- Update `Cslib.lean` root imports
- Achieve clean `lake build` with zero sorries

**Non-Goals**:
- Refactoring existing S5 soundness/completeness files
- Creating subdirectory structure (Soundness/S4.lean) -- use flat naming instead
- Proving decidability or finite model property for S4
- Modifying the S4Axiom inductive type or instance registrations

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe polymorphism mismatch between S4Axiom and canonical model | H | L | S4Axiom uses same universe structure as ModalAxiom; verify with `lean_hover_info` on first use |
| Completeness proof by_contra block requires exact term matching for Derivable | M | L | Follow S5 completeness proof term-for-term, substituting S4Axiom constructors |
| Import cycle if S4Completeness imports both Soundness and S4Soundness | M | L | S4Completeness only needs Completeness.lean (which already imports Soundness); S4Soundness is independent |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: S4 Soundness [NOT STARTED]

**Goal**: Create `Cslib/Logics/Modal/Metalogic/S4Soundness.lean` with sorry-free proofs of S4 axiom soundness and the S4 soundness theorem.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/S4Soundness.lean` with module header and imports (`Cslib.Logics.Modal.Metalogic.DerivationTree`)
- [ ] Implement `s4_axiom_sound`: pattern match on 7 `S4Axiom` cases, proving each valid on reflexive + transitive frames
  - Propositional cases (implyK, implyS, efq, peirce): identical to S5 `axiom_sound`
  - modalK: identical to S5
  - modalT: use `h_refl` parameter (reflexive frames)
  - modalFour: use `h_trans` parameter (transitive frames)
  - NOTE: no modalB case (this is the key difference from S5)
- [ ] Implement `s4_soundness`: instantiate parameterized `soundness` theorem with `s4_axiom_sound` callback, taking `DerivationTree (@S4Axiom Atom) Gamma phi` and frame conditions (h_refl, h_trans) -- no h_eucl
- [ ] Implement `s4_soundness_derivable`: instantiate parameterized `soundness_derivable` with `s4_axiom_sound` callback, taking `Derivable (@S4Axiom Atom) phi` and frame conditions
- [ ] Verify with `lean_goal` at key positions; run `lake build Cslib.Logics.Modal.Metalogic.S4Soundness`

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/S4Soundness.lean` -- NEW: ~70 lines

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.S4Soundness` succeeds with no errors
- `lean_verify` on `s4_axiom_sound`, `s4_soundness`, `s4_soundness_derivable` shows no sorry

---

### Phase 2: S4 Completeness [NOT STARTED]

**Goal**: Create `Cslib/Logics/Modal/Metalogic/S4Completeness.lean` with a sorry-free proof of S4 completeness via canonical models.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/S4Completeness.lean` with module header and imports (`Cslib.Logics.Modal.Metalogic.MCS`, `Cslib.Logics.Modal.Metalogic.Soundness`)
- [ ] Implement `s4_completeness` theorem following the canonical model proof structure:
  - Type signature: `theorem s4_completeness (phi : Proposition Atom) (h_valid : forall (World : Type u) (m : Model World Atom), (forall w, m.r w w) -> (forall w1 w2 w3, m.r w1 w2 -> m.r w2 w3 -> m.r w1 w3) -> forall w, Satisfies m w phi) : Derivable (@S4Axiom Atom) phi`
  - Step 1: `by_contra h_not_deriv` -- assume phi is not S4-derivable
  - Step 2: Show `{neg(phi)}` is S4-consistent (same structure as S5 `completeness` proof, replacing `ModalAxiom` constructors with `S4Axiom` constructors)
  - Step 3: Apply `modal_lindenbaum` to extend to MCS
  - Step 4: Construct canonical world `w : CanonicalWorld (@S4Axiom Atom)`
  - Step 5: Apply `truth_lemma` instantiated at S4Axiom constructors (implyK, implyS, efq, peirce, modalK, modalT)
  - Step 6: Apply `h_valid` with `canonical_refl` (using S4Axiom.implyK, S4Axiom.implyS, S4Axiom.modalT) and `canonical_trans` (using S4Axiom.implyK, S4Axiom.implyS, S4Axiom.modalFour) -- NO `canonical_eucl`
  - Step 7: Derive contradiction via `mcs_not_mem_of_neg`
- [ ] Verify with `lean_goal` at key proof positions; run `lake build Cslib.Logics.Modal.Metalogic.S4Completeness`

**Timing**: 1.25 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/S4Completeness.lean` -- NEW: ~100-150 lines

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.S4Completeness` succeeds with no errors
- `lean_verify` on `s4_completeness` shows no sorry

---

### Phase 3: Module Integration [NOT STARTED]

**Goal**: Wire the new S4 files into the module aggregator and root imports, verify clean full build.

**Tasks**:
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.S4Soundness` to `Cslib/Logics/Modal/Metalogic.lean`
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.S4Completeness` to `Cslib/Logics/Modal/Metalogic.lean`
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.S4Soundness` to `Cslib.lean`
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.S4Completeness` to `Cslib.lean`
- [ ] Run full `lake build` and confirm zero errors, zero sorries
- [ ] Run `lean_verify` on all new theorems: `Cslib.Logic.Modal.s4_axiom_sound`, `Cslib.Logic.Modal.s4_soundness`, `Cslib.Logic.Modal.s4_soundness_derivable`, `Cslib.Logic.Modal.s4_completeness`

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` -- add 2 import lines
- `Cslib.lean` -- add 2 import lines

**Verification**:
- Full `lake build` succeeds with zero errors
- All 4 new theorems pass `lean_verify` with no sorry and no additional axioms beyond standard Lean axioms (propext, Quot.sound, Classical.choice)

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.S4Soundness` succeeds (Phase 1)
- [ ] `lake build Cslib.Logics.Modal.Metalogic.S4Completeness` succeeds (Phase 2)
- [ ] Full `lake build` succeeds with zero errors (Phase 3)
- [ ] `lean_verify` on `Cslib.Logic.Modal.s4_axiom_sound` -- no sorry
- [ ] `lean_verify` on `Cslib.Logic.Modal.s4_soundness` -- no sorry
- [ ] `lean_verify` on `Cslib.Logic.Modal.s4_soundness_derivable` -- no sorry
- [ ] `lean_verify` on `Cslib.Logic.Modal.s4_completeness` -- no sorry
- [ ] No existing tests or builds broken by the new imports

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/S4Soundness.lean` -- S4 axiom soundness + soundness theorem (~70 lines)
- `Cslib/Logics/Modal/Metalogic/S4Completeness.lean` -- S4 completeness via canonical models (~100-150 lines)
- `Cslib/Logics/Modal/Metalogic.lean` -- updated aggregator (2 new import lines)
- `Cslib.lean` -- updated root imports (2 new import lines)
- `specs/097_modal_s4_soundness_completeness/plans/01_s4-soundness-completeness.md` -- this plan

## Rollback/Contingency

The changes are purely additive (2 new files + 4 new import lines). Rollback is straightforward:
1. Delete `S4Soundness.lean` and `S4Completeness.lean`
2. Remove the 2 import lines from `Metalogic.lean`
3. Remove the 2 import lines from `Cslib.lean`
4. Run `lake build` to confirm clean state

If a proof gets stuck on a specific step (unlikely given the S5 template):
- Use `lean_goal` to inspect the goal state
- Compare with the corresponding S5 proof in `Soundness.lean` or `Completeness.lean`
- The literature reference (`s4-canonical-model-completeness.md`) provides the mathematical argument for each step
