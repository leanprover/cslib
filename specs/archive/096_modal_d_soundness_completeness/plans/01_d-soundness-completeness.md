# Implementation Plan: Modal D Soundness and Completeness

- **Task**: 96 - Establish soundness and completeness for modal logic D (serial frames)
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: Task 93 (modal system instances, completed)
- **Research Inputs**: specs/096_modal_d_soundness_completeness/reports/01_d-soundness-completeness.md
- **Artifacts**: plans/01_d-soundness-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Establish sorry-free soundness and completeness theorems for modal logic D (KD) over serial Kripke frames. D soundness proves that every DAxiom-derivable formula is valid on serial models. D completeness proves the converse via canonical model construction, showing the canonical model is serial using the D axiom plus NEC on a tautology. The key challenge is adapting the existing S5 box witness and truth lemma to work without axiom T, replacing the `mcs_box_closure` fallback with a D+NEC contradiction argument.

### Research Integration

The research report (01_d-soundness-completeness.md) and literature reference (canonical-model-d-seriality.md, from Open Logic Project rev 9f12419) provide the complete proof structure:

1. **Seriality proof** (OLP Theorem 4.16): If {psi | box psi in S} is inconsistent, then box bot in S; axiom D gives diamond bot in S; NEC on tautology (bot -> bot) gives box(bot -> bot) in S; MP yields bot in S, contradicting MCS.
2. **Box witness** (K-style): The existing `derive_box_from_inconsistency` must be adapted. The S5 version uses `mcs_box_closure` (axiom T) in the fallback case (neg phi not in L). For D, the fallback instead uses the same D+NEC contradiction: all L elements have box-versions in S, L |- bot implies box bot in S via `derive_box_from_box_context`, then D+NEC gives bot in S.
3. **Truth lemma**: Identical to S5 except the box case calls `mcs_box_witness_d` (with h_D) instead of `mcs_box_witness` (with h_T).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the "Modal Cube Expansion" effort (task 90, phase 5) by adding D soundness and completeness as sorry-free Lean 4 proofs, extending the modal metalogic from S5-only to multi-system support.

## Goals & Non-Goals

**Goals**:
- Prove `d_axiom_sound`: every DAxiom is valid on serial frames (6 cases)
- Prove `d_soundness`: wrapper combining `d_axiom_sound` with parameterized `soundness`
- Prove `canonical_serial`: the canonical model for any DAxiom-containing system is serial
- Prove `derive_box_from_inconsistency_d`: K-style box witness consistency without axiom T
- Prove `mcs_box_witness_d`: box witness for D (uses `derive_box_from_inconsistency_d`)
- Prove `truth_lemma_d`: truth lemma using D-style box witness
- Prove `d_completeness`: if phi is valid on all serial models, phi is DAxiom-derivable
- Zero sorry in all files; full `lake build` pass

**Non-Goals**:
- Refactoring the existing S5 truth lemma to share code with D (future task 98)
- Proving the converse direction (seriality implies D-axiom validity) beyond what exists in Basic.lean
- Generalizing to parameterized completeness over arbitrary frame classes

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| D+NEC contradiction argument is harder to formalize than expected | M | L | The argument has 5 clear steps; each uses existing infrastructure (derive_box_from_box_context, modal_closed_under_derivation, mcs_bot_not_mem) |
| Box witness adaptation changes the proof structure significantly | M | M | Follow the existing derive_box_from_inconsistency exactly, only replacing the h_T fallback branch (lines 349-353 of MCS.lean) with the D+NEC argument |
| Universe polymorphism issues in completeness assembly | L | L | Follow the S5 completeness pattern exactly; use `universe u` and `Type u` in the same positions |
| Truth lemma duplication is large | L | L | Accept duplication for now; task 98 can unify later via a witness-callback pattern |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases are strictly sequential since completeness depends on soundness infrastructure and the canonical model seriality proof.

---

### Phase 1: D Soundness [NOT STARTED]

**Goal**: Create DSoundness.lean with `d_axiom_sound`, `d_soundness`, and `d_soundness_derivable`.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/DSoundness.lean` with copyright header and module declaration
- [ ] Import `Cslib.Logics.Modal.Metalogic.DerivationTree` and `Cslib.Logics.Modal.ProofSystem.Instances`
- [ ] Implement `d_axiom_sound`: case analysis on `DAxiom` (6 cases). The 4 propositional cases (implyK, implyS, efq, peirce) are identical to S5. The modalK case needs no frame property. The modalD case uses `Relation.Serial` to obtain a witness world, following the pattern in `Satisfies.d` from Basic.lean
- [ ] Implement `d_soundness`: wrapper calling `soundness` with `d_axiom_sound` as the callback
- [ ] Implement `d_soundness_derivable`: wrapper for derivable formulas (empty context)
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.DSoundness`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DSoundness.lean` - NEW (~50-60 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.DSoundness` passes with zero errors
- `lean_verify` confirms zero sorry/axiom usage

---

### Phase 2: Canonical Seriality and Box Witness for D [NOT STARTED]

**Goal**: Create DCompleteness.lean with the canonical seriality theorem and D-specific box witness.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/DCompleteness.lean` with copyright header, module declaration, imports (MCS.lean, Soundness.lean, Instances)
- [ ] Implement `derive_box_from_inconsistency_d`: adaptation of `derive_box_from_inconsistency` that replaces `h_T` with `h_D`. The `neg phi in L` branch is identical. The `neg phi not in L` branch changes: instead of `mcs_box_closure` to put all L elements in S, use `derive_box_from_box_context` to get `box bot in S`, then: (a) axiom D instantiated at bot gives `box bot -> diamond bot`, so `diamond bot in S`; (b) `diamond bot = (box(bot -> bot)) -> bot`; (c) `bot -> bot` is derivable from implyK, so by NEC `box(bot -> bot)` is derivable, so `box(bot -> bot) in S`; (d) by MP `bot in S`, contradicting `mcs_bot_not_mem`
- [ ] Implement `mcs_box_witness_d`: follows `mcs_box_witness` exactly but passes `derive_box_from_inconsistency_d` instead of `derive_box_from_inconsistency`
- [ ] Implement `canonical_serial`: for any MCS S, show {psi | box psi in S} is consistent using the same D+NEC contradiction, then apply `modal_lindenbaum` to get MCS T with R S T. Signature takes `h_implyK`, `h_implyS`, `h_efq`, `h_K`, `h_D`, returns `exists T : CanonicalWorld Axioms, (CanonicalModel Axioms).r S T`
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.DCompleteness`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DCompleteness.lean` - NEW (partial, ~150-180 lines for this phase)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.DCompleteness` passes with zero errors
- `canonical_serial` type-checks with the correct signature
- `lean_verify` on `canonical_serial` confirms zero sorry

---

### Phase 3: Truth Lemma and D Completeness [NOT STARTED]

**Goal**: Add `truth_lemma_d` and `d_completeness` to DCompleteness.lean.

**Tasks**:
- [ ] Implement `truth_lemma_d`: follows `truth_lemma` from Completeness.lean with one change in the `.box` case -- call `mcs_box_witness_d` (with `h_D`) instead of `mcs_box_witness` (with `h_T`). All other cases (atom, bot, imp) are identical. Signature takes `h_implyK`, `h_implyS`, `h_efq`, `h_peirce`, `h_K`, `h_D` (no `h_T`)
- [ ] Implement `d_completeness`: contrapositive argument following S5 completeness pattern. Assume `not (Derivable DAxiom phi)`, show `{neg phi}` is consistent, extend to MCS M via Lindenbaum, construct canonical world, apply `canonical_serial` to show canonical model is serial, apply `h_valid` to get `Satisfies ... phi`, apply `truth_lemma_d` to get `phi in M`, contradiction with `neg phi in M`
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.DCompleteness`
- [ ] Run `lean_verify` on `d_completeness` to confirm zero sorry

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DCompleteness.lean` - EXTEND (~120-150 additional lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.DCompleteness` passes
- `d_completeness` has the correct type: `Derivable DAxiom phi` given validity on all serial models
- `lean_verify` confirms zero sorry/axiom usage in both DSoundness.lean and DCompleteness.lean

---

### Phase 4: Integration and Final Verification [NOT STARTED]

**Goal**: Wire DSoundness.lean and DCompleteness.lean into the module graph and verify full project build.

**Tasks**:
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.DSoundness` to `Cslib/Logics/Modal/Metalogic.lean`
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.DCompleteness` to `Cslib/Logics/Modal/Metalogic.lean`
- [ ] Add corresponding import lines to `Cslib.lean` (following the pattern of existing Modal imports)
- [ ] Update `Metalogic.lean` module docstring to mention D soundness and completeness
- [ ] Run full `lake build` to verify zero regressions across the entire project
- [ ] Verify DSoundness.lean and DCompleteness.lean have zero sorry with `lean_verify`

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` - ADD 2 import lines + update docstring
- `Cslib.lean` - ADD 2 import lines

**Verification**:
- Full `lake build` passes with zero errors
- `grep -rn "sorry" Cslib/Logics/Modal/Metalogic/DSoundness.lean Cslib/Logics/Modal/Metalogic/DCompleteness.lean` returns nothing
- All existing S5, bimodal, and temporal tests still pass

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.DSoundness` -- scoped build after Phase 1
- [ ] `lake build Cslib.Logics.Modal.Metalogic.DCompleteness` -- scoped build after Phases 2-3
- [ ] `lake build` -- full project build after Phase 4
- [ ] `lean_verify` on `d_axiom_sound`, `d_soundness`, `canonical_serial`, `truth_lemma_d`, `d_completeness` -- zero sorry, zero axiom usage
- [ ] `grep -rn "sorry" Cslib/Logics/Modal/Metalogic/DSoundness.lean Cslib/Logics/Modal/Metalogic/DCompleteness.lean` -- empty output

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/DSoundness.lean` -- NEW (~50-60 lines)
- `Cslib/Logics/Modal/Metalogic/DCompleteness.lean` -- NEW (~280-340 lines)
- `Cslib/Logics/Modal/Metalogic.lean` -- MODIFIED (2 new imports, updated docstring)
- `Cslib.lean` -- MODIFIED (2 new import lines)
- `specs/096_modal_d_soundness_completeness/plans/01_d-soundness-completeness.md` -- this plan

## Rollback/Contingency

All new code is in two new files (DSoundness.lean, DCompleteness.lean). Rollback is trivial: delete the two new files and revert the import additions in Metalogic.lean and Cslib.lean. No existing files are modified in their logic content, only import lists are extended.

If the D+NEC contradiction argument proves harder than expected in Phase 2, the `canonical_serial` proof can be marked [BLOCKED] with a detailed goal state dump, and the remaining phases deferred. The DSoundness.lean from Phase 1 is independently valuable and can be committed regardless.
