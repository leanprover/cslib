# Implementation Plan: Modal D Soundness and Completeness (Revised)

- **Task**: 96 - Establish soundness and completeness for modal logic D (serial frames)
- **Status**: [IMPLEMENTING]
- **Effort**: 3 hours
- **Dependencies**: Task 93 (modal system instances, completed)
- **Research Inputs**: specs/096_modal_d_soundness_completeness/reports/01_d-soundness-completeness.md
- **Artifacts**: plans/02_d-soundness-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Establish sorry-free soundness and completeness theorems for modal logic D (KD) over serial Kripke frames, following the proof structure from Blackburn, de Rijke, Venema "Modal Logic" (2002), Chapter 4 -- specifically Theorem 4.28 clause 3 (seriality is canonical) and the supporting infrastructure (Definition 4.18, Lemmas 4.19-4.21, Theorem 4.22). D soundness verifies that every DAxiom-derivable formula is valid on serial models. D completeness proves the converse via the completeness-via-canonicity method: construct the canonical model, show its frame is serial (Theorem 4.28 clause 3), then apply the Canonical Model Theorem (Theorem 4.22).

### Research Integration

The research report (01_d-soundness-completeness.md) provides codebase infrastructure analysis:
- `DAxiom` inductive (6 constructors) in `ProofSystem/Instances.lean` -- fully reusable
- Parameterized `soundness` theorem in `Soundness.lean` -- reusable with D-specific callback
- `CanonicalWorld`, `CanonicalModel` in `Completeness.lean` -- reusable definitions
- `derive_box_from_box_context`, `derive_box_from_inconsistency`, `mcs_box_witness` in `MCS.lean` -- the S5 versions use `h_T` (axiom T); D versions must replace the T-dependent fallback
- `Satisfies.d` in `Basic.lean` validates D on serial frames via `Relation.Serial`

### Prior Plan Reference

The prior plan (01_d-soundness-completeness.md) established the 4-phase structure and identified the correct key challenge: adapting `derive_box_from_inconsistency` to replace the `mcs_box_closure` (axiom T) fallback with a D+NEC contradiction argument. The effort estimate of 3 hours is validated. This revision adds explicit Blackburn cross-references, aligns the seriality proof step-by-step with Theorem 4.28 clause 3, and clarifies the precise Lean encoding of each Blackburn proof step.

### Literature Reference

**Primary source**: Blackburn, de Rijke, Venema, "Modal Logic" (Cambridge, 2002), Chapter 4.
Extracted reference: `specs/096_modal_d_soundness_completeness/references/blackburn-ch4-completeness.md`

**Key theorems used**:
- Definition 4.18 (Canonical Model) -- worlds = MCSs, R^Lambda wv iff box psi in w implies psi in v
- Lemma 4.19 -- R^Lambda wv iff box psi in w implies psi in v (equivalent characterization)
- Lemma 4.20 (Existence Lemma) -- if diamond phi in w, exists v with R wv and phi in v
- Lemma 4.21 (Truth Lemma) -- Satisfies(canonical, w, phi) iff phi in w
- Theorem 4.22 (Canonical Model Theorem) -- every normal logic is strongly complete w.r.t. its canonical model
- **Theorem 4.28 clause 3 (KD seriality is canonical)** -- the central new proof for this task

### Roadmap Alignment

This task advances the "Modal Cube Expansion" effort (task 90, phase 5) by adding D soundness and completeness as sorry-free Lean 4 proofs, extending the modal metalogic from S5-only to multi-system support.

## Goals & Non-Goals

**Goals**:
- Prove `d_axiom_sound`: every DAxiom is valid on serial frames (6 cases), following Blackburn Definition 4.9
- Prove `d_soundness`: wrapper combining `d_axiom_sound` with parameterized `soundness`
- Prove `canonical_serial`: the canonical model for any DAxiom-containing system is serial, following Blackburn Theorem 4.28 clause 3 step-by-step
- Prove `derive_box_from_inconsistency_d`: box witness consistency argument using D+NEC instead of T, adapting the fallback case (MCS.lean lines 349-354)
- Prove `mcs_box_witness_d`: box witness for D using `derive_box_from_inconsistency_d`
- Prove `truth_lemma_d`: truth lemma using D-style box witness (Blackburn Lemma 4.21 specialized)
- Prove `d_completeness`: completeness via canonicity (Blackburn Proposition 4.12 + Theorem 4.28), following the S5 completeness proof pattern
- Zero sorry in all files; full `lake build` pass

**Non-Goals**:
- Refactoring the existing S5 truth lemma to share code with D (future task 98)
- Proving the converse direction (seriality implies D-axiom validity) beyond what exists in Basic.lean
- Generalizing to parameterized completeness over arbitrary frame classes

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| D+NEC contradiction argument harder to formalize than expected | M | L | Blackburn Theorem 4.28 clause 3 gives 5 explicit steps; each maps to existing infrastructure (derive_box_from_box_context, modal_closed_under_derivation, mcs_bot_not_mem) |
| Box witness adaptation changes the proof structure significantly | M | M | Follow existing derive_box_from_inconsistency exactly, only replacing the h_T fallback branch (MCS.lean lines 349-353) with the D+NEC argument |
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

### Phase 1: D Soundness [COMPLETED]

**Goal**: Create Soundness/D.lean with `d_axiom_sound`, `d_soundness`, and `d_soundness_derivable`.

**Blackburn cross-reference**: Definition 4.9 (Soundness) -- "Proving soundness boils down to checking validity of the axioms" (p.195). Table 4.1: KD is sound w.r.t. serial (right-unbounded) frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Soundness/D.lean` with copyright header and module declaration
- [ ] Import `Cslib.Logics.Modal.Metalogic.Soundness` (for parameterized `soundness`) and `Cslib.Logics.Modal.ProofSystem.Instances` (for `DAxiom`)
- [ ] Implement `d_axiom_sound : DAxiom phi -> Model World Atom -> Relation.Serial m.r -> World -> Satisfies m w phi`
  - Case analysis on `DAxiom` (6 cases):
    - `implyK`, `implyS`, `efq`, `peirce`: Pure propositional, identical to S5 `axiom_sound` cases
    - `modalK`: Distribution axiom, needs no frame property (same as S5)
    - `modalD`: **Soundness of D axiom on serial frames** -- Given `box phi` at w, obtain witness w' from `hSer.serial w` (Relation.Serial provides LeftTotal), then `phi` holds at w', so `diamond phi` holds at w. This follows the pattern of `Satisfies.d` in Basic.lean, but proved directly on the raw `Satisfies` type for `DAxiom.modalD`
- [ ] Implement `d_soundness`: wrapper calling parameterized `soundness` with `d_axiom_sound` as callback
- [ ] Implement `d_soundness_derivable`: wrapper for derivable formulas (empty context)
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.Soundness.D`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Soundness/D.lean` - NEW (~50-60 lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Soundness.D` passes with zero errors
- `lean_verify` confirms zero sorry/axiom usage

---

### Phase 2: Canonical Seriality and Box Witness for D [COMPLETED]

**Goal**: Create Completeness/D.lean with `canonical_serial` (Blackburn Theorem 4.28 clause 3) and D-specific box witness (`derive_box_from_inconsistency_d`, `mcs_box_witness_d`).

**Blackburn cross-reference**: Theorem 4.28 clause 3 is the central theorem. The proof is:

> "For the third claim, it suffices to show that the canonical model for KD is right-unbounded [serial]. Let w be any point in the canonical model for KD. We must show that there exists a v in this model such that R^KD wv. As w is a KD-MCS it contains box p -> diamond p, thus by closure under uniform substitution it contains box top -> diamond top. Moreover, as top belongs to all normal modal logics, by generalization box top does too; so box top belongs to KD, hence by modus ponens diamond top in w. Hence, by the Existence Lemma, w has an R^KD successor v."

**Blackburn-to-Lean step mapping for `canonical_serial`**:

| Blackburn Step | Lean Implementation | Infrastructure |
|----------------|---------------------|----------------|
| "w is a KD-MCS, contains box p -> diamond p" | `h_D phi` gives `Axioms (box phi -> diamond phi)` for any phi | Axiom hypothesis `h_D` |
| "by uniform substitution, contains box top -> diamond top" | Instantiate `h_D` at `Proposition.top` (= `bot -> bot`). This gives `Axioms (box top -> diamond top)`. Since w is MCS, `box top -> diamond top in w` | `modal_closed_under_derivation` with derivation from axiom |
| "top belongs to all normal modal logics" | `top = bot -> bot` is derivable: `implyK bot bot` gives `bot -> (bot -> bot)`, then simplify; or directly from `h_implyK` | Propositional derivation |
| "by generalization, box top does too" | From derivation of `top`, apply `DerivationTree.necessitation` to get derivation of `box top`, then `modal_closed_under_derivation` to get `box top in w` | `necessitation` + `modal_closed_under_derivation` |
| "by modus ponens, diamond top in w" | Apply `modal_implication_property` with `box top -> diamond top in w` and `box top in w` | `modal_implication_property` |
| "by the Existence Lemma, w has successor v" | Blackburn Lemma 4.20. In Lean: `diamond top in w` means `(box (top -> bot)) -> bot in w`, i.e., `(box neg_top) -> bot in w`. The Existence Lemma constructs v with R wv. But we can use a simpler route: show `{psi | box psi in w}` is consistent, extend to MCS T via Lindenbaum, then R w T by construction | `modal_lindenbaum` + construction |

**Alternative (simpler) implementation of `canonical_serial`**: Instead of going through diamond top and the Existence Lemma (which requires a separate formalization), we prove seriality directly by showing `W = {psi | box psi in w}` is consistent:
1. Suppose W is inconsistent: exists L subset W with L |- bot
2. Since each psi_i in L has box psi_i in w, by `derive_box_from_box_context`: box bot in w
3. By axiom D instantiated at bot: `box bot -> diamond bot` in w (via `h_D` + `modal_closed_under_derivation`)
4. So `diamond bot in w`. But `diamond bot = (box(bot -> bot)) -> bot = (box top) -> bot`
5. `top = bot -> bot` is derivable, so by NEC `box top` is derivable, so `box top in w`
6. By MP: `bot in w`. Contradiction with `mcs_bot_not_mem`

This is equivalent to Blackburn's proof but avoids needing a separate Existence Lemma formalization -- the Lindenbaum extension of W directly gives the successor.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Completeness/D.lean` with copyright header, module declaration, imports (MCS.lean, Soundness.lean, Instances, Completeness.lean for CanonicalWorld/CanonicalModel)
- [ ] Implement `derive_box_from_inconsistency_d`: Adaptation of `derive_box_from_inconsistency` (MCS.lean lines 290-354) replacing `h_T` with `h_D`. Two cases:
  - **Case 1 (neg phi in L)**: Identical to existing code -- filter L to L', apply deduction theorem to get L' |- phi, then `derive_box_from_box_context` gives box phi in S, contradicting `h_not_box`. No change needed.
  - **Case 2 (neg phi not in L)**: **This is where the D-specific argument replaces T.** In S5, the code does `mcs_box_closure h_T` to put each element of L into S, then uses S's consistency. For D, we cannot do this (no axiom T). Instead:
    1. All elements of L satisfy `box x in S` (since neg phi not in L, all come from `{psi | box psi in S}`)
    2. From `L |- bot`, apply `derive_box_from_box_context h_implyK h_implyS h_K h_mcs d_bot h_L'_box` to get `box bot in S`
    3. Axiom D at bot: `box bot -> diamond bot`. Apply `mcs_mp_axiom` to get `diamond bot in S`
    4. `diamond bot` unfolds to `(box (bot -> bot)) -> bot`
    5. `bot -> bot` is derivable (from `h_implyK bot bot` then simplification, or directly), so by NEC `box(bot -> bot)` is derivable, so `box(bot -> bot) in S`
    6. By `modal_implication_property`: `bot in S`. Contradiction with `mcs_bot_not_mem`
- [ ] Implement `mcs_box_witness_d`: Follows `mcs_box_witness` (MCS.lean lines 360-391) exactly but calls `derive_box_from_inconsistency_d` (with `h_D`) instead of `derive_box_from_inconsistency` (with `h_T`)
- [ ] Implement `canonical_serial` (Blackburn Theorem 4.28 clause 3):
  - Signature: takes `h_implyK`, `h_implyS`, `h_efq`, `h_K`, `h_D`, and `S : CanonicalWorld Axioms`
  - Returns `exists T : CanonicalWorld Axioms, (CanonicalModel Axioms).r S T`
  - Proof: Let `W = {psi | box psi in S.val}`. Show W is consistent using the D+NEC argument (steps 1-6 above). Apply `modal_lindenbaum` to get MCS T extending W. Construct `CanonicalWorld` from T. Show `(CanonicalModel Axioms).r S T` by definition: for any phi, box phi in S implies phi in W implies phi in T.
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.Completeness.D`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness/D.lean` - NEW (partial, ~150-180 lines for this phase)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Completeness.D` passes with zero errors
- `canonical_serial` type-checks with the correct signature
- `lean_verify` on `canonical_serial` confirms zero sorry

---

### Phase 3: Truth Lemma and D Completeness [COMPLETED]

**Goal**: Add `truth_lemma_d` and `d_completeness` to Completeness/D.lean.

**Blackburn cross-reference**:
- **Lemma 4.21 (Truth Lemma)**: For any normal modal logic Lambda and formula phi, canonical_model, w satisfies phi iff phi in w. The proof is by induction on phi. The only case that differs between S5 and D is the box case, which uses the box witness (whose construction depends on the available axioms).
- **Proposition 4.12 + Theorem 4.28**: Lambda is strongly complete w.r.t. S iff every Lambda-consistent set is satisfiable on some structure in S. The KD canonical frame is serial (Theorem 4.28 clause 3), so any KD-consistent set is satisfiable on a serial model.

**Tasks**:
- [ ] Implement `truth_lemma_d`: Follows `truth_lemma` from Completeness.lean (lines 147-242) with one key change:
  - **atom, bot, imp cases**: Identical to S5 truth lemma. The imp case uses recursive calls to `truth_lemma_d` instead of `truth_lemma`
  - **box case (line 230-242)**: Call `mcs_box_witness_d` (with `h_D`) instead of `mcs_box_witness` (with `h_T`). The rest of the box case is identical: contrapositive, obtain witness T, apply recursive `truth_lemma_d` call
  - Signature takes `h_implyK`, `h_implyS`, `h_efq`, `h_peirce`, `h_K`, `h_D` (replaces `h_T` with `h_D`)
- [ ] Implement `d_completeness` (Blackburn Proposition 4.12 applied to KD):
  - Signature: `d_completeness (phi : Proposition Atom) (h_valid : forall (World : Type u) (m : Model World Atom), Relation.Serial m.r -> forall w, Satisfies m w phi) : Derivable DAxiom phi`
  - Proof by contradiction, following the S5 `completeness` pattern (lines 250-323):
    1. Assume `not (Derivable DAxiom phi)` (Blackburn: "Suppose Sigma is KD-consistent")
    2. Show `{neg phi}` is DAxiom-consistent (same deduction theorem argument as S5)
    3. By Lindenbaum (Blackburn Lemma 4.17): extend to MCS M containing neg phi
    4. Let `w = (M, hM_mcs) : CanonicalWorld DAxiom` (Blackburn Definition 4.18)
    5. Show canonical model is serial: `canonical_serial` (Blackburn Theorem 4.28 clause 3), passing DAxiom constructors. This yields `Relation.Serial (CanonicalModel DAxiom).r`
    6. Apply `h_valid` to canonical model with seriality proof (Blackburn: "by the Truth Lemma"): get `Satisfies (CanonicalModel DAxiom) w phi`
    7. By `truth_lemma_d` (Blackburn Lemma 4.21): `phi in M`
    8. But `neg phi in M`, so `bot in M` via `modal_implication_property`. Contradiction with `mcs_bot_not_mem` (Blackburn: MCS cannot contain bot by Proposition 4.16)
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.Completeness.D`
- [ ] Run `lean_verify` on `d_completeness` to confirm zero sorry

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness/D.lean` - EXTEND (~120-150 additional lines)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Completeness.D` passes
- `d_completeness` has the correct type: `Derivable DAxiom phi` given validity on all serial models
- `lean_verify` confirms zero sorry/axiom usage in both Soundness/D.lean and Completeness/D.lean

---

### Phase 4: Integration and Final Verification [NOT STARTED]

**Goal**: Wire Soundness/D.lean and Completeness/D.lean into the module graph and verify full project build.

**Tasks**:
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.Soundness.D` to `Cslib/Logics/Modal/Metalogic.lean`
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.Completeness.D` to `Cslib/Logics/Modal/Metalogic.lean`
- [ ] Update `Metalogic.lean` module docstring to mention D soundness and completeness
- [ ] If a `Cslib/Logics/Modal/Metalogic/Soundness.lean` directory conflict arises (file vs directory), restructure: rename existing `Soundness.lean` to `Soundness/S5.lean` and create `Soundness.lean` as module aggregator importing both S5 and D. Apply same pattern for `Completeness.lean` if needed. Alternatively, use flat naming `DSoundness.lean` / `DCompleteness.lean` if restructuring is too invasive
- [ ] Run full `lake build` to verify zero regressions across the entire project
- [ ] Verify Soundness/D.lean and Completeness/D.lean have zero sorry with `lean_verify`

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` - ADD 2 import lines + update docstring
- Possibly `Cslib/Logics/Modal/Metalogic/Soundness.lean` and `Completeness.lean` if restructured

**Verification**:
- Full `lake build` passes with zero errors
- `grep -rn "sorry" Cslib/Logics/Modal/Metalogic/Soundness/D.lean Cslib/Logics/Modal/Metalogic/Completeness/D.lean` returns nothing
- All existing S5, bimodal, and temporal tests still pass

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.Soundness.D` -- scoped build after Phase 1
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Completeness.D` -- scoped build after Phases 2-3
- [ ] `lake build` -- full project build after Phase 4
- [ ] `lean_verify` on `d_axiom_sound`, `d_soundness`, `canonical_serial`, `truth_lemma_d`, `d_completeness` -- zero sorry, zero axiom usage
- [ ] `grep -rn "sorry" Cslib/Logics/Modal/Metalogic/Soundness/D.lean Cslib/Logics/Modal/Metalogic/Completeness/D.lean` -- empty output

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Soundness/D.lean` -- NEW (~50-60 lines)
- `Cslib/Logics/Modal/Metalogic/Completeness/D.lean` -- NEW (~280-340 lines)
- `Cslib/Logics/Modal/Metalogic.lean` -- MODIFIED (2 new imports, updated docstring)
- `specs/096_modal_d_soundness_completeness/plans/02_d-soundness-completeness.md` -- this plan

## Rollback/Contingency

All new code is in two new files (Soundness/D.lean, Completeness/D.lean). Rollback is trivial: delete the two new files and revert the import additions in Metalogic.lean. No existing files are modified in their logic content, only import lists are extended.

If the D+NEC contradiction argument proves harder than expected in Phase 2, the `canonical_serial` proof can be marked [BLOCKED] with a detailed goal state dump, and the remaining phases deferred. The Soundness/D.lean from Phase 1 is independently valuable and can be committed regardless.

If the Soundness.lean file-vs-directory conflict is problematic, fall back to flat naming: `DSoundness.lean` and `DCompleteness.lean` at the Metalogic level, matching the prior plan's approach.
