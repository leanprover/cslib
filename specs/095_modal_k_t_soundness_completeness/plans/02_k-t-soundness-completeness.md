# Implementation Plan: Task #95 (v2)

- **Task**: 95 - Establish soundness and completeness for modal logics K and T
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: Task 93 (modal S5 preservation + Instances.lean) -- completed
- **Research Inputs**: specs/095_modal_k_t_soundness_completeness/reports/01_k-t-soundness-completeness.md
- **Artifacts**: plans/02_k-t-soundness-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Implement sorry-free soundness and completeness theorems for modal logics K and T, following Blackburn, de Rijke, Venema "Modal Logic" (2002), Chapter 4 (hereafter "BRV"). The proof architecture mirrors BRV's completeness-via-canonicity method: shared infrastructure (Lindenbaum, canonical model, Existence Lemma, Truth Lemma) is already parameterized from tasks 92-93; per-system work consists of axiom validity proofs (soundness) and canonicity proofs (completeness). K completeness requires a K-specific Existence Lemma (BRV Lemma 4.20) that avoids the axiom T dependency present in the existing `derive_box_from_inconsistency`. T completeness reuses the existing parameterized infrastructure directly, since TAxiom includes the T axiom needed by `mcs_box_witness` and `truth_lemma`.

### Research Integration

The research report (01_k-t-soundness-completeness.md) identified:
- All existing infrastructure is parameterized over `Axioms` -- fully reusable for both K and T
- KAxiom (5 constructors) and TAxiom (6 constructors) already exist in Instances.lean
- The parameterized `soundness` theorem accepts a generic `h_ax_sound` callback
- The existing `mcs_box_witness` and `truth_lemma` take explicit `h_T` -- usable for T but not K
- The `derive_box_from_inconsistency` else-branch (MCS.lean lines 349-354) uses `mcs_box_closure` with `h_T` -- this is the ONLY `h_T` dependency that K must avoid
- K-specific fix: when `neg phi not in L`, all elements of L have box-versions in S; from `L |- bot`, derive `L |- phi` via EFQ, then use `derive_box_from_box_context` to get `box phi in S`, contradiction

### Prior Plan Reference

Plan v1 (01_k-t-soundness-completeness.md) established the 5-phase structure, identified the K-specific box witness as the key challenge, and confirmed flat file naming to avoid Lean module hierarchy conflicts. Effort estimate of 5 hours validated. The K box witness EFQ approach was correctly identified. v2 adds explicit Blackburn theorem cross-references to every implementation step and clarifies the mathematical correspondence at each stage.

### Roadmap Alignment

No ROADMAP.md found.

## Blackburn Cross-Reference Map

This plan follows BRV Chapter 4 step-by-step. The mapping between BRV theorems and Lean definitions:

| BRV Reference | Content | Lean Target | Phase |
|---------------|---------|-------------|-------|
| Definition 4.5 | Normal modal logic (K axiom + Dual + generalization) | `KAxiom`, `DerivationTree` (existing) | -- |
| Definition 4.9 | Soundness | `k_soundness`, `t_soundness` | 1, 2 |
| Definition 4.15 | MCS | `Modal.SetMaximalConsistent` (existing) | -- |
| Proposition 4.16 | MCS properties (closure, completeness) | `modal_closed_under_derivation`, `modal_negation_complete` (existing) | -- |
| Lemma 4.17 | Lindenbaum's Lemma | `modal_lindenbaum` (existing) | -- |
| Definition 4.18 | Canonical model | `CanonicalWorld`, `CanonicalModel` (existing) | -- |
| Lemma 4.19 | R^Lambda equivalence (box membership) | Built into `CanonicalModel.r` definition (existing) | -- |
| Lemma 4.20 | Existence Lemma | `mcs_box_witness` (existing for T), `k_mcs_box_witness` (new for K) | 3 |
| Lemma 4.21 | Truth Lemma | `truth_lemma` (existing for T), `k_truth_lemma` (new for K) | 3, 4 |
| Theorem 4.22 | Canonical Model Theorem | Subsumed by completeness proofs | 3, 4 |
| Theorem 4.23 | K completeness | `k_completeness` | 3 |
| Theorem 4.28 cl.1 | T completeness (reflexivity is canonical) | `t_canonical_refl`, `t_completeness` | 4 |
| Definition 4.30 | Canonicity | Implicit in proof structure | -- |

## Goals & Non-Goals

**Goals**:
- Prove K soundness: every KAxiom is valid on all frames (BRV Definition 4.9, no frame conditions)
- Prove K completeness: if phi is valid on all frames then phi is K-derivable (BRV Theorem 4.23)
- Prove T soundness: every TAxiom is valid on reflexive frames (BRV Definition 4.9)
- Prove T completeness: if phi is valid on all reflexive frames then phi is T-derivable (BRV Theorem 4.28, clause 1)
- Zero sorry occurrences across all four files
- Flat file naming (KSoundness.lean, etc.) to avoid Lean module conflicts

**Non-Goals**:
- Modifying existing Soundness.lean or Completeness.lean (S5 files remain unchanged)
- Modifying MCS.lean (K-specific helpers are defined locally in KCompleteness.lean)
- D or S4 soundness/completeness (tasks 96-97)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| K box witness else-branch encoding (BRV Lemma 4.20 without axiom T) | H | M | Follow EFQ + `derive_box_from_box_context` pattern; mathematical argument is standard (BRV confirms no T needed for Existence Lemma) |
| K truth lemma recursive calls require careful parameter threading | M | L | K truth_lemma follows identical structure to existing truth_lemma, substituting `k_mcs_box_witness` for `mcs_box_witness` |
| Module hierarchy conflict with existing Soundness/Completeness files | H | L | Flat naming (KSoundness.lean) confirmed to avoid conflicts per research analysis |
| Lean universe polymorphism in completeness theorem quantifiers | M | L | Follow exact pattern from existing S5 completeness (universe u annotation) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4 | 1, 2 respectively |
| 3 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: K Soundness (BRV Definition 4.9 for K) [COMPLETED]

**Goal**: Prove every KAxiom is valid on arbitrary frames (no frame conditions needed). This implements BRV Definition 4.9 specialized to the logic K, confirming that the axiom set of K is sound with respect to the class of all frames (BRV Table 4.1).

**Blackburn correspondence**: Soundness for K is "routine" per BRV -- check each axiom schema is valid on all frames. The proof rules (modus ponens, generalization) preserve validity automatically via the parameterized `soundness` theorem.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/KSoundness.lean` with copyright header, module declaration, and imports (`DerivationTree`, `Instances`)
- [ ] Define `k_axiom_sound` (BRV Def. 4.9): case split on `h_ax : KAxiom phi`, prove each constructor valid on all frames
  - `implyK` (propositional tautology): `intro h_phi _; exact h_phi`
  - `implyS` (propositional tautology): `intro h1 h2 h3; exact h1 h3 (h2 h3)`
  - `efq` (propositional tautology): `intro h; exact absurd h id`
  - `peirce` (propositional tautology): `intro h; by_contra h_not; exact h_not (h (fun h_phi => absurd h_phi h_not))`
  - `modalK` (BRV Def. 4.5, K axiom validity): `intro h_box_imp h_box_phi w' hr; exact h_box_imp w' hr (h_box_phi w' hr)`
  - No frame conditions needed for any case -- all valid on arbitrary frames
- [ ] Define `k_soundness`: instantiate parameterized `soundness` with `k_axiom_sound` (BRV Def. 4.9, structural induction on derivation tree)
- [ ] Define `k_soundness_derivable`: instantiate parameterized `soundness_derivable` with `k_axiom_sound`
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.KSoundness`

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/KSoundness.lean` -- NEW, ~80 lines

**Verification**:
- File compiles with zero errors and zero sorries
- `k_axiom_sound`, `k_soundness`, `k_soundness_derivable` all type-check

---

### Phase 2: T Soundness (BRV Definition 4.9 for T) [COMPLETED]

**Goal**: Prove every TAxiom is valid on reflexive frames. This implements BRV Definition 4.9 specialized to the logic T = KT, confirming that the axiom set of T is sound with respect to reflexive frames (BRV Table 4.1).

**Blackburn correspondence**: The propositional and modalK cases are identical to K (valid on all frames). The new case is `modalT` (axiom T: `box phi -> phi`), which requires the reflexivity hypothesis -- this is precisely the frame condition for T per BRV Table 4.1.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/TSoundness.lean` with copyright header, module declaration, and imports
- [ ] Define `t_axiom_sound` (BRV Def. 4.9 for T): case split on `h_ax : TAxiom phi`, prove each constructor
  - Propositional cases (`implyK`, `implyS`, `efq`, `peirce`): identical to K, no frame conditions needed
  - `modalK`: identical to K, no frame conditions needed
  - `modalT` (BRV axiom T, p.194): `intro h_box; exact h_box w (h_refl w)` -- uses reflexivity hypothesis `h_refl : forall w, m.r w w`
- [ ] Define `t_soundness`: instantiate parameterized `soundness` with `t_axiom_sound`
- [ ] Define `t_soundness_derivable`: instantiate parameterized `soundness_derivable` with `t_axiom_sound`
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.TSoundness`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/TSoundness.lean` -- NEW, ~60 lines

**Verification**:
- File compiles with zero errors and zero sorries
- `t_axiom_sound`, `t_soundness`, `t_soundness_derivable` all type-check

---

### Phase 3: K Completeness (BRV Theorem 4.23) [COMPLETED]

**Goal**: Prove K completeness via canonical model construction following BRV Theorem 4.23. This is the most complex phase because the existing Existence Lemma (`mcs_box_witness`) requires axiom T, which K does not have.

**Blackburn correspondence -- detailed step mapping**:

1. **Canonical model** (BRV Def. 4.18): Reuse existing `CanonicalWorld KAxiom` and `CanonicalModel KAxiom`. Worlds = K-MCSs, accessibility R^K defined by box membership (BRV Def. 4.18, clause 2). No frame conditions needed for K (BRV Theorem 4.23 -- "choose M to be the canonical model for K ... based on any frame whatsoever").

2. **K-specific Existence Lemma** (BRV Lemma 4.20): The existing `mcs_box_witness` implements Lemma 4.20 but takes `h_T` because its helper `derive_box_from_inconsistency` uses `mcs_box_closure` (which applies axiom T) in the else-branch. BRV's proof of Lemma 4.20 does NOT use axiom T -- it works for any normal modal logic. The K-specific version must replicate the BRV proof directly:
   - **BRV proof structure**: Suppose `diamond phi in w`. Let `v^- = {phi} union {psi | box psi in w}`. Show `v^-` is consistent. Extend to MCS by Lindenbaum (BRV Lemma 4.17).
   - **Consistency argument** (encoded in `k_derive_box_from_inconsistency`): If `v^-` is inconsistent, there exist `psi_1, ..., psi_n in v^-` with `psi_1 ^ ... ^ psi_n |- not phi`. By normality (K distribution + necessitation), `box(psi_1 ^ ... ^ psi_n) |- box(not phi)`. Since `box psi_i in w` for all i, `box(not phi) in w`. Using Dual, `not(diamond phi) in w`, contradicting `diamond phi in w`.
   - **Lean encoding**: The `neg phi in L` branch of existing `derive_box_from_inconsistency` is IDENTICAL (does not use `h_T`). The `neg phi not in L` branch needs the K-specific fix: from `L |- bot` where all elements have box-versions in S, derive `L |- phi` via EFQ (`bot -> phi` then MP), then use existing `derive_box_from_box_context` to get `box phi in S`, contradiction with `h_not_box`.

3. **K-specific Truth Lemma** (BRV Lemma 4.21): Same structure as existing `truth_lemma`. The atom, bot, and imp cases are identical. The box case calls `k_mcs_box_witness` instead of `mcs_box_witness`. BRV proof: "the right to left direction... is precisely what the Existence Lemma guarantees."

4. **K completeness theorem** (BRV Theorem 4.23): Contrapositive argument. If phi is not K-derivable, then `{neg phi}` is K-consistent. Extend to K-MCS `Gamma+` by Lindenbaum (BRV Lemma 4.17). By Truth Lemma, `M^K, Gamma+ |= neg phi`. But phi is valid on all frames and `M^K` is based on some frame, so `M^K, Gamma+ |= phi`, contradiction. BRV: "simply choose M to be the canonical model for K."

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/KCompleteness.lean` with copyright header, module declaration, imports (MCS, Soundness, Completeness for CanonicalWorld/CanonicalModel)
- [ ] Define `k_derive_box_from_inconsistency` (BRV Lemma 4.20, consistency sub-proof) -- K-specific version of `derive_box_from_inconsistency` with NO `h_T` parameter
  - The `neg phi in L` branch: IDENTICAL to existing code (lines 316-348 of MCS.lean). Separate `neg phi` from L, use deduction theorem to get `L' |- phi`, then `derive_box_from_box_context` gives `box phi in S`, contradiction.
  - The `neg phi not in L` branch (KEY CHANGE, BRV-faithful): all elements of L are `psi_i` with `box psi_i in S`. From `d_bot : L |- bot`, build `L |- phi` via EFQ axiom (`bot -> phi` weakened into L, then MP with `d_bot`). Then call existing `derive_box_from_box_context` to get `box phi in S`, contradiction with `h_not_box`. This corresponds to BRV's argument that the box-lift gives `box(not phi) in w`, contradicting `diamond phi in w`.
- [ ] Define `k_mcs_box_witness` (BRV Lemma 4.20, Existence Lemma for K) -- K-specific box witness using `k_derive_box_from_inconsistency`
  - Same structure as existing `mcs_box_witness` (MCS.lean lines 360-391)
  - Signature takes `h_implyK h_implyS h_efq h_peirce h_K` (NO `h_T`)
  - Let `W = {psi | box psi in S} union {neg phi}`, show W is consistent (via `k_derive_box_from_inconsistency`), extend to MCS by `modal_lindenbaum` (BRV Lemma 4.17)
  - Returns: `exists T, MCS T /\ (forall psi, box psi in S -> psi in T) /\ phi not in T`
- [ ] Define `k_truth_lemma` (BRV Lemma 4.21 for K) -- K-specific truth lemma
  - Same structure as existing `truth_lemma` (Completeness.lean lines 147-242)
  - All cases identical except `.box phi` case which calls `k_mcs_box_witness` instead of `mcs_box_witness`
  - Signature takes `h_implyK h_implyS h_efq h_peirce h_K` (NO `h_T`)
  - BRV: induction on formula degree; box case uses Existence Lemma
- [ ] Define `k_completeness` (BRV Theorem 4.23) -- K completeness theorem
  - Statement: `(forall World m w, Satisfies m w phi) -> Derivable KAxiom phi`
  - Proof structure following BRV Theorem 4.23:
    1. `by_contra h_not_deriv` -- assume phi is not K-derivable
    2. `{neg phi}` is K-consistent (same derivation as S5 completeness lines 258-291, substituting KAxiom constructors)
    3. `modal_lindenbaum` gives K-MCS M extending `{neg phi}` (BRV Lemma 4.17)
    4. `w : CanonicalWorld KAxiom := (M, hM_mcs)` -- canonical world
    5. `k_truth_lemma ... w phi` applied to `h_valid` on `CanonicalModel KAxiom` gives `M, w |= phi` (BRV Lemma 4.21)
    6. `neg phi in M` (from step 3) with `mcs_not_mem_of_neg` gives `phi not in M`
    7. But `k_truth_lemma` also gives `phi in M` from step 5 -- contradiction
  - Key difference from S5: NO frame property hypotheses passed to `h_valid` (K is complete w.r.t. all frames)
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.KCompleteness`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/KCompleteness.lean` -- NEW, ~250 lines

**Verification**:
- File compiles with zero errors and zero sorries
- `k_derive_box_from_inconsistency`, `k_mcs_box_witness`, `k_truth_lemma`, `k_completeness` all type-check
- `lean_verify` confirms no sorry or axiom usage beyond `propext`, `Classical.choice`, `Quot.sound`

---

### Phase 4: T Completeness (BRV Theorem 4.28, clause 1) [COMPLETED]

**Goal**: Prove T completeness via canonical model with reflexive frame, reusing existing parameterized infrastructure. This implements BRV Theorem 4.28, clause 1: "the canonical model for T is reflexive."

**Blackburn correspondence -- detailed step mapping**:

1. **Canonical frame reflexivity** (BRV Thm 4.28, cl.1): "Let w be a point in this model, and suppose phi in w. As w is a T-MCS, phi -> diamond(phi) in w, thus by modus ponens, diamond(phi) in w. Thus R^T ww." In Lean: reuse existing `canonical_refl` instantiated at TAxiom. The existing `canonical_refl` takes `h_implyK`, `h_implyS`, `h_T` and calls `mcs_box_closure`, which applies axiom T to show `box phi in w` implies `phi in w`, establishing R^T ww.

2. **Truth Lemma** (BRV Lemma 4.21 for T): REUSE existing `truth_lemma` directly. TAxiom provides all needed axiom hypotheses including `h_T := TAxiom.modalT`. The existing `truth_lemma` and `mcs_box_witness` work for any Axioms that include T.

3. **T completeness theorem** (BRV Thm 4.28, cl.1, combined with Thm 4.22):
   - Assume phi is valid on all reflexive frames but not T-derivable
   - `{neg phi}` is T-consistent
   - Extend to T-MCS w by Lindenbaum (BRV Lemma 4.17)
   - Canonical model for T has reflexive frame (BRV Thm 4.28 cl.1 -- `t_canonical_refl`)
   - Truth Lemma gives `M^T, w |= neg phi` (BRV Lemma 4.21)
   - But phi is valid on all reflexive frames, canonical model is reflexive, so `M^T, w |= phi`
   - Contradiction
   - Simpler than S5: only reflexivity needed, no transitivity or Euclideanness

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/TCompleteness.lean` with copyright header, module declaration, imports
- [ ] Define `t_canonical_refl` (BRV Thm 4.28 cl.1) -- instantiate existing `canonical_refl` at TAxiom
  - `canonical_refl (fun phi psi => .implyK phi psi) (fun phi psi chi => .implyS phi psi chi) (fun phi => .modalT phi)`
  - This is the core canonicity proof: "if phi in w and w is a T-MCS, then phi -> diamond(phi) in w (axiom T), thus diamond(phi) in w, thus R^T ww"
- [ ] Define `t_truth_lemma` (BRV Lemma 4.21 for T) -- instantiate existing `truth_lemma` at TAxiom
  - Pass all six axiom hypotheses from TAxiom constructors (`.implyK`, `.implyS`, `.efq`, `.peirce`, `.modalK`, `.modalT`)
  - The existing `truth_lemma` takes `h_T`, which `TAxiom.modalT` provides
- [ ] Define `t_completeness` (BRV Thm 4.28 cl.1 + Thm 4.22) -- T completeness theorem
  - Statement: `(forall World m, (forall w, m.r w w) -> forall w, Satisfies m w phi) -> Derivable TAxiom phi`
  - Proof structure follows BRV exactly:
    1. `by_contra h_not_deriv` -- assume phi is not T-derivable
    2. `{neg phi}` is T-consistent (same derivation as S5 completeness, substituting TAxiom constructors)
    3. `modal_lindenbaum` gives T-MCS M extending `{neg phi}` (BRV Lemma 4.17)
    4. `w : CanonicalWorld TAxiom := (M, hM_mcs)` -- canonical world
    5. Apply `h_valid` on `CanonicalModel TAxiom` with `t_canonical_refl` (reflexivity -- BRV Thm 4.28 cl.1)
    6. `truth_lemma` gives `phi in M` (BRV Lemma 4.21)
    7. `neg phi in M` from step 3, contradiction via `mcs_not_mem_of_neg`
  - Key difference from S5: only `t_canonical_refl` passed, no transitivity or Euclideanness
  - Key difference from K: reflexivity hypothesis in `h_valid` quantifier, and uses existing `truth_lemma`/`mcs_box_witness` (not K-specific versions)
- [ ] Verify with `lake build Cslib.Logics.Modal.Metalogic.TCompleteness`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/TCompleteness.lean` -- NEW, ~150 lines

**Verification**:
- File compiles with zero errors and zero sorries
- `t_canonical_refl`, `t_truth_lemma`, `t_completeness` all type-check

---

### Phase 5: Module Integration and Final Verification [NOT STARTED]

**Goal**: Wire all four new files into the module graph and verify the entire project builds.

**Tasks**:
- [ ] Add imports to `Cslib/Logics/Modal/Metalogic.lean` aggregator:
  - `public import Cslib.Logics.Modal.Metalogic.KSoundness`
  - `public import Cslib.Logics.Modal.Metalogic.TSoundness`
  - `public import Cslib.Logics.Modal.Metalogic.KCompleteness`
  - `public import Cslib.Logics.Modal.Metalogic.TCompleteness`
- [ ] Add imports to `Cslib.lean` root file (after existing Modal Metalogic entries):
  - `public import Cslib.Logics.Modal.Metalogic.KSoundness`
  - `public import Cslib.Logics.Modal.Metalogic.KCompleteness`
  - `public import Cslib.Logics.Modal.Metalogic.TSoundness`
  - `public import Cslib.Logics.Modal.Metalogic.TCompleteness`
- [ ] Run `lake build` (full project) to verify zero regressions
- [ ] Run `grep -r sorry KSoundness.lean TSoundness.lean KCompleteness.lean TCompleteness.lean` in the Metalogic directory to confirm zero sorries
- [ ] Verify existing S5 Soundness.lean and Completeness.lean still compile unchanged

**Timing**: 0.75 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` -- add 4 new imports
- `Cslib.lean` -- add 4 new imports (after line 291)

**Verification**:
- Full `lake build` passes with zero errors
- No regressions in existing modal metalogic files
- `grep -r sorry` across all four new files returns empty

---

## Testing & Validation

- [ ] Each new file compiles individually via `lake build Cslib.Logics.Modal.Metalogic.{K,T}{Soundness,Completeness}`
- [ ] Full project build (`lake build`) passes with zero errors
- [ ] Zero `sorry` across all four new files (grep verification)
- [ ] `lean_verify` on key theorems confirms no axiom usage beyond `propext`, `Classical.choice`, `Quot.sound`
- [ ] Existing S5 soundness and completeness unaffected (no imports or definitions changed)

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/KSoundness.lean` -- K soundness (~80 lines)
- `Cslib/Logics/Modal/Metalogic/TSoundness.lean` -- T soundness (~60 lines)
- `Cslib/Logics/Modal/Metalogic/KCompleteness.lean` -- K completeness (~250 lines)
- `Cslib/Logics/Modal/Metalogic/TCompleteness.lean` -- T completeness (~150 lines)
- `Cslib/Logics/Modal/Metalogic.lean` -- updated aggregator
- `Cslib.lean` -- updated root imports

## Rollback/Contingency

All changes are additive: 4 new files + 8 new import lines. To revert:
1. Delete the four new `.lean` files
2. Remove the added import lines from `Metalogic.lean` and `Cslib.lean`
3. No existing files are modified in content

If K box witness (BRV Lemma 4.20 for K) proves difficult to encode, the phase can be marked [PARTIAL] and the three other files (KSoundness, TSoundness, TCompleteness) can still be completed independently. The K completeness file is the only one with medium risk.
