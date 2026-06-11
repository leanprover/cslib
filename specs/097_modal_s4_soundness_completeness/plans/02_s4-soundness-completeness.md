# Implementation Plan: S4 Soundness and Completeness (v2)

- **Task**: 97 - Establish soundness and completeness for modal logic S4
- **Status**: [IMPLEMENTING]
- **Effort**: 3 hours
- **Dependencies**: Task 93 (S5 soundness/completeness infrastructure)
- **Research Inputs**: specs/097_modal_s4_soundness_completeness/reports/01_s4-soundness-completeness.md
- **Artifacts**: plans/02_s4-soundness-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Establish sorry-free soundness and completeness theorems for S4 modal logic (reflexive + transitive frames) by creating two new Lean files that reuse the existing parameterized infrastructure. The proof structure follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4, specifically Theorems 4.27 (transitivity is canonical), 4.28 clause 1 (reflexivity is canonical), and 4.29 (S4 completeness by combining both). The primary reference material is extracted in `specs/097_modal_s4_soundness_completeness/references/blackburn-ch4-completeness.md`.

### Research Integration

Key findings from the research report (01_s4-soundness-completeness.md):

1. **S4Axiom** already defined in `Instances.lean:130-153` with 7 constructors (implyK, implyS, efq, peirce, modalK, modalT, modalFour) -- identical to ModalAxiom minus modalB.
2. **All canonical model infrastructure is parameterized**: `canonical_refl` requires h_implyK, h_implyS, h_T; `canonical_trans` requires h_implyK, h_implyS, h_4; `truth_lemma` requires h_implyK, h_implyS, h_efq, h_peirce, h_K, h_T.
3. **Minimal delta from S5**: `s4_axiom_sound` has 7 cases (drops modalB), `s4_completeness` removes the Euclidean condition from `h_valid` and omits the `canonical_eucl` call.
4. **Flat naming recommended**: `S4Soundness.lean` and `S4Completeness.lean` in `Metalogic/` to avoid disrupting existing imports.
5. **No new tactics needed** -- same structural proof techniques as S5.

### Blackburn Ch. 4 Proof Architecture

The plan follows the completeness-via-canonicity method from Blackburn et al. (2002):

- **Theorem 4.27** (K4 transitivity is canonical): If R^{K4} wv and R^{K4} vu, then for any phi in u: phi in u implies dia(phi) in v (by R vu), implies dia(dia(phi)) in w (by R wv), implies dia(phi) in w (by axiom 4: dia(dia(phi)) -> dia(phi) in w as a K4-MCS). Therefore R^{K4} wu.
  - **Lean correspondence**: `canonical_trans` in Completeness.lean:78-92, using `mcs_box_box` (axiom 4 direction: box(phi) -> box(box(phi))).
  - **Note on dual formulation**: Blackburn states 4 as dia(dia(p)) -> dia(p); the codebase uses the equivalent box formulation box(p) -> box(box(p)). The proof argument is identical under duality -- `mcs_box_box` applies axiom 4 to get box(box(phi)) from box(phi), then the accessibility chain yields the result. Both are Theorem 4.27.

- **Theorem 4.28, clause 1** (T reflexivity is canonical): For any phi in w: phi in w, and phi -> dia(phi) in w (axiom T as a T-MCS), so dia(phi) in w by modus ponens. Therefore R^T ww.
  - **Lean correspondence**: `canonical_refl` in Completeness.lean:65-76, using `mcs_box_closure` (axiom T: box(phi) -> phi).
  - **Note on dual formulation**: Blackburn states T as p -> dia(p); the codebase uses the equivalent box(p) -> p. Under the canonical relation definition (R wv iff box(psi) in w implies psi in v), reflexivity R ww follows from: box(phi) in w implies phi in w (by axiom T via MCS closure). Both are Theorem 4.28 clause 1.

- **Theorem 4.29** (S4 completeness): S4 = KT4 contains both T and 4 axioms. The proof of Thm 4.27 shows the canonical frame of any logic containing 4 is transitive; the proof of Thm 4.28 clause 1 shows the canonical frame of any logic containing T is reflexive. Since S4 contains both, its canonical frame is reflexive and transitive. Strong completeness follows by the Canonical Model Theorem (Thm 4.22).
  - **Lean correspondence**: `s4_completeness` (to be created) combines `canonical_refl` and `canonical_trans`, then applies `truth_lemma` and the canonical model argument. This directly mirrors Thm 4.29's proof by composition.

- **Soundness** (Def 4.9, Table 4.1): S4 is sound w.r.t. reflexive, transitive frames. Each axiom is valid on the frame class. Axiom T is valid on reflexive frames; axiom 4 is valid on transitive frames.

### Prior Plan Reference

Prior plan (01_s4-soundness-completeness.md) established the 3-phase structure and confirmed the minimal delta from S5. Key lessons: flat naming avoids import disruption; the S4Axiom type needs no modification; the completeness proof is structurally identical to S5 minus the Euclidean condition. Effort was estimated at 2.5 hours but is revised upward to 3 hours to account for careful Blackburn cross-referencing in docstrings and the completeness proof's contrapositive argument.

### Roadmap Alignment

This task advances the "Modal metalogic" items in ROADMAP.md by extending soundness and completeness from S5 to S4. It falls within the broader modal cube expansion effort (parent task 90).

## Goals & Non-Goals

**Goals**:
- Create `S4Soundness.lean` with sorry-free `s4_axiom_sound`, `s4_soundness`, and `s4_soundness_derivable`, with docstrings referencing Blackburn Def 4.9 and Table 4.1
- Create `S4Completeness.lean` with sorry-free `s4_completeness`, with docstrings referencing Blackburn Theorems 4.27, 4.28 (clause 1), and 4.29
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
| Completeness proof `by_contra` block requires exact term matching for Derivable | M | L | Follow S5 completeness proof term-for-term, substituting S4Axiom constructors |
| Import cycle if S4Completeness imports both Soundness and S4Soundness | M | L | S4Completeness only needs Completeness.lean (which already imports Soundness); S4Soundness is independent |
| Axiom 4 dual formulation confusion (box vs diamond) | M | L | Blackburn uses dia(dia(p)) -> dia(p); codebase uses box(p) -> box(box(p)). These are equivalent by duality. The existing `mcs_box_box` handles this correctly. Document the correspondence in docstrings |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: S4 Soundness [COMPLETED]

**Goal**: Create `Cslib/Logics/Modal/Metalogic/S4Soundness.lean` with sorry-free proofs of S4 axiom soundness and the S4 soundness theorem. This phase establishes that all S4 axioms are valid on reflexive + transitive frames (Blackburn Def 4.9, Table 4.1).

**Blackburn Reference**: Soundness (Def 4.9) reduces to checking validity of each axiom on the target frame class. For S4, the frame class is reflexive + transitive (Table 4.1). Axiom T (`box(phi) -> phi`) is valid on reflexive frames; axiom 4 (`box(phi) -> box(box(phi))`) is valid on transitive frames; propositional axioms and K are valid on all frames.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/S4Soundness.lean` with module header and imports (`Cslib.Logics.Modal.Metalogic.DerivationTree`)
- [ ] Add module docstring referencing Blackburn Def 4.9, Table 4.1, and the S4 = KT4 naming convention (p.194)
- [ ] Implement `s4_axiom_sound`: pattern match on 7 `S4Axiom` cases, proving each valid on reflexive + transitive frames
  - Propositional cases (implyK, implyS, efq, peirce): identical to S5 `axiom_sound`, valid on all frames
  - modalK: identical to S5, valid on all frames
  - modalT: use `h_refl` parameter -- validity on reflexive frames (Blackburn Thm 4.28 soundness direction)
  - modalFour: use `h_trans` parameter -- validity on transitive frames (Blackburn Thm 4.27 soundness direction)
  - NOTE: no modalB case (the key difference from S5 -- S4 drops the B axiom)
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

### Phase 2: S4 Completeness [COMPLETED]

**Goal**: Create `Cslib/Logics/Modal/Metalogic/S4Completeness.lean` with a sorry-free proof of S4 completeness via canonical models, following Blackburn Theorem 4.29 which combines Theorems 4.27 and 4.28 (clause 1).

**Blackburn Reference -- Theorem 4.29 (S4 completeness)**:
> "The proof of Theorem 4.27 shows that the canonical frame of *any* normal logic containing the 4 axiom is transitive, while the proof of the first clause of Theorem 4.28 shows that the canonical frame of *any* normal logic containing the T axiom is reflexive. As S4 contains both axioms, its canonical frame has both properties, thus the completeness result for S4 follows."

The proof proceeds by the Canonical Model Theorem (Thm 4.22): given a consistent set Sigma, Lindenbaum's Lemma (Lemma 4.17) extends it to an MCS Sigma+, and the Truth Lemma (Lemma 4.21) gives satisfaction in the canonical model. The key S4-specific step is showing the canonical frame is reflexive AND transitive:

- **Transitivity (Thm 4.27)**: Suppose R wv and R vu. For any phi in u: phi in u implies dia(phi) in v (by R vu), implies dia(dia(phi)) in w (by R wv). Since w is an S4-MCS containing axiom 4 (dia(dia(phi)) -> dia(phi)), modus ponens gives dia(phi) in w. Therefore R wu.
  - Lean: `canonical_trans` with S4Axiom.implyK, S4Axiom.implyS, S4Axiom.modalFour

- **Reflexivity (Thm 4.28, clause 1)**: For any phi in w: phi in w, and since w is an S4-MCS containing axiom T (phi -> dia(phi)), modus ponens gives dia(phi) in w. Therefore R ww.
  - Lean: `canonical_refl` with S4Axiom.implyK, S4Axiom.implyS, S4Axiom.modalT

- **Combination (Thm 4.29)**: The canonical frame for S4 is reflexive (from T, by Thm 4.28.1) and transitive (from 4, by Thm 4.27). Apply the Canonical Model Theorem.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/S4Completeness.lean` with module header and imports (`Cslib.Logics.Modal.Metalogic.Completeness` which brings in MCS, Soundness, etc.)
- [ ] Add module docstring referencing Blackburn Theorems 4.22, 4.27, 4.28 (clause 1), 4.29, and the completeness-via-canonicity method
- [ ] Implement `s4_completeness` theorem following Blackburn Thm 4.29:
  - Type signature:
    ```
    theorem s4_completeness (phi : Proposition Atom)
        (h_valid : forall (World : Type u) (m : Model World Atom),
          (forall w, m.r w w) ->
          (forall w1 w2 w3, m.r w1 w2 -> m.r w2 w3 -> m.r w1 w3) ->
          forall w, Satisfies m w phi) :
        Derivable (@S4Axiom Atom) phi
    ```
  - Step 1 -- Contrapositive setup: `by_contra h_not_deriv` -- assume phi is not S4-derivable
  - Step 2 -- Consistency (prerequisite for Lindenbaum, Lemma 4.17): Show `{neg(phi)}` is S4-consistent. This follows the same structure as S5 `completeness` proof, replacing `ModalAxiom` constructors with `S4Axiom` constructors throughout. Key substitutions: `.implyK` for S4Axiom.implyK, `.implyS` for S4Axiom.implyS, `.efq` for S4Axiom.efq, `.peirce` for S4Axiom.peirce
  - Step 3 -- Lindenbaum extension (Lemma 4.17): Apply `modal_lindenbaum` to extend `{neg(phi)}` to an S4-MCS
  - Step 4 -- Canonical world: Construct `w : CanonicalWorld (@S4Axiom Atom)` from the MCS
  - Step 5 -- Truth Lemma (Lemma 4.21): Apply `truth_lemma` instantiated at S4Axiom constructors (implyK, implyS, efq, peirce, modalK, modalT) to get satisfaction from membership
  - Step 6 -- Frame properties via Theorems 4.27 + 4.28.1 (combined = Thm 4.29): Apply `h_valid` with:
    - `canonical_refl` instantiated with S4Axiom.implyK, S4Axiom.implyS, S4Axiom.modalT (Thm 4.28, clause 1: T axiom makes canonical frame reflexive)
    - `canonical_trans` instantiated with S4Axiom.implyK, S4Axiom.implyS, S4Axiom.modalFour (Thm 4.27: 4 axiom makes canonical frame transitive)
    - NO `canonical_eucl` needed (this is the key simplification vs S5 -- S4 drops B axiom)
  - Step 7 -- Contradiction: Apply `mcs_not_mem_of_neg` to derive contradiction between neg(phi) in w and phi satisfied at w
- [ ] Add inline comments at Steps 2, 5, 6 citing the specific Blackburn theorem being instantiated
- [ ] Verify with `lean_goal` at key proof positions; run `lake build Cslib.Logics.Modal.Metalogic.S4Completeness`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/S4Completeness.lean` -- NEW: ~120-160 lines

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.S4Completeness` succeeds with no errors
- `lean_verify` on `s4_completeness` shows no sorry

---

### Phase 3: Module Integration [COMPLETED]

**Goal**: Wire the new S4 files into the module aggregator and root imports, verify clean full build.

**Tasks**:
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.S4Soundness` to `Cslib/Logics/Modal/Metalogic.lean` *(deviation: deferred to task 98 — aggregator imports handled by integration task to avoid parallel conflicts)*
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.S4Completeness` to `Cslib/Logics/Modal/Metalogic.lean` *(deviation: deferred to task 98)*
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.S4Soundness` to `Cslib.lean` *(deviation: deferred to task 98)*
- [ ] Add `public import Cslib.Logics.Modal.Metalogic.S4Completeness` to `Cslib.lean` *(deviation: deferred to task 98)*
- [x] Run full `lake build` and confirm zero errors, zero sorries *(deviation: altered — verified individual module builds instead of full build since aggregator imports deferred)*
- [x] Run `lean_verify` on all new theorems: `Cslib.Logic.Modal.s4_axiom_sound`, `Cslib.Logic.Modal.s4_soundness`, `Cslib.Logic.Modal.s4_soundness_derivable`, `Cslib.Logic.Modal.s4_completeness`

**Timing**: 0.75 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic.lean` -- add 2 import lines
- `Cslib.lean` -- add 2 import lines

**Verification**:
- Full `lake build` succeeds with zero errors
- All 4 new theorems pass `lean_verify` with no sorry and no additional axioms beyond standard Lean axioms (propext, Quot.sound, Classical.choice)

## Blackburn Cross-Reference Summary

| Blackburn Reference | Content | Lean Correspondence | Phase |
|---------------------|---------|---------------------|-------|
| Def 4.5 | Normal modal logic | `S4Axiom` inductive type | Background |
| Def 4.9 | Soundness definition | `s4_axiom_sound` | 1 |
| Table 4.1 | S4 = reflexive + transitive | Frame conditions in type signatures | 1, 2 |
| Def 4.15 | MCS definition | `SetMaximalConsistent` | Background |
| Lemma 4.17 | Lindenbaum's Lemma | `modal_lindenbaum` | 2 (Step 3) |
| Def 4.18 | Canonical model | `CanonicalModel`, `CanonicalWorld` | 2 (Step 4) |
| Lemma 4.19 | Canonical relation (box direction) | Built into `CanonicalModel.r` definition | 2 |
| Lemma 4.20 | Existence Lemma | `mcs_box_witness` | 2 (Step 5, inside truth_lemma) |
| Lemma 4.21 | Truth Lemma | `truth_lemma` | 2 (Step 5) |
| Thm 4.22 | Canonical Model Theorem | Overall structure of `s4_completeness` | 2 |
| Thm 4.27 | Transitivity is canonical (axiom 4) | `canonical_trans` | 2 (Step 6) |
| Thm 4.28.1 | Reflexivity is canonical (axiom T) | `canonical_refl` | 2 (Step 6) |
| Thm 4.29 | S4 completeness (combines 4.27 + 4.28.1) | `s4_completeness` | 2 |

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
- `Cslib/Logics/Modal/Metalogic/S4Completeness.lean` -- S4 completeness via canonical models (~120-160 lines)
- `Cslib/Logics/Modal/Metalogic.lean` -- updated aggregator (2 new import lines)
- `Cslib.lean` -- updated root imports (2 new import lines)
- `specs/097_modal_s4_soundness_completeness/plans/02_s4-soundness-completeness.md` -- this plan

## Rollback/Contingency

The changes are purely additive (2 new files + 4 new import lines). Rollback is straightforward:
1. Delete `S4Soundness.lean` and `S4Completeness.lean`
2. Remove the 2 import lines from `Metalogic.lean`
3. Remove the 2 import lines from `Cslib.lean`
4. Run `lake build` to confirm clean state

If a proof gets stuck on a specific step (unlikely given the S5 template):
- Use `lean_goal` to inspect the goal state
- Compare with the corresponding S5 proof in `Soundness.lean` or `Completeness.lean`
- The Blackburn reference (`blackburn-ch4-completeness.md`) provides the mathematical argument for each step, including the specific theorem number to consult
