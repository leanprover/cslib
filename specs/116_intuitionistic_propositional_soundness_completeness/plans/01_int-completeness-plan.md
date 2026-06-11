# Implementation Plan: Intuitionistic Propositional Soundness and Completeness

- **Task**: 116 - Intuitionistic propositional soundness and completeness
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: Tasks 113 (deduction theorem), 115 (Kripke semantics)
- **Research Inputs**: specs/116_intuitionistic_propositional_soundness_completeness/reports/01_int-completeness-research.md
- **Artifacts**: plans/01_int-completeness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Prove soundness and completeness of IntPropAxiom (intuitionistic propositional logic with axioms K, S, EFQ) with respect to intuitionistic Kripke semantics (`IForces`, `IValid` from `Kripke.lean`). The implementation creates three new files: `IntSoundness.lean` (soundness by induction on derivation trees), `IntLindenbaum.lean` (deductively closed consistent sets and the implication witness lemma), and `IntCompleteness.lean` (canonical model construction with DCCS worlds and the truth lemma).

### Research Integration

The research report (01_int-completeness-research.md) contains a critical discovery: standard MCS (maximal consistent sets) are **insufficient** for intuitionistic completeness because non-derivable formulas like `neg neg p -> p` end up in every MCS when `neg neg (neg neg p -> p)` is Int-derivable. The correct approach uses **deductively closed consistent sets (DCCS)** as canonical model worlds, not MCS. Key findings integrated:

1. **Worlds = DCCS** (not MCS): A DCCS is consistent + deductively closed (but NOT necessarily maximal). This avoids the MCS trap where all MCS contain non-derivable formulas whose double negation is derivable.
2. **Implication witness lemma**: If `phi -> psi not in S` (DCCS), then the deductive closure of `S union {phi}` is a DCCS containing `phi` and excluding `psi`. Proof uses EFQ composition for consistency and the deduction theorem for psi-exclusion.
3. **Starting world**: The set `{psi | [] |-_Int psi}` (all Int-theorems) is a DCCS that excludes any non-derivable formula, providing the starting world for the completeness argument.
4. **Soundness** follows the classical pattern with 3 axiom cases (no Peirce) and uses `iforces_persistence`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the propositional completeness items under the formal reasoning roadmap. It is Phase 4 of the parent task 112 (propositional completeness expansion).

## Goals & Non-Goals

**Goals**:
- Prove `int_soundness_derivable`: `Derivable IntPropAxiom phi -> IValid phi`
- Define `IntDCCS` (deductively closed consistent sets for IntPropAxiom)
- Prove the implication witness lemma for DCCS
- Construct the canonical Kripke model with DCCS worlds
- Prove `int_truth_lemma`: `IForces v bf S phi <-> phi in S.val` for DCCS worlds
- Prove `int_completeness`: `IValid phi -> Derivable IntPropAxiom phi`
- Prove `int_soundness_completeness`: `IValid phi <-> Derivable IntPropAxiom phi`

**Non-Goals**:
- Finite model property for Int (separate concern)
- Completeness for MinPropAxiom (minimal logic, no EFQ)
- Decidability of IntPropAxiom derivability
- Modifying existing MCS.lean or Completeness.lean files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Deductive closure definition does not compose well with Lean's type system | H | M | Define as a predicate on Sets, following MCS pattern; fall back to Subtype if needed |
| Implication witness psi-exclusion proof requires complex derivation tree construction | M | M | Research report provides the exact derivation steps; follow them methodically |
| IForces unfolding creates complex goal states in truth lemma | M | H | Use `simp only [IForces]` and break into small lemmas; mirror classical Completeness.lean structure |
| Universe polymorphism issues with canonical model world type | M | L | Follow Kripke.lean's universe annotations (`Type u`, `Type v`) |
| EFQ composition derivation (neg phi |- phi -> psi) is tricky to formalize | M | M | Build as standalone lemma with explicit DerivationTree; test with lean_multi_attempt |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: IntSoundness.lean [COMPLETED]

**Goal**: Prove that every IntPropAxiom-derivable formula is intuitionistically valid (IValid).

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` with module header and imports
- [ ] Prove `int_axiom_sound`: Each IntPropAxiom axiom is IValid (3 cases)
  - `implyK`: Use `iforces_persistence` -- given `IForces w' phi`, show `forall w'' >= w', IForces w'' psi -> IForces w'' phi` via persistence from `w' <= w''`
  - `implyS`: Use nested universal quantification over successors with transitivity
  - `efq`: `IForces w' bot = False`, so premise is vacuously false
- [ ] Prove `int_soundness`: If `DerivationTree IntPropAxiom Gamma phi`, then for any Kripke model where all of Gamma is forced at w, phi is forced at w (by induction on derivation tree, 4 cases: ax, assumption, modus_ponens, weakening)
- [ ] Prove `int_soundness_derivable`: `Derivable IntPropAxiom phi -> IValid phi`
- [ ] Verify with `lake build Cslib.Logics.Propositional.Metalogic.IntSoundness`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` - New file: soundness theorem

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.IntSoundness` succeeds
- `lean_verify` confirms no sorry or axiom usage beyond standard ones

---

### Phase 2: IntLindenbaum.lean [COMPLETED]

**Goal**: Define DCCS (deductively closed consistent sets) and prove the implication witness lemma.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` with module header and imports (`DeductionTheorem.lean`, `MCS.lean`)
- [ ] Define `IntDCCS (S : Set (PL.Proposition Atom)) : Prop` as the conjunction of:
  - `PropSetConsistent IntPropAxiom S` (consistency)
  - Deductive closure: `forall (L : List ...) (phi : ...), (forall x in L, x in S) -> Deriv IntPropAxiom L phi -> phi in S`
- [ ] Prove `int_dccs_bot_not_mem`: `IntDCCS S -> bot not in S`
- [ ] Prove `int_dccs_imp_property`: `IntDCCS S -> phi.imp psi in S -> phi in S -> psi in S`
- [ ] Prove helper derivation `int_neg_phi_imp_psi`: Build `DerivationTree IntPropAxiom [phi.imp .bot] (phi.imp psi)` using EFQ composition:
  - Step 1: EFQ axiom `bot -> psi`
  - Step 2: implyK on step 1: `(bot -> psi) -> (phi -> (bot -> psi))`
  - Step 3: MP: `phi -> (bot -> psi)`
  - Step 4: implyS: `(phi -> (bot -> psi)) -> ((phi -> bot) -> (phi -> psi))`
  - Step 5: MP: `(phi -> bot) -> (phi -> psi)`
  - Step 6: MP with assumption: `[phi -> bot] |- phi -> psi`
- [ ] Define `int_deductive_closure (S : Set ...) : Set ...` as `{phi | exists L, (forall x in L, x in S) /\ Deriv IntPropAxiom L phi}`
- [ ] Prove `int_deductive_closure_dccs`: If `PropSetConsistent IntPropAxiom S`, then `IntDCCS (int_deductive_closure S)` -- deductive closure is always a DCCS when starting from a consistent set
- [ ] Prove `int_deductive_closure_consistent`: If S is consistent, `int_deductive_closure S` is consistent (since any derivation of bot from the closure can be collapsed into a derivation of bot from S)
- [ ] Prove `int_imp_witness`: The implication witness lemma:
  - Statement: `IntDCCS S -> phi.imp psi not in S -> exists T, S subset T /\ IntDCCS T /\ phi in T /\ psi not in T`
  - Construction: Let `T = int_deductive_closure (S union {phi})`
  - Prove `S union {phi}` is consistent: by contradiction, if not, then by DT `S |- phi -> bot`, so `neg phi in S` (by closure). From `neg phi` derive `phi -> psi` using `int_neg_phi_imp_psi` and closure. Contradiction with `phi.imp psi not in S`.
  - Prove `T` is DCCS: by `int_deductive_closure_dccs`
  - Prove `phi in T`: `phi` is derivable from `S union {phi}` by assumption rule
  - Prove `psi not in T`: if `psi in T`, then exists `L subset S union {phi}` with `L |- psi`. By DT: `L' |- phi -> psi` for `L' subset S`. By deductive closure of S: `phi.imp psi in S`. Contradiction.
- [ ] Prove `int_theorems_dccs`: The set `{psi | Derivable IntPropAxiom psi}` is IntDCCS
- [ ] Verify with `lake build Cslib.Logics.Propositional.Metalogic.IntLindenbaum`

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - New file: DCCS definition and implication witness

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.IntLindenbaum` succeeds
- `lean_verify` confirms no sorry
- Key lemma `int_imp_witness` type-checks

---

### Phase 3: IntCompleteness.lean [NOT STARTED]

**Goal**: Build the canonical Kripke model, prove the truth lemma, and establish completeness.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` with module header and imports (`Kripke.lean`, `IntSoundness.lean`, `IntLindenbaum.lean`)
- [ ] Define `IntCanonicalWorld` as `{ S : Set (PL.Proposition Atom) // IntDCCS S }`
- [ ] Define the canonical preorder on `IntCanonicalWorld`: `S <= T iff S.val subset T.val`
  - Prove reflexivity and transitivity (Preorder instance)
- [ ] Define the canonical valuation: `int_canonical_val (w : IntCanonicalWorld) (p : Atom) := Proposition.atom p in w.val`
- [ ] Prove `int_canonical_val_upward_closed`: upward closure of atom membership (trivially from set inclusion)
- [ ] Prove `int_truth_lemma`: `IForces int_canonical_val (fun _ => False) S phi <-> phi in S.val`
  - By structural induction on `phi`:
  - **atom p**: `IForces ... S (atom p) = int_canonical_val S p = (atom p in S.val)`. Trivial.
  - **bot**: `IForces ... S bot = False`. Backward: `bot in S.val -> False` by `int_dccs_bot_not_mem`. Forward: `False -> bot in S.val` is vacuous.
  - **imp phi psi (backward)**: Given `phi.imp psi in S.val`, show `forall T >= S, IForces T phi -> IForces T psi`. Given `T >= S`: `phi.imp psi in T.val` (by `S.val subset T.val`). By IH backward on phi: `IForces T phi -> phi in T.val`. Then `phi in T.val` and `phi.imp psi in T.val` give `psi in T.val` by `int_dccs_imp_property`. By IH forward on psi: `psi in T.val -> IForces T psi`.
  - **imp phi psi (forward)**: Contrapositive. Assume `phi.imp psi not in S.val`. By `int_imp_witness`: exists DCCS `T` with `S.val subset T.val`, `phi in T.val`, `psi not in T.val`. Wrap `T` as `IntCanonicalWorld`. Then `S <= T`, `IForces T phi` (by IH backward), `not IForces T psi` (by IH forward contrapositive). So `not IForces S (phi.imp psi)`.
- [ ] Prove `int_completeness`: `IValid phi -> Derivable IntPropAxiom phi`
  - By contrapositive: assume `not Derivable IntPropAxiom phi`
  - Construct starting world: `W0 = {psi | Derivable IntPropAxiom psi}`, which is IntDCCS by `int_theorems_dccs`
  - `phi not in W0.val` (by assumption)
  - By truth lemma backward direction (contrapositive): `not IForces ... W0 phi`
  - The canonical model is a valid Kripke model (preorder + upward-closed valuation)
  - So there exists a Kripke model and world where phi is not forced
  - Therefore `not IValid phi`
- [ ] Prove `int_soundness_completeness`: `IValid phi <-> Derivable IntPropAxiom phi`
  - Forward: `int_completeness`
  - Backward: `int_soundness_derivable` (from Phase 1)
- [ ] Verify with `lake build Cslib.Logics.Propositional.Metalogic.IntCompleteness`
- [ ] Run full project build: `lake build`

**Timing**: 2 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` - New file: canonical model, truth lemma, completeness

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.IntCompleteness` succeeds
- `lean_verify` confirms no sorry in all three files
- Full `lake build` succeeds with no regressions

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Metalogic.IntSoundness` -- Phase 1
- [ ] `lake build Cslib.Logics.Propositional.Metalogic.IntLindenbaum` -- Phase 2
- [ ] `lake build Cslib.Logics.Propositional.Metalogic.IntCompleteness` -- Phase 3
- [ ] `lean_verify` on `int_soundness_completeness` to confirm no sorry
- [ ] Full `lake build` with no regressions
- [ ] Verify `int_completeness` uses only standard axioms (no classical choice beyond what Lean provides by default)

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` - Soundness of IntPropAxiom w.r.t. IValid
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - DCCS definition, deductive closure, implication witness
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` - Canonical model, truth lemma, completeness biconditional

## Rollback/Contingency

All three files are new additions. If implementation fails:
- Delete the created `.lean` files
- No existing files are modified, so no rollback of existing code is needed
- If Phase 2 (implication witness) is blocked, Phase 1 (soundness) remains independently valid
- If the DCCS approach encounters Lean-specific issues (e.g., universe problems with Subtype worlds), fall back to using MCS worlds with a separate `lindenbaum_excluding` lemma that uses Zorn on consistent sets not containing `phi`
