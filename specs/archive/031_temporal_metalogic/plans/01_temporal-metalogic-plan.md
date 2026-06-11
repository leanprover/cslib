# Implementation Plan: Task #31 -- Standalone Temporal Metalogic

- **Task**: 31 - Build standalone temporal metalogic
- **Status**: [IN PROGRESS]
- **Effort**: 18 hours
- **Dependencies**: Task 22 (temporal infrastructure), Task 23 (temporal semantics), Task 29 (generic MCS)
- **Research Inputs**: specs/031_temporal_metalogic/reports/01_temporal-metalogic-research.md
- **Artifacts**: plans/01_temporal-metalogic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Build the complete temporal metalogic module at `Cslib/Logics/Temporal/Metalogic/` as new Lean 4 development (not a port). The module comprises five files: DerivationTree setup (height, Deriv, DerivationSystem instance), DeductionTheorem (structural induction on 6-constructor tree), MCS theory (generic instantiation plus temporal-specific witness lemmas for Until/Since), Soundness (26-axiom validity over serial linear orders), and Completeness (canonical linear model construction with truth lemma). The modal metalogic at `Cslib/Logics/Modal/Metalogic/` serves as the direct structural template, with temporal-specific adaptations for the 6-constructor DerivationTree, the `swap_temporal` duality rule, and the canonical linear order (vs. accessibility relation).

### Research Integration

Key findings from the research report:
- All 3 dependencies (Tasks 22, 23, 29) are confirmed completed and provide complete infrastructure.
- The temporal `DerivationTree` has 6 constructors (vs. 5 for modal); constructors 4 (`temporal_necessitation`) and 5 (`temporal_duality`) both require empty context, making them vacuously impossible in the deduction theorem when context is `A :: Gamma`.
- The 26 axioms (4 propositional + 22 BX temporal) are all assigned `FrameClass.Base`, meaning soundness targets serial linear orders.
- The canonical model construction for temporal logic defines `S < T` via `{phi | G(phi) in S} subset T` and `{phi | H(phi) in T} subset S`, using linearity axioms BX7/BX7'/BX11/BX11' for totality.
- Until/Since witness conditions in MCS require enrichment axioms (BX13/BX13') and absorption axioms (BX5/BX5'/BX6/BX6').

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Implement `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean` with height function, Deriv wrapper, and `temporalDerivationSystem` instance
- Prove the deduction theorem for the 6-constructor temporal DerivationTree
- Instantiate generic MCS framework and prove temporal-specific witness conditions for Until/Since
- Prove soundness of all 26 BX axioms over serial linear temporal orders
- Prove completeness via canonical linear model with truth lemma for all 5 formula constructors
- Create barrel import `Cslib/Logics/Temporal/Metalogic.lean`
- All files compile with zero `sorry`, zero linter warnings

**Non-Goals**:
- Density-specific or discreteness-specific soundness/completeness (future extension)
- Decidability or tableau methods for temporal logic
- Finite model property
- Integration with bimodal logic (separate task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Canonical linear order construction complexity | H | M | Follow Burgess (1982) construction; use BX7/BX11 linearity axioms directly; lean on existing `TemporalDerived` theorems for G/H distribution |
| Until/Since witness lemmas require intricate axiom combinations | H | M | Research report identifies exact axioms needed (BX5/BX6/BX10/BX13); modal `mcs_box_witness` provides structural template |
| 26-axiom soundness proof is verbose | M | H | Group axioms by pattern (propositional, monotonicity, connectedness, linearity); use `Satisfies` simp lemmas extensively |
| `swap_temporal` soundness case is novel (no modal analog) | M | M | Prove standalone duality lemma by formula induction; the `swap_temporal` involution is already defined in `Formula.lean` |
| Generic MCS framework API mismatch | L | L | Task 29 is complete and modal metalogic already instantiates it successfully; follow same pattern |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 (for 3), 1 (for 4) |
| 4 | 5 | 3, 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: DerivationTree Setup [COMPLETED]

**Goal**: Extend the existing `DerivationTree` with a computable height function, create `Deriv`/`Derivable` Prop wrappers, and instantiate `temporalDerivationSystem` for the generic MCS framework.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean` with imports from `Temporal.ProofSystem.Derivation` and `Foundations.Logic.Metalogic.Consistency`
- [ ] Define `DerivationTree.height` function for all 6 constructors (axiom/assumption -> 0; modus_ponens -> 1 + max; temporal_necessitation/temporal_duality/weakening -> 1 + recursive)
- [ ] Prove height ordering lemmas: `height_modus_ponens_left`, `height_modus_ponens_right`, `height_temporal_necessitation`, `height_temporal_duality`, `height_weakening` (each shows subderivation height is strictly less than parent)
- [ ] Define `Temporal.Deriv (Gamma : Context Atom) (phi : Formula Atom) : Prop := Nonempty (DerivationTree FrameClass.Base Gamma phi)`
- [ ] Define `Temporal.Derivable (phi : Formula Atom) : Prop := Temporal.Deriv [] phi`
- [ ] Prove basic combinators: `mp_deriv`, `weakening_deriv`, `assumption_deriv` wrapping tree constructors
- [ ] Define `temporalDerivationSystem : Metalogic.DerivationSystem (Formula Atom)` providing Deriv, weakening, assumption, mp
- [ ] Verify `Formula Atom` has `HasBot` and `HasImp` instances (required by `DerivationSystem`); create them if missing

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean` - new file (~150 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.DerivationTree` passes with zero errors
- `grep -r sorry Cslib/Logics/Temporal/Metalogic/DerivationTree.lean` returns empty

---

### Phase 2: Deduction Theorem [COMPLETED]

**Goal**: Prove the deduction theorem for the temporal proof system by well-founded recursion on DerivationTree height, handling all 6 constructors.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` importing `DerivationTree`
- [ ] Define `removeAll` helper for list manipulation (or reuse from Mathlib if available)
- [ ] Implement `deduction_axiom` helper: given axiom `ax phi`, produce derivation of `A -> phi`
- [ ] Implement `deduction_imp_self` helper: produce derivation of `A -> A` via `implyK` and `implyS`
- [ ] Implement `deduction_assumption_other` helper: given `phi in Gamma` with `phi != A`, produce derivation of `A -> phi`
- [ ] Implement `deduction_mp` helper: combine `A -> (phi -> psi)` and `A -> phi` to get `A -> psi` via `implyS`
- [ ] Implement `deduction_with_mem` helper for the weakening subcase when `A in Gamma'`
- [ ] Prove `deduction_theorem`: for `d : DerivationTree fc (A :: Gamma) phi`, produce `DerivationTree fc Gamma (A.imp phi)` by well-founded recursion on `d.height`, with 6 cases:
  - `axiom`: wrap with `deduction_axiom`
  - `assumption` (A = phi): use `deduction_imp_self`
  - `assumption` (phi in Gamma, phi != A): use `deduction_assumption_other`
  - `modus_ponens`: recurse on both sub-derivations, combine with `deduction_mp`
  - `temporal_necessitation`: context is `[]`, but we have `A :: Gamma` -- contradiction (vacuous)
  - `temporal_duality`: context is `[]`, but we have `A :: Gamma` -- contradiction (vacuous)
  - `weakening`: three subcases (Gamma' = A :: Gamma, A in Gamma', A not in Gamma')
- [ ] Define `temporal_has_deduction_theorem : Metalogic.HasDeductionTheorem temporalDerivationSystem` wrapping the theorem for the generic MCS framework

**Timing**: 4 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` - new file (~300 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.DeductionTheorem` passes with zero errors
- `grep -r sorry Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` returns empty

---

### Phase 3: MCS Theory [COMPLETED]

**Goal**: Instantiate the generic MCS framework for temporal logic and prove temporal-specific MCS properties including Until/Since witness conditions needed for the canonical model truth lemma.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Metalogic/MCS.lean` importing `DeductionTheorem`
- [ ] Define abbreviations: `Temporal.SetConsistent`, `Temporal.SetMaximalConsistent` using `temporalDerivationSystem`
- [ ] Instantiate generic properties from Consistency.lean:
  - `temporal_lindenbaum`: every consistent set extends to MCS
  - `temporal_closed_under_derivation`: derivable formulas are in MCS
  - `temporal_implication_property`: modus ponens reflected in membership
  - `temporal_negation_complete`: either `phi` or `neg phi` in every MCS
- [ ] Prove `mcs_bot_not_mem`: `bot` is not in any MCS
- [ ] Prove negation lemmas: `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem`
- [ ] Prove `mcs_and_mem` and `mcs_or_mem`: conjunction/disjunction membership lemmas
- [ ] Prove G/H closure properties using derived theorems from `TemporalDerived`:
  - `mcs_all_future_mp`: if `G(phi -> psi) in S` and `G(phi) in S` then `G(psi) in S`
  - `mcs_all_past_mp`: symmetric for H
- [ ] Prove Until/Since membership properties:
  - `mcs_until_implies_some_future`: if `phi U psi in S` then `F(psi) in S` (via BX10)
  - `mcs_since_implies_some_past`: if `phi S psi in S` then `P(psi) in S` (via BX10')
- [ ] Prove Until witness lemma: if `phi U psi in S`, then there exists an MCS `T` such that the temporal ordering `S < T` holds, `psi in T`, and `phi` holds at all intermediate MCS. This uses BX5 (self-accumulation), BX13 (enrichment), and Lindenbaum's lemma.
- [ ] Prove Since witness lemma: symmetric to Until, using BX5'/BX13' and looking to the past
- [ ] Prove G-set consistency: if `G(phi) not in S`, then `{chi | G(chi) in S} union {neg phi}` is consistent (needed for canonical order construction)

**Timing**: 5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` - new file (~400 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.MCS` passes with zero errors
- `grep -r sorry Cslib/Logics/Temporal/Metalogic/MCS.lean` returns empty

---

### Phase 4: Soundness [COMPLETED]

**Goal**: Prove that every derivable formula is valid over serial linear temporal orders (models with `LinearOrder D`, `NoMaxOrder D`, `NoMinOrder D`).

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Metalogic/Soundness.lean` importing `DerivationTree` and `Temporal.Semantics.Validity`
- [ ] Prove `axiom_sound` handling all 26 axiom constructors:
  - Propositional (4): `imp_k`, `imp_s`, `efq`, `peirce` -- straightforward, valid in all models
  - Seriality (2): `serial_future`, `serial_past` -- use `NoMaxOrder`/`NoMinOrder` to obtain witnesses
  - Monotonicity (4): `left_mono_until_G`, `left_mono_since_H`, `right_mono_until`, `right_mono_since` -- unfold `Satisfies` for Until/Since/G/H, apply hypotheses
  - Connectedness (2): `connect_future`, `connect_past` -- use linear order transitivity
  - Enrichment (2): `enrichment_until`, `enrichment_since` -- combine Until/Since witnesses using enrichment structure
  - Self-accumulation (2): `self_accum_until`, `self_accum_since` -- strengthen Until/Since witnesses
  - Absorption (2): `absorb_until`, `absorb_since` -- collapse nested Until/Since using transitivity
  - Linearity (4): `linear_until`, `linear_since`, `temp_linearity`, `temp_linearity_past` -- case-split on linear order comparability of witness times
  - Until/Since-eventuality (2): `until_F`, `since_P` -- extract existential witness from Until/Since
  - F-Until/P-Since equivalence (2): `F_until_equiv`, `P_since_equiv` -- relate F to Until with trivial guard
- [ ] Prove `swap_temporal_satisfies` lemma: relate `Satisfies M t (swap_temporal phi)` to satisfaction of the time-reversed formula (by induction on `phi`)
- [ ] Prove `soundness`: by structural induction on `DerivationTree` with 6 cases:
  - `axiom`: apply `axiom_sound`
  - `assumption`: extract from context satisfaction
  - `modus_ponens`: apply IH to both sub-derivations, combine via implication satisfaction
  - `temporal_necessitation`: show `G(phi)` is satisfied (phi satisfied at all strictly future times)
  - `temporal_duality`: use `swap_temporal_satisfies` lemma
  - `weakening`: context monotonicity (subset of satisfied formulas)
- [ ] Prove `soundness_derivable`: specialize to empty context

**Timing**: 4 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean` - new file (~350 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Soundness` passes with zero errors
- `grep -r sorry Cslib/Logics/Temporal/Metalogic/Soundness.lean` returns empty

---

### Phase 5: Completeness [IN PROGRESS]

**Goal**: Prove completeness for temporal BX logic via the canonical linear model construction: every formula valid over all serial linear temporal orders is derivable.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Metalogic/Completeness.lean` importing `MCS` and `Soundness`
- [ ] Define `CanonicalWorld (Atom : Type*) := { S : Set (Formula Atom) // Temporal.SetMaximalConsistent S }`
- [ ] Define canonical temporal order on `CanonicalWorld`:
  - `canonical_lt S T := (forall phi, phi.all_future in S.val -> phi in T.val) and (forall phi, phi.all_past in T.val -> phi in S.val)` (strict future relation)
  - `canonical_le` extending `canonical_lt` with equality
- [ ] Prove canonical order properties:
  - Irreflexivity: using connectedness axioms BX4/BX4' and MCS properties
  - Transitivity: using G/H distribution (G(phi) -> G(G(phi)) derived via BX4 + temporal necessitation)
  - Totality: using linearity axioms BX11/BX11' and temporal linearity
- [ ] Prove seriality of canonical order:
  - `canonical_no_max`: using BX1 (serial_future) and G-set consistency lemma from MCS
  - `canonical_no_min`: using BX1' (serial_past) and H-set consistency lemma from MCS
- [ ] Define `CanonicalModel (Atom : Type*) : TemporalModel (CanonicalWorld Atom) Atom` with:
  - Linear order from canonical order proofs
  - `valuation S p := Formula.atom p in S.val`
- [ ] Prove `truth_lemma` by structural induction on formula:
  - `atom p`: by definition of canonical valuation
  - `bot`: by `mcs_bot_not_mem`
  - `imp phi psi`: by `temporal_implication_property` and `temporal_negation_complete`
  - `untl phi psi` (Until): forward direction uses Until witness lemma from MCS; reverse direction uses Until membership closure under the canonical order
  - `snce phi psi` (Since): symmetric to Until case
- [ ] Prove `completeness`: by contrapositive -- if `phi` is not derivable, then `{neg phi}` is consistent, extends to an MCS via `temporal_lindenbaum`, and the truth lemma shows `neg phi` is satisfied at that world, so `phi` is not valid

**Timing**: 5 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` - new file (~450 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Completeness` passes with zero errors
- `grep -r sorry Cslib/Logics/Temporal/Metalogic/Completeness.lean` returns empty

---

### Phase 6: Barrel Import and Final Verification [COMPLETED]

**Goal**: Create the barrel import file, run full project build, and verify zero sorry / zero linter warnings across all new files.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Metalogic.lean` barrel import with:
  ```
  import Cslib.Logics.Temporal.Metalogic.DerivationTree
  import Cslib.Logics.Temporal.Metalogic.DeductionTheorem
  import Cslib.Logics.Temporal.Metalogic.MCS
  import Cslib.Logics.Temporal.Metalogic.Soundness
  import Cslib.Logics.Temporal.Metalogic.Completeness
  ```
- [ ] Run `lake build` for full project verification
- [ ] Run `grep -rn sorry Cslib/Logics/Temporal/Metalogic/` to confirm zero sorry occurrences
- [ ] Run linter check across all 5 metalogic files
- [ ] Verify total line count is approximately 1,500 lines (within 10% tolerance)

**Timing**: 1 hour

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic.lean` - new barrel import file (~10 lines)

**Verification**:
- `lake build` passes with zero errors across entire project
- `grep -rn sorry Cslib/Logics/Temporal/Metalogic/` returns empty
- All 6 new files present in `Cslib/Logics/Temporal/Metalogic/`

## Testing & Validation

- [ ] Each phase passes `lake build` for its specific module
- [ ] Full `lake build` passes after all phases complete
- [ ] Zero `sorry` occurrences in any file under `Cslib/Logics/Temporal/Metalogic/`
- [ ] Zero linter warnings with `set_option linter.all true`
- [ ] `temporalDerivationSystem` successfully instantiates `Metalogic.DerivationSystem`
- [ ] `temporal_has_deduction_theorem` successfully instantiates `Metalogic.HasDeductionTheorem`
- [ ] Completeness theorem type: `Temporal.Derivable phi` from validity hypothesis
- [ ] Soundness theorem type: validity from `Temporal.Derivable phi`

## Artifacts & Outputs

- `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean` (~150 lines)
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` (~300 lines)
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` (~400 lines)
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean` (~350 lines)
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` (~450 lines)
- `Cslib/Logics/Temporal/Metalogic.lean` (~10 lines, barrel import)
- Total: ~1,660 lines across 6 files

## Rollback/Contingency

All new files are in the new directory `Cslib/Logics/Temporal/Metalogic/`. No existing files are modified. Rollback is a clean deletion:
```bash
rm -rf Cslib/Logics/Temporal/Metalogic/
rm -f Cslib/Logics/Temporal/Metalogic.lean
```

If specific phases encounter blockers (particularly the canonical linear order construction in Phase 5 or the Until/Since witness lemmas in Phase 3), mark the phase `[BLOCKED]` and document the specific goal state. These phases can use `sorry` as temporary placeholders while other phases proceed, with sorry elimination tracked as follow-up.
