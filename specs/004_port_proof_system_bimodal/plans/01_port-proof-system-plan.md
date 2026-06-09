# Implementation Plan: Port Bimodal Hilbert-Style Proof System

- **Task**: 4 - Port the Bimodal Hilbert-style proof system to Cslib
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: Tasks 2 (Bimodal Syntax), 20 (Propositional Theorems), 22 (Temporal Infrastructure), 32 (untl argument order fix) -- all completed
- **Research Inputs**: specs/004_port_proof_system_bimodal/reports/01_port-proof-system-research.md
- **Artifacts**: plans/01_port-proof-system-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Port the Bimodal Hilbert-style proof system from BimodalLogic to `Cslib/Logics/Bimodal/ProofSystem/`. The bimodal proof system extends the temporal BX system with S5 modal axioms and the modal-future interaction axiom MF, producing a 42-axiom system with 7 inference rules. The implementation closely follows the existing `Cslib/Logics/Temporal/ProofSystem/` template, adding modal operators (box, diamond) and the necessitation inference rule.

### Research Integration

Key findings from the research report (01_port-proof-system-research.md):
- 42 axiom constructors in 8 layers: propositional (4), S5 modal (5), BX temporal (22), interaction (1), uniformity (5), Prior (2), Z1 (1), density (2)
- 7 inference rules in DerivationTree (temporal has 6; bimodal adds `necessitation` for modal box)
- Naming swap: BimodalLogic `prop_k` = cslib `ImplyS`, `prop_s` = cslib `ImplyK` (already handled in temporal template)
- Argument order: consistent `untl(event, guard)` convention -- no swapping needed
- Prerequisites needed: `swap_temporal` (with box case) and `Formula.atoms` must be added to bimodal Formula.lean
- The `modal_5_collapse` axiom exists in the Axiom inductive but is not required by any typeclass

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the "Bimodal Porting" track. It is the critical prerequisite for tasks 5 (Perpetuity Theorems), 6 (Frame Conditions + Soundness), 7 (Deduction + MCS), 9 (Decidability/Tableau), 10 (Separation), and 11 (Conservative Extension).

## Goals & Non-Goals

**Goals**:
- Add `swap_temporal` and `Formula.atoms` to bimodal Formula.lean as prerequisites
- Create concrete 42-constructor `Axiom` inductive with `FrameClass` gating
- Create `DerivationTree` with 7 inference rules (including modal necessitation)
- Create `Derivable` Prop-valued wrapper with constructor-mirroring lemmas
- Create uniform substitution theorem (`Formula.subst`, `axiom_subst`, `derivation_subst`)
- Register `BimodalTMHilbert` instance for `Bimodal.HilbertTM` tag type
- Port `LinearityDerivedFacts` documentation and convenience definition

**Non-Goals**:
- Porting derived theorems (Task 5)
- Frame conditions or soundness proofs (Task 6)
- Deduction theorem or MCS theory (Task 7)
- Adding new typeclasses beyond what already exists in ProofSystem.lean

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `swap_temporal` with box case creates type-checking issues | M | L | Follow temporal template exactly; box maps to box (self-dual under temporal swap) |
| 42-case `axiom_subst` proof is tedious and error-prone | M | M | Mechanical 1:1 port from BimodalLogic; use `simp` where possible |
| Namespace conflicts with Temporal scoped notation | M | L | Use `scoped` notation in Bimodal namespace; do not open Temporal |
| `Finset` import needed for `Formula.atoms` pulls in Mathlib dependencies | L | M | Verify import with `lake build` early in Phase 1 |
| TemporalNecessitation instance requires `swap_temporal` distributional lemmas | M | L | Phase 1 includes all needed distributional lemmas |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases are fully sequential: each phase depends on the one before it.

---

### Phase 1: Prerequisites -- Formula Extensions [COMPLETED]

**Goal**: Add `swap_temporal` (with box case) and `Formula.atoms` to the bimodal Formula module, providing the infrastructure needed by DerivationTree and Substitution.

**Tasks**:
- [ ] Add `swap_temporal : Formula Atom -> Formula Atom` function with cases for all 6 constructors (atom, bot, imp, box, untl, snce). The box case maps `box(swap_temporal phi)` (box is self-dual under temporal swap)
- [ ] Add `swap_temporal_involution` theorem proving `phi.swap_temporal.swap_temporal = phi`
- [ ] Add distributional lemmas: `swap_temporal_neg`, `swap_temporal_diamond`, `swap_temporal_some_future`, `swap_temporal_some_past`, `swap_temporal_all_future`, `swap_temporal_all_past`
- [ ] Add `Formula.atoms [DecidableEq Atom] : Formula Atom -> Finset Atom` function with cases for all 6 constructors
- [ ] Add necessary imports for `Finset` (likely `Mathlib.Data.Finset.Basic` or similar)
- [ ] Verify `lake build Cslib.Logics.Bimodal.Syntax.Formula` passes

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` -- add swap_temporal, atoms, and distributional lemmas

**Verification**:
- `lake build Cslib.Logics.Bimodal.Syntax.Formula` passes with zero errors
- `swap_temporal_involution` is proven without sorry
- All distributional lemmas proven without sorry

---

### Phase 2: Axioms -- 42-Constructor Inductive and FrameClass [COMPLETED]

**Goal**: Create the concrete Axiom inductive type with all 42 constructors organized in 8 layers, plus FrameClass type with ordering instances.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean`
- [ ] Port `FrameClass` inductive (`Base | Dense | Discrete`) with `LE`, `DecidableRel`, `PartialOrder` instances (follow temporal template exactly)
- [ ] Port `FrameClass.base_le` theorem
- [ ] Port 4 propositional axiom constructors: `imp_k`, `imp_s`, `efq`, `peirce`
- [ ] Port 5 S5 modal axiom constructors: `modal_t`, `modal_4`, `modal_b`, `modal_5_collapse`, `modal_k_dist`
- [ ] Port 22 BX temporal axiom constructors (identical to temporal Axioms.lean): `serial_future`, `serial_past`, `left_mono_until_G`, `left_mono_since_H`, `right_mono_until`, `right_mono_since`, `connect_future`, `connect_past`, `enrichment_until`, `enrichment_since`, `self_accum_until`, `self_accum_since`, `absorb_until`, `absorb_since`, `linear_until`, `linear_since`, `until_F`, `since_P`, `temp_linearity`, `temp_linearity_past`, `F_until_equiv`, `P_since_equiv`
- [ ] Port 1 interaction axiom constructor: `modal_future` (MF: box(phi) -> box(G(phi)))
- [ ] Port 5 uniformity axiom constructors: `discrete_symm_fwd`, `discrete_symm_bwd`, `discrete_propagate_fwd`, `discrete_propagate_bwd`, `discrete_box_necessity`
- [ ] Port 2 Prior axiom constructors: `prior_UZ`, `prior_SZ`
- [ ] Port 1 Z1 axiom constructor: `z1`
- [ ] Port 2 density axiom constructors: `density`, `dense_indicator`
- [ ] Port `Axiom.minFrameClass` function mapping each constructor to its minimum frame class (propositional+modal+temporal+interaction -> Base; density -> Dense; uniformity+Prior+Z1 -> Discrete)
- [ ] Verify `lake build Cslib.Logics.Bimodal.ProofSystem.Axioms` passes

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean` -- create new file (~450 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.ProofSystem.Axioms` passes with zero errors
- All 42 constructors are present
- `minFrameClass` returns correct frame class for each axiom layer

---

### Phase 3: DerivationTree -- 7 Inference Rules [NOT STARTED]

**Goal**: Create the DerivationTree inductive type with 7 inference rules, lift function, and scoped notation.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean`
- [ ] Port `DerivationTree fc Gamma phi` inductive with 7 rules:
  - `axiom` -- gated by `h.minFrameClass <= fc`
  - `assumption` -- membership in context
  - `modus_ponens` -- implication elimination
  - `necessitation` -- from empty context, derive `box(phi)` (NEW vs temporal)
  - `temporal_necessitation` -- from empty context, derive `G(phi)`
  - `temporal_duality` -- from empty context, derive `swap_temporal(phi)`
  - `weakening` -- context monotonicity
- [ ] Port `DerivationTree.lift` for frame class monotonicity (7 cases, one per rule)
- [ ] Add scoped notation: `Gamma |- phi`, `Gamma |-[fc] phi`, `|- phi` (scoped to avoid conflicts with temporal notation)
- [ ] Verify `lake build Cslib.Logics.Bimodal.ProofSystem.Derivation` passes

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` -- create new file (~300 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.ProofSystem.Derivation` passes with zero errors
- All 7 inference rules are present
- `lift` handles all 7 cases

---

### Phase 4: Derivable -- Prop-Valued Wrapper [NOT STARTED]

**Goal**: Create the Prop-valued derivability wrapper with constructor-mirroring lemmas.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/ProofSystem/Derivable.lean`
- [ ] Define `Bimodal.Derivable fc Gamma p := Nonempty (DerivationTree fc Gamma p)`
- [ ] Port `Derivable.ofTree` coercion
- [ ] Port `Derivable.lift` for frame class monotonicity
- [ ] Port 7 constructor-mirroring lemmas: `ax`, `assume`, `mp`, `nec` (NEW), `temp_nec`, `temp_dual`, `weaken`
- [ ] Verify `lake build Cslib.Logics.Bimodal.ProofSystem.Derivable` passes

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Bimodal/ProofSystem/Derivable.lean` -- create new file (~180 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.ProofSystem.Derivable` passes with zero errors
- All 7 constructor-mirroring lemmas are proven without sorry

---

### Phase 5: Substitution -- Uniform Substitution Theorem [NOT STARTED]

**Goal**: Port the uniform substitution infrastructure including `Formula.subst`, structural lemmas, `axiom_subst` (42 cases), and the main `derivation_subst` theorem.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean`
- [ ] Port `Formula.subst q r : Formula Atom -> Formula Atom` (substitute atom q with atom r)
- [ ] Port structural simp lemmas: `subst_atom_eq`, `subst_atom_ne`, `subst_bot`, `subst_imp`, `subst_box`, `subst_untl`, `subst_snce`
- [ ] Port derived operator substitution lemmas: `subst_neg`, `subst_and`, `subst_or`, `subst_diamond`, `subst_some_future`, `subst_some_past`, `subst_all_future`, `subst_all_past`
- [ ] Port `subst_fresh_eq` (freshness preservation)
- [ ] Port `subst_atoms` (atoms of substituted formula)
- [ ] Port `Context.subst` and `atoms_of_context` with membership lemmas
- [ ] Port `swap_temporal_subst` (commutativity of swap and substitution)
- [ ] Port `axiom_subst` (42-case proof that axioms are closed under substitution)
- [ ] Port `axiom_subst_minFrameClass` (frame class preservation under substitution)
- [ ] Port `derivation_subst` main theorem (7-case proof that derivations are closed under substitution)
- [ ] Verify `lake build Cslib.Logics.Bimodal.ProofSystem.Substitution` passes

**Timing**: 2.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` -- create new file (~450 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.ProofSystem.Substitution` passes with zero errors
- `derivation_subst` is proven without sorry
- `axiom_subst` covers all 42 axiom constructors

---

### Phase 6: Instance Registration and LinearityDerivedFacts [NOT STARTED]

**Goal**: Register all typeclass instances connecting the concrete DerivationTree to the abstract `BimodalTMHilbert` typeclass, and port the linearity derived facts.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/ProofSystem/Instances.lean`
- [ ] Register `InferenceSystem Bimodal.HilbertTM (Bimodal.Formula Atom)` mapping `derivation phi` to `DerivationTree .Base [] phi`
- [ ] Register `ModusPonens` instance (via `modus_ponens` rule)
- [ ] Register `Necessitation` instance (via `necessitation` rule -- NEW vs temporal)
- [ ] Register 4 propositional `HasAxiom*` instances with name swap: `HasAxiomImplyK` (via `imp_s`), `HasAxiomImplyS` (via `imp_k`), `HasAxiomEFQ` (via `efq`), `HasAxiomPeirce` (via `peirce`)
- [ ] Register `PropositionalHilbert` bundled instance
- [ ] Register 4 modal `HasAxiom*` instances: `HasAxiomK` (via `modal_k_dist`), `HasAxiomT` (via `modal_t`), `HasAxiom4` (via `modal_4`), `HasAxiomB` (via `modal_b`)
- [ ] Register `ModalHilbert` and `ModalS5Hilbert` bundled instances
- [ ] Register `TemporalNecessitation` instance (via `temporal_necessitation` + `temporal_duality` for past direction, following temporal template pattern)
- [ ] Register 22 temporal `HasAxiom*` instances (one per BX axiom, following temporal Instances.lean template exactly)
- [ ] Register `TemporalBXHilbert` bundled instance
- [ ] Register `HasAxiomMF` instance (via `modal_future` axiom constructor)
- [ ] Register `BimodalTMHilbert` bundled instance (the final composition)
- [ ] Create `Cslib/Logics/Bimodal/ProofSystem/LinearityDerivedFacts.lean`
- [ ] Port `temp_linearity_derivation` convenience definition
- [ ] Port documentation about non-derivability of linearity from base axioms
- [ ] Verify `lake build Cslib.Logics.Bimodal.ProofSystem.Instances` passes
- [ ] Verify `lake build Cslib.Logics.Bimodal.ProofSystem.LinearityDerivedFacts` passes
- [ ] Run full `lake build` to confirm no regressions

**Timing**: 2 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` -- create new file (~220 lines)
- `Cslib/Logics/Bimodal/ProofSystem/LinearityDerivedFacts.lean` -- create new file (~70 lines)

**Verification**:
- `lake build Cslib.Logics.Bimodal.ProofSystem.Instances` passes with zero errors
- `BimodalTMHilbert Bimodal.HilbertTM (F := Bimodal.Formula Atom)` instance resolves
- Full `lake build` passes with zero errors
- Zero sorry occurrences across all new files

---

## Testing & Validation

- [ ] `lake build` passes with zero errors after all phases
- [ ] `grep -r sorry Cslib/Logics/Bimodal/ProofSystem/` returns zero matches
- [ ] `grep -r sorry Cslib/Logics/Bimodal/Syntax/Formula.lean` returns zero matches for new additions
- [ ] All 42 axiom constructors are present in Axioms.lean
- [ ] All 7 inference rules are present in Derivation.lean
- [ ] `BimodalTMHilbert` instance resolves for `Bimodal.HilbertTM`
- [ ] `axiom_subst` covers all 42 axiom cases
- [ ] `derivation_subst` covers all 7 rule cases
- [ ] No namespace conflicts with Temporal scoped notation

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/Syntax/Formula.lean` -- extended with swap_temporal + atoms (~100 lines added)
- `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean` -- new file (~450 lines)
- `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` -- new file (~300 lines)
- `Cslib/Logics/Bimodal/ProofSystem/Derivable.lean` -- new file (~180 lines)
- `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` -- new file (~450 lines)
- `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` -- new file (~220 lines)
- `Cslib/Logics/Bimodal/ProofSystem/LinearityDerivedFacts.lean` -- new file (~70 lines)

## Rollback/Contingency

All new files are in `Cslib/Logics/Bimodal/ProofSystem/` (new directory) and additions to Formula.lean. Rollback:
1. Delete all files in `Cslib/Logics/Bimodal/ProofSystem/`
2. Revert additions to `Cslib/Logics/Bimodal/Syntax/Formula.lean`
3. Run `lake build` to confirm clean state

If individual phases fail:
- Phase 1 (prerequisites): Can be developed independently in a separate file if Formula.lean conflicts arise
- Phase 5 (substitution): If `axiom_subst` is too difficult, the file can be deferred without blocking instance registration (Phase 6 does not depend on substitution for typeclass instances)
- Phase 6 (instances): If `TemporalNecessitation` instance is problematic, the `swap_temporal` distributional lemmas from Phase 1 should resolve it (same pattern as temporal template)
