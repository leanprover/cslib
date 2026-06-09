# Implementation Summary: Port Bimodal Hilbert-Style Proof System

**Task**: 4
**Status**: Implemented
**Session**: sess_1780980276_702f7c_4
**Date**: 2026-06-08

## Changes

### Phase 1: Formula Prerequisites
- Added `Formula.swap_temporal` with box case (6 constructors)
- Added `swap_temporal_involution` theorem
- Added distributional lemmas: `swap_temporal_neg`, `swap_temporal_diamond`, `swap_temporal_some_future`, `swap_temporal_some_past`, `swap_temporal_all_future`, `swap_temporal_all_past`
- Added `Formula.atoms` function (requires `DecidableEq Atom`, `Finset`)
- Added `atoms_swap_temporal` preservation theorem
- **File**: `Cslib/Logics/Bimodal/Syntax/Formula.lean` (import added: `Mathlib.Data.Finset.Basic`)

### Phase 2: Axioms (42 constructors)
- Created `FrameClass` inductive (`Base | Dense | Discrete`) with `LE`, `DecidableRel`, `PartialOrder`
- Created `Axiom` inductive with 42 constructors across 8 layers:
  - Propositional (4): `imp_k`, `imp_s`, `efq`, `peirce`
  - S5 Modal (5): `modal_t`, `modal_4`, `modal_b`, `modal_5_collapse`, `modal_k_dist`
  - BX Temporal (22): all 22 BX axioms
  - Interaction (1): `modal_future`
  - Uniformity (5): `discrete_symm_fwd/bwd`, `discrete_propagate_fwd/bwd`, `discrete_box_necessity`
  - Prior (2): `prior_UZ`, `prior_SZ`
  - Z1 (1): `z1`
  - Density (2): `density`, `dense_indicator`
- Created `Axiom.minFrameClass` function and `FrameClass.base_le` theorem
- **File**: `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean`

### Phase 3: DerivationTree (7 rules)
- Created `DerivationTree` inductive with 7 rules: `axiom`, `assumption`, `modus_ponens`, `necessitation` (NEW), `temporal_necessitation`, `temporal_duality`, `weakening`
- Created `DerivationTree.lift` for frame class monotonicity (7 cases)
- Added scoped notations: `Gamma |- phi`, `Gamma |-[fc] phi`, `|- phi`
- **File**: `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean`

### Phase 4: Derivable
- Created `Bimodal.Derivable` Prop-valued wrapper using `Nonempty`
- Created 7 constructor-mirroring lemmas: `ax`, `assume`, `mp`, `nec`, `temp_nec`, `temp_dual`, `weaken`
- Created `Derivable.lift` for frame class monotonicity
- **File**: `Cslib/Logics/Bimodal/ProofSystem/Derivable.lean`

### Phase 5: Substitution
- Created `Formula.subst` function (6 constructor cases)
- Created 14 structural simp lemmas (7 primitive + 7 derived)
- Created `subst_fresh_eq`, `subst_atoms` theorems
- Created `Context.subst`, `atoms_of_context` with membership lemmas
- Created `axiom_subst` (42-case proof)
- Created `swap_temporal_subst` commutativity theorem
- Created `axiom_subst_minFrameClass` frame class preservation
- Created `derivation_subst` main theorem (7-case proof)
- **File**: `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean`

### Phase 6: Instance Registration + LinearityDerivedFacts
- Registered `InferenceSystem Bimodal.HilbertTM (Bimodal.Formula Atom)`
- Registered `ModusPonens`, `Necessitation` instances
- Registered 4 propositional `HasAxiom*` instances (with name swap)
- Registered 4 modal `HasAxiom*` instances (K, T, 4, B)
- Registered `ModalHilbert`, `ModalS5Hilbert` bundled instances
- Registered `TemporalNecessitation` with past direction via duality
- Registered 22 temporal `HasAxiom*` instances
- Registered `TemporalBXHilbert` bundled instance
- Registered `HasAxiomMF` instance
- Registered `BimodalTMHilbert` bundled instance (final composition)
- Ported `temp_linearity_derivation` convenience definition
- **Files**: `Cslib/Logics/Bimodal/ProofSystem/Instances.lean`, `Cslib/Logics/Bimodal/ProofSystem/LinearityDerivedFacts.lean`

## Verification

- Zero `sorry` occurrences across all new/modified files
- Zero vacuous definitions
- Zero new axioms
- All modules build successfully
- `BimodalTMHilbert` instance resolves for `Bimodal.HilbertTM`
- Pre-existing error in `Modal/Metalogic/Completeness.lean` is unrelated

## Plan Deviations

- None (implementation followed plan)

## Files Modified/Created

| File | Action | Lines |
|------|--------|-------|
| `Cslib/Logics/Bimodal/Syntax/Formula.lean` | Modified | +100 |
| `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean` | Created | ~300 |
| `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` | Created | ~120 |
| `Cslib/Logics/Bimodal/ProofSystem/Derivable.lean` | Created | ~130 |
| `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` | Created | ~510 |
| `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` | Created | ~290 |
| `Cslib/Logics/Bimodal/ProofSystem/LinearityDerivedFacts.lean` | Created | ~75 |
