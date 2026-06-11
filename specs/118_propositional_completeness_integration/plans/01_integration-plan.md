# Implementation Plan: Propositional Completeness Integration (Task 118)

## Goals

**Goals**: `modal_satisfies_toModal_iff_evaluate`, `tautology_toModal_valid`, `toModal_valid_implies_tautology`, `tautology_iff_toModal_valid`

## Phases

### Phase 1: Add missing imports to Cslib.lean [COMPLETED]

- [x] **Task 1.1**: Add 10 missing imports for Semantics and Metalogic modules to Cslib.lean

### Phase 2: Semantic coherence theorem in FromPropositional.lean [COMPLETED]

- [x] **Task 2.1**: Add import for Cslib.Logics.Propositional.Semantics.Basic
- [x] **Task 2.2**: Prove `modal_satisfies_toModal_iff_evaluate` bridge lemma
- [x] **Task 2.3**: Prove `tautology_toModal_valid` forward direction
- [x] **Task 2.4**: Prove `toModal_valid_implies_tautology` backward direction
- [x] **Task 2.5**: Prove `tautology_iff_toModal_valid` full coherence biconditional

### Phase 3: Verification [COMPLETED]

- [x] **Task 3.1**: Run full `lake build`
- [x] **Task 3.2**: Run `lean_verify` on completeness theorems
- [x] **Task 3.3**: Confirm no sorry, no non-standard axioms

## Risks

- None identified: prototype compiles, imports exist, build is clean
