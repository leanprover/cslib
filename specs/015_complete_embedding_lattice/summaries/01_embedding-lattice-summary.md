# Implementation Summary: Task #15

- **Task**: 15 - Complete embedding lattice: atom simp lemmas, PL.toBimodal, triangle-commutes
- **Status**: Implemented
- **Session**: sess_1780964944_adc2c6_15
- **Plan**: plans/01_embedding-lattice-plan.md

## Changes

### Phase 1: Add Atom Simp Lemmas
Added 4 `@[simp]` lemmas for the `atom` constructor across 3 files:
- `PL.Proposition.toModal_atom` and `PL.Proposition.toTemporal_atom` in `Cslib/Logics/Propositional/Embedding.lean`
- `Modal.Proposition.toBimodal_atom` in `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean`
- `Temporal.Formula.toBimodal_atom` in `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean`

All proofs are `rfl` (definitional equality).

### Phase 2: PL.toBimodal and Triangle-Commutes
Created `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` with:
- `PL.Proposition.toBimodal`: direct PL-to-Bimodal embedding (3 constructor cases)
- `instCoePLToBimodal`: Coe instance
- 4 simp lemmas: `toBimodal_atom`, `toBimodal_bot`, `toBimodal_imp`, `toBimodal_neg` (all `rfl`)
- `PL.Proposition.toModal_toBimodal`: commutation via Modal path (`induction ... <;> simp [*]`)
- `PL.Proposition.toTemporal_toBimodal`: commutation via Temporal path (`induction ... <;> simp [*]`)
- `PL.Proposition.embedding_commutes`: diamond commutation (`simp`)

### Phase 3: Root Import and Full Build
- Added `public import Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding` to `Cslib.lean`
- Full `lake build` passes with zero errors

## Verification
- 0 `sorry` occurrences in all modified/created files
- 0 vacuous definitions
- 0 new axioms
- Full project build: pass (2730 jobs)

## Files Modified
- `Cslib/Logics/Propositional/Embedding.lean` (+2 simp lemmas)
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` (+1 simp lemma)
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` (+1 simp lemma)
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` (new file)
- `Cslib.lean` (+1 import line)

## Plan Deviations
- None (implementation followed plan)
