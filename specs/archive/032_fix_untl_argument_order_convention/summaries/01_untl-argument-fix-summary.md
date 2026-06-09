# Execution Summary: Fix untl/snce Argument Order Convention

- **Task**: 32 - Fix untl/snce argument order to match standard literature convention
- **Status**: Implemented
- **Duration**: ~2 hours
- **Phases**: 6/6 completed

## Changes Made

### Phase 1: Semantic Root Fix (Truth.lean)
- Swapped `φ` and `ψ` roles in `truth_at` for both `Formula.untl` and `Formula.snce` branches
- After: `untl φ ψ` has φ=EVENT (at witness s), ψ=GUARD (in interval)
- Updated all induction hypothesis references in `truth_double_shift_cancel` and `time_shift_preserves_truth` proofs
- Fixed `future_iff` and `past_iff` proofs (changed `fun hs => hns hs` to `hns`)

### Phase 2: Syntax Layer (both Formula.lean files)
- **Temporal Formula.lean**: Updated 8 derived operators:
  - `some_future φ`: `.untl .top φ` -> `.untl φ .top`
  - `some_past φ`: `.snce .top φ` -> `.snce φ .top`
  - `next φ`: `.untl .bot φ` -> `.untl φ .bot`
  - `prev φ`: `.snce .bot φ` -> `.snce φ .bot`
  - `release φ ψ`: `untl (neg φ) (neg ψ)` -> `untl (neg ψ) (neg φ)`
  - `trigger φ ψ`: `snce (neg φ) (neg ψ)` -> `snce (neg ψ) (neg φ)`
  - `strong_release φ ψ`: `untl ψ (and ψ φ)` -> `untl (and ψ φ) ψ`
  - `strong_trigger φ ψ`: `snce ψ (and ψ φ)` -> `snce (and ψ φ) ψ`
- Updated all 8 complexity function pattern-matching arms
- **Bimodal Formula.lean**: Updated `some_future` and `some_past`

### Phase 3: Foundation Axioms and ProofSystem
- Updated G/H/F/P encodings in 12 axiom abbreviations (BX2G, BX2H, BX3, BX3', BX4, BX4', BX10, BX10', BX11, BX11', BX12, BX12')
- Updated ModalFuture interaction axiom
- Updated `tempNec` and `tempNecPast` in ProofSystem.lean
- Variable-only axioms (BX5, BX5', BX6, BX6', BX7, BX7', BX13, BX13') unchanged

### Phase 4: Temporal Proof System Axiom Constructors
- Auto-updated via `abbrev` propagation from Phase 2
- All constructors verified to type-check

### Phase 5: Derived Theorems (TemporalDerived.lean)
- Updated `someFuture`/`somePast` private abbreviations
- **Critical change**: `F_mono`/`P_mono` now use BX3 (RightMonoUntil) / BX3' (RightMonoSince) instead of BX2G/BX2H, because F(φ) = untl(φ, top) has φ in EVENT position (arg1), and event monotonicity is BX3
- Updated `G_distribution`, `H_distribution`, `G_contrapose`, `H_contrapose` similarly

### Phase 6: Full Build Verification
- Full `lake build` passes (2756 jobs, 0 errors)
- Zero sorries, zero new axioms, zero vacuous definitions
- No remaining old-convention patterns (`untl .top` or `snce .top`)
- Subformulas.lean path navigation updated for swapped args

## Files Modified (8 files)
1. `Cslib/Logics/Bimodal/Semantics/Truth.lean` - Semantic swap + proof fixes
2. `Cslib/Logics/Temporal/Syntax/Formula.lean` - Derived operators + complexity patterns
3. `Cslib/Logics/Bimodal/Syntax/Formula.lean` - Derived operators
4. `Cslib/Foundations/Logic/Axioms.lean` - Axiom abbreviations
5. `Cslib/Foundations/Logic/ProofSystem.lean` - tempNec/tempNecPast
6. `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` - Proof re-derivation
7. `Cslib/Logics/Temporal/Syntax/Subformulas.lean` - Path navigation fix
8. `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` - Auto-updated (no manual changes)

## Files NOT Modified (as planned)
- `Cslib/Foundations/Logic/Connectives.lean` - Typeclass interface only
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` - Position-preserving, symmetric
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` - Auto-updated via abbrevs

## Plan Deviations
- Subformulas.lean required path navigation fix (not anticipated in plan, which said "no changes needed" -- the plan was correct that subformula closure is symmetric, but the proof navigation through the structure is position-dependent)

## BX12/BX12' Note
Under the corrected convention, BX12 becomes `F(φ) → F(φ)` (trivially valid) since both `some_future φ` and `untl φ top` encode the same formula. This is documented in the axiom docstring.
