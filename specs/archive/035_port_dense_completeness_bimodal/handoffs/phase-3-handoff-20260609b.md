# Phase 3 Handoff - Task 35 (Session 2)

## Status
Phase 2 COMPLETED. Phase 3 IN PROGRESS (3/6 files: FMCSDef, FMCS, TemporalContent done).

## What Was Done This Session
- Phase 2: BooleanStructure.lean (447 lines), InteriorOperators.lean (191 lines, 1 sorry resolved), UltrafilterMCS.lean (1053 lines) -- all compiling
- Phase 3 partial: FMCSDef.lean, FMCS.lean, TemporalContent.lean -- all compiling

## Files Created This Session (6 total)
1. `Cslib/Logics/Bimodal/Metalogic/Algebraic/BooleanStructure.lean` - Phase 2
2. `Cslib/Logics/Bimodal/Metalogic/Algebraic/InteriorOperators.lean` - Phase 2
3. `Cslib/Logics/Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` - Phase 2
4. `Cslib/Logics/Bimodal/Metalogic/Bundle/FMCSDef.lean` - Phase 3
5. `Cslib/Logics/Bimodal/Metalogic/Bundle/FMCS.lean` - Phase 3
6. `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalContent.lean` - Phase 3

## Critical Translation Patterns Discovered

### 1. Scoped Notation Conflicts
The cslib `Formula` has scoped notations that conflict with common variable names:
- `U` is a scoped notation for `Formula.untl` (until) -- use `uf` for ultrafilter variables
- `S` may conflict in subtype syntax `{S : Set ... // ...}` -- use `Omega` instead
- `⊢` (turnstile) notation cannot be used in `have` type annotations (`have d : ⊢ ...` fails)

**Solution**: Use explicit `DerivationTree FrameClass.Base` types instead of `⊢` notation. A local notation `⊢ᴮ` was defined in UltrafilterMCS.lean:
```lean
local notation:50 Γ " ⊢ᴮ " φ => DerivationTree FrameClass.Base Γ φ
```

### 2. Atom Type Inference
`Formula.bot` without explicit `Atom` annotation fails type inference in some contexts. Use `(Formula.bot : Formula Atom)` when needed (especially in `le_top_quot` and `fold_le_of_derives`).

### 3. fc Parameter Inference
`DerivationTree.assumption` and `DerivationTree.modus_ponens` often fail to infer `{fc : FrameClass}` in `by_contra` blocks. Add explicit type annotations:
```lean
have d_φ : (ctx) ⊢ᴮ φ := DerivationTree.assumption ctx φ (by simp)
```

### 4. MCS Type Mapping
| Source | Target |
|--------|--------|
| `SetMaximalConsistent (fc := FrameClass.Base) M` | `SetMaximalConsistent FrameClass.Base M` (from MCSProperties) |
| `BimodalSetMaximalConsistent M` | Not used; use `SetMaximalConsistent FrameClass.Base M` |
| `theorem_in_mcs h_mcs h_deriv` | `SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) h_deriv` |
| `set_lindenbaum` | Check `bimodal_lindenbaum` in MaximalConsistent.lean |
| `Ultrafilter` | `BoolAlgUltrafilter` (avoid Mathlib collision) |

### 5. noncomputable Annotations
- `BooleanAlgebra (LindenbaumAlg Atom)` instance needs `noncomputable`
- `box_interior` needs `noncomputable`
- `or_quot`, `and_quot`, `neg_quot` are already `noncomputable` from LindenbaumQuotient

### 6. Classical.propDecidable
Required for `List.filter (· ≠ φ)` to work with polymorphic `Formula Atom`. Add at namespace top:
```lean
attribute [local instance] Classical.propDecidable
```

### 7. Theorem Path Corrections
| Source | Target |
|--------|--------|
| `Bimodal.Theorems.Combinators.*` | `Theorems.Combinators.*` |
| `Bimodal.Theorems.Propositional.*` | `Theorems.Propositional.*` |
| `Bimodal.Theorems.past_necessitation` | `Theorems.past_necessitation` |
| `Bimodal.Metalogic.Core.deduction_theorem` | `Metalogic.Core.deduction_theorem` |
| `Axiom.prop_s` | `Axiom.imp_s` |
| `Axiom.prop_k` | `Axiom.imp_k` |
| `Axiom.ex_falso` | `Axiom.efq` |

## Immediate Next Action
Complete Phase 3 by porting 3 remaining files:

1. **WitnessSeed.lean** (648 lines) -- forward/backward temporal witness seeds. Imports TemporalContent. Contains:
   - `forward_temporal_witness_seed`, `past_temporal_witness_seed`
   - Consistency proofs for seeds
   - g_content/h_content duality theorems
   - `some_future_all_future_neg_absurd`, `some_past_all_past_neg_absurd`
   - Uses `theorem_in_mcs` (map to `closed_under_derivation`), `set_consistent_not_both`
   - Uses `DerivationTree.lift` for frame class lifting

2. **BFMCS.lean** (229 lines) -- Bundle of FMCS. Imports FMCS. Contains:
   - `BFMCS` structure with modal coherence
   - S5 properties (reflexivity, transitivity)
   - `diamond_witness` theorem
   - Uses `SetMaximalConsistent.negation_complete`, `set_consistent_not_both`
   - **NOTE**: BFMCS uses `FMCS D` which in source has no explicit `Atom` but cslib needs `FMCS Atom D`

3. **CanonicalFrame.lean** (297 lines) -- Canonical frame construction. Imports WitnessSeed, TemporalContent. Contains:
   - `ExistsTask`, `ExistsTask_past` relations
   - `canonical_forward_F`, `canonical_backward_P` (use WitnessSeed)
   - `canonical_forward_G`, `canonical_backward_H` (trivial)
   - `canonical_forward_U`, `canonical_backward_S` (until/since witnesses)
   - Transitivity proofs (use Temporal 4 axiom)
   - Uses `set_lindenbaum` (check cslib version: `bimodal_lindenbaum`)
   - Uses `temp_4_derived`, `temp_4_past`

Source: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Bundle/`
Target: `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/Bundle/`

## Key Issues to Watch

1. **`set_lindenbaum` availability**: The source uses `set_lindenbaum` which extends consistent sets to MCS. In cslib this is `bimodal_lindenbaum` in MaximalConsistent.lean. But it takes `BimodalSetConsistent`, not `SetConsistent FrameClass.Base`. May need a wrapper or `sorry`.

2. **`theorem_in_mcs` type mismatch**: Source uses `theorem_in_mcs h_mcs h_deriv`. The cslib version takes `BimodalSetMaximalConsistent`. For `SetMaximalConsistent fc`, use `closed_under_derivation` directly.

3. **`DerivationTree.lift`**: Source uses `.lift` for frame class lifting. Check if this exists in cslib.

4. **`temp_4_derived`/`temp_4_past`**: These are in MCSProperties.lean in cslib. The source uses them for transitivity proofs.

## Remaining Phases (3-12)
- Phase 3: 3 more Bundle files (WitnessSeed, BFMCS, CanonicalFrame)
- Phase 4: 5 Bundle files (ModalSaturation, SuccRelation, TemporalCoherence, Construction, UntilSinceCoherence)
- Phase 5: 7 BXCanonical files
- Phase 6: 5 Algebraic parametric files
- Phase 7: 2 BXCanonical secondary files
- Phase 8: 2 Chronicle files
- Phase 9: 3 Chronicle core files (3527 + 3487 + 1510 lines)
- Phase 10: 2 Countermodel files
- Phase 11: completeness_dense theorem
- Phase 12: Barrel imports and verification
