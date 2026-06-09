# Phase 5 Continuation Handoff

## Current State

Phase 5 (Completeness) has been significantly advanced with substantial new infrastructure, but the main `completeness` theorem still has 1 sorry.

## What Was Done in This Session

1. **Proved `mcs_g_trans`**: G(ψ) -> G(G(ψ)) in any MCS (G-transitivity/4-axiom)
   - Uses F-idempotency (BX6 absorb_until + BX3 right_mono_until)
   - Chain: G(ψ) ∉ Ω -> ¬G(G(ψ)) ∈ Ω -> F(¬G(ψ)) ∈ Ω -> F(F(¬ψ)) ∈ Ω -> F(¬ψ) ∈ Ω -> contradiction

2. **Proved `mcs_h_trans`**: H(ψ) -> H(H(ψ)) in any MCS (H-transitivity/4-axiom)
   - Symmetric to mcs_g_trans using BX6' absorb_since + BX3' right_mono_since

3. **Proved `mcs_ff_imp_f`**: F(F(ψ)) -> F(ψ) in any MCS (F-idempotency)
   - Key step: derive_and_top_intro gives ⊢ X → ⊤∧X
   - BX3: G(X→⊤∧X) → F(X) → F(⊤∧X)
   - BX6 absorb_until: F(⊤∧F(ψ)) → F(ψ)

4. **Proved `mcs_pp_imp_p`**: P(P(ψ)) -> P(ψ) (P-idempotency)

5. **Proved `past_of_future_subset`**: futureSet(Ω₁) ⊆ Ω₂ → pastSet(Ω₂) ⊆ Ω₁
   - Uses BX4 (connect_future): φ → G(P(φ))

6. **Proved `future_of_past_subset`**: pastSet(Ω₁) ⊆ Ω₂ → futureSet(Ω₂) ⊆ Ω₁
   - Uses BX4' (connect_past): φ → H(F(φ))

7. **Proved truth lemma components**:
   - `truth_lemma_g_forward`: G(ψ) ∈ W → ∀T accessible, ψ ∈ T
   - `truth_lemma_g_reverse`: (∀T accessible, ψ ∈ T) → G(ψ) ∈ W (uses mcs_g_witness)
   - `truth_lemma_h_reverse`: (∀T past-accessible, ψ ∈ T) → H(ψ) ∈ W (uses mcs_h_witness)

8. **Proved existence lemmas**:
   - `exists_future_successor`: every MCS has a future successor MCS
   - `exists_past_predecessor`: every MCS has a past predecessor MCS

9. **Helper derivations**:
   - `derive_dne`: ⊢ ¬¬X → X (double negation elimination)
   - `derive_h_nec`: ⊢ φ implies ⊢ H(φ) (H-necessitation via duality)
   - `derive_and_top_intro`: ⊢ φ → ⊤ ∧ φ
   - `mcs_dne`: ¬¬X ∈ Ω ↔ X ∈ Ω in MCS

## What Remains (1 sorry)

The `completeness` theorem requires:

### 1. LinearOrder instance on CanonicalWorld Atom
- Need to define a total order on all MCS
- **Totality** from BX11 (temp_linearity): F(φ) ∧ F(ψ) → F(φ∧ψ) ∨ F(φ∧F(ψ)) ∨ F(F(φ)∧ψ)
- **Issue**: canonical_acc (futureSet inclusion) is a preorder, not antisymmetric
- Two MCS can have mutually included future-sets without being equal
- Need either: (a) quotient by the equivalence, or (b) use a different order definition
- The bimodal completeness construction may provide a pattern for this

### 2. Truth lemma for Until/Since
- Until forward: (ψ U φ) ∈ W → ∃T > W, φ ∈ T ∧ ∀R between, ψ ∈ R
- Until reverse: ∃T > W, φ ∈ T ∧ ∀R between, ψ ∈ R → (ψ U φ) ∈ W
- These use BX5 (self_accum_until), BX6 (absorb_until), BX13 (enrichment_until)
- The "between" condition requires the order to be linear/total

### 3. Nontrivial + NoMaxOrder + NoMinOrder instances
- Nontrivial: from exists_future_successor (two distinct MCS exist)
- NoMaxOrder: from exists_future_successor (every MCS has a strict successor)
- NoMinOrder: from exists_past_predecessor
- These follow from the order definition + existence lemmas

### 4. Universe issue
- h_valid quantifies over D : Type (universe 0)
- CanonicalWorld Atom : Type u (matching Atom universe)
- Options: change h_valid to Type*, or use ULift

## Recommended Next Steps

1. Study the bimodal completeness construction at `Cslib/Logics/Bimodal/Metalogic/Completeness/`
2. Determine if the bimodal canonical order pattern can be adapted for temporal
3. Focus on the Until/Since truth lemma as the critical path
4. Consider whether a ℤ-chain approach (with Henkin witnesses) is simpler than the full canonical model

## Files Modified
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` (~420 lines, 1 sorry)
