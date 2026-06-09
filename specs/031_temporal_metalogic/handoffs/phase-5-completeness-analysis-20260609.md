# Phase 5 Completeness Analysis Handoff

## Current State

File: `Cslib/Logics/Temporal/Metalogic/Completeness.lean` -- 423 lines, 1 sorry (the main `completeness` theorem). Full lake build passes. The file was cleaned up and a new helper theorem `mcs_g_and_g_neg_absurd` was added. The `Mathlib.Order.Extension.Linear` import was added (provides `LinearExtension` / Szpilrajn extension theorem).

## What Was Done in This Session

1. **Extensive analysis of proof strategies** for the completeness theorem
2. **Identified fundamental difficulties** with canonical model and Z-chain approaches
3. **Added `mcs_g_and_g_neg_absurd`**: G(psi) and G(neg psi) cannot both be in an MCS
4. **Added `Mathlib.Order.Extension.Linear` import**: provides `LinearExtension`, `extend_partialOrder` (Szpilrajn's theorem)
5. **Cleaned up the file**: removed all messy intermediate code, restored to a clean state
6. **Verified full lake build passes**

## Key Findings from Analysis

### Universe Issue
- `h_valid` quantifies over `D : Type` (universe 0)
- `CanonicalWorld Atom` is in `Type u_1` (same universe as Atom)
- If `Atom : Type 0`, no issue. Otherwise, need `D = Int` or change to `D : Type*`
- Current theorem keeps `D : Type` to maintain backward compatibility

### Canonical Model Approach (CanonicalWorld + LinearExtension)
- `canonical_acc W1 W2 = forall psi, G(psi) in W1 -> psi in W2`
- `canonical_acc` is **transitive** (from `mcs_g_trans`)
- `canonical_acc` is **NOT reflexive** (G is strict future, no T axiom; proven by showing `{G(alpha), neg alpha}` is consistent)
- `canonical_acc` is **NOT total** (totality would imply reflexivity, contradiction)
- `LinearExtension` of a discrete partial order gives a linear order, but the truth lemma fails because the extension adds orderings beyond `canonical_acc`
- The G-forward truth lemma requires: `W < T` in linear order implies `canonical_acc W T`. The extension only gives the reverse direction.

### Z-Chain Approach (Int-indexed chain)
- Build chain(0) = M, iterate future/past successors
- G-forward truth lemma: straightforward from chain properties + `mcs_g_trans`
- G-reverse truth lemma: requires the chain to witness defects -- if G(alpha) not in chain(n), need alpha not in chain(m) for some m > n. This requires the chain to be built with defect-witnessing.
- **Until forward truth lemma**: the hardest case. Requires:
  - F(event) has lower formula complexity than (event U guard), allowing IH
  - But extracting the witness from F(event) membership requires G-reverse
  - Guard argument at intermediate points requires BX axiom reasoning
- **Until reverse truth lemma**: requires connecting semantic Until on Z back to MCS membership. The m = n+1 case (vacuous guard) doesn't match BX axioms (which are for arbitrary linear orders, not discrete Z).

### Totality of canonical_acc
- BX11 (temp_linearity) encodes linearity semantically but does NOT force totality of `canonical_acc` on MCS
- Attempted proof: if not canonical_acc W1 W2 and not canonical_acc W2 W1, derive contradiction. The argument constructs a common future successor T but cannot derive a contradiction from BX11 within T.
- Conclusion: **totality of canonical_acc is NOT provable from BX axioms alone** (or at least the standard proof technique does not apply directly)

## Recommended Next Steps

### Option A: Z-Chain with Full Henkin Construction (~500 lines)
1. Define chain construction with defect-witnessing rotation
2. Prove chain properties (MCS, futureSet transfer, pastSet transfer)
3. Prove G-forward and G-reverse truth lemma on chain
4. Prove Until/Since truth lemma by well-founded induction on formula complexity
5. Close completeness theorem

**Challenges**: Until-reverse truth lemma on discrete Z. BX axioms are designed for arbitrary linear orders, and the discrete semantics of Z creates a mismatch. The standard proof uses BX13 (enrichment) and BX5 (self-accumulation) but the argument is extremely technical.

### Option B: Change D : Type to D : Type* (~300 lines, cleaner)
1. Change the theorem statement to `D : Type*`
2. Use CanonicalWorld directly as D
3. Build a LinearOrder on CanonicalWorld using a well-order (not canonical_acc)
4. Prove the truth lemma using canonical_acc properties (not the linear order)
5. Handle the frame conditions (Nontrivial, NoMaxOrder, NoMinOrder)

**Challenge**: The truth lemma for G/H depends on the order matching canonical_acc. An arbitrary well-order breaks this correspondence. Would need to show that the truth lemma holds regardless of the linear order, which is not straightforward.

### Option C: Filtration + Extension (~400 lines)
1. Quotient CanonicalWorld by subformula-equivalence (agree on all subformulas of phi)
2. Get a finite quotient with well-defined truth values
3. Extend the finite model with infinite ascending/descending chains for seriality
4. Prove the truth lemma on the extended model

**Challenge**: The extension with infinite chains must preserve the truth lemma. The seriality extension is non-trivial.

## Files Modified
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` (~423 lines, 1 sorry)

## Key Definitions and Theorems Available
- `mcs_g_trans`, `mcs_h_trans`: G/H-transitivity
- `mcs_ff_imp_f`, `mcs_pp_imp_p`: F/P-idempotency
- `past_of_future_subset`, `future_of_past_subset`: connectivity (BX4/BX4')
- `truth_lemma_g_forward`, `truth_lemma_g_reverse`: G-case on canonical model
- `truth_lemma_h_reverse`: H-case on canonical model
- `exists_future_successor`, `exists_past_predecessor`: seriality
- `mcs_g_witness`, `mcs_h_witness` (from MCS.lean): key witness lemmas
- `mcs_g_and_g_neg_absurd`: G(psi) and G(neg psi) cannot coexist
- `neg_consistent_of_not_derivable`: {neg phi} consistent if phi not derivable
- `derive_dne`, `derive_h_nec`, `derive_and_top_intro`: derivation helpers
- `mcs_dne`: double negation elimination in MCS
- `LinearExtension` (from Mathlib): Szpilrajn extension theorem
