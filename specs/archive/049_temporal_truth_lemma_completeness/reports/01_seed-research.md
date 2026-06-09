# Seed Research Report: Task 49 — Temporal Truth Lemma and Completeness Assembly

**Task**: 49 — Temporal truth lemma and completeness assembly
**Date**: 2026-06-09
**Source**: Task 50 team research (teammates A, B, C, D)
**Purpose**: Pre-digested research to allow task 49 to skip or accelerate its research phase

---

## Overview

Task 49 proves the truth lemma on the chronicle frame constructed in Tasks 46-48 and uses it to close the sorry in `Temporal/Metalogic/Completeness.lean`. The truth lemma is mathematically concise (Burgess Claim 2.11, ~20 lines of text), but the Lean formalization requires careful countermodel extraction.

**Critical warning**: The bimodal countermodel extraction files (`ChronicleToCountermodelBasic.lean` and `ChronicleToCountermodel.lean`) are heavily box-entangled and NOT directly adaptable. Task 49 must build fresh temporal countermodel extraction. This is the key deviation from the copy-adapt strategy used in Tasks 46-48.

**Good news**: The temporal countermodel is structurally simpler than bimodal. The chronicle frame (X, <) with valuation V already IS the countermodel — no modal accessibility construction needed.

---

## 1. Literature Map: Burgess 1982 Claim 2.11 (Truth Lemma)

### The Truth Lemma Statement

Let (X, <, f, g) be the chronicle produced by the omega construction (Task 48). Define a valuation V on the linear order (X, <) by:
```
V(α) := {x ∈ X | α ∈ f(x)}    for atoms α
```
Then for ALL formulas φ and ALL x ∈ X:
```
(X, <, V) ⊨ φ at x    iff    φ ∈ f(x)
```

### Proof by Induction on Formula Complexity

**Atom case**: By definition of V.

**Negation (¬φ)**: By MCS property — φ ∈ f(x) iff ¬φ ∉ f(x) (negation completeness).

**Conjunction (φ ∧ ψ)**: By MCS closure under conjunction.

**Until (U(β,γ)) — the critical case**:
- Forward direction (U(β,γ) ∈ f(x) → x ⊨ U(β,γ)):
  By C5a (chronicle condition), ∃y > x with γ ∈ f(y) and β ∈ g(x,y).
  For any z with x < z < y: by C3, g(x,y) ⊆ f(z), so β ∈ f(z).
  By IH: y ⊨ γ and z ⊨ β for all such z. This gives x ⊨ U(β,γ).
  
- Backward direction (¬U(β,γ) ∈ f(x) → x ⊭ U(β,γ)):
  For any y > x with y ⊨ γ (equivalently γ ∈ f(y) by IH):
  By C4a, ∃z with x < z < y and ¬β ∈ f(z).
  By IH: z ⊭ β. So there's always a counterpoint. This gives x ⊭ U(β,γ).

**Since (S(β,γ)) case**: Mirror image of Until.

**G(φ) case**: Follows from MCS property and G axioms (or directly from C4/C5 chain).

**H(φ) case**: Mirror image of G.

### Completeness Conclusion

Since the formula φ₀ being satisfied lives in f(0) = A₀ (the MCS containing ¬φ₀ that we started with), the truth lemma gives 0 ⊨ ¬φ₀... wait — we start with a formula that is NOT derivable, so ¬φ is consistent, and A₀ is an MCS containing ¬φ. Then the truth lemma gives 0 ⊨ ¬φ, meaning φ is NOT true at 0 in the chronicle model. This is the countermodel.

**Lean target for the completeness theorem**:
```
theorem completeness : (∀ M : TemporalModel, M ⊨ φ) → ⊢ φ
```
Proof: Contrapositive. If ⊬ φ, then {¬φ} is consistent, so by Lindenbaum there's an MCS A₀ containing ¬φ. Apply the chronicle construction to get a model M = (X, <, V). By the truth lemma, 0 ⊨ ¬φ, so M ⊭ φ. Done.

### BdRV Theorem 7.15

BdRV states completeness of system **B** (= Burgess J₀) for all linear flows of time as Theorem 7.15. This is exactly the target. BdRV then uses 7.15 as a building block for well-ordering completeness (Theorem 7.19) — out of scope for Task 49.

---

## 2. Infrastructure Audit: Per-File Transfer Analysis

### BXCanonical/TruthLemma.lean (223 lines) → ~70% transfer rate

**What transfers directly**:
- `bot_not_in_mcs` (⊥ ∉ MCS)
- `imp_iff_mcs` (φ→ψ ∈ A iff φ ∉ A or ψ ∈ A)
- `G_iff_mcs` (Gφ ∈ A iff φ ∈ g_content A)
- `H_iff_mcs` (Hφ ∈ A iff φ ∈ h_content A)
- `until_forward_mcs` (U(β,γ) ∈ A → IH conclusion for U)
- `since_forward_mcs` (S(β,γ) ∈ A → IH conclusion for S)
- `bx_lt` (the temporal ordering derived from g_content)
- `F_from_witness`, `P_from_witness`

**What does NOT transfer**:
- `box_iff_mcs` (~30 lines): BIMODAL-ONLY — box case of truth lemma. **Remove entirely.**
- References to `bx_modal_witness` (bimodal modal witness)

**Net**: Remove ~30 lines, keep ~160 lines = ~70% transfer.

### BXCanonical/CanonicalModel.lean (771 lines) → ~40% transfer rate

**What transfers**:
- Z-chain MCS propagation patterns (forward_G, backward_H)
- The pattern of building a canonical linear order from MCSs
- The completeness skeleton (contrapositive, Lindenbaum, canonical model, countermodel)

**What does NOT transfer**:
- `FMCS`, `BFMCS` structures (bundle of families of MCS indexed by Int) — BIMODAL-SPECIFIC
- `bx_modal_witness_fc` — NOT NEEDED
- Modal saturation, box-equivalence classes — NOT NEEDED
- The `completeness_dense` / `completeness_discrete` case split on box indicators — NOT NEEDED for base temporal completeness

**Key observation**: The existing `Temporal/Metalogic/Completeness.lean` already has substantial canonical model infrastructure (see Section 5). Task 49 can reuse this rather than porting CanonicalModel.lean.

### Chronicle/ChronicleToCountermodelBasic.lean (1170 lines) → ~0% DIRECT TRANSFER

**WARNING**: This file is heavily box-entangled.

**Box references**: ~30 occurrences of `Formula.box`, `modal_k_dist`, `modal_t`, S5 box-stability reasoning.

**Specific bimodal constructions**:
- Dense/discrete case split driven by `Formula.box next_top`
- `ParametricCompleteness`, `ParametricTruthLemma` — algebraic completeness machinery from Bimodal/Algebraic/
- Cantor isomorphism (dense case) using algebraic completeness
- Discrete case depends entirely on WeakCanonical (Task 36) — completely sorry'd

**What MIGHT be salvageable**:
- `LimitDomSubtype` utilities (type-level subtypes of the limit domain)
- Countability instance construction
- `NoMinOrder`/`NoMaxOrder` instances for the limit

**Verdict**: Do NOT attempt to adapt this file. Extract only the structural utilities if needed.

### Chronicle/ChronicleToCountermodel.lean (229 lines) → ~0% DIRECT TRANSFER

**WARNING**: Everything after `mcs_mixed_case_absurd` (first ~50 lines) is bimodal-specific.

- `mcs_mixed_case_absurd` is fully proved but about box(next_top) — BIMODAL-SPECIFIC
- All discrete pipeline stubs are sorry'd
- The BFMCS construction is bimodal-specific

**Verdict**: Do NOT adapt this file. Build fresh for temporal.

---

## 3. Recommended Fresh Approach for Temporal Countermodel Extraction

### Why Fresh Is Better

The temporal countermodel is **structurally simpler** than bimodal:
- **Bimodal**: Chronicle frame (X, <, f, g) → extract worlds with both temporal order AND modal accessibility (via box-equivalence classes) → TemporalModel + ModalModel combined
- **Temporal**: Chronicle frame (X, <, f, g) → the frame (X, <) IS the temporal model; no modal accessibility needed

The bimodal `ChronicleToCountermodel*.lean` is complex precisely because it must construct a model satisfying BOTH temporal and modal requirements simultaneously.

### Fresh Approach Outline

1. **Define `TemporalChronicleFrame`**: Structure with `worlds : Type`, `lt : worlds → worlds → Prop` (linear order), and proof that it is a serial linear order.

2. **Define `TemporalChronicleModel`**: 
   ```lean
   structure TemporalChronicleModel where
     frame : TemporalChronicleFrame
     val : Atom → Set frame.worlds
   ```

3. **Extract from chronicle**: Given the limit chronicle (X, <, f, g) from Task 48, construct a `TemporalChronicleModel` with `val α := {x : X | α ∈ f(x)}`.

4. **Prove truth lemma** (TruthLemma.lean): By induction on formula complexity using chronicle conditions C4a, C5a, C3, MCS properties.

5. **Prove seriality**: The limit chronicle has `NoMaxOrder` and `NoMinOrder` (from ChronicleConstruction.lean, Task 48).

6. **Prove it's a valid TemporalModel**: The `TemporalChronicleFrame` satisfies all required frame conditions for the base temporal proof system (serial linear order).

7. **Close the sorry**: In `Completeness.lean` line 416, fill in the sorry with the chronicle construction + truth lemma.

### The Dense/Discrete Split Question

Teammate C raises a concern about the dense/discrete case split in Task 49:

**Base completeness**: `Completeness.lean` quantifies over `∀ (D : Type) [LinearOrder D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]`. The chronicle construction on ℚ produces a dense countable linear order. Task 49's completeness theorem only needs to produce ONE countermodel — the chronicle model on ℚ is sufficient.

**No case split needed for Task 49**: Unlike bimodal (which needs to handle both dense and discrete), the base temporal completeness just needs "not derivable → there exists a countermodel". The chronicle on ℚ IS that countermodel.

**Tasks 38-40** (dense/discrete/continuous completeness) will need separate machinery. But Task 49 only closes the base sorry.

---

## 4. Interaction with Existing Completeness.lean Infrastructure

### What Exists (lines 60-340)

From Teammate B and C's analysis of `Temporal/Metalogic/Completeness.lean`:

```
Line 60-340:
- CanonicalWorld (type of MCS worlds)
- canonical_acc (canonical accessibility: w1 < w2 iff g_content w1 ⊆ w2.formulas)
- G/H truth lemma for the Z-chain canonical model
- mcs_g_trans, mcs_h_trans
- past_of_future_subset, future_of_past_subset
- exists_future_successor, exists_past_predecessor
- The completeness theorem (line ~400) with a sorry at line 416
```

### Reconciliation Strategy

The existing `CanonicalWorld` and `canonical_acc` infrastructure is a Z-chain canonical model (for base completeness without Until/Since truth). Task 49 brings the Chronicle which provides Until/Since truth but is a ℚ-chain, not a Z-chain.

**Options**:
1. **Use the chronicle as the countermodel directly** (recommended): The chronicle provides a richer model (on ℚ, with full truth lemma including Until/Since). This fills the sorry that was previously pointing at a Z-chain solution. The Z-chain infrastructure in Completeness.lean can remain as-is for historical context or be removed later.

2. **Extend the Z-chain with chronicle truth lemma**: More complex, requires threading chronicle conditions through the Z-chain structure.

**Recommendation**: Option 1. The sorry at line 416 says "build a countermodel for ¬φ". The chronicle gives us exactly that. Insert a `sorry`-replacement that:
- Runs the oracle completeness argument: ⊬ φ → ∃ chronicle M, 0 ∉ M ⊨ φ
- The existing Lindenbaum + neg_consistent_of_not_derivable is already there

---

## 5. Implementation Strategy

### Recommended Phase Sequence for Task 49

1. **Phase 1**: Create `Chronicle/TruthLemma.lean` (~100-150 lines)
   - Port from BXCanonical/TruthLemma.lean, removing box_iff_mcs
   - Prove truth lemma for atom, bot, imp, G, H, Until, Since by induction

2. **Phase 2**: Create `Chronicle/ChronicleToCountermodel.lean` (FRESH, ~200-400 lines)
   - Define `TemporalChronicleModel` type
   - Prove NoMaxOrder/NoMinOrder for limit domain
   - Prove the limit domain is a serial linear order (Nontrivial, etc.)
   - Construct the valuation

3. **Phase 3**: Update `Completeness.lean` (~50-100 lines)
   - Import the chronicle construction (Tasks 46-48) and countermodel extraction (Phase 2)
   - Replace sorry at line 416 with:
     ```
     -- Use chronicle construction to get a countermodel
     -- Apply truth lemma to contradict derivability
     ```
   - Verify no new sorry stubs introduced

### Incremental Verification

After Phase 1: Check that TruthLemma.lean compiles cleanly with Tasks 46-48.
After Phase 2: Verify the `TemporalChronicleModel` satisfies all temporal frame requirements.
After Phase 3: Run `lake build` and confirm zero sorrys in Completeness.lean.

---

## 6. Risks and Warnings

### Risk 1 (HIGH): Box-Entanglement in Countermodel Files

This is the most critical risk. Attempting to adapt `ChronicleToCountermodelBasic.lean` or `ChronicleToCountermodel.lean` will waste significant time. Both files use approximately 30-50 box-formula references and depend on algebraic completeness machinery. The fresh approach described in Section 3 is shorter AND cleaner.

### Risk 2: CanonicalWorld/TPoint Overlap

Both the existing `CanonicalWorld` (in Completeness.lean) and the new `TPoint` (from Task 46) represent "a temporal MCS as a world". These are conceptually the same but may have different types. Task 49 must decide:
- Use `TPoint` throughout (may require refactoring existing Completeness.lean infrastructure)
- Keep `CanonicalWorld` for the Z-chain infrastructure, use `TPoint` for the chronicle

The simplest approach: leave `CanonicalWorld` and `canonical_acc` in place, don't refactor them, just add the chronicle-based completeness proof alongside.

### Risk 3: Definitional Equality of G/H Truth Conditions

The existing Completeness.lean's G/H truth lemma uses `futureSet`/`pastSet` notation. TruthLemma.lean (adapted from bimodal) uses `g_content`/`h_content`. These are definitionally equal (both mean `{φ | G φ ∈ M}`) but may cause type mismatch if not unified. Verify before writing Phase 3.

### Risk 4: Until/Since Truth Lemma Complexity

The "critical case" in the truth lemma (U(β,γ)) requires C4a and C5a to be available for the specific element positions in the limit chronicle. Verify the limit chronicle has C4a/C5a established in Task 48 (as `limit_satisfies_c4a` and `limit_satisfies_c5a`) before writing Phase 1.

### Risk 5: Dense/Discrete Interaction (Downstream, Not Task 49)

The chronicle construction produces a dense linear order on ℚ. Task 49 uses this for base completeness — this is fine. HOWEVER, Task 39 (discrete completeness) uses a DIFFERENT approach (Int model, not chronicle). Task 40 (continuous) may rely on Task 49's infrastructure. These interactions do NOT block Task 49 but should be noted for planning tasks 38-40.

---

## 7. Scope Estimate Revision

**Original estimate**: 500-1,200 lines
**Revised estimate**: 800-1,800 lines

**Reasoning for revision**:
- TruthLemma.lean: 100-150 lines (bimodal is 223, remove box case = ~160, add some cleanup)
- ChronicleToCountermodel.lean (FRESH): 200-400 lines (simpler than bimodal's 1399 because no modal accessibility)
- Completeness.lean updates: 50-100 lines
- Supporting glue: 100-300 lines (TemporalChronicleFrame type, seriality proofs, etc.)
- Total: 450-950 lines minimum + overhead = **800-1,800 range**

The lower bound (500) assumed the bimodal countermodel files could be adapted with ~50% transfer. Since they cannot, the lower bound rises. But the upper bound is also lower (1,200 → 1,800) because the temporal approach is simpler in structure (no FMCS/BFMCS/S5).

---

## 8. Naming Conventions

| Bimodal Name | Temporal Name | Notes |
|---|---|---|
| `TruthLemma.lean` | `TruthLemma.lean` | Keep identical filename |
| `truth_lemma` | `truth_lemma` | Keep identical definition name |
| `CanonicalModel` (bimodal CanonicalModel.lean) | NOT PORTED | Build fresh countermodel instead |
| `ChronicleToCountermodel` | `ChronicleToCountermodel` | Keep identical filename, FRESH content |
| `TemporalModel` (from existing semantics) | `TemporalModel` | Reuse existing type |
| `BXPoint` (bimodal) | `TPoint` (temporal) | Different as in Task 46 |

---

## 9. Relevant Codebase Paths

### Source Files (bimodal — partial reference only)
```
Cslib/Logics/Bimodal/Metalogic/BXCanonical/
├── TruthLemma.lean                    (223 lines — ~70% transfer rate)
├── CanonicalModel.lean                (771 lines — ~40% transfer rate, reference only)
└── Chronicle/
    ├── ChronicleToCountermodelBasic.lean  (1170 lines — DO NOT ADAPT)
    └── ChronicleToCountermodel.lean       (229 lines — DO NOT ADAPT)
```

### Prerequisite Files (must exist before Task 49)
```
Cslib/Logics/Temporal/Metalogic/Chronicle/
├── RRelation.lean                    (from Task 46)
├── Frame.lean                        (from Task 46)
├── CanonicalChain.lean               (from Task 46)
├── OrderedSeedConsistency.lean       (from Task 46)
├── ChronicleTypes.lean               (from Task 47)
├── PointInsertion.lean               (from Task 47)
├── CounterexampleElimination.lean    (from Task 48)
└── ChronicleConstruction.lean        (from Task 48)
```

### Target Files (temporal — create/update these)
```
Cslib/Logics/Temporal/Metalogic/Chronicle/
├── TruthLemma.lean                   (new — Phase 1, ~100-150 lines)
└── ChronicleToCountermodel.lean      (new FRESH — Phase 2, ~200-400 lines)

Cslib/Logics/Temporal/Metalogic/
└── Completeness.lean                 (update — Phase 3, fill sorry at line 416)
```

---

## References

- Burgess 1982, Section 2, Claim 2.11 (truth lemma) and completeness conclusion
- Blackburn/de Rijke/Venema 2002, Theorem 7.15 (completeness of B for linear flows)
- `specs/050_burgess_prior_art_seed_research/reports/01_team-research.md`
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-a-findings.md` (truth lemma analysis, bimodal differences)
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-b-findings.md` (per-file transfer rates, box-entanglement details)
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-c-findings.md` (scope revision, dense/discrete risks, CanonicalWorld overlap)
- `specs/050_burgess_prior_art_seed_research/reports/01_teammate-d-findings.md` (copy-adapt strategy, name alignment)
