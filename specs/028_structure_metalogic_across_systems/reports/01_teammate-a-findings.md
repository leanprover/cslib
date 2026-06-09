# Teammate A Findings: Primary Approach — Metalogic Structure Analysis

**Task**: 28 — Structure metalogic across Propositional, Modal, Temporal, and Bimodal systems
**Date**: 2026-06-09
**Angle**: Primary implementation approach — what goes where and what imports what

---

## Key Findings

### Finding 1: DeductionTheorem + MCS Core Are Tightly Coupled to Concrete DerivationTree (HIGH confidence)

The BimodalLogic `Metalogic/Core/` layer (~1,360 lines) contains three files:
- `DeductionTheorem.lean` (441 lines) — structural induction on `DerivationTree`
- `MaximalConsistent.lean` (528 lines) — `Consistent`, `MaximalConsistent`, `SetMaximalConsistent`, `set_lindenbaum`
- `MCSProperties.lean` (366 lines) — `closed_under_derivation`, `implication_property`, `negation_complete`

**Critical observation**: The DeductionTheorem performs pattern matching on the `DerivationTree` inductive's 7 constructors (axiom, assumption, modus_ponens, necessitation, temporal_necessitation, temporal_duality, weakening). This means:

1. **The deduction theorem cannot be generic** — it requires induction on a concrete inductive type, not a typeclass.
2. **Each logic with a different DerivationTree needs its own deduction theorem**.
3. **MaximalConsistent and MCSProperties depend on DeductionTheorem** — so they also need per-logic versions.

However, the *structure* of the MCS theory is nearly identical across logics. The proofs for `closed_under_derivation`, `implication_property`, `negation_complete`, and `set_lindenbaum` only use:
- `DerivationTree.modus_ponens` (modus ponens rule)
- `DerivationTree.assumption` (assumption rule)
- `DerivationTree.weakening` (weakening rule)
- `DerivationTree.axiom` (axiom instantiation)
- The deduction theorem itself

The modal/temporal-specific rules (necessitation, temporal_necessitation, temporal_duality) are only needed in the DeductionTheorem proof itself (where they are handled by the case that shows these rules cannot fire with non-empty contexts).

### Finding 2: MCS Temporal Properties Are Bimodal-Specific (HIGH confidence)

`MCSProperties.lean` has temporal-specific content at the bottom (lines 230–366):
- `all_future_all_future` — uses `Bimodal.Theorems.TemporalDerived.temp_4_derived` and `DerivationTree.lift`
- `temp_4_past` — uses `DerivationTree.temporal_duality` and `Formula.swap_temporal`
- `all_past_all_past` — same pattern as `all_future_all_future`

These depend on:
- The bimodal `Formula` type (with `.all_future`, `.all_past`, `.swap_temporal`)
- The bimodal `DerivationTree` (with `.temporal_duality`)
- Bimodal-specific derived theorems

**Conclusion**: The generic MCS properties (consistency, deductive closure, implication property, negation completeness, Lindenbaum) can be separated from the temporal MCS properties.

### Finding 3: Soundness Is Inherently Semantics-Dependent (HIGH confidence)

The soundness proof (2,415 lines in SoundnessLemmas/) is entirely about task frame semantics:
- `is_valid` quantifies over `TaskFrame D`, `TaskModel F`, `WorldHistory F`, shift-closed `Omega` sets
- Individual axiom validity proofs reference `truth_at`, `time_shift`, `ShiftClosed`
- Frame class parameterization (`Base`, `Dense`, `Discrete`) is specific to task frame semantics

**Conclusion**: Soundness proofs are fundamentally per-logic because they connect proof systems to specific semantic models. There is no meaningful abstraction to share between:
- Modal soundness (Kripke frames with accessibility relations)
- Temporal soundness (linear orders)
- Bimodal soundness (task frames with world histories)

### Finding 4: The Completeness Architecture Is Also Per-Logic (HIGH confidence)

The completeness proof chain (Completeness.lean + Bundle/ ~5,700 lines) depends on:
- The specific canonical model construction (FMCS, BFMCS for bimodal; would be different for modal/temporal)
- Per-logic MCS properties (modal closure for box, temporal coherence for G/H)
- The Truth Lemma which pattern-matches on formula constructors

Even the "generic" parts (disjunction_intro, conjunction_intro in Completeness.lean) use `DerivationTree` and bimodal `Formula` directly.

### Finding 5: Three Metalogic Components CAN Be Factored Out (MEDIUM confidence)

Despite the tight coupling, three metalogic patterns could potentially be factored:

1. **Generic MCS infrastructure** (as a typeclass/interface): Define `class HasDeductionTheorem` or a generic `MCS` structure parameterized by a formula type and derivability relation. This would capture the pattern without the concrete proof.

2. **Decidability framework**: `SignedFormula`, `Branch`, `Tableau` patterns could be parameterized over formula types (they only need `DecidableEq`). But the tableau rules themselves are formula-specific.

3. **Conservative extension pattern**: The `ExtFormula`/`ExtDerivation`/`Lifting` structure is a general pattern (add fresh atom, embed, lift derivations) but all proofs reference the concrete `Formula` type.

**Assessment**: The effort to abstract these is significant and may not pay off given that only 4 logics use them. Copy-and-adapt is likely more practical than deep abstraction.

---

## Recommended Approach: Per-Logic Metalogic with Shared Patterns

### Proposed Directory Structure

```
Cslib/
├── Foundations/Logic/
│   ├── Connectives.lean          # (existing) HasBot, HasImp, HasBox, HasUntil, HasSince
│   ├── InferenceSystem.lean      # (existing) InferenceSystem, DerivableIn
│   ├── ProofSystem.lean          # (existing) PropositionalHilbert, ModalHilbert, etc.
│   ├── Axioms.lean               # (existing) Axiom abbreviations
│   ├── Theorems/                 # (existing/Task 20) Generic propositional theorems
│   └── Metalogic/                # NEW: Generic metalogic patterns (optional)
│       ├── Consistency.lean      # Abstract consistency/MCS interface
│       └── Lindenbaum.lean       # Parameterized Lindenbaum lemma (if feasible)
│
├── Logics/
│   ├── Propositional/
│   │   ├── Defs.lean             # (existing)
│   │   ├── NaturalDeduction/     # (existing) ND proof system
│   │   └── (no Hilbert metalogic — PL uses natural deduction in CSLib)
│   │
│   ├── Modal/
│   │   ├── Basic.lean            # (existing) Modal.Proposition, Kripke Model
│   │   ├── ProofSystem/          # (Task 21) DerivationTree, instances
│   │   ├── Theorems/             # (Task 21) S4/S5 derived theorems
│   │   ├── Semantics/            # Kripke semantics (already in Basic.lean)
│   │   └── Metalogic/            # NEW: Modal-specific metalogic
│   │       ├── DeductionTheorem.lean  # Modal DeductionTheorem
│   │       ├── MCS.lean              # Modal MCS + Lindenbaum
│   │       ├── Soundness.lean        # Modal soundness (Kripke)
│   │       └── Completeness.lean     # Modal completeness (canonical Kripke model)
│   │
│   ├── Temporal/
│   │   ├── Syntax/               # (existing) Temporal.Formula
│   │   ├── ProofSystem/          # (Task 22) DerivationTree, instances
│   │   ├── Theorems/             # (Task 22) Temporal derived theorems
│   │   ├── Semantics/            # (Task 23) Temporal semantics on LinearOrder
│   │   └── Metalogic/            # NEW: Temporal-specific metalogic
│   │       ├── DeductionTheorem.lean  # Temporal DeductionTheorem
│   │       ├── MCS.lean              # Temporal MCS + Lindenbaum
│   │       ├── Soundness.lean        # Temporal soundness (linear orders)
│   │       └── Completeness.lean     # Temporal completeness (canonical linear model)
│   │
│   └── Bimodal/
│       ├── Syntax/               # (existing) Bimodal.Formula
│       ├── Embedding/            # (existing) Modal/Temporal/PL → Bimodal
│       ├── Semantics/            # (Task 3) TaskFrame, WorldHistory, Truth
│       ├── ProofSystem/          # (Task 4) DerivationTree, 42-axiom Hilbert
│       ├── Theorems/             # (Task 5) Perpetuity theorems
│       └── Metalogic/            # (Tasks 6-11) Bimodal metalogic
│           ├── Core/
│           │   ├── DeductionTheorem.lean
│           │   ├── MaximalConsistent.lean
│           │   └── MCSProperties.lean
│           ├── Soundness.lean
│           ├── SoundnessLemmas/
│           ├── Completeness.lean
│           ├── Bundle/           # FMCS, BFMCS, canonical model
│           ├── BXCanonical/      # Burgess-style completeness
│           ├── Algebraic/        # Algebraic completeness
│           ├── Decidability/     # FMP, Tableau, Decision procedure
│           ├── ConservativeExtension/
│           └── WeakCanonical/    # Separation, expressiveness
```

### Import Hierarchy for Metalogic

```
Foundations/Logic/Theorems/          (generic propositional lemmas)
       ↓                ↓
Modal/ProofSystem/     Temporal/ProofSystem/
Modal/Theorems/        Temporal/Theorems/
Modal/Metalogic/       Temporal/Metalogic/        (per-logic, parallel)
       ↓                       ↓
            Bimodal/Metalogic/                     (imports both)
```

Key import relationships:
- **Modal/Metalogic/** imports Modal/ProofSystem/ and Foundations/Logic/Theorems/ only
- **Temporal/Metalogic/** imports Temporal/ProofSystem/ and Foundations/Logic/Theorems/ only
- **Bimodal/Metalogic/** imports everything above, plus its own Semantics/ and ProofSystem/
- **No cross-import** between Modal/Metalogic/ and Temporal/Metalogic/

---

## Evidence/Examples

### Example 1: DeductionTheorem case analysis (why per-logic is required)

In BimodalLogic's `DeductionTheorem.lean` (line 211+), the proof matches on all 7 constructors:
```lean
private noncomputable def deduction_with_mem {fc : FrameClass} (Γ' : Context) (A φ : Formula)
    (h_deriv : Γ' ⊢[fc] φ) ...
```

A modal `DerivationTree` would only have 5 constructors (axiom, assumption, mp, necessitation, weakening). A temporal one would have 6 (adding temporal_necessitation and temporal_duality but removing modal necessitation). The case analysis is structurally different.

### Example 2: MCS properties that ARE generic vs NOT

**Generic** (same proof structure, different formula/derivation types):
- `closed_under_derivation`: Uses only assumption + weakening + mp
- `implication_property`: Uses only assumption + mp + closed_under_derivation
- `negation_complete`: Uses deduction theorem + closed_under_derivation
- `set_lindenbaum`: Uses Zorn's lemma + consistency definitions

**NOT generic** (uses bimodal-specific features):
- `all_future_all_future`: Uses `temp_4_derived` (bimodal temporal theorem)
- `temp_4_past`: Uses `temporal_duality` constructor + `swap_temporal`
- `box_closure`, `box_box`: Uses modal axioms T and 4

### Example 3: Soundness proof structure

Each axiom validity proof is entirely semantic:
```lean
-- Bimodal version: quantifies over TaskFrame, WorldHistory, shift-closed Omega
def is_valid (D : Type*) [AddCommGroup D] [LinearOrder D] ... (φ : Formula) : Prop :=
  ∀ (F : TaskFrame D) (M : TaskModel F) (Omega : Set (WorldHistory F)) ...
```

A modal soundness would instead quantify over Kripke frames:
```lean
-- Modal version would look like:
def is_valid (φ : Proposition Atom) : Prop :=
  ∀ (W : Type*) (M : Model W Atom) (w : W), satisfies M w φ
```

These are fundamentally different types — no shared infrastructure.

---

## Assessment of Existing Tasks

### Tasks That Correctly Capture Metalogic Distribution

| Task | Status | Assessment |
|------|--------|-----------|
| 20 (Propositional Hilbert Theorems) | PLANNED | **Correct** — pure `[PropositionalHilbert S]` lemmas, no metalogic |
| 21 (Modal proof system + theorems) | NOT STARTED | **Correct scope for proof system + theorems; needs metalogic addition** |
| 22 (Temporal infrastructure + theorems) | NOT STARTED | **Correct scope for infra + theorems; needs metalogic addition** |
| 23 (Temporal semantics) | NOT STARTED | **Correct** — standalone temporal semantics |
| 3 (Task Frame Semantics) | NOT STARTED | **Correct** — inherently bimodal |
| 4 (Bimodal Proof System) | NOT STARTED | **Correct** — inherently bimodal |
| 5 (Perpetuity Theorems) | NOT STARTED | **Correct** — inherently bimodal |
| 6 (Frame Conditions + Soundness) | NOT STARTED | **Correct** — bimodal soundness |
| 7 (Deduction + MCS Theory) | NOT STARTED | **Correct** — bimodal metalogic core |
| 8 (Strong Completeness) | NOT STARTED | **Correct** — bimodal completeness |
| 9 (Decidability + Tableau) | NOT STARTED | **Correct** — bimodal decidability |
| 10 (Separation) | NOT STARTED | **Correct** — bimodal separation |
| 11 (Conservative Extension) | NOT STARTED | **Correct** — bimodal conservative ext. |

### Identified Gaps

**Gap 1: No standalone modal metalogic task**
Tasks 21 covers proof system + theorems but NOT soundness, completeness, or deduction theorem for modal logic. The ROADMAP explicitly says "DeductionTheorem stays per-logic" — but there is no task to create a modal DeductionTheorem, MCS theory, soundness, or completeness for standalone modal logic.

**Recommendation**: Either:
- (A) Add a new task "Modal metalogic: DeductionTheorem, MCS, Soundness, Completeness for Kripke semantics"
- (B) Expand Task 21 to include metalogic — but this would make it very large (~3,000+ lines)
- (C) Accept that modal metalogic is not needed independently (it can be derived from bimodal metalogic via embedding) — but this defeats the "standalone module" principle

**Gap 2: No standalone temporal metalogic task**
Same gap as modal. Task 22+23 cover proof system, theorems, and semantics but not metalogic. There is no task for temporal DeductionTheorem, MCS theory, soundness, or completeness on LinearOrder semantics.

**Recommendation**: Add a new task "Temporal metalogic: DeductionTheorem, MCS, Soundness, Completeness for linear order semantics"

**Gap 3: No explicit decision on shared vs duplicated MCS infrastructure**
The existing tasks don't address whether the MCS infrastructure (Consistent, SetConsistent, SetMaximalConsistent, Lindenbaum) should be:
- Duplicated per-logic (simplest, matches BimodalLogic)
- Abstracted into Foundations/ (cleanest, but requires typeclass/interface design)
- Only implemented for Bimodal and derived for others via embedding (laziest)

**Recommendation**: This decision should be made explicitly. My assessment: duplicate per-logic with shared naming conventions, since the proofs are structurally similar but type-incompatible.

### No Tasks Need Revision

The existing tasks (3-11, 20-23) are correctly scoped for what they cover. The gap is that modal and temporal metalogic is not covered at all. The ROADMAP focuses on "extracting reusable content" from BimodalLogic, but modal/temporal metalogic would be **new development** (no BimodalLogic counterpart for standalone modal/temporal soundness/completeness).

---

## Confidence Levels

| Finding | Confidence |
|---------|-----------|
| DeductionTheorem must be per-logic (concrete inductive) | HIGH |
| MCS core properties have identical structure across logics | HIGH |
| Soundness/completeness are inherently per-semantics | HIGH |
| Temporal MCS properties are bimodal-specific | HIGH |
| New tasks needed for modal/temporal metalogic | MEDIUM |
| Shared MCS infrastructure in Foundations/ is feasible | LOW (possible but uncertain benefit) |
