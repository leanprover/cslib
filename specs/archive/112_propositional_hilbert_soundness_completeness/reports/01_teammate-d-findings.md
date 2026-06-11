# Research Report: Task 112 — Teammate D (Horizons)

**Task**: 112 — Establish soundness and completeness for the propositional Hilbert proof systems
**Role**: Teammate D — Strategic horizons and architectural alignment
**Focus**: How propositional metalogic fits into the broader landscape (modal, temporal, bimodal)

---

## Key Findings

### 1. The Metalogic Landscape is Deeply Uniform

The codebase has a remarkably consistent three-layer metalogic architecture across all logics:

**Layer A: Generic foundation** (`Cslib/Foundations/Logic/Metalogic/`)
- `Consistency.lean`: `DerivationSystem` struct, `SetConsistent`, `SetMaximalConsistent`, Lindenbaum's lemma (via Zorn), `HasDeductionTheorem`, `closed_under_derivation`, `implication_property`, `negation_complete`

**Layer B: Logic-specific MCS instantiation** (e.g., `Modal/Metalogic/MCS.lean`, `Propositional/Metalogic/MCS.lean`)
- Instantiates generic framework for the concrete `propDerivationSystem` / `modalDerivationSystem`
- Proves domain-specific MCS properties (modal adds box-closure lemmas; propositional stays simpler)

**Layer C: Soundness and Completeness** (e.g., `Modal/Metalogic/Soundness.lean`, `Completeness.lean`)
- Parameterized `soundness` theorem (induction on `DerivationTree`)
- `CanonicalModel` construction, `truth_lemma`, top-level `completeness`
- System-specific wrappers: `k_soundness`, `t_soundness`, `s5_soundness`, etc.

**What exists for propositional**: Only Layers A (foundation) and B (MCS) are complete. Layer C (soundness and completeness) is entirely missing.

### 2. Propositional Semantics Infrastructure is Absent

There is no `Cslib/Logics/Propositional/Semantics/` directory at all. Modal logic has `Modal/Basic.lean` which defines:
- `Model World Atom` (with relation `r` and valuation `v`)
- `Satisfies m w φ` (recursive on formula structure)
- `Proposition.valid` (universal satisfaction)

The propositional analogue would be:
- A `Valuation Atom` type (function `Atom → Prop` or `Atom → Bool`)
- `Evaluate v φ : Prop` (truth-value semantics, recursive on formula structure — no worlds/relations)
- `Valid φ : Prop` (true under all valuations)
- `Tautology` / `Satisfiable` predicates

This is **simpler** than modal semantics: no worlds, no accessibility relation. The `box` case in `Modal.Satisfies` (universal quantification over accessible worlds) disappears entirely.

### 3. Propositional Completeness is a Special Case of Modal Completeness

This is the most strategically important architectural insight:

- **Modal**: A single-world frame with a trivial (empty or reflexive) accessibility relation collapses `□φ` to `φ` itself. A propositional valuation IS a modal valuation restricted to a single world.
- **Formally**: `PL.Proposition.toModal` already exists in `Cslib/Logics/Modal/FromPropositional.lean` — the embedding is defined and coercion is registered.
- **Implication**: Propositional truth-table semantics can be seen as Kripke semantics over the trivial 1-world frame `{w}` with `r w w` (or with empty relation). A propositional tautology is a modal formula valid on all trivial frames.

However, for readability and the user's stated goal ("congenial to the modal metalogic"), it is better to give propositional semantics its **own direct treatment** with valuations, and prove soundness/completeness at that level. The connection to modal semantics should be stated as a theorem (embedding respects semantics) rather than deriving propositional completeness via modal machinery.

### 4. The Canonical Model Construction is Simpler for Propositional Logic

In the modal completeness proof, the `CanonicalModel` requires:
- `CanonicalWorld Axioms` = MCS type
- Accessibility relation: `R S T ↔ ∀ ψ, □ψ ∈ S → ψ ∈ T`
- Valuation: `v S p ↔ atom p ∈ S`
- Truth Lemma handles the `box` case (the hard case, requiring `mcs_box_witness`)

For propositional completeness, there is no `box` case. The canonical valuation is simply:
- `v p ↔ atom p ∈ M` (where `M` is an MCS)

The Truth Lemma becomes trivial for `atom`, `bot`, and `imp` cases (identical to modal without the `box` case). There is **no** need for an existence lemma or `mcs_box_witness`. The canonical model is not a Kripke model at all — it is a single world whose truth value function is exactly the MCS membership predicate.

### 5. The Modal Pattern for System-Specific Soundness is the Right Template

The modal pattern for system-specific files is:

```
Soundness.lean          -- parameterized soundness theorem
KSoundness.lean         -- k_axiom_sound + k_soundness (instantiation for K)
TSoundness.lean         -- t_axiom_sound + t_soundness (instantiation for T)
... etc.
```

For propositional logic, the situation is simpler: there is only one system (classical propositional logic `HilbertCl`), but there are also three levels of the propositional hierarchy (`HilbertMin`, `HilbertInt`, `HilbertCl`). The pattern should be:

```
Propositional/Metalogic/Soundness.lean       -- parameterized soundness
Propositional/Metalogic/Completeness.lean    -- completeness for CPL
```

Optionally later:
```
Propositional/Metalogic/IPLCompleteness.lean -- completeness for intuitionistic (Kripke semantics)
```

### 6. The `PropositionalAxiom` Type Already Mirrors the Modal Pattern

Looking at `Modal.Metalogic.Soundness.lean`, the parameterized `soundness` theorem takes:
```
h_ax_sound : ∀ ψ, Axioms ψ → ∀ w, Satisfies m w ψ
```
For propositional logic, the analog is:
```
h_ax_sound : ∀ ψ, PropositionalAxiom ψ → ∀ v, Evaluate v ψ = True
```

The four axiom cases (`implyK`, `implyS`, `efq`, `peirce`) are identical to the first four cases handled in `Modal.Metalogic.Soundness.axiom_sound` — they share the same propositional axiom base. This means propositional soundness is a **strict simplification** of the modal soundness proof (just remove the modal axiom cases and worlds).

### 7. Temporal Logic Establishes Soundness Without System-Specific Files

The temporal metalogic proves a single `soundness` theorem in `Temporal/Metalogic/Soundness.lean` — there is no `BXSoundness.lean` (because BX is the only temporal system). For propositional logic, similarly, we need only one soundness file since `CPL` is the canonical classical system.

### 8. What the Temporal `PropositionalHelpers.lean` Tells Us

`Temporal/Metalogic/PropositionalHelpers.lean` reveals the infrastructure for lifting generic propositional theorems from `Foundations/Logic/Theorems/Propositional/` into specific logics. This file provides a bridge pattern (`wrap`/`unwrap`) that propositional metalogic can also use — though propositional metalogic IS the propositional layer, so no bridging is needed: we prove directly.

### 9. File Structure Recommendation

To align with modal and temporal patterns, the following file structure is recommended:

```
Cslib/Logics/Propositional/
├── Semantics/
│   ├── Valuation.lean      -- Valuation type, Evaluate function, Valid predicate
│   └── Validity.lean       -- Tautology, satisfiability, model-theoretic validity (optional)
├── Metalogic/
│   ├── DeductionTheorem.lean   [EXISTS]
│   ├── MCS.lean                [EXISTS]
│   ├── Soundness.lean          [NEW] -- parameterized soundness + PropositionalAxiom soundness
│   └── Completeness.lean       [NEW] -- canonical valuation from MCS, truth lemma, completeness
```

This exactly mirrors the modal pattern:
```
Modal/
├── Basic.lean                  -- semantics (analogous to Propositional/Semantics/Valuation.lean)
├── Metalogic/
│   ├── DeductionTheorem.lean
│   ├── MCS.lean
│   ├── Soundness.lean
│   └── Completeness.lean
```

### 10. Embedding Coherence Theorem

Once both propositional and modal soundness/completeness are in place, there is a natural **coherence theorem** to prove (future work):

> If `PropositionalAxiom φ`, then `ModalAxiom φ.toModal`.

And conversely:

> If `φ : PL.Proposition Atom` and `⊢_PL φ`, then `⊢_Modal φ.toModal` (conservativity).

This is not needed for task 112 but is the natural next step in the PR/Mathlib submission pipeline.

---

## Strategic Recommendations

### Recommendation 1: Implement propositional semantics as its own `Valuation`-based layer

Do NOT derive propositional completeness as a corollary of modal completeness via the embedding. Instead, give propositional logic its own `Evaluate : (Atom → Prop) → PL.Proposition Atom → Prop` function and prove soundness/completeness natively. This is:
- More readable
- Simpler (no world/relation machinery)
- Pedagogically appropriate as a foundation before modal logic
- Congenial: shares the same structural proof shape (contrapositive + Lindenbaum + canonical model)

### Recommendation 2: Keep the same proof structure as modal completeness

The proof of propositional completeness should be structurally identical to `KCompleteness.lean` / `Completeness.lean`, just with:
- No `CanonicalWorld` type (use `Set (PL.Proposition Atom)` directly as a valuation)
- No accessibility relation
- No `box` case in Truth Lemma
- `Evaluate v φ ↔ φ ∈ M` as the Truth Lemma (where `v p = atom p ∈ M`)

### Recommendation 3: Name conventions matching modal pattern

Use parallel naming:
- `prop_axiom_sound` (analogous to `axiom_sound`, `k_axiom_sound`)
- `prop_soundness` (analogous to `soundness`, `k_soundness`)
- `PropCanonicalValuation` or `CanonicalValuation` (analogous to `CanonicalModel`)
- `prop_truth_lemma` (analogous to `truth_lemma`, `k_truth_lemma`)
- `prop_completeness` (analogous to `k_completeness`, `completeness`)

### Recommendation 4: Target 2 new files in a single implementation wave

Unlike the modal cube which required 13+ files, propositional soundness and completeness are achievable in 2 lean files plus a semantics file:
1. `Propositional/Semantics/Valuation.lean` (~50-80 lines)
2. `Propositional/Metalogic/Soundness.lean` (~60-80 lines)
3. `Propositional/Metalogic/Completeness.lean` (~100-130 lines)

This is approximately 250-290 lines total — a focused, small implementation.

### Recommendation 5: Propositional completeness does NOT help with modal completeness

The propositional embedding and propositional completeness do not "transfer" to give modal completeness for free. Modal completeness requires the full canonical Kripke model construction (existence lemma, box-witness, truth lemma for `box` formulas). Propositional completeness is a prerequisite in a pedagogical sense but not a formal lemma used in modal completeness proofs in this codebase.

---

## Alignment with Existing Architecture

| Component | Modal | Temporal | Propositional (needed) |
|-----------|-------|----------|----------------------|
| Formula type | `Modal.Proposition` | `Formula` | `PL.Proposition` (exists) |
| Semantics | `Model`, `Satisfies` | `TemporalModel`, `Satisfies` | `Valuation`, `Evaluate` (NEW) |
| Axioms | `ModalAxiom`, `KAxiom`, etc. | `Axiom` | `PropositionalAxiom` (exists) |
| Derivation tree | `DerivationTree Axioms Γ φ` | `DerivationTree FC Γ φ` | `DerivationTree Γ φ` (exists) |
| Derivation system | `modalDerivationSystem Axioms` | temporal DS | `propDerivationSystem` (exists) |
| Deduction theorem | `modal_has_deduction_theorem` | `temporal_has_deduction_theorem` | `prop_has_deduction_theorem` (exists) |
| MCS | `Modal.SetMaximalConsistent` | `Temporal.SetMaximalConsistent` | `PropSetMaximalConsistent` (exists) |
| Lindenbaum | `modal_lindenbaum` | `temporal_lindenbaum` | `prop_lindenbaum` (exists) |
| Soundness | `soundness` in Soundness.lean | `soundness` in Soundness.lean | MISSING |
| Completeness | `completeness` in Completeness.lean | `completeness` in Completeness.lean | MISSING |
| Proof system typeclass | `ClassicalHilbert` (+ modal) | `TemporalBXHilbert` | `ClassicalHilbert` (exists) |
| Instance registration | `ProofSystem/Instances.lean` | `ProofSystem/Instances.lean` | `ProofSystem/Instances.lean` (exists) |

The propositional system is essentially **complete at the proof-system level** and has the full MCS infrastructure. The only gap is:
1. Propositional semantics (valuations)
2. Soundness theorem
3. Completeness theorem

---

## Confidence Level

**Very high confidence** on all findings. The codebase is consistent and well-documented. The architectural pattern is clear from examining modal and temporal metalogic in detail. The propositional metalogic infrastructure (MCS, deduction theorem, derivation system) is production-ready and directly usable.

**High confidence** on the strategic recommendations:
- The 2+1 file structure (semantics + soundness + completeness) exactly mirrors the modal pattern
- The proof of completeness is structurally simple (remove box case from modal proof)
- The canonical valuation construction has no major obstacles

**Medium confidence** on the embedding coherence discussion: while the embedding `PL.Proposition.toModal` exists in `FromPropositional.lean`, verifying that semantics-preservation holds under this embedding is future work that needs more investigation.

---

## Appendix: Critical Files Read

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/Soundness.lean` — parameterized modal soundness
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/Completeness.lean` — S5 completeness (canonical model, truth lemma)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/KSoundness.lean` — K soundness (system-specific instantiation pattern)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/KCompleteness.lean` — K completeness (K-specific box witness, truth lemma)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/MCS.lean` — propositional MCS (already uses generic framework)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` — deduction theorem (complete)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Derivation.lean` — propDerivationSystem
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Instances.lean` — ClassicalHilbert instance
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Defs.lean` — PL.Proposition type, theory types, CPL/IPL
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/Consistency.lean` — generic MCS framework
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Basic.lean` — modal model/satisfies definitions
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/FromPropositional.lean` — PL→Modal embedding
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Soundness.lean` — temporal soundness pattern
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Completeness.lean` — temporal completeness pattern
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` — bridge pattern for lifting
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/ProofSystem.lean` — ClassicalHilbert hierarchy
