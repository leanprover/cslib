# Research Report: Task #112 (Round 2)

**Task**: Establish soundness and completeness for propositional Hilbert proof systems
**Date**: 2026-06-10
**Mode**: Team Research (4 teammates)
**Session**: sess_1781156597_744ceb

---

## Summary

This round drew on the newly converted literature sources (CZ full text, AML handbook chapters) and deep codebase analysis to work through exactly what is needed for all three propositional Hilbert levels. The key finding is a sharp complexity asymmetry: **classical completeness is immediately implementable (~250 lines, all infrastructure exists)**, while intuitionistic and minimal completeness require fundamentally different semantic machinery that does not yet exist in the codebase (~600-800 additional lines of new infrastructure).

Four convergent findings drive the implementation strategy:

1. **The MCS infrastructure is classical-only.** `prop_lindenbaum`, `prop_negation_complete`, and the entire `MCS.lean` framework produce maximally consistent sets with the excluded-middle property (`φ ∈ S ∨ ¬φ ∈ S`). This is the correct canonical construction for bivalent semantics but is structurally incompatible with intuitionistic completeness, which requires prime theories (deductively closed sets with the disjunction property) as canonical worlds.

2. **`HilbertMin` and `HilbertInt` have zero instance registrations.** The tag types exist in `ProofSystem.lean` but no derivation trees, inference system instances, or axiom types exist for them. New `MinPropAxiom` and `IntPropAxiom` inductive types must be created before any soundness/completeness work can begin for these levels.

3. **The propositional `DerivationTree` hardcodes all four classical axioms.** Unlike the modal `DerivationTree Axioms Γ φ` which is parameterized over an axiom predicate, the propositional version uses `PropositionalAxiom` directly. The cleanest solution (all teammates agree) is to create separate axiom inductive types for each level, exactly mirroring the modal `KAxiom`/`TAxiom`/`S4Axiom` pattern.

4. **Minimal logic semantics differs from intuitionistic.** In intuitionistic Kripke semantics, `⊥` is never forced (always false at every world). In minimal logic, `⊥` is treated as a propositional atom with an upward-closed valuation — it can be forced at some worlds. This requires a different model type with an extra field for the ⊥-valuation.

---

## Key Findings

### Classical Completeness: Ready for Implementation

All four teammates confirm that classical completeness is a near-verbatim simplification of the modal K completeness proof. The exact mapping:

| Modal K (existing) | Propositional Classical (new) |
|---------------------|------------------------------|
| `CanonicalWorld Axioms` | `PropCanonicalWorld` (subtype of `PropSetMaximalConsistent`) |
| `CanonicalModel Axioms` | `canonicalValuation : PropCanonicalWorld → Valuation` |
| `k_truth_lemma` | `prop_truth_lemma` (remove `.box` case, use `prop_*` APIs) |
| `k_completeness` | `prop_completeness` (same structure, no frame conditions) |
| `k_axiom_sound` | `prop_axiom_sound` (4 cases: K, S, EFQ, Peirce — all trivial) |

The `imp` case of the Truth Lemma (the only hard step) transfers from `KCompleteness.lean` lines 193-248 with three changes: use `prop_closed_under_derivation` instead of `modal_closed_under_derivation`, use `prop_implication_property` instead of `modal_implication_property`, and remove the `h_K`/`h_implyK`/etc. explicit axiom parameters.

**Files**: `Semantics/Basic.lean` (~50 lines), `Metalogic/Soundness.lean` (~70 lines), `Metalogic/Completeness.lean` (~130 lines). Total: ~250 lines.

### Intuitionistic Completeness: New Infrastructure Required

CZ Chapter 2, Theorem 2.43 proves intuitionistic completeness via Hintikka systems — a fundamentally different approach from the MCS method used for classical and modal logic. The canonical model for intuitionistic logic has:

- **Worlds** = prime deductively-closed consistent theories (or equivalently, saturated consistent tableaux from CZ)
- **Accessibility** = set inclusion (information growth: `w ≤ w'` iff `w ⊆ w'`)
- **Forcing** = intuitionistic forcing with universal quantification over successors for `→`

The forcing relation for `PL.Proposition Atom` (with `atom | bot | imp` primitives):
- `w ⊩ atom p` iff `atom p ∈ w`
- `w ⊩ ⊥` iff `False` (never forced)
- `w ⊩ φ → ψ` iff `∀ w' ≥ w, w' ⊩ φ → w' ⊩ ψ`

**Key new ingredients needed**:
1. `IntPropAxiom` inductive type (implyK, implyS, efq — no peirce)
2. `intDerivationSystem` and instance registrations for `HilbertInt`
3. `IModel` / `IntFrame` structure (partial order + persistent valuation)
4. `IForces` forcing relation with persistence lemma
5. Prime theory definition and `int_lindenbaum` (consistent → prime theory extension)
6. Canonical model construction from prime theories
7. Intuitionistic Truth Lemma and completeness theorem

### Minimal Completeness: Shares Infrastructure but Differs on ⊥

Minimal logic shares the Kripke frame structure with intuitionistic logic but differs in the forcing clause for `⊥`:

- **Intuitionistic**: `w ⊩ ⊥` iff `False` (⊥ never forced)
- **Minimal**: `w ⊩ ⊥` iff `⊥ ∈ V_bot(w)` (⊥ potentially forced, upward-closed)

This means minimal logic needs a model type with an additional `V_bot` field (or treating ⊥ as an atom). Teammate C identified this as a HIGH risk that was underestimated in Round 1.

However, all structural infrastructure (persistence, Truth Lemma structure, canonical model construction) is shared between intuitionistic and minimal cases. The parameterized soundness pattern (callback for axiom soundness) covers both with different axiom callbacks.

### CZ Chapter 1 Attribution Correction

Teammate C identified that CZ Chapter 1 proves classical completeness via **semantic tableaux / Hintikka systems**, not via Henkin/MCS. The MCS approach used in the codebase comes from CZ Chapter 5 (canonical model method). This does not affect implementation — the MCS approach is valid and supported by existing infrastructure — but the citation should reference CZ Chapter 5, not Chapter 1.

### Literature Assessment

The new AML handbook chapters are primarily about general modal completeness theory (lattice of NExtK, canonical formulas, Sahlqvist correspondence). **Section 3** on superintuitionistic logics and the Gödel translation (Int → S4) is directly relevant to future work connecting intuitionistic and modal completeness, but does not change the implementation approach for task 112.

---

## Synthesis

### Conflicts Resolved

**1. Scope estimation divergence**: Teammate A estimates ~780 total lines, Teammate B estimates ~615, Teammate C estimates 1200-2500+. The divergence stems from different assumptions about what counts as "new infrastructure."

**Resolution**: The realistic estimate is ~250 lines for classical (all agree), plus ~400-600 lines for the shared intuitionistic Kripke infrastructure, plus ~100-200 lines for minimal-specific adaptations. Total: **~750-1050 lines across 8-10 new files**. Teammate C's higher estimate includes potential code for Hintikka system formalization, which is not needed if we use the prime theory approach instead.

**2. Hintikka systems vs. prime theories for intuitionistic completeness**: Teammate A describes the CZ Hintikka approach in detail. Teammate B recommends prime deductively-closed theories as cleaner for Lean. Teammate C notes both are different from MCS.

**Resolution**: Use the **prime theory approach** (Teammate B's recommendation). It fits more naturally with the existing Lindenbaum/Zorn infrastructure in `Consistency.lean`, avoids defining a new "tableau" type, and produces canonical model worlds of the same shape (`Set (Proposition Atom)`) as the modal canonical model. The Hintikka system approach is equivalent but adds an extra layer of indirection.

**3. Minimal ⊥ semantics**: Teammate A says minimal and intuitionistic share the same model. Teammate C says they need different model types because ⊥ is forceable in minimal.

**Resolution**: Teammate C is correct. The standard Kripke semantics for minimal logic treats ⊥ as an atom with an upward-closed valuation (Johansson 1937, Colacito-de Jongh-Vardas). However, this can be handled by parameterizing the `IForces` function over the ⊥ forcing clause, rather than creating an entirely separate model type. A single `IModel` with an optional `bot_forces` field covers both cases.

**4. Whether to refactor `DerivationTree` or create new types**: Teammate C raises this as an architecture decision. Teammates A and B both recommend creating separate axiom inductive types (like modal `KAxiom`, `S4Axiom`).

**Resolution**: Create separate `MinPropAxiom` and `IntPropAxiom` inductive types. Do NOT refactor the existing `DerivationTree` — the existing `propDerivationSystem` and all code depending on it should remain unchanged. The new axiom types enable separate derivation systems (`intDerivationSystem`, `minDerivationSystem`) using the same `DerivationTree`-style pattern but with restricted axiom constructors. This mirrors exactly how the modal codebase handles K, T, S4, S5 as different axiom sets over the same tree structure.

### Gaps Identified

1. **Deduction theorem compatibility**: The existing `prop_has_deduction_theorem` uses only K and S axioms (confirmed by Teammate A). This means it is automatically compatible with all three levels — no new deduction theorem proofs needed.

2. **Prime theory Lindenbaum lemma**: No existing infrastructure. The generic `set_lindenbaum` in `Consistency.lean` produces MCS (negation-complete sets), not prime theories. A new `int_lindenbaum` producing prime deductively-closed theories is needed. Estimated ~50-80 lines.

3. **NaturalDeduction infrastructure**: Teammate D notes that `NaturalDeduction/` already has a theory-parameterized derivation system. The relationship between this and the Hilbert system should be clarified but is not blocking for task 112.

4. **Coherence theorem**: Once classical semantics is defined, a ~20-30 line semantic coherence theorem for `FromPropositional.lean` becomes provable. Should be included in the integration phase.

---

## Recommended Task Decomposition

Based on the unanimous team recommendation, task 112 should be **expanded** into sub-tasks with the following dependency structure:

```
Sub-task A: Classical soundness/completeness (~250 lines, 3 files)
  ├── Semantics/Basic.lean (Valuation, Evaluate, Tautology)
  ├── Metalogic/Soundness.lean (prop_axiom_sound, prop_soundness)
  └── Metalogic/Completeness.lean (canonicalValuation, prop_truth_lemma, prop_completeness)
  Dependencies: None. All infrastructure exists. Implement immediately.

Sub-task B: Axiom types + derivation systems for Int/Min (~80 lines, 1-2 files)
  ├── ProofSystem/IntMinAxioms.lean (IntPropAxiom, MinPropAxiom, derivation systems)
  └── ProofSystem/IntMinInstances.lean (HilbertInt, HilbertMin instance registrations)
  Dependencies: None (parallel with A).

Sub-task C: Propositional Kripke semantics (~150 lines, 1 file)
  └── Semantics/Kripke.lean (IModel, IForces, persistence, IValid)
  Dependencies: A (for design pattern reference).

Sub-task D: Intuitionistic soundness/completeness (~350 lines, 3 files)
  ├── Metalogic/IntSoundness.lean (int_axiom_sound, int_soundness)
  ├── Metalogic/IntLindenbaum.lean (prime theory infrastructure, int_lindenbaum)
  └── Metalogic/IntCompleteness.lean (canonical Kripke model, int_truth_lemma, int_completeness)
  Dependencies: B, C.

Sub-task E: Minimal soundness/completeness (~150 lines, 2 files)
  ├── Metalogic/MinSoundness.lean (min_axiom_sound, min_soundness — thin wrapper)
  └── Metalogic/MinCompleteness.lean (adapted forcing for ⊥, min_completeness)
  Dependencies: B, C, D (shares infrastructure).

Sub-task F: Module integration (~50 lines)
  ├── Update Cslib.lean imports
  └── Semantic coherence theorem for FromPropositional.lean
  Dependencies: A, D, E.
```

**Implementation ordering**: A → B (parallel with A) → C → D → E → F

**Critical path**: A is standalone and should proceed immediately. B and C can follow in parallel. D is the hardest sub-task (prime theory Lindenbaum + intuitionistic Truth Lemma). E reuses D's infrastructure.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (exact proof steps for all 3 levels) | completed | high |
| B | Alternatives (reuse patterns, Gödel translation assessment) | completed | high |
| C | Critic (gaps, risks, scope estimation) | completed | high |
| D | Horizons (strategic alignment, AML assessment) | completed | high |

---

## References

### Primary Literature
- Chagrov, A. and Zakharyaschev, M. (1997). *Modal Logic*. Oxford Logic Guides, Vol. 35.
  - Chapter 1 (Theorem 1.16): Classical completeness via semantic tableaux
  - Chapter 2 (Section 2.2): Intuitionistic Kripke semantics
  - Chapter 2 (Section 2.6, Theorem 2.43): Intuitionistic completeness via Hintikka systems
  - Chapter 5 (Section 5.1): Henkin/canonical model construction (what the codebase actually follows)
- Zakharyaschev, M., Wolter, F., Chagrov, A. "Advanced Modal Logic" (Handbook chapter)
  - Section 3: Superintuitionistic logics and Gödel translation (future work reference)

### Critical Codebase Files
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` — Complete MCS infrastructure (classical only)
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` — `DerivationTree` (hardcoded `PropositionalAxiom`)
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` — `ClassicalHilbert HilbertCl` (only level with instances)
- `Cslib/Logics/Modal/Metalogic/KCompleteness.lean` — Direct template for classical propositional completeness
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` — Parameterized soundness pattern to adapt
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` — Generic MCS/Lindenbaum (classical only)
- `Cslib/Foundations/Logic/ProofSystem.lean` — `HilbertMin`, `HilbertInt`, `HilbertCl` tag types
