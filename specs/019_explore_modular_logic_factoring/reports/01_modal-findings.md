# Modal Logic Factoring Analysis

**Task**: 19 — Explore modular logic factoring
**Focus**: Modal components in BimodalLogic that belong in Modal/
**Date**: 2026-06-08

---

## (a) What Currently Exists in cslib's Modal Module

### Basic.lean (393 lines — the most developed logic)
- `Modal.Proposition Atom` with `{atom, bot, imp, box}` + derived connectives
- `ModalConnectives` instance
- `Model World Atom` (accessibility relation + valuation)
- `Satisfies` recursive definition for all constructors
- Simp lemmas for satisfaction of neg, diamond, and, or
- `Judgement`, `HasInferenceSystem` instance for semantic derivation
- **Proved frame correspondence theorems**: K (all models), T↔reflexive, B↔symmetric, 4↔transitive, 5↔Euclidean, D↔serial — with BOTH directions for all non-K axioms
- `Proposition.valid`, `logic` (modal logic of a model class)

### Cube.lean (140 lines)
- Definitions of 15 standard modal logics (K, T, B, Four, Five, K45, D, D4, D5, D45, DB, TB, KB5, S4, S5)
- Subset ordering proofs: `k_subset_d`, `k_subset_b`, `k_subset_four`, `k_subset_five`, `d_subset_t`, `k_subset_t`
- Validity proofs: `K.k_valid`, `T.t_valid`

### Denotation.lean (85 lines)
- `Proposition.denotation`: maps propositions to sets of worlds
- `satisfies_mem_denotation` characterization theorem
- `neg_denotation`, `theoryEq_denotation_eq`

### What Modal Currently Lacks
- No Hilbert-style proof system
- No `Derivation`/`DerivationTree`
- No `Derivable` predicate
- No derived theorems (K/S combinators, S5 derived results)
- No substitution
- No context management
- No natural deduction (PL has it, Modal doesn't)
- `ModalHilbert` and `ModalS5Hilbert` classes exist in ProofSystem.lean but have no concrete instances

---

## (b) BimodalLogic Components That Are Purely Modal

### From Task 5 (Derived Theorems)

**ModalS4.lean (~400 lines)**: S4 derived theorems using only `box`, `imp`, `bot` — no temporal operators. Examples: `□(φ → ψ) → (□φ → □ψ)`, transitivity `□φ → □□φ` as derived rules, iteration lemmas.

**ModalS5.lean (~400 lines)**: S5 derived theorems — purely modal. Examples: `◇□φ → □φ`, `◇φ → □◇φ` as derived consequences, S5 reduction lemmas.

**GeneralizedNecessitation.lean (~400 lines)**: `⊢ φ₁ → ... → φₙ → ψ` implies `⊢ □φ₁ → ... → □φₙ → □ψ`. Purely modal if stated for a single `□`. The bimodal version generalizes to temporal necessitation too.

### From Task 4 (Proof System)
- BimodalLogic's 42 axiom schemata include a **purely modal subset**: the S5 axioms (K, T, 4, B/5, D, Dual). Already defined polymorphically in `Axioms.lean`.
- `DerivationTree` has 7 rules; modus ponens and necessitation are purely modal/propositional.
- **Substitution.lean (~500 lines)**: The substitution function is structural and could be defined per-logic with a typeclass.

### From Task 6 (Frame Conditions + Soundness)
- cslib **already has** modal frame condition proofs semantically (K/T/B/4/5/D valid under the right relation properties, with bidirectional characterizations). Missing: connecting these to a syntactic proof system.

---

## (c) What Could Be Factored into Modal/

### Tier 2: Modal-level — generic over `[ModalS5Hilbert S]`

| Component | ~Lines | Target Location |
|-----------|--------|-----------------|
| S4 derived theorems | ~400 | `Cslib/Logics/Modal/Theorems/S4.lean` |
| S5 derived theorems | ~400 | `Cslib/Logics/Modal/Theorems/S5.lean` |
| Generalized necessitation | ~400 | `Cslib/Logics/Modal/Theorems/GenNec.lean` |

**Total: ~1,200 lines** that belong in Modal/, not Bimodal/.

### What Modal/ Would Need

1. **Modal proof system** — A `Modal.DerivationTree` with necessitation + K axiom, providing `ModalHilbert Modal.HilbertK` and `ModalS5Hilbert Modal.HilbertS5` instances
2. **Substitution** — `Modal.Proposition.subst` and the substitution theorem for K/S5
3. **Connection to semantics** — Linking the existing semantic frame correspondence theorems to the syntactic proof system

### Feasibility

The S4/S5 derived theorems from BimodalLogic are stated for the bimodal `DerivationTree` but only use the `box`-related rules (necessitation) and propositional axioms. They could be restated at the `[ModalS5Hilbert S]` level. The challenge is that BimodalLogic's proofs build `DerivationTree` terms directly (constructive proof terms), so they need to be refactored to use the typeclass API instead. This is non-trivial but feasible.

### Impact on Existing Tasks

**Task 5 (Port Derived Theorems)**: ModalS4 + ModalS5 + GenNec (~1,200 lines) → `Modal/Theorems/` with `[ModalS5Hilbert S]` signatures instead of `Bimodal/Theorems/`.

**Current gap**: Modal/ has Kripke semantics and frame correspondence theorems, but NO Hilbert-style proof system or derived theorems. Adding these would make Modal/ a complete standalone module.

### Summary

| Component | Lines | Should Live In | Blocking Issue |
|-----------|-------|----------------|----------------|
| S4 derived theorems | ~400 | Modal/ or typeclass | Refactor from concrete to generic |
| S5 derived theorems | ~400 | Modal/ or typeclass | Same; depends on BimodalLogic:294 |
| Generalized necessitation | ~400 | Modal/ or typeclass | Uses only box+MP |
| Modal Kripke completeness | new | Modal/ | Would be new development |
| Uniform substitution (modal) | ~500 | Modal/ | Definition per type, theorem generic |
