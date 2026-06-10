# Teammate D Findings: Strategic Horizons

**Task**: 80 — Generic DeductionTheorem interface across all logic domains
**Angle**: Long-term alignment, strategic direction, creative alternatives
**Date**: 2026-06-10

## Key Findings

### 1. The "Most General Level" Principle Is Strongly Satisfied

A generic deduction theorem in `Foundations/Logic/` perfectly aligns with the project's core architectural principle. The existing precedent is strong:

- `Foundations/Logic/Metalogic/Consistency.lean` already provides generic MCS theory parameterized over `DerivationSystem`
- `Foundations/Logic/Helpers/ListHelpers.lean` (created by task 79) already extracted the shared `removeAll` utilities
- `Foundations/Logic/ProofSystem.lean` defines the typeclass hierarchy (`PropositionalHilbert`, `ModalHilbert`, etc.)
- `Foundations/Logic/InferenceSystem.lean` provides the generic inference framework

The deduction theorem proof is **mathematically logic-agnostic** — it depends only on the structure of derivation trees, not on the specific logic. Placing it in Foundations is the natural home.

### 2. FormalizedFormalLogic/Foundation Validates the Typeclass Approach

The FormalizedFormalLogic/Foundation project (the most mature multi-logic Lean 4 formalization, with Gödel incompleteness theorems formalized) uses an architecture strikingly similar to what task 80 proposes:

- **`Entailment` typeclass**: `class Entailment (S : Type*) (F : outParam Type*) where Prf : S → F → Type*` — generic proof relation
- **`Deduction` typeclass**: Generic deduction theorem as a bidirectional equivalence between `adjoin φ 𝓢 ⊢! ψ` and `𝓢 ⊢! φ 🡒 ψ`
- **`Axiomatized` typeclass**: Shared axiom handling and weakening
- **`Sound`/`Complete` typeclasses**: Separate semantic/proof-theoretic properties

Their approach confirms that a typeclass-based abstraction for proof systems is both practical and the emerging standard in Lean 4 logic formalization.

**Critical difference**: FormalizedFormalLogic works at the `Prop` level (derivability, `Nonempty` wrappers), while CSLib's deduction theorem operates at the `Type` level (concrete `DerivationTree` terms with pattern matching and height). This means CSLib's generic typeclass needs to expose **concrete tree accessors**, not just derivability predicates.

### 3. Extensibility Assessment: Good for Known Patterns

**Current pattern**: Each logic has 4 common constructors (ax, assumption, mp, weakening) plus 0-3 "empty-context-only" constructors (necessitation, temporal_necessitation, temporal_duality). The extra constructors are all discharged identically: `simp at hA` (the context is `A :: Γ` which is non-empty, contradicting the empty-context requirement).

**Future logic assessment**:
| Logic | Extra Constructors | Deduction Theorem Pattern |
|-------|-------------------|--------------------------|
| Epistemic (K_i) | `knowledge_necessitation` (empty ctx) | Same `simp at hA` discharge |
| Deontic (SDL) | `obligation_necessitation` (empty ctx) | Same `simp at hA` discharge |
| PDL | `program_necessitation` (empty ctx) | Same `simp at hA` discharge |
| Conditional | None expected | Pure propositional pattern |
| Intuitionistic | Different — no Peirce/DNE | Would NOT use this framework |

The pattern holds for all normal modal logics and their temporal/dynamic extensions. It would break only for intuitionistic or substructural logics — which are not on this project's roadmap and have fundamentally different proof theories.

**Recommendation**: Design the "extra constructor dispatch" as a single callback/method, not hard-coded for specific constructor names. This lets any future logic plug in without touching the generic core.

### 4. Broader Metalogic Generalization — Task 80 as a Stepping Stone

Task 41 ("Abstract shared completeness infrastructure") is the next major deduplication target. Analyzing the relationship:

| Shared Pattern | Task 80 (Deduction) | Task 41 (Completeness) |
|---------------|---------------------|----------------------|
| Core abstraction | DerivationTree constructors | Canonical model construction |
| What varies | Extra constructors (0-3) | Modal/temporal operators, frame class |
| Dispatch mechanism | `simp at hA` for all extras | Per-logic witness/seed construction |
| Difficulty | Medium (structural) | Very High (semantic) |

Task 80 establishes the *pattern* for abstracting over derivation tree structure. The typeclass interface designed here (especially the height function and constructor accessors) will likely be reused or extended for completeness proofs. This argues for designing the typeclass slightly more generally than task 80 strictly requires.

### 5. Cognitive Cost Analysis

**The typeclass approach wins on readability in the long run:**

- **Status quo**: 4 files × ~200 lines = ~800 lines total. A developer extending the library must understand one 200-line file. But if they want to understand *why* it works, they must diff 4 files to see which parts are universal vs. domain-specific.
- **After task 80**: 1 generic file (~200 lines) + 4 instance files (~15-25 lines each) = ~300 lines total. A developer sees the proof structure once. Adding a new logic means providing a short instance — the proof strategy is explicit, not implicit in copy-paste.

**The real readability concern** is the typeclass interface itself. If it requires 15+ fields, instance construction becomes a puzzle. The design should aim for ≤8 fields in the core typeclass.

**Quantitative**: 600 lines eliminated, ~100 lines of new typeclass infrastructure added. Net savings: ~500 lines. The typeclass adds a one-time learning cost but eliminates the ongoing synchronization burden (keeping 4 parallel proofs consistent during refactoring).

### 6. Creative Alternative: Hybrid Approach (Recommended)

Rather than pure typeclass abstraction OR pure documentation, consider a **two-layer design**:

**Layer 1 — `HasDerivationTree` typeclass** (in `Foundations/Logic/Metalogic/`):
- Exposes the 4 common constructors, height, and height lemmas
- Provides a single `extraCasesVacuous` method for handling domain-specific constructors
- Contains the generic `deduction_theorem` and `deduction_with_mem` proofs

**Layer 2 — Thin domain wrappers** (in each logic's `DeductionTheorem.lean`):
- Each file provides a `HasDerivationTree` instance (~15-25 lines)
- Each file provides the `*_has_deduction_theorem` wrapper connecting to `DerivationSystem`
- **Each file retains its docstring** explaining the domain-specific constructor count and why extra cases are vacuous

This preserves domain-level documentation and discoverability while eliminating code duplication.

### 7. Task 79 Interaction

Task 79 (status: PLANNED) already completed Phase 1 which extracted `removeAll` + list helpers to `Foundations/Logic/Helpers/ListHelpers.lean`. This is a direct dependency for task 80 — the generic deduction theorem proof will import `ListHelpers` rather than defining its own list utilities.

Task 79's plan explicitly marks the DeductionTheorem generalization as "separated into task 80." The groundwork (list helpers, `module` keyword migration from task 78) is ready.

## Strategic Alignment Assessment

| Criterion | Rating | Notes |
|-----------|--------|-------|
| Fits "most general level" principle | ✅ Strong | Perfect fit — proof is logic-agnostic |
| Module hierarchy compatibility | ✅ Strong | Foundations → all logics, no cross-logic coupling |
| Future extensibility | ✅ Good | Works for all normal modal logics; callback-based dispatch handles unknowns |
| Consistency with existing patterns | ✅ Strong | Follows `DerivationSystem`/`HasDeductionTheorem` precedent |
| Alignment with external projects | ✅ Good | FormalizedFormalLogic uses similar architecture |
| Stepping stone for task 41 | ✅ Moderate | Establishes pattern, but completeness needs different abstraction layer |
| Mathlib contribution potential | ⚠️ Low | CSLib-specific proof trees unlikely to land in Mathlib |
| Cognitive cost trade-off | ✅ Positive | Net simplification for library users |

## Creative/Unconventional Approaches Considered

### A. Meta-Theorem Documentation (Rejected)
Each logic keeps its own proof but follows a documented template. A custom linter checks conformance.
- **Pros**: Zero coupling, easy to understand individually
- **Cons**: Doesn't actually eliminate code. Linter is fragile. Doesn't prevent drift during refactoring.
- **Verdict**: Rejected. The duplication is real engineering debt, not a documentation problem.

### B. Tactic Macro (Partial Consideration)
Write a `deduction_theorem_tactic` that handles the common cases and leaves only domain-specific goals.
- **Pros**: Very lightweight — no typeclass overhead
- **Cons**: Fragile across Lean version upgrades. Doesn't compose with generic MCS framework. Hard to understand proof state.
- **Verdict**: Not recommended as primary approach, but could complement the typeclass approach for the `deduction_with_mem` proof body.

### C. Generic Inductive with Extra Constructor Parameter (Worth Exploring)
Instead of a typeclass, define a single parameterized inductive:
```lean
inductive GenericDerivationTree (ExtraCtor : List F → F → Type) : List F → F → Type where
  | ax : ... | assumption : ... | mp : ... | weakening : ...
  | extra (Γ : List F) (φ : F) (h : ExtraCtor Γ φ) (hΓ : Γ = []) : ...
```
- **Pros**: Single inductive, clean pattern matching, height computed once
- **Cons**: Requires each logic to map its concrete tree into the generic one (possibly expensive). Breaks existing `DerivationTree` API. Would need `ExtraCtor` to carry proofs about empty context.
- **Verdict**: Interesting but too invasive. Would require rewriting all downstream code that pattern-matches on domain-specific trees.

### D. Reflection/Embedding Approach (Novel)
Each logic provides a `toGenericTree` function that erases domain-specific constructors into a unified representation, prove the generic theorem on the unified representation, then lift back.
- **Pros**: Zero changes to existing `DerivationTree` types
- **Cons**: Double proof obligation (embedding correctness + generic theorem). More complex than typeclass approach.
- **Verdict**: Overly complex for the savings.

## Long-Term Recommendations

1. **Proceed with the two-layer typeclass approach** (Layer 1: `HasDerivationTree` in Foundations, Layer 2: thin instances in each logic). This is the most aligned with project architecture, external best practice, and future extensibility.

2. **Design `HasDerivationTree` with ≤8 fields**, focusing on:
   - The 4 common constructors (as match/recursor access)
   - Height function + 3 height ordering lemmas
   - One callback for "remaining constructors are vacuous when context is non-empty"

3. **Keep domain-specific `DeductionTheorem.lean` files** (not empty) — they should contain the instance definition, the `*_has_deduction_theorem` wrapper, and a docstring explaining the domain-specific aspects. This preserves discoverability.

4. **Name the typeclass `HasDerivationTree`** to clearly signal it's about tree structure, not just derivability. This distinguishes it from the existing `HasDeductionTheorem` (which is a `Prop`-level property) and `DerivationSystem` (which bundles `Deriv`, `weakening`, `assumption`, `mp`).

5. **Consider future-proofing** for task 41 by making the typeclass extensible (e.g., allow additional methods that completeness proofs might need, without requiring them for the deduction theorem).

## Confidence Level

**High** — The strategic alignment is clear, the external validation from FormalizedFormalLogic is strong, and the existing project infrastructure (task 79 groundwork, `DerivationSystem`, `HasDeductionTheorem`) already points in this direction. The main uncertainty is in the detailed typeclass design (how to express the "extra constructors are vacuous" dispatch cleanly), which is an implementation question rather than a strategic one.
