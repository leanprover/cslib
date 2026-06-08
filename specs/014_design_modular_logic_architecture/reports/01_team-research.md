# Research Report: Task #14

**Task**: Design modular logic architecture for composable modal, temporal, and bimodal syntax and proof systems
**Date**: 2026-06-08
**Mode**: Team Research (4 teammates)

## Summary

This report synthesizes findings from 4 parallel research agents investigating how to design a modular architecture so that modal, temporal, and bimodal (TM) logic can each be imported independently and composed together. The research examined cslib's existing infrastructure, BimodalLogic's monolithic codebase, the FormalizedFormalLogic/Foundation project, Mathlib patterns, and the academic literature on combining logics.

The core finding is that **full compositional decomposition of the bimodal metalogic is not feasible**, but a **practical modular architecture** is achievable through separate formula types per logic, a shared typeclass layer for connectives, cslib's `InferenceSystem` framework for proof system abstraction, and embedding/conservative-extension theorems as the composition mechanism.

## Key Findings

### 1. Separate Formula Types with Shared Typeclass Layer (Consensus Recommendation)

All teammates converge on the approach established by [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation): each logic defines its own concrete inductive `Formula` type, and composition is achieved through shared typeclasses on those types, not by extending or parameterizing a single inductive.

**Why not a single parameterized formula type?** Lean 4 has no mechanism for extending inductive types. Parameterizing constructors with boolean/proof guards (e.g., `| box : hasBox = true → ...`) breaks pattern matching, notation, decidable equality, and `grind` automation. No existing Lean 4 project uses this pattern.

**Why not a typeclass-stratified monolith?** (Teammate B proposed this.) While a single Formula with all 6 constructors plus typeclass-based access gating matches some Mathlib patterns, it provides only discipline-based (not type-based) separation — pure modal code can still pattern-match on temporal constructors. Given that cslib already uses separate formula types (PL, Modal, HML, CLL each have their own), the separate-types approach is more aligned with cslib conventions.

**Concrete typeclass hierarchy** (from Teammate A, aligned with Foundation):
```lean
-- Cslib.Foundations.Logic.Connectives (new)
class HasBot (F : Type*) where bot : F
class HasImp (F : Type*) where imp : F → F → F
class HasBox (F : Type*) where box : F → F
class HasUntil (F : Type*) where untl : F → F → F
class HasSince (F : Type*) where snce : F → F → F

class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F
class TemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F, HasSince F
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```

**Three concrete formula types:**
- `Modal.Formula Atom` with `{atom, bot, imp, box}` — new, BimodalLogic-aligned primitives
- `Temporal.Formula Atom` with `{atom, bot, imp, untl, snce}` — new standalone temporal logic
- `Bimodal.Formula Atom` with `{atom, bot, imp, box, untl, snce}` — ported from BimodalLogic

Each type instantiates its appropriate connective class. Axioms and theorems defined polymorphically over connective classes (e.g., `[ModalConnectives F]`) apply to both Modal.Formula and Bimodal.Formula.

### 2. Do NOT Modify the Existing cslib Modal Module

**Conflict resolved**: Teammate A recommended refactoring `Cslib.Logics.Modal.Proposition` from `{atom, neg, and, diamond}` to `{atom, bot, imp, box}` to align with BimodalLogic. Teammate D explicitly recommended leaving it unchanged. The Critic (C) noted this would break all existing `grind`-based proofs.

**Resolution**: Leave `Cslib.Logics.Modal` unchanged. It serves its purpose (Kripke semantics for the Modal Cube) with a different design philosophy (diamond-primary, semantic-first). Define new `Cslib.Logics.Modal.Syntax` or similar with box-primary primitives if a Hilbert-style modal proof system is needed. The existing module is ~460 lines total and doesn't need to participate in the BimodalLogic architecture.

The two modal formula types (existing diamond-primary, new box-primary) can coexist via an equivalence theorem and embedding functions, if needed.

### 3. The Interaction Axiom Makes Full Metalogic Decomposition Impossible

The Critic's most important finding (high confidence): BimodalLogic's axiom `modal_future` (MF: `□φ → □(Gφ)`) is a modal-temporal *interaction* axiom whose soundness proof requires the combined semantic apparatus (world histories + temporal order + shift-closure). The derived axiom TF (`□φ → G□φ`) falls out of MF + S5 properties, deepening the entanglement.

**Consequences for metalogic results:**

| Result | Decomposable? | Reason |
|--------|--------------|--------|
| Propositional theorems | Yes | Self-contained, no modal/temporal operators |
| Pure modal S5 theorems | Partially | Depend only on box, imp, bot + modal axioms |
| Pure temporal BX theorems | Partially | BX1-BX12 are purely temporal; TL/Lin may interact |
| Interaction theorems (MF, TF, perpetuity) | No | Require both semantic frameworks simultaneously |
| Soundness | No | MF soundness requires task frames + world histories |
| Completeness | No | MCS construction uses all 42 axiom constructors; Burgess-Xu chronicles require interaction axiom |
| Decidability | No | Tableau operates on full 6-constructor Formula; modal and temporal rules interact in branch saturation |

**Implication**: The bimodal metalogic must remain monolithic. Standalone modal and temporal modules can have their own soundness/completeness results, but the bimodal results are NOT compositions of the two — they are independent proofs about the combined system.

### 4. Semantic Frameworks Are Fundamentally Different

| Aspect | cslib Modal | BimodalLogic |
|--------|------------|--------------|
| Framework | Kripke model `(W, R, V)` | Task frame `(W, T, ·)` with world histories |
| Modal operator | `□φ` = ∀ accessible worlds via R | `□φ` = ∀ world histories in shift-closed Ω |
| Accessibility | Binary relation `r : World → World → Prop` | Quantification over histories (implicit S5) |
| Temporal dimension | None | `LinearOrderedAddCommGroup T` polymorphic |
| Satisfaction | `Satisfies m w φ : Prop` | `truth_at M τ t ht φ : Prop` |

These cannot be unified into a single abstract semantic framework without losing the specific properties each relies on. The architecture should maintain separate semantic layers:
- Kripke semantics for pure modal logic (existing cslib)
- Linear order semantics for pure temporal logic (new)
- Task frame semantics for bimodal TM logic (ported from BimodalLogic)

### 5. cslib's InferenceSystem Is the Right Proof System Abstraction

All teammates agree that `InferenceSystem (S : Type*) (α : Type*)` with `derivation (a : α) : Sort v` is well-positioned for composable proof systems. It's already used across cslib (Modal, CLL, Propositional ND) and is more general than Foundation's `Entailment`.

**Composition via tags:**
```lean
opaque ModalLogic.Tag : Type := Empty
opaque TemporalLogic.Tag : Type := Empty
opaque BimodalLogic.Tag : Type := Empty
```

Each logic provides an `InferenceSystem` instance with its own tag. The `S⇓a` notation disambiguates which proof system is in scope.

### 6. Embeddings and Conservative Extension as the Composition Mechanism

Rather than composing formula types, define embedding functions:
```lean
def Modal.Formula.toBimodal : Modal.Formula Atom → Bimodal.Formula Atom
def Temporal.Formula.toBimodal : Temporal.Formula Atom → Bimodal.Formula Atom
```

Then prove conservative extension theorems:
```lean
theorem modal_embedding_sound : ⊢_Modal φ → ⊢_TM (φ.toBimodal)
theorem modal_embedding_conservative : ⊢_TM (φ.toBimodal) → ⊢_Modal φ
```

BimodalLogic already has a `ConservativeExtension/` directory demonstrating this pattern. These theorems precisely characterize how the separate logics relate, without requiring shared formula types.

### 7. The FrameClass Pattern Is Reusable Infrastructure

BimodalLogic's `FrameClass` enum with `minFrameClass` gating and `DerivationTree` parameterization by frame class is a clean, working example of composable proof systems *within* a logic. This pattern should be preserved in the port and potentially elevated to cslib infrastructure.

### 8. Prior Art Confirms the Approach

- **FormalizedFormalLogic/Foundation** (Lean 4): Separate formula types per logic, shared typeclass hierarchy for connectives, polymorphic axiom definitions. The gold standard.
- **Coalition Logic ITP 2024** (Lean 4): Typeclasses to generalize over logic components, proving metatheorems against typeclass interfaces.
- **Mathlib algebraic hierarchy**: Extension via `extends`, mixin typeclasses for properties, forgetful instances. Directly applicable pattern.
- **BimodalLogic's FrameConditions**: Typeclass hierarchy for frame conditions (`LinearTemporalFrame`, `DenseTemporalFrame`, `DiscreteTemporalFrame`).

## Synthesis

### Conflicts Resolved

| Conflict | Positions | Resolution |
|----------|-----------|------------|
| Monolithic vs. separate formula types | B: monolithic with typeclass gating; A,D: separate types | **Separate types** — aligns with cslib conventions and provides type-level separation |
| Refactor existing cslib Modal? | A: yes (align primitives); C,D: no (breaks proofs) | **No** — leave existing module unchanged, create new box-primary types alongside |
| How much decomposition? | A: ambitious decomposition; C: metalogic cannot decompose | **Pragmatic** — separate syntax, keep metalogic monolithic per logic |
| "Compose" vs. "Extend"? | C: extend is more practical | **Hybrid** — separate modules (composition at syntax/typeclass level), monolithic metalogic per logic (extend at proof level) |

### Gaps Identified

1. **No verification that InferenceSystem works for Hilbert-style derivations** — currently used only for semantic derivation. Needs proof-of-concept.
2. **No analysis of compilation time impact** — typeclass-heavy designs can increase compile times. BimodalLogic already has significant compilation times.
3. **Propositional layer alignment unaddressed** — cslib's `PL.Proposition` uses `{atom, and, or, impl}`, not `{atom, bot, imp}`. A third mismatch beyond modal and bimodal.
4. **`expose`/`module` interaction with typeclasses untested** — cslib uses these extensively; unclear how they interact with scoped typeclass instances.
5. **No concrete estimate of porting effort** — how much of BimodalLogic's ~50,000 lines can transfer directly vs. needs rewriting?

### Recommendations

#### Recommended Architecture

```
Cslib/
├── Foundations/
│   └── Logic/
│       ├── InferenceSystem.lean      -- UNCHANGED
│       └── Connectives.lean          -- NEW: typeclass hierarchy for connectives
├── Logics/
│   ├── Modal/                        -- UNCHANGED (existing Kripke-style modal logic)
│   │   ├── Basic.lean
│   │   ├── Cube.lean
│   │   └── Denotation.lean
│   ├── Temporal/                     -- NEW (standalone temporal logic)
│   │   ├── Syntax/
│   │   │   ├── Formula.lean          -- atom, bot, imp, untl, snce
│   │   │   └── Context.lean
│   │   ├── ProofSystem/
│   │   │   ├── Axioms.lean           -- Temporal axioms only (TK, T4, TT, TA, TL, Lin)
│   │   │   └── Derivation.lean
│   │   └── Semantics.lean            -- Linear order semantics
│   ├── Bimodal/                      -- NEW (ported from BimodalLogic)
│   │   ├── Syntax/
│   │   │   ├── Formula.lean          -- atom, bot, imp, box, untl, snce
│   │   │   ├── Context.lean
│   │   │   └── Subformulas/
│   │   ├── ProofSystem/
│   │   │   ├── Axioms.lean           -- All 21+ axiom schemata
│   │   │   └── Derivation.lean       -- FrameClass-parameterized derivation trees
│   │   ├── Semantics/
│   │   │   ├── TaskFrame.lean
│   │   │   ├── WorldHistory.lean
│   │   │   ├── Truth.lean
│   │   │   └── Validity.lean
│   │   ├── FrameConditions/          -- Typeclass hierarchy for frame conditions
│   │   ├── Metalogic/
│   │   │   ├── Soundness.lean
│   │   │   ├── Completeness.lean
│   │   │   └── Decidability.lean
│   │   └── Embedding/                -- NEW: Modal → Bimodal, Temporal → Bimodal
│   │       ├── ModalEmbedding.lean
│   │       ├── TemporalEmbedding.lean
│   │       └── ConservativeExtension.lean
│   ├── HML/                          -- UNCHANGED
│   ├── Propositional/                -- UNCHANGED
│   └── LinearLogic/                  -- UNCHANGED
```

#### Implementation Strategy

1. **Phase 1**: Define `Connectives.lean` typeclass hierarchy and `Temporal.Syntax.Formula`
2. **Phase 2**: Port `Bimodal.Syntax` from BimodalLogic (minimal changes — align with connective typeclasses)
3. **Phase 3**: Port `Bimodal.ProofSystem` and `Bimodal.Semantics`
4. **Phase 4**: Define embedding functions (`Modal.Formula.toBimodal`, `Temporal.Formula.toBimodal`)
5. **Phase 5**: Port `Bimodal.Metalogic` (soundness, completeness, decidability — largely intact from BimodalLogic)
6. **Phase 6**: Prove conservative extension theorems
7. **Phase 7**: (Optional) Add standalone temporal logic metalogic results

#### Key Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Formula type strategy | Separate types per logic | Aligns with cslib, provides type-level separation |
| Primitive connectives (new types) | bot, imp, box | Aligns with BimodalLogic, Foundation, standard proof theory |
| Proof system abstraction | cslib's `InferenceSystem` with tags | Already in place, more general than alternatives |
| Semantic framework | Separate per logic | Frameworks are fundamentally incompatible |
| Metalogic decomposition | Monolithic per logic | Interaction axioms prevent cross-logic factoring |
| Existing Modal module | Unchanged | Different design philosophy, works for its purpose |
| Composition mechanism | Embeddings + conservative extension | BimodalLogic already demonstrates this pattern |

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (Implementation Patterns) | completed | high |
| B | Alternatives (Prior Art) | completed | medium-high |
| C | Critic (Gaps & Blind Spots) | completed | high |
| D | Horizons (Strategic Direction) | completed | high |

## References

- FormalizedFormalLogic/Foundation — [GitHub](https://github.com/FormalizedFormalLogic/Foundation) — State-of-the-art composable logic in Lean 4
- Obendrauf et al. (2024) — *Lean Formalization of Completeness Proof for Coalition Logic with Common Knowledge*. ITP 2024, LIPIcs vol. 309
- Oswald, J. (2025) — *A Simple Typeclass for Logic Formulae in Lean4* — Blog post on typeclass-based logic formula design
- Oswald, J. (2025) — *A Meditation on Extending Inductive Types in Lean4* — Analysis of Lean 4's inability to extend inductives
- van Doorn et al. (2024) — *Use and Abuse of Instance Parameters in the Lean Mathematical Library*. J. Automated Reasoning
- Mathlib Community — *Algebraic Hierarchy Design* documentation
- Benzmüller, C. (2025) — *Faithful Logic Embeddings in HOL — Deep and Shallow*
- Swierstra, W. (2008) — *Data Types à la Carte*. JFP 18(4) — Compositional syntax via functors (not directly viable in Lean 4)
- Funcao — *LML: A deep-embedding formalization of modal logic in Coq* — [GitHub](https://github.com/funcao/LML)
