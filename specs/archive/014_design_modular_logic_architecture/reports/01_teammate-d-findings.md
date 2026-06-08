# Teammate D Findings: Strategic Horizons

**Task**: 14 — Design modular logic architecture
**Angle**: Strategic direction, long-term alignment, and creative approaches
**Date**: 2026-06-08

## Key Findings (Strategic Insights)

### 1. cslib Is a Computer Science Foundations Library — Not Just a Logic Library

The project already spans:
- **Logics**: Modal, Propositional, HML, Linear Logic (CLL)
- **Languages**: CCS, Combinatory Logic
- **Computability**: URM machines, regular/omega-regular languages, Myhill-Nerode
- **Crypto**: Secret sharing (Shamir), perfect secrecy (OTP)
- **ML**: PAC learning, VC dimension
- **Probability**: PMFs

This breadth means the logic architecture must serve as infrastructure for other modules, not just be a self-contained logic formalization. The modal logic module already demonstrates this: `Cslib.Logics.HML` builds on LTS bisimulation, and `Cslib.Logics.Modal` provides the Modal Cube. Any composable logic framework must integrate with these existing modules without disrupting them.

### 2. cslib Already Has a Compositional Infrastructure — Use It

Three key abstractions already exist and should be the strategic foundation:

**InferenceSystem** (`Cslib.Foundations.Logic.InferenceSystem`):
- `class InferenceSystem (S : Type*) (α : Type*)` with `derivation (a : α) : Sort v`
- Already used by: Modal logic (`HasInferenceSystem (Judgement World Atom)`), CLL (`HasInferenceSystem (Sequent Atom)`), Propositional ND (`InferenceSystem T (Sequent)` and `InferenceSystem T (Proposition Atom)`)
- The `S` tag parameter is the natural composition point — different logics can use different tags

**LogicalEquivalence** (`Cslib.Foundations.Logic.LogicalEquivalence`):
- `class LogicalEquivalence (Proposition) (Judgement) (Valid)` requiring congruence + validity preservation
- Already instantiated for HML and CLL
- Any new logic should instantiate this

**Context/Congruence** (`Cslib.Foundations.Syntax`):
- `HasContext`, `HasHContext`, `Congruence` typeclasses
- Used by HML and CLL for propositional contexts

### 3. The Existing Logics Have Fundamentally Different Formula Types — And That's OK

| Logic | Formula Type | Parametric Over | Connectives |
|-------|-------------|-----------------|-------------|
| Propositional | `Proposition Atom` | `Atom` | atom, and, or, impl |
| Modal | `Proposition Atom` | `Atom` | atom, neg, and, diamond |
| HML | `Proposition Label` | `Label` (LTS actions) | true, false, and, or, diamond(μ), box(μ) |
| CLL | `Proposition Atom` | `Atom` | atom, atomDual, one, zero, top, bot, tensor, parr, oplus, with, bang, quest |
| BimodalLogic | `Formula` | hardcoded `Atom` | atom, bot, imp, box, untl, snce |

The lesson: there is no single shared formula type across these logics. Each logic defines its own inductive type with its own constructors. This is the right approach — trying to force a universal formula type would be over-engineering. The composition point is at the **semantics and proof system** level via `InferenceSystem`, not at the syntax level.

### 4. BimodalLogic Uses Until/Since — Not All-Future/All-Past — as Primitives

This is a crucial architectural insight. BimodalLogic's temporal operators are:
- `untl` (Until) and `snce` (Since) as primitives
- `all_future` (G) and `all_past` (H) derived as `¬F(¬φ)` where `F(φ) = U(φ, ⊤)`

This means a standalone "temporal logic" module for cslib should have Until/Since as the primitive operators (following Burgess 1982), not G/H. The BimodalLogic Formula type cannot simply be decomposed into "modal part" + "temporal part" at the constructor level because Until/Since are binary operators that don't appear in pure modal logic.

## Long-Term Architecture Vision

### The Three-Layer Pattern

Based on the existing codebase patterns, the architecture should follow three layers:

```
Layer 1: Syntax (each logic defines its own Formula inductive)
  ├── Cslib.Logics.Modal.Proposition     -- existing
  ├── Cslib.Logics.Temporal.Formula      -- new: atom, bot, imp, untl, snce
  └── Cslib.Logics.Bimodal.Formula       -- new: atom, bot, imp, box, untl, snce

Layer 2: Proof Systems (typeclassed via InferenceSystem)
  ├── Modal: semantic satisfaction         -- existing (HasInferenceSystem)
  ├── Temporal: Hilbert axioms            -- new (InferenceSystem tag)
  └── Bimodal: Hilbert axioms             -- ported from BimodalLogic

Layer 3: Metalogic (soundness, completeness, decidability)
  ├── Each logic proves its own results
  └── Conservative extension / embedding theorems connect them
```

### Future Logics This Architecture Could Support

| Logic | Formula Extension | Composition Pattern |
|-------|-------------------|---------------------|
| Epistemic (S5 per agent) | `know(i, φ)` per agent i | Multi-agent modal with indexed box operators |
| Deontic | `obligatory(φ)`, `permitted(φ)` | Additional modal operators on same frames |
| Dynamic | `[α]φ` where α is a program | Modal over program-labeled transitions (like HML) |
| CTL/CTL* | Path quantifiers + temporal | Branching-time variants of Until/Since |
| PDL | `[α]φ` with program constructors | Labeled modal + program composition |
| Temporal + Epistemic | Both operators | True bimodal composition |

The key insight: most of these are "modal logic + X" where X introduces new operators. The cslib pattern of separate formula types + shared InferenceSystem infrastructure handles this well.

## Alignment Analysis

### Alignment with Mathlib's Compositional Patterns

Mathlib handles algebraic composition through:
1. **Unbundled typeclasses**: `CommMonoid`, `Ring`, `Field` as independent typeclasses with `extends`
2. **Instance composition**: `Ring` extends `AddCommGroup` and `Monoid`
3. **Forgetful functors**: Every `Ring` is an `AddCommGroup` via coercion

For logic systems, the analogous pattern would be:
- **Typeclass for logic features**: `class HasBox (F : Type*) where box : F → F`
- **Typeclass for temporal features**: `class HasUntil (F : Type*) where untl : F → F → F`
- **Composition**: A bimodal formula type satisfies both

However, this is **NOT recommended** because:
- Formula types are defined by their constructors (inductives), not by operations
- The Mathlib algebraic pattern works because operations are functions; formula constructors are data
- Lean 4 doesn't support open/extensible inductives

**Instead, follow Mathlib's semantic composition pattern**: frame conditions as typeclasses (already done in BimodalLogic's `FrameConditions.FrameClass`).

### The HML Connection — Labeled Modalities

HML has `diamond (μ : Label) (φ)` — a labeled modality where μ is an LTS action. This is precisely the pattern for multi-modal logics: box operators indexed by agents, programs, or temporal directions.

The BimodalLogic's `box` (metaphysical necessity) and temporal operators (Until/Since) can be viewed as specific instances of a multi-labeled modality system. However, Until/Since are binary, not unary like HML's diamond — so they don't fit the labeled-diamond pattern directly.

**Strategic recommendation**: Don't try to unify HML, modal, and temporal under one labeled-modality framework. The formula types are genuinely different. Instead, share the semantic and proof-theoretic infrastructure (InferenceSystem, LogicalEquivalence, frame conditions as typeclasses).

## Creative Approaches

### 1. Formula Embeddings Rather Than Formula Composition

Instead of trying to compose formula types, define embeddings:

```lean
def Modal.Proposition.toTM : Modal.Proposition Atom → Bimodal.Formula
def Temporal.Formula.toTM : Temporal.Formula → Bimodal.Formula
```

Then prove that these embeddings preserve derivability:
```lean
theorem modal_embedding_sound : ⊢_Modal φ → ⊢_TM (φ.toTM)
theorem modal_embedding_complete : ⊢_TM (φ.toTM) → ⊢_Modal φ  -- conservative extension
```

This gives composability without sharing formula types. BimodalLogic already has `ConservativeExtension/` proving exactly this pattern.

### 2. Typeclass-Based Frame Conditions (Already in BimodalLogic)

BimodalLogic's `FrameConditions` module already demonstrates the right pattern:
```lean
class LinearTemporalFrame (T : Type*) ...
class SerialFrame (T : Type*) ...
class DenseTemporalFrame (T : Type*) ...
class DiscreteTemporalFrame (T : Type*) ...
```

This should be elevated to cslib's infrastructure, not just kept in BimodalLogic.

### 3. Lean 4 Macros for Boilerplate Reduction (NOT for Formula Generation)

Lean 4's macro system could help with:
- Generating notation (`scoped prefix`, `scoped infix`) for new logics
- Deriving `DecidableEq` and `Countable` instances
- Automating `InferenceSystem` instance creation

But it should NOT be used to generate formula types from specifications. Inductives need explicit definitions for Lean's type checker, and macro-generated types would be hard to debug and maintain.

### 4. The `InferenceSystem` Tag as Logic Identifier

Currently, `InferenceSystem.Default` is used for "the" canonical inference system. For multiple logics, use distinct tags:

```lean
opaque ModalLogic.Tag : Type := Empty
opaque TemporalLogic.Tag : Type := Empty
opaque BimodalLogic.Tag : Type := Empty
```

This lets `S⇓a` disambiguate which proof system is in scope, without changing the InferenceSystem infrastructure.

### 5. Shared Propositional Core via Formula Embedding

Both modal and bimodal logics have propositional fragments. Rather than sharing a formula type, define:
```lean
class HasPropositionalFragment (F : Type*) where
  atom : Atom → F
  bot : F
  imp : F → F → F
```

This typeclass would let automation (simp lemmas, tactics) work generically across logics without requiring a shared formula type.

## Recommendations

### Scope: Design for Bimodal First, But With Eyes Open

The task should NOT be rescoped to "design a general multi-modal framework." That would be over-engineering. The right approach:

1. **Design the Temporal and Bimodal modules** to work with cslib's existing infrastructure (InferenceSystem, LogicalEquivalence)
2. **Don't modify the existing Modal module** — it works well as-is for Kripke semantics
3. **Establish the embedding/conservative extension pattern** as the composition mechanism
4. **Keep formula types separate** — each logic gets its own inductive
5. **Share frame condition typeclasses** — elevate BimodalLogic's FrameClass pattern to cslib infrastructure

### Concrete Architecture Recommendation

```
Cslib/Logics/
├── Modal/           -- UNCHANGED (Proposition Atom, Kripke semantics)
│   ├── Basic.lean
│   ├── Cube.lean
│   └── Denotation.lean
├── Temporal/        -- NEW (standalone temporal logic)
│   ├── Formula.lean     -- atom, bot, imp, untl, snce
│   ├── ProofSystem.lean -- temporal axioms only (TK, T4, TT, TA, TL, Lin)
│   ├── Semantics.lean   -- linear order semantics
│   └── Metalogic/       -- temporal-specific soundness/completeness
├── Bimodal/         -- NEW (combined logic, ported from BimodalLogic)
│   ├── Formula.lean     -- atom, bot, imp, box, untl, snce (full TM formula)
│   ├── ProofSystem.lean -- all 21 axioms
│   ├── Semantics.lean   -- task frame semantics
│   ├── Metalogic/       -- soundness, completeness, decidability
│   ├── Embedding/       -- Modal → Bimodal, Temporal → Bimodal embeddings
│   └── FrameConditions/ -- elevated from BimodalLogic
├── HML/             -- UNCHANGED
├── Propositional/   -- UNCHANGED
└── LinearLogic/     -- UNCHANGED
```

### What NOT to Do

1. **Don't create a universal `Formula` type** parameterized by which operators to include
2. **Don't modify `Cslib.Logics.Modal.Proposition`** — it has a different design philosophy (neg, and, diamond as primitives) from BimodalLogic (bot, imp, box as primitives)
3. **Don't try to make BimodalLogic's proofs factor into "modal part" + "temporal part"** — the interaction axioms (MF, TF) and the soundness/completeness proofs inherently require the combined system
4. **Don't use Lean 4 metaprogramming for formula type generation** — the complexity cost outweighs the boilerplate savings
5. **Don't rush to generalize** — get one concrete bimodal port working, then extract patterns

## Confidence Level

**High** on the strategic recommendations. The codebase evidence is clear:
- cslib's existing infrastructure (InferenceSystem, LogicalEquivalence) is the right composition point
- Formula types should remain separate per logic
- Embeddings + conservative extension theorems are the right composition mechanism (BimodalLogic already uses this pattern)
- The three-layer architecture (syntax / proof system / metalogic) with shared typeclasses is well-established

**Medium** on specific implementation details (exact file organization, whether FrameConditions should live in `Cslib.Foundations` or `Cslib.Logics`).

**Low** on metaprogramming approaches — these need experimentation to validate and have high risk of adding complexity without proportional benefit.
