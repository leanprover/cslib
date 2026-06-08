# Teammate B Findings: Alternative Patterns and Prior Art

**Task**: 14 — Design modular logic architecture for composable modal, temporal, and bimodal syntax and proof systems
**Date**: 2026-06-08
**Angle**: Alternative compositional patterns, prior art in other provers, and non-obvious design strategies

---

## Key Findings

### 1. Lean 4 Has No Native Inductive Type Extension

The most critical constraint for this design is that **Lean 4 has no mechanism for extending inductive types**. Unlike structures (where `extends` creates products), extending an inductive type would require a **sum** (coproduct) operation, which creates fundamental ambiguity for recursive constructors. When `PropFormula` has `imp : PropFormula → PropFormula → PropFormula`, should extending it to `ModalFormula` rebind those references to `ModalFormula` or leave them as `PropFormula`? Each choice yields different behavioral and proof-theoretic outcomes.

This means the "data types à la carte" (Swierstra 2008) approach — representing syntax as functorial fixed points of composable signature functors — is **not directly viable in Lean 4**. The pattern works well in Haskell (with flexible type-level programming) but Lean's universe-polymorphic inductive types don't support the required higher-kinded abstractions without significant encoding overhead.

**Implication**: Any modular architecture must work *around* monolithic inductive types, not try to compose them at the type level.

### 2. The Coalition Logic Paper (ITP 2024) Demonstrates the Most Relevant Pattern

Obendrauf et al. (ITP 2024) formalized Coalition Logic (CL) and its extension with Common Knowledge (CLC) in Lean 4, using **typeclasses to generalize over logic components**. Their key insight:

- Define a single formula type that includes all constructors
- Use **typeclasses** to abstract over which axioms/rules are available
- Prove metatheorems against typeclass interfaces, not concrete types
- Instantiate the same proofs for CL, CLK (CL + individual knowledge), and CLC

This is the closest prior art to our situation. The pattern is:
```
class HasBoxModality (F : Type) where
  box : F → F

class HasTemporalOps (F : Type) where  
  until : F → F → F
  since : F → F → F
```

Then proofs about `[HasBoxModality F]` apply to both pure modal and bimodal formulas.

### 3. Mathlib's Algebraic Hierarchy Provides the Gold Standard Pattern

Mathlib's approach to algebraic structures is directly applicable:

- **Extension through bundled inheritance**: `CommRing extends Ring`, incorporating ancestor fields
- **Morphism classes**: `RingHomClass` as a typeclass for structure-preserving maps
- **Avoid exponential explosion**: Only introduce new typeclasses when there's "real mathematics" to be done

The relevant Mathlib pattern for our case:

```
-- Mathlib style: AddGroup → AddCommGroup → Module → ...
-- Our analog: HasPropLogic → HasModalLogic → HasTemporalLogic → HasBimodalLogic
```

Where each level adds operators and axioms, and theorems proven at lower levels automatically apply at higher levels.

### 4. Three Viable Architecture Patterns

#### Pattern A: Typeclass-Stratified Monolithic Formula (Recommended)

Keep a single `Formula` type with all constructors, but use typeclasses to gate access:

```lean
inductive Formula (Atom : Type) where
  | atom : Atom → Formula Atom
  | bot : Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  | box : Formula Atom → Formula Atom           -- modal
  | untl : Formula Atom → Formula Atom → Formula Atom  -- temporal
  | snce : Formula Atom → Formula Atom → Formula Atom  -- temporal

class PropFormula (F : Type) where
  atom : Atom → F
  bot : F
  imp : F → F → F

class ModalFormula (F : Type) extends PropFormula F where
  box : F → F

class TemporalFormula (F : Type) extends PropFormula F where
  untl : F → F → F
  snce : F → F → F

class BimodalFormula (F : Type) extends ModalFormula F, TemporalFormula F
```

**Pros**: Matches Mathlib conventions. Proofs at `[ModalFormula F]` level are reusable. No encoding overhead.
**Cons**: The concrete `Formula` type still has all constructors visible; discipline is needed to avoid temporal constructors in pure modal proofs.

#### Pattern B: Parameterized Formula with Operator Tags

```lean
inductive Op where
  | prop | modal | temporal | bimodal

inductive Formula (ops : Set Op) (Atom : Type) where
  | atom : Atom → Formula ops Atom
  | bot : Formula ops Atom
  | imp : Formula ops Atom → Formula ops Atom → Formula ops Atom
  | box : (h : Op.modal ∈ ops) → Formula ops Atom → Formula ops Atom
  | untl : (h : Op.temporal ∈ ops) → Formula ops Atom → Formula ops Atom → Formula ops Atom
  | snce : (h : Op.temporal ∈ ops) → Formula ops Atom → Formula ops Atom → Formula ops Atom
```

**Pros**: Compile-time enforcement of operator availability. Cannot accidentally use temporal operators in pure modal context.
**Cons**: Proof terms carry evidence. Embedding functions between `Formula {prop, modal}` and `Formula {prop, modal, temporal}` require explicit coercion. Nonstandard pattern — fights Lean's grain.

#### Pattern C: Separate Types with Embedding Functions

Define independent types and explicit embeddings:

```lean
-- Pure modal
inductive ModalFormula (Atom : Type) where
  | atom | bot | imp | box

-- Pure temporal
inductive TemporalFormula (Atom : Type) where
  | atom | bot | imp | untl | snce

-- Combined
inductive BimodalFormula (Atom : Type) where
  | atom | bot | imp | box | untl | snce

def ModalFormula.embed : ModalFormula Atom → BimodalFormula Atom
def TemporalFormula.embed : TemporalFormula Atom → BimodalFormula Atom
```

**Pros**: Clean separation. Each module is self-contained. Matches the current cslib `Modal.Proposition` design.
**Cons**: Massive duplication. Every lemma about `imp` must be proved three times. Embedding functions create proof obligations. This is the **anti-Mathlib** pattern.

### 5. Deep vs Shallow Embedding Tradeoffs

The literature identifies a spectrum:

- **Deep embeddings** (what both cslib and BimodalLogic currently use): Inductive formula types with explicit syntax. Required for metatheorems (soundness, completeness, decidability). Cannot be avoided for the proof-theoretic results.

- **Shallow embeddings**: Represent formulas as `Prop`-valued functions. Excellent for *using* a logic to prove things, poor for *proving things about* the logic.

- **Hybrid approach** (recommended by recent work): Use deep embedding for metatheory, provide a shallow embedding for users who want to reason *within* the logic. Connect them via faithfulness theorems.

For cslib's purposes, **deep embedding is mandatory** since the goal includes soundness, completeness, and decidability. A shallow embedding could be a convenient user-facing layer but is secondary.

### 6. The cslib InferenceSystem Framework is a Key Asset

The existing `InferenceSystem` typeclass in cslib is well-designed for composability:

```lean
class InferenceSystem (S : Type*) (α : Type*) where
  derivation (a : α) : Sort v
```

This is **parametric over both the system tag `S` and the derivable type `α`**. This means:
- Modal proof system: `InferenceSystem ModalSystem (ModalJudgement World Atom)`
- Temporal proof system: `InferenceSystem TemporalSystem (TemporalJudgement T Atom)`
- Bimodal proof system: `InferenceSystem BimodalSystem (BimodalJudgement World T Atom)`

Each can be an independent instance. The `S` tag allows multiple proof systems to coexist for the same formula type.

### 7. Category-Theoretic Approaches: Theoretically Elegant, Practically Impractical

The idea of representing logics as categories (with formulas as objects and proofs as morphisms) and logic translations as functors is well-studied (Meseguer 1989, Goguen & Burstall's "Institutions"). However:

- Lean's category theory library (Mathlib.CategoryTheory) operates at a high abstraction level
- Encoding the morphism structure of proof systems as categorical morphisms adds significant overhead
- No existing Lean 4 project has successfully used this approach for practical logic formalization

**Verdict**: Not recommended for this project. The overhead far exceeds the benefit.

### 8. The BimodalLogic FrameConditions Module Shows a Viable Typeclass Pattern

The existing `FrameConditions/FrameClass.lean` in BimodalLogic already demonstrates a successful typeclass hierarchy for frame conditions:

```
LinearTemporalFrame
        |
   SerialFrame
      /    \
Dense       Discrete
```

This pattern can be **directly extended** to the logic/proof-system level:
- `HasModalAxioms` (K, T, 4, B, 5)
- `HasTemporalAxioms` (BX1-BX12)
- `HasInteractionAxioms` (MF, TF)
- `HasDensityAxioms` (DN, dense_indicator)
- `HasDiscretenessAxioms` (Prior-UZ/SZ, Z1)

The `FrameClass` enum and `Axiom.minFrameClass` pattern already implement a version of this gating.

---

## Alternative Approaches Analyzed

| Approach | Feasibility | Composability | Proof Reuse | Lean 4 Fit |
|----------|------------|---------------|-------------|-----------|
| Data types à la carte | Low | High | High | Poor (no HKT) |
| Typeclass-stratified monolith | High | Medium | High | Excellent |
| Parameterized formula (Op tags) | Medium | High | Medium | Fair |
| Separate types + embeddings | High | Low | Low | Good |
| Shallow embedding | Medium | High | Low for metatheory | Good |
| Category-theoretic | Low | Theoretical | N/A | Poor |
| Oswald Language typeclass | Medium | Medium | High | Fair |

---

## Evidence and Examples

### Mathlib Hierarchy Design (Gold Standard)

From `algebra.hierarchy_design` documentation:
> "We try to avoid exponential explosion by only introducing new algebraic typeclasses either when there is 'real mathematics' to be done with them, or when there is a meaningful gain in simplicity by factoring out a common substructure."

This directly applies: we should only separate modal and temporal logics as independent modules if there is real mathematics at each level (there is — pure modal logic has its own completeness theorem, pure temporal logic has its own).

### cslib Already Has Divergent Formula Designs

Current cslib has three different formula types:
- `Cslib.Logic.PL.Proposition`: atom, and, or, impl (4 constructors, no bot)
- `Cslib.Logic.Modal.Proposition`: atom, neg, and, diamond (4 constructors, no bot/impl)
- `Cslib.Logic.HML.Proposition`: true, false, and, or, diamond, box (6 constructors, label-indexed modalities)

These are **incompatible** — no shared interface, no embedding functions, completely independent proof developments. This is exactly the situation the modular architecture should address.

### BimodalLogic's Monolithic Approach Works but Doesn't Compose

BimodalLogic's `Formula` has 6 constructors (atom, bot, imp, box, untl, snce) with ~740 lines of derived operators and properties. The proof system has 42 axiom constructors organized into 8 layers. The `FrameClass` enum gates axiom availability.

This works well for the bimodal case but cannot be imported independently as "just modal logic" or "just temporal logic" — you always get everything.

---

## Recommendations

### Primary Recommendation: Typeclass-Stratified Architecture (Pattern A)

1. **Define a single `Formula` type** with all constructors (matching BimodalLogic's structure)
2. **Create typeclass hierarchy** for formula capabilities:
   - `HasPropConnectives` → `HasModalOp` → `HasTemporalOps` → `HasBimodalOps`
3. **Stratify proof systems** using `InferenceSystem` with different tags:
   - Tag per logic level (ModalSystem, TemporalSystem, BimodalSystem)
   - Lifting functions between levels
4. **Stratify semantics** using the existing cslib pattern:
   - `Model` for pure modal (accessibility relation)
   - `TemporalModel` for pure temporal (linear order)
   - `TaskModel` for bimodal (frame + histories)
5. **Port metalogic results** at the appropriate level of generality:
   - Modal soundness/completeness at `[HasModalOp F]` level
   - Temporal soundness/completeness at `[HasTemporalOps F]` level
   - Bimodal results compose the above with interaction axioms

### Secondary Recommendation: Unify cslib's Existing Formula Types

Before porting BimodalLogic, unify cslib's three existing `Proposition` types behind a common interface. This is necessary groundwork regardless of which composition pattern is chosen.

### Anti-Recommendation: Do NOT Use Separate Types with Embeddings

Pattern C (separate types) would create massive duplication and make the port from BimodalLogic extremely painful. Every lemma about implication, negation, conjunction, etc. would need to be proved independently for each formula type. This fights against Lean 4's strengths.

---

## Confidence Level

**Medium-High**

- **High confidence** on the core constraint: Lean 4 cannot extend inductive types, ruling out data-types-à-la-carte and naive composition approaches.
- **High confidence** on the typeclass-stratified approach: This is well-established in Mathlib and has been demonstrated for logics in the ITP 2024 coalition logic paper.
- **Medium confidence** on the specific typeclass hierarchy: The exact factoring (which typeclasses, which methods) needs experimentation. The interaction between modal and temporal operators may resist clean separation for some metatheoretic results.
- **Lower confidence** on proof reuse estimates: The BimodalLogic soundness proof heavily interleaves modal and temporal reasoning (e.g., the MF axiom `□φ → □Gφ` is inherently bimodal). Whether the interaction proofs can be cleanly factored is unclear without attempting it.

---

## References

- Obendrauf, K., Baanen, A., Koopmann, P., Stebletsova, V. (2024). *Lean Formalization of Completeness Proof for Coalition Logic with Common Knowledge*. ITP 2024, LIPIcs vol. 309. [Paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.28)
- Oswald, J. (2025). *A Simple Typeclass for Logic Formulae in Lean4*. [Blog](https://jamesoswald.dev/posts/a-type-class-for-logic/)
- Oswald, J. (2025). *A Meditation on Extending Inductive Types in Lean4*. [Blog](https://jamesoswald.dev/posts/meditation-extending-inductive-types/)
- van Doorn, F., Ebner, G., Lewis, R.Y. (2024). *Use and Abuse of Instance Parameters in the Lean Mathematical Library*. J. Automated Reasoning. [Paper](https://link.springer.com/article/10.1007/s10817-024-09712-7)
- Mathlib Community. *Algebraic Hierarchy Design*. [Docs](https://leanprover-community.github.io/mathlib_docs/algebra/hierarchy_design.html)
- Benzmüller, C. (2025). *Faithful Logic Embeddings in HOL — Deep and Shallow*. [Paper](https://arxiv.org/html/2502.19311v3)
- Swierstra, W. (2008). *Data Types à la Carte*. JFP 18(4).
- Funcao. *LML: A deep-embedding formalization of modal logic in Coq*. [GitHub](https://github.com/funcao/LML)
