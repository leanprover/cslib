# Teammate B Findings: Alternative Approaches & Prior Art

**Task**: 28 — Structure metalogic across Propositional, Modal, Temporal, and Bimodal systems
**Angle**: Alternative patterns, prior art, external libraries
**Date**: 2026-06-09

## Key Findings

### 1. FormalizedFormalLogic/Foundation — The Most Relevant Prior Art

The [Foundation](https://github.com/FormalizedFormalLogic/Foundation) project is the closest existing Lean 4 library to what CSLib is building. It formalizes propositional, first-order, modal, and provability logic with shared infrastructure.

**Architecture pattern**: Foundation uses a shared `Logic/` layer with:
- `LogicSymbol.lean` — A `LogicalConnective` typeclass providing `Top`, `Bot`, `Tilde`, `Arrow`, `Wedge`, `Vee` for any formula type, plus a homomorphism framework (`LogicalConnective.HomClass`, `α →ˡᶜ β`) for structure-preserving maps between formula types
- `Entailment.lean` — A generic `Entailment` typeclass: `class Entailment (S : Type*) (F : outParam Type*) where Prf : S → F → Type*`, with `Sound`/`Complete` typeclasses parameterized over both a proof system `S` and a semantic model `M`
- `Embedding.lean` — Generic logic embedding mechanisms
- `LindenbaumAlgebra.lean` — Shared Lindenbaum algebra construction
- `Decidability.lean` — Generic decidability infrastructure

**Metalogic separation**: Each logic (Propositional, Modal, etc.) has its own `Hilbert/`, `Kripke/`, `Maximal/` (MCS theory), and semantic modules, but they share the Entailment and LogicSymbol foundations.

**Key insight**: Foundation keeps `Sound` and `Complete` as **generic typeclasses** parameterized over proof system and model, then provides **per-logic instances**. This is directly applicable to CSLib.

### 2. LeanLTL — Unifying Framework for Temporal Logics

[LeanLTL](https://github.com/UCSCFormalMethods/LeanLTL) (ITP 2025) unifies LTL, LTLf, LTLMT, and LTLfMT by **parameterizing over trace types** (finite vs infinite). The key pattern:

- Define a common formula syntax
- Parameterize semantics over `Trace` abstraction layers (`Trace`, `TraceFun`, `TraceSet`)
- Provide logic-specific embeddings that map standard LTL/LTLf into the unified framework

**Relevance to CSLib**: The "parameterize semantics over model type, unify syntax via typeclasses" pattern directly maps to CSLib's challenge. Propositional, Modal, Temporal logics share syntactic typeclasses (`HasBot`, `HasImp`, etc.) but have different semantic model types.

### 3. James Oswald's `Language` Typeclass

[A Simple Typeclass for Logic Formulae](https://jamesoswald.dev/posts/a-type-class-for-logic/) proposes a single universal `Language` typeclass indexing connectives by arity, with `ParseTree` for structural induction. This covers propositional, first-order, modal (K, KD45), description logics, and relevance logic.

**Assessment**: Too coarse for CSLib's needs. The arity-indexed approach loses the fine-grained `HasBot`/`HasImp`/`HasBox` decomposition that CSLib already uses effectively. The Foundation approach (separate connective typeclasses + bundled classes) is better for a multi-logic hierarchy.

### 4. Mathlib Algebraic Hierarchy Patterns

Mathlib's algebraic hierarchy provides battle-tested patterns for CSLib's challenge:

**Pattern A — Forgetful Inheritance**: `CommRing extends Ring extends Group extends Monoid`. Each level adds axioms; lower-level theorems apply automatically. CSLib already does this: `ModalHilbert extends PropositionalHilbert`, `BimodalTMHilbert extends ModalS5Hilbert`.

**Pattern B — Instance Transfer**: Mathlib propagates properties via injective/surjective function patterns. For CSLib: if `embed : Modal.Formula → Bimodal.Formula` is injective and structure-preserving, then metalogic results can transfer along the embedding.

**Pattern C — Bundled vs Unbundled**: Mathlib uses unbundled typeclasses for the main hierarchy to avoid exponential blowup. CSLib's current `HasAxiom*` approach is correctly unbundled. The bundled `PropositionalHilbert`, `ModalHilbert` etc. are lightweight wrappers (contain only proof obligations, no data), which is fine.

**Pattern D — "Only add a class when there's real math to do"**: Don't create `HasSoundness`, `HasCompleteness`, etc. as typeclasses unless they actually enable shared proofs. Foundation does this right: `Sound` and `Complete` are typeclasses because they enable generic reasoning. But `HasDeductionTheorem` may not be useful as a typeclass since the proof depends on the specific derivation tree.

## Alternative Approaches

### Approach 1: "Foundation-Style" — Shared Metalogic Kernel

Modeled on FormalizedFormalLogic/Foundation:

```
Cslib/Foundations/Logic/
  Metalogic/
    Consistency.lean       -- Generic Consistent, MaximalConsistent defs
    Lindenbaum.lean        -- Generic Lindenbaum lemma (Zorn application)
    Soundness.lean         -- class Sound (S : Type*) (M : Type*) [...]
    Completeness.lean      -- class Complete (S : Type*) (M : Type*) [...]
    DeductionTheorem.lean  -- class HasDeductionTheorem (S : Type*) [...]

Cslib/Logics/Modal/
  Metalogic/
    MCS.lean              -- Modal-specific MCS (witnessed by box/diamond)
    Soundness.lean        -- instance : Sound Modal.HilbertK KripkeModel
    Completeness.lean     -- instance : Complete Modal.HilbertK KripkeModel

Cslib/Logics/Temporal/
  Metalogic/
    MCS.lean              -- Temporal-specific MCS (witnessed by until/since)
    Soundness.lean        -- instance : Sound Temporal.HilbertBX LinearModel

Cslib/Logics/Bimodal/
  Metalogic/              -- (existing tasks 6-11, ported as-is)
```

**What's shared**: Consistency/MCS definitions, Lindenbaum's lemma skeleton, `Sound`/`Complete` typeclass interface.
**What's per-logic**: DeductionTheorem (structural induction on different derivation trees), witness conditions (modal witnesses vs temporal witnesses), canonical model construction, frame conditions.

### Approach 2: "Lifting Along Embeddings" — Metalogic Transfer

Use the existing embedding functions (`ModalEmbedding`, `TemporalEmbedding`, `PropositionalEmbedding` already in `Cslib/Logics/Bimodal/Embedding/`) to **lift metalogic results**:

```
-- If Modal soundness holds and embedding preserves derivability:
theorem bimodal_modal_fragment_sound :
  ∀ φ : Modal.Formula, (Bimodal.HilbertTM ⊢ φ.toBimodal) → (KripkeValid φ)

-- Conservative extension gives:
-- If φ is in the modal fragment, Bimodal soundness implies Modal soundness
```

This is what the Separation Theorem (task 10) already does — it characterizes which bimodal formulas reduce to modal/temporal fragments. The lifting approach could be formalized as:

```lean
class MetalogicLift (embed : F₁ → F₂) (S₁ S₂ : Type*) where
  lift_derivability : S₂ ⊢ (embed φ) → S₁ ⊢ φ
  reflect_derivability : S₁ ⊢ φ → S₂ ⊢ (embed φ)
```

**Tradeoff**: Elegant but requires the embeddings and conservative extension results to be in place first (tasks 10-11). Useful for later work, not for structuring the initial metalogic porting.

### Approach 3: "Minimal Shared + Per-Logic Replication" — Pragmatic Port

Don't abstract at all. Port metalogic per-logic with copy-paste-adapt:

```
Cslib/Logics/Modal/Metalogic/     -- Standalone modal metalogic
Cslib/Logics/Temporal/Metalogic/  -- Standalone temporal metalogic
Cslib/Logics/Bimodal/Metalogic/   -- Bimodal metalogic (from BimodalLogic)
```

The propositional level stays in `Foundations/Logic/` as theorems (no metalogic beyond what's already there).

**Tradeoff**: Fast to implement, zero abstraction overhead, easy to review. But duplicates MCS theory and Lindenbaum lemma across logics. This is acceptable if the amount of duplication is small (100-200 lines per logic for MCS basics).

## Evidence/Examples

### What Can Actually Be Shared

After examining both codebases, here's a concrete breakdown:

| Metalogic Component | Generic Potential | Evidence |
|---|---|---|
| Consistency definition | **High** — `¬(Γ ⊢ ⊥)` is universal | Foundation uses generic `Inconsistent` class |
| Lindenbaum's lemma | **Medium** — Zorn application is generic, but witness conditions differ per logic | Foundation has generic `LindenbaumAlgebra.lean` |
| MCS boolean properties | **Medium** — deductive closure, negation completeness are generic given deduction theorem | Foundation's `MaximalConsistentSet.lean` is in Modal/ (not shared) |
| Deduction theorem | **Low** — requires induction on logic-specific derivation tree constructors | Task 20 research explicitly found this is per-logic |
| Soundness proof | **Low** — inherently semantics-specific (Kripke vs task frames vs linear orders) | Foundation: separate proofs per logic |
| Completeness proof | **Low** — canonical model construction is entirely logic-specific | Foundation: separate proofs per logic |
| Decidability/Tableau | **None** — inherently logic-specific decision procedure | Even the tableau rules differ per logic |

### What Foundation Actually Shares vs Doesn't

Foundation shares: `LogicSymbol`, `Entailment`, `Embedding`, `LindenbaumAlgebra`, `Decidability`, `ForcingRelation`, `Semantics`, `Calculus`.

Foundation does NOT share: MCS theory (it's in `Modal/Maximal/`), soundness proofs, completeness proofs, deduction theorems, tableau methods. Each logic has its own.

### CSLib Already Has Good Architecture

The existing CSLib typeclass hierarchy (`HasBot`/`HasImp`/`HasBox`/`HasUntil`/`HasSince` → bundled classes → `PropositionalHilbert`/`ModalHilbert`/`BimodalTMHilbert`) is well-designed and closely parallels Foundation's approach. The propositional theorems are already generic over `[PropositionalHilbert S]`, meaning they automatically apply to modal, temporal, and bimodal systems.

## Tradeoffs Summary

| Approach | Abstraction Cost | Duplication | Import Complexity | Time to Implement |
|---|---|---|---|---|
| 1. Foundation-Style Kernel | Medium | Low | Medium (shared → per-logic) | 2-4 extra hours |
| 2. Embedding Lifting | High | None (ideal) | High (requires tasks 10-11 first) | Blocked on other tasks |
| 3. Minimal Pragmatic | Zero | Medium (~200 lines × 2-3 logics) | Low (each logic self-contained) | Fastest |

## Recommendations

1. **Adopt a lightweight version of Approach 1**: Add `Sound`/`Complete` typeclasses to `Foundations/Logic/` (Foundation pattern). Add a generic `Consistent` definition. Keep the Lindenbaum lemma per-logic for now (the witness conditions differ enough that a generic version adds more complexity than it saves).

2. **Don't create `HasDeductionTheorem` as a typeclass** — the proof is structural induction on different derivation trees, so a generic typeclass would just be a wrapper around the per-logic proof with no sharing benefit.

3. **Keep MCS theory per-logic** — the 150-200 lines of shared MCS definitions (consistency, maximal consistency) can go in Foundations, but the actual Lindenbaum lemma and MCS properties should stay per-logic since witness conditions differ.

4. **Use Approach 2 (Lifting) as a future layer** after tasks 10-11 complete. The embedding infrastructure already exists; once conservative extension is proven, metalogic transfer theorems become natural corollaries.

## Confidence Level

**High** for the architectural analysis. The Foundation project provides strong evidence that the "shared connective typeclasses + per-logic metalogic" pattern works in practice. CSLib is already on the right track.

**Medium** for the specific recommendations on what to share vs replicate — this depends on how much the user values zero-duplication vs simplicity.
