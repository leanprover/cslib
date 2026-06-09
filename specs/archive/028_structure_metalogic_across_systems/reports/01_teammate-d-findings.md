# Teammate D (Horizons): Strategic Metalogic Structure

**Task**: 28 — Structure metalogic across Propositional, Modal, Temporal, and Bimodal systems
**Date**: 2026-06-09
**Angle**: Long-term alignment, extensibility, and strategic direction

## Key Findings (Strategic Insights)

### 1. The Existing Roadmap Already Enforces a Sound Layering — But Metalogic Is Only Planned for Bimodal

The ROADMAP and task list have an excellent foundations-first invariant (`Foundations → Modal/Temporal → Bimodal`), but metalogic (soundness, completeness, deduction theorem, decidability, MCS theory) is currently planned **only** for Bimodal (tasks 6–11). Tasks 21 and 22 stop at proof systems + derived theorems — no standalone modal or temporal metalogic is scoped.

This is a significant gap. The Temporal/Semantics task (23) defines temporal models but never proves soundness or completeness for temporal logic independently. Similarly, Modal has Kripke semantics in `Modal/Basic.lean` (Denotation) but no task to prove soundness/completeness for modal K, S4, or S5 as standalone results.

**Strategic implication**: CSLib will have bimodal metalogic but not standalone modal or temporal metalogic. This undermines the "each level is a standalone, importable library" principle stated in ROADMAP.md.

### 2. The Typeclass Architecture Creates a Natural "Metalogic Interface" Opportunity

The `ProofSystem.lean` typeclass hierarchy (`PropositionalHilbert → ModalHilbert → ModalS5Hilbert`, `PropositionalHilbert → TemporalBXHilbert`) suggests a parallel metalogic typeclass hierarchy could work:

```
class HasSoundness (S : Type*) (M : Type*) [ProofSystem S F] [Semantics M F] where
  soundness : DerivableIn S φ → Valid M φ

class HasCompleteness (S : Type*) (M : Type*) [ProofSystem S F] [Semantics M F] where
  completeness : Valid M φ → DerivableIn S φ
```

But there's a fundamental obstacle: **the metalogic results require different data**. Modal soundness needs Kripke frames. Temporal soundness needs linear orders. Bimodal soundness needs task frames. Unlike proof-theoretic theorems (which are purely syntactic and parametrized by typeclasses), metalogic results are deeply entangled with their semantic models.

### 3. Deduction Theorem Is Per-Logic by Necessity — But MCS Theory Has Shareable Structure

The research for task 20 already established that `DeductionTheorem` requires structural induction on concrete `DerivationTree`s and stays per-logic. This is correct and shouldn't change.

However, MCS theory (Maximal Consistent Sets) has generic components:
- The consistency definition `¬Nonempty (S⇓⊥)` is type-generic
- Lindenbaum's lemma (Zorn's lemma application) has a generic shape
- Deductive closure, negation completeness, and the implication property are generic

Currently these are all in `Bimodal/Metalogic/Core/`. A `Foundations/Logic/Metalogic/MCS.lean` with generic MCS definitions could be reused by Modal, Temporal, and Bimodal. The bimodal MCS module would then extend with bimodal-specific properties (modal saturation, temporal coherence, etc.).

### 4. The Embedding Hierarchy Is Well-Positioned for Metalogic Transfer

The existing embeddings (`PropositionalEmbedding`, `ModalEmbedding`, `TemporalEmbedding`) already prove commutativity (the embedding diamond commutes). They are structural (syntax-only) with `@[simp]` lemmas.

**Untapped potential**: Once soundness/completeness is proven at each level, the embeddings could transfer results upward:
- If `Modal.HilbertK ⊢ φ` and modal soundness holds, then `φ` is valid in all Kripke frames
- Since `ModalEmbedding` preserves structure, `φ.toBimodal` should be valid in task frames restricted to their modal fragment
- The Separation Theorem (task 10) already proves the converse: bimodal theorems in the modal fragment can be separated back to pure modal theorems

This suggests a **transfer pipeline**: prove soundness/completeness at each level independently, then connect via embedding-compatible lemmas. This is more modular and more useful to external consumers than proving everything only at the bimodal level.

### 5. CSLib Already Has Natural Deduction for Propositional Logic

`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (by Thomas Waring) provides sequent-style natural deduction with cut, weakening, and substitution. This is independent of the Hilbert system. It demonstrates that CSLib already supports non-Hilbert proof systems.

For metalogic structure, this means the framework should not assume Hilbert-style exclusively. A `Foundations/Logic/Metalogic/` directory should be agnostic to proof system type where possible.

## Strategic Alignment

### How Does This Serve CSLib's Goals?

1. **Community contribution**: If someone wants to add epistemic logic, they need:
   - A formula type (easy, follow Modal.Proposition pattern)
   - A proof system (follow ModalHilbert typeclass pattern)  
   - Theorems (import from Foundations/Logic/Theorems/)
   - **Metalogic (currently impossible without reimplementing from scratch)**
   
   A generic MCS framework in Foundations would let epistemic logic contributors focus on their specific models rather than rebuilding Lindenbaum's lemma.

2. **PR submission pipeline (task 12)**: The modular structure means PRs could be:
   - PR-Metalogic-Foundations: Generic MCS, consistency definitions (~300-500 lines, small)
   - PR-Modal-Metalogic: Modal soundness + completeness (~1000-2000 lines)
   - PR-Temporal-Metalogic: Temporal soundness + completeness (~1000-2000 lines)
   - PR-Bimodal-Metalogic: Existing tasks 6-11 (~30,000 lines)
   
   The first three are independently reviewable and useful, making the PR pipeline smoother.

3. **Import structure**: The metalogic should mirror the proof theory import structure:
   ```
   Foundations/Logic/Metalogic/  (generic: MCS, consistency)
        ↓                ↓
   Modal/Metalogic/   Temporal/Metalogic/   (standalone soundness/completeness)
                            ↓
                    Bimodal/Metalogic/       (tasks 6-11, unchanged scope)
   ```

### Alignment with Existing Task Structure

The current task structure needs **additions, not revisions** to the existing bimodal tasks (6-11). Those are correctly scoped as inherently bimodal. What's missing are:

- **Generic MCS foundations** (new task or addition to a Foundations task)
- **Modal metalogic** (soundness/completeness for S5, extending task 21)
- **Temporal metalogic** (soundness/completeness for BX on linear orders, extending task 23)

## Opportunities

### 1. Factor Generic MCS Into Foundations

Extract from BimodalLogic's `Metalogic/Core/`:
- `SetConsistent` (generic version, ~50 lines)
- `SetMaximalConsistent` (generic version, ~50 lines)
- `ConsistentSupersets` (generic, ~30 lines)
- `set_lindenbaum` (Lindenbaum's lemma via Zorn, ~200 lines of generic structure)
- Generic MCS properties: deductive closure, negation completeness, implication property (~150 lines)

**Estimated new work**: ~300-500 lines in `Foundations/Logic/Metalogic/MCS.lean`
**Benefit**: All four logics reuse this. Bimodal task 7 reduces in scope by ~500 lines.

### 2. Create Standalone Modal Soundness/Completeness

Modal K/S5 soundness and completeness are textbook results. The Kripke semantics already exists in `Modal/Basic.lean`. With a standalone modal DerivationTree (task 21), soundness should be provable directly.

This could be a new task or an extension of task 21.

### 3. Connect Temporal Semantics to Temporal Soundness

Task 23 already plans `Temporal.Model` on `LinearOrder` and `Temporal.Satisfies`. Adding temporal soundness as part of task 23 (or a follow-up) would make Temporal/ the first CSLib logic with a complete verified proof theory, per the ROADMAP milestone.

### 4. Embedding-Compatible Metalogic Transfer

Once standalone metalogic exists at each level, theorems like:
- "If φ is a modal validity, then φ.toBimodal is a bimodal validity"
- "If φ is a bimodal validity in the temporal fragment, then there exists ψ with φ = ψ.toBimodal and ψ is a temporal validity"

These transfer theorems connect the levels and are more valuable to external users than having metalogic only at the bimodal level.

## Creative Approaches

### 1. "Metalogic Kit" Pattern

Instead of monolithic metalogic per logic, provide a **metalogic kit** in Foundations:
- Generic consistency/MCS definitions
- A `SoundnessProof` structure template
- A `CompletenessProof` structure template
- Lindenbaum's lemma as a reusable tool

Each logic instantiates the kit with its own formula type, semantics, and proof system. This is analogous to how Mathlib provides algebraic structure building blocks.

### 2. Do Not Over-Abstract

The BimodalLogic repo's metalogic is tightly coupled to the bimodal `DerivationTree` with 42 axioms. Trying to abstract too aggressively (e.g., a single generic completeness proof) would be architecturally wrong — the proof strategies genuinely differ:
- Modal S5 completeness uses canonical Kripke models with universal accessibility
- Temporal BX completeness uses chronicle/chain constructions on linear orders
- Bimodal TM completeness uses the Burgess-Xu construction with task frames

The right abstraction level is: **share definitions and lemmas, not proofs**.

### 3. Prioritize Temporal Metalogic

The ROADMAP says temporal is the first logic that would have "a complete verified proof theory" in CSLib. Making this true by adding temporal soundness/completeness would be a strong demonstration of the modular architecture's value, and a compelling story for the Zulip discussion in task 12.

## Confidence Level

- **High confidence**: Generic MCS can and should be factored to Foundations
- **High confidence**: Standalone modal/temporal metalogic is missing and needed
- **Medium confidence**: The exact scope of generic MCS vs. per-logic MCS needs investigation
- **Medium confidence**: Embedding-compatible transfer theorems are feasible but need careful scoping
- **Low confidence**: The "metalogic kit" pattern — worth exploring but may be over-engineering
