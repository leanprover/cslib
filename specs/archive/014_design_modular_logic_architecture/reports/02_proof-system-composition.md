# Research Report: Proof System Composition Across a Four-Level Logic Hierarchy

**Task**: 14 — Design modular logic architecture
**Date**: 2026-06-08
**Focus**: How to define composable Hilbert-style proof systems (axioms, derivation trees, inference rules) across Propositional → Modal → Temporal → Bimodal in Lean 4

## Summary

This report investigates how to compose proof systems across four logic levels, each with its own formula type. The key finding is that Foundation's approach — **axioms as polymorphic typeclass methods on the proof system tag, not on the formula type** — is the right pattern for cslib. Derivation trees should remain monolithic per logic (not composed from sub-derivation trees), with composition achieved via embedding functions and lifting theorems. The cslib `InferenceSystem` framework maps cleanly to Foundation's `Entailment`.

---

## Question 1: Axiom Composition

**Recommendation: Polymorphic axiom definitions + typeclass-gated availability on the proof system tag.**

### The Foundation Pattern

Foundation defines axioms in two layers:

**Layer 1 — Axiom formulas as polymorphic `abbrev`s** (defined once, parameterized over any `F` with the right connectives):
```lean
namespace Cslib.Logic.Axioms
variable {F : Type*} [HasBot F] [HasImp F]

protected abbrev ImplyK (φ ψ : F) := φ.imp (ψ.imp φ)
protected abbrev ImplyS (φ ψ χ : F) := (φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))
protected abbrev EFQ (φ : F) := HasBot.bot.imp φ

-- Modal axioms (require HasBox)
variable [HasBox F]
protected abbrev AxiomK (φ ψ : F) := (φ.imp ψ).box.imp (φ.box.imp ψ.box)
protected abbrev AxiomT (φ : F) := φ.box.imp φ
protected abbrev Axiom4 (φ : F) := φ.box.imp φ.box.box
protected abbrev AxiomB (φ : F) := φ.imp φ.diamond.box

-- Temporal axioms (require HasUntil, HasSince)
variable [HasUntil F] [HasSince F]
protected abbrev SerialFuture : F := top.imp (some_future top)
protected abbrev ConnectFuture (φ : F) := φ.imp (some_past φ |>.all_future)
-- etc.
end Cslib.Logic.Axioms
```

**Layer 2 — HasAxiom typeclasses on the proof system tag** (stating that a particular system proves the axiom):
```lean
class HasAxiomImplyK (𝓢 : S) where
  implyK {φ ψ : F} : 𝓢 ⊢! Axioms.ImplyK φ ψ

class HasAxiomEFQ (𝓢 : S) where
  efq {φ : F} : 𝓢 ⊢! Axioms.EFQ φ

class HasAxiomK (𝓢 : S) where
  K {φ ψ : F} : 𝓢 ⊢! Axioms.AxiomK φ ψ

class HasAxiomT (𝓢 : S) where
  T {φ : F} : 𝓢 ⊢! Axioms.AxiomT φ
```

**Layer 3 — Bundled proof system classes** via `extends`:
```lean
class Minimal (𝓢 : S) extends
  ModusPonens 𝓢, HasAxiomImplyK 𝓢, HasAxiomImplyS 𝓢,
  HasAxiomAndElim 𝓢, HasAxiomAndInst 𝓢, HasAxiomOrInst 𝓢, HasAxiomOrElim 𝓢

class Classical (𝓢 : S) extends Minimal 𝓢, HasAxiomDNE 𝓢

class ModalK (𝓢 : S) extends Classical 𝓢, Necessitation 𝓢, HasAxiomK 𝓢
class ModalS5 (𝓢 : S) extends ModalK 𝓢, HasAxiomT 𝓢, HasAxiom4 𝓢, HasAxiomB 𝓢
```

### Why NOT separate Axiom inductives per level

BimodalLogic currently uses a single `Axiom : Formula → Type` inductive with 42 constructors. The alternative of having `PropAxiom`, `ModalAxiom`, `TemporalAxiom`, `BimodalAxiom` as separate inductives has severe downsides:

1. **Pattern matching becomes cumbersome** — the `BimodalAxiom` type would need to include copies of all sub-axioms or sum-type injections
2. **minFrameClass would need to work across sum types**
3. **Every theorem about axioms needs cases for each injection**

The polymorphic-axiom + typeclass approach avoids all this: axioms are just formulas, and the typeclass hierarchy controls which axioms a particular system proves.

### Why NOT a single Axiom inductive with guards

BimodalLogic's `minFrameClass` pattern works well *within* a single logic, but doesn't extend well *across* logics with different formula types. The typeclass approach is more compositional.

### Recommended Approach for cslib

Keep BimodalLogic's `Axiom` inductive for the bimodal system (it's battle-tested with 42 constructors and the FrameClass parameterization), but **additionally** define polymorphic axiom formulas and HasAxiom typeclasses. The concrete `Axiom` inductive provides the axiom instances:

```lean
-- The existing BimodalLogic Axiom inductive stays for the concrete bimodal system
-- But we also provide typeclass instances:
instance : HasAxiomImplyK Bimodal.HilbertTM where
  implyK := ⟨DerivationTree.axiom _ _ (Axiom.prop_k _ _ _) trivial⟩

instance : HasAxiomT Bimodal.HilbertTM where
  T := ⟨DerivationTree.axiom _ _ (Axiom.modal_t _) trivial⟩
```

This way, theorems proved generically about `[HasAxiomT 𝓢]` apply to the concrete bimodal system automatically.

---

## Question 2: DerivationTree Composition

**Recommendation: Separate DerivationTree inductives per logic. Do NOT try to compose derivation trees by injecting one into another.**

### Why separate derivation trees

Each logic level has different inference rules:

| Level | Rules |
|-------|-------|
| Propositional | axiom, assumption, modus_ponens, weakening |
| Modal | + necessitation |
| Temporal | + temporal_necessitation, temporal_duality |
| Bimodal | all of the above |

Trying to build `BimodalDerivation` by composing `PropDerivation` + `ModalDerivation` + `TemporalDerivation` doesn't work because:
1. **The formula types differ** — `PropDerivation` is over `Propositional.Formula`, but necessitation produces `box φ` which doesn't exist in `Propositional.Formula`
2. **Necessitation rules constrain the context to be empty** — this constraint needs to be enforced in the inductive itself
3. **The Axiom type is specific to each logic** — `BimodalDerivation` needs `Bimodal.Axiom`, not a union of sub-axiom types

### Concrete structure

```lean
-- Each logic has its own derivation tree
inductive Propositional.Derivation : PropContext → PropFormula → Type where
  | axiom : PropAxiom φ → Derivation Γ φ
  | assumption : φ ∈ Γ → Derivation Γ φ
  | modus_ponens : Derivation Γ (φ.imp ψ) → Derivation Γ φ → Derivation Γ ψ
  | weakening : Derivation Γ φ → Γ ⊆ Δ → Derivation Δ φ

inductive Modal.Derivation : ModalContext → ModalFormula → Type where
  | axiom : ModalAxiom φ → Derivation Γ φ
  | assumption : φ ∈ Γ → Derivation Γ φ
  | modus_ponens : Derivation Γ (φ.imp ψ) → Derivation Γ φ → Derivation Γ ψ
  | necessitation : Derivation [] φ → Derivation [] (φ.box)
  | weakening : Derivation Γ φ → Γ ⊆ Δ → Derivation Δ φ

-- Bimodal.DerivationTree stays essentially as-is from BimodalLogic
-- (with FrameClass parameterization)
```

### Composition via lifting, not injection

The connection between levels is via lifting theorems (see Question 8), not by building derivation trees from sub-trees.

---

## Question 3: InferenceSystem Integration

**Recommendation: Map `InferenceSystem` to Foundation's `Entailment` pattern, using logic-specific tag types.**

### cslib's InferenceSystem vs Foundation's Entailment

| Feature | cslib `InferenceSystem` | Foundation `Entailment` |
|---------|------------------------|------------------------|
| Tag type | `S : Type*` | `S : Type*` |
| Formula type | `α : Type*` | `F : outParam Type*` |
| Derivation | `derivation (a : α) : Sort v` | `Prf : S → F → Type*` |
| Derivability | `DerivableIn S a := Nonempty (S⇓a)` | `Provable 𝓢 φ := Nonempty (𝓢 ⊢! φ)` |

These are essentially isomorphic. The key difference: Foundation uses `outParam` for `F`, which enables better type inference. cslib's version is already suitable.

### Tag types for each logic

```lean
-- Tag types (opaque to prevent accidental unification)
opaque Propositional.HilbertCl : Type := Empty  -- Classical propositional logic
opaque Modal.HilbertK : Type := Empty           -- Modal logic K
opaque Modal.HilbertS5 : Type := Empty          -- Modal logic S5
opaque Temporal.HilbertBX : Type := Empty       -- BX temporal logic
opaque Bimodal.HilbertTM : Type := Empty        -- TM bimodal logic

-- Each tag gets InferenceSystem instances
-- For Hilbert-style derivation (Type-valued):
instance : InferenceSystem Bimodal.HilbertTM (BimodalJudgement) where
  derivation j := DerivationTree .Base j.context j.formula

-- For semantic derivation (Prop-valued, existing pattern):
instance : HasInferenceSystem (Modal.Judgement World Atom) where
  derivation j := Satisfies j.m j.w j.φ
```

### Disambiguating S⇓a

The `S` parameter selects the proof system:
```lean
-- Bimodal Hilbert derivation
example : Bimodal.HilbertTM⇓([] ⊢ φ.box.imp φ)

-- Modal semantic derivation (default tag)
example : ⇓Modal[m,w ⊨ □φ → φ]
```

Both can coexist because they use different tag types.

---

## Question 4: FrameClass Parameterization

**Recommendation: FrameClass is specific to the bimodal and temporal levels. Propositional and basic modal logic don't need it.**

### Analysis

BimodalLogic's FrameClass pattern (Base/Dense/Discrete) with `minFrameClass` gating is specific to the temporal dimension — it controls which temporal frame properties (dense ordering, discrete ordering) the axioms assume.

- **Propositional logic**: No frame class needed (all axioms are unconditionally valid)
- **Modal logic**: Frame conditions are expressed via typeclasses on the model (`Std.Refl`, `IsTrans`, etc.), not via a FrameClass enum. cslib already does this correctly.
- **Temporal logic**: Could use a simpler FrameClass (just Base/Dense/Discrete) or go without it if only one frame class is needed
- **Bimodal logic**: The full FrameClass parameterization is essential and should be preserved from BimodalLogic

The FrameClass pattern and the typeclass-based axiom pattern serve different purposes:
- **FrameClass** gates axiom *availability* within a single proof system
- **HasAxiom typeclasses** gate axiom *existence* across different proof systems

Both are needed. They compose naturally: a `[HasAxiomT 𝓢]` instance can be provided for any FrameClass, while density-specific instances require `[DenseFrame T]`.

---

## Question 5: Necessitation Rules and Composition

**Recommendation: Necessitation rules are logic-level specific. Lifting preserves the empty-context constraint.**

### The constraint

Both modal necessitation (`⊢ φ → ⊢ □φ`) and temporal necessitation (`⊢ φ → ⊢ Gφ`) only apply to theorems (empty context). This is baked into the DerivationTree constructor:

```lean
| necessitation (φ : Formula) (d : DerivationTree fc [] φ) : DerivationTree fc [] (Formula.box φ)
```

### Lifting interaction

When lifting a propositional derivation into a modal derivation, necessitation works correctly because:
1. The propositional derivation has an empty context: `PropDerivation [] φ`
2. The lifting function preserves the empty context: `liftPropToModal : PropDerivation [] φ → ModalDerivation [] (embed φ)`
3. Now necessitation can be applied: `ModalDerivation.necessitation (liftPropToModal d)`

This is safe because the structural constraint (empty context) is enforced by the inductive type, not by the formula type.

### Foundation's approach

Foundation uses `Necessitation` as a typeclass on the proof system tag:
```lean
class Necessitation (𝓢 : S) where
  nec {φ : F} : 𝓢 ⊢! φ → 𝓢 ⊢! □φ
```

This works with the `Entailment.Prf` (which is like `InferenceSystem.derivation`) to give `nec : 𝓢 ⊢! φ → 𝓢 ⊢! □φ`. The empty-context requirement is implicit: `𝓢 ⊢! φ` means "φ is a theorem of system 𝓢" (provable from the axioms alone, no assumptions).

For cslib, the recommendation is to use Foundation's approach for theorems proved at the typeclass level, and BimodalLogic's explicit `DerivationTree` approach for constructive proofs that need the tree structure.

---

## Question 6: The Interaction Axiom Problem

**Recommendation: Interaction axioms live exclusively in the bimodal level. No "interaction layer" pattern is needed.**

### Analysis

MF (`□φ → □(Gφ)`) involves both `box` (from `HasBox`) and `all_future` (derived from `HasUntil`). It cannot be stated over `ModalFormula` (no `untl`) or `TemporalFormula` (no `box`). It can only be stated over `BimodalFormula` (which has both).

### Design

```lean
-- Can be defined polymorphically IF the formula type has both connectives:
def Axioms.ModalFuture [HasBox F] [HasUntil F] (φ : F) : F :=
  φ.box.imp (all_future φ |>.box)

-- But it should ONLY appear as an axiom of the bimodal system:
class HasAxiomMF (𝓢 : S) where
  MF {φ : F} : 𝓢 ⊢! Axioms.ModalFuture φ
```

There's no need for a separate "interaction layer" — the bimodal proof system class simply extends both modal and temporal:

```lean
class BimodalHilbert (𝓢 : S) extends
  ModalS5 𝓢,           -- Modal axioms + necessitation
  TemporalBX 𝓢,        -- Temporal axioms + temporal necessitation + duality
  HasAxiomMF 𝓢         -- Interaction axiom
```

The interaction axiom is just another axiom in the bimodal system's `extends` chain.

---

## Question 7: Derivable/Provable Predicates

**Recommendation: Align BimodalLogic's `Derivable` with cslib's `InferenceSystem.DerivableIn`.**

### Current state

| Concept | BimodalLogic | cslib InferenceSystem | Foundation |
|---------|-------------|----------------------|------------|
| Constructive proof | `DerivationTree fc Γ φ : Type` | `S⇓a : Sort v` | `𝓢 ⊢! φ : Type*` |
| Existence | `Derivable fc Γ φ : Prop` | `DerivableIn S a : Prop` | `𝓢 ⊢ φ : Prop` |
| Notation | `Γ ⊢[fc] φ` / `Γ |-![fc] φ` | `S⇓a` | `𝓢 ⊢! φ` / `𝓢 ⊢ φ` |

### Alignment

The relationship is direct:
- `InferenceSystem.derivation` ↔ `DerivationTree` (constructive witness)
- `InferenceSystem.DerivableIn` ↔ `Derivable` (existence, via `Nonempty`)

For the composable architecture:

```lean
-- Judgement type bundles context + formula for each logic
structure Bimodal.Judgement where
  fc : FrameClass
  ctx : Context
  formula : Formula

-- InferenceSystem instance maps to DerivationTree
instance : InferenceSystem Bimodal.HilbertTM Bimodal.Judgement where
  derivation j := DerivationTree j.fc j.ctx j.formula

-- Then S⇓a gives DerivationTree, and DerivableIn gives Derivable
-- Both existing notations (S⇓a and Γ ⊢[fc] φ) can coexist
```

---

## Question 8: Proof Lifting Theorems

**Recommendation: Define structural embedding functions on derivation trees + prove conservative extension at the Derivable (Prop) level.**

### The embedding chain

```
Propositional → Modal → Bimodal
                         ↑
Propositional → Temporal → Bimodal
```

### Lifting functions (Type-valued, structural recursion)

```lean
-- Propositional → Modal
def liftPropToModal : PropDerivation Γ φ → ModalDerivation (Γ.map embed) (embed φ)
  | .axiom h => .axiom (embedPropAxiom h)
  | .assumption h => .assumption (mem_map_embed h)
  | .modus_ponens d₁ d₂ => .modus_ponens (liftPropToModal d₁) (liftPropToModal d₂)
  | .weakening d h => .weakening (liftPropToModal d) (map_subset_embed h)

-- Modal → Bimodal
def liftModalToBimodal : ModalDerivation Γ φ → BimodalDerivation fc (Γ.map embed) (embed φ)
  | .axiom h => .axiom _ _ (embedModalAxiom h) (FrameClass.base_le fc)
  | .assumption h => .assumption _ _ (mem_map_embed h)
  | .modus_ponens d₁ d₂ => .modus_ponens _ _ _ (liftModalToBimodal d₁) (liftModalToBimodal d₂)
  | .necessitation d => .necessitation _ (liftModalToBimodal d)
  | .weakening d h => .weakening _ _ _ (liftModalToBimodal d) (map_subset_embed h)

-- Temporal → Bimodal (analogous)
-- Propositional → Bimodal (via transitivity)
```

### Conservative extension (Prop-valued)

```lean
-- Soundness of embedding (always holds)
theorem modal_embedding_sound :
    ModalDerivable Γ φ → BimodalDerivable fc (Γ.map embed) (embed φ) :=
  fun ⟨d⟩ => ⟨liftModalToBimodal d⟩

-- Conservative extension (non-trivial, requires proof)
-- "If a pure modal formula is derivable in TM, it's derivable in S5"
theorem modal_embedding_conservative :
    BimodalDerivable fc (Γ.map embedModal) (embedModal φ) → ModalDerivable Γ φ
```

### Conservative extension analysis

The conservative extension direction is harder and may not hold in full generality:

| Embedding | Soundness | Conservative Extension |
|-----------|-----------|----------------------|
| Prop → Modal | ✓ trivial | ✓ (propositional tautologies remain tautologies) |
| Prop → Temporal | ✓ trivial | ✓ (same reasoning) |
| Modal → Bimodal | ✓ trivial | ✓ for theorems (MF doesn't add purely modal theorems) |
| Temporal → Bimodal | ✓ trivial | ✓ for theorems (MF doesn't add purely temporal theorems) |
| Prop → Bimodal | ✓ trivial (transitive) | ✓ (transitive) |

Conservative extension for Modal → Bimodal holds because: the bimodal system adds temporal axioms and MF, but MF only produces formulas involving both `box` and `all_future`. A formula in the pure modal fragment (no `untl`/`snce`) cannot be derived from MF unless it's already derivable from the modal axioms alone. This is a standard result in combined modal logic theory (Craig interpolation argument).

BimodalLogic already has `ConservativeExtension/` with `embedFormula`, `embedAxiom`, and `embedDerivation` demonstrating this pattern (though for a different purpose: fresh-atom extension rather than cross-logic embedding).

---

## Concrete Architecture Recommendation

### Layer 1: Shared Axiom Definitions (new file)

```lean
-- Cslib/Foundations/Logic/Axioms.lean
namespace Cslib.Logic.Axioms
variable {F : Type*}

-- Propositional (require HasBot, HasImp)
variable [HasBot F] [HasImp F]
protected abbrev ImplyK (φ ψ : F) := imp φ (imp ψ φ)
protected abbrev ImplyS (φ ψ χ : F) := imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ))
protected abbrev EFQ (φ : F) := imp bot φ
protected abbrev Peirce (φ ψ : F) := imp (imp (imp φ ψ) φ) φ

-- Modal (additionally require HasBox)
variable [HasBox F]
protected abbrev AxiomK (φ ψ : F) := imp (box (imp φ ψ)) (imp (box φ) (box ψ))
protected abbrev AxiomT (φ : F) := imp (box φ) φ
protected abbrev Axiom4 (φ : F) := imp (box φ) (box (box φ))

-- Temporal (additionally require HasUntil, HasSince)
variable [HasUntil F] [HasSince F]
-- ... BX axioms ...

-- Interaction (require both HasBox and HasUntil)
variable [HasBox F] [HasUntil F]
protected abbrev ModalFuture (φ : F) := imp (box φ) (box (all_future φ))
end Cslib.Logic.Axioms
```

### Layer 2: HasAxiom Typeclasses (per axiom)

```lean
-- Cslib/Foundations/Logic/ProofSystem.lean
class ModusPonens (𝓢 : S) where
  mdp {φ ψ : F} : 𝓢⇓(imp φ ψ) → 𝓢⇓φ → 𝓢⇓ψ

class Necessitation (𝓢 : S) where
  nec {φ : F} : 𝓢⇓φ → 𝓢⇓(box φ)

class TemporalNecessitation (𝓢 : S) where
  tempNec {φ : F} : 𝓢⇓φ → 𝓢⇓(all_future φ)

class HasAxiomImplyK (𝓢 : S) where
  implyK {φ ψ : F} : 𝓢⇓(Axioms.ImplyK φ ψ)
-- ... etc for each axiom
```

### Layer 3: Bundled Proof System Classes

```lean
class PropositionalHilbert (𝓢 : S) extends
  ModusPonens 𝓢, HasAxiomImplyK 𝓢, HasAxiomImplyS 𝓢, HasAxiomEFQ 𝓢, HasAxiomPeirce 𝓢

class ModalHilbert (𝓢 : S) extends
  PropositionalHilbert 𝓢, Necessitation 𝓢, HasAxiomK 𝓢

class ModalS5Hilbert (𝓢 : S) extends
  ModalHilbert 𝓢, HasAxiomT 𝓢, HasAxiom4 𝓢, HasAxiomB 𝓢, HasAxiom5Collapse 𝓢

class TemporalBXHilbert (𝓢 : S) extends
  PropositionalHilbert 𝓢, TemporalNecessitation 𝓢, TemporalDuality 𝓢,
  HasAxiomSerialFuture 𝓢, HasAxiomConnectFuture 𝓢, -- ... etc

class BimodalTMHilbert (𝓢 : S) extends
  ModalS5Hilbert 𝓢, TemporalBXHilbert 𝓢, HasAxiomMF 𝓢
```

### Layer 4: Concrete Systems with DerivationTree

```lean
-- Keep BimodalLogic's DerivationTree with FrameClass for the concrete bimodal system
-- Add separate DerivationTree types for modal and temporal if needed for metalogic
-- Provide InferenceSystem instances for each

instance : BimodalTMHilbert Bimodal.HilbertTM where
  mdp := fun d₁ d₂ => DerivationTree.modus_ponens _ _ _ d₁ d₂
  nec := fun d => DerivationTree.necessitation _ d
  implyK := DerivationTree.axiom _ _ (Axiom.prop_k _ _ _) trivial
  T := DerivationTree.axiom _ _ (Axiom.modal_t _) trivial
  MF := DerivationTree.axiom _ _ (Axiom.modal_future _) trivial
  -- ... etc
```

### Practical Benefits

1. **Theorems proved at `[PropositionalHilbert 𝓢]` automatically apply to Modal, Temporal, and Bimodal** — e.g., the deduction theorem, which is purely propositional
2. **Theorems proved at `[ModalHilbert 𝓢]` automatically apply to Bimodal** — e.g., modal K distribution derived theorems
3. **The concrete `DerivationTree` is preserved** for metalogic proofs that need the tree structure
4. **`InferenceSystem` notation (`S⇓a`) works alongside the existing `⊢[fc]` notation**

---

## What Can and Can't Be Shared

| Component | Shared via typeclasses | Logic-specific |
|-----------|----------------------|----------------|
| Axiom formulas | ✓ (polymorphic abbrevs) | |
| Modus ponens | ✓ (`ModusPonens` class) | |
| Deduction theorem | ✓ (at `PropositionalHilbert` level) | |
| Necessitation | ✓ (`Necessitation` class) | Which formulas it applies to |
| K-distribution derived theorems | ✓ (at `ModalHilbert` level) | |
| DerivationTree | | ✓ (separate inductive per logic) |
| Axiom inductive (`Axiom : F → Type`) | | ✓ (specific constructors per logic) |
| FrameClass parameterization | | ✓ (bimodal/temporal only) |
| Metalogic proofs (soundness, completeness) | | ✓ (inherently logic-specific) |
| Embedding functions | | ✓ (specific to each pair of logics) |

---

## References

- [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) — Entailment class, HasAxiom typeclasses, Hilbert.Normal
- [Foundation Logic Book](https://formalizedformallogic.github.io/Book/) — Documentation of Foundation's proof system architecture
- BimodalLogic `ProofSystem/Axioms.lean` — 42-constructor Axiom inductive with minFrameClass
- BimodalLogic `ProofSystem/Derivation.lean` — FrameClass-parameterized DerivationTree
- BimodalLogic `ConservativeExtension/` — embedFormula, embedAxiom, embedDerivation pattern
- cslib `InferenceSystem.lean` — S⇓a notation, DerivableIn
- cslib `Propositional/NaturalDeduction/Basic.lean` — Theory-parameterized natural deduction
