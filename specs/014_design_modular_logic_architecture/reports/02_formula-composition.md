# Formula Type Composition for Four-Level Logic Hierarchy

**Task**: 14 — Design modular logic architecture
**Date**: 2026-06-08
**Focus**: How to define formula types for Propositional → Modal → Temporal → Bimodal so they compose via imports

## Summary

Lean 4 cannot extend inductive types. The established pattern (FormalizedFormalLogic/Foundation, Mathlib) is: **each logic defines its own standalone `Formula` inductive with duplicated shared constructors**, shares a typeclass layer for notation and polymorphic axioms, and provides explicit embedding functions between formula types. This is the recommended approach for cslib.

---

## Question 1: Can Lean 4 Inductive Types Compose via Import?

**No.** Lean 4's `extends` keyword works for structures (product types) but not for inductives (sum types). The core problem, analyzed by Oswald (2025): when `PropFormula` has `imp : PropFormula → PropFormula → PropFormula`, extending to `ModalFormula` creates ambiguity — should recursive positions become `ModalFormula` or stay `PropFormula`? There is no natural resolution.

**Consequence**: Each level must define its own complete inductive type. The shared constructors (`atom`, `bot`, `imp`) are **duplicated** across all four types. This is exactly what Foundation does — `Propositional.Formula` has `{atom, falsum, and, or, imp}`, `Modal.Formula` has `{atom, falsum, imp, box}`, and `InterpretabilityLogic.Formula` has `{atom, falsum, imp, box, rhd}`. The shared constructors are redefined in each type.

---

## Question 2: The Foundation Pattern in Detail

Foundation's architecture has three layers:

### Layer 1: Atomic Notation Classes (`Foundation/Vorspiel/NotationClass.lean`)

Individual operator typeclasses, each declaring one operation and its notation:

```lean
class Box (α : Type*) where box : α → α
prefix:76 "□" => Box.box

class Dia (α : Type*) where dia : α → α
prefix:76 "◇" => Dia.dia

class Arrow (α : Type*) where arrow : α → α → α
infixr:60 " 🡒 " => Arrow.arrow

class Tilde (α : Type*) where tilde : α → α
prefix:75 "∼" => Tilde.tilde

-- etc. for Top, Bot, Wedge, Vee
```

### Layer 2: Bundled Connective Classes (`Foundation/Logic/LogicSymbol.lean`)

Composition via `extends`:

```lean
class LogicalConnective (α : Type*)
  extends Top α, Bot α, Tilde α, Arrow α, Wedge α, Vee α

class BasicModalLogicalConnective (F : Type*)
  extends LogicalConnective F, Box F, Dia F

-- In InterpretabilityLogic/LogicSymbol.lean:
class InterpretabilityLogicalConnective (F : Type*)
  extends BasicModalLogicalConnective F, Rhd F
```

### Layer 3: Concrete Formula Types (each logic separately)

**Propositional** (`Foundation/Propositional/Formula/Basic.lean`):
```lean
inductive Formula (α : Type u) : Type u
  | atom   : α → Formula α
  | falsum : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  deriving DecidableEq

instance : LogicalConnective (Formula α) where
  tilde := neg; arrow := imp; wedge := and; vee := or
  top := verum; bot := falsum
```

**Modal** (`Foundation/Modal/Formula/Basic.lean`):
```lean
inductive Formula (α : Type*) where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

-- Derived: neg, verum, or, and, dia
instance : BasicModalLogicalConnective (Formula α) where
  tilde := neg; arrow := imp; wedge := and; vee := or
  top := verum; bot := falsum; box := box; dia := dia

instance : ŁukasiewiczAbbrev (Formula α) where
  top := rfl; neg := rfl; or := rfl; and := rfl
```

**InterpretabilityLogic** (`Foundation/InterpretabilityLogic/Formula/Basic.lean`):
```lean
inductive Formula (α : Type*) where
  | atom    : α → Formula α
  | falsum  : Formula α
  | imp     : Formula α → Formula α → Formula α
  | box     : Formula α → Formula α
  | rhd     : Formula α → Formula α → Formula α

instance : InterpretabilityLogicalConnective (Formula α) where
  -- all the same as Modal, plus: rhd := rhd
```

**Key observations**:
- Foundation's Propositional uses `{atom, falsum, and, or, imp}` — 5 constructors with `and`/`or` as primitive
- Foundation's Modal uses `{atom, falsum, imp, box}` — 4 constructors, Łukasiewicz style (neg, and, or derived)
- The propositional and modal constructors **differ** (PL has `and`/`or`; Modal does not)
- No embedding functions exist between Propositional and Modal in Foundation
- Embedding functions exist between Modal → InterpretabilityLogic and back (with `RhdFree` guard)

---

## Question 3: Embedding Functions

Foundation's embedding pattern (`Foundation/InterpretabilityLogic/Formula/OfModal.lean`):

```lean
-- Modal → InterpretabilityLogic (total embedding)
def Modal.Formula.toInterpretabilityLogicFormula : Modal.Formula α → InterpretabilityLogic.Formula α
  | .atom a  => .atom a
  | ⊥        => ⊥
  | φ 🡒 ψ    => (φ.toInterpretabilityLogicFormula) 🡒 (ψ.toInterpretabilityLogicFormula)
  | □φ       => □(φ.toInterpretabilityLogicFormula)

instance : Coe (Modal.Formula α) (InterpretabilityLogic.Formula α) :=
  ⟨Formula.toInterpretabilityLogicFormula⟩
```

```lean
-- InterpretabilityLogic → Modal (partial, requires RhdFree proof)
def InterpretabilityLogic.Formula.toModalFormula
    (φ : Formula α) (_ : φ.RhdFree := by grind) : Modal.Formula α :=
  match φ with
  | atom a  => .atom a
  | ⊥       => ⊥
  | imp φ ψ => (φ.toModalFormula) 🡒 (ψ.toModalFormula)
  | box φ   => □(φ.toModalFormula)
```

**For our four-level hierarchy, the embeddings would be:**

```lean
-- Propositional → Modal (total)
def Propositional.Formula.toModal : Propositional.Formula Atom → Modal.Formula Atom
  | .atom a => .atom a
  | .bot    => .bot
  | .imp φ ψ => .imp (φ.toModal) (ψ.toModal)

-- Propositional → Temporal (total)
def Propositional.Formula.toTemporal : Propositional.Formula Atom → Temporal.Formula Atom
  | .atom a => .atom a
  | .bot    => .bot
  | .imp φ ψ => .imp (φ.toTemporal) (ψ.toTemporal)

-- Modal → Bimodal (total)
def Modal.Formula.toBimodal : Modal.Formula Atom → Bimodal.Formula Atom
  | .atom a  => .atom a
  | .bot     => .bot
  | .imp φ ψ => .imp (φ.toBimodal) (ψ.toBimodal)
  | .box φ   => .box (φ.toBimodal)

-- Temporal → Bimodal (total)
def Temporal.Formula.toBimodal : Temporal.Formula Atom → Bimodal.Formula Atom
  | .atom a   => .atom a
  | .bot      => .bot
  | .imp φ ψ  => .imp (φ.toBimodal) (ψ.toBimodal)
  | .untl φ ψ => .untl (φ.toBimodal) (ψ.toBimodal)
  | .snce φ ψ => .snce (φ.toBimodal) (ψ.toBimodal)

-- Bimodal → Modal (partial, requires TemporalFree proof)
-- Bimodal → Temporal (partial, requires ModalFree proof)
```

**Preserving properties under embeddings**: Embeddings are structurally recursive and injective. Key theorems to prove:

```lean
-- Embedding preserves structural properties
theorem Modal.Formula.toBimodal_injective : Function.Injective (@Modal.Formula.toBimodal Atom)
theorem Temporal.Formula.toBimodal_injective : Function.Injective (@Temporal.Formula.toBimodal Atom)

-- Embedding preserves derived connectives
theorem Modal.Formula.toBimodal_neg : (φ.neg).toBimodal = φ.toBimodal.neg
theorem Modal.Formula.toBimodal_and : (φ.and ψ).toBimodal = φ.toBimodal.and ψ.toBimodal

-- Embedding commutes with complexity
theorem Modal.Formula.toBimodal_complexity : φ.toBimodal.complexity = φ.complexity
```

These all follow by structural induction and definitional unfolding — straightforward proofs.

---

## Question 4: The "Open Sum" Alternative

Could `Bimodal.Formula` be defined as `Modal.Formula Atom ⊕ Temporal.Formula Atom` modulo shared propositional constructors?

**No, this is impractical.** The coproduct `⊕` creates a disjoint sum where `Sum.inl (Modal.Formula.bot)` and `Sum.inr (Temporal.Formula.bot)` are different terms. You would need a quotient to identify shared constructors, but:

1. Quotient types destroy pattern matching — you can't case-split on `Bimodal.Formula` constructors
2. Lean's equation compiler won't generate recursive functions over quotient inductives
3. `DecidableEq` on quotients requires decidable equality of the equivalence relation
4. No existing project uses this pattern

**The duplication of shared constructors is cheap and correct.** Three copies of `| bot : Formula Atom` is ~3 lines of code, and `DecidableEq`, `BEq`, `Countable` derive automatically on each.

---

## Question 5: Derived Connectives

Each concrete formula type should define its own derived connectives as `abbrev` or `def` on the concrete type, AND register them via the shared typeclass.

### On concrete types (per logic):

```lean
-- In Modal.Formula namespace
abbrev neg (φ : Modal.Formula Atom) := imp φ bot
abbrev top : Modal.Formula Atom := imp bot bot
abbrev or (φ ψ : Modal.Formula Atom) := imp (neg φ) ψ
abbrev and (φ ψ : Modal.Formula Atom) := neg (imp φ (neg ψ))
abbrev dia (φ : Modal.Formula Atom) := neg (box (neg φ))
```

```lean
-- In Temporal.Formula namespace (additional temporal derived ops)
abbrev some_future (φ : Temporal.Formula Atom) := untl φ top
abbrev some_past (φ : Temporal.Formula Atom) := snce φ top
abbrev all_future (φ : Temporal.Formula Atom) := neg (some_future (neg φ))
abbrev all_past (φ : Temporal.Formula Atom) := neg (some_past (neg φ))
```

### Via typeclass (for polymorphic code):

Polymorphic axioms and theorems use the typeclass methods:

```lean
-- Polymorphic over any formula type with modal connectives
theorem k_axiom [ModalConnectives F] [ŁukasiewiczAbbrev F] (φ ψ : F) :
    ... -- uses □, 🡒 notation from typeclasses
```

**Recommended approach**: Use `abbrev` for derived connectives at the concrete type level (so `grind`/`simp` can unfold them), and the typeclass for polymorphic definitions.

---

## Question 6: DecidableEq, BEq, Countable

These derive automatically and independently on each concrete formula type:

```lean
inductive Modal.Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | bot : Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  | box : Formula Atom → Formula Atom
  deriving DecidableEq, BEq

-- Countable requires [Countable Atom]:
instance [Countable Atom] : Countable (Modal.Formula Atom) := ...
```

Foundation demonstrates this pattern — `DecidableEq` is derived on each formula type independently. No cross-type composition is needed.

BimodalLogic's existing `DecidableEq`, `BEq`, `Countable`, `LawfulBEq`, `ReflBEq`, `Infinite`, and `Denumerable` instances all work on the monolithic `Formula` type and will transfer directly to `Bimodal.Formula Atom` with minimal changes (mainly adding the `Atom` parameter and `deriving` where possible).

---

## Question 7: Notation

Foundation solves this elegantly using scoped notation on typeclass operations. The key insight: **notation is bound to the typeclass, not the formula type**.

```lean
-- These are defined ONCE on the typeclass operations:
prefix:76 "□" => Box.box        -- works for any type with [Box F]
prefix:76 "◇" => Dia.dia
infixr:60 " 🡒 " => Arrow.arrow
prefix:75 "∼" => Tilde.tilde
```

When you open the appropriate namespace, notation resolves through typeclass instances:

```lean
-- In a file working with Modal.Formula:
open scoped LO  -- gets □, ◇, 🡒, etc.
-- □ resolves to Modal.Formula.box via the Box instance

-- In a file working with Bimodal.Formula:
-- □ resolves to Bimodal.Formula.box via a different Box instance
```

**For cslib**, the recommended pattern uses `scoped` notation within each logic's namespace:

```lean
namespace Cslib.Logic.Modal
  scoped prefix:40 "□" => Formula.box
  scoped prefix:40 "◇" => Formula.dia
  -- etc.
end Cslib.Logic.Modal

namespace Cslib.Logic.Temporal
  scoped prefix:40 "G" => Formula.all_future
  scoped prefix:40 "H" => Formula.all_past
  scoped prefix:40 "F" => Formula.some_future
  scoped prefix:40 "P" => Formula.some_past
  -- etc.
end Cslib.Logic.Temporal

namespace Cslib.Logic.Bimodal
  -- Gets all of the above plus combined notations
  scoped prefix:40 "□" => Formula.box
  scoped prefix:40 "G" => Formula.all_future
  -- etc.
end Cslib.Logic.Bimodal
```

When working in one logic, `open scoped Cslib.Logic.Modal` brings in only modal notation. When working in bimodal, `open scoped Cslib.Logic.Bimodal` brings in everything. No conflicts because scoped notation is opt-in.

**Alternative (Foundation-style)**: Define notation on typeclass methods globally, and let instance resolution disambiguate. This works when only one formula type is in scope at a time.

---

## Question 8: Subformula Closure

BimodalLogic's SubformulaClosure, NestingDepth, and TemporalFormulas operate on the full 6-constructor formula type. **These cannot be meaningfully factored** because:

1. `subformulas` must enumerate all subformulas including temporal ones inside modal ones and vice versa
2. `closureWithNeg` needs the full formula type to compute negation closure
3. `NestingDepth` counts both modal and temporal nesting simultaneously
4. `TemporalFormulas` extracts temporal subformulas from a bimodal formula — this is inherently a bimodal operation

**Recommendation**: Keep subformula closure operations at the bimodal level only. Modal.Formula and Temporal.Formula can have their own simpler `subformulas` if needed, but the full closure machinery is bimodal-specific (used by decidability and completeness).

---

## Recommended Architecture

### Concrete Definitions

```lean
-- Cslib/Logics/Propositional/Formula.lean (refactored from current Defs.lean)
namespace Cslib.Logic.Propositional

inductive Formula (Atom : Type u) : Type u where
  | atom : Atom → Formula Atom
  | bot  : Formula Atom
  | imp  : Formula Atom → Formula Atom → Formula Atom
  deriving DecidableEq, BEq

namespace Formula
abbrev neg (φ : Formula Atom) : Formula Atom := imp φ bot
abbrev top : Formula Atom := imp bot bot
abbrev or (φ ψ : Formula Atom) : Formula Atom := imp (neg φ) ψ
abbrev and (φ ψ : Formula Atom) : Formula Atom := neg (imp φ (neg ψ))
end Formula

end Cslib.Logic.Propositional
```

```lean
-- Cslib/Logics/Modal/Formula.lean (new, replaces current Proposition in Basic.lean)
namespace Cslib.Logic.Modal

inductive Formula (Atom : Type u) : Type u where
  | atom : Atom → Formula Atom
  | bot  : Formula Atom
  | imp  : Formula Atom → Formula Atom → Formula Atom
  | box  : Formula Atom → Formula Atom
  deriving DecidableEq, BEq

namespace Formula
abbrev neg (φ : Formula Atom) : Formula Atom := imp φ bot
abbrev top : Formula Atom := imp bot bot
abbrev or (φ ψ : Formula Atom) : Formula Atom := imp (neg φ) ψ
abbrev and (φ ψ : Formula Atom) : Formula Atom := neg (imp φ (neg ψ))
abbrev dia (φ : Formula Atom) : Formula Atom := neg (box (neg φ))
end Formula

end Cslib.Logic.Modal
```

```lean
-- Cslib/Logics/Temporal/Formula.lean (new)
namespace Cslib.Logic.Temporal

inductive Formula (Atom : Type u) : Type u where
  | atom : Atom → Formula Atom
  | bot  : Formula Atom
  | imp  : Formula Atom → Formula Atom → Formula Atom
  | untl : Formula Atom → Formula Atom → Formula Atom
  | snce : Formula Atom → Formula Atom → Formula Atom
  deriving DecidableEq, BEq

namespace Formula
abbrev neg (φ : Formula Atom) : Formula Atom := imp φ bot
abbrev top : Formula Atom := imp bot bot
abbrev or (φ ψ : Formula Atom) : Formula Atom := imp (neg φ) ψ
abbrev and (φ ψ : Formula Atom) : Formula Atom := neg (imp φ (neg ψ))
abbrev some_future (φ : Formula Atom) : Formula Atom := untl φ top
abbrev some_past (φ : Formula Atom) : Formula Atom := snce φ top
abbrev all_future (φ : Formula Atom) : Formula Atom := neg (some_future (neg φ))
abbrev all_past (φ : Formula Atom) : Formula Atom := neg (some_past (neg φ))
end Formula

end Cslib.Logic.Temporal
```

```lean
-- Cslib/Logics/Bimodal/Formula.lean (ported from BimodalLogic)
namespace Cslib.Logic.Bimodal

inductive Formula (Atom : Type u) : Type u where
  | atom : Atom → Formula Atom
  | bot  : Formula Atom
  | imp  : Formula Atom → Formula Atom → Formula Atom
  | box  : Formula Atom → Formula Atom
  | untl : Formula Atom → Formula Atom → Formula Atom
  | snce : Formula Atom → Formula Atom → Formula Atom
  deriving DecidableEq, BEq

-- All derived connectives from both Modal and Temporal:
namespace Formula
abbrev neg (φ : Formula Atom) : Formula Atom := imp φ bot
abbrev top : Formula Atom := imp bot bot
abbrev or (φ ψ : Formula Atom) : Formula Atom := imp (neg φ) ψ
abbrev and (φ ψ : Formula Atom) : Formula Atom := neg (imp φ (neg ψ))
abbrev dia (φ : Formula Atom) : Formula Atom := neg (box (neg φ))
abbrev some_future (φ : Formula Atom) : Formula Atom := untl φ top
abbrev some_past (φ : Formula Atom) : Formula Atom := snce φ top
abbrev all_future (φ : Formula Atom) : Formula Atom := neg (some_future (neg φ))
abbrev all_past (φ : Formula Atom) : Formula Atom := neg (some_past (neg φ))
-- ... always, sometimes, swap_temporal, complexity, etc.
end Formula

end Cslib.Logic.Bimodal
```

### Typeclass Layer

```lean
-- Cslib/Foundations/Logic/Connectives.lean (new)
namespace Cslib.Logic

-- Atomic notation classes
class HasBot (F : Type*) where bot : F
class HasImp (F : Type*) where imp : F → F → F
class HasBox (F : Type*) where box : F → F
class HasUntil (F : Type*) where untl : F → F → F
class HasSince (F : Type*) where snce : F → F → F

-- Bundled connective classes
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F

class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F

class TemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F, HasSince F

class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F

-- Property classes for derived connectives
class ŁukasiewiczDerived (F : Type*) [PropositionalConnectives F] where
  neg (φ : F) : F := HasImp.imp φ HasBot.bot
  top : F := HasImp.imp HasBot.bot HasBot.bot
  or (φ ψ : F) : F := HasImp.imp (neg φ) ψ
  and (φ ψ : F) : F := neg (HasImp.imp φ (neg ψ))

end Cslib.Logic
```

### Embedding Functions

```lean
-- Cslib/Logics/Bimodal/Embedding.lean (new)
namespace Cslib.Logic

def Modal.Formula.toBimodal : Modal.Formula Atom → Bimodal.Formula Atom
  | .atom a  => .atom a
  | .bot     => .bot
  | .imp φ ψ => .imp (φ.toBimodal) (ψ.toBimodal)
  | .box φ   => .box (φ.toBimodal)

def Temporal.Formula.toBimodal : Temporal.Formula Atom → Bimodal.Formula Atom
  | .atom a   => .atom a
  | .bot      => .bot
  | .imp φ ψ  => .imp (φ.toBimodal) (ψ.toBimodal)
  | .untl φ ψ => .untl (φ.toBimodal) (ψ.toBimodal)
  | .snce φ ψ => .snce (φ.toBimodal) (ψ.toBimodal)

-- Coercions for convenience
instance : Coe (Modal.Formula Atom) (Bimodal.Formula Atom) := ⟨Modal.Formula.toBimodal⟩
instance : Coe (Temporal.Formula Atom) (Bimodal.Formula Atom) := ⟨Temporal.Formula.toBimodal⟩

-- Key theorems
theorem Modal.Formula.toBimodal_injective : Function.Injective (@Modal.Formula.toBimodal Atom) := by
  intro φ ψ h; induction φ generalizing ψ <;> cases ψ <;> simp_all [toBimodal]

theorem Modal.Formula.toBimodal_preserves_neg :
    (φ.neg).toBimodal = φ.toBimodal.neg := by simp [Formula.neg, toBimodal]

end Cslib.Logic
```

---

## Impact on Existing cslib

### What Changes

| File | Change | Effort |
|------|--------|--------|
| `Cslib/Logics/Propositional/Defs.lean` | Refactor `Proposition` to use `{atom, bot, imp}` primitives (currently `{atom, and, or, impl}`) | Medium — ~150 lines, requires reproving `Theory`, `IsIntuitionistic`, `IsClassical` |
| `Cslib/Logics/Modal/Basic.lean` | Replace `Proposition` with new `Formula` using `{atom, bot, imp, box}`; reprove `Satisfies`, axioms | Medium — ~270 lines, `grind` proofs need reworking |
| `Cslib/Logics/Modal/Cube.lean` | Adapt to new `Formula`; reprove logic inclusions | Low — ~140 lines, follows from `Satisfies` changes |
| `Cslib/Logics/Modal/Denotation.lean` | Adapt `denotation` to new `Formula` | Low — ~50 lines |

### What Doesn't Change

| File | Reason |
|------|--------|
| `Cslib/Logics/HML/` | Different design (labeled modalities), stays independent |
| `Cslib/Logics/LinearLogic/` | Unrelated logic system |
| `Cslib/Foundations/Logic/InferenceSystem.lean` | Unchanged — already general enough |
| `Cslib/Foundations/Logic/LogicalEquivalence.lean` | Unchanged — already parametric |

---

## Confidence Level

- **Separate types with duplicated constructors**: **High** — this is exactly what Foundation does and it works at scale (8+ logics, Gödel's incompleteness theorems)
- **Typeclass layer for notation/polymorphism**: **High** — Foundation and Mathlib both demonstrate this
- **Embedding functions with `Coe` instances**: **High** — Foundation's Modal → InterpretabilityLogic pattern is directly applicable
- **Refactoring existing cslib Modal to box-primary**: **Medium** — the `grind` proofs will need rework but the module is small
- **Refactoring existing cslib Propositional to bot+imp only**: **Medium** — removes `and`/`or` as primitives, which changes the Natural Deduction module

## References

- [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) — primary reference for composition pattern
- [A Meditation on Extending Inductive Types in Lean4](https://jamesoswald.dev/posts/meditation-extending-inductive-types/) — analysis of why inductive extension is impossible
- [A Simple Typeclass for Logic Formulae in Lean4](https://jamesoswald.dev/posts/a-type-class-for-logic/) — alternative Language typeclass approach
