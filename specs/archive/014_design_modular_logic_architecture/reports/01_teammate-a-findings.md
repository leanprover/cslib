# Teammate A Findings: Implementation Approaches and Patterns

**Task**: 14 — Design modular logic architecture for composable modal, temporal, and bimodal syntax and proof systems
**Date**: 2026-06-08
**Angle**: Primary — concrete implementation patterns for modularity
**Confidence Level**: High (for recommended approach), Medium (for some alternatives)

---

## Key Findings

### 1. The Two Repositories Have Fundamentally Different Formula Designs

**cslib's Modal Logic** (`Cslib.Logics.Modal.Basic`):
- `Proposition Atom` with 4 constructors: `atom`, `neg`, `and`, `diamond`
- `box` is *derived* as `¬◇¬φ`
- Semantic-first: uses `Satisfies` function directly, with `InferenceSystem` wired to `Judgement`
- No Hilbert-style proof system; the `InferenceSystem` instance yields `Satisfies.Bundled` (semantic derivation)
- Clean, concise, ~270 lines total

**BimodalLogic** (`Theories/Bimodal/Syntax/Formula.lean`):
- `Formula` with 6 constructors: `atom`, `bot`, `imp`, `box`, `untl`, `snce`
- `neg` is *derived* as `φ.imp bot`; `diamond` is derived as `¬□¬φ`
- Proof-system-first: 21+ axiom schemata in `Axiom`, derivation trees in `DerivationTree`
- Semantics defined separately via task frames with temporal polymorphism
- Large codebase (~15,000+ lines across all modules)

**Critical incompatibility**: cslib uses `neg` as primitive and `box` as derived; BimodalLogic uses `bot`+`imp` as primitives and `neg` as derived. These are logically equivalent but structurally different, which matters for pattern matching, induction, and proof automation.

### 2. The FormalizedFormalLogic/Foundation Pattern Is the State of the Art

The Foundation project (https://github.com/FormalizedFormalLogic/Foundation) provides the most mature pattern for composable logic in Lean 4. Their architecture:

**Layer 1 — Notation typeclasses** (atomic, single-responsibility):
```lean
class Box (α : Type*) where box : α → α
class Dia (α : Type*) where dia : α → α
class Arrow (α : Type*) where arrow : α → α → α
-- etc.
```

**Layer 2 — Bundled connective classes** (composition via `extends`):
```lean
class LogicalConnective (α : Type*) extends Top α, Bot α, Tilde α, Arrow α, Wedge α, Vee α
class BasicModalLogicalConnective (F : Type*) extends LogicalConnective F, Box F, Dia F
class InterpretabilityLogicalConnective (F : Type*) extends BasicModalLogicalConnective F, Rhd F
```

**Layer 3 — Concrete formula types** (each instantiates its connective class):
```lean
inductive Modal.Formula (α : Type*) where
  | atom | falsum | imp | box  -- 4 constructors

instance : BasicModalLogicalConnective (Modal.Formula α) where ...

inductive InterpretabilityLogic.Formula (α : Type*) where
  | atom | falsum | imp | box | rhd  -- 5 constructors (adds ▷)

instance : InterpretabilityLogicalConnective (InterpretabilityLogic.Formula α) where ...
```

**Layer 4 — Property classes** (constrain relationships between connectives):
```lean
class DiaByBox (F) [Box F] [Dia F] [Tilde F] where
  dia_by_box {φ : F} : ◇φ = ∼□(∼φ)

class ŁukasiewiczAbbrev (F : Type*) [LogicalConnective F] extends NegAbbrev F where
  top : ⊤ = ∼(⊥ : F)
  or {φ ψ : F} : φ ⋎ ψ = ∼φ 🡒 ψ
  and {φ ψ : F} : φ ⋏ ψ = ∼(φ 🡒 ∼ψ)
```

**Layer 5 — Entailment** (proof system abstraction):
```lean
class Entailment (S : Type*) (F : outParam Type*) where
  Prf : S → F → Type*
```

**Key insight**: Foundation does NOT compose logics by extending inductive types. Each logic has its own concrete `Formula` type. Composition is achieved through shared typeclasses on those types. Axioms are defined polymorphically over any type satisfying the right connective class.

### 3. cslib's InferenceSystem Is Already Well-Positioned

The `InferenceSystem` typeclass in cslib:
```lean
class InferenceSystem (S : Type*) (α : Type*) where
  derivation (a : α) : Sort v
```

This is analogous to Foundation's `Entailment` but more general (returns `Sort v` instead of `Type*`). The `S` parameter is a "tag" for the system, and `α` is the type of derivable things. This naturally supports:
- Multiple proof systems for the same formula type (different `S` tags)
- Semantic derivation (as currently done with `Satisfies.Bundled`)
- Hilbert-style derivation (as BimodalLogic does)
- Both coexisting via different `S` tags

### 4. cslib's Propositional Logic Already Has a Separate Hierarchy

`Cslib.Logic.PL.Proposition` defines a propositional formula type with `atom`, `and`, `or`, `impl`, and derives `neg` from `impl`. It has `Theory` (sets of propositions), `IsIntuitionistic`, `IsClassical` typeclasses, and natural deduction via `InferenceSystem`. This shows cslib already practices the pattern of separate formula types per logic.

### 5. Mathlib's Algebraic Hierarchy Lessons

Mathlib's key patterns for composable structures:

1. **Bundled inheritance with `extends`**: `Monoid` extends `MulOneClass` extends `Mul`. Each class bundles the fields of its ancestors.
2. **Avoid diamond inheritance where possible**: When two axes of extension exist (e.g., `AddGroup` + `Monoid` → `Ring`), Mathlib uses `extends` for one path and instance parameters for the other.
3. **Mixin typeclasses for properties**: `IsCommutative`, `IsTrans`, etc. are separate from the algebraic structure. cslib already follows this for frame properties (`Std.Refl`, `Std.Symm`, etc.).
4. **Forgetful instances**: A `Group` instance automatically provides a `Monoid` instance. Similarly, a `BimodalFormula` should automatically provide a `ModalFormula`-like view.

### 6. Temporal Logic Formalizations Are Monolithic

Existing Lean 4 temporal logic projects (LeanearTemporalLogic, Lentil/TLA) all define monolithic formula types with temporal operators baked in. None attempt to compose temporal logic from a base propositional fragment. This is because temporal operators fundamentally change the semantics (from state-based to trace-based), making clean composition harder than in the algebraic case.

### 7. BimodalLogic's Proof System Has Deep Entanglement

The 21 axiom schemata in BimodalLogic are organized into layers:
- **Propositional** (4): prop_k, prop_s, ex_falso, peirce
- **S5 Modal** (5): modal_t, modal_4, modal_b, modal_5_collapse, modal_k_dist
- **BX Temporal** (22): Burgess-Xu axioms for Until/Since
- **Modal-Temporal Interaction** (1): modal_future (□φ → G□φ)

The interaction axiom (`modal_future`) explicitly couples the modal and temporal fragments. The DerivationTree type is parameterized by `FrameClass` (Base, Dense, Discrete), with axioms gated by `minFrameClass ≤ fc`. This is a clean pattern that *could* be factored.

---

## Recommended Approach

### Strategy: "Separate Formula Types with Shared Typeclass Layer"

Follow the Foundation pattern adapted to cslib's conventions. Do NOT try to create a single polymorphic formula type. Instead:

#### A. Define a Typeclass Hierarchy for Connectives

```lean
-- In Cslib.Foundations.Logic.Connectives (new file)
namespace Cslib.Logic

-- Notation classes (some may already exist)
class HasBot (F : Type*) where bot : F
class HasImp (F : Type*) where imp : F → F → F
class HasBox (F : Type*) where box : F → F
class HasUntil (F : Type*) where untl : F → F → F
class HasSince (F : Type*) where snce : F → F → F

-- Bundled connective classes
class PropositionalConnectives (F : Type*) extends
  HasBot F, HasImp F

class ModalConnectives (F : Type*) extends
  PropositionalConnectives F, HasBox F

class TemporalConnectives (F : Type*) extends
  PropositionalConnectives F, HasUntil F, HasSince F

class BimodalConnectives (F : Type*) extends
  ModalConnectives F, HasUntil F, HasSince F
  -- Equivalently: ModalConnectives F, TemporalConnectives F
  -- (Lean resolves the diamond via `extends`)
```

#### B. Keep Separate Concrete Formula Types

```lean
-- Cslib.Logics.Modal.Syntax (refactored from current Basic)
inductive Modal.Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | bot : Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  | box : Formula Atom → Formula Atom

instance : ModalConnectives (Modal.Formula Atom) where ...

-- Cslib.Logics.Temporal.Syntax (new)
inductive Temporal.Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | bot : Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  | untl : Formula Atom → Formula Atom → Formula Atom
  | snce : Formula Atom → Formula Atom → Formula Atom

instance : TemporalConnectives (Temporal.Formula Atom) where ...

-- Cslib.Logics.Bimodal.Syntax (port from BimodalLogic)
inductive Bimodal.Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | bot : Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  | box : Formula Atom → Formula Atom
  | untl : Formula Atom → Formula Atom → Formula Atom
  | snce : Formula Atom → Formula Atom → Formula Atom

instance : BimodalConnectives (Bimodal.Formula Atom) where ...
```

#### C. Define Axioms Polymorphically

```lean
-- Cslib.Logics.Modal.Axioms
namespace Modal.Axioms
variable {F : Type*} [ModalConnectives F]

-- Derived connectives
def neg (φ : F) : F := HasImp.imp φ HasBot.bot
def diamond (φ : F) : F := neg (HasBox.box (neg φ))

-- Axiom schemas as formulas
def K (φ ψ : F) : F := HasImp.imp (HasBox.box (HasImp.imp φ ψ)) (HasImp.imp (HasBox.box φ) (HasBox.box ψ))
def T (φ : F) : F := HasImp.imp (HasBox.box φ) φ
-- etc.
end Modal.Axioms
```

#### D. Use InferenceSystem for All Proof Systems

```lean
-- Tag types for different proof systems
structure Modal.HilbertK : Type := -- K proof system tag
structure Modal.HilbertS5 : Type := -- S5 proof system tag
structure Bimodal.HilbertTM : Type := -- TM proof system tag

-- Semantic derivation uses Default tag (already exists)
-- Hilbert-style derivation uses specific tags
instance : InferenceSystem Modal.HilbertS5 (Judgement World Atom) where
  derivation j := ... -- Hilbert derivation trees
```

#### E. Provide Embedding Functions Between Formula Types

```lean
-- Embed modal formulas into bimodal formulas
def Modal.Formula.toBimodal : Modal.Formula Atom → Bimodal.Formula Atom
  | .atom a => .atom a
  | .bot => .bot
  | .imp φ ψ => .imp (toBimodal φ) (toBimodal ψ)
  | .box φ => .box (toBimodal φ)

-- Embed temporal formulas into bimodal formulas
def Temporal.Formula.toBimodal : Temporal.Formula Atom → Bimodal.Formula Atom
  | .atom a => .atom a
  | .bot => .bot
  | .imp φ ψ => .imp (toBimodal φ) (toBimodal ψ)
  | .untl φ ψ => .untl (toBimodal φ) (toBimodal ψ)
  | .snce φ ψ => .snce (toBimodal φ) (toBimodal ψ)

-- Key theorem: embeddings preserve derivability
theorem Modal.soundness_lifts_to_bimodal :
  Modal.Derivable φ → Bimodal.Derivable (φ.toBimodal) := ...
```

#### F. Handle the cslib Modal Refactoring

The current `Cslib.Logics.Modal.Proposition` uses `neg`/`and`/`diamond` as primitives (classical De Morgan style). For composability with BimodalLogic, it should be refactored to use `bot`/`imp`/`box` as primitives (Hilbert/Łukasiewicz style), with `neg`, `and`, `diamond` as derived. This aligns with:
- BimodalLogic's existing conventions
- Foundation's conventions
- Standard proof theory conventions (Hilbert systems work with `bot`+`imp`+`box`)

**However**, the existing semantic results (`Satisfies.k`, `Satisfies.t`, etc.) should be preserved. The refactoring would:
1. Change the 4 constructors from `(atom, neg, and, diamond)` to `(atom, bot, imp, box)`
2. Derive `neg`, `and`, `or`, `diamond` via `def`
3. Re-prove the satisfaction characterization lemmas
4. Keep the `InferenceSystem` integration unchanged

### Why NOT a Single Parameterized Formula Type

An alternative would be parameterizing `Formula` over which constructors are available:
```lean
-- DO NOT DO THIS
inductive Formula (hasBox : Bool) (hasUntil : Bool) (Atom : Type*) where
  | atom : Atom → Formula hasBox hasUntil Atom
  | bot : Formula hasBox hasUntil Atom
  | imp : Formula hasBox hasUntil Atom → Formula hasBox hasUntil Atom → Formula hasBox hasUntil Atom
  | box : hasBox = true → Formula hasBox hasUntil Atom → Formula hasBox hasUntil Atom
  | untl : hasUntil = true → Formula hasBox hasUntil Atom → Formula hasBox hasUntil Atom → Formula hasBox hasUntil Atom
```

This is problematic because:
1. **Lean 4 does not support indexed inductive families with propositional guards well** — the proof obligations infect every pattern match
2. **Induction principles become unwieldy** — every case carries guard proofs
3. **Notation breaks** — `□φ` would need to carry a proof that `hasBox = true`
4. **No one does this** — not Foundation, not Mathlib, not any temporal logic project
5. **Decidable equality becomes complex** — the derived instances won't work

---

## Evidence/Examples

### Foundation Pattern in Practice

Foundation demonstrates that the InterpretabilityLogic cleanly extends modal logic:

```lean
-- Foundation/InterpretabilityLogic/LogicSymbol.lean
class InterpretabilityLogicalConnective (F : Type*) extends BasicModalLogicalConnective F, Rhd F

-- Foundation/InterpretabilityLogic/Formula/Basic.lean
inductive Formula (α : Type*) where
  | atom | falsum | imp | box | rhd  -- adds ▷ to modal formula
  deriving DecidableEq

instance : InterpretabilityLogicalConnective (Formula α) where ...
```

This is exactly the pattern needed: `BimodalConnectives` would extend `ModalConnectives` with `HasUntil` and `HasSince`, and the `Bimodal.Formula` type would add `untl` and `snce` constructors.

### BimodalLogic's FrameClass Pattern Is Reusable

The `FrameClass` and `minFrameClass` approach for axiom gating is clean:
```lean
inductive FrameClass | Base | Dense | Discrete

-- Each axiom declares its minimum frame class
def Axiom.minFrameClass : Axiom φ → FrameClass
  | modal_t _ => .Base
  | density _ => .Dense
  | prior_UZ _ => .Discrete

-- DerivationTree is parameterized by FrameClass
inductive DerivationTree (fc : FrameClass) : Context → Formula → Type where
  | axiom ... (h_fc : h.minFrameClass ≤ fc) : ...
```

This can be adopted directly in cslib's architecture.

---

## Proposed Module Layout

```
Cslib/
├── Foundations/
│   └── Logic/
│       ├── InferenceSystem.lean     -- (existing, unchanged)
│       └── Connectives.lean         -- NEW: typeclass hierarchy
├── Logics/
│   ├── Modal/
│   │   ├── Syntax.lean              -- NEW: Formula with (atom, bot, imp, box)
│   │   ├── Axioms.lean              -- NEW: polymorphic axiom definitions
│   │   ├── Semantics.lean           -- REFACTORED from Basic.lean
│   │   ├── Denotation.lean          -- (existing, adapted)
│   │   ├── Cube.lean                -- (existing, adapted)
│   │   └── ProofSystem.lean         -- NEW: Hilbert derivation
│   ├── Temporal/
│   │   ├── Syntax.lean              -- NEW: Formula with (atom, bot, imp, untl, snce)
│   │   ├── Axioms.lean              -- NEW: BX temporal axioms
│   │   ├── Semantics.lean           -- NEW: linear order semantics
│   │   └── ProofSystem.lean         -- NEW: temporal derivation
│   └── Bimodal/
│       ├── Syntax.lean              -- PORT: from BimodalLogic
│       ├── Axioms.lean              -- PORT: TM axioms
│       ├── Semantics/
│       │   ├── TaskFrame.lean       -- PORT
│       │   ├── WorldHistory.lean    -- PORT
│       │   ├── Truth.lean           -- PORT
│       │   └── Validity.lean        -- PORT
│       ├── ProofSystem.lean         -- PORT: derivation trees
│       ├── Embedding.lean           -- NEW: Modal/Temporal → Bimodal
│       └── Metalogic/
│           ├── Soundness.lean       -- PORT
│           ├── Completeness.lean    -- PORT
│           └── Decidability.lean    -- PORT
```

---

## Risk Assessment

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| Refactoring cslib Modal breaks existing proofs | High | Gradual refactoring with deprecation aliases |
| Polymorphic axioms harder to use than concrete ones | Medium | Provide notation and instances for common cases |
| Embedding functions complex to maintain | Low | They're structurally recursive, easy to write |
| Temporal semantics too different for shared abstraction | Medium | Accept separate semantic layers; share only syntax/proof system typeclasses |
| `grind` tactic depends on specific formula structure | Medium | Re-tag `@[grind]` attributes after refactoring |

---

## Confidence Level

- **Overall approach (separate types + shared typeclasses)**: **High** — this is the established pattern in Foundation, Mathlib, and the broader Lean community
- **Specific typeclass hierarchy**: **Medium** — the exact set of notation classes needs experimentation; cslib may want different granularity than Foundation
- **Embedding-based composition**: **High** — structurally recursive embeddings are standard and compose well
- **Feasibility of refactoring current Modal**: **Medium** — depends on downstream usage of the current `Proposition` type and `Satisfies` function
