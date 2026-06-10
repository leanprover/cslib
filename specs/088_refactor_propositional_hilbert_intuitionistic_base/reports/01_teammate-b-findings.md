# Teammate B Findings: Alternative Approaches and Prior Art

**Task**: #88 — Refactor propositional Hilbert system to intuitionistic base with uniform extension architecture
**Date**: 2026-06-10
**Angle**: Alternative approaches, prior art from Lean 4 repos, Mathlib patterns

## Key Findings

### 1. FormalizedFormalLogic/Foundation — The Reference Implementation

The most mature and directly relevant Lean 4 project is [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) (~1,378 commits, 99.7% Lean). Their design is **radically different** from cslib's current approach and directly addresses the exact problem this task targets.

**Their key architectural choices:**

#### A. Axiom Sets as `Set (Formula α)`, not inductives

```lean
abbrev Axiom (α) := Set (Formula α)
```

Axioms are simply sets of formulas. A "logic" is defined by composing axiom sets. This avoids the inductive duplication problem entirely.

#### B. Layered Entailment Typeclasses (Min → Int → Cl)

```lean
-- Minimal logic: implication + conjunction + disjunction
class Minimal (𝓢 : S) extends ModusPonens 𝓢, HasAxiomImplyK 𝓢, HasAxiomImplyS 𝓢, ...

-- Intuitionistic = Minimal + EFQ
class Int (𝓢 : S) extends Minimal 𝓢, HasAxiomEFQ 𝓢

-- Classical = Minimal + DNE  (note: NOT Int + DNE)
class Cl (𝓢 : S) extends Minimal 𝓢, HasAxiomDNE 𝓢
```

**Critical insight**: Their `Cl` extends `Minimal` directly, not `Int`. This avoids forcing classical reasoning to go through intuitionistic. However, they prove `Int` instances from `Cl` via `EFQ` being derivable from `DNE`.

#### C. Concrete Hilbert Systems as Structures with Schema Sets

```lean
structure Hilbert (α) where
  schema : Set (Formula α)
  schema_closed : ∀ φ ∈ schema, ∀ s, φ⟦s⟧ ∈ schema

-- Named logics:
protected def Min : Hilbert α := ⟨∅, by tauto⟩
protected def Int : Hilbert α := ⟨{ Axioms.EFQ φ | φ }, by grind⟩
protected def Cl  : Hilbert α := ⟨{ Axioms.EFQ φ | φ } ∪ { Axioms.LEM φ | φ }, by grind⟩
```

Extensions are just set unions. Going from Int to Cl means adding `{ Axioms.LEM φ | φ }`. Going from K to KT means adding `{ Axioms.T φ | φ }`.

#### D. `sumNormal` for Modal Logic Extensions

```lean
-- Combine two logics with shared rules
inductive sumNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {φ} : L₁ ⊢ φ → sumNormal L₁ L₂ φ
  | mem₂ {φ} : L₂ ⊢ φ → sumNormal L₁ L₂ φ
  | mdp  {φ ψ} : sumNormal L₁ L₂ (φ 🡒 ψ) → sumNormal L₁ L₂ φ → sumNormal L₁ L₂ ψ
  | subst {φ s} : sumNormal L₁ L₂ φ → sumNormal L₁ L₂ (φ⟦s⟧)
  | nec {φ}     : sumNormal L₁ L₂ φ → sumNormal L₁ L₂ (□φ)
```

Then `S := sumNormal GL {Axioms.T (.atom 0)}` — the logic S is GL plus the T axiom.

#### E. `Has*` Typeclasses on Axiom Sets (not on proof systems)

```lean
class HasK (Ax : Axiom α) where
  p : α; q : α
  ne_pq : p ≠ q
  mem_K : Axioms.K (.atom p) (.atom q) ∈ Ax

class HasT (Ax : Axiom α) where
  p : α
  mem_T : Axioms.T (.atom p) ∈ Ax
```

This means typeclass resolution can automatically derive that `Normal Ax` has axiom T whenever `Ax.HasT`.

### 2. James Oswald's Language Typeclass Pattern

[James Oswald's approach](https://jamesoswald.dev/posts/a-type-class-for-logic/) uses a `Language α` class that abstracts over formula types with indexed connectives `(Fin n → α) → α`. This is more general (covers description logics, first-order logics) but more complex than needed for cslib's hierarchy.

**Relevance**: The insight about using typeclasses over languages rather than extending inductives is valuable but the arity-indexed approach is overengineered for cslib's use case.

### 3. Extending Inductive Types in Lean 4

[James Oswald's meditation on extending inductives](https://jamesoswald.dev/posts/meditation-extending-inductive-types/) confirms that Lean 4 has **no native way to extend inductive types**. Current workarounds:

- **Metaprogramming**: Auto-generate redundant constructors (complex, fragile)
- **Custom recOn/casesOn**: Generate canonical isomorphisms between subtypes
- **Sum types**: `PropositionalAxiom φ ⊕ ModalAxiomExtra φ` (manual but explicit)

The Foundation project avoids this entirely by using `Set (Formula α)` instead of inductive axiom types.

### 4. Mathlib's Typeclass Diamond Handling

Mathlib faces the same diamond problem extensively. Key patterns:

- **Mixin classes**: Small single-concern classes (e.g., `IsMulLeftCancel`) composed freely
- **`extends` chains with forgetful inheritance**: `CommMonoid extends Monoid extends MulOneClass`
- **Tabled typeclass resolution**: Lean 4's tabled resolution is exponentially faster than Lean 3's in the presence of diamonds
- **Unbundled mixins for ordering**: `OrderedCommMonoid` uses separate `CommMonoid`, `PartialOrder`, and `IsOrderedMonoid` rather than one big class

**Relevance for cslib**: The current `HasAxiom*` mixin pattern is already Mathlib-aligned. The issue is that `PropositionalHilbert` bundles too much (includes `HasAxiomPeirce`).

## Alternative Approaches Compared

### Approach A: Foundation-Style (Axiom Sets as `Set (Formula α)`)

**How it works**: Define axiom schemas as abbreviations. Logics are sets of these schemas. Extension = set union. The derivation tree is parameterized by the axiom set.

```lean
-- Adapting to cslib's style:
structure LogicAxioms (F : Type*) where
  axioms : Set F
  
def IPL : LogicAxioms (Proposition Atom) := ⟨{ Axioms.EFQ φ | φ }⟩
def CPL : LogicAxioms (Proposition Atom) := ⟨IPL.axioms ∪ { Axioms.DNE φ | φ }⟩
def ModalK : LogicAxioms (Modal.Proposition Atom) := ⟨CPL.toModal ∪ { Axioms.AxiomK φ ψ | ... }⟩
```

**Pros**: Maximum flexibility, no axiom duplication, Foundation proves this scales to 20+ logics
**Cons**: Major refactor, loses the nice `extends` typeclass hierarchy, substitution closure must be handled

### Approach B: Typeclass Layering (Min → Int → Cl, current `HasAxiom*` extended)

**How it works**: Split `PropositionalHilbert` into layers:

```lean
class MinimalHilbert (S) extends ModusPonens S, HasAxiomImplyK S, HasAxiomImplyS S
class IntuitionisticHilbert (S) extends MinimalHilbert S, HasAxiomEFQ S
class ClassicalHilbert (S) extends IntuitionisticHilbert S, HasAxiomPeirce S
-- OR: ClassicalHilbert extends MinimalHilbert + HasAxiomDNE (Foundation's approach)
```

**Pros**: Minimal change, preserves current architecture, clear hierarchy
**Cons**: Still duplicates axioms in concrete inductives, derivation trees still separate

### Approach C: Parameterized Derivation Tree with Sum-Type Axioms

**How it works**: A single parameterized derivation tree:

```lean
inductive GenericDerivationTree (AxiomPred : F → Prop) (rules : RuleSet) : List F → F → Type where
  | ax (Γ) (φ) (h : AxiomPred φ) : GenericDerivationTree AxiomPred rules Γ φ
  | assumption ...
  | modus_ponens ...
  | weakening ...
  -- Rules are added by the RuleSet parameter
```

And axiom predicates compose:

```lean
def PropositionalAxiomPred (φ : F) : Prop := ∃ a b, φ = Axioms.ImplyK a b ∨ ...
def ModalAxiomPred (φ : F) : Prop := PropositionalAxiomPred φ ∨ ∃ a b, φ = Axioms.AxiomK a b ∨ ...
```

**Pros**: Single derivation tree codebase, axiom extension is clean
**Cons**: Inference rules (necessitation) vary per logic, hard to parameterize

### Approach D: Theory-Parameterized (ND-style, already in cslib)

**How it works**: The Natural Deduction system already has this pattern:

```lean
-- ND is already parameterized over Theory T
inductive Theory.Derivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u
```

Where `Theory.MPL = ∅`, `Theory.IPL = Set.range (⊥ → ·)`, `Theory.CPL = Set.range (¬¬A → A)`.

**Pros**: Already exists in codebase, very clean extension model
**Cons**: ND-specific (uses impI/impE/botE, not ax/MP), would need adaptation to Hilbert style

## Evidence/Examples from Existing Libraries

| Library | Approach | Int/Cl Split | Extension Pattern | Scale |
|---------|----------|-------------|-------------------|-------|
| Foundation | Axiom sets + Entailment classes | Min → Int → Cl | `sumNormal` / set union | 20+ logics |
| cslib ND | Theory-parameterized | IPL/CPL as Theory | Set.range unions | 3 theories |
| cslib Hilbert | Bundled class + inductives | None (always classical) | `extends` chain | 5 logics |
| Oswald | Language typeclass | N/A | Arity-indexed connectives | Prototype |

## Trade-offs Summary

| Criterion | Approach A (Sets) | Approach B (Layers) | Approach C (Param DT) | Approach D (Theory) |
|-----------|-------------------|---------------------|----------------------|---------------------|
| Refactor size | **Large** | **Small** | **Medium** | **Medium** |
| Axiom duplication | None | Still present | None | None |
| Derivation tree unification | Natural | No | Yes | Separate |
| Typeclass ergonomics | Good (via Has*) | Best (extends) | Good | Good |
| Proof reuse | Excellent | Good | Excellent | Good |
| Foundation precedent | Yes | Partial | No | No |
| Compatibility with existing code | Low | High | Medium | Medium |

## Recommendations

1. **Approach B (Typeclass Layering) is the minimum viable change**: Split `PropositionalHilbert` into `IntuitionisticHilbert` (ImplyK + ImplyS + EFQ + MP) and `ClassicalHilbert` (+ Peirce/DNE). This preserves all existing code and adds the intuitionistic base.

2. **Approach A (Foundation-style) is the gold standard**: If the goal is to support many extensions cleanly, the Foundation project proves this scales. But it requires rethinking the axiom representation from inductives to sets.

3. **Hybrid approach**: Use Approach B for the typeclass hierarchy (IntuitionisticHilbert → ClassicalHilbert → ModalHilbert → ...) but also adopt Approach C's parameterized derivation tree to eliminate axiom/constructor duplication.

4. **The ND system already shows the way**: `Theory.IPL` and `Theory.CPL` in `Defs.lean` demonstrate the intuitionistic/classical split at the theory level. The Hilbert side should mirror this.

## Confidence Level

**High** for the analysis of Foundation's approach (read actual source code).
**High** for the typeclass layering recommendation (directly addresses the task).
**Medium** for the hybrid approach (untested combination, may have unforeseen typeclass issues).
**Low** for the parameterized derivation tree (no existing Lean 4 library does this successfully for heterogeneous rule sets).
