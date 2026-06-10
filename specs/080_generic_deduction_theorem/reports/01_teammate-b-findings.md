# Teammate B Findings: Alternative Design Patterns for Generic Deduction Theorem

**Task**: 80 — Generic DeductionTheorem interface across all logic domains
**Date**: 2026-06-10
**Angle**: Alternative approaches beyond typeclasses; prior art survey

## Key Findings

### 1. The Exact Diff Is Tiny

A side-by-side diff of PL vs Modal DeductionTheorem reveals that the **actual logic** is identical. The only differences are:

- **Type names**: `PL.Proposition` vs `Proposition` vs `Formula`; `PropositionalAxiom` vs `ModalAxiom` vs `Axiom`
- **Extra constructor cases**: Modal adds 1 (`necessitation`), Temporal adds 2 (`temporal_necessitation`, `temporal_duality`), Bimodal adds 3 (all three). Every extra case is discharged identically: `simp at hA` (context is `[]`, but `A ∈ []` is impossible)
- **Axiom constructor naming**: PL uses `.implyK`, Modal uses `.implyK`, Temporal uses `.imp_s`, Bimodal uses `.imp_s` / `.imp_k`
- **Weakening proof style**: PL/Modal use `fun _ h => nomatch h`; Temporal/Bimodal use `List.nil_subset _`
- **FrameClass parameter**: Temporal/Bimodal have an extra `{fc : FrameClass}` parameter; PL/Modal don't

The core proof structure (helpers, recursion, termination) is 100% shared.

### 2. Five Alternative Approaches Evaluated

#### Alternative A: Parametric Function with Constructor-Handler Callback

**Idea**: Write `deduction_theorem` as a plain function parameterized by the extra-constructor handler, not a typeclass.

```lean
noncomputable def generic_deduction_theorem
    {F : Type*} [DecidableEq F] [HasImp F]
    {D : List F → F → Type*}
    (handle_ax : ∀ Γ A φ, ... → D Γ (HasImp.imp A φ))
    (handle_mp : ∀ Γ A φ ψ, D Γ ... → D Γ ... → D Γ ...)
    ...
    (handle_extras : ∀ Γ' A φ (d : D Γ' φ) (hA : A ∈ Γ'),
        IsExtraConstructor d → D (removeAll Γ' A) (HasImp.imp A φ))
    (Γ : List F) (A B : F) (d : D (A :: Γ) B) :
    D Γ (HasImp.imp A B) := ...
```

**Pros**: No typeclass overhead; clear dependency injection; each logic passes its handler at the call site.
**Cons**: Cannot pattern-match on an abstract `D : List F → F → Type*` — Lean requires concrete inductives for `match`. This is the **fatal flaw**: you cannot recurse over an abstract type family without a concrete inductive or a recursor. The well-founded recursion on `d.height` also requires `d` to be a concrete inductive value.

**Verdict**: ❌ Not feasible without wrapping in a typeclass/structure anyway.

#### Alternative B: Typeclass with Abstract Recursor

**Idea**: Define a typeclass that provides the `match`/`casesOn` recursor abstractly.

```lean
class HasDerivationTree (F : Type*) [HasImp F] where
  Tree : List F → F → Type*
  height : Tree Γ φ → Nat
  casesOn : Tree Γ φ →
    (ax : ∀ ...) →
    (assumption : ∀ ...) →
    (mp : ∀ ...) →
    (weakening : ∀ ...) →
    (extra : ∀ ...) →
    Motive
```

**Pros**: Clean abstraction; each logic only provides the `casesOn` implementation.
**Cons**: Defining the `casesOn` type signature is extremely complex — it must handle all possible motive types, intermediate goal states, and the well-founded recursion termination proof. The motive-based recursor pattern works for simple cases but becomes unwieldy for mutual recursion (`deduction_with_mem` + `deduction_theorem`).

**Verdict**: ⚠️ Theoretically possible but very hard to get right. The `casesOn` signature would be enormous and fragile.

#### Alternative C: Structure-Based Approach (Recommended)

**Idea**: A `structure` (not class) that bundles the derivation tree type with its operations, where each logic instantiates the structure explicitly. The generic proof takes the structure as an explicit argument.

```lean
structure DeductionTreeOps (F : Type*) [HasImp F] where
  Tree : List F → F → Type*
  height : Tree Γ φ → Nat
  ax_intro : ∀ Γ φ, IsAxiom φ → Tree [] φ
  assumption_intro : ∀ Γ φ, φ ∈ Γ → Tree Γ φ
  mp_intro : ∀ Γ φ ψ, Tree Γ (imp φ ψ) → Tree Γ φ → Tree Γ ψ
  weakening_intro : ∀ Γ Δ φ, Tree Γ φ → Γ ⊆ Δ → Tree Δ φ
  imp_k : ∀ Γ φ ψ, Tree Γ (imp φ (imp ψ φ))  -- from axiom
  imp_s : ∀ Γ φ ψ χ, Tree Γ (imp (imp φ (imp ψ χ)) ...)
  -- For the extra constructors:
  extra_empty_ctx : ∀ φ (d : Tree Γ' φ) (hA : A ∈ Γ'),
      IsExtraConstructor d → False  -- extra constructors require Γ' = []
  height_mp_left : ...
  height_mp_right : ...
  height_weakening : ...
```

**Pros**: Explicit, no typeclass resolution overhead; structure fields are straightforward; each logic fills in the concrete operations.
**Cons**: Still can't pattern-match on `Tree` without a concrete type. The recursion in `deduction_with_mem` and `deduction_theorem` fundamentally needs to destructure the derivation tree.

**Verdict**: ⚠️ Same fundamental problem as Alternative A — you need to pattern match on the concrete inductive type.

#### Alternative D: Tactic/Macro-Level Abstraction

**Idea**: Write a custom Lean 4 macro or tactic that generates the deduction theorem proof for a given logic, parameterized by the constructor list.

```lean
-- A macro that generates the full deduction theorem given:
-- 1. The formula type
-- 2. The derivation tree type
-- 3. The axiom constructor names
-- 4. The list of extra constructors (all discharged by `simp at hA`)
macro "derive_deduction_theorem" formula:ident tree:ident axiom_type:ident
    extras:ident* : command => ...
```

**Pros**: Zero runtime overhead; generates idiomatic domain-specific code; easily extensible to new logics.
**Cons**: Requires significant Lean 4 metaprogramming expertise; harder to maintain and debug than plain Lean; the generated code is not visible for review; does not reduce the number of definitions, just automates their creation.

**Verdict**: ⚠️ Technically viable but high implementation cost and maintenance burden. Not idiomatic for a math library.

#### Alternative E: Typeclass on DerivationTree with Match-Based Dispatch

**Idea** (the approach the task description suggests): A typeclass that exposes constructors, height, and height lemmas, plus a list of "extra constructors" that are all vacuously impossible with non-empty context. The generic proof uses the typeclass methods instead of direct pattern matching.

```lean
class HasDerivationTree (F : Type*) [HasImp F] where
  Tree : List F → F → Type*
  height : Tree Γ φ → Nat
  -- Elimination into cases (each case returns a dependent sum)
  cases : Tree Γ φ → DerivationCase F Tree Γ φ
  -- Height lemmas
  height_mp_left : ...
  height_mp_right : ...
  height_weakening : ...

inductive DerivationCase (F : Type*) (Tree : List F → F → Type*)
    (Γ : List F) (φ : F) where
  | ax : IsAxiom φ → DerivationCase ...
  | assumption : φ ∈ Γ → DerivationCase ...
  | mp : (ψ : F) → Tree Γ (imp ψ φ) → Tree Γ ψ → DerivationCase ...
  | weakening : (Γ' : List F) → Tree Γ' φ → Γ' ⊆ Γ → DerivationCase ...
  | extraEmptyCtx : Γ = [] → Tree [] φ → DerivationCase ...
```

**Pros**: The key insight — define a **shared case-analysis type** `DerivationCase` that captures the common 4 constructors plus a catch-all "extra" case. Each logic's `cases` function maps its concrete constructors to this shared type. The generic proof pattern-matches on `DerivationCase` (a concrete inductive) rather than on the abstract `Tree`.

**Cons**: Adds a level of indirection (the `cases` function); the `extraEmptyCtx` case still needs careful handling; axiom representation needs abstraction.

**Verdict**: ✅ This is the most viable approach. It solves the fundamental "can't match on abstract types" problem by introducing a shared intermediate type.

### 3. Prior Art Survey

#### FormalizedFormalLogic/Foundation (iehality/lean4-logic)

The major Lean 4 multi-logic formalization project. It covers Propositional, First-Order, Modal, and Provability logics. **Key finding: it does NOT share deduction theorem proofs across logics.** Each logic system proves its own completeness independently. This is the most directly comparable project to cslib, and it chose not to attempt generic deduction theorem abstraction.

#### Mathlib4 ModelTheory

Uses a `Language` type parameterized by function/relation arities, with `Language.Structure` typeclass for interpretation. The abstraction strategy is: define syntax generically over `Language`, then prove properties about arbitrary languages. However, this works because first-order logic has a **single uniform syntax** — there's no analogue of "some logics have extra constructors."

The key Mathlib pattern relevant here: **define a shared inductive type for the common cases, then let each domain provide a mapping from its concrete type into the shared type**.

#### James Oswald's Typeclass for Logic Formulae

Oswald defines a `Language α` typeclass parameterizing over n-ary connective families. The approach is more about formula syntax than proof theory. His key insight matches our situation: "Lean does not have a nice natural way to extend inductive types" — so you must use typeclasses or structures to abstract over them.

His "meditation on extending inductive types" suggests automatic generation of `casesOn` functions via metaprogramming as the most promising approach — exactly the `cases` field in Alternative E.

#### LeanLTL (ITP 2025)

A unifying framework for linear temporal logics. Uses parametric types and typeclass-based semantics but focuses on model-checking properties, not Hilbert-system metatheory.

#### Datatype-Generic Programming (Nathan McRae)

Explores the `Fix` functor pattern for abstracting over inductive type shapes. While theoretically elegant, requires `unsafe` in Lean 4 and is not suitable for proof-carrying code.

### 4. The Fundamental Constraint

**You cannot pattern-match on an abstract type in Lean 4.** This is the single most important constraint for this design. Lean's `match` expression requires a concrete inductive type. This means:

- Pure parametric/callback approaches (A, C) fail
- You MUST introduce either a concrete shared inductive (Alternative E's `DerivationCase`) or use a recursor-style API (Alternative B)
- The `DerivationCase` approach is strictly simpler than the full recursor approach

### 5. Axiom Abstraction Challenge

The four logics use different axiom types (`PropositionalAxiom`, `ModalAxiom`, `Axiom` for Temporal/Bimodal). The deduction theorem proof doesn't care about axiom content — it only needs:

1. An axiom derivation: `Tree [] φ` from an axiom witness
2. The `implyK` axiom: `Tree [] (imp φ (imp ψ φ))` for any `φ`, `ψ`
3. The `implyS` axiom: `Tree [] (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))` for any `φ`, `ψ`, `χ`

These can be required as typeclass/structure fields without exposing the axiom type at all.

### 6. FrameClass Complication

Temporal and Bimodal have a `{fc : FrameClass}` parameter on `DerivationTree`; PL and Modal don't. Options:

- **Option A**: Use a universe-polymorphic "trivial frame class" `Unit` for PL/Modal, with all operations ignoring it
- **Option B**: Make FrameClass an optional parameter with a default
- **Option C**: Simply parameterize the generic proof over an extra type parameter that PL/Modal set to `Unit`

Option C is simplest and avoids changing existing definitions.

## Recommended Approach

**Alternative E: Typeclass with shared `DerivationCase` inductive**, combined with these design decisions:

1. Define `DerivationCase` as a shared inductive in `Foundations/Logic/`
2. Define a `HasDerivationTree` typeclass with `Tree`, `height`, `cases : Tree Γ φ → DerivationCase ...`, and required axiom derivations (`implyK`, `implyS`)
3. Write the generic `deduction_theorem` and `deduction_with_mem` once, pattern-matching on `DerivationCase`
4. Each logic provides a `HasDerivationTree` instance whose `cases` function maps concrete constructors to `DerivationCase`, collapsing all extra constructors into `extraEmptyCtx`
5. Each logic's `DeductionTheorem.lean` reduces to ~20-30 lines: the instance + a one-line invocation

**Why not pure typeclasses without `DerivationCase`?** Because you need to pattern-match somewhere, and Lean won't let you match on an abstract type. The `DerivationCase` indirection is the minimal price.

**Why not a tactic/macro?** Higher maintenance cost, less transparent, and doesn't reduce conceptual complexity — just hides the duplication behind metaprogramming.

**Why not the parametric callback approach?** Fatal flaw: can't recurse over an abstract type in Lean 4.

## Confidence Level

**High** on the overall approach (typeclass + shared case type).
**Medium** on the exact API surface — the `DerivationCase` definition needs careful design to handle:
- The `weakening` case's recursive structure (subderivation of strictly smaller height)
- The `extraEmptyCtx` proof obligation (each logic must prove its extras require `Γ = []`)
- Well-founded recursion termination using the abstract `height` function

The main risk is that Lean 4's well-founded recursion checker may struggle with the abstract `height` measure. If it does, a `WellFoundedRelation` instance on the abstract `Tree` type (provided by the typeclass) should resolve it.

## Sources

- [James Oswald: A Simple Typeclass for Logic Formulae in Lean4](https://jamesoswald.dev/posts/a-type-class-for-logic/)
- [James Oswald: A Meditation on Extending Inductive Types in Lean4](https://jamesoswald.dev/posts/meditation-extending-inductive-types/)
- [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation)
- [Mathlib ModelTheory Semantics](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Semantics.html)
- [LeanLTL: A Unifying Framework for Linear Temporal Logics in Lean](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.37)
- [Nathan McRae: Datatype-Generic Programming in Lean4](https://nathanmcrae.name/blog/datatype-generic-programming-in-lean4.html)
- [Lean 4 Inductive Types Reference](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)
- [Lean 4 Induction and Recursion](https://docs.lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html)
