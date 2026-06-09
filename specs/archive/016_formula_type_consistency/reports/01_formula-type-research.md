# Research Report: Add DecidableEq to Modal.Proposition, Resolve LukasiewiczDerived

**Task**: 16
**Date**: 2026-06-08
**Status**: Researched

## Summary

This task involves two small consistency fixes identified in the code review (review-20260608.md, issues #7 and #8):

1. **Add `deriving DecidableEq, BEq` to `Modal.Proposition`** -- straightforward, aligns with all sibling formula types.
2. **Resolve `LukasiewiczDerived` usage** -- the class is defined but never instantiated. The recommended approach is to add a docstring clarifying its intended role rather than instantiating it, since instantiation would provide no value given the current architecture.

## Finding 1: Modal.Proposition Lacks DecidableEq

### Current State

`Modal.Proposition` (defined at `Cslib/Logics/Modal/Basic.lean:46-54`) is the only formula type in the Logics hierarchy that does NOT derive `DecidableEq` and `BEq`.

**Comparison across formula types**:

| Type | File | `deriving DecidableEq, BEq` |
|------|------|-----------------------------|
| `PL.Proposition` | `Cslib/Logics/Propositional/Defs.lean:55` | Yes |
| `Modal.Proposition` | `Cslib/Logics/Modal/Basic.lean:46` | **No** |
| `Temporal.Formula` | `Cslib/Logics/Temporal/Syntax/Formula.lean:43` | Yes |
| `Bimodal.Formula` | `Cslib/Logics/Bimodal/Syntax/Formula.lean:44` | Yes |

### Why It Is Needed

`DecidableEq` is needed for:
- **`Finset` membership**: Contexts (`Ctx`) in natural deduction and proof systems are `Finset (Proposition Atom)`, which requires `DecidableEq` on the element type.
- **`if`/`decide` expressions**: Any decidable conditional on propositions.
- **Task 21 dependency**: Task 21 (port modal proof system ~1,600 lines) explicitly depends on task 16. The modal `DerivationTree` will need `Finset`-based contexts just like propositional natural deduction (`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:70`), requiring `DecidableEq (Modal.Proposition Atom)`.

### Proposed Change

Add `deriving DecidableEq, BEq` after the `Modal.Proposition` inductive definition:

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Proposition Atom)
  | box (φ : Proposition Atom)
deriving DecidableEq, BEq
```

**Constraint**: The derived `DecidableEq` instance will be conditional: `[DecidableEq Atom] -> DecidableEq (Modal.Proposition Atom)`. This matches the behavior of all other formula types (see `PL.Proposition` at `Defs.lean:43` which has `variable {Atom : Type u} [DecidableEq Atom]`).

### Impact Analysis

**Files that import `Modal.Basic`**:
- `Cslib/Logics/Modal/Cube.lean` -- no impact (does not use equality)
- `Cslib/Logics/Modal/Denotation.lean` -- no impact (does not use equality)
- `Cslib/Logics/Propositional/Embedding.lean` -- no impact (defines coercions only)
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` -- no impact (defines coercions only)

**Risk**: None. Adding a `deriving` clause only creates new instances; it does not change existing definitions or proofs. The generated instance is conditional on `[DecidableEq Atom]`, so no new constraints are imposed on existing code that does not use equality.

## Finding 2: LukasiewiczDerived Never Instantiated

### Current State

`LukasiewiczDerived` is defined at `Cslib/Foundations/Logic/Connectives.lean:75-84`:

```lean
class LukasiewiczDerived (F : Type*) [HasBot F] [HasImp F] where
  neg : F -> F := fun phi => HasImp.imp phi HasBot.bot
  top : F := HasImp.imp HasBot.bot HasBot.bot
  or : F -> F -> F := fun phi psi => HasImp.imp (HasImp.imp phi HasBot.bot) psi
  and : F -> F -> F := fun phi psi =>
    HasImp.imp (HasImp.imp phi (HasImp.imp psi HasBot.bot)) HasBot.bot
```

No formula type registers an instance. Instead, each formula type defines its own `abbrev` versions:
- `Modal.Proposition.neg`, `.top`, `.or`, `.and` (Basic.lean:57-68)
- `Bimodal.Formula.neg`, `.top`, `.or`, `.and` (Formula.lean:47-58)
- `Temporal.Formula.neg`, `.top`, `.or`, `.and` (Formula.lean:46-57)
- `PL.Proposition.neg`, `.top`, `.or`, `.and` (Defs.lean:58-69)

### Analysis: Why Not Instantiate?

Instantiating `LukasiewiczDerived` for the formula types would provide no benefit in the current architecture because:

1. **Axioms use `HasBot`/`HasImp` directly**: The polymorphic axioms in `Axioms.lean` spell out derived connectives explicitly (e.g., `HasImp.imp (HasImp.imp phi HasBot.bot) HasBot.bot` for DNE) rather than using `LukasiewiczDerived.neg`. This is the correct approach because `LukasiewiczDerived` is not in the typeclass hierarchy for axioms.

2. **Each type has its own notation**: The scoped notations (e.g., `scoped prefix:40 "neg" => Proposition.neg`) bind to the type-specific `abbrev` definitions, not to `LukasiewiczDerived` fields. Changing this would break existing proofs.

3. **`abbrev` is definitionally equal**: The current `abbrev` definitions are definitionally equal to what `LukasiewiczDerived` would provide. There is no semantic gap.

4. **Potential future role**: `LukasiewiczDerived` could be useful if a future polymorphic proof system needs to abstract over derived connectives uniformly (e.g., a polymorphic `HasNeg` or `HasOr` typeclass). But this is speculative and the class design would likely change.

### Recommended Action

Add a docstring to `LukasiewiczDerived` explaining its status:

```lean
/-- Lukasiewicz-style derived connectives from `bot` and `imp`.
    Provides `neg`, `top`, `or`, `and` as abbreviations.

    **Status**: Currently not instantiated. Each concrete formula type defines
    its own `abbrev` versions of these connectives directly, which are
    definitionally equal to these defaults. This class is retained for
    potential future use in polymorphic proof system abstractions. -/
```

This is preferable to:
- **Deleting it**: It documents a design pattern and may be useful later.
- **Instantiating it**: Would add instances that no code uses, increasing typeclass search overhead for no benefit.

## Implementation Plan

### Phase 1: Add DecidableEq to Modal.Proposition

**File**: `Cslib/Logics/Modal/Basic.lean`
**Change**: Add `deriving DecidableEq, BEq` after line 54 (the closing of the `Proposition` inductive)

**Verification**: `lake build Cslib.Logics.Modal.Basic` and then `lake build` for full project.

### Phase 2: Update LukasiewiczDerived Docstring

**File**: `Cslib/Foundations/Logic/Connectives.lean`
**Change**: Replace the docstring on lines 73-74 with an expanded version noting the class is currently uninstantiated and explaining why.

**Verification**: `lake build Cslib.Foundations.Logic.Connectives`

### Estimated Effort

Both changes are trivial one-line (Phase 1) and docstring-only (Phase 2) modifications. Total effort: under 15 minutes.

## Downstream Dependencies

Task 21 (port modal proof system) depends on task 16. With `DecidableEq` added, the modal `DerivationTree` can use `Finset`-based contexts (`Ctx Atom := Finset (Modal.Proposition Atom)`), mirroring the propositional natural deduction architecture.

No other tasks are blocked by this change.
