# Research Report: Port Conservative Extension to cslib

## Task Overview

Port 4 files from `BimodalLogic/Theories/Bimodal/Metalogic/ConservativeExtension/` to
`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/` in the cslib project.

**Source**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/ConservativeExtension/`
**Target**: `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/`

## Source File Analysis

### Line Counts (Actual)

| File | Lines | Description |
|------|-------|-------------|
| ExtFormula.lean | 353 | Extended formula type with `ExtAtom := Atom + Unit` |
| ExtDerivation.lean | 287 | Extended axioms, derivation trees, embedding |
| Substitution.lean | 262 | Substitution `sigma[q -> bot]` and closure properties |
| Lifting.lean | 697 | Lifting infrastructure: `liftDerivationWith`, `lift_derivation_qfree` |
| **Total** | **1,599** | |

### Sorry Status

**Zero sorry occurrences** in all 4 source files. All proofs are complete.

### Key Definitions and Theorems

#### ExtFormula.lean
- `ExtAtom := Atom + Unit` -- extended atom type with one fresh atom
- `freshAtom : ExtAtom := Sum.inr ()` -- the fresh atom
- `ExtFormula` -- inductive type mirroring `Formula` over `ExtAtom`
- `embedAtom : Atom -> ExtAtom := Sum.inl` -- atom embedding
- `embedFormula : Formula -> ExtFormula` -- structural formula embedding
- `embedFormula_injective` -- key injectivity theorem
- `fresh_not_in_embedFormula_atoms` -- critical freshness lemma
- 14 simp lemmas for embedding preservation of derived operators

#### ExtDerivation.lean
- `ExtAxiom : ExtFormula -> Type` -- 42 axiom constructors mirroring base `Axiom`
- `ExtAxiom.minFrameClass` -- frame class assignment
- `ExtDerivationTree fc : ExtContext -> ExtFormula -> Type` -- 7 inference rules
- `embedAxiom` -- lift base axioms to extended axioms (42 cases)
- `embedDerivation` -- lift base derivation trees to extended (7 recursive cases)

#### Substitution.lean
- `substFormula : ExtFormula -> ExtFormula` -- replace `freshAtom` with `bot`
- `substAxiom` -- axiom schema closure under substitution (42 cases)
- `substFormula_preserves_qfree` -- q-free formulas are fixed points
- `substFormula_of_embedded` -- embedded formulas unchanged
- `substFormula_idempotent` -- substitution is idempotent

#### Lifting.lean (most complex)
- `unembedFormula : ExtFormula -> Formula` -- partial inverse of embedding
- `unembed_embed` -- left-inverse property
- `embed_unembed_qfree` -- right-inverse for q-free formulas
- `substFreshWith a : ExtFormula -> ExtFormula` -- replace `freshAtom` with `Sum.inl a`
- `substAxiomFresh` -- axiom closure under parameterized substitution (42 cases)
- `unembedAxiom` -- convert `ExtAxiom` to base `Axiom` (42 cases)
- `collectDerivInl` -- collect all `Sum.inl` atoms from derivation tree
- `liftDerivationWith` -- combined lifting function (7 recursive cases)
- **`lift_derivation_qfree`** -- **main conservative extension theorem**

## Critical Porting Differences

### 1. Polymorphic Atom Type (HIGH IMPACT)

**Source** (BimodalLogic): `Formula` uses concrete `Atom` (struct with `base : String` and `fresh_index : Option Nat`).
- `ExtAtom := Atom + Unit` is straightforward since `Atom` is concrete.
- `Infinite Atom` needed for `exists_fresh_atom` -- source has this via injection of `Nat`.

**Target** (cslib): `Formula (Atom : Type u)` is universe-polymorphic.
- `ExtAtom` must be defined as `Atom + Unit` where `Atom` is a type parameter.
- `Infinite Atom` must be a typeclass constraint (not inherent).
- The `exists_fresh_atom` function requires `[Infinite Atom]` and `[DecidableEq Atom]`.
- The `Countable` deriving on `ExtFormula` needs `[Countable Atom]`.
- The `Hashable` instance on `ExtAtom` needs `[Hashable Atom]`.

**Porting strategy**: Add `variable {Atom : Type u} [DecidableEq Atom]` throughout.
Add `[Infinite Atom]` where freshness is needed (mainly Lifting.lean).
Add `[Countable Atom]` if deriving Countable is needed.

### 2. Axiom Name Differences (MEDIUM IMPACT)

The cslib `Axiom` type uses different names for the first three propositional axioms:

| BimodalLogic | cslib | Formula |
|-------------|-------|---------|
| `prop_k` | `imp_k` | `(p -> (q -> r)) -> ((p -> q) -> (p -> r))` |
| `prop_s` | `imp_s` | `p -> (q -> p)` |
| `ex_falso` | `efq` | `bot -> p` |

All other 39 axiom names are identical. The `embedAxiom`, `substAxiom`, `substAxiomFresh`,
`liftAxiom`, and `unembedAxiom` functions each have 42 match arms that must use the cslib names.

### 3. Missing `always`/`sometimes` Definitions (LOW IMPACT)

The source defines `ExtFormula.always` and `ExtFormula.sometimes` but these are
**not used** in any axiom schema or theorem statement. They are only convenience definitions.
The cslib `Formula` type does not define `always`/`sometimes`.

**Strategy**: Include these as local definitions in `ExtFormula` since they're self-contained.

### 4. Namespace Convention (MECHANICAL)

| BimodalLogic | cslib |
|-------------|-------|
| `Bimodal.Metalogic.ConservativeExtension` | `Cslib.Logic.Bimodal.Metalogic.ConservativeExtension` |
| `Bimodal.Syntax` | `Cslib.Logic.Bimodal` |
| `Bimodal.ProofSystem` | `Cslib.Logic.Bimodal` |
| `open Bimodal.Syntax` | `open Cslib.Logic.Bimodal` |
| `open Bimodal.ProofSystem` | `open Cslib.Logic.Bimodal` |

### 5. Import Changes (MECHANICAL)

| Source Import | cslib Import |
|--------------|-------------|
| `import Bimodal.Syntax.Formula` | `import Cslib.Logics.Bimodal.Syntax.Formula` |
| `import Bimodal.ProofSystem.Derivation` | `import Cslib.Logics.Bimodal.ProofSystem.Derivation` |
| `import Bimodal.Metalogic.ConservativeExtension.ExtFormula` | `import Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ExtFormula` |
| `import Bimodal.Metalogic.ConservativeExtension.ExtDerivation` | `import Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ExtDerivation` |
| `import Bimodal.Metalogic.ConservativeExtension.Substitution` | `import Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.Substitution` |
| `import Mathlib.Tactic.DeriveCountable` | Keep or check if needed |
| `import Mathlib.Data.Countable.Basic` | Keep or check if needed |

### 6. `module` Declaration

cslib files use `module` declaration (see Formula.lean, Context.lean). The ported files
should include this where appropriate for public API files.

### 7. `@[expose] public section` Pattern

cslib uses `@[expose] public section` for public-facing definitions (see Formula.lean,
Context.lean). The conservative extension files should follow this pattern for publicly
exported definitions.

## Dependency Analysis

### Task 4 (ProofSystem) Status

Task 4 is listed as a dependency. Checking the existing cslib codebase:
- `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean` -- EXISTS with all 42 axiom constructors
- `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` -- EXISTS with all 7 inference rules
- `Cslib/Logics/Bimodal/ProofSystem/Derivable.lean` -- EXISTS
- `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` -- EXISTS
- `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` -- EXISTS
- `Cslib/Logics/Bimodal/ProofSystem/LinearityDerivedFacts.lean` -- EXISTS

**Task 4 is fully merged and available.** All required dependencies exist.

### Internal Dependencies (File Order)

```
ExtFormula.lean
    |
    v
ExtDerivation.lean  (depends on ExtFormula + ProofSystem/Derivation)
    |
    v
Substitution.lean   (depends on ExtFormula + ExtDerivation)
    |
    v
Lifting.lean        (depends on Substitution, transitively all above)
```

### External Dependencies

All external dependencies are available in cslib:
- `Cslib.Logics.Bimodal.Syntax.Formula` -- `Formula`, `Formula.atoms`, `Formula.swap_temporal`
- `Cslib.Logics.Bimodal.Syntax.Context` -- `Context` type alias
- `Cslib.Logics.Bimodal.ProofSystem.Axioms` -- `Axiom`, `FrameClass`, `Axiom.minFrameClass`
- `Cslib.Logics.Bimodal.ProofSystem.Derivation` -- `DerivationTree`
- `Mathlib.Data.Finset.Basic` -- `Finset` operations
- `Mathlib.Data.Countable.Basic` -- `Countable` class (if deriving is used)

## Proof Strategy Summary

The conservative extension result (`lift_derivation_qfree`) proves:

> If `ExtDerivationTree fc (L.map embedFormula) (embedFormula phi)` (an extended
> derivation of an embedded formula from embedded assumptions), then
> `Nonempty (DerivationTree fc L phi)` (there exists a base derivation).

The proof strategy (Goldblatt 1992):
1. **Embed** base formulas into extended formulas via `embedFormula` (injects `Atom` as `Sum.inl`)
2. **Define substitution** `sigma[q -> bot]` replacing the fresh atom `Sum.inr ()` with `bot`
3. **Show axiom closure**: all 42 axiom schemas are closed under substitution
4. **Choose fresh atom**: collect all `Sum.inl` atoms in the derivation tree, choose `a` not among them
5. **Apply `substFreshWith a`**: replace `Sum.inr ()` with `Sum.inl a` throughout
6. **Unembed**: convert the resulting derivation tree back to the base language

The freshness argument ensures that the chosen `a` does not collide with any atom already
used in the derivation, preserving all irreflexivity-type reasoning.

## Porting Strategy

### Phase 1: ExtFormula.lean
- Port the `ExtFormula` inductive type, parameterized over `Atom`
- Port `embedAtom`, `embedFormula`, all simp lemmas
- Port `embedFormula_injective`, `fresh_not_in_embedFormula_atoms`
- Add typeclass constraints: `[DecidableEq Atom]` for `Finset` operations, `[Hashable Atom]` for `Hashable` instance
- Rename namespace to `Cslib.Logic.Bimodal.Metalogic.ConservativeExtension`
- Add copyright header and `module` declaration

### Phase 2: ExtDerivation.lean
- Port `ExtAxiom` inductive (rename `prop_k` -> `imp_k`, `prop_s` -> `imp_s`, `ex_falso` -> `efq`)
- Port `ExtDerivationTree` inductive
- Port `embedAxiom` (42 cases, name changes)
- Port `embedDerivation` (7 recursive cases)

### Phase 3: Substitution.lean
- Port `substFormula`, all simp lemmas
- Port `substAxiom` (42 cases, name changes)
- Port `substFormula_preserves_qfree`, `substFormula_of_embedded`, `substFormula_idempotent`
- Port `substFormula_map_embedded`

### Phase 4: Lifting.lean
- Port `unembedFormula`, `unembed_embed`, `embed_unembed_qfree`
- Port `substFreshWith`, `substAxiomFresh` (42 cases)
- Port `unembedAxiom` (42 cases)
- Port `collectDerivInl`, `liftDerivationWith` (7 recursive cases)
- Port `lift_derivation_qfree` -- requires `[Infinite Atom]` constraint
- Port `exists_fresh_atom` -- uses `Infinite.exists_notMem_finset`

### Phase 5: Verification
- Run `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension`
- Verify zero sorry occurrences
- Run linter checks

## Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| Polymorphic Atom complicates type inference | Medium | Add explicit type annotations where needed |
| 42-case axiom matches repeated 5 times | Low | Mechanical but tedious; copy-paste with find/replace |
| `Countable` deriving may not work with polymorphic Atom | Low | Use explicit instance with `[Countable Atom]` |
| `Hashable ExtAtom` instance needs adjustment | Low | Parameterize over `[Hashable Atom]` |
| Universe polymorphism in `DerivationTree` | Low | Follow existing cslib patterns |

## Estimated Effort

The porting is primarily mechanical:
- ~80% is namespace/import renaming and axiom name changes
- ~15% is adding typeclass constraints for the polymorphic Atom
- ~5% is adjusting proofs for cslib's slightly different API

Estimated ported line count: ~1,600-1,700 lines (slight increase due to copyright headers,
module declarations, and typeclass constraints).

## Blockers

**None.** Task 4 (ProofSystem) is fully merged and available. All Mathlib dependencies
are present. Source files have zero sorry occurrences.
