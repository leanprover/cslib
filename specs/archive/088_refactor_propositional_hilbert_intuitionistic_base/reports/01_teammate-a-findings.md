# Teammate A Findings: Primary Architecture for Intuitionistic Base with Uniform Extensions

**Task**: 88 — Refactor propositional Hilbert system to intuitionistic base with uniform extension architecture
**Date**: 2026-06-10
**Angle**: Primary implementation approach

## Key Findings

### 1. The Current Architecture Already Has the Right Atoms

The existing codebase already follows a "fine-grained axiom typeclass" pattern that is almost perfectly suited for an intuitionistic refactoring:

- **Individual axiom typeclasses**: `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`, `HasAxiomDNE`, `HasAxiomK`, `HasAxiomT`, `HasAxiom4`, `HasAxiomB`, `HasAxiom5`, `HasAxiomD`, plus all temporal axioms
- **Inference rule typeclasses**: `ModusPonens`, `Necessitation`, `TemporalNecessitation`
- **Bundled classes**: `PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`

The problem is entirely in the **bundled layer**: `PropositionalHilbert` is defined as classical (includes `HasAxiomPeirce`), and everything extends it.

### 2. Many Theorems Don't Actually Need Peirce

Critical finding: `Combinators.lean` (the foundational theorem file) is parameterized over `[PropositionalHilbert S]` but **never uses** `HasAxiomPeirce` or `HasAxiomEFQ`. The combinators (`imp_trans`, `identity`, `b_combinator`, `flip`, `app1`, `app2`, `pairing`, `dni`) only need `ModusPonens + HasAxiomImplyK + HasAxiomImplyS`.

Similarly, `BigConj.lean` requires `PropositionalHilbert` but likely only needs the minimal/intuitionistic fragment.

The classical axiom is actually needed in:
- `Core.lean`: `double_negation`, `raa`, `efq_neg`, `rcp`, `lce_imp`, `rce_imp` (these use Peirce directly)
- `Connectives.lean`: `classical_merge`, De Morgan laws (these use Peirce via `double_negation` and `lce_imp`/`rce_imp`)

### 3. FormalizedFormalLogic/Foundation Uses a Three-Level Hierarchy

The Foundation project uses:

```
Minimal := ModusPonens + NegationEquiv + HasAxiomVerum 
         + HasAxiomImplyK + HasAxiomImplyS
         + HasAxiomAndElim + HasAxiomAndInst
         + HasAxiomOrInst + HasAxiomOrElim

Int extends Minimal, HasAxiomEFQ

Cl extends Minimal, HasAxiomDNE
```

Key differences from cslib:
- Foundation has primitive `∧`/`∨` connectives with separate axioms; cslib uses Lukasiewicz encoding (derived from `→`/`⊥`)
- Foundation's `Cl` extends `Minimal` directly (not `Int`), using `HasAxiomDNE` rather than Peirce
- Foundation's modal `Hilbert.Normal` is parameterized over an **axiom set** `Ax` (a `Set (Formula α)`), not via typeclasses — each logic is `Normal Ax` for a different `Ax`

### 4. The Extension Pattern in cslib Is Uniform

The current cslib pattern for extending logics is:

```
BaseLogic = PropBase + [extra rules] + [extra axiom typeclasses]
```

This is seen in:
- `ModalHilbert` = `PropositionalHilbert` + `Necessitation` + `HasAxiomK`
- `ModalS5Hilbert` = `ModalHilbert` + `HasAxiomT` + `HasAxiom4` + `HasAxiomB`
- `TemporalBXHilbert` = `PropositionalHilbert` + `TemporalNecessitation` + 22 temporal axiom classes
- `BimodalTMHilbert` = `ModalS5Hilbert` + `TemporalBXHilbert` + `HasAxiomMF`

The refactoring simply needs to insert intuitionistic logic between minimal logic and the current `PropositionalHilbert`, following this same pattern.

### 5. The ND System Already Models the IPL/CPL Distinction

In `NaturalDeduction/Basic.lean`, there are already:
- `Theory.MPL` (minimal — empty theory)
- `Theory.IPL` (intuitionistic — adds EFQ)
- `Theory.CPL` (classical — adds DNE)
- `IsIntuitionistic` / `IsClassical` typeclasses

This confirms the three-level hierarchy is the right design for the Hilbert system too.

## Recommended Approach: Option B (Three-Level Hierarchy)

### Design

```lean
/-- Minimal propositional Hilbert system: K + S + MP. -/
class MinimalHilbert (S : Type*) [HasBot F] [HasImp F]
    [InferenceSystem S F]
    extends ModusPonens S (F := F),
            HasAxiomImplyK S (F := F),
            HasAxiomImplyS S (F := F)

/-- Intuitionistic propositional Hilbert system: Minimal + EFQ. -/
class IntuitionisticHilbert (S : Type*) [HasBot F] [HasImp F]
    [InferenceSystem S F]
    extends MinimalHilbert S (F := F),
            HasAxiomEFQ S (F := F)

/-- Classical propositional Hilbert system: Intuitionistic + Peirce. -/
class ClassicalHilbert (S : Type*) [HasBot F] [HasImp F]
    [InferenceSystem S F]
    extends IntuitionisticHilbert S (F := F),
            HasAxiomPeirce S (F := F)
```

### Why Three Levels (Not Two)

1. **MinimalHilbert** enables the most theorem reuse. Combinators like `imp_trans`, `identity`, `b_combinator`, `flip`, `app1`, `app2`, `pairing`, `dni` are all valid in minimal logic (no EFQ needed). Having this level means these theorems can be used by ANY system extending MinimalHilbert.

2. **IntuitionisticHilbert** is the natural base for most logic extensions. Modal logic K, temporal BX, etc. are all classically presented, but many of their propositional underpinnings only need intuitionistic logic.

3. **ClassicalHilbert** adds the strictly classical principles. `double_negation`, `raa`, `rcp`, `lce_imp`, `rce_imp`, `classical_merge`, De Morgan laws all genuinely require Peirce.

### Refactoring the Extension Chain

```lean
-- Modal logics extend IntuitionisticHilbert (not ClassicalHilbert!)
-- because the modal axioms themselves don't require Peirce.
-- Classical modal logics can separately extend ClassicalHilbert.

class ModalHilbertK (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends IntuitionisticHilbert S (F := F),
            Necessitation S (F := F),
            HasAxiomK S (F := F)

-- For the current S5 system (which is classical):
class ModalS5Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ClassicalHilbert S (F := F),
            Necessitation S (F := F),
            HasAxiomK S (F := F),
            HasAxiomT S (F := F),
            HasAxiom4 S (F := F),
            HasAxiomB S (F := F)

-- Temporal BX extends ClassicalHilbert (since BX is classical)
class TemporalBXHilbert (S : Type*) [HasBot F] [HasImp F] [HasUntil F]
    [HasSince F] [InferenceSystem S F]
    extends ClassicalHilbert S (F := F),
            TemporalNecessitation S (F := F),
            -- ... all 22 temporal axiom classes
```

### Refactoring the Theorem Files

The key change is to **stratify** the theorem variable blocks:

```lean
-- Combinators.lean: only needs MinimalHilbert
variable [MinimalHilbert S (F := F)]

-- Core.lean (intuitionistic fragment): needs IntuitionisticHilbert
section Intuitionistic
variable [IntuitionisticHilbert S (F := F)]
theorem efq_axiom ...
-- intuitionistic theorems that use EFQ but not Peirce
end Intuitionistic

-- Core.lean (classical fragment): needs ClassicalHilbert
section Classical
variable [ClassicalHilbert S (F := F)]
theorem peirce_axiom ...
theorem double_negation ...
theorem raa ...
theorem lce_imp ...
theorem rce_imp ...
end Classical
```

### Tag Type Updates

```lean
-- Add new tag types
opaque Propositional.HilbertMin : Type := Empty   -- Minimal
opaque Propositional.HilbertInt : Type := Empty   -- Intuitionistic
-- Rename existing:
-- Propositional.HilbertCl stays as-is (Classical)

-- More modal tags for K (not just S5)
opaque Modal.HilbertK : Type := Empty    -- already exists
```

### Concrete Axiom Inductives

The axiom inductives should also be stratified:

```lean
-- Minimal axioms (shared by all)
inductive MinimalAxiom : PL.Proposition Atom → Prop where
  | implyK (φ ψ) : MinimalAxiom (φ.imp (ψ.imp φ))
  | implyS (φ ψ χ) : MinimalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))

-- Intuitionistic adds EFQ
inductive IntuitionisticAxiom : PL.Proposition Atom → Prop where
  | minimal (h : MinimalAxiom φ) : IntuitionisticAxiom φ
  | efq (φ) : IntuitionisticAxiom (Proposition.bot.imp φ)

-- Classical adds Peirce  
inductive ClassicalAxiom : PL.Proposition Atom → Prop where
  | intuitionistic (h : IntuitionisticAxiom φ) : ClassicalAxiom φ
  | peirce (φ ψ) : ClassicalAxiom (((φ.imp ψ).imp φ).imp φ)
```

This nesting pattern (each level embeds the previous via a constructor) is clean and follows the same pattern that could be used for modal extensions:

```lean
inductive ModalKAxiom : Modal.Proposition Atom → Prop where
  | intuitionistic (h : IntuitionisticAxiom (embed φ)) : ModalKAxiom φ  -- or duplicated
  | modalK (φ ψ) : ModalKAxiom (□(φ → ψ) → (□φ → □ψ))
```

### Migration Path

1. **Phase 1**: Add `MinimalHilbert` and `IntuitionisticHilbert` to `ProofSystem.lean`. Rename `PropositionalHilbert` to `ClassicalHilbert`. Add `abbrev PropositionalHilbert := ClassicalHilbert` as compatibility alias.

2. **Phase 2**: Weaken `Combinators.lean` from `[PropositionalHilbert S]` to `[MinimalHilbert S]`. All theorems should still compile since they don't use EFQ or Peirce.

3. **Phase 3**: Split `Core.lean` into intuitionistic and classical sections. Move `efq_axiom` to intuitionistic section, `double_negation`/`raa`/`rcp`/`lce_imp`/`rce_imp` to classical.

4. **Phase 4**: Update `Connectives.lean` — `contrapose_imp`/`contraposition` are intuitionistic; `classical_merge`, De Morgan, `iff_intro` with conjunction elimination are classical.

5. **Phase 5**: Update modal/temporal/bimodal bundled classes to extend `IntuitionisticHilbert` or `ClassicalHilbert` as appropriate.

6. **Phase 6**: Add `MinimalAxiom`, `IntuitionisticAxiom` inductives alongside existing `PropositionalAxiom`. Update `DerivationTree` to use the appropriate axiom type.

7. **Phase 7**: Remove the `PropositionalHilbert` compatibility alias once all downstream code is updated.

## Evidence/Examples

### Theorem Classification by Required Axioms

| Theorem | Required Level | Currently Requires | Notes |
|---------|---------------|-------------------|-------|
| `imp_trans` | Minimal | PropositionalHilbert | Only uses K, S, MP |
| `identity` | Minimal | PropositionalHilbert | SKK construction |
| `b_combinator` | Minimal | PropositionalHilbert | Composition |
| `flip` | Minimal | PropositionalHilbert | C combinator |
| `app1`, `app2` | Minimal | PropositionalHilbert | Application |
| `pairing` | Minimal | PropositionalHilbert | = app2 |
| `dni` | Minimal | PropositionalHilbert | = app1 |
| `efq_axiom` | Intuitionistic | PropositionalHilbert | Uses EFQ |
| `contrapose_imp` | Minimal | PropositionalHilbert | Only uses b_combinator, flip |
| `contraposition` | Minimal | PropositionalHilbert | Uses contrapose_imp |
| `peirce_axiom` | Classical | PropositionalHilbert | Uses Peirce |
| `double_negation` | Classical | PropositionalHilbert | Uses Peirce + EFQ |
| `raa` | Classical | PropositionalHilbert | Uses EFQ + dni |
| `efq_neg` | Classical | PropositionalHilbert | Uses raa + flip |
| `rcp` | Classical | PropositionalHilbert | Uses DNE + dni + contraposition |
| `lce_imp` | Classical | PropositionalHilbert | Uses Peirce + efq_neg |
| `rce_imp` | Classical | PropositionalHilbert | Uses Peirce + efq_neg + K |
| `classical_merge` | Classical | PropositionalHilbert | Uses Peirce + contraposition |
| `iff_intro` | Minimal | PropositionalHilbert | Uses pairing |
| `demorgan_*` | Classical | PropositionalHilbert | Uses DNE |

**Key insight**: `contrapose_imp` and `contraposition` are intuitionistically valid! They don't need Peirce — they only use `b_combinator` and `flip`, which are minimal. However, `rcp` (reverse contraposition) is genuinely classical.

### Analogy with Modal Extension Pattern

The proposed hierarchy exactly mirrors the existing modal extension pattern:

```
MinimalHilbert  ←→  ModalHilbertK (base modal)
IntuitionisticHilbert  ←→  ModalHilbertK + HasAxiomD (serial modal)  
ClassicalHilbert  ←→  ModalS5Hilbert (full modal)
```

Just as `ModalS5Hilbert` adds axioms T, 4, B on top of `ModalHilbert`, `ClassicalHilbert` adds Peirce on top of `IntuitionisticHilbert`. The pattern is uniform: each logic is defined by its base + extra axioms.

## Confidence Level

**High** — The architecture follows directly from:
1. The existing codebase structure (individual axiom typeclasses already exist)
2. The FormalizedFormalLogic/Foundation pattern (Minimal → Int → Cl hierarchy)
3. Concrete analysis of which theorems actually need which axioms
4. Natural alignment with the existing modal extension pattern

The main risk is **typeclass diamond issues** when both `ModalS5Hilbert` and `TemporalBXHilbert` extend `ClassicalHilbert` (which already happens with `PropositionalHilbert` today in `BimodalTMHilbert`). The existing `BimodalTMHilbert` already handles this, so the pattern is proven to work in Lean 4.
