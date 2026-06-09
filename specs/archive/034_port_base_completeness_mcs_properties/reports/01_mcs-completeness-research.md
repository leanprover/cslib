# Research Report: Port Base MCS Completeness Properties (Task 34)

## Source Analysis

**Source file**: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Completeness.lean` (520 lines)

The source file is in the BimodalLogic repository at the expected path. It contains the following sections:

1. **Imports** (lines 1-6): `Bimodal.ProofSystem`, `Bimodal.Semantics`, `Bimodal.Metalogic.Soundness`, `Bimodal.Metalogic.Core.MaximalConsistent`, `Bimodal.Metalogic.Core.MCSProperties`, `Bimodal.Theorems.Propositional.Core`
2. **Namespace**: `Bimodal.Metalogic`
3. **Opens**: `Syntax ProofSystem Semantics Theorems.Combinators Theorems.Propositional`, `Bimodal.Metalogic.Core`

The source uses non-polymorphic `Formula` (no type parameter). The `⊢` notation stands for `DerivationTree FrameClass.Base [] phi`.

## Target Analysis

**Target file**: `Cslib/Logics/Bimodal/Metalogic/Completeness.lean` -- DOES NOT EXIST YET. Must be created.

### Existing Infrastructure (from tasks 6 and 7)

The following modules are already ported and available:

| Module | Path | Key Definitions |
|--------|------|-----------------|
| DerivationTree | `Core/DerivationTree.lean` | `DerivationTree`, `lift`, `weakening` |
| DeductionTheorem | `Core/DeductionTheorem.lean` | `deduction_theorem` |
| MaximalConsistent | `Core/MaximalConsistent.lean` | `Consistent`, `MaximalConsistent`, `derives_bot_from_phi_neg_phi`, `bimodal_lindenbaum` |
| MCSProperties | `Core/MCSProperties.lean` | `SetConsistent`, `SetMaximalConsistent`, `closed_under_derivation`, `implication_property`, `negation_complete`, `all_future_all_future`, `all_past_all_past`, `set_consistent_not_both`, `neg_excludes` |
| Core barrel | `Core.lean` | Re-exports all 4 modules above |
| Perpetuity/Helpers | `Theorems/Perpetuity/Helpers.lean` | `double_negation`, `dni`, `contraposition`, `imp_trans`, `unwrap`, `wrap`, `identity` |
| Axioms | `ProofSystem/Axioms.lean` | All axiom constructors including `modal_t`, `modal_4`, `modal_k_dist`, `prop_s`, `efq`, `peirce` |

### Namespace Mapping

| Source | Target |
|--------|--------|
| `Bimodal.Metalogic` | `Cslib.Logic.Bimodal.Metalogic` (new) |
| `Bimodal.Metalogic.Core` | `Cslib.Logic.Bimodal.Metalogic.Core` |
| `Set Formula` | `Set (Formula Atom)` |
| `Formula` (plain) | `Formula Atom` (polymorphic) |
| `⊢ phi` | `DerivationTree FrameClass.Base ([] : List (Formula Atom)) phi` |
| `Gamma ⊢ phi` | `DerivationTree FrameClass.Base Gamma phi` |
| `double_negation φ` | `Cslib.Logic.Bimodal.Theorems.Perpetuity.double_negation φ` |
| `dni φ` | `Cslib.Logic.Bimodal.Theorems.Perpetuity.dni φ` |

### Key Type Differences

- Source: `Formula` is a plain type without universe parameters.
- Target: `Formula (Atom : Type u) : Type u` is universe-polymorphic.
- Source: `SetMaximalConsistent (fc := FrameClass.Base) S` is the standard constraint.
- Target: Same definition but with `{Atom : Type*}` universally quantified.

## Definition Inventory

### Theorems to Port (11 total)

All are in namespace `SetMaximalConsistent` in the source (namespace `Bimodal.Metalogic`).

#### Group 1: Propositional MCS Properties (6 theorems)

| # | Name | Signature | Lines | Dependencies |
|---|------|-----------|-------|-------------|
| 1 | `disjunction_intro` | `φ ∈ S ∨ ψ ∈ S → (φ.or ψ) ∈ S` | 61-109 | `closed_under_derivation`, `deduction_theorem`, `derives_bot_from_phi_neg_phi`, `Axiom.ex_falso`, `Axiom.prop_s` |
| 2 | `disjunction_elim` | `(φ.or ψ) ∈ S → φ ∈ S ∨ ψ ∈ S` | 116-127 | `negation_complete`, `implication_property` |
| 3 | `disjunction_iff` | `(φ.or ψ) ∈ S ↔ (φ ∈ S ∨ ψ ∈ S)` | 133-136 | `disjunction_intro`, `disjunction_elim` |
| 4 | `conjunction_intro` | `φ ∈ S ∧ ψ ∈ S → (φ.and ψ) ∈ S` | 144-181 | `negation_complete`, `implication_property`, `closed_under_derivation`, `derives_bot_from_phi_neg_phi` |
| 5 | `conjunction_elim` | `(φ.and ψ) ∈ S → φ ∈ S ∧ ψ ∈ S` | 187-284 | `negation_complete`, `closed_under_derivation`, `deduction_theorem`, `derives_bot_from_phi_neg_phi`, `Axiom.prop_s` |
| 6 | `conjunction_iff` | `(φ.and ψ) ∈ S ↔ (φ ∈ S ∧ ψ ∈ S)` | 290-293 | `conjunction_intro`, `conjunction_elim` |

#### Group 2: Modal MCS Properties (2 theorems)

| # | Name | Signature | Lines | Dependencies |
|---|------|-----------|-------|-------------|
| 7 | `box_closure` | `□φ ∈ S → φ ∈ S` | 314-331 | `closed_under_derivation`, `Axiom.modal_t` |
| 8 | `box_box` | `□φ ∈ S → □□φ ∈ S` | 345-362 | `closed_under_derivation`, `Axiom.modal_4` |

#### Group 3: Diamond-Box Duality (3 theorems)

| # | Name | Signature | Lines | Dependencies |
|---|------|-----------|-------|-------------|
| 9 | `neg_box_implies_diamond_neg` | `¬□φ ∈ S → ◇¬φ ∈ S` | 371-436 | `negation_complete`, `closed_under_derivation`, `derives_bot_from_phi_neg_phi`, `double_negation`, `Axiom.modal_k_dist`, `DerivationTree.necessitation` |
| 10 | `diamond_neg_implies_neg_box` | `◇¬φ ∈ S → ¬□φ ∈ S` | 443-498 | `negation_complete`, `closed_under_derivation`, `derives_bot_from_phi_neg_phi`, `dni`, `Axiom.modal_k_dist`, `DerivationTree.necessitation` |
| 11 | `diamond_box_duality` | `¬□φ ∈ S ↔ ◇¬φ ∈ S` | 508-511 | `neg_box_implies_diamond_neg`, `diamond_neg_implies_neg_box` |

## Dependency Analysis

### Required Imports

The target file will need:

```lean
import Cslib.Logics.Bimodal.Metalogic.Core  -- barrel for all Core modules
import Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers  -- double_negation, dni
```

### Dependencies from Already-Ported Code

All dependencies are satisfied by existing ported modules:

1. **From MCSProperties.lean** (task 7):
   - `SetMaximalConsistent` (definition)
   - `SetConsistent` (definition)
   - `SetMaximalConsistent.closed_under_derivation`
   - `SetMaximalConsistent.implication_property`
   - `SetMaximalConsistent.negation_complete`
   - `set_consistent_not_both`
   - `SetMaximalConsistent.neg_excludes`

2. **From MaximalConsistent.lean** (task 7):
   - `derives_bot_from_phi_neg_phi`

3. **From DeductionTheorem.lean** (task 7):
   - `deduction_theorem`

4. **From DerivationTree.lean** (task 6):
   - `DerivationTree.axiom`, `.assumption`, `.modus_ponens`, `.weakening`, `.necessitation`

5. **From ProofSystem/Axioms.lean**:
   - `Axiom.ex_falso`, `Axiom.prop_s`, `Axiom.modal_t`, `Axiom.modal_4`, `Axiom.modal_k_dist`

6. **From Perpetuity/Helpers.lean** (task 5 or earlier):
   - `double_negation` (only used in `neg_box_implies_diamond_neg`)
   - `dni` (only used in `diamond_neg_implies_neg_box`)

### No External Blockers

All dependencies are satisfied. No missing imports or unported dependencies.

## Translation Guide

### Namespace and Structure

```lean
-- File: Cslib/Logics/Bimodal/Metalogic/Completeness.lean
namespace Cslib.Logic.Bimodal.Metalogic

open Cslib.Logic.Bimodal
open Cslib.Logic
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable
```

### Key Translation Patterns

1. **Notation**: The source uses `⊢` notation (scoped in `Bimodal.Metalogic`). The target should use the scoped notation from `Cslib.Logic.Bimodal.ProofSystem.Derivation` which provides the same `⊢` and `⊢[fc]` notation.

2. **Type polymorphism**: Every `Formula` becomes `Formula Atom`, every `Set Formula` becomes `Set (Formula Atom)`.

3. **Frame class constraint**: Source uses `SetMaximalConsistent (fc := FrameClass.Base) S`. Target uses the same pattern since `SetMaximalConsistent` is already fc-parameterized.

4. **double_negation/dni access**: The source opens `Theorems.Propositional` to get these. In the target, they live in `Cslib.Logic.Bimodal.Theorems.Perpetuity`. Use:
   ```lean
   open Cslib.Logic.Bimodal.Theorems.Perpetuity (double_negation dni)
   ```

5. **Axiom references**: Source `Axiom.ex_falso`, `Axiom.prop_s`, etc. map directly to `Bimodal.Axiom.ex_falso` etc. in target (same constructor names, with the `Cslib.Logic.Bimodal` prefix resolved by the `open`).

6. **Context/List**: Source uses `Context` alias for `List Formula`. Target uses `Context Atom` alias for `List (Formula Atom)`.

### Proof Structure Preservation

All proofs in the source are sorry-free and follow the same MCS proof pattern:
1. Use negation completeness or direct derivation
2. Build a `DerivationTree` from axioms + assumptions
3. Apply `closed_under_derivation` to lift the derivation into MCS membership
4. Handle contradiction via `derives_bot_from_phi_neg_phi`

The proof strategies should port directly with only namespace/type parameter adjustments.

## Risk Assessment

**Low Risk**: This is a mechanical port. The proofs follow a repetitive MCS-property pattern that has been successfully ported before (in MCSProperties.lean for tasks 6/7). Key factors:

1. All 11 theorems use the same proof infrastructure already available in the target.
2. The only new import needed (`Perpetuity.Helpers`) is already ported and available.
3. No complex universe issues -- the polymorphism is standard `{Atom : Type*}`.
4. No new axioms or definitions needed -- only theorems that build on existing foundations.
5. The source proofs are sorry-free and well-structured.

**Potential Minor Issues**:
- The `⊢` notation scope: may need explicit `open scoped` or local notation redefinition.
- The `double_negation` and `dni` functions in `Perpetuity.Helpers` use `noncomputable` and local notation. The Completeness.lean file should also use `noncomputable section` for the diamond-box duality proofs.

## Recommended Implementation Approach

### Phase 1: File Creation and Imports (~20 lines)
Create `Cslib/Logics/Bimodal/Metalogic/Completeness.lean` with proper imports, namespace, and opens.

### Phase 2: Propositional Properties (~230 lines)
Port `disjunction_intro`, `disjunction_elim`, `disjunction_iff`, `conjunction_intro`, `conjunction_elim`, `conjunction_iff`.

### Phase 3: Modal Properties (~50 lines)
Port `box_closure`, `box_box`.

### Phase 4: Diamond-Box Duality (~160 lines)
Port `neg_box_implies_diamond_neg`, `diamond_neg_implies_neg_box`, `diamond_box_duality`.

### Phase 5: Verification
Run `lake build Cslib.Logics.Bimodal.Metalogic.Completeness` to verify no errors.

**Total estimated**: ~460 lines (source is 520 but the header/comments can be trimmed).

## Summary

- **Source**: 520 lines, 11 theorems, sorry-free, well-structured MCS property proofs.
- **Target**: New file to be created at `Cslib/Logics/Bimodal/Metalogic/Completeness.lean`.
- **Dependencies**: All satisfied by existing ported code (tasks 6, 7).
- **Translation**: Mechanical -- namespace adjustments and type polymorphism.
- **Risk**: Low. Same proof patterns as already-ported MCSProperties.lean.
- **No blockers identified**.
