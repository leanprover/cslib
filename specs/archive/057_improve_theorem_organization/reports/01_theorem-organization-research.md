# Research Report: Theorem Organization Improvement

**Task**: 57 - Improve theorem organization in cslib  
**Date**: 2026-06-09  
**Session**: sess_1781050904_b91db3

## 1. Complete Import Dependency Map

### 1.1 Files to Move: Generic Temporal Theorems

#### `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean`
- **Imported by**:
  - `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` (uses `G_distribution`, `H_distribution`)
  - `Cslib/Logics/Temporal/Theorems.lean` (barrel import)
- **Imports**:
  - `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`
  - `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`
- **Namespace**: `Cslib.Logic.Theorems.Temporal.TemporalDerived`

#### `Cslib/Logics/Temporal/Theorems/FrameConditions.lean`
- **Imported by**:
  - `Cslib/Logics/Temporal/Theorems.lean` (barrel import)
- **Imports**:
  - `Mathlib.Algebra.Order.Group.Defs`
  - `Mathlib.Algebra.Order.Group.Int`
  - `Mathlib.Data.Int.SuccPred`
  - `Mathlib.Order.SuccPred.LinearLocallyFinite`
- **Namespace**: `Cslib.Logic.Temporal.FrameConditions`

### 1.2 Files to Refactor: Redundant Concrete Bimodal Theorems

#### `Cslib/Logics/Bimodal/Theorems/Combinators.lean`
- **Imported by**:
  - `Cslib/Logics/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean`
  - `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Bundle/WitnessSeed.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalContent.lean`
  - `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean`
  - `Cslib/Logics/Bimodal/Theorems/GeneralizedNecessitation.lean`
  - `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean`
- **Imports**:
  - `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean`
  - `Cslib/Logics/Bimodal/Syntax/Formula.lean`

#### `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean`
- **Imported by**:
  - `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricTruthLemma.lean`
  - `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean`
  - `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean`
  - `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Bundle/Construction.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/FMP.lean`
- **Imports**:
  - `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean`
  - `Cslib/Logics/Bimodal/Syntax/Formula.lean`
  - `Cslib/Logics/Bimodal/Theorems/Combinators.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean`

#### `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean`
- **Imported by**:
  - `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Bundle/ModalSaturation.lean`
  - `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean`
  - `Cslib/Logics/Bimodal/Theorems/GeneralizedNecessitation.lean`
- **Imports**:
  - `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean`

### 1.3 Files Using the Bimodal Theorems Extensively (Downstream Consumers)

These files in `Metalogic/` are the main consumers of the concrete Bimodal theorem modules. They reference theorems via namespaces like `Theorems.Combinators.imp_trans`, `Theorems.Propositional.double_negation`, etc.:

- `Metalogic/Algebraic/LindenbaumQuotient.lean` (uses Combinators + Propositional)
- `Metalogic/Algebraic/BooleanStructure.lean` (uses Combinators)
- `Metalogic/Algebraic/ParametricTruthLemma.lean` (uses Combinators)
- `Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` (uses Combinators)
- `Metalogic/Algebraic/UltrafilterMCS.lean` (uses Combinators)
- `Metalogic/BXCanonical/Frame.lean` (uses Combinators + Propositional)
- `Metalogic/BXCanonical/OrderedSeedConsistency.lean` (opens both)
- `Metalogic/BXCanonical/CanonicalModel.lean` (opens Combinators)
- `Metalogic/BXCanonical/TruthLemma.lean` (uses Propositional)
- `Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` (uses both)
- `Metalogic/BXCanonical/Chronicle/RRelation.lean` (uses both extensively)
- `Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` (opens Combinators)
- `Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` (uses Combinators)
- `Metalogic/BXCanonical/Completeness/Dense.lean` (opens Propositional)
- `Metalogic/Bundle/WitnessSeed.lean` (uses Combinators + Propositional)
- `Metalogic/Bundle/TemporalContent.lean` (uses Combinators + Propositional)
- `Metalogic/Bundle/SuccRelation.lean` (uses Propositional)
- `Metalogic/Bundle/ModalSaturation.lean` (imports Connectives)
- `Metalogic/Bundle/Construction.lean` (imports Core)
- `Metalogic/Core/MCSProperties.lean` (uses one Foundations ref directly)
- `Metalogic/Decidability/FMP/FMP.lean` (imports Core)

## 2. Generic vs. Concrete Verification

### 2.1 TemporalDerived.lean (Logics/Temporal/) -- CONFIRMED GENERIC

The file is parameterized entirely over typeclasses:
```lean
variable {F : Type*} [HasBot F] [HasImp F] [HasUntil F] [HasSince F]
variable {S : Type*} [InferenceSystem S F]
variable [TemporalBXHilbert S (F := F)]
```

No concrete `Formula`, `DerivationTree`, `FrameClass`, or `Axiom` types appear. It belongs alongside the Modal and Propositional foundations theorems in `Foundations/Logic/Theorems/`.

### 2.2 FrameConditions.lean (Logics/Temporal/) -- CONFIRMED GENERIC

The file defines pure typeclass hierarchy (`LinearTemporalFrame`, `SerialFrame`, `DenseTemporalFrame`, `DiscreteTemporalFrame`) with no reference to any concrete formula or derivation type. The only concrete content is the `Int` instance at the end, which is fine -- it's a standard mathematical instance. However, it imports only Mathlib (no cslib imports), and its namespace is `Cslib.Logic.Temporal.FrameConditions`. It belongs in Foundations.

### 2.3 Bimodal Theorems Files -- CONFIRMED CONCRETE

All three files use concrete `DerivationTree`, `Formula Atom`, `FrameClass`, and `Axiom` types:
```lean
variable {Atom : Type*}
-- All theorems have type: DerivationTree fc [] (...)
-- All axiom references: DerivationTree.axiom [] _ (Axiom.imp_s ...) (FrameClass.base_le fc)
```

## 3. Theorem-by-Theorem Overlap Analysis

### 3.1 Combinators: Bimodal vs. Foundations

| # | Bimodal Theorem | Foundations Equivalent | Status |
|---|----------------|----------------------|--------|
| 1 | `imp_trans` | `imp_trans` | EXACT OVERLAP |
| 2 | `mp` | (uses `ModusPonens.mp` directly) | EXACT OVERLAP |
| 3 | `identity` | `identity` | EXACT OVERLAP |
| 4 | `b_combinator` | `b_combinator` | EXACT OVERLAP |
| 5 | `theorem_flip` | `theorem_flip` | EXACT OVERLAP |
| 6 | `theorem_app1` | `theorem_app1` | EXACT OVERLAP |
| 7 | `theorem_app2` | `theorem_app2` | EXACT OVERLAP |
| 8 | `pairing` | `pairing` | EXACT OVERLAP |
| 9 | `dni` | `dni` | EXACT OVERLAP |
| 10 | `combine_imp_conj` | `combine_imp_conj` | EXACT OVERLAP |
| 11 | `combine_imp_conj_3` | `combine_imp_conj_3` | EXACT OVERLAP |
| 12 | **`temp_future_derived`** | **NO EQUIVALENT** | CONCRETE-ONLY |

**Summary**: 11 of 12 theorems have exact generic equivalents. Only `temp_future_derived` uses concrete modal axioms (`Axiom.modal_future`, `Axiom.modal_t`, `Axiom.modal_4`) and cannot be replaced.

### 3.2 Propositional/Core: Bimodal vs. Foundations

| # | Bimodal Theorem | Foundations Equivalent | Status |
|---|----------------|----------------------|--------|
| 1 | `lem` | `lem` | EXACT OVERLAP |
| 2 | `efq_axiom` | `efq_axiom` | EXACT OVERLAP |
| 3 | `peirce_axiom` | `peirce_axiom` | EXACT OVERLAP |
| 4 | `double_negation` | `double_negation` | EXACT OVERLAP |
| 5 | `raa` | `raa` | EXACT OVERLAP |
| 6 | `efq_neg` | `efq_neg` | EXACT OVERLAP |
| 7 | `rcp` | `rcp` | EXACT OVERLAP (but Bimodal takes explicit `Gamma`) |
| 8 | `lce_imp` | `lce_imp` | EXACT OVERLAP |
| 9 | `rce_imp` | `rce_imp` | EXACT OVERLAP |
| 10 | **`ecq`** | **NO EQUIVALENT** | BIMODAL-ONLY (uses DeductionTheorem) |
| 11 | **`ldi`** | **NO EQUIVALENT** | BIMODAL-ONLY (left disjunction intro, context-based) |
| 12 | **`rdi`** | **NO EQUIVALENT** | BIMODAL-ONLY (right disjunction intro, context-based) |
| 13 | **`lce`** | **NO EQUIVALENT** | BIMODAL-ONLY (context-based, uses DeductionTheorem) |
| 14 | **`rce`** | **NO EQUIVALENT** | BIMODAL-ONLY (context-based, uses DeductionTheorem) |

**Summary**: 9 of 14 theorems have generic equivalents. 5 theorems (`ecq`, `ldi`, `rdi`, `lce`, `rce`) use the concrete Deduction Theorem and work with non-empty contexts -- these require the concrete derivation tree and MUST be kept.

### 3.3 Propositional/Connectives: Bimodal vs. Foundations

| # | Bimodal Theorem | Foundations Equivalent | Status |
|---|----------------|----------------------|--------|
| 1 | `classical_merge` | `classical_merge` | OVERLAP (Bimodal uses DT, Foundations is DT-free) |
| 2 | `iff_intro` | `iff_intro` | EXACT OVERLAP |
| 3 | `contrapose_imp` | `contrapose_imp` | EXACT OVERLAP |
| 4 | `contraposition` | `contraposition` | EXACT OVERLAP |
| 5 | `contrapose_iff` | `contrapose_iff` | EXACT OVERLAP |
| 6 | `iff_neg_intro` | `iff_neg_intro` | EXACT OVERLAP |
| 7 | `demorgan_conj_neg_forward` | `demorgan_conj_neg_forward` | EXACT OVERLAP |
| 8 | `demorgan_conj_neg_backward` | `demorgan_conj_neg_backward` | EXACT OVERLAP |
| 9 | `demorgan_conj_neg` | `demorgan_conj_neg` | EXACT OVERLAP |
| 10 | `demorgan_disj_neg_forward` | `demorgan_disj_neg_forward` | EXACT OVERLAP |
| 11 | `demorgan_disj_neg_backward` | `demorgan_disj_neg_backward` | EXACT OVERLAP |
| 12 | `demorgan_disj_neg` | `demorgan_disj_neg` | EXACT OVERLAP |
| 13 | **`iff_elim_left`** | **NO EQUIVALENT** | BIMODAL-ONLY (uses DT + lce) |
| 14 | **`iff_elim_right`** | **NO EQUIVALENT** | BIMODAL-ONLY (uses DT + rce) |

**Summary**: 12 of 14 theorems have generic equivalents. 2 theorems (`iff_elim_left`, `iff_elim_right`) use the Deduction Theorem with non-empty contexts and must be kept.

**Note**: `classical_merge` has a Foundations version that is DT-free, while the Bimodal version uses the Deduction Theorem. Both prove the same statement. The Bimodal version can be replaced since the Foundations version is strictly more general.

### 3.4 Overall Overlap Summary

| File | Total Theorems | Have Generic Equiv | Concrete-Only |
|------|---------------|-------------------|---------------|
| Combinators | 12 | 11 | 1 (`temp_future_derived`) |
| Propositional/Core | 14 | 9 | 5 (`ecq`, `ldi`, `rdi`, `lce`, `rce`) |
| Propositional/Connectives | 14 | 12 | 2 (`iff_elim_left`, `iff_elim_right`) |
| **Total** | **40** | **32** | **8** |

## 4. The Wrap/Unwrap Bridge Pattern

### 4.1 Pattern Documentation (from `Perpetuity/Helpers.lean`)

The bridge pattern converts between concrete `DerivationTree` and abstract `InferenceSystem.DerivableIn`:

```lean
-- Convert concrete -> abstract (wrapping)
def wrap {φ : Bimodal.Formula Atom}
    (d : ⊢ φ) : InferenceSystem.DerivableIn Bimodal.HilbertTM φ := ⟨d⟩

-- Convert abstract -> concrete (unwrapping)
def unwrap {φ : Bimodal.Formula Atom}
    (h : InferenceSystem.DerivableIn Bimodal.HilbertTM φ) : ⊢ φ := h.some
```

where `⊢ φ` is notation for `DerivationTree FrameClass.Base [] φ`.

### 4.2 Usage Example

```lean
-- Calling Foundations generic theorem from Bimodal context:
def imp_trans {φ ψ χ : Bimodal.Formula Atom}
    (h1 : ⊢ φ.imp ψ) (h2 : ⊢ ψ.imp χ) : ⊢ φ.imp χ :=
  unwrap (Theorems.Combinators.imp_trans (wrap h1) (wrap h2))
```

### 4.3 How It Works

1. The `InferenceSystem` instance in `Instances.lean` maps `HilbertTM => φ` to `DerivationTree .Base [] φ`
2. `InferenceSystem.DerivableIn HilbertTM φ = Nonempty (DerivationTree .Base [] φ)`
3. `wrap` creates `⟨d⟩` (Nonempty constructor)
4. `unwrap` uses `.some` (noncomputable choice from Nonempty)
5. The `PropositionalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert` instances in `Instances.lean` provide all required typeclasses

### 4.4 Already Working in Perpetuity/Principles.lean

The `Perpetuity/Principles.lean` file already demonstrates the wrap/unwrap pattern in production:

```lean
def future_k_dist (φ₁ φ₂ : Bimodal.Formula Atom) :
    ⊢ (φ₁.imp φ₂).all_future.imp (φ₁.all_future.imp φ₂.all_future) := by
  exact unwrap (@Theorems.Temporal.TemporalDerived.G_distribution
    (Bimodal.Formula Atom) _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ₁) (ψ := φ₂))
```

This calls the generic `G_distribution` from `Logics/Temporal/Theorems/TemporalDerived.lean` and unwraps it into a concrete derivation tree.

## 5. Namespace Conflict Analysis

### 5.1 Moving TemporalDerived.lean to Foundations

**Proposed path**: `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean`

**Current Foundations directory structure**:
```
Cslib/Foundations/Logic/Theorems/
├── BigConj.lean
├── Combinators.lean
├── Modal/
│   ├── Basic.lean
│   └── S5.lean
└── Propositional/
    ├── Connectives.lean
    ├── Core.lean
    └── Reasoning.lean
```

There is **no** existing `Temporal/` directory under `Foundations/Logic/Theorems/`. Creating `Temporal/TemporalDerived.lean` would be conflict-free. The namespace `Cslib.Logic.Theorems.Temporal.TemporalDerived` is already used by the file, so no namespace change is needed -- only the file path changes.

### 5.2 Moving FrameConditions.lean to Foundations

**Proposed path**: `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean`

The namespace `Cslib.Logic.Temporal.FrameConditions` does not conflict with anything in `Foundations/Logic/Theorems/`. The file path change is purely organizational.

## 6. FrameConditions.lean Assessment

### 6.1 Should It Move?

**Yes, with caveats.**

**Arguments for moving**:
- Uses no concrete types (pure typeclass hierarchy + Mathlib imports)
- Namespace is `Cslib.Logic.Temporal.FrameConditions` -- consistent with Foundations conventions
- Only imported by `Logics/Temporal/Theorems.lean` barrel file (1 consumer)
- Semantically describes frame structure, not a specific logic implementation

**Arguments against moving**:
- The `Int` instance at the end is a concrete instantiation, but standard mathematical instances like this are common in Foundations-level files
- It imports only Mathlib (no dependency on other cslib files), so no circular dependency risk

**Recommendation**: Move to `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean`. Update the barrel import in `Logics/Temporal/Theorems.lean`.

### 6.2 Circular Dependency Check

No circular dependency risk for either move:
- `TemporalDerived.lean` imports from `Foundations/Logic/Theorems/Propositional/` (already in Foundations)
- `FrameConditions.lean` imports only from Mathlib
- Neither file imports anything from `Logics/Bimodal/` or `Logics/Temporal/`

## 7. Theorems That Genuinely Need Concrete Types

These theorems MUST remain in `Logics/Bimodal/Theorems/` because they use concrete `DerivationTree`, `Axiom`, `FrameClass`, `Formula`, or the Deduction Theorem:

### 7.1 Combinators.lean -- Keep 1 theorem
- **`temp_future_derived`**: Uses `Axiom.modal_future`, `Axiom.modal_t`, `Axiom.modal_4` -- concrete bimodal modal axioms that have no typeclass equivalent in this generality

### 7.2 Propositional/Core.lean -- Keep 5 theorems
- **`ecq`**: Uses `DerivationTree.assumption` with non-empty context `[A, A.neg]`
- **`ldi`**: Uses `DerivationTree.assumption` with context `[A]`
- **`rdi`**: Uses `DerivationTree.assumption` with context `[B]`
- **`lce`**: Uses `DerivationTree.assumption` with context `[A.and B]` + Deduction Theorem
- **`rce`**: Uses `DerivationTree.assumption` with context `[A.and B]` + Deduction Theorem

Note: `lce_imp` and `rce_imp` in the Bimodal file are themselves derived from `lce`/`rce` + Deduction Theorem. However, DT-free versions now exist in Foundations (`lce_imp`, `rce_imp`), so the Bimodal wrapper versions can be removed. The context-based `lce` and `rce` themselves must stay.

### 7.3 Propositional/Connectives.lean -- Keep 2 theorems
- **`iff_elim_left`**: Uses `lce` (context-based conjunction elimination)
- **`iff_elim_right`**: Uses `rce` (context-based conjunction elimination)

## 8. Recommended Actions

### Phase 1: Move Generic Files to Foundations (LOW RISK)

#### Action 1.1: Move TemporalDerived.lean
- **From**: `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean`
- **To**: `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean`
- **Changes needed**:
  - Create `Cslib/Foundations/Logic/Theorems/Temporal/` directory
  - Move the file (no content changes needed -- namespace already matches)
  - Update `Cslib/Logics/Temporal/Theorems.lean` barrel import
  - Update `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` import
  - Update `Cslib/Foundations/Logic/Theorems.lean` barrel to include new module
- **Risk**: LOW -- only 2 downstream consumers, no namespace change needed
- **Impact**: 2 files need import path updates

#### Action 1.2: Move FrameConditions.lean
- **From**: `Cslib/Logics/Temporal/Theorems/FrameConditions.lean`
- **To**: `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean`
- **Changes needed**:
  - Move the file (no content changes needed)
  - Update `Cslib/Logics/Temporal/Theorems.lean` barrel import
  - Update `Cslib/Foundations/Logic/Theorems.lean` barrel to include new module
- **Risk**: LOW -- only 1 downstream consumer
- **Impact**: 1 file needs import path update

### Phase 2: Refactor Redundant Bimodal Combinators (MEDIUM RISK)

#### Action 2.1: Replace Bimodal Combinators with Bridge Wrappers
- **Target**: `Cslib/Logics/Bimodal/Theorems/Combinators.lean`
- **Strategy**: Replace the 11 redundant theorem implementations with wrap/unwrap bridges to Foundations. Keep `temp_future_derived` as-is.
- **Example transformation**:
  ```lean
  -- Before (349 lines of manual proof):
  def imp_trans {fc : FrameClass} {A B C : Formula Atom}
      (h1 : DerivationTree fc [] (A.imp B))
      (h2 : DerivationTree fc [] (B.imp C)) : DerivationTree fc [] (A.imp C) := by
    have s_axiom := DerivationTree.axiom (fc := fc) [] _ (Axiom.imp_s ...) ...
    ...
  
  -- After (1 line per theorem):
  noncomputable def imp_trans {fc : FrameClass} {A B C : Formula Atom}
      (h1 : DerivationTree fc [] (A.imp B))
      (h2 : DerivationTree fc [] (B.imp C)) : DerivationTree fc [] (A.imp C) :=
    unwrap (Theorems.Combinators.imp_trans (wrap h1) (wrap h2))
  ```
- **Risk**: MEDIUM -- 7 downstream consumers that `open Cslib.Logic.Bimodal.Theorems.Combinators` or reference theorems by qualified name
- **Critical concern**: The current theorems work for arbitrary `fc : FrameClass`, but the wrap/unwrap bridge only works at `FrameClass.Base` (since `HilbertTM` maps to `.Base`). Need to verify that all 7 consumers use `.Base` or can be lifted.

**BLOCKER IDENTIFIED**: The wrap/unwrap pattern as implemented in `Helpers.lean` only works for `FrameClass.Base`. But many Bimodal Combinators theorems are parameterized over `{fc : FrameClass}` and called at non-Base frame classes via `FrameClass.base_le fc` lifting. The bridge would need to:
1. Wrap at `.Base` level
2. Lift to arbitrary `fc` via `DerivationTree.lift (FrameClass.base_le fc)`

This is feasible but requires each bridge wrapper to include the lift step.

#### Action 2.2: Replace Bimodal Propositional/Core with Bridge Wrappers
- **Target**: `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean`
- **Strategy**: Replace the 9 redundant theorems with bridge wrappers. Keep `ecq`, `ldi`, `rdi`, `lce`, `rce`.
- **Risk**: MEDIUM -- 6 downstream consumers
- **Same fc concern**: `efq_axiom`, `peirce_axiom`, `double_negation`, `rcp`, `lce_imp`, `rce_imp` are parameterized over `fc`. Bridge wrappers need lift step.

#### Action 2.3: Replace Bimodal Propositional/Connectives with Bridge Wrappers
- **Target**: `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean`
- **Strategy**: Replace the 12 redundant theorems with bridge wrappers. Keep `iff_elim_left`, `iff_elim_right`.
- **Risk**: MEDIUM -- 5 downstream consumers
- **Special case**: `classical_merge` in Bimodal uses DT but the Foundations version is DT-free. The bridge should call the Foundations version directly.

### Phase 3: Cleanup and Verification

#### Action 3.1: Update Bimodal TemporalDerived.lean
- After Phase 2, `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` should already work since it calls the Bimodal Combinators/Propositional by the same names -- the bridge wrappers preserve the API.

#### Action 3.2: Full Build Verification
- Run `lake build` after each phase to catch any type mismatches or missing imports.

## 9. Risk Assessment Summary

| Phase | Action | Risk | Files Changed | Downstream Impact |
|-------|--------|------|---------------|-------------------|
| 1.1 | Move TemporalDerived | LOW | 4 | 2 import updates |
| 1.2 | Move FrameConditions | LOW | 3 | 1 import update |
| 2.1 | Bridge Combinators | MEDIUM | 1 + verify 7 | Type signature preserved |
| 2.2 | Bridge Prop/Core | MEDIUM | 1 + verify 6 | Type signature preserved |
| 2.3 | Bridge Prop/Connectives | MEDIUM | 1 + verify 5 | Type signature preserved |
| 3.1 | Verify TemporalDerived | LOW | 0 | Build check |
| 3.2 | Full build | LOW | 0 | Final verification |

## 10. Key Technical Considerations

### 10.1 FrameClass Lifting Pattern

The bridge wrapper for `fc`-polymorphic theorems must follow this pattern:

```lean
noncomputable def identity {fc : FrameClass} (A : Formula Atom) :
    DerivationTree fc [] (A.imp A) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@Theorems.Combinators.identity _ _ _ Bimodal.HilbertTM _ _ A))
```

This works because:
1. The Foundations theorem produces `InferenceSystem.DerivableIn HilbertTM (A.imp A)`
2. `unwrap` gives `DerivationTree .Base [] (A.imp A)`
3. `DerivationTree.lift (FrameClass.base_le fc)` lifts to arbitrary `fc`

### 10.2 Context-Based Theorems Cannot Use Bridge

Theorems with non-empty contexts (`ecq`, `ldi`, `rdi`, `lce`, `rce`, `iff_elim_left`, `iff_elim_right`) operate on `DerivationTree fc Gamma phi` where `Gamma` is non-empty. The `InferenceSystem.DerivableIn` abstraction only covers empty contexts (`[]`), so these theorems have no generic equivalent and must remain concrete.

### 10.3 `noncomputable` Propagation

All bridge wrappers must be `noncomputable` because `unwrap` uses `Nonempty.some` (classical choice). Most downstream consumers already mark their sections `noncomputable`, but this should be verified.

### 10.4 Import Simplification

After bridging, the Bimodal theorem files can drop imports of `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` and `Cslib/Logics/Bimodal/Syntax/Formula.lean` if they are no longer directly constructing axiom instances. However, `Instances.lean` (which provides the typeclass instances) must be imported instead. This import is already present in `Helpers.lean`.
