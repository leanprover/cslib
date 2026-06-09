# Task 6: Port Frame Conditions and Soundness -- Research Report

## 1. Source File Inventory

All files reside under `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/`.

### FrameConditions/ (4 files, 790 lines)

| File | Lines | Key Definitions |
|------|-------|-----------------|
| `FrameClass.lean` | 220 | `LinearTemporalFrame`, `SerialFrame`, `DenseTemporalFrame`, `DiscreteTemporalFrame` marker typeclasses; `Int` instances; `mk'` helpers |
| `Validity.lean` | 204 | `valid_over`, `valid_linear`, `valid_dense_fc`, `valid_discrete_fc`; equivalence lemmas with existing `valid_dense`/`valid_discrete` |
| `Soundness.lean` | 190 | `soundness_over`, `soundness_linear`, `soundness_dense`, `soundness_discrete`; parameterized axiom validity theorems; `soundness_Int` |
| `Compatibility.lean` | 176 | `AxiomLinearCompatible`, `AxiomDenseCompatible`, `AxiomDiscreteCompatible` typeclasses; monotonicity instances; per-axiom instances |

### Metalogic/SoundnessLemmas/ (3 files, 2,415 lines)

| File | Lines | Key Definitions |
|------|-------|-----------------|
| `Core.lean` | 106 | `is_valid` (local validity def), `valid_at_triple`, `truth_at_swap_swap` involution |
| `DenseValidity.lean` | 1,338 | All swap_axiom_*_valid theorems; `axiom_swap_valid` (42 cases); `axiom_locally_valid`; `mp_preserves_valid`, `necessitation_preserves_local_valid`; `derivable_valid_and_swap_valid` (combined soundness for dense); `derivable_implies_swap_valid` |
| `FrameClassVariants.lean` | 971 | `axiom_swap_valid_general` (general version); `derivable_implies_swap_valid_general`; `prior_UZ_is_valid`, `prior_SZ_is_valid`, `z1_is_valid`, `z1_past_is_valid`; `axiom_swap_valid_discrete`; `derivable_valid_and_swap_valid_discrete`; `derivable_implies_swap_valid_discrete` |

### Metalogic/ top-level (3 files, 1,475 lines)

| File | Lines | Key Definitions |
|------|-------|-----------------|
| `Soundness.lean` | 1,372 | All individual axiom validity theorems (prop_k_valid through z1_valid); `axiom_valid`, `axiom_dense_valid`, `axiom_discrete_valid`; main `soundness` theorem (Base); `soundness_dense_valid`, `soundness_dense`; `soundness_discrete_valid`, `soundness_discrete` |
| `DenseSoundness.lean` | 51 | `density_sound_dense`, `axiom_dense_valid'` -- thin wrappers re-exporting from Soundness.lean |
| `DiscreteSoundness.lean` | 53 | `discreteness_forward_sound_discrete`, `axiom_discrete_valid'` -- thin wrappers re-exporting from Soundness.lean |

**Total: 10 files, 4,680 lines**

## 2. Sorry Status

**Zero sorries found.** All proofs in all 10 source files are complete. Grep output confirms only comments mentioning "sorry-free" appear, with no actual `sorry` calls.

## 3. Import Dependency Map

### Internal Dependencies (BimodalLogic -> BimodalLogic)

```
SoundnessLemmas/Core
  <- Bimodal.Semantics.Truth
  <- Bimodal.ProofSystem.Derivation
  <- Bimodal.ProofSystem.Axioms

SoundnessLemmas/DenseValidity
  <- SoundnessLemmas/Core
  <- Mathlib.Order.SuccPred.{Basic, Archimedean}

SoundnessLemmas/FrameClassVariants
  <- SoundnessLemmas/DenseValidity

Metalogic/Soundness
  <- Bimodal.ProofSystem.Derivation
  <- Bimodal.Semantics.Validity
  <- SoundnessLemmas/FrameClassVariants

FrameConditions/FrameClass
  <- Mathlib (only -- no BimodalLogic imports)

FrameConditions/Validity
  <- FrameConditions/FrameClass
  <- Bimodal.Semantics.Validity

FrameConditions/Soundness
  <- FrameConditions/Validity
  <- Metalogic/Soundness

FrameConditions/Compatibility
  <- FrameConditions/Soundness
  <- Bimodal.ProofSystem.Axioms

DenseSoundness, DiscreteSoundness
  <- Metalogic/Soundness
  <- Bimodal.Semantics.Validity
```

### External Dependencies (cslib modules already ported)

The following cslib modules are required (from Tasks 3 and 4):

- `Cslib.Logics.Bimodal.Syntax.Formula` -- Formula type with Atom parameterization
- `Cslib.Logics.Bimodal.Syntax.Context` -- Context type
- `Cslib.Logics.Bimodal.Semantics.Truth` -- truth_at, Truth simp lemmas
- `Cslib.Logics.Bimodal.Semantics.Validity` -- valid, valid_dense, valid_discrete, ShiftClosed
- `Cslib.Logics.Bimodal.Semantics.TaskFrame` -- TaskFrame
- `Cslib.Logics.Bimodal.Semantics.TaskModel` -- TaskModel
- `Cslib.Logics.Bimodal.Semantics.WorldHistory` -- WorldHistory, time_shift
- `Cslib.Logics.Bimodal.ProofSystem.Axioms` -- Axiom, FrameClass, minFrameClass
- `Cslib.Logics.Bimodal.ProofSystem.Derivation` -- DerivationTree

### Mathlib Dependencies

- `Mathlib.Algebra.Order.Group.Defs` (AddCommGroup ordering)
- `Mathlib.Algebra.Order.Group.Int` (Int instances)
- `Mathlib.Data.Int.SuccPred` (Int SuccOrder/PredOrder)
- `Mathlib.Order.SuccPred.LinearLocallyFinite` (IsSuccArchimedean for Int)
- `Mathlib.Order.SuccPred.Basic` (SuccOrder, PredOrder)
- `Mathlib.Order.SuccPred.Archimedean` (IsSuccArchimedean, IsPredArchimedean)
- `Mathlib.Algebra.Order.Ring.Rat` (FrameClass.lean, may not be needed)

## 4. Key Porting Adaptations

### 4.1 Atom Parameterization

The source uses a monomorphic `Formula`. The cslib uses `Formula Atom` with `Atom : Type u`. Every definition and theorem must be adapted:

**Source pattern**:
```lean
theorem prop_k_valid (phi psi chi : Formula) : valid (...) := ...
```

**Target pattern**:
```lean
variable {Atom : Type*}
theorem prop_k_valid (phi psi chi : Formula Atom) : valid (...) := ...
```

This is a systematic transformation affecting all 10 files. Proof bodies should not change since they only manipulate formulas structurally.

### 4.2 Namespace Rename

- Source: `Bimodal.Metalogic`, `Bimodal.FrameConditions`, `Bimodal.Syntax`, etc.
- Target: `Cslib.Logic.Bimodal` (note: file path is `Cslib/Logics/Bimodal/` but namespace is `Cslib.Logic.Bimodal`)

### 4.3 Import Adaptation

- `import Bimodal.Semantics.Truth` -> `import Cslib.Logics.Bimodal.Semantics.Truth`
- `import Bimodal.ProofSystem.Derivation` -> `import Cslib.Logics.Bimodal.ProofSystem.Derivation`
- `import Bimodal.Semantics.Validity` -> `import Cslib.Logics.Bimodal.Semantics.Validity`
- `import Bimodal.ProofSystem.Axioms` -> `import Cslib.Logics.Bimodal.ProofSystem.Axioms`
- Keep Mathlib imports as-is (already in project)
- Some Mathlib imports may already be transitively available via `Cslib.Init`

### 4.4 Frame Variable Naming

The cslib convention uses `ℱ` for frame variables instead of `F` (because `F` is scoped notation for `Formula.some_future`). All soundness proofs use `F : TaskFrame D` which must become `ℱ : TaskFrame D`.

### 4.5 TaskModel Parameterization

Source: `TaskModel F` (monomorphic)
Target: `TaskModel Atom ℱ` (parameterized by Atom)

### 4.6 Module/Section Keywords

cslib files use Lean 4's `module` keyword and `@[expose] public section` pattern. New files should follow the existing convention seen in Semantics/*.lean.

### 4.7 open Statement Adaptation

- `open Bimodal.Syntax` -> `open Cslib.Logic.Bimodal`
- `open Bimodal.Semantics` -> already in scope via namespace
- `open Bimodal.ProofSystem` -> already in scope via namespace

## 5. Target Module Structure

```
Cslib/Logics/Bimodal/
├── FrameConditions/
│   ├── FrameClass.lean         -- LinearTemporalFrame, SerialFrame, Dense/Discrete typeclasses
│   ├── Validity.lean           -- valid_over, valid_linear, valid_dense_fc, valid_discrete_fc
│   ├── Soundness.lean          -- soundness_over, soundness_linear/dense/discrete
│   └── Compatibility.lean      -- AxiomLinearCompatible, AxiomDenseCompatible, etc.
├── Metalogic/
│   └── Soundness/
│       ├── Core.lean           -- is_valid, truth_at_swap_swap
│       ├── DenseValidity.lean  -- swap validity for dense frame class
│       ├── FrameClassVariants.lean -- general + discrete swap validity
│       ├── Soundness.lean      -- main soundness theorems
│       ├── DenseSoundness.lean -- thin wrapper
│       └── DiscreteSoundness.lean -- thin wrapper
```

### Build Order (dependency-respecting)

1. `FrameConditions/FrameClass.lean` (Mathlib-only imports)
2. `Metalogic/Soundness/Core.lean` (imports Truth, Derivation, Axioms)
3. `Metalogic/Soundness/DenseValidity.lean` (imports Core)
4. `Metalogic/Soundness/FrameClassVariants.lean` (imports DenseValidity)
5. `Metalogic/Soundness/Soundness.lean` (imports FrameClassVariants, Derivation, Validity)
6. `FrameConditions/Validity.lean` (imports FrameClass, Validity)
7. `FrameConditions/Soundness.lean` (imports FC/Validity, Metalogic/Soundness)
8. `FrameConditions/Compatibility.lean` (imports FC/Soundness, Axioms)
9. `Metalogic/Soundness/DenseSoundness.lean` (imports Soundness)
10. `Metalogic/Soundness/DiscreteSoundness.lean` (imports Soundness)

## 6. Risk Assessment

### Low Risk
- **FrameClass.lean** (220 lines): Pure Mathlib imports, no BimodalLogic dependencies. Marker typeclasses with trivial proofs. Straightforward port.
- **DenseSoundness.lean** (51 lines): Thin wrapper, trivial port.
- **DiscreteSoundness.lean** (53 lines): Thin wrapper, trivial port.
- **Core.lean** (106 lines): Small file, `is_valid` def + one induction lemma.

### Medium Risk
- **Validity.lean** (204 lines): Parameterized validity defs and equivalence proofs. May need care with typeclass resolution for the `haveI` patterns.
- **Soundness.lean** (FC, 190 lines): Bridges FC layer to Metalogic layer. Depends on correct compilation of both layers.
- **Compatibility.lean** (176 lines): Instance resolution for 13+ axiom instances. Need to match axiom constructor names.

### Higher Risk
- **DenseValidity.lean** (1,338 lines): Largest single file. 42-case axiom swap proof + combined soundness with `termination_by d.height`. The `Atom` parameterization may affect universe level issues in `is_valid` (defined with `Type*`).
- **FrameClassVariants.lean** (971 lines): Complex discrete validity proofs (prior_UZ_is_valid, z1_is_valid) with well-founded recursion on succ/pred chains.
- **Soundness.lean** (Metalogic, 1,372 lines): The main soundness theorem with 42+ axiom cases, each calling individual validity lemmas. The `Atom` parameterization propagates through every case.

### Key Risk: Universe Levels

The source `is_valid` uses `Type*`:
```lean
def is_valid (D : Type*) ... (phi : Formula) : Prop := ...
```

In cslib with `Formula Atom` where `Atom : Type u`, the universe for `D` must be compatible. The existing cslib `valid` uses `D : Type` (not `Type*`) explicitly to avoid universe issues. The ported `is_valid` may need similar treatment.

## 7. FrameConditions vs Standalone Temporal

The FrameConditions files define marker typeclasses (`LinearTemporalFrame`, `DenseTemporalFrame`, `DiscreteTemporalFrame`) that are specific to the bimodal logic setting. These are NOT standalone temporal frame conditions -- they bundle AddCommGroup + LinearOrder + IsOrderedAddMonoid + frame-specific constraints.

Task 22 (standalone temporal) would define its own frame conditions without the bimodal coupling. The frame conditions in this task remain entirely within `Cslib/Logics/Bimodal/FrameConditions/`.

## 8. Estimated Effort

| Phase | Est. Lines | Complexity | Time |
|-------|-----------|------------|------|
| Phase 1: FrameClass.lean | 220 | Low | Short |
| Phase 2: SoundnessLemmas/Core.lean | 106 | Low | Short |
| Phase 3: SoundnessLemmas/DenseValidity.lean | 1,338 | High | Long |
| Phase 4: SoundnessLemmas/FrameClassVariants.lean | 971 | High | Long |
| Phase 5: Metalogic/Soundness.lean | 1,372 | High | Long |
| Phase 6: FrameConditions/Validity.lean | 204 | Medium | Medium |
| Phase 7: FrameConditions/Soundness.lean | 190 | Medium | Medium |
| Phase 8: FrameConditions/Compatibility.lean | 176 | Medium | Medium |
| Phase 9: DenseSoundness + DiscreteSoundness | 104 | Low | Short |
| Phase 10: Integration & lake build | N/A | Medium | Medium |

**Total: ~4,680 source lines -> ~5,000 target lines** (accounting for copyright headers, module declarations, and Atom parameterization overhead).

## 9. Dependency Verification

Tasks 3 (Semantics) and 4 (ProofSystem) must be completed. Checking what exists in cslib:

**Semantics** (Task 3 -- present):
- `Cslib/Logics/Bimodal/Semantics/TaskFrame.lean` -- present
- `Cslib/Logics/Bimodal/Semantics/TaskModel.lean` -- present
- `Cslib/Logics/Bimodal/Semantics/WorldHistory.lean` -- present
- `Cslib/Logics/Bimodal/Semantics/Truth.lean` -- present
- `Cslib/Logics/Bimodal/Semantics/Validity.lean` -- present (with `valid_dense`, `valid_discrete`, `ShiftClosed`)

**ProofSystem** (Task 4 -- present):
- `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean` -- present (with `FrameClass`, `Axiom`, `minFrameClass`)
- `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` -- present (with `DerivationTree`)

**Additional dependencies** listed in state.json:
- `BimodalLogic:291` -- source commit reference
- Task 32 -- not found in active_projects, may be completed/archived

All required cslib modules for this port are present. No blockers identified.

## 10. Porting Strategy

### Recommended Approach: Bottom-Up Build Order

1. Start with files that have no internal dependencies (FrameClass.lean, Core.lean)
2. Build up through DenseValidity -> FrameClassVariants -> Soundness
3. Layer FrameConditions on top
4. Add thin wrappers last (DenseSoundness, DiscreteSoundness)

### Porting Checklist Per File

For each file:
1. Create file with Apache 2.0 copyright header
2. Add `module` keyword (for files using public imports) or standard imports
3. Set `namespace Cslib.Logic.Bimodal`
4. Add `variable {Atom : Type*}` where needed
5. Replace `Formula` with `Formula Atom`
6. Replace `Context` with `Context Atom`
7. Replace `TaskModel F` with `TaskModel Atom ℱ`
8. Replace `F : TaskFrame D` with `ℱ : TaskFrame D`
9. Update open statements
10. Verify `lake build` after each file
11. Run `grep -r sorry` to confirm zero sorries
