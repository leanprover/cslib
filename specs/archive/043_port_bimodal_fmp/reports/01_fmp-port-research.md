# Research Report: Port Bimodal Finite Model Property (FMP)

**Task**: 43 -- Port FMP infrastructure from BimodalLogic to Cslib
**Date**: 2026-06-09
**Session**: sess_1749474600_a3b2c1_43

---

## 1. Source File Inventory

The FMP infrastructure in the source repository lives in two locations:

### FMP Directory (`Theories/Bimodal/Metalogic/Decidability/FMP/`)

| File | Lines | Description |
|------|-------|-------------|
| `ClosureMCS.lean` | 279 | Closure MCS definitions, projection, cardinality bounds |
| `Filtration.lean` | 323 | Filtration equivalence, quotient construction, filtered frame |
| `FiniteModel.lean` | 177 | Finiteness theorem via characteristic set injection |
| `TruthPreservation.lean` | 400 | MCS truth, filtration lemma, MCS properties for operators |
| `FMP.lean` | 248 | Main FMP theorem, contrapositive, size bound |
| `DenseFMP.lean` | 112 | Dense time specialization (delegates to base FMP) |
| `DiscreteFMP.lean` | 117 | Discrete time specialization (delegates to base FMP) |

### Barrel Import (`Theories/Bimodal/Metalogic/Decidability/FMP.lean`)

| File | Lines | Description |
|------|-------|-------------|
| `FMP.lean` | 47 | Re-exports all 7 FMP files |

**Total FMP-specific lines**: 1,703

### Required Dependency Files (NOT yet ported)

| File | Lines | What FMP needs from it |
|------|-------|------------------------|
| `Syntax/Subformulas.lean` | 229 | `Formula.subformulas`, `self_mem_subformulas`, all `mem_subformulas_of_*` lemmas |
| `Syntax/SubformulaClosure/Closure.lean` | 367 | `subformulaClosure`, `closureWithNeg`, membership/subset lemmas |
| `Core/RestrictedMCS/Basic.lean` | 653 | `ClosureRestricted`, `RestrictedConsistent`, `RestrictedMCS`, `restricted_lindenbaum`, negation completeness, `restricted_mcs_exists_containing`, `restricted_mcs_from_formula` |

**Lines needed from dependencies**: ~1,249 (not all of Basic.lean is needed; the `iter_F`/`iter_P` boundedness theorems at lines 441-653 are NOT required by FMP)

**Total porting scope**: ~2,500-2,700 lines (FMP files + required dependency portions)

---

## 2. Target Analysis

### Existing Structure

The target `Cslib/Logics/Bimodal/Metalogic/Decidability/` already contains 10 files from the Task 42 core tableau port. There is NO `FMP/` subdirectory yet.

Key existing infrastructure:
- `SignedFormula.lean` -- Contains a **branch-based** `subformulaClosure` (different from the formula-based one the FMP needs)
- `Decidability.lean` -- Barrel import for existing decidability files

### Available Dependencies (already ported)

| Cslib Module | Provides |
|-------------|----------|
| `Syntax/Formula.lean` | `Formula Atom` type (polymorphic, unlike source `Formula`) |
| `ProofSystem/Axioms.lean` | `Axiom` constructors (`imp_s`, `efq`, `modal_t`, `modal_4`, etc.) |
| `ProofSystem/Derivation.lean` | `DerivationTree`, `FrameClass`, `Context` |
| `Metalogic/Core/MaximalConsistent.lean` | `Consistent`, `MaximalConsistent`, `inconsistent_derives_bot`, `derives_bot_from_phi_neg_phi`, `deduction_theorem` |
| `Metalogic/Core/MCSProperties.lean` | `SetConsistent fc`, `SetMaximalConsistent fc`, `derivation_exchange`, `temp_4_derived`, `temp_4_past` |
| `Metalogic/Core/DeductionTheorem.lean` | `deduction_theorem` |
| `Semantics/TaskFrame.lean` | `TaskFrame`, `FiniteTaskFrame` |
| `Theorems/Perpetuity/Helpers.lean` | `double_negation` |
| `Foundations/Logic/Metalogic/Consistency.lean` | `consistent_chain_union` (generic), `set_lindenbaum` (generic) |

### Missing Dependencies (must port)

1. **`Syntax/Subformulas.lean`** -- `Formula.subformulas` and associated membership lemmas. The target `Formula Atom` type does not have a `subformulas` function.

2. **`Syntax/SubformulaClosure/Closure.lean`** -- `subformulaClosure` (Finset-based), `closureWithNeg`, membership lemmas for all constructors. The existing `subformulaClosure` in `SignedFormula.lean` is branch-based (for tableau use), not formula-based (for FMP use).

3. **`Core/RestrictedMCS/Basic.lean`** (partial) -- `ClosureRestricted`, `RestrictedConsistent`, `RestrictedMCS`, `restricted_lindenbaum`, `restricted_mcs_negation_complete`, `restricted_mcs_exists_containing`, `restricted_mcs_from_formula`. Only the first ~440 lines are needed; the `iter_F`/`iter_P` sections (lines 441-653) depend on `Bundle/` modules which are out of scope.

---

## 3. Namespace Mapping

### Source -> Target Namespace

| Source | Target |
|--------|--------|
| `Bimodal.Metalogic.Decidability.FMP` | `Cslib.Logic.Bimodal.Metalogic.Decidability.FMP` |
| `Bimodal.Syntax` | `Cslib.Logic.Bimodal` |
| `Bimodal.Semantics` | `Cslib.Logic.Bimodal.Semantics` |
| `Bimodal.Metalogic.Core` | `Cslib.Logic.Bimodal.Metalogic.Core` |
| `Bimodal.ProofSystem` | `Cslib.Logic.Bimodal.ProofSystem` (via `Cslib.Logic.Bimodal`) |

### Key Type/Definition Renames

| Source | Target | Notes |
|--------|--------|-------|
| `Formula` (concrete) | `Formula Atom` (polymorphic) | Add `Atom` type parameter everywhere |
| `Axiom.prop_s phi psi` | `Axiom.imp_s phi psi` | Axiom name changed |
| `Axiom.ex_falso phi` | `Axiom.efq phi` | Axiom name changed |
| `SetConsistent (fc := FrameClass.Base) S` | `SetConsistent FrameClass.Base S` | Signature difference (named vs positional) |
| `DerivationTree FrameClass.Base [] phi` | Same, but use `⊢ phi` notation | Notation available |
| `Bimodal.Theorems.TemporalDerived.temp_4_derived` | `temp_4_derived` (in `MCSProperties.lean`) | Already ported as private def |
| `temp_4_past` | `temp_4_past` (in `MCSProperties.lean`) | Already ported as private def |
| `double_negation` | `Cslib.Logic.Bimodal.Theorems.Perpetuity.double_negation` | Already ported |

### Import Mapping

| Source Import | Target Import |
|--------------|---------------|
| `Bimodal.Metalogic.Core.RestrictedMCS.Basic` | New: `Cslib.Logics.Bimodal.Metalogic.Core.RestrictedMCS` |
| `Bimodal.Metalogic.Core.MCSProperties` | `Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties` |
| `Bimodal.Syntax.SubformulaClosure.Closure` | New: `Cslib.Logics.Bimodal.Syntax.SubformulaClosure` |
| `Bimodal.Syntax.Subformulas` | New: `Cslib.Logics.Bimodal.Syntax.Subformulas` |
| `Bimodal.Semantics.Validity` | `Cslib.Logics.Bimodal.Semantics.Validity` |
| `Bimodal.Semantics.Truth` | `Cslib.Logics.Bimodal.Semantics.Truth` |
| `Bimodal.Theorems.TemporalDerived` | Not needed (temp_4_derived/temp_4_past are in MCSProperties) |
| `Bimodal.Theorems.Propositional.Core` | `Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers` (for `double_negation`) |
| `Mathlib.Data.Setoid.Basic` | Same |
| `Mathlib.Data.Fintype.Quotient` | Same |
| `Mathlib.Data.Fintype.Card` | Same |
| `Mathlib.Data.Fintype.Powerset` | Same |
| `Mathlib.Data.Set.Finite.Basic` | Same |
| `Mathlib.Order.Basic` | Same |
| `Mathlib.Order.SuccPred.Basic` | Same |
| `Mathlib.Data.Finset.Basic` | Same |
| `Mathlib.Order.Zorn` | Same |

---

## 4. Dependency Graph

```
Subformulas.lean (NEW)
    |
    v
SubformulaClosure.lean (NEW)
    |
    v
RestrictedMCS.lean (NEW)
    |
    v
ClosureMCS.lean
    |
    v
Filtration.lean
    |
    v
FiniteModel.lean
    |
    v
TruthPreservation.lean
    |
    v
FMP.lean
   / \
  v   v
DenseFMP.lean  DiscreteFMP.lean
```

### External Dependencies
- `Filtration.lean` depends on `Semantics/Validity.lean`, `Semantics/Truth.lean` (already ported)
- `TruthPreservation.lean` depends on `Semantics/Truth.lean`, `Semantics/Validity.lean` (already ported)
- `FMP.lean` depends on `Semantics/Validity.lean`, `Theorems/Perpetuity/Helpers.lean` (for `double_negation`)
- `RestrictedMCS.lean` depends on `Core/MaximalConsistent.lean`, `Core/MCSProperties.lean` (already ported)

---

## 5. Porting Complexity Assessment

### Phase 0: Prerequisite Infrastructure (NEW files)

**File 1: `Cslib/Logics/Bimodal/Syntax/Subformulas.lean`** (~230 lines)
- Port `Formula.subformulas` and all membership lemmas
- **Challenge**: The source uses concrete `Formula`, target uses `Formula Atom`. The `subformulas` function itself is straightforward recursive, but membership lemmas need `Atom` type variable everywhere.
- **Risk**: Low. Straightforward structural port.

**File 2: `Cslib/Logics/Bimodal/Syntax/SubformulaClosure.lean`** (~300 lines, subset of Closure.lean)
- Port `subformulaClosure`, `closureWithNeg`, all membership/subset lemmas
- Skip: diamond detection infrastructure (not needed by FMP)
- **Challenge**: Depends on `Subformulas.lean` above.
- **Risk**: Low. Clean Finset-based definitions with simple proofs.

**File 3: `Cslib/Logics/Bimodal/Metalogic/Core/RestrictedMCS.lean`** (~440 lines)
- Port core RestrictedMCS definitions, restricted Lindenbaum, and formula construction
- Skip: `iter_F`/`iter_P` boundedness theorems (lines 441-653 of source)
- **Challenge**: The source's `consistent_chain_union` for `SetConsistent (fc := FrameClass.Base)` is defined in the source's `MaximalConsistent.lean`. The target has `consistent_chain_union` at the Foundation level for `Metalogic.SetConsistent D`. Need to either:
  (a) Prove a bridge lemma from `Cslib.Logic.Bimodal.Metalogic.Core.SetConsistent fc` to `Metalogic.SetConsistent`, OR
  (b) Prove `consistent_chain_union` directly for the bimodal-specific `SetConsistent fc`
- **Risk**: Medium. The Zorn's lemma application in `restricted_lindenbaum` is the most complex proof here. The chain union lemma needs careful type-level adaptation.

### Phase 1: ClosureMCS.lean (~280 lines)
- Thin wrapper over RestrictedMCS, reexporting with FMP-specific names
- **Challenge**: Minimal -- mostly `abbrev` definitions and simple theorem applications
- **Risk**: Low

### Phase 2: Filtration.lean (~325 lines)
- Filtration equivalence, Setoid, quotient, filtered frame
- **Challenge**: The `RefinedFilteredTaskFrame` definition involves `TaskFrame D` with type class constraints. The proof of `forward_comp` and `converse` for the refined frame uses `AddCommGroup`, `LinearOrder`, `IsOrderedAddMonoid` -- all standard Mathlib constraints.
- **Risk**: Low-Medium. The frame definition proofs should port directly.

### Phase 3: FiniteModel.lean (~180 lines)
- Finiteness via characteristic set injection
- **Challenge**: Uses `Set.instFinite` from Mathlib for finite powerset. Need to verify Mathlib API hasn't changed.
- **Risk**: Low

### Phase 4: TruthPreservation.lean (~400 lines)
- MCS truth definition, bot/negation/implication/box/temporal properties
- **Challenge**: Uses axiom names (`prop_s` -> `imp_s`, `ex_falso` -> `efq`). The `temp_4_derived` and `temp_4_past` are private in the target's MCSProperties -- need to either make them accessible or re-derive them.
- **Risk**: Medium. The `temp_4_derived`/`temp_4_past` are `private def` in the target. The FMP TruthPreservation.lean uses them directly. Options: (a) make them non-private in MCSProperties, (b) re-derive in TruthPreservation, or (c) provide public wrappers.

### Phase 5: FMP.lean (~250 lines)
- Main FMP theorem
- **Challenge**: Uses `double_negation` from Theorems.Propositional.Core. The target has this in Perpetuity/Helpers.
- **Risk**: Low

### Phase 6: DenseFMP.lean + DiscreteFMP.lean (~230 lines)
- Both are trivial delegations to base FMP
- **Challenge**: Near-zero -- both just call `mcs_finite_model_property` and `fmp_contrapositive`
- **Risk**: Minimal

### Phase 7: Barrel import + Integration
- Update `Decidability.lean` barrel to include FMP
- **Risk**: Minimal

---

## 6. Key Technical Challenges

### Challenge 1: Polymorphic Formula Type
- **Impact**: Every definition and theorem gains an `Atom` type parameter
- **Mitigation**: Systematic `variable {Atom : Type*}` at the top of each file
- **Effort**: Low -- mechanical transformation

### Challenge 2: `consistent_chain_union` for Bimodal `SetConsistent`
- **Impact**: The source's `consistent_chain_union` is defined for its own `SetConsistent (fc := FrameClass.Base)`. The target's foundation-level `consistent_chain_union` works with `Metalogic.SetConsistent D`.
- **Solution**: Define `consistent_chain_union` for the bimodal `SetConsistent fc` in `MCSProperties.lean` (or a new helper file). This can be done by showing the bimodal `SetConsistent fc` satisfies the same conditions, or by directly proving the chain union property.
- **Effort**: Medium -- one key proof (~50 lines)

### Challenge 3: Private `temp_4_derived` / `temp_4_past`
- **Impact**: `TruthPreservation.lean` needs these derived theorems
- **Solution**: Make them `protected` or add public wrappers in `MCSProperties.lean`
- **Effort**: Low -- one-line change per definition

### Challenge 4: Axiom Name Differences
- `prop_s` -> `imp_s`
- `ex_falso` -> `efq`
- **Mitigation**: Search-and-replace during porting
- **Effort**: Minimal

---

## 7. Sorry Risk Assessment

The source FMP files contain **zero sorry**. All proofs are complete.

### Potential Sorry Risks in the Port

1. **`restricted_lindenbaum`** (Zorn's lemma application): The chain union lemma adaptation could be tricky. If the bimodal `SetConsistent` doesn't directly match the foundation-level version, a bridge proof is needed.
   - **Mitigation**: The proof structure is identical; only the type signatures differ.
   - **Risk**: Low -- structural translation, not novel proof.

2. **`RefinedFilteredTaskFrame.forward_comp`**: Uses `add_nonneg`, `neg_nonneg`, `le_antisymm` on ordered groups.
   - **Mitigation**: Standard Mathlib API; should be stable.
   - **Risk**: Minimal.

3. **No novel proofs required**: Every theorem in the FMP infrastructure has a complete proof in the source. The port is a namespace/type-parameter adaptation, not new mathematics.

**Assessment**: Zero-sorry completion is achievable.

---

## 8. Recommended File Layout

```
Cslib/Logics/Bimodal/
├── Syntax/
│   ├── Formula.lean          (existing)
│   ├── Subformulas.lean      (NEW - Phase 0)
│   └── SubformulaClosure.lean (NEW - Phase 0)
├── Metalogic/
│   ├── Core/
│   │   ├── RestrictedMCS.lean (NEW - Phase 0)
│   │   ├── MCSProperties.lean (existing, may need edits)
│   │   └── ...
│   └── Decidability/
│       ├── FMP/
│       │   ├── ClosureMCS.lean         (NEW - Phase 1)
│       │   ├── Filtration.lean         (NEW - Phase 2)
│       │   ├── FiniteModel.lean        (NEW - Phase 3)
│       │   ├── TruthPreservation.lean  (NEW - Phase 4)
│       │   ├── FMP.lean               (NEW - Phase 5)
│       │   ├── DenseFMP.lean          (NEW - Phase 6)
│       │   └── DiscreteFMP.lean       (NEW - Phase 6)
│       ├── FMP.lean                   (NEW barrel - Phase 7)
│       └── Decidability.lean          (UPDATE - Phase 7)
```

---

## 9. Estimated Effort

| Phase | Files | Lines | Hours |
|-------|-------|-------|-------|
| Phase 0: Prerequisites | 3 new | ~970 | 3-4 |
| Phase 1: ClosureMCS | 1 new | ~280 | 1 |
| Phase 2: Filtration | 1 new | ~325 | 1.5 |
| Phase 3: FiniteModel | 1 new | ~180 | 1 |
| Phase 4: TruthPreservation | 1 new | ~400 | 2 |
| Phase 5: FMP | 1 new | ~250 | 1 |
| Phase 6: Dense+Discrete | 2 new | ~230 | 0.5 |
| Phase 7: Integration | 2 modified | ~60 | 0.5 |
| **Total** | **12 files** | **~2,695** | **10-11** |

---

## 10. Blockers and Risks

### No Blockers Identified

Task 42 (core tableau) is complete. All prerequisite Lean infrastructure exists.

### Risks

1. **`consistent_chain_union` bridge** (Medium) -- May need 50-80 lines of new proof. Fallback: prove directly for bimodal `SetConsistent fc`.

2. **`temp_4_derived`/`temp_4_past` visibility** (Low) -- These are `private` in target. Either change visibility or re-derive.

3. **Mathlib API drift** (Low) -- `Set.instFinite`, `Fintype.Quotient` etc. may have different names in current Mathlib. Verify with `lean_local_search` during implementation.

---

## 11. Recommendations

1. **Port prerequisites first** (Phase 0) -- `Subformulas.lean`, `SubformulaClosure.lean`, `RestrictedMCS.lean` must exist before any FMP file can compile.

2. **Build incrementally** -- After each phase, run `lake build Cslib.Logics.Bimodal.Metalogic.Decidability.FMP.{Module}` to verify.

3. **Make `temp_4_derived`/`temp_4_past` accessible** -- Change from `private` to `protected` or add public API in MCSProperties.lean during Phase 0.

4. **Verify `consistent_chain_union` approach early** -- The chain union lemma is the most technically uncertain part. Resolve this in Phase 0 before committing to the full FMP port.

5. **Target: zero sorry** -- The source has zero sorry. The port should maintain this standard.
