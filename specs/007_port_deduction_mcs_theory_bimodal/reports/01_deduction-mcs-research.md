# Research Report: Task 7 -- Port Deduction Infrastructure and MCS Theory

**Task**: 7 -- Port Deduction Infrastructure and MCS Theory (PR 6)
**Session**: sess_1780988937_c2e52d
**Date**: 2026-06-09
**Status**: Researched

## 1. Source File Inventory

All source files are located at `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Core/`.

| Source File | Lines | Key Contents |
|-------------|-------|-------------|
| DeductionTheorem.lean | 441 | Deduction theorem via well-founded recursion on height |
| MaximalConsistent.lean | 528 | Consistent, MaximalConsistent, SetConsistent, SetMaximalConsistent, Lindenbaum lemma, basic closure |
| MCSProperties.lean | 366 | Set-based MCS closure, implication property, negation completeness, temporal 4 future/past |
| RestrictedMCS/Basic.lean | 653 | ClosureRestricted, RestrictedMCS, restricted Lindenbaum, iter_F/P boundedness |
| RestrictedMCS/Deferral.lean | 764 | DeferralRestrictedMCS, deferral Lindenbaum, closure under derivation, iter_F/P boundedness |
| Core.lean | 25 | Barrel import file |
| **Total** | **2,777** | |

## 2. Existing cslib Infrastructure Assessment

### 2.1 Namespace Convention

cslib uses `Cslib.Logic.Bimodal` as the namespace (not `Cslib.Logics.Bimodal` despite the file path). All existing bimodal modules follow this pattern.

### 2.2 Formula Type

The cslib `Formula` type is **parametric over `Atom : Type u`**, unlike the source which uses a fixed `Formula` type. This is a significant porting difference -- all definitions and theorems must be polymorphic in `Atom`.

- **cslib**: `Formula (Atom : Type u) : Type u` with constructors `atom`, `bot`, `imp`, `box`, `untl`, `snce`
- **Source**: `Formula : Type` (not polymorphic)

### 2.3 DerivationTree

cslib's `DerivationTree` matches the source structurally but with parametric `Atom`:
- 7 constructors: `axiom`, `assumption`, `modus_ponens`, `necessitation`, `temporal_necessitation`, `temporal_duality`, `weakening`
- Height function: `DerivationTree.height` with `mp_height_gt_left` and `mp_height_gt_right`
- **Missing**: `subderiv_height_lt` (needed for weakening case in deduction theorem termination proof)

### 2.4 Axiom Names (Differences)

| Source Name | cslib Name | Description |
|-------------|-----------|-------------|
| `Axiom.prop_k` | `Axiom.imp_k` | Distribution (K combinator) |
| `Axiom.prop_s` | `Axiom.imp_s` | Weakening (S combinator) |
| `Axiom.ex_falso` | `Axiom.efq` | Ex falso quodlibet |
| `Axiom.right_mono_until` | `Axiom.right_mono_until` | Same |
| `Axiom.right_mono_since` | `Axiom.right_mono_since` | Same |

### 2.5 Available Propositional Theorems (via Helpers)

The `Cslib.Logic.Bimodal.Theorems.Perpetuity.Helpers` module provides DerivationTree-level bridges:
- `identity`: `|- phi -> phi`
- `imp_trans`: Transitivity of implication
- `dni`: Double negation introduction
- `contraposition`: From `|- phi -> psi`, derive `|- neg psi -> neg phi`
- `double_negation`: Double negation elimination `|- neg neg phi -> phi`

### 2.6 Generic MCS Foundations (Task 29)

`Cslib/Foundations/Logic/Metalogic/Consistency.lean` (273 lines) provides:
- `DerivationSystem F` structure with `Deriv`, `weakening`, `assumption`, `mp`
- `Consistent`, `SetConsistent`, `SetMaximalConsistent`
- `consistent_chain_union`, `set_lindenbaum`
- `HasDeductionTheorem D`
- `closed_under_derivation`, `implication_property`, `negation_complete`

This generic framework can be instantiated for bimodal logic, similar to how temporal logic instantiates it in `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean`.

### 2.7 Temporal Pattern (Task 31)

The temporal metalogic provides the exact porting template:
1. `DerivationTree.lean`: defines `Temporal.Deriv` (Prop-valued), creates `temporalDerivationSystem` instance
2. `DeductionTheorem.lean`: proves deduction theorem, instantiates `HasDeductionTheorem`
3. `MCS.lean`: defines abbreviations (`Temporal.SetConsistent`, `Temporal.SetMaximalConsistent`), provides domain-specific MCS properties

### 2.8 Missing Infrastructure

| Missing Component | Needed By | Impact |
|-------------------|-----------|--------|
| `subderiv_height_lt` | DeductionTheorem.lean | Must add to Derivation.lean (trivial, 3 lines) |
| `temp_4_derived` (Gφ -> GGφ) | MCSProperties.lean | Must port from source or derive from foundation theorems |
| `past_necessitation` | MCSProperties.lean | Must port or derive via temporal duality |
| `SubformulaClosure` module | RestrictedMCS | **NOT available** -- entire module unported |
| `Bundle` modules (CanonicalTaskRelation, SuccExistence) | RestrictedMCS | **NOT available** -- entire module unported |
| `NestingDepth` module | RestrictedMCS | **NOT available** -- entire module unported |
| `deferralClosure` | Deferral.lean | **NOT available** -- unported |

## 3. Dependency Analysis

### 3.1 Cross-File Dependencies (Source)

```
DeductionTheorem.lean
    imports: Derivation, Combinators
    ↓
MaximalConsistent.lean
    imports: ProofSystem, Semantics, DeductionTheorem, Propositional.Core, Zorn
    ↓
MCSProperties.lean
    imports: DeductionTheorem, MaximalConsistent, TemporalDerived
    ↓
RestrictedMCS/Basic.lean
    imports: MaximalConsistent, MCSProperties, SubformulaClosure.NestingDepth,
             Bundle.CanonicalTaskRelation, Bundle.SuccExistence
    ↓
RestrictedMCS/Deferral.lean
    imports: RestrictedMCS.Basic, Bundle.SuccExistence
```

### 3.2 What Can Be Ported Now

The first three files (DeductionTheorem, MaximalConsistent, MCSProperties) can be ported:
- Their dependencies are satisfied (ProofSystem from task 4, Perpetuity from task 5, generic MCS from task 29)
- They only need minor additions (`subderiv_height_lt`, temporal derived theorems)

### 3.3 What Cannot Be Ported Yet

**RestrictedMCS/Basic.lean** and **RestrictedMCS/Deferral.lean** depend on:
- `SubformulaClosure.NestingDepth` -- defines `closureWithNeg`, `subformulaClosure`, `f_nesting_depth`, `p_nesting_depth`, `closure_F_bound`, `closure_P_bound`
- `Bundle.CanonicalTaskRelation` -- defines `iter_F`, `iter_P`
- `Bundle.SuccExistence` -- defines `iter_F_one_eq_some_future`, `iter_P_one_eq_some_past`, `iter_F_leaves_closure`, `iter_P_leaves_closure`, `deferralClosure`, and many more

These are large modules (likely 1000+ lines each) from the completeness machinery. They are not ported and are not dependencies of this task.

## 4. Porting Strategy

### 4.1 Recommended Approach: Port Core Three + Barrel (Skip RestrictedMCS)

**Phase 1: Prerequisite additions (small)**
- Add `subderiv_height_lt` to `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean`
- Add temporal derived theorems (`temp_4_derived`, `past_necessitation`) as bimodal DerivationTree-level helpers, likely in a new file `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` or extend `Perpetuity/Helpers.lean`

**Phase 2: DeductionTheorem.lean**
- Port to `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean`
- Namespace: `Cslib.Logic.Bimodal.Metalogic.Core`
- Key adaptations:
  - Add `Atom` type parameter throughout
  - Rename `Axiom.prop_s` -> `Axiom.imp_s`, `Axiom.prop_k` -> `Axiom.imp_k`
  - Use cslib `DerivationTree` constructors and notations
  - Port the `removeAll` helper
  - Well-founded recursion on `height` (same structure)

**Phase 3: MaximalConsistent.lean**
- Port to `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean`
- **Key decision**: The generic framework from task 29 provides `SetConsistent`, `SetMaximalConsistent`, `set_lindenbaum`, etc. The source duplicates these definitions specifically for the bimodal `DerivationTree`.
- **Recommended approach**: Create a `bimodalDerivationSystem` instance (like the temporal pattern), then define bimodal-specific abbreviations. Use the generic theorems where possible, and add bimodal-specific list-based consistency (`Consistent`, `MaximalConsistent`) that the deduction theorem works with directly.
- MCS closure properties that use the deduction theorem: delegate to generic `closed_under_derivation` after proving `HasDeductionTheorem` for the bimodal system.

**Phase 4: MCSProperties.lean**
- Port to `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean`
- Contains: `cons_filter_neq_perm`, `derivation_exchange`, temporal 4 future/past properties
- The temporal 4 properties require `temp_4_derived` and `past_necessitation` (from Phase 1)

**Phase 5: Barrel file + verification**
- Create `Cslib/Logics/Bimodal/Metalogic/Core.lean` barrel import
- Run `lake build`, verify zero sorry, zero errors

### 4.2 RestrictedMCS Deferral

The RestrictedMCS files should be **deferred to a later task** (likely task 34 or 35, which port completeness infrastructure). Reasons:
1. They depend on unported `SubformulaClosure` and `Bundle` modules
2. They represent ~1,417 lines of code with deep external dependencies
3. The core MCS infrastructure (DeductionTheorem + MaximalConsistent + MCSProperties) is self-contained and useful independently
4. Tasks 9 (Decidability) and 34 (base completeness) both depend on task 7 but can use the core three files

### 4.3 Reuse of Generic Framework

A key architectural decision: whether MaximalConsistent.lean duplicates set-based definitions or reuses the generic framework.

**Recommended**: Follow the temporal pattern:
1. Create `bimodalDerivationSystem : Metalogic.DerivationSystem (Formula Atom)` in a bridging section
2. Define abbreviations: `Bimodal.SetConsistent`, `Bimodal.SetMaximalConsistent`
3. Prove `bimodal_has_deduction_theorem : HasDeductionTheorem bimodalDerivationSystem`
4. Generic lemmas (`set_lindenbaum`, `closed_under_derivation`, `implication_property`, `negation_complete`) become immediate corollaries

This avoids re-proving ~150 lines of generic MCS theory and keeps the architecture consistent with temporal logic.

**However**: The source also defines list-based `Consistent` and `MaximalConsistent` which the deduction theorem uses directly. These are needed for the list-based MCS closure proofs. Keep these as bimodal-specific definitions alongside the generic set-based ones.

## 5. Complexity Estimates per File

| File | Source Lines | Est. Port Lines | Difficulty | Notes |
|------|-------------|-----------------|-----------|-------|
| Prerequisites | -- | ~80 | Low | `subderiv_height_lt`, temporal derived helpers |
| DeductionTheorem.lean | 441 | ~400 | Medium-High | Well-founded recursion, `Atom` parametricity |
| MaximalConsistent.lean | 528 | ~350 | Medium | Much delegates to generic framework |
| MCSProperties.lean | 366 | ~300 | Medium | Temporal 4 properties need derived theorems |
| Core.lean (barrel) | 25 | ~15 | Trivial | Just imports |
| **Total (portable)** | **1,360** | **~1,145** | | |

The reduction from 1,360 to ~1,145 is due to reuse of the generic MCS framework from task 29.

## 6. Risk Areas

### 6.1 Well-Founded Recursion Termination (DeductionTheorem)

The deduction theorem uses `termination_by h.height` with `decreasing_by simp_wf`. The cslib `Derivation.lean` may need `subderiv_height_lt` for the weakening case. Risk: low -- the proof structure is identical, just needs the lemma added.

### 6.2 Atom Parametricity

The source uses a fixed `Formula` type. cslib uses `Formula (Atom : Type u)`. All definitions must be universe-polymorphic. Risk: low-medium -- mostly mechanical, but may require explicit universe annotations.

### 6.3 Axiom Name Mismatches

Several axioms are renamed between source and cslib (`prop_s` -> `imp_s`, etc.). Risk: low -- systematic search-and-replace.

### 6.4 DerivationSystem Instance

Creating the `bimodalDerivationSystem` instance requires matching cslib's `Nonempty` wrapper pattern vs. the source's direct `DerivationTree` usage. The temporal metalogic has already solved this pattern, so risk is low.

### 6.5 Temporal Derived Theorems

The MCSProperties file depends on `temp_4_derived` (Gφ -> GGφ) and `past_necessitation`. These are multi-step derivations from the source's `Theorems/TemporalDerived.lean`. They either need to be ported as prerequisite helpers or re-derived from the cslib foundation theorems. Risk: medium -- the proofs are ~50-80 lines each and involve BX axioms.

### 6.6 `FrameClass` Parametricity

The source MCS definitions are parametric over `FrameClass` (e.g., `Consistent {fc : FrameClass} (Gamma : Context)`). The generic framework from task 29 does not have frame class parameters. This means the bimodal-specific list-based definitions keep their `fc` parameter, while the generic set-based definitions operate at a fixed level. The `bimodalDerivationSystem` should be defined at `FrameClass.Base` (like temporal) with `lift` for other frame classes.

## 7. Detailed Porting Notes per File

### DeductionTheorem.lean

- **Namespace**: `Cslib.Logic.Bimodal.Metalogic.Core`
- **Imports**: `Cslib.Logics.Bimodal.ProofSystem.Derivation`, `Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers`
- **Key changes**:
  - Replace `Bimodal.Syntax.Formula` with `Bimodal.Formula Atom`
  - Replace `Bimodal.ProofSystem.DerivationTree` with `Bimodal.DerivationTree`
  - Replace `Axiom.prop_s` with `Axiom.imp_s`, `Axiom.prop_k` with `Axiom.imp_k`
  - Add `variable {Atom : Type*}` at section level
  - Use `Bimodal.FrameClass.base_le` instead of `FrameClass.base_le`
  - Port `removeAll`, `removeAll_subset`, `cons_removeAll_perm` helpers
  - The `identity` combinator is available from `Helpers.lean`
  - Well-founded recursion structure is identical

### MaximalConsistent.lean

- **Namespace**: `Cslib.Logic.Bimodal.Metalogic.Core`
- **Imports**: `Cslib.Logics.Bimodal.ProofSystem.Derivation`, `Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem`, `Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers`, `Cslib.Foundations.Logic.Metalogic.Consistency`, `Mathlib.Order.Zorn`
- **Key changes**:
  - Define `bimodalDerivationSystem` at FrameClass.Base as `Metalogic.DerivationSystem (Bimodal.Formula Atom)`
  - Define bimodal-specific `Consistent` and `MaximalConsistent` for list-based (needed by deduction theorem proofs)
  - Define `Bimodal.SetConsistent` / `Bimodal.SetMaximalConsistent` as abbreviations of generic framework
  - Lindenbaum lemma: delegate to `Metalogic.set_lindenbaum`
  - Keep `inconsistent_derives_bot`, `derives_neg_from_inconsistent_extension`, `derives_bot_from_phi_neg_phi` as bimodal-specific helpers
  - The `usedFormulas` function and related lemmas can be omitted since the generic framework handles chain union internally
  - MCS closure properties: delegate to generic `closed_under_derivation` etc.
  - Keep `theorem_in_mcs` (specific to bimodal with its own proof pattern)

### MCSProperties.lean

- **Namespace**: `Cslib.Logic.Bimodal.Metalogic.Core`
- **Imports**: `Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem`, `Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent`
- **Key changes**:
  - `cons_filter_neq_perm` and `derivation_exchange` port directly
  - For temporal 4 properties: need `temp_4_derived` and `temp_4_past` which use `TemporalDerived.temp_4_derived` and `past_necessitation`
  - Either port the derived theorems inline or create a prerequisite module
  - `set_consistent_not_both` may delegate to generic `set_consistent_not_both`
  - `neg_excludes` ports directly

## 8. File Structure (Target)

```
Cslib/Logics/Bimodal/
  ProofSystem/
    Derivation.lean          (ADD: subderiv_height_lt)
  Theorems/
    Perpetuity/
      Helpers.lean           (existing, may ADD: past_necessitation, temp_4_derived)
  Metalogic/
    Core/
      DeductionTheorem.lean  (NEW: ~400 lines)
      MaximalConsistent.lean (NEW: ~350 lines)
      MCSProperties.lean     (NEW: ~300 lines)
    Core.lean                (NEW: barrel, ~15 lines)
```

## 9. Recommendations

1. **Port the core three files** (DeductionTheorem, MaximalConsistent, MCSProperties) as they are self-contained with existing dependencies.
2. **Defer RestrictedMCS** to a later task that ports SubformulaClosure and Bundle infrastructure.
3. **Follow the temporal pattern** for generic MCS framework integration.
4. **Add prerequisite lemmas first**: `subderiv_height_lt`, `temp_4_derived`, `past_necessitation`.
5. **Estimated total**: ~1,145 lines of new code across 4 files (3 core + 1 barrel), plus ~80 lines of prerequisite additions to existing files.
