# Research Report: Task 46 -- Temporal R-Relation and Witness Infrastructure

**Task**: 46 -- Define the Burgess R-relation r(A, beta, C) and prove its key properties
**Date**: 2026-06-09
**Session**: sess_1781037367_539c9b_46

---

## 1. Current State of the Temporal Metalogic Codebase

### 1.1 Existing Files (DO NOT MODIFY)

| File | Lines | Key Content |
|------|-------|-------------|
| `Metalogic/MCS.lean` | 704 | `Temporal.SetConsistent`, `Temporal.SetMaximalConsistent`, `temporal_lindenbaum`, `mcs_g_mp`, `mcs_h_mp`, `mcs_g_witness`, `mcs_h_witness`, `futureSet`, `pastSet` |
| `Metalogic/Completeness.lean` | 418 | `CanonicalWorld`, `canonical_acc`, truth lemma for G/H, `exists_future_successor`, `exists_past_predecessor`, `completeness` (1 sorry at line 416 -- Task 49 target) |
| `Metalogic/DeductionTheorem.lean` | ~9700 | Deduction theorem infrastructure |
| `Metalogic/DerivationTree.lean` | ~80 | Height measure, `Temporal.Deriv`, `temporalDerivationSystem` |
| `Metalogic/Soundness.lean` | ~18700 | Soundness theorem |
| `Theorems/TemporalDerived.lean` | 270 | Typeclass-style temporal derived theorems: `G_distribution`, `H_distribution`, `G_contrapose`, etc. |
| `Theorems/FrameConditions.lean` | exists | Frame condition theorems |

### 1.2 Missing Infrastructure (Phase 0 Prerequisites)

The bimodal Chronicle files import Bundle/ infrastructure that does not yet exist in the temporal module. These must be created as Phase 0 deliverables before the Chronicle files can be ported.

#### 1.2.1 No Temporal Chronicle/ Directory

The directory `Cslib/Logics/Temporal/Metalogic/Chronicle/` does not exist yet. All Chronicle files must be created from scratch.

#### 1.2.2 Key Infrastructure Gaps

1. **g_content/h_content definitions**: The bimodal module has `Bundle/TemporalContent.lean` (169 lines) with `g_content`, `h_content`, `f_content`, `p_content`, `u_content`, `s_content`, plus membership simp lemmas and duality lemmas. The temporal module has `futureSet`/`pastSet` in `MCS.lean` (mathematically equivalent but packaged differently). The chronicle needs the `g_content` formulation.

2. **Witness seed consistency**: The bimodal `Bundle/WitnessSeed.lean` (607 lines) provides `forward_temporal_witness_seed_consistent`, `past_temporal_witness_seed_consistent`, `until_witness_seed_consistent`, `since_witness_seed_consistent`, and the g_content/h_content duality theorems (`g_content_subset_implies_h_content_reverse`, `h_content_subset_implies_g_content_reverse`). The temporal module has `mcs_g_witness` and `mcs_h_witness` in `MCS.lean`, which prove the G/H witness property using inline consistency arguments. The chronicle needs the seed-style formulation.

3. **SetDeductivelyClosed (DCS) type**: Defined in bimodal `ChronicleTypes.lean` with `ClosedUnderDerivation`, `SetDeductivelyClosed`, `mcs_is_dcs`, and helper lemmas (`dcs_modus_ponens`, `dcs_conj_closed`, `cud_not_mem_is_sdc`, etc.). Not present in temporal module.

4. **DerivationTree-level propositional combinators**: The bimodal `Theorems/Propositional/Core.lean` (302 lines) provides `double_negation`, `efq_axiom`, `lce_imp`, `rce_imp`, etc. at the `DerivationTree FrameClass.Base` level. The temporal module already imports `Cslib.Foundations.Logic.Theorems.Propositional.Core` (typeclass style) via `Theorems/TemporalDerived.lean`, but does NOT have DerivationTree-level versions.

5. **DerivationTree-level temporal derived theorems**: The bimodal `Theorems/TemporalDerived.lean` (372 lines) provides `temp_k_dist_derived`, `G_distribution`, `until_imp_F`, `since_imp_P`, etc. at the `DerivationTree FrameClass.Base` level. The temporal module has typeclass versions in `Theorems/TemporalDerived.lean` (270 lines).

---

## 2. Bimodal Source File Analysis

### 2.1 RRelation.lean (1695 lines) -- Primary Target

**Namespace**: `Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle`

**Imports**: ChronicleTypes, Bundle/WitnessSeed, Theorems/TemporalDerived, Theorems/Propositional/Core, Mathlib/Order/Zorn

**Key definitions and theorems** (in dependency order):

| Declaration | Lines | Transfer | Notes |
|-------------|-------|----------|-------|
| `theorem_in_mcs` helper | 66-69 | Rewrite | Use `temporal_closed_under_derivation` |
| `until_implies_F_in_mcs` | 95-102 | Direct | Uses BX10 axiom |
| `until_self_accum_in_mcs` | 107-116 | Direct | Uses BX5 axiom |
| `since_implies_P_in_mcs` | 121-128 | Direct | Uses BX10' axiom |
| `rRelation_guard_continues'` | 138-144 | Direct | Core Lemma 2.3 consequence |
| `deductiveClosure` and DCS machinery | 151-216 | Direct | All purely logical |
| `rMaximal_extension_exists` | 233-296 | Remove `fc` param | Zorn's lemma |
| `rMaximalSince_extension_exists` | 300-333 | Remove `fc` param | Mirror |
| `r3Maximal_extension_exists` | 352-393 | Remove `fc` param | Three-argument |
| `r3MaximalSince_extension_exists` | 398-439 | Remove `fc` param | Mirror |
| `burgessR_absorption` | 489-511 | Direct | Lemma 2.5 (single element) |
| `burgessRSet_absorption` | 519-528 | Direct | Lemma 2.5 (set version) |
| `burgessRSince_absorption` | 536-558 | Direct | Mirror |
| `burgessRSetSince_absorption` | 563-572 | Direct | Mirror |
| `burgessR3_absorption` | 593-607 | Direct | Full three-argument |
| `mcs_contrapositive_mem` | 615-620 | Direct | Helper |
| `c4_hard_case_G_neg_delta` | 637-665 | Adapt | Uses bimodal `liftBase` |
| `c4'_hard_case_H_neg_delta` | 673-700 | Adapt | Mirror |
| `burgessR3Maximal_extension_exists` | 754-783 | Remove `fc` | Key existence theorem |
| BurgessR3Maximal accessor lemmas | 790-809 | Direct | Trivial |
| BurgessR3 bridging lemmas | 828-878 | Direct | Key for C4 |
| `dcs_neg_insert_consistent` | 895-926 | Adapt | Uses bimodal `double_negation` |
| Guard algebra (`untl_conj_guard`, etc.) | 947-1119 | Adapt | Uses bimodal propositional imports |
| `deductiveClosure_singleton_imp` | 1140-1145 | Direct | |
| burgessR propagation | 1154-1174 | Direct | |
| `burgessR3Maximal_exists_from_seed` | 1202-1220 | Remove `fc` | |
| Burgess Lemma 2.3 equivalence | 1222-1487 | Adapt | Core mathematical content |
| Xu's Lemma 3.2.1 | 1488-1583 | Adapt | Uses several helpers |
| `burgessR3Maximal_from_g_content_sub` | 1637-1664 | Adapt | Key infrastructure lemma |
| `burgessR3Maximal_with_guard` | 1678-1693 | Remove `fc` | |

**Bimodal-specific elements to remove**:
- `fc : FrameClass` parameter everywhere (temporal has single system)
- `liftBase` helper (unnecessary)
- `FrameClass.base_le fc` trivial witnesses (replaced by `trivial`)
- `SetMaximalConsistent fc M` becomes `Temporal.SetMaximalConsistent M`
- `SetConsistent fc` becomes `Temporal.SetConsistent` (or an alias)
- `DerivationTree fc L phi` becomes temporal `DerivationTree FrameClass.Base L phi`

**Key observation**: The temporal `DerivationTree` already uses `FrameClass.Base` everywhere (since temporal has only one frame class). So the bimodal `DerivationTree fc` with `fc = FrameClass.Base` maps directly to the temporal `DerivationTree FrameClass.Base`.

### 2.2 ChronicleTypes.lean (300+ lines relevant) -- Definitions Only

**Key definitions to port**:

| Definition | Lines | Transfer | Notes |
|------------|-------|----------|-------|
| `ClosedUnderDerivation` | 70-72 | Direct | Already formula-type-agnostic |
| `SetDeductivelyClosed` | 75-76 | Direct | |
| `mcs_is_dcs` | 79-82 | Adapt | Use temporal MCS |
| DCS helpers | 85-138 | Direct | `cud_contains_theorems`, `dcs_modus_ponens`, `dcs_conj_closed`, etc. |
| `rRelation` | 147-151 | Direct | Core definition |
| `rRelationSince` | 153-155 | Direct | |
| `r3Relation` | 157-158 | Direct | |
| `rMaximal`, `rMaximalSince` | 165-179 | Remove `fc` | |
| `R3Maximal`, `R3MaximalSince` | 181-195 | Remove `fc` | |
| `burgessR`, `burgessRSet`, etc. | 199-218 | Direct | Core Burgess definitions |
| `BurgessR3Maximal` | 214-217 | Remove `fc` | |

**NOT porting from ChronicleTypes**: `Adjacent`, `Chronicle`, `ValidChronicle`, C0-C5 conditions (these are Task 48 scope).

### 2.3 Frame.lean (464 lines) -- Partial Port

| Content | Lines | Transfer | Notes |
|---------|-------|----------|-------|
| `BXPoint` structure | 43-45 | Replace with `TPoint` | Uses `Temporal.SetMaximalConsistent` |
| `bx_le` (temporal ordering) | 49-50 | Rename to `t_le` | `g_content w.formulas ⊆ v.formulas` |
| `bx_modal_equiv` | 52-53 | **REMOVE** | Bimodal-only |
| `g_content_closed_derivation` | 57-70 | Adapt | Uses temporal generalized K |
| `h_content_closed_derivation` | 72-85 | Adapt | Mirror |
| `g_content_set_consistent` | 94-121 | Adapt | Uses temporal serial_future |
| `h_content_set_consistent` | 123-150 | Adapt | Mirror |
| `bx_le_refl` | 154-155 | **SORRY** | Same irreflexive semantics issue |
| `bx_le_trans` | 159-163 | Direct | Uses `all_future_all_future` |
| `bx_forward_witness` | 167-174 | Adapt | Uses temporal witness seed |
| `bx_backward_witness` | 176-185 | Adapt | Mirror |
| `bx_G_forward` / `bx_G_backward` | 189-234 | Adapt | Core G witness |
| `bx_H_forward` / `bx_H_backward` | 238-286 | Adapt | Mirror |
| Modal equivalence (288-393) | | **REMOVE** | Bimodal-only |
| Box preservation (396-434) | | **REMOVE** | Bimodal-only |
| Until/Since eventuality | 442-462 | Adapt | Uses temporal axioms |

### 2.4 CanonicalChain.lean (95 lines) -- 100% Transfer

All content transfers with mechanical changes:
- `BXPoint` -> `TPoint`
- Remove `FrameClass.Base`
- Update namespace
- Remove `Filtration.DefectChain` import (bimodal-only)

Key lemmas: `F_imp_top_until_mcs`, `P_imp_top_since_mcs`, `absorb_until_mcs`, `absorb_since_mcs`, delegation bridges.

### 2.5 OrderedSeedConsistency.lean (151 lines) -- 100% Transfer

All content transfers with mechanical changes. Key lemmas: `enriched_resolving_seed_consistent`, `temp_linearity_mcs`, `two_defect_consistent_seed`, `no_new_f_defects`, `resolved_target_in_successor`.

### 2.6 Bundle/TemporalContent.lean (169 lines) -- Direct Source for Phase 0

Definitions: `g_content`, `h_content`, `f_content`, `p_content`, `u_content`, `s_content`, simp lemmas, duality lemmas.

**Decision point**: The temporal `MCS.lean` already has `futureSet`/`pastSet` defined as:
```lean
def futureSet (Omega) := {phi | Formula.all_future phi in Omega}
def pastSet (Omega) := {phi | Formula.all_past phi in Omega}
```
These are mathematically identical to `g_content`/`h_content`. Options:
- (A) Create `TemporalContent.lean` with `g_content`/`h_content` as aliases to `futureSet`/`pastSet`
- (B) Create independent `g_content`/`h_content` definitions (matching bimodal exactly)
- (C) Use `futureSet`/`pastSet` directly in chronicle files

**Recommendation**: Option (B) -- independent definitions matching bimodal naming exactly. This maximizes Task 41 abstraction potential. Leave `futureSet`/`pastSet` in `MCS.lean` untouched; the chronicle files use `g_content`/`h_content` exclusively.

### 2.7 Bundle/WitnessSeed.lean (607 lines) -- Direct Source for Phase 0

**Core content**:
1. Duality helpers: `some_future_all_future_neg_absurd`, `some_past_all_past_neg_absurd` (67-100)
2. Duality conversions: `neg_some_future_to_all_future_neg`, `neg_some_past_to_all_past_neg` (106-142)
3. Forward witness seed: `forward_temporal_witness_seed`, `forward_temporal_witness_seed_consistent` (148-259)
4. Past witness seed: `past_temporal_witness_seed`, `past_temporal_witness_seed_consistent` (266-376)
5. Until/Since witness seeds: `until_witness_seed_consistent`, `since_witness_seed_consistent` (382-544)
6. g_content/h_content duality: `g_content_subset_implies_h_content_reverse`, `h_content_subset_implies_g_content_reverse` (552-606)

**Key observation**: The temporal `MCS.lean` already proves `mcs_g_witness` and `mcs_h_witness` using inline consistency arguments that are structurally similar to the witness seed proofs but packaged differently (they prove the witness existence directly rather than factoring through seed consistency). The chronicle needs the seed-style formulation because `Frame.lean` calls `forward_temporal_witness_seed_consistent` directly.

---

## 3. Dependency Ordering and Phase Structure

### 3.1 Dependency DAG

```
Phase 0a: TemporalContent.lean (g_content, h_content definitions)
    |
Phase 0b: WitnessSeed.lean (depends on TemporalContent, uses MCS.lean)
    |        \
Phase 0c: ChronicleTypes.lean [DCS portion only] (depends on TemporalContent)
    |         |
Phase 1: Frame.lean (depends on WitnessSeed, ChronicleTypes/DCS)
    |
Phase 2: CanonicalChain.lean (depends on Frame)
    |
Phase 3: OrderedSeedConsistency.lean (depends on Frame, CanonicalChain)
    |
Phase 4: RRelation.lean (depends on ChronicleTypes, WitnessSeed, Frame)
```

### 3.2 Recommended Phase Sequence

**Phase 0a** (~100-120 lines): `Temporal/Metalogic/TemporalContent.lean`
- `g_content`, `h_content`, `f_content`, `p_content`, `u_content`, `s_content`
- Membership simp lemmas
- No duality lemmas yet (those go in WitnessSeed)

**Phase 0b** (~400-500 lines): `Temporal/Metalogic/WitnessSeed.lean`
- Duality helpers: `some_future_all_future_neg_absurd`, etc.
- Duality conversions: `neg_some_future_to_all_future_neg`, etc.
- Forward/past witness seed definitions and consistency
- Until/since witness seed consistency
- g_content/h_content duality theorems
- NOTE: This is the heaviest Phase 0 deliverable. The bimodal version is 607 lines but is parameterized over `fc : FrameClass`. The temporal version should be shorter (~400-500 lines) because `fc` is always `FrameClass.Base`.

**Phase 0c** (~80-100 lines): `Temporal/Metalogic/Chronicle/ChronicleTypes.lean`
- DCS definitions only: `ClosedUnderDerivation`, `SetDeductivelyClosed`, `mcs_is_dcs`
- DCS helpers: `dcs_modus_ponens`, `dcs_conj_closed`, `cud_contains_theorems`, etc.
- r-relation definitions: `rRelation`, `rRelationSince`, `r3Relation`
- Maximality definitions: `rMaximal`, `rMaximalSince`, `R3Maximal`, etc.
- Burgess relation definitions: `burgessR`, `burgessRSet`, `BurgessR3Maximal`, etc.
- NO Chronicle structure, conditions, or ValidChronicle (Task 48 scope)

**Phase 1** (~200-280 lines): `Temporal/Metalogic/Chronicle/Frame.lean`
- `TPoint` structure (replacing `BXPoint`)
- `t_le` temporal ordering
- `g_content_closed_derivation`, `h_content_closed_derivation`
- `g_content_set_consistent`, `h_content_set_consistent`
- `t_le_refl` (sorry -- same irreflexive semantics issue as bimodal)
- `t_le_trans`
- Forward/backward temporal witnesses
- G/H forward/backward lemmas
- Until/Since eventuality resolution
- NO modal equivalence, box preservation (bimodal-only)

**Phase 2** (~50-70 lines): `Temporal/Metalogic/Chronicle/CanonicalChain.lean`
- `F_imp_top_until_mcs`, `P_imp_top_since_mcs`
- `absorb_until_mcs`, `absorb_since_mcs`
- Delegation bridges

**Phase 3** (~80-100 lines): `Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean`
- `enriched_resolving_seed_consistent`
- `temp_linearity_mcs`
- `two_defect_consistent_seed`
- `no_new_f_defects`
- `resolved_target_in_successor`

**Phase 4** (~800-1000 lines): `Temporal/Metalogic/Chronicle/RRelation.lean`
- All r-relation lemmas from bimodal RRelation.lean
- Deductive closure infrastructure
- R-maximal extension existence (Zorn)
- Burgess absorption lemmas (Lemma 2.5)
- BurgessR3Maximal existence and properties
- Guard algebra
- Burgess Lemma 2.3 equivalence
- Xu's Lemma 3.2.1
- BurgessR3Maximal from g_content inclusion

---

## 4. Technical Challenges and Risks

### 4.1 Derivation API Differences (CRITICAL)

The bimodal chronicle uses `DerivationTree fc L phi` with explicit `fc : FrameClass` parameter. The temporal module uses the same `DerivationTree` type but always at `FrameClass.Base`. This means:

- Bimodal: `DerivationTree fc [] phi` where `fc` varies
- Temporal: `DerivationTree FrameClass.Base [] phi` always

The bimodal `liftBase` helper (`d.lift (FrameClass.base_le fc)`) is unnecessary in temporal because all derivations are already at `Base`. Every occurrence of `(FrameClass.base_le fc)` becomes `trivial` and every `liftBase fc d` becomes just `d`.

However, the temporal `MCS.lean` wraps derivations in `Nonempty`: `temporalDerivationSystem.Deriv L phi` is `Nonempty (DerivationTree FrameClass.Base L phi)`. The bimodal chronicle works with bare `DerivationTree` objects. The temporal chronicle will need to use the `Nonempty` wrapper consistently. This is a systematic but mechanical change.

**Action**: Use `temporal_closed_under_derivation` (from MCS.lean) which takes `temporalDerivationSystem.Deriv L phi` (i.e., `Nonempty (DerivationTree ...)`). When constructing derivation trees, wrap with `Nonempty.intro` or `exact <...>`.

### 4.2 Propositional Combinators

The bimodal RRelation.lean imports `Theorems/Propositional/Core.lean` for `double_negation`, `lce_imp`, `rce_imp`, `efq_axiom`. The temporal module does NOT have DerivationTree-level versions of these.

**Options**:
- (A) Create `Temporal/Theorems/Propositional/Core.lean` (~200 lines)
- (B) Directly construct the needed derivation trees inline
- (C) Use the Foundations typeclass versions and lift

**Recommendation**: Option (C) is cleanest. The existing `Cslib.Foundations.Logic.Theorems.Propositional.Core` provides `double_negation`, `efq`, `lce_imp`, `rce_imp` etc. as typeclass theorems. The temporal `Formula` type has the needed typeclass instances. When a DerivationTree-level version is needed, construct it from the axiom system directly (the proofs are short -- 5-15 lines each). For frequently used ones, define private helpers in the chronicle files.

**Revised recommendation**: Actually, examining the usage in `Frame.lean` and `RRelation.lean`, these are called dozens of times. Creating a small file with the temporal DerivationTree-level versions would reduce code duplication significantly. Create `Temporal/Metalogic/PropositionalHelpers.lean` (~100 lines) with the most-used ones.

### 4.3 Temporal Derived Theorem API

The bimodal RRelation.lean uses `Theorems.TemporalDerived.temp_k_dist_derived`, `Theorems.past_k_dist`, `Theorems.generalized_temporal_k`, `Theorems.generalized_past_k`, `Theorems.past_necessitation` at the DerivationTree level.

The temporal module already has typeclass-level versions in `Theorems/TemporalDerived.lean` but NOT DerivationTree-level versions. The bimodal `Theorems/TemporalDerived.lean` (372 lines) provides these.

**Key question**: Does the temporal `DerivationTree` already have `temporal_necessitation` and `temporal_duality`? YES -- these are constructors of the temporal `DerivationTree` inductive type.

The missing pieces are the **derived** theorems like `generalized_temporal_k` (distributing G over a context) and `temp_k_dist_derived` (K distribution for G). These are used heavily in `WitnessSeed.lean` and `Frame.lean`.

**Action**: Either port the needed derived theorems to a new `Temporal/Metalogic/TemporalDerivedHelpers.lean`, or inline them. Given the heavy usage, a small helper file is justified.

### 4.4 Sorry Status

The bimodal RRelation.lean has NO sorry stubs in the active code. The seed research mentioned "open guard semantics sorrys" but these were from a comment about REMOVED axioms (BX9, until_guard). The current code does NOT use these removed axioms and has no sorrys.

The only sorry in the temporal module is in `Completeness.lean` at line 416 (the completeness theorem itself -- Task 49 target). This does not affect Task 46.

`Frame.lean` has one sorry: `bx_le_refl` (reflexivity under irreflexive semantics). This will carry over as `t_le_refl` with the same sorry.

### 4.5 `set_lindenbaum_base` vs `temporal_lindenbaum`

The bimodal `Frame.lean` calls `set_lindenbaum_base` to extend consistent sets to MCS at `FrameClass.Base`. The temporal module has `temporal_lindenbaum` which does the same thing. These are direct substitutions.

### 4.6 Naming Convention

Following the seed research recommendation: keep identical names to bimodal for Task 41 abstraction, EXCEPT:
- `BXPoint` -> `TPoint` (different MCS types)
- `bx_le` -> `t_le` (clarity)
- `bx_forward_witness` -> `t_forward_witness` (clarity)

All r-relation names (`rRelation`, `rMaximal`, `burgessR`, `BurgessR3Maximal`, etc.) stay identical.

---

## 5. Literature Proof Structure

**Source**: Burgess 1982, "Axioms for tense logic II: Time periods", Section 2

### Step Map

1. **Lemma 2.2 (Consistency Criterion)**: If A is MCS and U(gamma, delta) in A, then gamma is consistent.
   - NOTE: This is FALSE under strict (irreflexive) Until semantics for gamma = bot
   - The codebase DOES NOT implement this lemma directly
   - Instead uses BX10 (`until_implies_F_in_mcs`) and BX5 (`until_self_accum_in_mcs`)

2. **Lemma 2.3 (r-relation definition and equivalence)**:
   - Define `rRelation(A, B)` and `burgessR(A, beta, C)`
   - Prove equivalence: `burgessR(A, beta, C) <-> burgessRSince(C, beta, A)` (lines 1363-1474)
   - Uses BX4/BX4' (connect_future/past) and BX3/BX3' (right_mono_until/since)
   - Uses A3a/A3b (enrichment_until/since) -- the bridging axioms

3. **Lemma 2.4 (Witness Existence)**: If U(gamma, beta) in A, then exists B, C with beta in B, gamma in C, R(A, B, C)
   - Implemented as `burgessR3Maximal_exists_from_seed` (lines 1202-1220)
   - Proof: Construct seed from eta, take deductive closure, apply Zorn

4. **Lemma 2.5 (Absorption / Intersection Identity)**: Transitivity of the r-relation
   - Implemented as `burgessR_absorption` (lines 489-511) and `burgessR3_absorption` (lines 593-607)
   - Uses BX6 (absorb_until) and BX6' (absorb_since)

### Potential Formalization Challenges

- Step 2 (Lemma 2.3 equivalence) is the most complex proof in RRelation.lean (~250 lines)
- The proof requires several duality helpers that bridge between `some_future`/`all_future` and negation
- Step 3 (witness existence) requires Zorn's lemma from Mathlib

---

## 6. Revised Line Count Estimates

| Phase | File | Estimated Lines |
|-------|------|-----------------|
| 0a | TemporalContent.lean | 100-120 |
| 0b | WitnessSeed.lean | 400-500 |
| 0c | ChronicleTypes.lean (DCS/definitions only) | 80-100 |
| 0-helper | PropositionalHelpers.lean | 60-80 |
| 1 | Frame.lean | 200-280 |
| 2 | CanonicalChain.lean | 50-70 |
| 3 | OrderedSeedConsistency.lean | 80-100 |
| 4 | RRelation.lean | 800-1000 |
| **Total** | | **1770-2250** |

This revises the seed research estimate of 1200-2000 slightly upward due to the PropositionalHelpers file and the fact that some derivation tree constructions will be slightly longer in the temporal module (explicit `Nonempty` wrapping).

---

## 7. Recommended Approach

### 7.1 Implementation Order

Follow the dependency DAG strictly:
1. Phase 0a: TemporalContent.lean
2. Phase 0b: WitnessSeed.lean (heaviest prerequisite)
3. Phase 0c: ChronicleTypes.lean (definitions only)
4. Phase 0-helper: PropositionalHelpers.lean (inline private helpers OR separate file)
5. Phase 1: Frame.lean
6. Phase 2: CanonicalChain.lean
7. Phase 3: OrderedSeedConsistency.lean
8. Phase 4: RRelation.lean

### 7.2 Key Design Decisions

1. **g_content naming**: Use `g_content`/`h_content` (not `futureSet`/`pastSet`) in all chronicle files
2. **No fc parameter**: All temporal derivations are at `FrameClass.Base`. Remove `fc` parameter everywhere
3. **Nonempty wrapping**: Use `Nonempty (DerivationTree ...)` consistently via `temporal_closed_under_derivation`
4. **Propositional helpers**: Create as private definitions within the files that use them (avoid creating a separate public file that would add to maintenance burden)
5. **DCS type**: Place in `ChronicleTypes.lean` within the Chronicle namespace
6. **No sorry except t_le_refl**: The reflexivity sorry from bimodal carries over unchanged

### 7.3 Testing Strategy

After each phase:
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.{ModuleName}`
- Verify no new sorrys (except `t_le_refl`)
- Verify existing `Completeness.lean` still compiles (no import conflicts)

After all phases:
- `lake build` full project
- Verify the single sorry in `t_le_refl` is the only new sorry

---

## 8. Blockers

None identified. All prerequisites are available:
- Mathlib's `Order.Zorn` for Zorn's lemma (already imported by bimodal RRelation.lean)
- The temporal `Formula` type has the same constructors as bimodal (atom, bot, imp, untl, snce)
- The temporal `DerivationTree` has all needed constructors (axiom, assumption, modus_ponens, temporal_necessitation, temporal_duality, weakening)
- All needed axioms (BX2-BX7, BX10, BX12, A3a/A3b, BX4/BX4', serial_future/past) are present in the temporal axiom system
