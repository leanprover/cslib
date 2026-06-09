# Research Report: Task 48 — Temporal Counterexample Elimination and Chronicle Construction

**Task**: 48 — Temporal counterexample elimination and chronicle construction
**Date**: 2026-06-09
**Session**: sess_1781037367_539c9b_48

---

## 1. Executive Summary

Task 48 ports two files from the bimodal Chronicle to temporal:
- `CounterexampleElimination.lean` (3529 lines bimodal -> estimated 2200-2800 temporal)
- `ChronicleConstruction.lean` (1531 lines bimodal -> estimated 1200-1500 temporal)

Both files have **zero sorry stubs** in bimodal. The `[Denumerable (Formula Atom)]` instance exists at `Cslib/Logics/Temporal/Syntax/Formula.lean:208`. The transfer rate is genuinely ~95% -- the only changes are mechanical namespace/import rewrites and FrameClass parameter removal.

**However**, a key prerequisite is missing: the temporal code has no `Chronicle` structure or `Adjacent` definition. These must be created as part of this task (either in a new file or at the top of `CounterexampleElimination.lean`). The bimodal `ChronicleTypes.lean` defines both, but the temporal `ChronicleTypes.lean` only defines DCS infrastructure and r-relation types -- not the Chronicle structure itself.

---

## 2. Infrastructure Audit

### 2.1 Chronicle Structure (MISSING -- Must Create)

The bimodal `Chronicle Atom` structure is defined at `BXCanonical/Chronicle/ChronicleTypes.lean:221`:

```lean
structure Chronicle (Atom : Type*) where
  f : Rat → Set (Formula Atom)
  g : Rat → Rat → Set (Formula Atom)
  dom : Finset Rat
```

The temporal `ChronicleTypes.lean` (216 lines) defines DCS, r-relation, R3Maximal, BurgessR3Maximal -- but NOT the Chronicle structure, Adjacent, or chronicle conditions (c0, c2', c4, etc.).

**Required additions to temporal `ChronicleTypes.lean`** (or a new file):
1. `Adjacent (dom : Finset Rat) (x y : Rat) : Prop` -- identical to bimodal
2. `structure Chronicle (Atom : Type*)` -- identical to bimodal
3. `Chronicle.c0` -- remove `fc : FrameClass` parameter, use `Temporal.SetMaximalConsistent`
4. `Chronicle.c2'` -- remove `fc : FrameClass`, use temporal `BurgessR3Maximal`
5. `Chronicle.c4`, `Chronicle.c4'`, `Chronicle.c5`, `Chronicle.c5'` -- no FrameClass needed
6. `ChronicleInvariant` -- simplified for temporal

### 2.2 Denumerable Instance (EXISTS)

```lean
-- At Cslib/Logics/Temporal/Syntax/Formula.lean:207-209
noncomputable instance [Countable Atom] [Infinite Atom] :
    Denumerable (Formula Atom) :=
  Classical.choice (nonempty_denumerable (Formula Atom))
```

This requires `[Countable Atom]` and `[Infinite Atom]` constraints on `Atom`. The bimodal version has the same pattern.

### 2.3 Point Insertion Lemmas (EXIST)

All point insertion lemmas needed by CounterexampleElimination exist in temporal `PointInsertion.lean` (2888 lines):

| Bimodal Lemma | Temporal Equivalent | Status |
|---|---|---|
| `lemma_2_4` | `lemma_2_4` (line 276) | EXISTS |
| `lemma_2_4_with_guard` | `lemma_2_4_with_guard` (line 2217) | EXISTS |
| `lemma_2_4_since_with_guard` | `lemma_2_4_since_with_guard` (line 2868) | EXISTS |
| `lemma_2_6_splitting` | `lemma_2_6_splitting` (line 1188) | EXISTS |
| `lemma_2_7` | `lemma_2_7` (line 1884) | EXISTS |
| `lemma_2_7_since` | `lemma_2_7_since` (line 2520) | EXISTS |
| `lemma_2_8` | `lemma_2_8` (line 2135) | EXISTS |
| `lemma_2_8_since` | `lemma_2_8_since` (line 2787) | EXISTS |

### 2.4 MCS/Propositional Helpers (MOSTLY EXIST)

Available in temporal:
- `double_negation` -- `PropositionalHelpers.lean:32`
- `dni` -- `PropositionalHelpers.lean:160`
- `efq_axiom` -- `PropositionalHelpers.lean:52`
- `imp_trans` -- `PropositionalHelpers.lean:57`
- `pairing` -- `PropositionalHelpers.lean:70`
- `lce_imp` / `rce_imp` -- `PropositionalHelpers.lean:91/134`
- `conj_left_mcs` / `conj_right_mcs` -- `PointInsertion.lean:425/433`
- `conj_mcs` -- `PointInsertion.lean:332`
- `self_accum_until_mcs` / `self_accum_since_mcs` -- `PointInsertion.lean:306/313`
- `G_implies_F_mcs` / `H_implies_P_mcs` -- `PointInsertion.lean:443/472`
- `connect_future_mcs'` -- `PointInsertion.lean:323`
- `some_future_all_future_neg_absurd` -- `WitnessSeed.lean:41`
- `some_past_all_past_neg_absurd` -- `WitnessSeed.lean:53`
- `forward_temporal_witness_seed_consistent` -- `WitnessSeed.lean:170`
- `past_temporal_witness_seed_consistent` -- `WitnessSeed.lean:183`
- `g_content_sub` -- `PointInsertion.lean:755`
- `h_content_sub_imp_g_content_sub'` -- `PointInsertion.lean:1145`
- `g_content_sub_imp_h_content_sub'` -- `PointInsertion.lean:1166`
- `demorgan_disj_neg_forward` -- `PointInsertion.lean:1261` (private)

**MISSING** (need creation):
- `demorgan_disj_neg_backward` -- Used 8 times in bimodal CounterexampleElimination. Type: `(A.neg.and B.neg).imp (A.or B).neg`. Must be added to `PropositionalHelpers.lean` or at the top of `CounterexampleElimination.lean`.
- `identity` (trivial: `φ.imp φ`) -- Referenced via `Combinators.identity`; can use `DerivationTree.axiom [] _ (.imp_s φ φ) trivial` pattern or define separately.
- `g_propagation_witness` -- Used in bimodal `eliminate_g_prop_counterexample` but this function is likely NOT needed in temporal (it handles G-propagation failures specific to the bimodal framework). Verify during implementation.
- `set_lindenbaum_fc` -- The temporal equivalent is `temporal_lindenbaum` in `MCS.lean:59`. Signature differs slightly (no `fc` parameter).

### 2.5 Sorry Stubs in Bimodal Source

**Zero sorry stubs** in both files:
```
grep -n "sorry" CounterexampleElimination.lean  -> (no output)
grep -n "sorry" ChronicleConstruction.lean      -> (no output)
```

The open guard semantics sorrys mentioned in the task description exist in `RRelation.lean` and `PointInsertion.lean` upstream, NOT in these two files.

---

## 3. Per-File Transfer Analysis

### 3.1 CounterexampleElimination.lean (3529 lines)

**Structure** (6 sections):
1. **Helper lemmas** (lines 1-350): `exists_rat_gt_finset`, `exists_rat_lt_finset`, `exists_rat_between_not_in_finset`, `BurgessR3Maximal_g_content_sub`, `burgessR3Maximal_from_h_content_sub`, `c2'_preserved_on_old_adjacent`
2. **Simple elimination** (lines 350-500): `eliminate_C5_counterexample`, `eliminate_C5'_counterexample`, `eliminate_g_prop_counterexample`, `eliminate_h_prop_counterexample`
3. **Type definitions** (lines 500-700): `PotentialCounterexampleKind`, `PotentialCounterexample`, `EliminationResult`, `C5ForwardWalkResult`
4. **C5 forward walk** (lines 700-1250): `c5_forward_walk` (recursive, termination by domain filter card)
5. **C5 backward walk** (lines 1250-1800): `c5_backward_walk` (mirror)
6. **Main function** (lines 1850-3529): `eliminate_potential_counterexample` (4 cases: c5_forward, c5_backward, c4_forward, c4_backward)

**What transfers directly** (~95%):
- All rational arithmetic helpers (section 1)
- All BurgessR3Maximal lemmas (section 1) -- temporal `BurgessR3Maximal` has identical type
- C5/C5' counterexample structures (section 2)
- PotentialCounterexampleKind (4 cases identical -- NO modal cases)
- PotentialCounterexample structure
- EliminationResult structure (remove `fc` from type params)
- C5ForwardWalkResult / C5BackwardWalkResult (remove `fc`)
- `c5_forward_walk` / `c5_backward_walk` recursive walks
- `eliminate_potential_counterexample` main function

**What needs mechanical change**:
1. **Import paths**: `Cslib.Logics.Bimodal.X` -> `Cslib.Logics.Temporal.X`
2. **Namespace**: `Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle` -> `Cslib.Logic.Temporal.Metalogic.Chronicle`
3. **FrameClass removal**: Remove `fc : FrameClass` parameter from ALL signatures. Change `SetMaximalConsistent fc` to `Temporal.SetMaximalConsistent`. Change `DerivationTree fc` to `DerivationTree FrameClass.Base`.
4. **`liftBase fc` removal**: Replace `liftBase fc (...)` with just `(...)` since temporal derivations are already at `FrameClass.Base`.
5. **Bimodal theorem references**: Replace `Cslib.Logic.Bimodal.Theorems.Combinators.identity` with temporal equivalent. Replace `Cslib.Logic.Bimodal.Theorems.Propositional.demorgan_disj_neg_backward` with a locally defined version. Replace `Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived` with temporal equivalent.
6. **`g_propagation_witness`**: The bimodal code uses this for `eliminate_g_prop_counterexample`. In the temporal version, this function may not be needed (it handles modal-specific G-propagation). If the omega chain only processes C4/C5 defects (not G-propagation defects), this helper can be omitted.

**Estimated temporal size**: 2200-2800 lines (slightly smaller due to no FrameClass threading).

### 3.2 ChronicleConstruction.lean (1531 lines)

**Structure** (9 sections):
1. **Singleton chronicle** (lines 75-155): `singleton_chronicle`, `singleton_c0`, `singleton_invariant`, `singleton_c4`, `singleton_c4'`
2. **Countability** (lines 178-205): Countable/Infinite/Denumerable instances for PotentialCounterexample
3. **Omega chain** (lines 205-315): `counterexample_enum`, `omega_chain`, `omega_chain_val`, domain/f/g monotonicity
4. **Witness lifting** (lines 400-555): `omega_chain_c5_witness`, `omega_chain_c5'_witness`, `omega_chain_c4_witness`, `omega_chain_c4'_witness`
5. **Limit chronicle** (lines 556-630): `limit_dom`, `limit_f`, `limit_f_eq`, `limit_c0`, `limit_f_zero`
6. **C5 satisfaction** (lines 640-745): `limit_satisfies_c5_weak`, `limit_satisfies_c5'_weak`, `limit_F_resolution`, `limit_P_resolution`
7. **C4 satisfaction** (lines 745-830): `limit_satisfies_c4`, `limit_satisfies_c4'`
8. **Limit g + C3** (lines 830-930): `limit_g`, `limit_c3`, `limit_c3_interval_subset_*`
9. **Forward G / Backward H** (lines 930-1050): `limit_forward_G`, `limit_backward_H`
10. **g/h duality** (lines 930-1025): `g_content_sub_imp_h_content_sub`, `h_content_sub_imp_g_content_sub`
11. **Strong C5** (lines 1200-1530): `adj_g_mem_limit_f`, `exists_containing_adjacent`, `limit_satisfies_c5_strong`, `limit_satisfies_c5'_strong`
12. **Chronicle model exists** (line 1182): `chronicle_model_exists`

**What transfers directly** (~95%):
- All singleton definitions and vacuous proofs
- PotentialCounterexample Countable/Infinite/Denumerable instances
- Omega chain definition and monotonicity proofs
- All witness lifting theorems
- Limit domain/function definitions
- All limit satisfaction theorems (C4, C5 weak and strong)
- Limit g function and C3
- Forward G / Backward H
- g/h duality theorems
- Adjacent pair g-value propagation

**What needs mechanical change**:
1. Import paths
2. Namespace
3. FrameClass removal throughout (57 references)
4. `liftBase fc` removal
5. Bimodal theorem references (temporal equivalents exist, see Section 2.4)

**Note on g/h duality**: The bimodal `ChronicleConstruction.lean` contains `g_content_sub_imp_h_content_sub` and `h_content_sub_imp_g_content_sub` (lines 930-1025). The temporal `PointInsertion.lean` already has these at lines 1145 and 1166 (`h_content_sub_imp_g_content_sub'` and `g_content_sub_imp_h_content_sub'`). The duplicates in ChronicleConstruction can be replaced with references to the existing PointInsertion versions.

**Estimated temporal size**: 1200-1500 lines.

---

## 4. Key Simplifications vs Bimodal

### 4.1 No FrameClass Parameter

Every function in both bimodal files takes `fc : FrameClass` as an explicit parameter. In temporal, this is simply removed. `SetMaximalConsistent fc M` becomes `Temporal.SetMaximalConsistent M`. `DerivationTree fc Γ φ` becomes `DerivationTree FrameClass.Base Γ φ`.

### 4.2 No `liftBase` Calls

The bimodal code uses `liftBase fc (...)` to lift base-level derivations to arbitrary frame classes. In temporal, all derivations are already at `FrameClass.Base`, so `liftBase` is unnecessary.

### 4.3 No Modal Defect Types

The bimodal `PotentialCounterexampleKind` has 4 cases. The temporal version is identical (4 cases: c4_forward, c4_backward, c5_forward, c5_backward). The bimodal originally had modal defect types but those were already removed by the time the bimodal code was finalized.

### 4.4 No `g_propagation_witness`

The bimodal `eliminate_g_prop_counterexample` and `eliminate_h_prop_counterexample` handle G/H-propagation failures. These are used in the recursive walk but NOT in the omega chain enumeration (which only enumerates C4/C5 defects). The temporal version may still need these for the recursive walk. Verify during implementation whether `c5_forward_walk` calls `eliminate_g_prop_counterexample` -- it does NOT. It calls splitting lemmas (2.6/2.7/2.8) directly. So `eliminate_g_prop_counterexample` can be omitted from the temporal port.

### 4.5 No `CanonicalModel` Import

The bimodal imports `CanonicalModel` for various helpers. Most temporal equivalents exist in `PointInsertion.lean`, `PropositionalHelpers.lean`, `WitnessSeed.lean`, and `MCS.lean`.

---

## 5. Missing Infrastructure (Must Create)

### 5.1 Chronicle Structure and Conditions

**Priority**: Must create BEFORE CounterexampleElimination.

**Location**: Extend `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean`

**Content** (~80 lines):
```lean
-- Adjacent definition (identical to bimodal)
def Adjacent (dom : Finset Rat) (x y : Rat) : Prop :=
  x ∈ dom ∧ y ∈ dom ∧ x < y ∧ ∀ z ∈ dom, ¬(x < z ∧ z < y)

-- Chronicle structure (identical to bimodal)
structure Chronicle (Atom : Type*) where
  f : Rat → Set (Formula Atom)
  g : Rat → Rat → Set (Formula Atom)
  dom : Finset Rat

-- Chronicle conditions (no FrameClass parameter)
def Chronicle.c0 (chi : Chronicle Atom) : Prop :=
  ∀ x ∈ chi.dom, Temporal.SetMaximalConsistent (chi.f x)

def Chronicle.c2' (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, Adjacent chi.dom x y →
    BurgessR3Maximal (chi.f x) (chi.g x y) (chi.f y)

def Chronicle.c4 (chi : Chronicle Atom) : Prop := ...
def Chronicle.c4' (chi : Chronicle Atom) : Prop := ...
```

### 5.2 `demorgan_disj_neg_backward`

**Priority**: Must create BEFORE CounterexampleElimination.

**Type**: `(A.neg.and B.neg).imp (A.or B).neg`

**Location**: `PropositionalHelpers.lean` or top of `CounterexampleElimination.lean`

**Size**: ~30 lines. The bimodal version at `Connectives.lean:249` is a straightforward propositional derivation.

### 5.3 `identity` combinator

**Priority**: Low -- can be inlined or defined as a 2-line helper.

**Type**: `φ.imp φ`

---

## 6. Literature Proof Structure

**Source**: Burgess 1982, Section 2, Lemmas 2.9-2.10 and Theorem 2.8
**Strategy**: Omega-step inductive construction with directed limit

### Step Map

1. **Singleton chronicle**: Start with dom = {0}, f(0) = A (given MCS)
2. **Enumerate defects**: Use Denumerable on PotentialCounterexample to assign each defect a natural number
3. **Cantor unpairing**: Process counterexample_enum((unpair n).2) at step n+1 to ensure every defect is processed infinitely often
4. **C5 elimination (Lemma 2.10)**: For Until defects, insert witness beyond or between existing points using recursive walk
5. **C5' elimination (Lemma 2.10')**: Mirror for Since
6. **C4 elimination**: For negated-Until defects, insert counterexample point between x and y
7. **C4' elimination**: Mirror for Since
8. **Take union**: limit_dom = union of all dom(n), limit_f(x) = f_n(x) for first n with x in dom(n)
9. **Limit g via C3**: limit_g(x,z) = {phi | forall y in limit_dom, x < y < z -> phi in limit_f(y)}
10. **Verify C0-C5**: Each condition transfers from finite stages to limit

### Dependencies
- Steps 4-7 depend on Step 1-3 (enumeration structure)
- Step 8 depends on Steps 4-7 (monotone chain)
- Step 9 depends on Step 8 (dense limit domain)
- Step 10 depends on Steps 8-9

### Formalization Already Complete in Bimodal
All steps above are fully formalized (zero sorry) in the bimodal code. The temporal port is mechanical.

---

## 7. Implementation Plan Recommendation

### Phase 1: Chronicle Infrastructure (~80 lines)
Extend `ChronicleTypes.lean` with Adjacent, Chronicle, chronicle conditions.

### Phase 2: Propositional Helper (~30 lines)
Add `demorgan_disj_neg_backward` to `PropositionalHelpers.lean` or as a private definition.

### Phase 3: CounterexampleElimination (~2200-2800 lines)
Port from bimodal. All proof content transfers with mechanical namespace/FrameClass changes.

### Phase 4: ChronicleConstruction (~1200-1500 lines)
Port from bimodal. Same mechanical changes. Can reuse temporal `h_content_sub_imp_g_content_sub'` and `g_content_sub_imp_h_content_sub'` instead of re-proving.

### Phase 5: Build verification
`lake build Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleConstruction`

---

## 8. Risks

### Risk 1: Temporal derivation API differences (LOW)
The bimodal code uses `DerivationTree.axiom [] _ (Axiom.X ...) trivial` extensively. The temporal axiom names may differ slightly. The temporal axiom system uses the same names (`.connect_past`, `.F_until_equiv`, `.since_P`, `.P_since_equiv`, `.serial_future`, `.serial_past`, etc.) as confirmed by grep of `PointInsertion.lean`.

### Risk 2: `set_lindenbaum` API (LOW)
The bimodal uses `set_lindenbaum_fc` which takes an `fc` parameter. The temporal equivalent is `temporal_lindenbaum` at `MCS.lean:59`. The signature difference is minor.

### Risk 3: `private` visibility of helpers (MEDIUM)
Several helpers in temporal `PointInsertion.lean` are marked `private` (e.g., `demorgan_disj_neg_forward`). If `CounterexampleElimination.lean` needs them, they must either be made non-private or re-derived locally. The bimodal version has the same issue -- the helpers are in separate files. Temporal may need to redefine some locally.

### Risk 4: `maxHeartbeats` (MEDIUM)
The temporal `PointInsertion.lean` already uses `maxHeartbeats 3200000`. The recursive walk functions (`c5_forward_walk`, `c5_backward_walk`) and the main `eliminate_potential_counterexample` are large tactic proofs that may need elevated heartbeat limits. The bimodal versions compile without special limits, but the temporal may differ.

---

## 9. Blockers

**None identified**. All prerequisites exist. The task can proceed directly to planning.

---

## 10. Relevant Codebase Paths

### Source Files (bimodal -- adapt from these)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` (3529 lines)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` (1531 lines)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` (Chronicle struct, Adjacent def)

### Prerequisite Files (temporal -- must exist)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` (216 lines, needs extension)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` (2888 lines)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` (254 lines)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` (~714 lines)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` (174 lines)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean` (253 lines)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/Formula.lean` (Denumerable instance at line 208)

### Target Files (create)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` (new, ~2200-2800 lines)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` (new, ~1200-1500 lines)
