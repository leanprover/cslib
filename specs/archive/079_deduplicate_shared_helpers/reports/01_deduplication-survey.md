# Systematic Deduplication Survey Across Logics/

**Task**: 079 - Systematic deduplication audit and consolidation across Logics/
**Session**: sess_1781108968_4593b9
**Date**: 2026-06-10

## 1. Methodology

### Scanning Approach

The survey covered 187 Lean files under `Cslib/Logics/` and 15 files under `Cslib/Foundations/Logic/` (total ~74,280 lines). Four complementary methods were used:

1. **Name-based scan**: Extracted all `def`, `theorem`, `lemma`, `instance`, `abbrev` declarations with file locations; identified names appearing in 2+ files.
2. **Structure-based comparison**: Compared parallel directory trees across logic domains (Propositional, Modal, Temporal, Bimodal) to identify mirrored file structures.
3. **Content-based diffing**: For files with matching names across domains, diffed their contents to assess similarity percentage and identify the nature of differences.
4. **Import-based analysis**: Checked what `Foundations/Logic/` already provides and whether logic domains use it or reimplement it.

### Key Metrics

- **Total names appearing in 2+ files**: ~120 unique identifiers
- **Names shared between Temporal and Bimodal**: 475 (across parallel proof constructions)
- **Names shared between Propositional and Modal**: 16 (DerivationTree/DeductionTheorem infrastructure)
- **Names shared between HML and Modal**: 12 (Kripke semantics boilerplate)

---

## 2. Findings by Category

### (A) Exact Duplicates: removeAll + List Helpers

**Files involved** (4 copies):
| File | Lines | Domain |
|------|-------|--------|
| `Propositional/Metalogic/DeductionTheorem.lean` | 236 | Propositional |
| `Modal/Metalogic/DeductionTheorem.lean` | 257 | Modal |
| `Temporal/Metalogic/DeductionTheorem.lean` | 239 | Temporal |
| `Bimodal/Metalogic/Core/DeductionTheorem.lean` | 327 | Bimodal |

**Duplicated items** (identical logic, different formula/axiom types):
- `removeAll` -- identical `List.filter` definition in all 4 files
- `removeAll_subset_of_subset` / `removeAll_sub_of_sub` -- same proof, minor naming variation in Temporal
- `mem_removeAll_of_mem_of_ne` -- identical in all 4
- `removeAll_subset_removeAll` / `removeAll_sub_removeAll` -- identical logic

**Total duplicated lines**: ~100 lines (25 lines x 4 copies; 3 copies are redundant)

**Recommended action**: Extract `removeAll` and its 3 helper lemmas to a shared file in `Foundations/Logic/` or a utility module. Each DeductionTheorem file can import and use it.

**Estimated complexity**: Low. Pure list lemmas with no type dependencies on Formula types.

---

### (B) Structural Duplicates: DeductionTheorem Proof

**Files involved**: Same 4 files as (A).

The deduction theorem proof follows an identical structure across all 4 logics:
1. `deduction_axiom` -- use implyK to weaken axiom under implication
2. `deduction_imp_self` -- identity via implyS + implyK
3. `deduction_assumption_other` -- use implyK with assumption
4. `deduction_mp` -- modus ponens under implication via implyS
5. `deduction_with_mem` -- key recursive helper for weakening case
6. `deduction_theorem` -- main theorem by WF recursion on height
7. `*_has_deduction_theorem` -- wrapper for generic MCS framework

**Differences**: The only structural difference is the number of DerivationTree constructors matched:
- Propositional: 4 constructors (ax, assumption, modus_ponens, weakening)
- Modal: 5 constructors (+ necessitation, vacuously impossible)
- Temporal: 6 constructors (+ temporal_necessitation, temporal_duality)
- Bimodal: 7 constructors (+ necessitation, temporal_necessitation, temporal_duality)

The extra constructors are all discharged by `simp at hA` (context is non-empty but these constructors require empty context).

**Total duplicated lines**: ~800 lines (4 x ~200 lines; 3 copies redundant)

**Recommended action**: This is the highest-value deduplication target. Two approaches:
- **Option 1 (Generic proof)**: Parameterize the proof over a `DerivationTree`-like inductive that exposes a common interface (ax, assumption, mp, weakening + list of "empty-context-only" constructors). The generic proof handles the 4 shared cases; each logic provides the vacuous-case dispatch.
- **Option 2 (Typeclass approach)**: Extend the existing `DerivationSystem` / `HasDeductionTheorem` framework in Foundations to carry the proof generically, where each logic only provides the instance.

**Feasibility note**: The Foundations framework already has `DerivationSystem` and `HasDeductionTheorem` as a property. The issue is that the *proof* of the deduction theorem is currently done directly on each logic's concrete `DerivationTree` type. Generalizing requires a shared `height` function and pattern-matching interface, which may require a typeclass like `HasDerivationTree` with `height`, `mp_height_gt_left`, etc.

**Estimated complexity**: Medium-High. Requires designing a shared interface for DerivationTree constructors.

---

### (C) Structural Duplicates: DerivationTree Height Infrastructure

**Files involved** (4-5 copies):
| File | Lines | Domain |
|------|-------|--------|
| `Propositional/ProofSystem/Derivation.lean` | 147 | Propositional |
| `Modal/Metalogic/DerivationTree.lean` | 187 | Modal |
| `Temporal/Metalogic/DerivationTree.lean` | 134 | Temporal |
| `Bimodal/Metalogic/Core/DerivationTree.lean` | 88 | Bimodal |
| `Bimodal/ProofSystem/Derivation.lean` | 168 | Bimodal |

**Duplicated items** (4 copies each):
- `height` -- recursive height function on DerivationTree
- `height_modus_ponens_left` / `mp_height_gt_left` -- height strictly decreases in left MP subderivation
- `height_modus_ponens_right` / `mp_height_gt_right` -- same for right
- `height_weakening` / `subderiv_height_lt` -- height strictly decreases in weakening subderivation
- `mp_deriv` -- modus ponens convenience wrapper
- `weakening_deriv` -- weakening convenience wrapper
- `assumption_deriv` -- assumption convenience wrapper
- `Derivable` / `Deriv` -- abbreviations for `Nonempty DerivationTree`

**Total duplicated lines**: ~400 lines (each file ~60-80 lines of height infrastructure, 3-4 copies redundant)

**Recommended action**: These are intrinsically tied to each logic's DerivationTree inductive type. Deduplication requires either:
- A shared generic `DerivationTree` parameterized over the set of extra constructors, or
- A typeclass/interface exposing height, mp_height, etc. that each DerivationTree implements

This is coupled with finding (B) above -- solving one likely solves both.

**Estimated complexity**: Medium-High (same as B).

---

### (D) Structural Duplicates: Temporal/Bimodal Chronicle Parallel Files

This is the **largest duplication cluster by line count**. The Temporal Chronicle construction and the Bimodal BXCanonical Chronicle construction follow the same proof strategy with the Bimodal version adding a `FrameClass` parameter.

**Parallel file pairs** (7 pairs):

| Temporal File | Lines | Bimodal File | Lines | Shared Names |
|---------------|-------|--------------|-------|-------------|
| `Chronicle/ChronicleConstruction.lean` | 1,433 | `BXCanonical/Chronicle/ChronicleConstruction.lean` | 1,529 | 51 |
| `Chronicle/ChronicleTypes.lean` | 323 | `BXCanonical/Chronicle/ChronicleTypes.lean` | 385 | 43 |
| `Chronicle/PointInsertion.lean` | 2,717 | `BXCanonical/Chronicle/PointInsertion.lean` | 3,553 | 61 |
| `Chronicle/RRelation.lean` | 710 | `BXCanonical/Chronicle/RRelation.lean` | 1,692 | 36 |
| `Chronicle/CounterexampleElimination.lean` | 3,234 | `BXCanonical/Chronicle/CounterexampleElimination.lean` | 3,526 | 8 |
| `Chronicle/OrderedSeedConsistency.lean` | 135 | `BXCanonical/OrderedSeedConsistency.lean` | 150 | 6 |
| `Chronicle/CanonicalChain.lean` | 76 | `BXCanonical/CanonicalChain.lean` | 92 | 6 |

**Additional parallel files**:

| Temporal File | Lines | Bimodal File | Lines | Shared Names |
|---------------|-------|--------------|-------|-------------|
| `TemporalContent.lean` | 220 | `Bundle/TemporalContent.lean` | 167 | 14 |
| `WitnessSeed.lean` | 252 | `Bundle/WitnessSeed.lean` | 605 | 9 |
| `Chronicle/Frame.lean` | 248 | `BXCanonical/Frame.lean` | 463 | 2 |
| `Chronicle/TruthLemma.lean` | 232 | `BXCanonical/TruthLemma.lean` | 222 | - |
| `Chronicle/ChronicleToCountermodel.lean` | 138 | `BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 227 | - |

**Total Temporal lines in parallel structure**: ~9,718
**Total Bimodal lines in parallel structure**: ~12,611
**Estimated shared proof content**: ~60-70% (the Bimodal versions add FrameClass parameterization and extra modal cases)

**Nature of differences**:
- Bimodal versions parameterize over `FrameClass` (Temporal fixes it to `FrameClass.Base`)
- Bimodal versions handle additional modal operators (box, diamond)
- Bimodal has extra `necessitation` constructor cases in derivation proofs
- Bimodal uses `SetMaximalConsistent fc` vs Temporal's `SetMaximalConsistent`
- Core proof strategy (chronicle construction, point insertion, counterexample elimination) is identical

**Recommended action**: This is a genuine structural parallel where Bimodal extends Temporal. Two consolidation strategies:

- **Option 1 (Parameterize Temporal)**: Add an optional `FrameClass` parameter to the Temporal versions. Bimodal imports Temporal and specializes. Pros: maximal code sharing. Cons: adds complexity to the simpler Temporal versions.
- **Option 2 (Factor shared core)**: Extract the purely temporal parts of the proof (chronicle types, point insertion seed logic, counterexample elimination core) into a shared module that both import. Each logic adds its specific cases.
- **Option 3 (Leave as intentional parallel)**: Accept that these are genuinely different proof constructions for different logics, and that the shared structure reflects the mathematical relationship (Bimodal extends Temporal). Focus deduplication efforts on the smaller helper duplicates.

**Estimated complexity**: Very High for Options 1-2 (touching 9,000+ lines of complex proof code). The risk-reward ratio may not justify full consolidation.

---

### (E) Structural Duplicates: Propositional Theorem Re-proofs

**Files involved**:
| File | Lines | Status |
|------|-------|--------|
| `Foundations/Logic/Theorems/Combinators.lean` | 333 | **Generic typeclass version (canonical)** |
| `Foundations/Logic/Theorems/Propositional/Core.lean` | ~300 | **Generic typeclass version (canonical)** |
| `Foundations/Logic/Theorems/Propositional/Connectives.lean` | 546 | **Generic typeclass version (canonical)** |
| `Bimodal/Theorems/Combinators.lean` | 195 | **Delegates to Foundations via wrap/unwrap** |
| `Bimodal/Theorems/Propositional/Core.lean` | 287 | **Partially delegates, partially re-proves** |
| `Bimodal/Theorems/Propositional/Connectives.lean` | 140 | **Fully delegates to Foundations** |
| `Bimodal/Theorems/Perpetuity/Helpers.lean` | 134 | **Fully delegates to Foundations** |
| `Temporal/Metalogic/PropositionalHelpers.lean` | 232 | **RE-PROVES EVERYTHING FROM SCRATCH** |

**Key finding**: The Bimodal domain has mostly completed the migration to the Foundations typeclass-based theorems (Combinators and Perpetuity/Helpers delegate via `wrap`/`unwrap`). However, **Temporal/PropositionalHelpers re-proves all propositional theorems from scratch** using direct DerivationTree construction, ignoring the generic versions in Foundations entirely.

**Duplicated theorems in Temporal/PropositionalHelpers** (all could delegate to Foundations):
- `double_negation` (78 lines of direct proof vs 1-line delegation in Bimodal)
- `efq_axiom` (trivial axiom wrapper)
- `imp_trans` (re-derived from scratch)
- `pairing` (re-derived from scratch)
- `lce_imp` / `rce_imp` (re-derived from scratch)
- `dni` (re-derived from scratch)
- `identity` (re-derived from scratch)
- `demorgan_disj_neg_backward` (re-derived from scratch)

**Total wasted lines**: ~200 lines (most of PropositionalHelpers.lean)

**Recommended action**: **HIGH PRIORITY**. Replace `Temporal/Metalogic/PropositionalHelpers.lean` with a thin delegation layer (like Bimodal/Perpetuity/Helpers.lean), wrapping the generic Foundations theorems. This requires Temporal to have `InferenceSystem` / `PropositionalHilbert` instances (which the Temporal `Instances.lean` already provides).

**Estimated complexity**: Low-Medium. The pattern is already established in Bimodal/Perpetuity/Helpers.lean.

---

### (F) Structural Duplicates: Bimodal TemporalDerived vs Foundations TemporalDerived

**Files involved**:
| File | Lines | Status |
|------|-------|--------|
| `Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` | 293 | **Generic typeclass version (canonical)** |
| `Bimodal/Theorems/TemporalDerived.lean` | 380 | **Partially duplicates, partially extends** |

**Duplicated theorems** (12 names shared):
- `until_mono_guard`, `since_mono_guard` -- direct axiom wrappers (identical)
- `until_mono_event`, `since_mono_event` -- direct axiom wrappers (identical)
- `until_implies_someFuture`, `since_implies_somePast` -- direct axiom wrappers
- `F_mono`, `P_mono` -- monotonicity derived from BX3
- `G_distribution`, `H_distribution` -- K-distribution derived theorems
- `connect_future_thm`, `connect_past_thm` -- connectedness axiom wrappers

**Nature**: Bimodal/TemporalDerived re-proves these using concrete DerivationTree, while Foundations has the generic versions. The Bimodal file also contains additional Bimodal-specific theorems (`temp_4_derived`, `dne_lift_F`, etc.) that go beyond the generic framework.

**Recommended action**: Medium priority. Have Bimodal/TemporalDerived delegate the common temporal theorems to Foundations (like Connectives.lean already does) and keep only Bimodal-specific extensions.

**Estimated complexity**: Medium. Requires matching Bimodal's DerivationTree API with the generic Nonempty-based API.

---

### (G) Structural Duplicates: MCS Properties (Bimodal vs Foundations)

**Files involved**:
| File | Lines | Status |
|------|-------|--------|
| `Foundations/Logic/Metalogic/Consistency.lean` | 277 | **Generic DerivationSystem framework** |
| `Bimodal/Metalogic/Core/MCSProperties.lean` | 487 | **Re-implements + extends** |
| `Modal/Metalogic/MCS.lean` | 324 | **Properly delegates to Foundations** |
| `Propositional/Metalogic/MCS.lean` | 129 | **Properly delegates to Foundations** |
| `Temporal/Metalogic/MCS.lean` | 482 | **Properly delegates to Foundations** |

**Key finding**: Modal, Propositional, and Temporal MCS files properly instantiate the generic framework from `Foundations/Logic/Metalogic/Consistency.lean`. However, **Bimodal/MCSProperties re-implements** the following from scratch:
- `SetConsistent` (redefined instead of using the generic version)
- `SetMaximalConsistent` (redefined)
- `SetMaximalConsistent.closed_under_derivation` (re-proved)
- `SetMaximalConsistent.implication_property` (re-proved)
- `SetMaximalConsistent.negation_complete` (re-proved)
- `set_consistent_not_both` (re-proved)

The Bimodal file also adds genuinely new content: `temp_4_derived`, `temp_4_past`, `allFuture_allFuture`, `allPast_allPast`, `neg_excludes` -- these are Bimodal-specific and not duplicates.

**Total duplicated lines**: ~200 lines of re-proved generic MCS theory

**Recommended action**: Refactor Bimodal/MCSProperties to import and use the generic `DerivationSystem` framework from Foundations, keeping only the Bimodal-specific extensions.

**Estimated complexity**: Medium. Requires creating a `bimodalDerivationSystem` that maps to the generic framework (similar to what Modal/Propositional/Temporal already have).

---

### (H) Structural Duplicates: HML vs Modal

**Files involved**:
| File | Lines | Shared Names |
|------|-------|-------------|
| `HML/Basic.lean` | 266 | 12 |
| `Modal/Basic.lean` | 394 | 12 |
| `Modal/Denotation.lean` | 85 | 3 |

**Duplicated items**:
- `Proposition.neg` -- negation defined identically in both
- `theory` / `TheoryEq` / `satisfies_theory` / `theoryEq_satisfies` -- theory/equivalence definitions
- `satisfies_mem_denotation` / `neg_satisfies` / `neg_denotation` -- denotation lemmas
- `Satisfies.Bundled` -- bundled satisfaction relation

**Nature**: HML (Hennessy-Milner Logic) is a strict subset of Modal logic. Both define Kripke semantics independently. HML uses `Finset` for modal operators (finite branching) while Modal uses `Set`, which is a genuine structural difference.

**Recommended action**: Low priority. While there is conceptual overlap, HML's `Finset`-based approach and Modal's `Set`-based approach are fundamentally different type-level choices. Deduplication would require a shared abstract interface for accessibility relations, which may be over-engineering for 2 logics with only 12 shared names.

**Estimated complexity**: Medium (interface design for Kripke semantics abstraction).

---

### (I) Near-Duplicates: wrap/unwrap Bridge Pattern

**Files with `unwrap` definition** (3 within Bimodal alone):
- `Bimodal/Theorems/Combinators.lean:73`
- `Bimodal/Theorems/Perpetuity/Helpers.lean:60`
- `Bimodal/Theorems/Propositional/Core.lean:44`

Also `wrap'`/`unwrap'` in `Bimodal/Theorems/Propositional/Connectives.lean`.

**Nature**: Each file independently defines `unwrap` as `h.some` to extract a `DerivationTree` from `Nonempty`. This is a 2-line definition duplicated 3-4 times within Bimodal alone.

**Recommended action**: Extract a single `unwrap` definition to a shared utilities file or the `Derivation.lean` file that all theorem modules import.

**Estimated complexity**: Very Low.

---

### (J) Near-Duplicates: Syntax Parallel Files

**Temporal/Bimodal Syntax parallels**:
| Component | Temporal Lines | Bimodal Lines | Shared Names |
|-----------|---------------|---------------|-------------|
| `Formula.lean` | 549 | 210 | 17 |
| `Context.lean` | 131 | 140 | 16 |
| `Subformulas.lean` | 218 | 240 | 20 |

**Nature**: Bimodal formulas extend Temporal formulas with `box` and `diamond` constructors. The shared definitions (`swapTemporal`, `allFuture`, `somePast`, `singleton`, etc.) are structurally identical but operate on different `Formula` types.

**Recommended action**: Low priority. The parallel structure reflects the mathematical relationship (Bimodal formulas = Temporal formulas + modal operators). Deduplication would require parameterizing Formula over an "operator set," which is a significant design change with unclear benefits.

**Estimated complexity**: High (redesigning the Formula inductive type).

---

### (K) Near-Duplicates: Semantics Validity

**Files involved**:
| File | Lines | Shared Names |
|------|-------|-------------|
| `Temporal/Semantics/Validity.lean` | 198 | 6 |
| `Bimodal/Semantics/Validity.lean` | 275 | 6 |

**Shared definitions**: `valid_implies_valid_discrete`, `valid_implies_valid_dense`, `valid_iff_empty_consequence`, `valid_consequence`

**Nature**: Both define validity for their respective frame types. The Bimodal version adds TaskFrame-specific constructions.

**Recommended action**: Low priority. Frame-type differences make generic abstraction complex.

**Estimated complexity**: Medium-High.

---

### (L) Near-Duplicates: GeneralizedNecessitation

**Files involved**:
| File | Lines |
|------|-------|
| `Temporal/Metalogic/GeneralizedNecessitation.lean` | 168 |
| `Bimodal/Theorems/GeneralizedNecessitation.lean` | 130 |

**Shared concepts**: `reverse_deduction`, `contrapose_imp`, `contraposition`, `generalized_temporal_k`, `generalized_past_k`, `temp_k_dist_derived`, `past_k_dist`

**Nature**: Both derive generalized K-distribution for temporal operators. The Temporal version re-proves `contrapose_imp` and `contraposition` (which exist in Foundations), while the Bimodal version delegates more. Both derive temporal necessitation patterns independently.

**Recommended action**: Medium priority. The Temporal version should delegate propositional lemmas to Foundations. The temporal K-distribution pattern could potentially be moved to Foundations/Logic/Theorems/Temporal/ if generalized.

**Estimated complexity**: Medium.

---

## 3. Existing Abstractions in Foundations/Logic/

`Foundations/Logic/` already provides significant shared infrastructure that some logics use and others bypass:

| Abstraction | File | Used By | Bypassed By |
|-------------|------|---------|-------------|
| `InferenceSystem` typeclass | `InferenceSystem.lean` | All logics | - |
| `PropositionalHilbert` typeclass bundle | `ProofSystem.lean` | Bimodal (via instances) | Temporal (partially) |
| `TemporalBXHilbert` typeclass bundle | `ProofSystem.lean` | Foundations/Temporal | Bimodal (partially) |
| `DerivationSystem` structure | `Consistency.lean` | Modal, Prop, Temporal | **Bimodal** |
| `HasDeductionTheorem` property | `Consistency.lean` | Modal, Prop, Temporal | **Bimodal** |
| `SetMaximalConsistent` + Lindenbaum | `Consistency.lean` | Modal, Prop, Temporal | **Bimodal** |
| `imp_trans`, `identity`, `pairing`, etc. | `Combinators.lean` | Bimodal (delegated) | **Temporal** |
| `double_negation`, `efq_axiom`, etc. | `Propositional/Core.lean` | Bimodal (delegated) | **Temporal** |
| `contrapose_imp`, `contraposition`, etc. | `Propositional/Connectives.lean` | Bimodal (delegated) | **Temporal** |
| `G_distribution`, `H_distribution`, etc. | `Temporal/TemporalDerived.lean` | (available) | **Bimodal** |

**Pattern**: Bimodal has largely migrated to using Foundations for propositional theorems but not for MCS theory or temporal derived theorems. Temporal has migrated for MCS theory but not for propositional theorems.

---

## 4. Priority Ranking

Ordered by **impact** (duplicate_count x lines_saved) x **feasibility**:

| Priority | Category | Est. Lines Saved | Feasibility | Description |
|----------|----------|-----------------|-------------|-------------|
| **P1** | (E) Temporal PropositionalHelpers | ~200 | High | Replace re-proved theorems with Foundations delegations |
| **P2** | (I) wrap/unwrap duplication | ~15 | Very High | Extract shared bridge utilities within Bimodal |
| **P3** | (A) removeAll list helpers | ~75 | High | Extract to shared module |
| **P4** | (G) Bimodal MCSProperties | ~200 | Medium | Delegate to Foundations DerivationSystem framework |
| **P5** | (F) Bimodal TemporalDerived | ~150 | Medium | Delegate common temporal theorems to Foundations |
| **P6** | (L) Temporal GeneralizedNecessitation | ~60 | Medium | Delegate propositional lemmas to Foundations |
| **P7** | (B+C) DeductionTheorem generalization | ~800 | Medium-High | Generic deduction theorem proof across all logics |
| **P8** | (D) Chronicle parallel files | ~5,000+ | Very Low | Temporal/Bimodal chronicle factoring |
| **P9** | (H) HML vs Modal | ~50 | Low | Abstract Kripke semantics interface |
| **P10** | (J+K) Syntax/Semantics parallels | ~100 | Low | Formula type parameterization |

### Estimated Total Lines Recoverable

- **High-feasibility items (P1-P6)**: ~700 lines
- **Medium-feasibility items (P7)**: ~800 lines
- **Low-feasibility items (P8-P10)**: ~5,150 lines (but very high risk)

### Recommended Phase Grouping

**Phase 1** (Low risk, high reward): P1 + P2 + P3 (~290 lines saved)
- Replace Temporal/PropositionalHelpers with thin delegation layer
- Consolidate wrap/unwrap within Bimodal
- Extract removeAll to shared module

**Phase 2** (Medium risk, medium reward): P4 + P5 + P6 (~410 lines saved)
- Bimodal MCSProperties delegates to Foundations
- Bimodal TemporalDerived delegates common theorems
- Temporal GeneralizedNecessitation delegates propositional lemmas

**Phase 3** (Higher risk, high reward): P7 (~800 lines saved)
- Generic deduction theorem requiring DerivationTree interface design

**Phase 4** (Research needed): P8 (~5,000 lines but very high complexity)
- Chronicle factoring -- recommend further research before attempting

---

## 5. Recommendations

### Immediate Actions (Phase 1)

1. **Create `Foundations/Logic/Helpers/ListRemoveAll.lean`** (or add to existing utility):
   - Move `removeAll`, `removeAll_subset_of_subset`, `mem_removeAll_of_mem_of_ne`, `removeAll_subset_removeAll` here
   - Update all 4 DeductionTheorem files to import

2. **Refactor `Temporal/Metalogic/PropositionalHelpers.lean`**:
   - Add `InferenceSystem`/`PropositionalHilbert` instances for Temporal if not already present
   - Replace all 11 re-proved theorems with wrap/unwrap delegations to Foundations
   - Follow the pattern established in `Bimodal/Theorems/Perpetuity/Helpers.lean`

3. **Consolidate `unwrap` within Bimodal**:
   - Keep `unwrap` in one canonical location (e.g., `Bimodal/Theorems/Combinators.lean`)
   - Have other files import it

### Medium-Term Actions (Phase 2)

4. **Bimodal MCS migration**:
   - Create `bimodalDerivationSystem` mapping to `Foundations.DerivationSystem`
   - Replace re-proved `SetConsistent`, `SetMaximalConsistent`, etc. with instantiations
   - Keep Bimodal-specific extensions (`temp_4_derived`, `allFuture_allFuture`)

5. **Bimodal TemporalDerived delegation**:
   - For shared temporal theorems, delegate to Foundations/Temporal/TemporalDerived via instances
   - Keep Bimodal-specific extensions

### Long-Term Actions (Phase 3)

6. **Generic DeductionTheorem**:
   - Design a `HasDerivationTree` typeclass exposing `height`, `mp_height_gt_left`, etc.
   - Write one generic deduction theorem proof in Foundations
   - Each logic provides the instance

### Not Recommended

7. **Chronicle factoring** (P8): The Temporal/Bimodal chronicle construction is a massive (>15,000 lines combined) proof with deep interconnections. While 60-70% of the content is structurally parallel, the differences (FrameClass parameterization, modal operators) are pervasive. The risk of breaking working proofs outweighs the benefit. If attempted, it should be a dedicated multi-week effort with thorough testing.

8. **Formula type parameterization** (P10): Changing the Formula inductive type is too invasive for the benefit.
