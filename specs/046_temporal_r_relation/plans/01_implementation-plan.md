# Implementation Plan: Task #46

- **Task**: 46 - Burgess R-Relation Implementation
- **Status**: [NOT STARTED]
- **Effort**: 14 hours
- **Dependencies**: None (existing MCS.lean and Completeness.lean are prerequisites; both already exist)
- **Research Inputs**: specs/046_temporal_r_relation/reports/02_research-report.md, specs/046_temporal_r_relation/reports/01_seed-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Port the Burgess R-relation infrastructure from the bimodal `BXCanonical/Chronicle/` module to a new temporal-only `Temporal/Metalogic/Chronicle/` directory. This requires first creating prerequisite infrastructure (Phase 0 deliverables: TemporalContent, WitnessSeed, generalized necessitation helpers) that exists in the bimodal module but not yet in the temporal module. Then port the four Chronicle files (Frame, CanonicalChain, OrderedSeedConsistency, RRelation) with mechanical adaptations: remove the `fc : FrameClass` parameter, replace bimodal MCS types with `Temporal.SetMaximalConsistent`, and adapt derivation tree construction to use `Nonempty` wrapping where needed.

### Research Integration

Key findings from the research report (02_research-report.md):
- The bimodal R-relation code is ~95% purely temporal; the only barrier is type-porting
- The temporal module lacks `generalized_temporal_k`, `past_necessitation`, and `past_k_dist` at the DerivationTree level (these are in bimodal `Theorems/GeneralizedNecessitation.lean`)
- The temporal module has `futureSet`/`pastSet` (mathematically identical to `g_content`/`h_content`) but the chronicle uses the `g_content` naming; create independent definitions
- The temporal module has `mcs_g_trans`/`mcs_h_trans` (equivalents of bimodal `all_future_all_future`) and `derive_g_contradiction`/`derive_h_contradiction` (equivalents of seed consistency proofs), but these are private in Completeness.lean
- Several helpers (`derive_dne`, `derive_h_nec`, `derive_contrapositive`) are private in MCS.lean/Completeness.lean and need to be promoted or duplicated
- The only sorry will be `t_le_refl` (same irreflexive semantics issue as bimodal `bx_le_refl`)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items consulted for this plan.

## Goals & Non-Goals

**Goals**:
- Create `TemporalContent.lean` with `g_content`, `h_content`, `f_content`, `p_content`, `u_content`, `s_content` definitions and simp lemmas
- Create `WitnessSeed.lean` with forward/past temporal witness seed consistency proofs and g_content/h_content duality theorems
- Create `Chronicle/ChronicleTypes.lean` with DCS types, r-relation definitions, r-maximality, and Burgess relation definitions (no Chronicle structure -- that is Task 48)
- Create `Chronicle/Frame.lean` with `TPoint`, `t_le`, g/h-content closure, set consistency, transitivity, forward/backward witnesses, G/H forward/backward, eventuality resolution
- Create `Chronicle/CanonicalChain.lean` with F/P-to-Until/Since conversion, absorption, delegation bridges
- Create `Chronicle/OrderedSeedConsistency.lean` with enriched seed consistency, linearity, two-defect seeds
- Create `Chronicle/RRelation.lean` with all r-relation lemmas (Lemmas 2.2-2.5), deductive closure, Zorn existence, guard algebra, Burgess R3 machinery

**Non-Goals**:
- Modifying existing files (`MCS.lean`, `Completeness.lean`, `DeductionTheorem.lean`)
- Creating the Chronicle structure, conditions C0-C5, or ValidChronicle (Task 48)
- Creating PointInsertion or CounterexampleElimination (Tasks 47-48)
- Abstracting bimodal/temporal to a shared module (Task 41)
- Resolving the `t_le_refl` sorry (known open issue from bimodal)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Missing generalized necessitation (temporal has no `generalized_temporal_k`) | H | H | Create temporal-specific `GeneralizedNecessitation.lean` in Phase 0b |
| Propositional combinator differences (bimodal uses `Theorems.Propositional.double_negation`, temporal uses private `derive_dne`) | M | H | Create temporal `PropositionalHelpers.lean` or inline private helpers per-file |
| `Nonempty` wrapping mismatch (`temporalDerivationSystem.Deriv` = `Nonempty (DerivationTree ...)`) | M | M | Use `temporal_closed_under_derivation` consistently; wrap with `Nonempty.intro` when constructing trees |
| RRelation.lean scope (800-1000 lines, largest single file) | M | M | Split Phase 6 into two sub-phases if needed; verify incrementally with `lake build` |
| Import cycle risk between new files and existing Completeness.lean | H | L | New files import MCS.lean but NOT Completeness.lean; keep private helpers duplicated rather than promoting |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 1, 2, 3 |
| 5 | 5, 6 | 4 |
| 6 | 7 | 3, 4, 5, 6 |

Phases within the same wave can execute in parallel.

---

### Phase 1: TemporalContent Definitions [COMPLETED]

**Goal**: Create `g_content`, `h_content`, and related set definitions with simp membership lemmas. These are the foundational definitions used by all subsequent Chronicle files.

**Tasks**:
- [ ] Create file `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean`
- [ ] Import `Cslib.Logics.Temporal.Metalogic.MCS`
- [ ] Define `g_content (M : Set (Formula Atom)) : Set (Formula Atom) := {phi | Formula.all_future phi ∈ M}`
- [ ] Define `h_content (M : Set (Formula Atom)) : Set (Formula Atom) := {phi | Formula.all_past phi ∈ M}`
- [ ] Define `f_content`, `p_content` (using `some_future`/`some_past`)
- [ ] Define `u_content (M : Set (Formula Atom)) : Set (Formula Atom × Formula Atom) := { p | Formula.untl p.1 p.2 ∈ M }`
- [ ] Define `s_content` (using `snce`)
- [ ] Add `@[simp]` membership lemmas: `mem_g_content_iff`, `mem_h_content_iff`, `mem_f_content_iff`, `mem_p_content_iff`, `mem_u_content_iff`, `mem_s_content_iff`
- [ ] Add duality lemmas: `f_content_iff_not_neg_in_g_content`, `p_content_iff_not_neg_in_h_content` (adapt from bimodal `TemporalContent.lean` lines 88-167)
- [ ] Register in `Cslib/Logics/Temporal/Metalogic.lean` import list
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.TemporalContent`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean` - NEW file (~120 lines)
- `Cslib/Logics/Temporal/Metalogic.lean` - Add import

**Verification**:
- File compiles with `lake build`
- All 6 content definitions and 6 simp lemmas present
- Duality lemmas prove without sorry

---

### Phase 2: Generalized Necessitation and Propositional Helpers [COMPLETED]

**Goal**: Create the temporal versions of `generalized_temporal_k`, `generalized_past_k`, `past_necessitation`, `past_k_dist`, and `temp_k_dist_derived` at the DerivationTree level. Also create propositional helpers (`double_negation`, `efq_axiom`, `lce_imp`, `rce_imp`, `pairing`, `imp_trans`, `dni`, `contraposition`) needed by later phases.

**Tasks**:
- [ ] Create file `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean`
- [ ] Import `Cslib.Logics.Temporal.Metalogic.MCS` (for `DerivationTree`, `deduction_theorem`)
- [ ] Implement `past_necessitation`: from `⊢ φ` derive `⊢ H(φ)` using temporal_duality + temporal_necessitation + swap_temporal (adapt the pattern from Completeness.lean `derive_h_nec`)
- [ ] Implement `temp_k_dist_derived`: `⊢ G(φ→ψ) → (G(φ) → G(ψ))` (adapt from bimodal `TemporalDerived.lean`)
- [ ] Implement `past_k_dist`: `⊢ H(φ→ψ) → (H(φ) → H(ψ))` (mirror using past_necessitation)
- [ ] Implement `generalized_temporal_k`: from `L ⊢ φ` derive `G(L) ⊢ G(φ)` by induction on L (adapt from bimodal lines 95-109)
- [ ] Implement `generalized_past_k`: from `L ⊢ φ` derive `H(L) ⊢ H(φ)` by induction on L (mirror)
- [ ] Create file `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean`
- [ ] Import `Cslib.Logics.Temporal.Metalogic.MCS`
- [ ] Implement `double_negation`: `⊢ ¬¬φ → φ` (promote from Completeness.lean `derive_dne`)
- [ ] Implement `efq_axiom`: `⊢ ⊥ → φ` (trivial axiom wrapper)
- [ ] Implement `pairing`: `⊢ φ → ψ → (φ ∧ ψ)` (derive from imp_s, imp_k, Peirce)
- [ ] Implement `lce_imp`: `⊢ (φ ∧ ψ) → φ` (left conjunction elimination)
- [ ] Implement `rce_imp`: `⊢ (φ ∧ ψ) → ψ` (right conjunction elimination)
- [ ] Implement `imp_trans`: from `⊢ φ → ψ` and `⊢ ψ → χ` derive `⊢ φ → χ`
- [ ] Implement `dni`: `⊢ φ → ¬¬φ` (double negation introduction)
- [ ] Implement `contraposition`: from `⊢ φ → ψ` derive `⊢ ¬ψ → ¬φ`
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.GeneralizedNecessitation`
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.PropositionalHelpers`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` - NEW file (~120 lines)
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` - NEW file (~100 lines)

**Verification**:
- Both files compile with `lake build`
- `generalized_temporal_k` and `generalized_past_k` prove by induction on List
- All propositional helpers are derivation tree constructions (no sorry)

---

### Phase 3: WitnessSeed Consistency [COMPLETED]

**Goal**: Create temporal witness seed definitions and consistency proofs. This is the heaviest Phase 0 prerequisite (~400 lines). Port from bimodal `Bundle/WitnessSeed.lean` (607 lines) with simplification (no `fc` parameter, always `FrameClass.Base`).

**Tasks**:
- [ ] Create file `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean`
- [ ] Import `TemporalContent`, `GeneralizedNecessitation`, `PropositionalHelpers`, `MCS`
- [ ] Port duality helpers: `some_future_all_future_neg_absurd` and `some_past_all_past_neg_absurd` (lines 67-100 of bimodal source). Remove `fc` parameter, use `FrameClass.Base` directly. Remove `(FrameClass.base_le fc)` replaced by `trivial`
- [ ] Port duality conversions: `neg_some_future_to_all_future_neg` and `neg_some_past_to_all_past_neg` (lines 106-142 of bimodal source)
- [ ] Port forward temporal witness seed definition: `forward_temporal_witness_seed M psi := {psi} ∪ g_content M`
- [ ] Port `forward_temporal_witness_seed_consistent`: If `F(ψ) ∈ M` for MCS M, then the forward seed is consistent (lines 148-259 of bimodal source). Adapt: replace `SetMaximalConsistent fc` with `Temporal.SetMaximalConsistent`, use temporal `generalized_temporal_k` from Phase 2, replace `set_lindenbaum_base` with `temporal_lindenbaum`
- [ ] Port past temporal witness seed: `past_temporal_witness_seed M psi := {psi} ∪ h_content M`
- [ ] Port `past_temporal_witness_seed_consistent` (lines 266-376 of bimodal source)
- [ ] Port until witness seed: `until_witness_seed_consistent` (lines 382-462 of bimodal source)
- [ ] Port since witness seed: `since_witness_seed_consistent` (lines 465-544 of bimodal source)
- [ ] Port g_content/h_content duality theorems: `g_content_subset_implies_h_content_reverse` and `h_content_subset_implies_g_content_reverse` (lines 552-606 of bimodal source). These use BX4/BX4' (connect_future/connect_past) which exist in the temporal axiom system
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.WitnessSeed`

**Timing**: 2.5 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean` - NEW file (~400-500 lines)

**Verification**:
- File compiles with `lake build`
- All 6 key theorems prove without sorry
- `g_content_subset_implies_h_content_reverse` works (critical for Frame.lean backward witnesses)

---

### Phase 4: ChronicleTypes (DCS and R-Relation Definitions) [COMPLETED]

**Goal**: Create the DCS (deductively closed set) infrastructure and all r-relation/Burgess relation definitions. Port from bimodal `Chronicle/ChronicleTypes.lean` (lines 67-218 only -- NOT the Chronicle structure, conditions, or Adjacent predicate which are Task 48).

**Tasks**:
- [ ] Create directory `Cslib/Logics/Temporal/Metalogic/Chronicle/`
- [ ] Create file `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean`
- [ ] Import `TemporalContent`, `GeneralizedNecessitation`, `PropositionalHelpers`, `MCS`
- [ ] Port `ClosedUnderDerivation` (remove `fc` parameter; use `FrameClass.Base` always): `def ClosedUnderDerivation (Omega : Set (Formula Atom)) : Prop := ∀ (L : List (Formula Atom)) (phi : Formula Atom), (∀ psi ∈ L, psi ∈ Omega) → (DerivationTree FrameClass.Base L phi) → phi ∈ Omega`
- [ ] Port `SetDeductivelyClosed`: `def SetDeductivelyClosed (Omega : Set (Formula Atom)) : Prop := Temporal.SetConsistent Omega ∧ ClosedUnderDerivation Omega`
- [ ] Port `mcs_is_dcs`: Temporal MCS is DCS. Use `temporal_closed_under_derivation`
- [ ] Port DCS helpers: `cud_contains_theorems`, `dcs_contains_theorems`, `cud_modus_ponens`, `dcs_modus_ponens`, `cud_conj_closed`, `dcs_conj_closed`, `cud_not_mem_is_sdc`
- [ ] Port r-relation definitions: `rRelation`, `rRelationSince`, `r3Relation`, `r3RelationSince`
- [ ] Port r-maximality definitions: `rMaximal`, `rMaximalSince`, `R3Maximal`, `R3MaximalSince` (remove `fc : FrameClass` parameter)
- [ ] Port Burgess relation definitions: `burgessR`, `burgessRSet`, `burgessRSince`, `burgessRSetSince`, `burgessR3`, `BurgessR3Maximal` (remove `fc : FrameClass` parameter)
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes`

**Timing**: 1.5 hours

**Depends on**: 1, 2, 3

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` - NEW file (~150 lines)

**Verification**:
- File compiles with `lake build`
- `mcs_is_dcs` proves using `temporal_closed_under_derivation`
- All definition signatures match bimodal naming (for Task 41 alignment)

---

### Phase 5: Chronicle Frame [COMPLETED]

**Goal**: Create `TPoint` structure, temporal ordering `t_le`, g/h-content closure under derivation, set consistency, transitivity, forward/backward witnesses, G/H forward/backward propagation, and eventuality resolution. Port from bimodal `Frame.lean` (464 lines) with ~60% transfer rate (bimodal-only content removed).

**Tasks**:
- [ ] Create file `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean`
- [ ] Import `ChronicleTypes`, `WitnessSeed`, `GeneralizedNecessitation`, `PropositionalHelpers`
- [ ] Define `TPoint (Atom : Type*)` structure: `formulas : Set (Formula Atom)` + `is_mcs : Temporal.SetMaximalConsistent formulas`
- [ ] Define `t_le (w v : TPoint Atom) : Prop := g_content w.formulas ⊆ v.formulas`
- [ ] Port `g_content_closed_derivation`: uses `generalized_temporal_k` from Phase 2 to show that if all `G(lᵢ) ∈ Ω` and `L ⊢ φ`, then `G(φ) ∈ Ω`
- [ ] Port `h_content_closed_derivation`: uses `generalized_past_k` (mirror)
- [ ] Port `g_content_set_consistent`: `g_content` of an MCS is consistent (uses serial_future axiom)
- [ ] Port `h_content_set_consistent`: mirror using serial_past
- [ ] Port `t_le_refl` with sorry (same irreflexive semantics issue as bimodal)
- [ ] Port `t_le_trans`: uses `mcs_g_trans` (temporal equivalent of bimodal `all_future_all_future`)
- [ ] Port `t_forward_witness`: if `F(ψ) ∈ w.formulas`, exists `v` with `t_le w v ∧ ψ ∈ v.formulas`. Uses `forward_temporal_witness_seed_consistent` from Phase 3
- [ ] Port `t_backward_witness`: if `P(ψ) ∈ w.formulas`, exists `v` with `t_le v w ∧ ψ ∈ v.formulas`. Uses `past_temporal_witness_seed_consistent` and `h_content_subset_implies_g_content_reverse`
- [ ] Port `t_G_forward` / `t_G_backward`: G membership forward/backward along `t_le`
- [ ] Port `t_H_forward` / `t_H_backward`: H membership forward/backward along `t_le`. Uses `g_content_subset_implies_h_content_reverse`
- [ ] Port `t_until_eventuality_resolution`: uses BX10 `until_F` axiom + `t_forward_witness`
- [ ] Port `t_since_eventuality_resolution`: uses BX10' `since_P` axiom + `t_backward_witness`
- [ ] DO NOT port: `bx_modal_equiv`, `bx_modal_witness`, `box_preserved_along_bx_le`, `neg_box_to_box_neg_box'` (these are bimodal-only, ~150 lines)
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.Frame`

**Timing**: 2 hours

**Depends on**: 1, 2, 3, 4

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` - NEW file (~250 lines)

**Verification**:
- File compiles with `lake build`
- Only sorry is in `t_le_refl`
- `t_forward_witness` and `t_backward_witness` prove without sorry
- `t_G_backward` constructs witness MCS via Lindenbaum's lemma

---

### Phase 6: CanonicalChain and OrderedSeedConsistency [COMPLETED]

**Goal**: Port the two small files that provide MCS-level axiom applications and seed consistency lemmas for the chronicle construction. Both are near-100% transfer with mechanical changes.

**Tasks**:
- [ ] Create file `Cslib/Logics/Temporal/Metalogic/Chronicle/CanonicalChain.lean`
- [ ] Import `Frame` (for TPoint)
- [ ] Port `F_imp_top_until_mcs`: `F(ψ) → ψ U ⊤` using BX12 `F_until_equiv` axiom. Change `BXPoint` to `TPoint`, `w.is_mcs` uses `Temporal.SetMaximalConsistent`
- [ ] Port `P_imp_top_since_mcs`: mirror using BX12' `P_since_equiv`
- [ ] Port `absorb_until_mcs`: `(φ ∧ (ψ U φ)) U φ → ψ U φ` using BX6 `absorb_until` axiom
- [ ] Port `absorb_since_mcs`: mirror using BX6' `absorb_since`
- [ ] Port `delegation_until_eventuality`: delegates to `t_until_eventuality_resolution` from Frame
- [ ] Port `delegation_since_eventuality`: mirror
- [ ] DO NOT import `Filtration.DefectChain` (bimodal-only import); remove that dependency
- [ ] Create file `Cslib/Logics/Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean`
- [ ] Import `Frame`, `CanonicalChain`
- [ ] Port `enriched_resolving_seed` definition and `enriched_resolving_seed_consistent` theorem. Uses `forward_temporal_witness_seed_consistent`, `lce_imp`, `rce_imp` from PropositionalHelpers
- [ ] Port `ordered_two_defect_seed_consistent` (special case of enriched resolving seed)
- [ ] Port `temp_linearity_mcs`: BX11 three-way disjunction at MCS level. Uses `pairing` from PropositionalHelpers and `temp_linearity` axiom
- [ ] Port `two_defect_consistent_seed`: combines `temp_linearity_mcs` with `enriched_resolving_seed_consistent`
- [ ] Port `no_new_f_defects`: uses `all_future_all_future` (= `mcs_g_trans` in temporal) and `some_future_all_future_neg_absurd` from WitnessSeed
- [ ] Port `resolved_target_in_successor`: trivial set membership
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.CanonicalChain`
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.OrderedSeedConsistency`

**Timing**: 1.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CanonicalChain.lean` - NEW file (~70 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean` - NEW file (~100 lines)

**Verification**:
- Both files compile with `lake build`
- No sorry in either file
- `temp_linearity_mcs` correctly produces the three-way disjunction

---

### Phase 7: RRelation Core Lemmas [NOT STARTED]

**Goal**: Port the main RRelation.lean from bimodal (1695 lines) to temporal (~800-1000 lines). This is the largest and most complex phase. It contains the deductive closure infrastructure, R-maximal extension existence via Zorn's lemma, Burgess absorption lemmas (Lemma 2.5), BurgessR3Maximal existence and properties, guard algebra, Burgess Lemma 2.3 equivalence, and Xu's Lemma 3.2.1.

**Tasks**:
- [ ] Create file `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean`
- [ ] Import `ChronicleTypes`, `WitnessSeed`, `GeneralizedNecessitation`, `PropositionalHelpers`, `Frame`, `Mathlib.Order.Zorn`
- [ ] Port `theorem_in_mcs` helper (private, remove `fc` parameter)
- [ ] Port `until_implies_F_in_mcs` and `until_self_accum_in_mcs` (BX10, BX5 at MCS level): remove `fc` parameter, use `Temporal.SetMaximalConsistent`
- [ ] Port `since_implies_P_in_mcs` (BX10' at MCS level)
- [ ] Port `rRelation_guard_continues'`: core Lemma 2.3 consequence
- [ ] Port deductive closure infrastructure: `deductiveClosure` definition, `deductiveClosure_subset`, `deductiveClosure_closed`, `deductiveClosure_is_dcs` (~lines 151-216)
- [ ] Port `rMaximal_extension_exists` via Zorn's lemma (~lines 233-296): remove `fc` parameter. The Zorn's lemma application uses `ClosedUnderDerivation` monotonicity over chains
- [ ] Port `rMaximalSince_extension_exists` (mirror, ~lines 300-333)
- [ ] Port `r3Maximal_extension_exists` and `r3MaximalSince_extension_exists` (~lines 352-439)
- [ ] Port Burgess absorption lemmas: `burgessR_absorption`, `burgessRSet_absorption`, `burgessRSince_absorption`, `burgessRSetSince_absorption`, `burgessR3_absorption` (Lemma 2.5, ~lines 489-607). Uses BX6/BX6' `absorb_until`/`absorb_since`
- [ ] Port `mcs_contrapositive_mem` helper (~lines 615-620)
- [ ] Port `c4_hard_case_G_neg_delta` and `c4'_hard_case_H_neg_delta` (~lines 637-700): adapt `liftBase` removal (replace with identity since all at FrameClass.Base)
- [ ] Port `burgessR3Maximal_extension_exists` (~lines 754-783): remove `fc` parameter
- [ ] Port BurgessR3Maximal accessor lemmas (~lines 790-809)
- [ ] Port BurgessR3 bridging lemmas (~lines 828-878): key for C4 condition
- [ ] Port `dcs_neg_insert_consistent` (~lines 895-926): adapt to use temporal `double_negation` from PropositionalHelpers
- [ ] Port guard algebra lemmas: `untl_conj_guard`, `untl_guard_strengthening`, `untl_guard_and_propagation`, `snce_conj_guard`, `snce_guard_strengthening`, `snce_guard_and_propagation` (~lines 947-1119): adapt propositional imports to use PropositionalHelpers
- [ ] Port `deductiveClosure_singleton_imp` (~lines 1140-1145)
- [ ] Port `burgessR_propagation` (~lines 1154-1174)
- [ ] Port `burgessR3Maximal_exists_from_seed` (~lines 1202-1220): remove `fc` parameter
- [ ] Port Burgess Lemma 2.3 equivalence (~lines 1222-1487): the core mathematical content. Uses A3a/A3b (enrichment_until/since), BX4/BX4' (connect_future/past), BX3/BX3' (right_mono_until/since). Adapt bimodal theorem references to temporal equivalents
- [ ] Port Xu's Lemma 3.2.1 (~lines 1488-1583): uses several helper lemmas from above
- [ ] Port `burgessR3Maximal_from_g_content_sub` (~lines 1637-1664): key infrastructure lemma
- [ ] Port `burgessR3Maximal_with_guard` (~lines 1678-1693): remove `fc` parameter
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation`

**Timing**: 3 hours

**Depends on**: 3, 4, 5, 6

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` - NEW file (~800-1000 lines)

**Verification**:
- File compiles with `lake build`
- No sorry anywhere in this file
- `burgessR3Maximal_exists_from_seed` proves (Lemma 2.4 witness existence)
- Burgess Lemma 2.3 equivalence proves (r-relation forward/backward directions)
- `burgessR3_absorption` proves (Lemma 2.5)
- Full project `lake build` succeeds with only the pre-existing `sorry` in Completeness.lean and the `t_le_refl` sorry in Frame.lean

## Testing & Validation

- [ ] After each phase: `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.{ModuleName}`
- [ ] After all phases: `lake build` (full project)
- [ ] Verify `t_le_refl` is the only NEW sorry (pre-existing sorry in Completeness.lean line 416 is unchanged)
- [ ] Verify no import cycles: new files import MCS.lean but NOT Completeness.lean
- [ ] Verify naming alignment: all r-relation names match bimodal (`rRelation`, `rMaximal`, `burgessR`, `BurgessR3Maximal`, etc.)
- [ ] Verify `TPoint` structure has correct fields and uses `Temporal.SetMaximalConsistent`

## Artifacts & Outputs

- `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean` (~120 lines)
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` (~120 lines)
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` (~100 lines)
- `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean` (~400-500 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` (~150 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` (~250 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CanonicalChain.lean` (~70 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean` (~100 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` (~800-1000 lines)
- **Total**: ~2110-2410 lines across 9 new files

## Rollback/Contingency

All work is in NEW files. No existing files are modified (except possibly `Metalogic.lean` to add imports). Rollback consists of deleting the new files:
```bash
rm -rf Cslib/Logics/Temporal/Metalogic/Chronicle/
rm -f Cslib/Logics/Temporal/Metalogic/TemporalContent.lean
rm -f Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean
rm -f Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean
rm -f Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean
```

If Phase 7 (RRelation) proves too large, it can be split into two files:
- `RRelation/Core.lean` (deductive closure, Zorn existence, absorption)
- `RRelation/Lemmas.lean` (Burgess 2.3 equivalence, Xu 3.2.1, guard algebra)
