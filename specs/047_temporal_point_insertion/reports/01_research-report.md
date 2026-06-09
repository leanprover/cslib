# Research Report: Task 47 -- Temporal Point Insertion

**Task**: 47 -- Temporal Point Insertion
**Date**: 2026-06-09
**Session**: sess_1781037367_539c9b_47

---

## 1. Executive Summary

Task 47 ports the chronicle type extensions and point insertion proofs from the bimodal `BXCanonical/Chronicle/` to the temporal `Temporal/Metalogic/Chronicle/` module. The key mathematical content is Burgess Lemmas 2.4-2.8: constructing Until/Since witnesses and eliminating chronicle defects via point insertion.

**Task 46 created substantial temporal infrastructure** that Task 47 can build on. The existing temporal Chronicle files already contain: DCS definitions, r-relation, r3-relation, R-maximality, Burgess R3/R3Maximal, deductive closure, Zorn-based maximal extension existence, burgessR3 absorption, and several key helpers. This means Task 47's scope is primarily:

1. **Extending RRelation.lean** with missing monotonicity helpers and the `burgessR_implies_burgessRSince` / `burgessRSince_implies_burgessR` lemmas
2. **Creating PointInsertion.lean** with Lemmas 2.4-2.8 and their Since-direction mirrors, plus Xu Lemma 3.2.1

**Central simplification vs bimodal**: No `FrameClass` parameter (single proof system), no box modality (eliminates C5b/C6b cases entirely).

---

## 2. Existing Infrastructure Inventory (from Task 46)

### 2.1 ChronicleTypes.lean (216 lines) -- COMPLETE

Already contains:
- `ClosedUnderDerivation`, `SetDeductivelyClosed`, `mcs_is_dcs`
- `cud_contains_theorems`, `dcs_contains_theorems`, `cud_modus_ponens`, `dcs_modus_ponens`
- `cud_conj_closed`, `dcs_conj_closed`, `cud_not_mem_is_sdc`
- `rRelation`, `rRelationSince`, `r3Relation`, `r3RelationSince`
- `rMaximal`, `rMaximalSince`, `R3Maximal`, `R3MaximalSince`
- `burgessR`, `burgessRSet`, `burgessRSince`, `burgessRSetSince`, `burgessR3`, `BurgessR3Maximal`
- `rRelation_subset`, `rRelationSince_subset`, `r3Relation_subset`
- `R3Maximal_dcs`, `R3Maximal_r3`
- `SetConsistent_of_subset`

**No chronicle structure or conditions C0-C5 yet** -- these are in the bimodal ChronicleTypes.lean (lines 221-286) but NOT in the temporal version. Task 47 should NOT add them here since they belong to Task 48 (counterexample elimination / full chronicle construction). Point insertion operates purely at the BurgessR3Maximal level.

### 2.2 Frame.lean (254 lines) -- COMPLETE

Already contains:
- `TPoint` structure, `t_le` ordering
- `g_content_closed_derivation`, `h_content_closed_derivation`
- `g_content_set_consistent`, `h_content_set_consistent`
- `t_le_refl` (sorry'd), `t_le_trans`
- `t_forward_witness`, `t_backward_witness`
- `t_G_forward`, `t_G_backward`, `t_H_forward`, `t_H_backward`
- `t_until_eventuality_resolution`, `t_since_eventuality_resolution`

### 2.3 RRelation.lean (424 lines) -- PARTIAL

Already contains:
- `theorem_in_mcs'`, `until_implies_F_in_mcs`, `until_self_accum_in_mcs`, `since_implies_P_in_mcs`
- `rRelation_guard_continues'`
- `deductiveClosure`, `subset_deductiveClosure`, `deductiveClosure_closed`, `deductiveClosure_consistent`, `deductiveClosure_is_dcs`, `deductiveClosure_closed_under_derivation`
- `rMaximal_extension_exists` (Zorn-based)
- `r3Maximal_extension_exists` (Zorn-based)
- `burgessR_absorption`, `burgessRSince_absorption`, `burgessRSet_absorption`, `burgessRSetSince_absorption`, `burgessR3_absorption`
- `deductiveClosure_singleton_imp`, `dcs_neg_insert_consistent`
- `mcs_contrapositive_mem`
- `burgessR3Maximal_extension_exists`, `burgessR3Maximal_from_g_content_sub`

**MISSING (needed by PointInsertion)**:
- `untl_left_mono_G` -- G(phi->psi) -> untl(event, phi) -> untl(event, psi)
- `untl_left_mono_thm` -- derives untl_left_mono_G from a theorem
- `snce_left_mono_H` -- H(phi->psi) -> snce(event, phi) -> snce(event, psi)
- `snce_left_mono_thm` -- derives snce_left_mono_H from a theorem
- `burgessR_implies_burgessRSince` -- key duality: burgessR(A, beta, C) implies snce(alpha, beta) in C for all alpha in A
- `burgessRSince_implies_burgessR` -- mirror duality

### 2.4 Other Temporal Files

- `TemporalContent.lean` (222 lines): `g_content`, `h_content`, `f_content`, `p_content`, `u_content`, `s_content` + membership lemmas + duality
- `GeneralizedNecessitation.lean` (163 lines): `generalized_temporal_k`, `generalized_past_k`, `temp_k_dist_derived`, `past_k_dist`, `past_necessitation`
- `PropositionalHelpers.lean` (174 lines): `double_negation`, `efq_axiom`, `imp_trans`, `pairing`, `lce_imp`, `rce_imp`, `dni`
- `WitnessSeed.lean` (253 lines): `forward_temporal_witness_seed_consistent`, `past_temporal_witness_seed_consistent`, `until_witness_seed_consistent`, `since_witness_seed_consistent`, `g_content_subset_implies_h_content_reverse`, `h_content_subset_implies_g_content_reverse`
- `MCS.lean`: `temporal_lindenbaum`, `temporal_implication_property`, `temporal_closed_under_derivation`, `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem`, `neg_some_future_to_all_future_neg`, `neg_some_past_to_all_past_neg`, `mcs_g_trans`
- `CanonicalChain.lean` (78 lines): canonical chain infrastructure
- `OrderedSeedConsistency.lean` (136 lines): ordered seed consistency

### 2.5 Temporal Axiom System (all needed axioms present)

The temporal axiom system at `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` includes ALL axioms needed for point insertion:
- `enrichment_until` (BX13): p /\ U(psi, phi) -> U(psi /\ S(phi, p), phi)
- `enrichment_since` (BX13'): p /\ S(psi, phi) -> S(psi /\ U(phi, p), phi)
- `self_accum_until` (BX5): U(psi, phi) -> U(psi, phi /\ U(psi, phi))
- `self_accum_since` (BX5'): S(psi, phi) -> S(psi, phi /\ S(psi, phi))
- `absorb_until` (BX6): U(phi /\ U(psi, phi), phi) -> U(psi, phi)
- `absorb_since` (BX6'): S(phi /\ S(psi, phi), phi) -> S(psi, phi)
- `linear_until` (BX7): conj -> D1 \/ D2 \/ D3
- `linear_since` (BX7'): mirror
- `left_mono_until_G` (BX2G), `left_mono_since_H` (BX2H)
- `right_mono_until` (BX3), `right_mono_since` (BX3')
- `connect_future` (BX4), `connect_past` (BX4')
- `until_F` (BX10), `since_P` (BX10')
- `serial_future`, `serial_past`
- `F_until_equiv`, `P_since_equiv`

---

## 3. Transfer Analysis: Bimodal PointInsertion.lean (3556 lines)

### 3.1 Structure of the Bimodal File

The file contains these major sections:

| Lines | Content | Transfer Notes |
|-------|---------|----------------|
| 1-100 | Header, imports, helper defs | Rewrite imports, remove fc |
| 111-200 | `F_neg_of_G_not`, `P_neg_of_H_not`, `lemma_2_4` | Port with fc removal |
| 200-310 | `until_F_mcs`, `self_accum_until_mcs`, `connect_future_mcs`, `conj_mcs`, `or_elim_mcs`, `linear_until_mcs`, `linear_since_mcs`, `lemma_2_5b` | Port directly |
| 310-370 | `lemma_2_6` (counterexample insertion) | Port directly |
| 370-470 | `conj_left_mcs`, `conj_right_mcs`, `G_implies_F_mcs`, `H_implies_P_mcs` | Port directly |
| 470-570 | `dcs_neg_union_consistent`, `r3Maximal_neg_of_not_mem`, `R3Maximal_is_mcs`, `mcs_no_proper_dcs_extension` | Port directly |
| 575-680 | `dc_delta_B_controlled`, `BurgessR3Maximal_extension_fails`, `dc_delta_B_burgessR3` | Port directly |
| 680-840 | `xu_lemma_2_3_since_top`, `xu_lemma_2_3_until_top` | Port directly |
| 840-1050 | `burgessR3_univ_of_inconsistent_ext`, `g_content_sub` proof | Port directly |
| 1050-1160 | Right/left mono derivation helpers | Port directly |
| 1155-1500 | Enrichment structures, iterated enrichment | Port directly |
| 1500-1700 | `xu_lemma_3_2_1_until`, `xu_lemma_3_2_1_since` | Port directly |
| 1700-2300 | `lemma_2_7` seed + main theorem, `lemma_2_8` | Port directly |
| 2300-2600 | Mirror: `lemma_2_7_since_seed`, `lemma_2_7_since` | **THIS IS THE SINCE MIRROR** |
| 2600-3200 | `lemma_2_8_since_seed_consistent`, `lemma_2_8_since` | **SINCE MIRROR** |
| 3200-3556 | `lemma_2_4_with_guard`, `lemma_2_4_since_with_guard` | Port directly |

### 3.2 What Does NOT Transfer

1. **`FrameClass` parameter**: Every function signature has `(fc : FrameClass)` -- remove all occurrences
2. **`liftBase`**: Used to lift base-level derivations to arbitrary frame class -- remove
3. **Bimodal import paths**: All `Cslib.Logic.Bimodal.*` references -> `Cslib.Logic.Temporal.*`
4. **Bimodal theorem references**: `Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived` -> `temp_k_dist_derived` (already in temporal namespace)
5. **`Cslib.Logic.Bimodal.Theorems.past_necessitation`** -> `past_necessitation` (already in temporal)
6. **`Cslib.Logic.Bimodal.Theorems.past_k_dist`** -> `past_k_dist` (already in temporal)
7. **`Cslib.Logic.Bimodal.Theorems.Combinators.*`** -> temporal PropositionalHelpers equivalents
8. **`Cslib.Logic.Bimodal.Theorems.Propositional.*`** -> temporal PropositionalHelpers equivalents
9. **`SetMaximalConsistent fc`** -> `Temporal.SetMaximalConsistent`
10. **`SetConsistent fc`** -> `Temporal.SetConsistent`
11. **`set_lindenbaum_fc`** -> `temporal_lindenbaum`
12. **`SetMaximalConsistent.implication_property`** -> `temporal_implication_property`
13. **`SetMaximalConsistent.negation_complete`** -> `temporal_negation_complete`
14. **`SetMaximalConsistent.neg_excludes`** -> `mcs_not_mem_of_neg`

### 3.3 Box-related code (ELIMINATE)

**None found in PointInsertion.lean.** The bimodal PointInsertion.lean does not contain any box-specific cases. The C5b/C6b elimination happens at the chronicle construction level (Task 48), not at the point insertion level. All 3556 lines transfer with only mechanical changes.

---

## 4. Dependency Analysis and Phase Decomposition

### 4.1 Phase 0: RRelation Extension (~250-350 lines)

The temporal RRelation.lean needs these additions BEFORE PointInsertion.lean can be created:

1. **Left monotonicity helpers**:
   - `untl_left_mono_G`: G(phi -> psi) -> untl(event, phi) -> untl(event, psi) at MCS level
   - `untl_left_mono_thm`: theorem-level version (derive via temporal_necessitation + untl_left_mono_G)
   - `snce_left_mono_H`: H(phi -> psi) -> snce(event, phi) -> snce(event, psi) at MCS level
   - `snce_left_mono_thm`: theorem-level version

2. **BurgessR duality lemmas**:
   - `burgessR_implies_burgessRSince`: If burgessR(A, beta, C) then snce(alpha, beta) in C for all alpha in A
   - `burgessRSince_implies_burgessR`: Mirror

These are defined in the bimodal `RRelation.lean` at lines 1066-1500 (approximately 400 lines of bimodal code). With fc removal, this becomes roughly 250-350 lines.

### 4.2 Phase 1: Core PointInsertion Helpers (~400-500 lines)

Create `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` with:

1. **MCS-level axiom helpers**: `until_F_mcs`, `self_accum_until_mcs`, `self_accum_since_mcs`, `connect_future_mcs`, `conj_mcs`, `or_elim_mcs`, `linear_until_mcs`, `linear_since_mcs`, `conj_left_mcs`, `conj_right_mcs`
2. **F/G and P/H helpers**: `F_neg_of_G_not`, `P_neg_of_H_not`, `G_implies_F_mcs`, `H_implies_P_mcs`
3. **DCS/R3Maximal properties**: `dcs_neg_union_consistent` (already in RRelation), `r3Maximal_neg_of_not_mem`, `R3Maximal_is_mcs`, `mcs_no_proper_dcs_extension`
4. **BurgessR3Maximal helpers**: `dc_delta_B_controlled`, `BurgessR3Maximal_extension_fails`, `dc_delta_B_burgessR3`
5. **Content ordering**: `lemma_2_5b`, `lemma_2_5b_past`

### 4.3 Phase 2: Xu Lemmas and Content Proofs (~500-700 lines)

1. **Xu Lemma 2.3**: `xu_lemma_2_3_since_top`, `xu_lemma_2_3_until_top`
2. **Inconsistent extension helpers**: `burgessR3_univ_of_inconsistent_ext`, content duality, g_content subset from BurgessR3Maximal
3. **Derivation-level monotonicity**: `untl_left_mono_deriv`, `snce_left_mono_deriv`, `untl_right_mono_deriv`, `snce_right_mono_deriv`
4. **List conjunction helpers**: `list_conj`, `list_conj_implies_elem`, `list_conj_mem_dcs`, `list_conj_mem_mcs`
5. **Enrichment structures**: `EnrichedEvent`, `iterated_enrichment`, `EnrichedEventSince`, `iterated_enrichment_since`
6. **Xu Lemma 3.2.1**: `xu_lemma_3_2_1_until`, `xu_lemma_3_2_1_since`

### 4.4 Phase 3: Lemmas 2.4-2.8 (Until direction) (~500-700 lines)

1. **Lemma 2.4**: Until witness endpoint construction
2. **Lemma 2.6**: Counterexample insertion (delta not in C -> insert D with neg delta)
3. **Lemma 2.7**: Until-formula splitting (the main result)
4. **Lemma 2.8**: Variant of 2.7 with additional hypothesis about C
5. **Lemma 2.4 with guard**: Strengthened version returning guard membership

### 4.5 Phase 4: Since-direction Mirrors (~500-700 lines)

1. **Lemma 2.7 since**: Mirror of 2.7 using BX5'/BX7'/BX13'
2. **Lemma 2.8 since**: Mirror of 2.8
3. **Lemma 2.4 since with guard**: Since-direction of 2.4 with guard

---

## 5. Key Risks and Mitigations

### Risk 1: MCS API Mismatch (MEDIUM)

The bimodal code uses `SetMaximalConsistent fc` with methods like `.implication_property`, `.negation_complete`, `.neg_excludes`, `.closed_under_derivation`. The temporal code uses standalone functions like `temporal_implication_property`, `temporal_negation_complete`, `mcs_neg_of_not_mem`.

**Mitigation**: Systematic search-and-replace during porting. The functionality is identical; only the calling convention differs.

### Risk 2: `FrameClass` Removal Cascading (LOW)

Every definition and theorem in the bimodal file carries `(fc : FrameClass)`. The temporal versions drop this parameter entirely, using `FrameClass.Base` as the fixed derivation system.

**Mitigation**: Straightforward removal. The temporal `DerivationTree` already uses `FrameClass.Base` throughout.

### Risk 3: Missing `identity` combinator (LOW)

The bimodal code uses `Cslib.Logic.Bimodal.Theorems.Combinators.identity` in several places. The temporal `PropositionalHelpers.lean` does not export a named `identity` combinator.

**Mitigation**: Define `identity` locally or add to `PropositionalHelpers.lean`:
```lean
def identity (φ : Formula Atom) : DerivationTree FrameClass.Base [] (φ.imp φ) :=
  DerivationTree.axiom [] _ (Axiom.imp_refl φ) trivial
```
Or use `imp_refl` axiom directly.

### Risk 4: `theorem_flip` / `mp` helpers (LOW)

The bimodal code uses `theorem_flip` and `mp` as derivation combinators. These may need temporal equivalents.

**Mitigation**: Define locally or port from bimodal Combinators.lean. These are simple propositional derivations.

### Risk 5: `some_future_all_future_neg_absurd` scope (LOW)

This is already available in temporal `WitnessSeed.lean`. Verify it's accessible from the Chronicle namespace.

**Mitigation**: Add appropriate `open` declarations.

### Risk 6: Existing sorry in Frame.lean (LOW)

`t_le_refl` has a sorry. This does not affect point insertion, which operates at the BurgessR3Maximal level, not the TPoint ordering level.

---

## 6. Line Count Estimate

| Phase | Description | Estimated Lines |
|-------|-------------|-----------------|
| Phase 0 | RRelation extension (monotonicity + duality) | 250-350 |
| Phase 1 | PointInsertion core helpers | 400-500 |
| Phase 2 | Xu lemmas + enrichment | 500-700 |
| Phase 3 | Lemmas 2.4-2.8 (Until) | 500-700 |
| Phase 4 | Since-direction mirrors | 500-700 |
| **Total** | | **2150-2950** |

This aligns with the task description estimate of 1500-2800 lines.

---

## 7. Literature Proof Structure

**Source**: Burgess 1982 "Axioms for tense logic II", Section 2, Lemmas 2.4-2.8; Xu 1988 "An approach to bimodal temporal logic", Section 3

**Strategy**: Direct construction + Zorn's lemma for maximality, linearity axiom for splitting

### Step Map

1. **Lemma 2.4 (witness existence)**: Given U(gamma, beta) in MCS A, construct MCS C with beta in C and g_content(A) subset C, plus BurgessR3Maximal(A, B, C).
   - Source: Burgess 1982, Lemma 2.4
   - Lean approach: forward_temporal_witness_seed + Lindenbaum + burgessR3Maximal_from_g_content_sub

2. **Lemma 2.5b (transitivity)**: g_content ordering is transitive.
   - Source: Burgess 1982, Lemma 2.5
   - Lean approach: GG(phi) in A (axiom 4 transitivity) -> G(phi) in D -> phi in C

3. **Lemma 2.6 (counterexample insertion)**: Given BurgessR3Maximal(A, B, C) and delta not in C, produce MCS D with neg-delta in D and g_content(A) subset D.
   - Source: Burgess 1982, Lemma 2.6
   - Lean approach: F(neg delta) from G(delta) not in A + Lindenbaum

4. **Xu Lemma 2.3 (top-guard presence)**: If BurgessR3Maximal(A, B, C), then S(alpha, top) in B for all alpha in A, and U(gamma, top) in B for all gamma in C.
   - Source: Xu 1988, Lemma 2.3
   - Lean approach: Contradiction via BurgessR3Maximal_extension_fails + dc_delta_B_burgessR3

5. **Xu Lemma 3.2.1 (full guard presence)**: If BurgessR3Maximal(A, B, C), then U(gamma, beta) in B for all beta in B and gamma in C.
   - Source: Xu 1988, Lemma 3.2.1
   - Lean approach: BX5 (self_accum) + BX3/BX2G monotonicity + contradiction

6. **Lemma 2.7 (Until splitting)**: Given BurgessR3Maximal(A, B, C) with U(xi, eta) in A and eta not in B, produce D with xi in D and BurgessR3Maximal(A, B', D) and BurgessR3Maximal(D, B'', C).
   - Source: Burgess 1982, Lemma 2.7 (with BX13 enrichment from task 107)
   - Lean approach: BX5 + BX7 (linearity) + BX13 (enrichment) + seed consistency + Lindenbaum

7. **Lemma 2.8 (variant)**: Like 2.7 with additional hypothesis.
   - Source: Burgess 1982, Lemma 2.8

### Dependencies
- Steps 4, 5 depend on Step 1 (BurgessR3Maximal infrastructure)
- Step 6 depends on Steps 4 and 5
- Step 7 depends on Step 6

---

## 8. Recommendations

1. **Phase ordering**: Start with Phase 0 (RRelation extension) as it unblocks all subsequent phases.
2. **File organization**: Create PointInsertion.lean as a single file (matching bimodal structure). It will be large (2000+ lines) but cohesive.
3. **Incremental verification**: Run `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation` after Phase 0, then `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion` after each subsequent phase.
4. **Do NOT add Chronicle/ChronicleTypes conditions C0-C5**: These belong to Task 48 and should not be added prematurely.
5. **The existing temporal ChronicleTypes.lean and RRelation.lean are correct**: No modifications needed to existing definitions, only additions.

---

## References

- Burgess 1982: "Axioms for tense logic II: Time periods", Sections 2.4-2.8
- Xu 1988: "An approach to bimodal temporal logic", Sections 2.5, 3.2
- Bimodal source: `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` (3556 lines)
- Bimodal source: `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean` (1591 lines)
- Task 50 seed research: `specs/050_burgess_prior_art_seed_research/reports/`
