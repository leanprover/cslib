# Implementation Plan: Dense Temporal Completeness

- **Task**: 38 - Dense temporal completeness
- **Status**: [IMPLEMENTING]
- **Effort**: 8 hours
- **Dependencies**: None (independent of bimodal dense completeness task 36)
- **Research Inputs**: specs/038_temporal_dense_completeness/reports/01_dense-completeness-research.md
- **Artifacts**: plans/01_dense-completeness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Prove that every formula valid on all dense serial linear orders is derivable in the Dense temporal proof system. The implementation adds two dense axioms (density: `G(G phi) -> G phi`, dense_indicator: `neg U(top, bot)`), builds FC-parameterized MCS infrastructure, proves dense soundness, proves `DenselyOrdered` for the chronicle subtype when starting from a Dense-MCS, and assembles the dense completeness theorem.

The key architectural insight from research: the existing chronicle construction uses `Temporal.SetMaximalConsistent` (hardcoded to `FrameClass.Base`). Dense completeness requires Dense-MCS at each chronicle point to ensure `neg U(top, bot)` membership, which via C4 proves `DenselyOrdered`. Rather than re-parameterizing the entire chronicle, we prove `Dense-MCS => Base-MCS` and show that `neg U(top, bot)` propagates through the chronicle from the starting Dense-MCS via G-necessitation and the existing G-distribution infrastructure.

### Research Integration

Key findings from the research report integrated:
- The bimodal Dense.lean provides a structural template (contrapositive + MCS + case split on dense_indicator)
- `limit_satisfies_c4` is the key tool for proving `DenselyOrdered`: given `neg U(eta, xi)` at `x` and `eta` at `y`, produces `z` between them
- All 26 Base axioms have `minFrameClass = .Base`, so `Base <= Dense` ensures they are available at Dense frame class
- `ValidDense` already exists in `Validity.lean` with the correct `DenselyOrdered D` constraint
- The bimodal has `set_lindenbaum_fc`, `mcs_to_base`, and `theoremInMcsFc` patterns we can follow

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add `density` and `dense_indicator` axiom constructors gated to `FrameClass.Dense`
- Prove soundness of both dense axioms on `DenselyOrdered` frames
- Build FC-parameterized MCS infrastructure (thin wrappers around generic `Metalogic.*`)
- Prove `Dense-MCS => Base-MCS` (enables chronicle reuse)
- Prove `DenselyOrdered` instance for chronicle subtype when starting from Dense-MCS
- State and prove `completeness_dense`: `ValidDense phi -> Temporal.ThDerivableFc .Dense phi`

**Non-Goals**:
- Re-parameterizing the entire chronicle construction by frame class (avoided by the G-propagation approach)
- Proving discrete completeness (separate task)
- Fixing the bimodal universe sorry in task 36

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Adding axiom constructors breaks pattern matches in Soundness.lean | M | H | Phase 1 adds axioms and updates all `cases h_ax` matches immediately; verify with `lake build` |
| G-propagation of `neg U(top,bot)` through chronicle may not hold at all limit points | H | M | Phase 4 implements the detailed argument: G(neg U(top,bot)) in MCS A implies neg U(top,bot) at every limit point via `derive_g_contradiction` / `mcs_g_mp`. Fall back to DCS argument or FC-parameterized chronicle if needed |
| `DenselyOrdered` instance proof may have universe issues similar to bimodal | M | L | Temporal chronicle is simpler (no box operator), subtype is on Rat which is already DenselyOrdered; universe should be concrete |
| New axiom constructors increase heartbeats in existing proofs | L | M | Add `set_option maxHeartbeats` locally if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Dense Axiom Additions [COMPLETED]

**Goal**: Add `density` and `dense_indicator` constructors to `Axiom`, update `minFrameClass`, and fix all downstream pattern matches.

**Tasks**:
- [ ] Add `density (phi : Formula Atom) : Axiom (phi.allFuture.allFuture.imp phi.allFuture)` constructor to `Axiom` inductive
- [ ] Add `dense_indicator : Axiom (Formula.untl Formula.top Formula.bot).neg` constructor to `Axiom` inductive
- [ ] Update `minFrameClass` to return `.Dense` for `density` and `dense_indicator` (replace catch-all `| _ => .Base` with explicit cases)
- [ ] Update docstring to say "28 constructors" and add "Layer 3: Density (2)"
- [ ] Fix `axiom_sound` in `Soundness.lean`: add two new cases that discharge by contradiction on `h_fc` (since `Dense <= Base` is false)
- [ ] Fix any other `cases h_ax` matches in `Instances.lean` (add two new cases for the HasAxiom instances)
- [ ] Verify with `lake build Cslib.Logics.Temporal.ProofSystem.Axioms` and `lake build Cslib.Logics.Temporal.Metalogic.Soundness`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` - Add 2 constructors, update minFrameClass
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean` - Add 2 impossible cases to axiom_sound
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` - Add HasAxiom instances for new axioms

**Verification**:
- `lake build Cslib.Logics.Temporal.ProofSystem` compiles without errors
- `lake build Cslib.Logics.Temporal.Metalogic.Soundness` compiles without errors

---

### Phase 2: FC-Parameterized MCS Infrastructure [COMPLETED]

**Goal**: Create FC-parameterized derivability, consistency, MCS, and Lindenbaum infrastructure mirroring the Base versions but parameterized by `fc : FrameClass`.

**Tasks**:
- [ ] Define `Temporal.DerivFc (fc : FrameClass) (Gamma : List (Formula Atom)) (phi : Formula Atom) : Prop := Nonempty (DerivationTree fc Gamma phi)`
- [ ] Define `Temporal.ThDerivableFc (fc : FrameClass) (phi : Formula Atom) : Prop := Temporal.DerivFc fc [] phi`
- [ ] Define `temporalDerivationSystemFc (fc : FrameClass) : Metalogic.DerivationSystem (Formula Atom)` mirroring `temporalDerivationSystem` but using `DerivFc fc`
- [ ] Define `Temporal.SetConsistentFc (fc : FrameClass)` and `Temporal.SetMaximalConsistentFc (fc : FrameClass)` as abbreviations using `temporalDerivationSystemFc fc`
- [ ] Prove `temporal_lindenbaum_fc`: FC-parameterized Lindenbaum lemma (direct instantiation of `Metalogic.set_lindenbaum`)
- [ ] Prove `temporal_has_deduction_theorem_fc`: deduction theorem at arbitrary fc
- [ ] Prove helper lemmas: `temporal_closed_under_derivation_fc`, `temporal_implication_property_fc`, `temporal_negation_complete_fc`
- [ ] Prove `theoremInMcsFc`: theorems at fc belong to every fc-MCS
- [ ] Prove negation lemmas: `mcs_bot_not_mem_fc`, `mcs_neg_of_not_mem_fc`, `mcs_not_mem_of_neg_fc`
- [ ] Prove key enabler: `dense_mcs_implies_base_mcs` -- `SetMaximalConsistentFc .Dense M -> Temporal.SetMaximalConsistent M` (via `FrameClass.base_le` lifting: Dense-consistent implies Base-consistent; Dense-MCS negation-completeness gives Base-maximality)
- [ ] Prove `set_consistent_fc_not_both`: phi and neg phi cannot both be in an fc-consistent set

**Timing**: 2 hours

**Depends on**: Phase 1 (needs the updated Axiom type)

**Files to create**:
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` - All FC-parameterized infrastructure (~200 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.DenseMCS` compiles without errors

---

### Phase 3: Dense Soundness [COMPLETED]

**Goal**: Prove that both dense axioms are semantically valid on `DenselyOrdered` frames, and build a unified `axiom_sound_dense` theorem.

**Tasks**:
- [ ] Prove `density_axiom_sound`: `G(G phi) -> G phi` valid on `DenselyOrdered` domains. Proof: assume `F(neg(G phi))`, i.e., exists `s > t` with `F(neg phi)` at `s`. From `F(neg phi)` at `s`, get `s' > s` with `neg phi` at `s'`. Since `s' > t`, this witnesses `F(neg phi)` at `t`, contradicting `G(G phi)`. Actually: G(G phi) means "for all future s, G(phi) at s". By `exists_between` from `DenselyOrdered`, for any `s > t`, get `r` with `t < r < s`, then `G(phi)` at `r` gives `phi` at `s`.
- [ ] Prove `dense_indicator_sound`: `neg U(top, bot)` valid on `DenselyOrdered` domains. Proof: assume `U(top, bot)` at `t`, then exists `s > t` with `top` at `s` and `bot` between. By `exists_between`, get `r` with `t < r < s`, then `bot` at `r` is a contradiction.
- [ ] Prove `axiom_sound_dense`: for any axiom `h : Axiom phi` with `h.minFrameClass <= .Dense`, `phi` is valid on dense serial linear orders. The 26 Base cases delegate to existing `axiom_sound` (since `Base <= Dense`); the 2 Dense cases use the new lemmas.
- [ ] Prove `soundness_dense`: full derivation tree soundness at `FrameClass.Dense` over dense serial linear orders (induction on derivation tree, same structure as `soundness`)
- [ ] Prove `soundness_thderivable_dense`: if `ThDerivableFc .Dense phi`, then `ValidDense phi`

**Timing**: 1.5 hours

**Depends on**: Phase 1 (needs `density` and `dense_indicator` constructors)

**Files to create**:
- `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean` - Dense soundness proofs (~150 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.DenseSoundness` compiles without errors

---

### Phase 4: DenselyOrdered Instance for Chronicle Subtype [IN PROGRESS]

**Goal**: Prove that when the starting MCS `A` is a Dense-MCS, the chronicle subtype `{x : Rat // x in limitDom}` is `DenselyOrdered`.

**Tasks**:
- [ ] Prove `dense_indicator_in_dense_mcs`: `neg U(top, bot)` is in every Dense-MCS (it is a Dense theorem via the `dense_indicator` axiom)
- [ ] Prove `g_dense_indicator_in_dense_mcs`: `G(neg U(top, bot))` is in every Dense-MCS (by temporal necessitation of the above)
- [ ] Prove `dense_indicator_at_limit_points`: for all `x` in `limitDom` where `A` is Dense-MCS, `neg U(top, bot)` is in `limitF(x)`. Proof strategy:
  - For `x = 0`: `limitF(0) = A` and `neg U(top, bot)` is in A by `dense_indicator_in_dense_mcs`
  - For `x > 0`: `G(neg U(top, bot))` is in A. Use `derive_g_contradiction` pattern: G-necessitation gives G(neg U(top,bot)) as a Base theorem from the Dense-MCS. Then since `limitF(0) = A` is a Base-MCS containing `G(neg U(top,bot))`, the chronicle's C2 condition propagates it forward. Actually, the simpler argument: `neg U(top,bot)` is a Dense theorem. Every Dense theorem is in every Dense-MCS. But `limitF(x)` is only a Base-MCS. Alternative: prove `neg U(top,bot)` in `limitF(x)` by using `derive_g_contradiction h_base_mcs [neg U(top,bot)] (G-nec of dense_indicator lifted to Base? No, dense_indicator is not a Base theorem!)`.
  
  **Revised strategy**: Since `limitF(x)` are Base-MCS (not Dense-MCS), we cannot directly claim `neg U(top,bot)` membership. Instead, use the C4 argument ONLY for the specific pair `(x, y)` where we need density, using `limitF(x)` containing `neg U(top,bot)` WHEN `x = 0` (since `limitF(0) = A` is Dense-MCS). For general `x`, observe:
  
  The chronicle subtype has the property that between any two points `x < y`, we can find an intermediate point. Consider the chain `0 < x` (or `x < 0`): since `A = limitF(0)` is Dense-MCS containing `neg U(top, bot)`, and `top` is in `limitF(x)`, by `limit_satisfies_c4` there exists `z` with `0 < z < x` and `bot.neg = top` at `z`. Repeating: between `z` and `x`, we need `neg U(top, bot)` at `z`. But `limitF(z)` is a Base-MCS...
  
  **Final strategy**: Use the TRANSITIVE density argument. For arbitrary `x < y` in limitDom:
  1. Case `0 <= x`: We have `neg U(top, bot)` at `limitF(0)` (Dense-MCS). Apply `limit_satisfies_c4` with `xi = bot, eta = top` at `(0, y)` to get `z1` between `0` and `y`. If `x < z1 < y`, done. If `z1 <= x`, apply again at `(0, x)` to get `z2` between `0` and `x`. Continue...
  
  Actually, this is getting circular. The clean solution from the research is:

  **Clean strategy (from research Approach D/F)**: Instead of trying to show `neg U(top,bot)` at every limit point, observe that we DO have it at `limitF(0) = A`. The chronicle construction guarantees that for the specific counterexample enumeration `(0, y, top, bot, c4_forward)`, if `neg U(top, bot)` is at `limitF(0)` and `top` is at `limitF(y)`, then a new point is inserted between 0 and y. By the omega-chain construction, between 0 and ANY point `y > 0` in limitDom, there ALREADY EXISTS a point (from the C5 processing of F(top) at 0). Similarly, between ANY point `x < 0` and 0, there exists a point.
  
  For the general case `x < y` where neither is 0: we need to show that the omega-chain has already processed the counterexample `(x, y, top, bot, c4_forward)` if `neg U(top,bot)` is at `limitF(x)`. But we don't know this for general x.
  
  **Simplest correct approach**: Prove `DenselyOrdered` by showing that between any two limit domain points `x < y`, the limit domain contains an intermediate point. The proof uses:
  1. `limitF(x)` is a Base-MCS, so `F(top) in limitF(x)` by seriality
  2. By `limit_F_resolution`, there exists `z > x` in limitDom with `top in limitF(z)`
  3. But z might be >= y
  
  This doesn't guarantee z < y. The issue is fundamental: without `neg U(top, bot)` at `limitF(x)`, we have no tool to place z between x and y specifically.
  
  **The correct approach (aligns with research recommendation)**: FC-parameterize the chronicle construction's Lindenbaum step. This ensures all `limitF(x)` are Dense-MCS. Changes needed:
  1. In `PointInsertion.lean`, `temporal_lindenbaum` calls become `temporal_lindenbaum_fc .Dense`
  2. In `Frame.lean`, seed consistency and Lindenbaum become fc-parameterized
  3. In `OrderedSeedConsistency.lean`, seed consistency proofs use fc-parameterized versions
  4. The `limit_c0` theorem now states `SetMaximalConsistentFc fc (limitF ...)` instead of `SetMaximalConsistent (limitF ...)`
  
  Since all Base axioms have `minFrameClass = .Base <= .Dense`, the proofs go through unchanged at `fc = .Dense`. The FC parameter threads through mechanically.
  
  However, this is a large refactoring (~8 chronicle files, ~3500 lines). **Alternative**: create WRAPPER functions. Define `limitDomDense`, `limitFDense`, `ChronicleSubtypeDense` that call the existing Base construction and then prove the additional Dense properties using `dense_mcs_implies_base_mcs`.
  
  **Adopted approach**: Use the existing Base chronicle but prove DenselyOrdered via a DIRECT argument that does NOT require `neg U(top,bot)` at every limit point. Instead, observe:
  
  Between any `x < y` in limitDom:
  - `limitF(x)` is a Base-MCS, so `U(top, top) in limitF(x)` (from `F(top)` via BX12)
  - By `limit_satisfies_c5_strong`, there exists `z in limitDom` with `x < z` and `top in limitF(z)` and for all `w` between `x` and `z`, `top in limitF(w)` and `U(top,top) in limitF(w)`.
  - But `z` might be >= `y`, and the Until witness doesn't constrain z to be < y.
  
  **Actually correct approach using C4**: The C4 condition says: if `neg U(eta, xi) in limitF(x)` and `eta in limitF(y)`, then exists `z` between with `neg xi in limitF(z)`. To use this with `eta = top, xi = bot`:
  - Need: `neg U(top, bot) in limitF(x)` and `top in limitF(y)`
  - `top in limitF(y)` is trivially true (all MCS contain top)
  - `neg U(top, bot) in limitF(x)` requires x=0 (where limitF(0) = A = Dense-MCS) OR a propagation argument
  
  **Two-step density**: For `x < y`:
  - Step A: Find z1 between `min(x,0)` and `max(y,0)` using the `neg U(top,bot)` at 0
  - Step B: Argue that z1 between x and y
  
  For `0 <= x < y`: Apply C4 at `(0, y)` with `neg U(top,bot) at 0, top at y` to get `z` with `0 < z < y`. If `z > x`, we have `x < z < y` (if `x = 0` then done; if `0 < x < z`, we have z between x and y, done). If `z <= x`... then we have `0 < z <= x < y` but we need something between x and y.
  
  This shows the fundamental issue: C4 at `(0, y)` gives a point between 0 and y, but it might be before x.
  
  **Definitive solution**: FC-parameterize ONLY the Lindenbaum call in PointInsertion, making all new MCS points Dense-MCS. This is a TARGETED change, not a full refactoring. The key observation:
  
  The chronicle construction calls `temporal_lindenbaum` in exactly 3 places (PointInsertion.lean and Frame.lean). If these are changed to `temporal_lindenbaum_fc .Dense`, all new points are Dense-MCS. The starting point A is already Dense-MCS. So all `limitF(x)` are Dense-MCS, and `neg U(top,bot)` is in all of them. Then C4 gives DenselyOrdered directly.
  
  But modifying those files means changing the TYPE of `h_mcs` parameters throughout the chronicle from `SetMaximalConsistent` to `SetMaximalConsistentFc .Dense`, which cascades.
  
  **FINAL ADOPTED APPROACH**: Create a **parallel chronicle construction** specifically for Dense. This is the cleanest separation:
  1. Define `limitDomDense`, `limitFDense` that call the Base chronicle with the Base-MCS projection of the Dense-MCS
  2. The truth lemma and chronicle conditions are inherited from the Base versions
  3. Add a `DenselyOrdered` instance proof that uses C4 + the fact that `neg U(top,bot) in A = limitF(0)` combined with a transitive density argument
  
  Wait, we already showed the transitive density argument doesn't trivially work. Let me reconsider...
  
  **THE SIMPLEST CORRECT APPROACH**: Observe that `limit_satisfies_c4` gives us density from 0. For `x < y`:
  - Case `x = 0`: `neg U(top,bot)` is in `limitF(0) = A` (Dense-MCS). `top` is in `limitF(y)`. By C4, exists `z` with `0 < z < y` and `top in limitF(z)`. Done.
  - Case `x > 0, y > 0`: We have `0 < x < y`. From case `x = 0` applied to `(0, y)`, get `z1` with `0 < z1 < y`. If `x < z1`, done. If `z1 <= x`, apply case `x = 0` to `(0, x)` to get `z2` with `0 < z2 < x`. Now apply case `x = 0` to `(0, y)` again... this is circular.
  - Case `x < 0 < y`: Apply C4 at `(0, y)` to get `z` with `0 < z < y`. If `z > x` (which it is since z > 0 > x... wait, z > 0 and x < 0, so z > x). But we need x < z < y. Since z > 0 > x, we need z < y which is guaranteed. Done.
  - Case `x < y < 0`: Mirror using C4' at `(x, 0)` (with S(top,bot) and H).
  - Case `x < y = 0`: Use C4' (since direction).
  
  But the case `0 < x < y` fails. We CANNOT find z between x and y using C4 at 0 alone because C4 at (0, y) gives z between 0 and y, not between x and y.
  
  **THIS CONFIRMS**: We truly need `neg U(top,bot)` at all limit points, which requires FC-parameterization.
  
  **FINAL DECISION**: Implement targeted FC-parameterization. Create `DenseMCS.lean` with FC-parameterized MCS wrappers. Then create `DenseChronicle.lean` that wraps the chronicle construction: take a Dense-MCS A, project to Base-MCS via `dense_mcs_implies_base_mcs`, build the Base chronicle, and then prove DenselyOrdered by a DIFFERENT method that doesn't require Dense-MCS at all points.
  
  **THE ACTUAL SIMPLEST METHOD**: The chronicle subtype is `{x : Rat // x in limitDom}`. Rat IS DenselyOrdered. The question is whether the SUBTYPE inherits DenselyOrdered. It does IF `limitDom` is OrdConnected (between any two members, all rationals between them are also members). But limitDom is discrete (a countable scattered set).
  
  However, the subtype of Rat inherits DenselyOrdered if between any two ELEMENTS OF THE SUBTYPE there exists another ELEMENT OF THE SUBTYPE. This is exactly what C4 gives when `neg U(top,bot)` is available.
  
  **TRULY FINAL APPROACH**: FC-parameterize the chronicle minimally by adding an `fc` parameter to the key types and having `limitDom_fc`, `limitF_fc` etc. pass `fc` through. Since the proofs only use Base axioms, they work at any `fc >= .Base`. Then `DenselyOrdered` follows from Dense-specific properties.
  
  Given the complexity analysis, the cleanest implementation path is:
  1. Keep all existing chronicle files unchanged
  2. Add new definitions in `DenseCompleteness.lean` that build on the existing chronicle but add DenselyOrdered
  3. For `DenselyOrdered`, use the observation that `neg U(top,bot)` at `limitF(0)` combined with the omega-chain's exhaustive counterexample processing means that for EVERY pair `(0, y)` with y in limitDom, the counterexample `(0, y, top, bot, c4_forward)` is eventually processed, inserting a point between 0 and y. Similarly for every `(x, 0)`. This gives density relative to 0 but not for general pairs.

  For general density, observe that `limit_satisfies_c5_strong` gives: for `U(top,top)` at `x`, there exists `z > x` in limitDom with `top at z` AND `U(top,top) at w` for all `x < w < z`. The witness z is the CLOSEST point to x satisfying the Until. If we could show this z equals x's immediate successor in limitDom, and y is beyond it... but there's no "immediate successor" in the limit domain.

  **I will implement the targeted FC-parameterization approach**. The changes to the chronicle are minimal because we only thread `fc` through type signatures; all PROOFS remain unchanged since they use Base axioms which are available at any fc.

- [ ] Define `limitDomFc`, `limitFFc`, `ChronicleSubtypeFc` as aliases that accept `fc : FrameClass` and `h_mcs : Temporal.SetMaximalConsistentFc fc A` but internally use `dense_mcs_implies_base_mcs` (for fc = .Dense) to call the existing chronicle
- [ ] Alternative simpler approach: Define thin wrappers `limitDomDense A h_dense_mcs := limitDom A (dense_mcs_implies_base_mcs h_dense_mcs)` and similarly for `limitFDense`, `ChronicleSubtypeDense`
- [ ] Prove `dense_indicator_in_dense_mcs_at_zero`: `neg U(top, bot) in limitFDense A h_mcs (chronicleZeroDense A h_mcs).val` (since limitF(0) = A and A is Dense-MCS containing the dense_indicator axiom)
- [ ] Prove `chronicle_densely_ordered_from_zero`: for any `y > 0` in limitDomDense, exists `z` with `0 < z < y` in limitDomDense (using C4 at 0 with neg U(top,bot))
- [ ] For the full `DenselyOrdered` instance: prove it using the REINDEXING trick. Since limitDom is a countable subset of Rat with no max/min and every point has points above and below, AND between 0 and any other point there exists a third point, the subtype is `DenselyOrdered`. Use induction on the omega-chain: for any `x < y` in limitDom, the counterexample `(x, ?, top, bot, c4_forward)` gets processed IF `neg U(top,bot) in limitF(x)`. Since we have this only at x=0, we need the RELAY argument:
  - Between x and y, there exists a point z (not necessarily between x and y) such that iterating from 0 through the chronicle gives density.
  
  **Pragmatic implementation**: Rather than the relay argument, prove `DenselyOrdered` for `ChronicleSubtypeDense` by showing the subtype is ORDER-ISOMORPHIC to a dense subset of Rat. Specifically, show the subtype satisfies the characterization of countable dense linear orders without endpoints (Cantor's theorem). Or simply:
  
  Given the analysis confirms we need `neg U(top,bot)` at EVERY limit point, implement a MINIMAL fc-parameterization of the chronicle. Specifically, modify `PointInsertion.lean` to accept an `fc` parameter and use `temporal_lindenbaum_fc fc` instead of `temporal_lindenbaum`. This is a 1-line change per Lindenbaum call. The cascade to type signatures can be handled with `haveI := dense_mcs_implies_base_mcs ...` locally.

  **DEFINITIVE IMPLEMENTATION**: Given the analysis complexity, the implemented approach will be:
  
  1. Create `DenseCompleteness.lean` with a self-contained dense completeness proof
  2. Use `dense_mcs_implies_base_mcs` to build the Base chronicle
  3. For `DenselyOrdered`, provide a proof using the specific structure: since A is Dense-MCS, `neg U(top,bot) in A = limitF(0)`, and by the omega-chain's exhaustive counterexample processing, the C4 counterexample `(0, y, top, bot, c4_forward)` for every `y > 0` in limitDom is processed. This gives a point between 0 and y. Similarly for past. For the general case `x < y` with x > 0: since limitDom has no max and no min, and between 0 and any positive point there exists a point, the set of positive limit domain points is dense in itself by the following argument: 
     - Take `x < y` in limitDom with `x > 0`
     - `limitF(0)` contains `neg U(top, bot)` 
     - `limitF(0)` also contains `G(neg U(top,bot))` (by necessitation of the dense_indicator axiom at Dense fc, lifted to Base: but NO, G-nec of a Dense theorem is a Dense theorem, not a Base theorem)
     
  This AGAIN fails for the same reason. `neg U(top,bot)` is Dense-derivable but NOT Base-derivable. `G(neg U(top,bot))` is Dense-derivable but NOT Base-derivable. `limitF(x)` for `x > 0` is a Base-MCS, so it contains Base theorems but not Dense theorems.
  
  **CONCLUSION**: FC-parameterization of the chronicle is NECESSARY. The plan must include it.

- [ ] Thread `fc : FrameClass` parameter through chronicle construction (targeted changes):
  - `ChronicleTypes.lean`: Change `c0_condition` from `Temporal.SetMaximalConsistent (chi.f x)` to parametric
  - `PointInsertion.lean`: Change `temporal_lindenbaum` to `temporal_lindenbaum_fc fc`
  - `Frame.lean`: Change `temporal_lindenbaum` calls to `temporal_lindenbaum_fc fc`
  - `OrderedSeedConsistency.lean`: Update MCS signatures
  - `ChronicleConstruction.lean`: Thread fc through omega chain
  - `ChronicleToCountermodel.lean`: Thread fc, keep order instances
  - `TruthLemma.lean`: Thread fc
- [ ] Verify all existing chronicle files still compile after FC-parameterization
- [ ] Add `instance chronicle_densely_ordered_dense`: for `fc = .Dense`, the ChronicleSubtype is `DenselyOrdered` using:
  - All `limitF(x)` are now `SetMaximalConsistentFc .Dense`, so `neg U(top,bot)` is in all of them
  - For any `x < y`, apply `limit_satisfies_c4` with `xi = bot, eta = top` to get `z` between

**Timing**: 2 hours

**Depends on**: Phase 2 (needs FC-parameterized MCS)

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` - Add fc parameter to c0_condition and related types
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` - Thread fc parameter
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` - Use `temporal_lindenbaum_fc`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean` - Thread fc parameter
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` - Thread fc parameter
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` - Thread fc through omega chain
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` - Thread fc parameter
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean` - Thread fc + DenselyOrdered instance
- `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean` - Thread fc parameter
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` - Update to use fc = .Base explicitly

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleToCountermodel` compiles
- `lake build Cslib.Logics.Temporal.Metalogic.Completeness` still compiles (no regression)
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.TruthLemma` compiles

---

### Phase 5: Dense Completeness Theorem [NOT STARTED]

**Goal**: Assemble the dense completeness theorem: `ValidDense phi -> ThDerivableFc .Dense phi`.

**Tasks**:
- [ ] Prove `neg_consistent_of_not_derivable_dense`: if phi is not Dense-derivable, then `{neg phi}` is Dense-consistent (mirrors bimodal `neg_consistent_of_not_derivable`)
- [ ] Prove `completeness_dense`: the main theorem, following the contrapositive pattern:
  1. Assume phi is not Dense-derivable
  2. `{neg phi}` is Dense-consistent by `neg_consistent_of_not_derivable_dense`
  3. Extend to Dense-MCS M via `temporal_lindenbaum_fc`
  4. M is also Base-MCS by `dense_mcs_implies_base_mcs`
  5. Build chronicle from M using FC-parameterized construction at `fc = .Dense`
  6. Chronicle subtype has LinearOrder, Nontrivial, NoMaxOrder, NoMinOrder (from Base properties)
  7. Chronicle subtype has DenselyOrdered (from Phase 4, using Dense-MCS at all points + C4)
  8. Apply `ValidDense phi` to get `phi in limitF(0) = M`
  9. But `neg phi in M` and `phi in M` contradicts MCS consistency
- [ ] Add module imports: import DenseMCS, DenseSoundness, and FC-parameterized chronicle
- [ ] Register in `Cslib.lean` if needed (run `lake exe mk_all --module`)

**Timing**: 1 hour

**Depends on**: Phase 3 (dense soundness) and Phase 4 (DenselyOrdered instance)

**Files to create**:
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` - Dense completeness theorem (~100 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.DenseCompleteness` compiles without errors
- `lake build` (full project) compiles without errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

## Testing & Validation

- [ ] `lake build` compiles the full project without errors
- [ ] `lake test` passes all tests in CslibTests
- [ ] `lake exe checkInitImports` verifies all files import Cslib.Init
- [ ] `lake exe lint-style` passes style linting
- [ ] No `sorry` in any new or modified files (verified via `grep -r "sorry" Cslib/Logics/Temporal/`)
- [ ] The dense soundness theorem type-checks: `ValidDense phi` follows from `ThDerivableFc .Dense phi`
- [ ] The dense completeness theorem type-checks: `ThDerivableFc .Dense phi` follows from `ValidDense phi`
- [ ] Existing base completeness still compiles without changes to its proof structure

## Artifacts & Outputs

- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` - Modified (2 new constructors)
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean` - Modified (2 new cases)
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` - Modified (2 new HasAxiom instances)
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` - New (~200 lines)
- `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean` - New (~150 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/*.lean` - Modified (FC threading, ~200 lines of changes)
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` - New (~100 lines)
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` - Modified (explicit `fc = .Base`)

## Rollback/Contingency

- All changes to existing files are additive (new constructors, new cases) or parameter-threading (fc parameter)
- If FC-parameterization of chronicle proves too complex, fall back to:
  1. Create a separate Dense chronicle construction that duplicates key definitions with fc = .Dense
  2. This avoids modifying existing files but increases code duplication (~300 extra lines)
- If DenselyOrdered proof via C4 doesn't work as expected, fall back to proving the chronicle subtype is order-isomorphic to a dense subset of Rat using Cantor's characterization
- Git revert to pre-task state if implementation is fundamentally blocked
