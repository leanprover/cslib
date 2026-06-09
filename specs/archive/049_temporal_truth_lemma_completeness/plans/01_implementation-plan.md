# Implementation Plan: Task #49

- **Task**: 49 - Temporal truth lemma and completeness assembly
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: Tasks 46, 47, 48 (chronicle infrastructure, all completed)
- **Research Inputs**: specs/049_temporal_truth_lemma_completeness/reports/01_research-report.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Build a countermodel from the chronicle limit construction and prove the truth lemma connecting `Satisfies` to MCS membership, then close the single `sorry` at line 416 of `Completeness.lean`. The approach uses `limit_dom` as a subtype of `Rat` for the model domain D, which inherits `LinearOrder` from `Rat` and needs only `Nontrivial`, `NoMaxOrder`, and `NoMinOrder` -- all derivable from seriality axioms and `limit_F_resolution`/`limit_P_resolution`. The truth lemma proceeds by structural induction on all 5 formula constructors (atom, bot, imp, untl, snce), using `limit_satisfies_c5_strong`/`limit_satisfies_c5'_strong` for the Until/Since forward direction and `limit_satisfies_c4`/`limit_satisfies_c4'` for the backward direction. No Cantor isomorphism or density argument is needed.

### Research Integration

Key findings from the research report (01_research-report.md):
- The sorry at line 416 needs a countermodel from the chronicle limit; the existing comment block (lines 405-415) describes a Z-indexed chain approach that is now superseded by the chronicle construction
- Countermodel domain: `D := {x : Rat // x in limit_dom A h_mcs}` inherits LinearOrder automatically
- `Nontrivial` from `zero_mem_limit_dom` + `limit_F_resolution` (F(top) in every MCS)
- `NoMaxOrder`/`NoMinOrder` from seriality axioms (`mcs_f_top_mem`/`mcs_p_top_mem`) + `limit_F_resolution`/`limit_P_resolution`
- Truth lemma Until forward: `limit_satisfies_c5_strong` gives witness y with guard in `limit_g`, which by definition means all intermediate limit_dom points satisfy the guard -- exactly what the subtype D quantifiers require
- Truth lemma Until backward: by contradiction using `limit_satisfies_c4` to find an intermediate point z with `psi.neg in f(z)`, contradicting IH
- `[Denumerable (Formula Atom)]` must be added to the completeness theorem signature
- `t_le_refl` sorry in Frame.lean is unrelated and should not be touched
- No circular import risk: TruthLemma.lean imports ChronicleConstruction.lean (not Frame.lean or Completeness.lean)
- Bimodal TruthLemma.lean (223 lines) provides ~70% structural transfer for case structure; ChronicleToCountermodel*.lean provides 0% transfer (bimodal-specific pipeline)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task is the final step in the Temporal Logic completeness chain (tasks 46-49 from task 31 expansion). Completing task 49 removes the last `sorry` from the temporal completeness theorem, which is a major milestone in the ROADMAP.

## Goals & Non-Goals

**Goals**:
- Create `ChronicleToCountermodel.lean` with the model type, order instances, and TemporalModel definition
- Create `TruthLemma.lean` with the truth lemma for all 5 formula constructors
- Close the `sorry` in `Completeness.lean` by importing and applying the countermodel construction
- Add `[Denumerable (Formula Atom)]` to the completeness theorem signature
- Achieve `lake build` with zero sorries on the completeness path

**Non-Goals**:
- Fix the `t_le_refl` sorry in `Frame.lean` (unrelated to completeness)
- Refactor or clean up existing `CanonicalWorld`/`canonical_acc` infrastructure in `Completeness.lean` (it remains valid for G/H truth lemma helpers)
- Build a Cantor isomorphism or density argument
- Abstract shared logic between bimodal and temporal completeness

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Until backward case requires careful IH application at intermediate point z | M | M | z is in limit_dom by C4, so it is a valid subtype element; IH applies directly |
| Heartbeat limits on truth lemma induction | M | M | Use `set_option maxHeartbeats` and break into per-case helper lemmas if needed |
| Universe level mismatch on subtype D | L | L | `{x : Rat // x in limit_dom A h_mcs}` lives in Type, matching ValidSerial D requirement |
| Circular imports | L | L | TruthLemma imports ChronicleConstruction (not Frame.lean/Completeness.lean); Completeness imports ChronicleToCountermodel at the end of the import chain |
| Subtype coercion friction (t.val vs t) | M | M | Define helper lemmas early for `t.val` membership and ordering conversion |
| Formula.neg unfolding issues | M | L | Use `mcs_mem_iff_neg_not_mem` and explicit negation lemmas from MCS.lean |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: ChronicleToCountermodel.lean [COMPLETED]

**Goal**: Build the countermodel infrastructure -- define the subtype D, prove LinearOrder/Nontrivial/NoMaxOrder/NoMinOrder instances, and define the TemporalModel.

**Tasks**:
- [ ] Create file `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean`
- [ ] Add imports: `ChronicleConstruction`, `Satisfies`, `MCS` (for helper lemmas)
- [ ] Define `ChronicleSubtype A h_mcs := {x : Rat // x in limit_dom A h_mcs}` (or use inline subtype)
- [ ] Prove `LinearOrder` instance on the subtype (inherited from Rat via `Subtype.instLinearOrder` or similar)
- [ ] Prove `Nontrivial` instance: use `zero_mem_limit_dom` to get point 0, then `mcs_f_top_mem` to get `F(top) in limit_f(0)`, then `limit_F_resolution` to get a second point y > 0 in limit_dom
- [ ] Prove `NoMaxOrder` instance: for any `t : ChronicleSubtype`, show `F(top) in limit_f(t.val)` (since limit_c0 gives MCS, and mcs_f_top_mem gives F(top) in every MCS), then `limit_F_resolution` gives y > t.val in limit_dom
- [ ] Prove `NoMinOrder` instance: mirror using `mcs_p_top_mem` and `limit_P_resolution`
- [ ] Define `chronicle_valuation A h_mcs : ChronicleSubtype -> Atom -> Prop := fun t p => Formula.atom p in limit_f A h_mcs t.val`
- [ ] Define `chronicle_model A h_mcs : TemporalModel ChronicleSubtype Atom` using the valuation

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean` - new file (~100-200 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleToCountermodel` succeeds with no errors
- All four typeclass instances (LinearOrder, Nontrivial, NoMaxOrder, NoMinOrder) compile without sorry
- `chronicle_model` has type `TemporalModel ChronicleSubtype Atom`

---

### Phase 2: TruthLemma.lean [COMPLETED]

**Goal**: Prove the truth lemma: `Satisfies (chronicle_model A h_mcs) t phi <-> phi in limit_f A h_mcs t.val` for all `t : ChronicleSubtype` and all `phi : Formula Atom`, by structural induction on phi.

**Tasks**:
- [ ] Create file `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean`
- [ ] Add imports: `ChronicleToCountermodel`, `ChronicleConstruction` (for limit_* theorems)
- [ ] Define helper for subtype ordering: `chronicle_lt_iff` converting `t < s` (subtype) to `t.val < s.val`
- [ ] Prove atom case: `Satisfies M t (atom p) <-> M.valuation t p <-> (atom p) in limit_f(t.val)` by definition
- [ ] Prove bot case: `Satisfies M t bot <-> False` and `bot not_in limit_f(t.val)` by `mcs_bot_not_mem` + `limit_c0`
- [ ] Prove imp case: by IH + `temporal_implication_property` + `mcs_neg_of_not_mem`/`mcs_mem_iff_neg_not_mem`
- [ ] Prove untl forward direction: assume `untl phi psi in limit_f(t.val)`, use `limit_satisfies_c5_strong` to get witness y with event phi and guard psi in limit_g; convert y to subtype element; apply IH
- [ ] Prove untl backward direction: assume `exists s : D, t < s /\ Satisfies M s phi /\ forall r between, Satisfies M r psi`; by IH get `phi in f(s.val)` and guard condition; by contradiction assume `untl phi psi not_in f(t.val)`, so `neg(untl phi psi) in f(t.val)`; use `limit_satisfies_c4` to get z between t and s with `psi.neg in f(z.val)`; z is in limit_dom so it is a valid subtype element; by hypothesis `Satisfies M z psi`, by IH `psi in f(z.val)`, contradicting consistency
- [ ] Prove snce case: mirror of untl using `limit_satisfies_c5'_strong` and `limit_satisfies_c4'`
- [ ] Assemble truth lemma theorem: `chronicle_truth_lemma` combining all 5 cases via structural induction (`fun phi => match phi with ...` or `induction phi`)

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean` - new file (~300-500 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.TruthLemma` succeeds with no errors
- `chronicle_truth_lemma` has the expected iff type with no sorry
- All 5 formula cases (atom, bot, imp, untl, snce) are proved

---

### Phase 3: Close the Sorry in Completeness.lean [COMPLETED]

**Goal**: Replace the `sorry` at line 416 of `Completeness.lean` with the actual proof using `chronicle_model_exists` and the truth lemma, and add `[Denumerable (Formula Atom)]` to the theorem signature.

**Tasks**:
- [ ] Add import `Cslib.Logics.Temporal.Metalogic.Chronicle.TruthLemma` to `Completeness.lean`
- [ ] Add `[Denumerable (Formula Atom)]` variable or typeclass assumption to the `completeness` theorem (the chronicle construction requires countability of formulas)
- [ ] Remove the Z-chain comment block (lines 405-415) and the `sorry`
- [ ] Insert the proof body:
  1. Apply chronicle limit construction to M (via `limit_dom`, `limit_f`, etc., or via a wrapper from ChronicleToCountermodel)
  2. Build `chronicle_model` on the subtype D
  3. The subtype has `LinearOrder`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder` (from Phase 1)
  4. Apply `h_valid D chronicle_model (zero_point)` to get `Satisfies chronicle_model 0 phi`
  5. By `chronicle_truth_lemma`, `phi in limit_f(0) = M`
  6. Contradiction with `h_phi_not_M`
- [ ] Verify no other sorries remain in Completeness.lean
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Completeness` to verify

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` - modify (~20-30 lines changed)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Completeness` succeeds with no errors
- `grep -r "sorry" Cslib/Logics/Temporal/Metalogic/Completeness.lean` returns nothing
- The completeness theorem type-checks with the new `[Denumerable (Formula Atom)]` constraint
- Full `lake build` succeeds (no regressions from the new import chain)

## Testing & Validation

- [ ] `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleToCountermodel` compiles clean
- [ ] `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.TruthLemma` compiles clean
- [ ] `lake build Cslib.Logics.Temporal.Metalogic.Completeness` compiles clean with no sorry
- [ ] No circular imports: verify that TruthLemma.lean does NOT import Frame.lean or Completeness.lean
- [ ] `lean_verify` on `completeness` theorem confirms no sorry axioms used
- [ ] Full `lake build` succeeds with no regressions

## Artifacts & Outputs

- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean` - new file (~100-200 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean` - new file (~300-500 lines)
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` - modified (sorry removed, import added, Denumerable constraint added)

## Rollback/Contingency

If the truth lemma proof encounters an unexpected obstacle (e.g., the Until backward case requires infrastructure not available in ChronicleConstruction.lean):

1. Revert Completeness.lean changes via `git checkout -- Cslib/Logics/Temporal/Metalogic/Completeness.lean`
2. Keep new files (TruthLemma.lean, ChronicleToCountermodel.lean) with sorry at the stuck point
3. Mark the plan as [PARTIAL] and document which case/step is blocked
4. The existing sorry in Completeness.lean remains functional

If heartbeat limits are hit:
- Extract individual cases (atom, bot, imp, untl, snce) into separate helper theorems
- Increase `maxHeartbeats` selectively for the induction theorem
- Break the untl/snce proofs into forward/backward helper lemmas
