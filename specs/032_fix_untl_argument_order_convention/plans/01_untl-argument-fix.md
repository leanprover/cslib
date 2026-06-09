# Implementation Plan: Fix untl/snce Argument Order Convention

- **Task**: 32 - Fix untl/snce argument order to match standard literature convention
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: Tasks 22 (Temporal Infrastructure), 3 (Bimodal Semantics) -- both completed
- **Research Inputs**: specs/032_fix_untl_argument_order_convention/reports/01_untl-argument-order.md
- **Artifacts**: plans/01_untl-argument-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Fix the argument order convention for `untl` (Until) and `snce` (Since) operators across cslib to match Burgess 1982 and the BimodalLogic source. Currently, `truth_at` interprets `untl phi psi` with phi=GUARD (holds continuously) and psi=EVENT (holds at witness). The target convention is `untl phi psi` with phi=EVENT (holds at witness) and psi=GUARD (holds continuously). This is a semantic argument swap, not a constructor signature change. The mismatch causes axiom BX12 to be provably unsound (and at least 5 others likely unsound). Approximately 7 files need changes across Temporal and Bimodal modules, plus re-verification of derived theorem proofs.

### Research Integration

Research report `01_untl-argument-order.md` provided:
- Complete file-by-file change list with specific line numbers
- Semantic analysis of each axiom under old and new conventions
- Identification of 5 risk areas (complexity pattern matching, proof validity, BX12 triviality, nested axiom consistency, abbreviation-referenced proofs)
- Confirmation that embedding files and subformula files need no changes
- Dependency-ordered implementation sequence

### Prior Plan Reference

A prior plan (v1) existed with the same 6-phase sequential structure. Source code review confirms its analysis is sound. This revision refines the change lists based on verified line numbers from current source code, and provides more precise guidance for Phase 5 proof re-derivation (the highest-risk phase).

### Roadmap Alignment

This task is a Wave 1 blocker for downstream temporal/bimodal work (tasks 4, 5, 6, 23, 31). Completing it unblocks the entire temporal logic and bimodal porting pipeline.

## Goals & Non-Goals

**Goals**:
- Swap `untl`/`snce` semantics in `truth_at` so arg1=EVENT, arg2=GUARD
- Update all derived operators (`some_future`, `some_past`, `next`, `prev`, `release`, `trigger`, `strong_release`, `strong_trigger`) in both Temporal and Bimodal Formula files
- Update all complexity function pattern-matching arms
- Update all 16 temporal axiom abbreviations in `Axioms.lean`
- Update `tempNec`/`tempNecPast` in `ProofSystem.lean`
- Update all axiom constructors in Temporal `ProofSystem/Axioms.lean`
- Re-verify/fix all proofs in `TemporalDerived.lean`
- Achieve clean `lake build` with zero errors

**Non-Goals**:
- Changing the `untl`/`snce` constructor signatures (they remain `F -> F -> F`)
- Modifying the embedding (`TemporalEmbedding.lean`) or subformula files (structurally symmetric)
- Adding new axioms or theorems beyond what exists
- Resolving BX12/BX12' triviality (note in comments; may need separate Burgess verification)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Complexity pattern-matching arms silently wrong | H | H | Manually verify each pattern against new derived operator expansions; test with `lake build` after Phase 2 |
| TemporalDerived proofs invalid after convention change | H | H | Re-derive proofs using lean_goal/lean_multi_attempt; F_mono likely needs BX3 instead of BX2G |
| BX12/BX12' become trivial tautologies (F(p)->F(p)) | M | H | Document as known issue; verify against Burgess 1982 in follow-up |
| Nested axiom args (BX5/BX6/BX7/BX13) swapped incorrectly | H | M | Trace each nested `untl`/`snce` call against research report analysis |
| Truth.lean proofs break after semantic swap | M | M | The proof structure is symmetric (phi/psi swap preserves proof shapes); build after Phase 1 to confirm |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases are strictly sequential because each layer builds on the previous convention change.

---

### Phase 1: Semantic Root Fix (Truth.lean) [COMPLETED]

**Goal**: Swap the semantic interpretation of `untl`/`snce` arguments in the truth evaluation so that arg1=EVENT (holds at witness time) and arg2=GUARD (holds continuously in interval).

**Tasks**:
- [ ] Update the `truth_at` docstring (line 51-52) to reflect new convention:
  - Change `Until U(phi,psi): exists s > t, phi(s) AND forall r in (t,s), psi(r)` to indicate phi=event, psi=guard
  - Change `Since S(phi,psi): exists s < t, phi(s) AND forall r in (s,t), psi(r)` similarly
- [ ] Swap phi/psi roles in the `Formula.untl` branch (lines 64-66):
  - Current: `exists s, t < s AND truth_at ... s psi AND forall r, ... truth_at ... r phi`
  - Target: `exists s, t < s AND truth_at ... s phi AND forall r, ... truth_at ... r psi`
  - This means: swap `ψ` and `φ` in the `truth_at` calls (witness gets `φ`, interval gets `ψ`)
- [ ] Swap phi/psi roles in the `Formula.snce` branch (lines 67-69): same swap pattern
- [ ] Run `lake build Cslib.Logics.Bimodal.Semantics.Truth` -- expect downstream failures in theorems that use `some_future_iff` etc., since those depend on derived ops not yet updated

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Semantics/Truth.lean` - Swap phi/psi in untl and snce branches of truth_at (lines 64-69); update docstring (lines 51-52)

**Verification**:
- `lake build Cslib.Logics.Bimodal.Semantics.Truth` compiles (the truth_at function itself will compile since the swap is type-correct; downstream theorems in the same file may fail until Phase 2)
- Manual inspection confirms arg1 position is now the EVENT (existential witness) and arg2 is the GUARD (universal interval)

---

### Phase 2: Syntax Layer (both Formula.lean files) [COMPLETED]

**Goal**: Update all derived temporal operator definitions and complexity function patterns in both Temporal and Bimodal Formula files to reflect the new `untl(event, guard)` convention.

**Tasks**:

**Temporal Formula.lean** (`Cslib/Logics/Temporal/Syntax/Formula.lean`):
- [ ] Update `some_future` (line 63-64): `.untl .top φ` -> `.untl φ .top`
- [ ] Update `some_past` (line 71-72): `.snce .top φ` -> `.snce φ .top`
- [ ] Update `next` (line 366): `.untl .bot φ` -> `.untl φ .bot`
- [ ] Update `prev` (line 370): `.snce .bot φ` -> `.snce φ .bot`
- [ ] Update `release` (lines 391-392): `.untl (Formula.neg φ) (Formula.neg ψ)` -> `.untl (Formula.neg ψ) (Formula.neg φ)` (Release R(phi,psi) = neg(untl(neg psi, neg phi)) -- neg psi is EVENT, neg phi is GUARD)
- [ ] Update `trigger` (lines 395-396): `.snce (Formula.neg φ) (Formula.neg ψ)` -> `.snce (Formula.neg ψ) (Formula.neg φ)`
- [ ] Update `strong_release` (lines 407-408): `.untl ψ (Formula.and ψ φ)` -> `.untl (Formula.and ψ φ) ψ` (and(psi,phi) is EVENT, psi is GUARD)
- [ ] Update `strong_trigger` (lines 411-412): `.snce ψ (Formula.and ψ φ)` -> `.snce (Formula.and ψ φ) ψ`
- [ ] Update complexity function patterns (lines 308-334):
  - G(phi) pattern (line 312): `.imp (.untl (.imp .bot .bot) (.imp φ .bot)) .bot` -> `.imp (.untl (.imp φ .bot) (.imp .bot .bot)) .bot`
  - H(phi) pattern (line 314): `.imp (.snce (.imp .bot .bot) (.imp φ .bot)) .bot` -> `.imp (.snce (.imp φ .bot) (.imp .bot .bot)) .bot`
  - R(phi,psi) pattern (lines 316-317): `.imp (.untl (.imp φ .bot) (.imp ψ .bot)) .bot` -> `.imp (.untl (.imp ψ .bot) (.imp φ .bot)) .bot`
  - T(phi,psi) pattern (lines 319-320): `.imp (.snce (.imp φ .bot) (.imp ψ .bot)) .bot` -> `.imp (.snce (.imp ψ .bot) (.imp φ .bot)) .bot`
  - next(phi) pattern (line 324): `.untl .bot φ` -> `.untl φ .bot`
  - F(phi) pattern (line 326): `.untl (.imp .bot .bot) φ` -> `.untl φ (.imp .bot .bot)`
  - prev(phi) pattern (line 330): `.snce .bot φ` -> `.snce φ .bot`
  - P(phi) pattern (line 332): `.snce (.imp .bot .bot) φ` -> `.snce φ (.imp .bot .bot)`
- [ ] Update module-level docstring (lines 22-27) to reflect new convention: `F phi = phi U top`, `P phi = phi S top`

**Bimodal Formula.lean** (`Cslib/Logics/Bimodal/Syntax/Formula.lean`):
- [ ] Update `some_future` (line 65-66): `.untl .top φ` -> `.untl φ .top`
- [ ] Update `some_past` (line 73-74): `.snce .top φ` -> `.snce φ .top`

- [ ] Run `lake build Cslib.Logics.Temporal.Syntax.Formula` and `lake build Cslib.Logics.Bimodal.Syntax.Formula` to verify

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Swap args in 8 derived operators + update 8 complexity patterns + update docstrings
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` - Swap args in `some_future` and `some_past`

**Verification**:
- Both Formula modules compile cleanly
- Spot-check: `some_future φ` unfolds to `untl φ top` (phi=event in arg1)
- Spot-check: complexity of `G(φ)` still returns `1 + complexity φ` (pattern matches correctly)
- Run `lake build Cslib.Logics.Bimodal.Semantics.Truth` to verify Truth.lean now compiles end-to-end (since derived ops match semantics)

---

### Phase 3: Foundation Axioms and ProofSystem [COMPLETED]

**Goal**: Update all 16 temporal axiom abbreviations in `Axioms.lean`, the interaction axiom `ModalFuture`, and the temporal necessitation rules in `ProofSystem.lean` to use the new convention.

**Tasks**:

**Axioms.lean** (`Cslib/Foundations/Logic/Axioms.lean`):
- [ ] BX1 `SerialFuture` (lines 111-113): Both args are `top`, symmetric -- no change needed
- [ ] BX1' `SerialPast` (lines 117-119): Symmetric -- no change needed
- [ ] BX2G `LeftMonoUntilG` (lines 124-129): Swap `G_imp` from `HasUntil.untl top (neg ...)` to `HasUntil.untl (neg ...) top` (line 127). Keep `untl ψ φ` and `untl ψ χ` as-is (line 129) since the structure `untl(guard, event)` -> `untl(event, guard)` means the variable names now refer to different semantic roles but the axiom pattern is preserved
- [ ] BX2H `LeftMonoSinceH` (lines 134-139): Swap `H_imp` from `HasSince.snce top (neg ...)` to `HasSince.snce (neg ...) top` (line 137)
- [ ] BX3 `RightMonoUntil` (lines 144-149): Swap `G_imp` (line 147) same as BX2G
- [ ] BX3' `RightMonoSince` (lines 154-159): Swap `H_imp` (line 157) same as BX2H
- [ ] BX4 `ConnectFuture` (lines 163-168): Swap `P_φ` from `snce top φ` to `snce φ top` (line 166); swap `G_P_φ` from `untl top (neg P_φ)` to `untl (neg P_φ) top` (line 167)
- [ ] BX4' `ConnectPast` (lines 172-177): Swap `F_φ` from `untl top φ` to `untl φ top` (line 175); swap `H_F_φ` from `snce top (neg F_φ)` to `snce (neg F_φ) top` (line 176)
- [ ] BX13 `EnrichmentUntil` (lines 182-186): Swap `untl ψ φ` to keep axiom structure but swap `snce p φ` to `snce φ p`... actually all `untl`/`snce` calls here need review against the axiom's intended meaning. The key: `HasUntil.untl ψ φ` stays as-is (args are variables, semantics changes), but `HasSince.snce p φ` stays as-is too (same reasoning). No arg-position changes needed since these are variable-named args whose semantic interpretation changes with the convention
- [ ] BX13' `EnrichmentSince` (lines 190-194): Same analysis
- [ ] BX5 `SelfAccumUntil` (lines 198-202): No arg-position changes (uses `untl ψ φ` with variables)
- [ ] BX5' `SelfAccumSince` (lines 206-210): No arg-position changes
- [ ] BX6 `AbsorbUntil` (lines 214-218): No arg-position changes
- [ ] BX6' `AbsorbSince` (lines 222-226): No arg-position changes
- [ ] BX7 `LinearUntil` (lines 230-237): No arg-position changes
- [ ] BX7' `LinearSince` (lines 241-248): No arg-position changes
- [ ] BX10 `UntilF` (lines 253-255): Swap F(ψ) encoding from `HasUntil.untl top ψ` to `HasUntil.untl ψ top` (line 255)
- [ ] BX10' `SinceP` (lines 260-262): Swap P(ψ) encoding from `HasSince.snce top ψ` to `HasSince.snce ψ top` (line 262)
- [ ] BX11 `TempLinearity` (lines 266-275): Swap `F'` definition from `HasUntil.untl top x` to `HasUntil.untl x top` (line 271)
- [ ] BX11' `TempLinearityPast` (lines 279-288): Swap `P'` definition from `HasSince.snce top x` to `HasSince.snce x top` (line 284)
- [ ] BX12 `FUntilEquiv` (lines 293-295): Swap F(φ) from `HasUntil.untl top φ` to `HasUntil.untl φ top`; note: `HasUntil.untl φ top` is now both F(φ) and the RHS, making this `F(φ) -> F(φ)` (trivially valid)
- [ ] BX12' `PSinceEquiv` (lines 299-301): Symmetric swap
- [ ] `ModalFuture` (lines 313-317): Swap G_φ encoding from `HasUntil.untl top neg_φ` to `HasUntil.untl neg_φ top` (line 316)

**ProofSystem.lean** (`Cslib/Foundations/Logic/ProofSystem.lean`):
- [ ] `tempNec` (lines 82-84): Swap `HasUntil.untl (HasImp.imp (HasBot.bot : F) HasBot.bot) (HasImp.imp φ HasBot.bot)` to `HasUntil.untl (HasImp.imp φ HasBot.bot) (HasImp.imp (HasBot.bot : F) HasBot.bot)`
- [ ] `tempNecPast` (lines 90-92): Swap `HasSince.snce (HasImp.imp (HasBot.bot : F) HasBot.bot) (HasImp.imp φ HasBot.bot)` to `HasSince.snce (HasImp.imp φ HasBot.bot) (HasImp.imp (HasBot.bot : F) HasBot.bot)`

- [ ] Run `lake build Cslib.Foundations.Logic.Axioms` and `lake build Cslib.Foundations.Logic.ProofSystem` to verify

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/Axioms.lean` - Swap args in F/G/P/H encodings within axiom abbreviations; variable-only `untl`/`snce` calls stay as-is
- `Cslib/Foundations/Logic/ProofSystem.lean` - Swap args in `tempNec` and `tempNecPast`

**Verification**:
- Both modules compile cleanly
- Spot-check: BX4 `ConnectFuture` encodes `φ → G(P(φ))` correctly with new F/G/P encodings
- Spot-check: BX10 `UntilF` encodes `U(ψ,φ) → F(ψ)` where F(ψ) = `untl(ψ,top)`

---

### Phase 4: Temporal Proof System Axiom Constructors [COMPLETED]

**Goal**: Update all axiom constructors in the Temporal proof system to match the new convention. Many of these use `Formula.some_future`, `Formula.some_past`, `Formula.all_future`, `Formula.all_past` which will auto-update from Phase 2. Direct `Formula.untl`/`Formula.snce` calls with explicit args need manual checking.

**Tasks**:
- [ ] `serial_future` (line 89): Uses `Formula.some_future` -- auto-updates via Phase 2. Verify.
- [ ] `serial_past` (line 93): Uses `Formula.some_past` -- auto-updates. Verify.
- [ ] `left_mono_until_G` (lines 97-98): Uses `Formula.untl ψ φ` and `all_future`. The `all_future` auto-updates. The direct `untl ψ φ` stays (variable-named). But verify the formula matches `Axioms.LeftMonoUntilG` after Phase 3 changes.
- [ ] `left_mono_since_H` (lines 102-103): Symmetric. Verify.
- [ ] `right_mono_until` (lines 107-108): Uses `Formula.untl φ χ` and `Formula.untl ψ χ`. Variable-named, stays. Verify matches `Axioms.RightMonoUntil`.
- [ ] `right_mono_since` (lines 112-113): Symmetric. Verify.
- [ ] `connect_future` (lines 116-117): Uses `some_past` and `all_future` -- auto-updates. Verify.
- [ ] `connect_past` (lines 120-121): Uses `some_future` and `all_past` -- auto-updates. Verify.
- [ ] `enrichment_until` (lines 125-127): Direct `Formula.untl` and `Formula.snce` with variable args. Stays as-is. Verify matches abbreviation.
- [ ] `enrichment_since` (lines 131-133): Symmetric. Verify.
- [ ] `self_accum_until` (lines 137-139): Direct `Formula.untl`. Stays. Verify.
- [ ] `self_accum_since` (lines 143-145): Symmetric. Verify.
- [ ] `absorb_until` (lines 149-150): Stays. Verify.
- [ ] `absorb_since` (lines 154-155): Stays. Verify.
- [ ] `linear_until` (lines 159-165): All `Formula.untl` with variables. Stays. Verify.
- [ ] `linear_since` (lines 169-175): Stays. Verify.
- [ ] `until_F` (lines 178-179): Uses `Formula.some_future` -- auto-updates. Verify.
- [ ] `since_P` (lines 182-183): Uses `Formula.some_past` -- auto-updates. Verify.
- [ ] `temp_linearity` (lines 187-191): Uses `Formula.some_future` -- auto-updates. Verify.
- [ ] `temp_linearity_past` (lines 195-199): Uses `Formula.some_past` -- auto-updates. Verify.
- [ ] `F_until_equiv` (lines 202-203): Uses `Formula.some_future` and `Formula.untl φ Formula.top`. `some_future` auto-updates. But `Formula.untl φ Formula.top` -- with new convention, this is U(φ, ⊤) which means "φ is EVENT, ⊤ is GUARD" = ∃s>t, φ(s) ∧ ∀r: ⊤ = F(φ). So both sides become F(φ) -> F(φ). This is correct. Verify.
- [ ] `P_since_equiv` (lines 206-207): Symmetric. Verify.
- [ ] Run `lake build Cslib.Logics.Temporal.ProofSystem.Axioms` to verify

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` - Primarily verification that auto-updated derived ops produce correct formulas; fix any direct `untl`/`snce` calls that don't match

**Verification**:
- Module compiles cleanly
- Each axiom constructor type-checks against its corresponding abbreviation in `Axioms.lean`
- No mismatched argument positions

---

### Phase 5: Derived Theorems (TemporalDerived.lean) [COMPLETED]

**Goal**: Update private abbreviations and re-verify/fix all derived theorem proofs that may break under the new convention.

**Tasks**:
- [ ] Update convention comment (lines 15-17): Change to reflect new convention or delete the discrepancy note
- [ ] Update `someFuture` abbreviation (line 39): `HasUntil.untl top' φ` -> `HasUntil.untl φ top'`
- [ ] Update `somePast` abbreviation (line 41): `HasSince.snce top' φ` -> `HasSince.snce φ top'`
- [ ] Re-verify `F_mono` (lines 95-99): **Critical change needed.** With new convention, `someFuture φ = untl(φ, top')` so φ is arg1 (EVENT) and top' is arg2 (GUARD). Changing the EVENT from φ to ψ requires BX3 (`RightMonoUntil`) not BX2G (`LeftMonoUntilG`). Current proof uses `LeftMonoUntilG` with `ψ := top'` -- needs to change to `RightMonoUntil` with `χ := top'` (the GUARD stays constant while EVENT changes).
- [ ] Re-verify `P_mono` (lines 103-107): Symmetric change -- use `RightMonoSince` instead of `LeftMonoSinceH`
- [ ] Re-verify `F_neg_G` (lines 112-114): Uses `someFuture (neg' φ)` -- abbreviation auto-updates. Should still work since it's just DNI.
- [ ] Re-verify `P_neg_H` (lines 117-119): Same analysis.
- [ ] Re-verify `G_distribution` (lines 132-155): Uses `LeftMonoUntilG` with `ψ := top'` for the F_mono pattern internally. Need to check if the proof structure still works. The `BX2G` instances at lines 141-144 and 149-150 pass `ψ := top'` -- after convention change, this puts top' in the "EVENT" position of the outer `untl`, but F(x) = untl(x, top') has x in EVENT position. So BX2G with ψ:=top' gives `G(φ→χ) → (untl(top', φ) → untl(top', χ))` which changes the GUARD (arg2) under globally -- this IS what we want for F_mono (monotonicity of the event inside F). Wait -- `untl(top', φ)` has top'=EVENT, φ=GUARD. That is NOT F(φ). F(φ) = `untl(φ, top')` with φ=EVENT. So BX2G with ψ:=top' does not give F-monotonicity. The proof needs restructuring to use BX3 (RightMonoUntil) instead.
- [ ] Re-verify `H_distribution` (lines 159-176): Same restructuring may be needed
- [ ] Re-verify `G_contrapose` (lines 181-191): Same BX2G usage pattern
- [ ] Re-verify `H_contrapose` (lines 194-204): Same
- [ ] Re-verify `G_and_intro`, `H_and_intro`, `G_imp_trans'`, `H_imp_trans'`, `connect_future_G`, `connect_past_H`: These build on G_distribution/H_distribution, so if those are fixed, these should follow
- [ ] Run `lake build Cslib.Logics.Temporal.Theorems.TemporalDerived` to verify

**Timing**: 1.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` - Update abbreviations, update convention comment, re-derive F_mono/P_mono/G_distribution/H_distribution/G_contrapose/H_contrapose proofs

**Key proof re-derivation strategy for F_mono**:

After the convention change, F(φ) = `untl(φ, top')` where φ is arg1 (EVENT). To prove G(φ→ψ) → F(φ) → F(ψ), we need to change the EVENT from φ to ψ while keeping GUARD=top'. This is BX3 `RightMonoUntil` (event monotonicity), not BX2G:

```
RightMonoUntil: G(φ→ψ) → (untl(φ, χ) → untl(ψ, χ))
Instantiate χ := top': G(φ→ψ) → (untl(φ, top') → untl(ψ, top')) = G(φ→ψ) → (F(φ) → F(ψ))
```

For `G_distribution`, the same pattern applies: the core argument uses BX2G/BX3 to establish monotonicity of F under globally, then contraposes to get G-distribution. The restructured proof should use BX3 where previously BX2G was used for the F-level step, and BX2G where BX3 was used for the guard-level step.

**Verification**:
- Module compiles cleanly with zero errors and zero sorries
- All proof terms are well-typed under the new convention
- `lean_verify` on key theorems confirms no axiom leakage

---

### Phase 6: Full Build Verification and Documentation [NOT STARTED]

**Goal**: Full project build verification and documentation of the completed convention change.

**Tasks**:
- [ ] Run full `lake build` to verify entire project compiles
- [ ] Grep for remaining old-convention patterns:
  - `grep -rn 'untl .top' Cslib/` should find no instances (old `F(φ)` pattern)
  - `grep -rn 'snce .top' Cslib/` should find no instances (old `P(φ)` pattern)
  - `grep -rn 'untl top' Cslib/Foundations/` should find only BX1 (symmetric `untl top top`)
- [ ] Verify TemporalEmbedding.lean still compiles (position-preserving, no changes needed)
- [ ] Verify Subformulas.lean still compiles (structurally symmetric, no changes needed)
- [ ] Add convention note to Truth.lean docstring documenting `untl(event, guard)` per Burgess 1982
- [ ] Add comment on BX12/BX12' noting they are trivially valid (F(φ) → F(φ)) under the corrected convention

**Timing**: 15 minutes

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Bimodal/Semantics/Truth.lean` - Add/update convention documentation
- No other file modifications expected (verification only)

**Verification**:
- `lake build` passes with zero errors across entire project
- No files missed in the conversion
- Convention is documented in the semantics file

## Testing & Validation

- [ ] `lake build` module-level verification after each phase
- [ ] Full `lake build` passes after Phase 6
- [ ] Zero sorry occurrences in modified files
- [ ] Grep verification: no remaining old-convention patterns
- [ ] `lean_verify` on F_mono, P_mono, G_distribution confirms no axiom leakage

## Artifacts & Outputs

- `specs/032_fix_untl_argument_order_convention/plans/01_untl-argument-fix.md` (this plan)
- `specs/032_fix_untl_argument_order_convention/summaries/01_untl-argument-fix-summary.md` (upon completion)

## Rollback/Contingency

All changes are to Lean source files tracked in git. If the convention change causes intractable proof failures:
1. `git stash` or `git checkout -- .` to revert all changes
2. The change is purely mechanical (argument swapping) with no structural additions, so partial rollback per-file is straightforward
3. If TemporalDerived proofs prove intractable, mark Phase 5 as [PARTIAL] with specific blocking theorems documented, and complete the remaining phases; downstream tasks can proceed with the convention fix even if some derived theorems need re-derivation later
