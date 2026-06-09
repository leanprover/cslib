# Implementation Plan: Port Perpetuity Theorems to Bimodal Module

- **Task**: 5 - Port Perpetuity theorems to Cslib/Logics/Bimodal/Theorems/Perpetuity/
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: Tasks 4 (ProofSystem), 21 (Modal Theorems), 22 (Temporal Infrastructure)
- **Research Inputs**: specs/005_port_derived_theorems_bimodal/reports/01_perpetuity-port-research.md
- **Artifacts**: plans/01_perpetuity-port-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Port the six perpetuity principles (P1--P6) and their supporting lemmas from BimodalLogic's `Bimodal.Theorems.Perpetuity` module to cslib's `Cslib/Logics/Bimodal/Theorems/Perpetuity/`. The source consists of three files (Helpers.lean, Principles.lean, Bridge.lean) totaling 2,051 lines, but roughly 850 lines of functionality already exist in cslib's Foundations layer (Combinators, Propositional, Modal, Temporal theorems). The port produces approximately 930 new lines. A critical prerequisite is adding `always`/`sometimes` connective definitions to the Bimodal Formula type.

### Research Integration

The research report identified:
- **850 lines of reuse**: Combinators (`imp_trans`, `identity`, `b_combinator`, `pairing`, `combine_imp_conj*`, `dni`), Propositional (`double_negation`, `contraposition`, `lce_imp`, `rce_imp`, `efq_neg`), Modal (`box_mono`, `diamond_mono`, `modal_duality_neg*`, `diamond_4`, `axiom5_derived`), and Temporal (`G_distribution`, `H_distribution`) are already available in cslib's typeclass hierarchy.
- **Critical gap**: `Formula.always` and `Formula.sometimes` are not defined on Bimodal Formula. Must be added before any Perpetuity theorem can compile.
- **Proof approach**: Hybrid typeclass + DerivationTree. Use typeclass theorems where available (instantiated at `Bimodal.HilbertTM`), fall back to DerivationTree for proofs requiring temporal duality or MF axiom interaction.
- **No sorry in source**: All six principles are fully proven in BimodalLogic.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add `Formula.always` and `Formula.sometimes` definitions with notation to Bimodal Formula
- Port all 6 perpetuity principles (P1--P6) with zero sorry
- Create `Cslib/Logics/Bimodal/Theorems/Perpetuity/{Helpers,Principles,Bridge}.lean`
- Reuse existing cslib Foundations theorems instead of re-proving duplicates
- Pass `lake build`, linter, and zero-sorry verification

**Non-Goals**:
- Porting GeneralizedNecessitation (already in Task 21)
- Porting the deduction theorem (Task 7 scope)
- Porting Propositional/Combinators (already completed in Task 20)
- Creating a generic `always`/`sometimes` typeclass (concrete definitions suffice)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `always`/`sometimes` definition breaks existing Formula simp lemmas | H | L | Match BimodalLogic definition exactly; run full `lake build` after addition |
| Typeclass instance resolution fails for complex nested formula types | M | M | Fall back to explicit `@` application or direct DerivationTree proofs |
| `future_k_dist`/`past_k_dist` via cslib's `G_distribution`/`H_distribution` has signature mismatch | M | L | Verify signatures before Phase 3; adapt wrapper if needed |
| Temporal duality proofs with `swap_temporal` need formula simplification lemmas | M | M | Source uses `simp only [...]` with existing swap lemmas; same lemmas exist in cslib |
| `temp_future_derived` (box_to_future helper) not available in cslib's typeclass layer | M | M | Derive from MF + MT + M4 axioms directly, following source pattern |
| Long linter lines in deeply nested formula types | L | H | Use `set_option linter.style.longLine false` where needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Add always/sometimes to Bimodal Formula [COMPLETED]

**Goal**: Define `Formula.always` and `Formula.sometimes` connectives on the Bimodal Formula type, with scoped notation, so that Perpetuity theorems can reference these operators.

**Tasks**:
- [ ] Add `Formula.always` definition to `Cslib/Logics/Bimodal/Syntax/Formula.lean`:
  ```lean
  abbrev Formula.always (φ : Formula Atom) : Formula Atom :=
    .and (.all_past φ) (.and φ (.all_future φ))
  ```
- [ ] Add `Formula.sometimes` definition:
  ```lean
  abbrev Formula.sometimes (φ : Formula Atom) : Formula Atom :=
    .neg (.always (.neg φ))
  ```
- [ ] Add scoped notation for both operators:
  ```lean
  @[inherit_doc] scoped prefix:40 "△" => Formula.always
  @[inherit_doc] scoped prefix:40 "▽" => Formula.sometimes
  ```
- [ ] Add `swap_temporal` lemmas for `always` and `sometimes` if needed for later phases
- [ ] Run `lake build Cslib.Logics.Bimodal.Syntax.Formula` to verify no regressions

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` - Add always/sometimes definitions and notation

**Verification**:
- `lake build Cslib.Logics.Bimodal.Syntax.Formula` passes with zero errors
- No downstream build regressions in ProofSystem or Semantics modules

---

### Phase 2: Port Helpers.lean [COMPLETED]

**Goal**: Create `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` with the core box-to-temporal lemmas (`box_to_future`, `box_to_past`, `box_to_present`) and a `temp_future_derived` helper.

**Tasks**:
- [ ] Create directory `Cslib/Logics/Bimodal/Theorems/Perpetuity/`
- [ ] Create `Helpers.lean` with Apache 2.0 header and module structure
- [ ] Port `temp_future_derived`: `⊢ □φ → G(□φ)` using MF + MT + M4 axioms. This can use cslib's typeclass instances (HasAxiomMF, HasAxiomT, HasAxiom4) rather than direct DerivationTree axiom calls. The proof follows: M4 (`□φ → □□φ`), MF (`□□φ → □G□φ`), MT (`□G□φ → G□φ`), compose.
- [ ] Port `box_to_future`: `⊢ □φ → Gφ` via MF + MT (typeclass approach: `imp_trans HasAxiomMF.MF HasAxiomT.T`)
- [ ] Port `box_to_past`: `⊢ □φ → Hφ` via temporal duality on `box_to_future`. This requires `DerivationTree.temporal_duality` plus `swap_temporal` simplification. Use the same pattern as the source.
- [ ] Port `box_to_present`: `⊢ □φ → φ` (just `HasAxiomT.T`)
- [ ] Decide on `axiom_in_context`/`apply_axiom_to`/`apply_axiom_in_context` -- these are context-based helpers for DerivationTree. Port only if needed by later phases (likely not needed since we use typeclass theorems instead).
- [ ] Add module to lakefile or appropriate import file if needed
- [ ] Run `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` - New file

**Verification**:
- `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers` passes
- Zero sorry in file (`grep -c sorry Helpers.lean` = 0)

---

### Phase 3: Port Principles.lean (P1--P5) [COMPLETED]

**Goal**: Create `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` with perpetuity principles P1 through P5, reusing cslib Foundations theorems for propositional, modal, and temporal reasoning.

**Tasks**:
- [ ] Create `Principles.lean` with Apache 2.0 header
- [ ] Port P1 (`perpetuity_1`): `⊢ □φ → △φ`. Uses `box_to_past`, `box_to_present`, `box_to_future` + `combine_imp_conj_3` from Combinators.
- [ ] Port `contraposition` -- reuse `Connectives.contraposition` from cslib rather than re-deriving
- [ ] Port `diamond_4` -- reuse `Modal.S5.diamond_4` from cslib
- [ ] Port `modal_5` -- reuse `Modal.S5.axiom5_derived` from cslib
- [ ] Port P2 (`perpetuity_2`): `⊢ ▽φ → ◇φ`. Contraposition of P1 applied to `¬φ`.
- [ ] Port `box_to_box_past`: `⊢ □φ → □Hφ`. Temporal duality on MF (same DerivationTree pattern as source).
- [ ] Port `box_conj_intro`, `box_conj_intro_imp`, `box_conj_intro_imp_3` -- these build boxed conjunctions from components. Can use cslib's `Necessitation.nec`, `HasAxiomK.K`, `ModusPonens.mp` and `imp_trans` rather than direct DerivationTree calls.
- [ ] Port P3 (`perpetuity_3`): `⊢ □φ → □△φ`. Uses `box_to_box_past`, identity, MF + `box_conj_intro_imp_3`.
- [ ] Port `box_dne`: Apply DNE inside box. Uses `double_negation`, `Necessitation.nec`, `HasAxiomK.K`.
- [ ] Port P4 (`perpetuity_4`): `⊢ ◇▽φ → ◇φ`. Contraposition of P3 applied to `¬φ` + DNI bridge.
- [ ] Port `future_k_dist` / `past_k_dist` -- map to cslib's `G_distribution` / `H_distribution` from `TemporalDerived.lean`. Verify these provide exactly `⊢ G(A → B) → (GA → GB)` and `⊢ H(A → B) → (HA → HB)`. If so, use directly; if signature differs, create thin wrappers.
- [ ] Port `persistence`: `⊢ ◇φ → △◇φ`. Key proof: uses `modal_5` (= `axiom5_derived`), `temp_future_derived`, temporal duality, `future_k_dist`/`past_k_dist`, `box_to_present`, `combine_imp_conj_3`.
- [ ] Port P5 (`perpetuity_5`): `⊢ ◇▽φ → △◇φ`. Simple composition: `imp_trans (perpetuity_4 φ) (persistence φ)`.

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` - New file

**Verification**:
- `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles` passes
- Zero sorry in file
- All five principles (P1--P5) type-check

---

### Phase 4: Port Bridge.lean (P6 + Supporting Lemmas) [COMPLETED]

**Goal**: Create `Cslib/Logics/Bimodal/Theorems/Perpetuity/Bridge.lean` with P6, bridge lemmas, monotonicity lemmas, and always decomposition/recomposition lemmas.

**Tasks**:
- [ ] Create `Bridge.lean` with Apache 2.0 header
- [ ] Reuse `dne` (= `double_negation`), `modal_duality_neg`, `modal_duality_neg_rev`, `box_mono`, `diamond_mono` from cslib's `Propositional.Core` and `Modal.Basic` respectively -- do NOT re-derive
- [ ] Port `future_mono`: `⊢ (A → B) → (GA → GB)`. Uses `G_distribution` + `TemporalNecessitation.tempNec`.
- [ ] Port `past_mono`: `⊢ (A → B) → (HA → HB)`. Uses temporal duality + `H_distribution` + `TemporalNecessitation.tempNecPast`.
- [ ] Port `lce_imp` / `rce_imp` -- reuse from cslib's `Propositional.Core.lce_imp` / `rce_imp`. Do NOT re-derive.
- [ ] Port `always_to_past`, `always_to_present`, `always_to_future` -- conjunction decomposition on `always φ = Hφ ∧ (φ ∧ Gφ)`. Uses `lce_imp` and `rce_imp`.
- [ ] Port `past_present_future_to_always` -- identity on the conjunction (definitional equality).
- [ ] Port `always_dni`: `⊢ △φ → △(¬¬φ)`. Uses `dni`, `past_mono`/`future_mono` to lift DNI through temporal operators, then `combine_imp_conj` to recombine.
- [ ] Port `always_dne`: `⊢ △(¬¬φ) → △φ`. Mirror of `always_dni` using `dne`.
- [ ] Port `temporal_duality_neg`: `⊢ ▽¬φ → ¬△φ`. Contraposition of `always_dni`.
- [ ] Port `temporal_duality_neg_rev`: `⊢ ¬△φ → ▽¬φ`. Contraposition of `always_dne`.
- [ ] Port `always_mono`: `⊢ (A → B) → (△A → △B)`. Decompose, apply `past_mono`/`future_mono`/identity, recombine.
- [ ] Port `double_contrapose`: `⊢ (¬A → ¬B) → (B → A)`. Uses `contraposition` + `dne` + `dni`.
- [ ] Port `bridge1`: `⊢ ¬□△φ → ◇▽¬φ`. Uses `modal_duality_neg_rev`, `temporal_duality_neg_rev`, `diamond_mono`.
- [ ] Port `bridge2`: `⊢ △◇¬φ → ¬▽□φ`. Uses `modal_duality_neg`, `always_mono`, `dni`.
- [ ] Port P6 (`perpetuity_6`): `⊢ ▽□φ → □△φ`. Chain: `bridge1`, P5 for `¬φ`, `bridge2`, then `double_contrapose`.

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Bridge.lean` - New file

**Verification**:
- `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Bridge` passes
- Zero sorry in file
- P6 type-checks

---

### Phase 5: Build Verification and Integration [NOT STARTED]

**Goal**: Full project build, sorry check, linter compliance, and integration with the Bimodal module tree.

**Tasks**:
- [ ] Run full `lake build` to verify no regressions across the project
- [ ] Run `grep -rn sorry Cslib/Logics/Bimodal/Theorems/Perpetuity/` and verify zero occurrences
- [ ] Verify linter compliance: add `set_option linter.all true` to each file (or use project-level setting) and fix any warnings. Use `set_option linter.style.longLine false` for unavoidably long lines in deeply nested formula types.
- [ ] Verify Apache 2.0 copyright headers on all three new files
- [ ] Run `lake shake` on each new file to remove unused imports
- [ ] Create or update the module hierarchy file if needed (e.g., `Cslib/Logics/Bimodal/Theorems.lean` or `Cslib/Logics/Bimodal/Theorems/Perpetuity.lean` barrel file)
- [ ] Verify the `always`/`sometimes` additions to Formula.lean do not break any existing downstream consumers

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` - Linter fixes if needed
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` - Linter fixes if needed
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Bridge.lean` - Linter fixes if needed
- Possibly `Cslib/Logics/Bimodal/Theorems/Perpetuity.lean` or `Cslib/Logics/Bimodal.lean` - Module barrel file

**Verification**:
- Full `lake build` passes with zero errors
- Zero sorry across all Perpetuity files
- Linter passes (or has documented suppressions for long lines)
- All 6 perpetuity principles (P1--P6) are proven and type-check

## Testing & Validation

- [ ] `lake build Cslib.Logics.Bimodal.Syntax.Formula` passes after Phase 1
- [ ] `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers` passes after Phase 2
- [ ] `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles` passes after Phase 3
- [ ] `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Bridge` passes after Phase 4
- [ ] Full `lake build` passes after Phase 5
- [ ] `grep -rn sorry Cslib/Logics/Bimodal/Theorems/Perpetuity/` returns zero matches
- [ ] Each file has Apache 2.0 copyright header
- [ ] No vacuous definitions (`def X := True` patterns)

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/Syntax/Formula.lean` - Modified (always/sometimes added)
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` - New file (~100 lines)
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` - New file (~450 lines)
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Bridge.lean` - New file (~400 lines)
- `specs/005_port_derived_theorems_bimodal/plans/01_perpetuity-port-plan.md` - This plan

## Rollback/Contingency

- If `always`/`sometimes` definitions break downstream modules, revert the Formula.lean change and investigate the conflict before proceeding.
- If a specific perpetuity principle cannot be proven without sorry, mark the specific theorem with `sorry` and document the blocker. Do not use vacuous definitions. The principle can be revisited once the blocker (e.g., Task 7 deduction theorem) is resolved.
- If typeclass instance resolution is too slow for deeply nested formula types, switch to explicit `@` notation or direct DerivationTree proofs for the affected theorems.
- Git revert of the Formula.lean changes will cleanly restore the prior state since no other files in this task depend on existing code (all other files are new).
