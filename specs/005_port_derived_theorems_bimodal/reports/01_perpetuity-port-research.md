# Research Report: Port Perpetuity Theorems to cslib

**Task**: 5 (port_derived_theorems_bimodal)
**Date**: 2026-06-08
**Agent**: lean-research-agent

## Executive Summary

The Perpetuity module (Bridge.lean, Helpers.lean, Principles.lean) from BimodalLogic totals 2,051 source lines and contains six perpetuity principles (P1--P6) plus extensive helper infrastructure. All proofs are fully proven with zero sorry. The port to cslib requires adapting from BimodalLogic's concrete `DerivationTree`-based proofs to cslib's typeclass-based `InferenceSystem` architecture, and adding `always`/`sometimes` connectives to the Bimodal Formula type (currently defined only in the Temporal module).

## Source File Analysis

### Helpers.lean (158 lines)

**Namespace**: `Bimodal.Theorems.Perpetuity`

**Imports**:
- `Bimodal.ProofSystem.Derivation`
- `Bimodal.Syntax.Formula`
- `Bimodal.Theorems.Combinators`

**Key Definitions** (8):
| Name | Type | Description |
|------|------|-------------|
| `box_to_future` | `phi.box.imp phi.all_future` | Box implies future (MF + MT) |
| `box_to_past` | `phi.box.imp phi.all_past` | Box implies past (temporal duality on MF) |
| `box_to_present` | `phi.box.imp phi` | Box implies present (MT axiom) |
| `axiom_in_context` | Γ ⊢ φ from axiom | Helper: axiom weakened to context |
| `apply_axiom_to` | ⊢ B from axiom(A→B) and ⊢ A | Helper: axiom + MP |
| `apply_axiom_in_context` | Γ ⊢ B from axiom(A→B) and Γ ⊢ A | Helper: context axiom + MP |

**Port complexity**: LOW. These are straightforward wrappers. The `box_to_*` lemmas use MF, MT, and temporal duality. The `axiom_in_context` helpers may not be needed in cslib's typeclass style since axioms are accessed via typeclass methods rather than explicit `DerivationTree.axiom` calls.

### Principles.lean (900 lines)

**Namespace**: `Bimodal.Theorems.Perpetuity`

**Imports**:
- `Bimodal.Theorems.Perpetuity.Helpers`
- `Bimodal.Theorems.Propositional.Connectives`
- `Bimodal.Theorems.GeneralizedNecessitation`

**Key Definitions** (23):
| Name | Type | Description |
|------|------|-------------|
| `double_negation` | `phi.neg.neg.imp phi` | DNE wrapper |
| `perpetuity_1` | `phi.box.imp phi.always` | P1: necessary implies always |
| `contraposition` | `B.neg.imp A.neg` from `A.imp B` | Classical contraposition |
| `diamond_4` | `phi.diamond.diamond.imp phi.diamond` | S4 for diamond |
| `modal_5` | `phi.diamond.imp phi.diamond.box` | S5 characteristic |
| `perpetuity_2` | `phi.sometimes.imp phi.diamond` | P2: sometimes implies possible |
| `box_to_box_past` | `phi.box.imp phi.all_past.box` | Box to boxed past |
| `box_conj_intro` | `(A.and B).box` from `A.box` and `B.box` | Boxed conjunction intro |
| `box_conj_intro_imp` | `P.imp (A.and B).box` from imps | Implication version |
| `box_conj_intro_imp_3` | Three-way version | For P3 |
| `perpetuity_3` | `phi.box.imp phi.always.box` | P3: necessity of perpetuity |
| `box_dne` | `A.box` from `A.neg.neg.box` | DNE inside box |
| `perpetuity_4` | `phi.sometimes.diamond.imp phi.diamond` | P4: possibility of occurrence |
| `mb_diamond` | `phi.imp phi.diamond.box` | MB axiom wrapper |
| `box_diamond_to_future_box_diamond` | `phi.diamond.box.imp (phi.diamond.box.all_future)` | TF for boxed diamond |
| `box_diamond_to_past_box_diamond` | `phi.diamond.box.imp (phi.diamond.box.all_past)` | Past version via duality |
| `future_k_dist` | `(A.imp B).all_future.imp (A.all_future.imp B.all_future)` | Future K distribution |
| `past_k_dist` | `(A.imp B).all_past.imp (A.all_past.imp B.all_past)` | Past K distribution |
| `persistence` | `phi.diamond.imp phi.diamond.always` | Persistence lemma |
| `perpetuity_5` | `phi.sometimes.diamond.imp phi.diamond.always` | P5: persistent possibility |

**Port complexity**: MEDIUM-HIGH. Key challenges:
1. `future_k_dist` and `past_k_dist` use `generalized_temporal_k` from GeneralizedNecessitation (Task 22 dependency)
2. `future_k_dist` uses `Bimodal.Metalogic.Core.deduction_theorem` (Task 7 dependency)
3. The proofs are heavily tied to `DerivationTree` constructors (`axiom`, `necessitation`, `temporal_necessitation`, `temporal_duality`, `modus_ponens`, `weakening`)

### Bridge.lean (993 lines)

**Namespace**: `Bimodal.Theorems.Perpetuity`

**Imports**:
- `Bimodal.Theorems.Perpetuity.Helpers`
- `Bimodal.Theorems.Perpetuity.Principles`
- `Bimodal.Theorems.Propositional.Connectives`

**Key Definitions** (21):
| Name | Type | Description |
|------|------|-------------|
| `dne` | `A.neg.neg.imp A` | DNE wrapper |
| `modal_duality_neg` | `phi.neg.diamond.imp phi.box.neg` | Modal duality forward |
| `modal_duality_neg_rev` | `phi.box.neg.imp phi.neg.diamond` | Modal duality reverse |
| `box_mono` | `A.box.imp B.box` from `A.imp B` | Box monotonicity |
| `diamond_mono` | `A.diamond.imp B.diamond` from `A.imp B` | Diamond monotonicity |
| `future_mono` | `A.all_future.imp B.all_future` from `A.imp B` | Future monotonicity |
| `past_mono` | `A.all_past.imp B.all_past` from `A.imp B` | Past monotonicity |
| `local_efq` | `A.neg.imp (A.imp B)` | Local EFQ |
| `local_lce` | `[A.and B] ⊢ A` | Left conjunction elim (context) |
| `local_rce` | `[A.and B] ⊢ B` | Right conjunction elim (context) |
| `lce_imp` | `(A.and B).imp A` | LCE implication form |
| `rce_imp` | `(A.and B).imp B` | RCE implication form |
| `always_to_past` | `phi.always.imp phi.all_past` | Decompose always: past |
| `always_to_present` | `phi.always.imp phi` | Decompose always: present |
| `always_to_future` | `phi.always.imp phi.all_future` | Decompose always: future |
| `past_present_future_to_always` | Components to always | Recompose always |
| `always_dni` | `phi.always.imp phi.neg.neg.always` | DNI distributes over always |
| `always_dne` | `phi.neg.neg.always.imp phi.always` | DNE distributes over always |
| `temporal_duality_neg` | `phi.neg.sometimes.imp phi.always.neg` | Temporal duality forward |
| `temporal_duality_neg_rev` | `phi.always.neg.imp phi.neg.sometimes` | Temporal duality reverse |
| `always_mono` | `A.always.imp B.always` from `A.imp B` | Always monotonicity |
| `double_contrapose` | `B.imp A` from `A.neg.imp B.neg` | Double contraposition |
| `bridge1` | `phi.always.box.neg.imp phi.neg.sometimes.diamond` | Bridge 1 |
| `bridge2` | `phi.neg.diamond.always.imp phi.box.sometimes.neg` | Bridge 2 |
| `perpetuity_6` | `phi.box.sometimes.imp phi.always.box` | P6: occurrent necessity |

**Port complexity**: HIGH. This file is the largest and contains:
1. Many definitions that duplicate cslib's Foundations theorems (`box_mono`, `diamond_mono`, `modal_duality_neg*`, `lce_imp`, `rce_imp`, `dne`, `local_efq`)
2. `always_*` decomposition lemmas that depend on the `always` connective
3. Heavy use of `deduction_theorem` for `lce_imp`/`rce_imp`
4. The P6 derivation chains together P5, bridge lemmas, and double contraposition

## Target Module Structure in cslib

### Current cslib Bimodal Module

```
Cslib/Logics/Bimodal/
├── Embedding/         (PropositionalEmbedding, ModalEmbedding, TemporalEmbedding)
├── ProofSystem/       (Axioms, Derivation, Derivable, Instances, Substitution, LinearityDerivedFacts)
├── Semantics/         (TaskFrame, TaskModel, Truth, Validity, WorldHistory)
└── Syntax/            (Formula, Context)
```

### Proposed Target Structure

```
Cslib/Logics/Bimodal/
├── ...existing...
└── Theorems/
    └── Perpetuity/
        ├── Helpers.lean       -- box_to_*, axiom helpers (adapted)
        ├── Principles.lean    -- P1-P5, contraposition, diamond_4, modal_5, persistence
        └── Bridge.lean        -- P6, bridge lemmas, duality lemmas, always/sometimes helpers
```

### Namespace Convention

cslib uses `Cslib.Logic.Bimodal` namespace. The ported files should use:
```
namespace Cslib.Logic.Bimodal.Theorems.Perpetuity
```

## Import Mapping

### BimodalLogic -> cslib Equivalents

| BimodalLogic Import | cslib Equivalent | Status |
|---------------------|------------------|--------|
| `Bimodal.ProofSystem.Derivation` | `Cslib.Logics.Bimodal.ProofSystem.Derivation` | Available |
| `Bimodal.Syntax.Formula` | `Cslib.Logics.Bimodal.Syntax.Formula` | Available (but missing `always`/`sometimes`) |
| `Bimodal.Theorems.Combinators` | `Cslib.Foundations.Logic.Theorems.Combinators` | Available (generic typeclass) |
| `Bimodal.Theorems.Propositional.Connectives` | `Cslib.Foundations.Logic.Theorems.Propositional.*` | Available (Core + Connectives) |
| `Bimodal.Theorems.GeneralizedNecessitation` | NOT YET PORTED | Task 22 dependency |
| `Bimodal.Metalogic.Core.deduction_theorem` | NOT YET PORTED | Task 7 dependency |

### Typeclass vs Concrete Mapping

| BimodalLogic Pattern | cslib Pattern |
|----------------------|---------------|
| `DerivationTree.axiom [] _ (Axiom.modal_k_dist A B) trivial` | `HasAxiomK.K` |
| `DerivationTree.axiom [] _ (Axiom.modal_t phi) trivial` | `HasAxiomT.T` |
| `DerivationTree.axiom [] _ (Axiom.modal_4 phi) trivial` | `HasAxiom4.four` |
| `DerivationTree.axiom [] _ (Axiom.modal_b phi) trivial` | `HasAxiomB.B` |
| `DerivationTree.axiom [] _ (Axiom.modal_future phi) trivial` | `HasAxiomMF.MF` |
| `DerivationTree.necessitation _ h` | `Necessitation.nec h` |
| `DerivationTree.temporal_necessitation _ h` | `TemporalNecessitation.tempNec h` |
| `DerivationTree.temporal_duality _ h` | Need temporal duality typeclass or direct use |
| `DerivationTree.modus_ponens [] _ _ h1 h2` | `ModusPonens.mp h1 h2` |
| `DerivationTree.axiom [] _ (Axiom.prop_s X Y) trivial` | `HasAxiomImplyK.implyK` (NOTE: swapped names!) |
| `DerivationTree.axiom [] _ (Axiom.prop_k X Y Z) trivial` | `HasAxiomImplyS.implyS` (NOTE: swapped names!) |
| `⊢ phi` (notation) | `InferenceSystem.DerivableIn S phi` |
| `⊢[fc] phi` (with frame class) | `InferenceSystem.DerivableIn S phi` (fc via typeclass) |
| `Γ ⊢ phi` (contextual) | Requires `DerivationTree` directly or deduction theorem |

## Existing cslib Theorems That Overlap

Many theorems in the Perpetuity files already exist in cslib's Foundations layer (generic typeclass style):

| Perpetuity Theorem | cslib Equivalent | Location |
|---------------------|------------------|----------|
| `contraposition` | `Connectives.contraposition` | Propositional/Connectives.lean |
| `box_mono` | `Modal.Basic.box_mono` | Modal/Basic.lean |
| `diamond_mono` | `Modal.Basic.diamond_mono` | Modal/Basic.lean |
| `modal_duality_neg` | `Modal.Basic.modal_duality_neg` | Modal/Basic.lean |
| `modal_duality_neg_rev` | `Modal.Basic.modal_duality_neg_rev` | Modal/Basic.lean |
| `diamond_4` | `Modal.S5.diamond_4` | Modal/S5.lean |
| `modal_5` (◇φ→□◇φ) | `Modal.S5.axiom5_derived` | Modal/S5.lean |
| `lce_imp` | `Propositional.Core.lce_imp` | Propositional/Core.lean |
| `rce_imp` | `Propositional.Core.rce_imp` | Propositional/Core.lean |
| `double_negation` (DNE) | `Propositional.Core.double_negation` | Propositional/Core.lean |
| `dni` | `Combinators.dni` | Combinators.lean |
| `imp_trans` | `Combinators.imp_trans` | Combinators.lean |
| `identity` | `Combinators.identity` | Combinators.lean |
| `b_combinator` | `Combinators.b_combinator` | Combinators.lean |
| `pairing` | `Combinators.pairing` | Combinators.lean |
| `combine_imp_conj` | `Combinators.combine_imp_conj` | Combinators.lean |
| `combine_imp_conj_3` | `Combinators.combine_imp_conj_3` | Combinators.lean |

**Key implication**: The ported code should reuse these existing generic theorems (instantiated to `Bimodal.HilbertTM`) rather than re-proving them.

## Critical Gaps and Blockers

### Gap 1: `always`/`sometimes` Not Defined on Bimodal Formula

The cslib `Cslib.Logic.Bimodal.Formula` type does NOT define `always` or `sometimes`. These are defined only on `Cslib.Logic.Temporal.Formula`. The BimodalLogic source defines them on `Bimodal.Formula`.

**Resolution**: Add `always` and `sometimes` definitions to `Cslib/Logics/Bimodal/Syntax/Formula.lean`:
```lean
/-- Temporal 'always' operator: △φ := Hφ ∧ (φ ∧ Gφ). -/
abbrev Formula.always (φ : Formula Atom) : Formula Atom :=
  .and (.all_past φ) (.and φ (.all_future φ))

/-- Temporal 'sometimes' operator: ▽φ := ¬△¬φ. -/
abbrev Formula.sometimes (φ : Formula Atom) : Formula Atom :=
  .neg (.always (.neg φ))
```
Plus notation: `scoped prefix:40 "△" => Formula.always` and `scoped prefix:40 "▽" => Formula.sometimes`.

### Gap 2: `future_k_dist` and `past_k_dist` Depend on Deduction Theorem

The `future_k_dist` proof uses `Bimodal.Metalogic.Core.deduction_theorem` (from Task 7) and `generalized_temporal_k` (from GeneralizedNecessitation, Task 22 dependency). However, these theorems CAN be proven in the generic typeclass style using `TemporalNecessitation.tempNec` and the existing BX axiom infrastructure.

**Resolution**: Derive `future_k_dist` and `past_k_dist` directly from the temporal BX axioms using the typeclass approach. The cslib `TemporalDerived.lean` already has `G_distribution` which is very close to `future_k_dist`. Specifically:
- `G_distribution`: `⊢ G(φ → ψ) → (Gφ → Gψ)` -- this IS `future_k_dist`
- `H_distribution` is not yet present but can be derived by temporal duality (same pattern as `past_k_dist`)

Actually, checking more carefully: `G_distribution` in cslib's `TemporalDerived.lean` provides exactly `future_k_dist`. And `H_distribution` is there too. So the dependency on Task 7/22 can be eliminated.

### Gap 3: Temporal Duality Not in Typeclass

The BimodalLogic uses `DerivationTree.temporal_duality` as a concrete inference rule. In cslib, `TemporalNecessitation` provides `tempNec` (G rule) and `tempNecPast` (H rule via temporal duality), but there is no direct "temporal duality" typeclass method. The `temporal_duality` rule (if ⊢ φ then ⊢ swap_temporal φ) is available only at the `DerivationTree` level.

**Resolution**: Either:
1. Work at the `DerivationTree` level for proofs that need temporal duality
2. Add a `TemporalDuality` typeclass if needed
3. Use `tempNecPast` which internalizes temporal duality for the past necessitation case

Option 1 is most practical since the Instances.lean file already provides the bridge between DerivationTree and typeclasses.

### Gap 4: Context-Based Proofs

Several proofs (e.g., `local_lce`, `local_rce`, `future_k_dist`) work in non-empty contexts (`Γ ⊢ φ`). The typeclass approach in cslib only provides `⊢ φ` (empty context via `InferenceSystem.DerivableIn`). These require using `DerivationTree` directly.

**Resolution**: The `lce_imp` and `rce_imp` are already available in cslib's `Propositional.Core` via the typeclass approach (using Peirce + EFQ). The context-based intermediate lemmas (`local_lce`, `local_rce`) are not needed.

For `future_k_dist`/`past_k_dist`: use cslib's existing `G_distribution`/`H_distribution` from `TemporalDerived.lean`.

## Sorry Status

**BimodalLogic source**: Zero sorry across all three files. All 6 perpetuity principles (P1--P6) are fully proven.

**External dependency (BimodalLogic task 294)**: The task description mentions this dependency, but since all proofs are already sorry-free, this is not a blocker.

## Porting Strategy

### Approach: Hybrid Typeclass + DerivationTree

The recommended approach is:

1. **Use existing cslib generic theorems** where available (contraposition, box_mono, diamond_mono, modal_duality_*, diamond_4, modal_5, lce_imp, rce_imp, DNE, DNI, etc.)

2. **Work at the DerivationTree level** for bimodal-specific proofs that need temporal duality or the MF axiom interaction (box_to_future, box_to_past, always_*, persistence, perpetuity_*)

3. **Bridge via Instances.lean** to convert between typeclass theorems and DerivationTree proofs as needed

### Port Order

1. **Phase 1**: Add `always`/`sometimes` to Bimodal Formula (prerequisite)
2. **Phase 2**: Port Helpers.lean (box_to_* lemmas, helper utilities)
3. **Phase 3**: Port Principles.lean (P1--P5, supporting lemmas)
4. **Phase 4**: Port Bridge.lean (P6, bridge lemmas, duality lemmas)

### Scope Reduction Opportunities

The source is 2,051 lines, but many definitions already exist in cslib. After eliminating duplicates:

| Category | Source Lines | Reusable from cslib | New Lines (est.) |
|----------|-------------|--------------------:|------------------|
| Combinators (imp_trans, identity, etc.) | ~100 | ~100 | 0 |
| Propositional (contraposition, DNE, LCE, RCE) | ~250 | ~250 | 0 |
| Modal (box_mono, diamond_mono, diamond_4, modal_5) | ~200 | ~200 | 0 |
| Temporal K dist (future_k_dist, past_k_dist) | ~100 | ~100 (G/H_distribution) | 0 |
| Box helpers (box_to_*, box_conj_*) | ~200 | 0 | ~150 |
| Always/sometimes decomposition | ~200 | 0 | ~180 |
| Perpetuity P1--P6 | ~400 | 0 | ~350 |
| Bridge/duality lemmas | ~300 | 0 | ~250 |
| Local EFQ (Bridge.lean) | ~200 | ~200 | 0 |
| **Total** | **~2,051** | **~850** | **~930** |

Estimated ported code: approximately 930 new lines (excluding duplicates and comments).

## Porting Checklist

### Prerequisites
- [ ] Add `Formula.always` and `Formula.sometimes` to `Cslib/Logics/Bimodal/Syntax/Formula.lean`
- [ ] Add `△` and `▽` scoped notation for bimodal formulas
- [ ] Verify `G_distribution` and `H_distribution` are available in `TemporalDerived.lean`

### Helpers.lean Port
- [ ] Port `box_to_future` (MF + MT via typeclasses or DerivationTree)
- [ ] Port `box_to_past` (temporal duality on `box_to_future`)
- [ ] Port `box_to_present` (MT axiom)
- [ ] Evaluate whether `axiom_in_context` / `apply_axiom_to` / `apply_axiom_in_context` are needed (likely not in typeclass style)

### Principles.lean Port
- [ ] Wire `perpetuity_1` to use `box_to_*` + `combine_imp_conj_3` from cslib Combinators
- [ ] Reuse `Connectives.contraposition` for `contraposition`
- [ ] Reuse `Modal.S5.diamond_4` for `diamond_4`
- [ ] Reuse `Modal.S5.axiom5_derived` for `modal_5`
- [ ] Port `perpetuity_2` (contraposition of P1)
- [ ] Port `box_to_box_past` (temporal duality on MF)
- [ ] Reuse or adapt `box_conj_intro*` (may need bimodal-specific version)
- [ ] Port `perpetuity_3` (box_conj_intro_imp_3)
- [ ] Port `box_dne` (DNE inside box)
- [ ] Port `perpetuity_4` (contraposition of P3 + DNI bridge)
- [ ] Use `G_distribution`/`H_distribution` for `future_k_dist`/`past_k_dist`
- [ ] Port `persistence` (modal_5 + MF/TF + temporal K distribution)
- [ ] Port `perpetuity_5` (P4 + persistence)

### Bridge.lean Port
- [ ] Reuse cslib DNE, DNI for `dne`/`dni`
- [ ] Reuse cslib `modal_duality_neg*` from Modal/Basic.lean
- [ ] Reuse cslib `box_mono`, `diamond_mono` from Modal/Basic.lean
- [ ] Port `future_mono`, `past_mono` using `G_distribution`/`H_distribution`
- [ ] Reuse cslib `lce_imp`, `rce_imp` from Propositional/Core.lean
- [ ] Port `always_to_past`, `always_to_present`, `always_to_future` (conjunction elimination on always)
- [ ] Port `past_present_future_to_always` (identity on conjunction)
- [ ] Port `always_dni`, `always_dne` (DNI/DNE distributed over always)
- [ ] Port `temporal_duality_neg`, `temporal_duality_neg_rev`
- [ ] Port `always_mono` (monotonicity for always operator)
- [ ] Port `double_contrapose` (or derive from cslib contraposition + DNE/DNI)
- [ ] Port `bridge1`, `bridge2`
- [ ] Port `perpetuity_6` (P5 + bridges + double_contrapose)

### Verification
- [ ] `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers`
- [ ] `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles`
- [ ] `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Bridge`
- [ ] Zero sorry verification
- [ ] Linter compliance (`weak.linter.mathlibStandardSet`)
- [ ] Apache 2.0 headers

## Dependencies Analysis

| Dependency | Task | Required? | Resolution |
|------------|------|-----------|------------|
| Task 4 (ProofSystem) | Yes | Already completed | Derivation, Axioms, Instances available |
| Task 20 (Propositional) | Yes | Already completed | Combinators, Core, Connectives available |
| Task 21 (Modal) | Yes | Already completed | Modal/Basic, Modal/S5 available |
| Task 22 (Temporal) | Partial | TemporalDerived has G/H_distribution | Available |
| Task 7 (Deduction) | No | Was needed for future_k_dist but cslib has G_distribution | Not blocking |
| Task 32 (dependency in state.json) | Unknown | Need to check | -- |

**Conclusion**: The port can proceed without waiting for Tasks 7 or 22, since the key theorems (`G_distribution`, `H_distribution`, `contraposition`, `box_mono`, `diamond_4`, `axiom5_derived`, etc.) are already available in cslib.

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Temporal duality bridge complexity | Medium | Medium | Use DerivationTree directly for proofs needing temporal duality |
| `always`/`sometimes` definitional mismatch | Low | High | Match BimodalLogic definition exactly |
| `G_distribution` not exactly matching `future_k_dist` signature | Low | Medium | Verify type signatures before relying on reuse |
| Typeclass instance resolution issues | Medium | Medium | Test incremental builds after each file |
| Linter compliance for long lines | Medium | Low | Use `set_option linter.style.longLine false` where needed |
