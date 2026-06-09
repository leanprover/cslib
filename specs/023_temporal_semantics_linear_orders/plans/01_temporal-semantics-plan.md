# Implementation Plan: Task #23 -- Temporal Semantics on Linear Orders

- **Task**: 23 - Define standalone temporal semantics on linear orders
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: Task 22 (Temporal Infrastructure -- COMPLETED), Task 32 (untl argument order fix -- COMPLETED)
- **Research Inputs**: specs/023_temporal_semantics_linear_orders/reports/02_temporal-semantics-research.md
- **Artifacts**: plans/01_temporal-semantics-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Create standalone temporal semantics on linear orders for the existing `Cslib.Logic.Temporal.Formula` type. This is new infrastructure -- not ported from BimodalLogic. The implementation defines `TemporalModel` (valuation on a linear order), `Satisfies` (recursive truth evaluation for the five formula constructors), and validity definitions quantified over all linear orders. The work is structured as three files (`Model.lean`, `Satisfies.lean`, `Validity.lean`) totaling an estimated 410-530 lines, targeting `Cslib/Logics/Temporal/Semantics/`.

### Research Integration

The research report (02_temporal-semantics-research.md) provides:
- Complete type signatures for `TemporalModel`, `Satisfies`, and validity definitions
- Confirmation that untl/snce use the Burgess convention (event, guard) matching the bimodal `truth_at`
- Identification of Mathlib dependencies (`LinearOrder`, `Nontrivial`, `DenselyOrdered`, `SuccOrder`/`PredOrder`)
- The decision to use raw Mathlib typeclasses in validity (not the existing `FrameConditions.lean` typeclasses which require `AddCommGroup`)
- Universe strategy: use `Type` (not `Type*`) in validity quantifiers, matching bimodal pattern
- List of 11 basic lemmas needed for downstream soundness work

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

- ROADMAP.md Phase 3 (Temporal Semantics): "Defines `Temporal.Model` on `LinearOrder`, `Temporal.Satisfies` for all five connectives, and frame conditions for dense/discrete/linear orders."
- Success metric: "Temporal semantics defined standalone on LinearOrder (Task 23: ~400-600 new lines)"
- This task is the sole remaining item in Phase 3 and unlocks Phase 4 item Task 31 (Temporal Metalogic).

## Goals & Non-Goals

**Goals**:
- Define `TemporalModel D Atom` structure with `valuation : D -> Atom -> Prop` on `LinearOrder D`
- Define `Temporal.Satisfies` for all five formula constructors (`atom`, `bot`, `imp`, `untl`, `snce`)
- Define `Temporal.Valid`, `Temporal.ValidDense`, `Temporal.ValidDiscrete`, `Temporal.ValidSerial`
- Define `Temporal.SemanticConsequence` and `Temporal.Satisfiable`
- Prove basic truth lemmas (`bot_false`, `imp_iff`, `atom_iff`, `some_future_iff`, etc.)
- Prove validity reduction lemmas (`valid_implies_valid_dense`, etc.)
- Zero sorry, full `lake build` pass

**Non-Goals**:
- Temporal soundness theorem (deferred to Task 31)
- Connecting to the existing `FrameConditions.lean` typeclasses (which require `AddCommGroup`)
- Notation for validity (`|= phi`) -- can be added in Task 31 if needed
- Connecting to bimodal `truth_at` (future work, not this task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe polymorphism issues in validity quantifiers | M | L | Use `Type` (not `Type*`) for domain quantification, matching bimodal `valid` pattern |
| Lean structural recursion issues with `Satisfies` | L | L | `Satisfies` is structurally recursive on formula -- Lean should accept it automatically |
| Import conflicts with existing Temporal modules | M | L | Semantics/ is a new directory with no overlapping definitions; imports go Formula -> Model -> Satisfies -> Validity |
| `some_future_iff` / `all_future_iff` lemma difficulty due to `abbrev` unfolding | M | M | Use `simp only` or `unfold` to control abbrev expansion; may need to unfold derived operators manually |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Model.lean -- TemporalModel structure [COMPLETED]

**Goal**: Define the `TemporalModel` structure and example model constructors.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Semantics/Model.lean`
- [ ] Add Apache 2.0 copyright header
- [ ] Import `Cslib.Logics.Temporal.Syntax.Formula` and `Mathlib.Order.Defs.LinearOrder`
- [ ] Define `structure TemporalModel (D : Type*) [LinearOrder D] (Atom : Type*) where valuation : D -> Atom -> Prop`
- [ ] Add example constructors: `TemporalModel.allFalse` (all atoms false everywhere), `TemporalModel.allTrue` (all atoms true everywhere), `TemporalModel.constant` (constant valuation)
- [ ] Add module docstring explaining the design rationale (why no frame structure beyond LinearOrder)
- [ ] Run `lake build Cslib.Logics.Temporal.Semantics.Model` to verify

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Semantics/Model.lean` - new file (~60-80 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Semantics.Model` passes with zero errors
- `TemporalModel` structure is accessible in the `Cslib.Logic.Temporal` namespace

---

### Phase 2: Satisfies.lean -- Truth evaluation and basic lemmas [IN PROGRESS]

**Goal**: Define the recursive satisfaction relation and prove basic truth lemmas for all formula constructors and derived operators.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
- [ ] Add Apache 2.0 copyright header
- [ ] Import `Cslib.Logics.Temporal.Semantics.Model`
- [ ] Define `Temporal.Satisfies (M : TemporalModel D Atom) (t : D) : Formula Atom -> Prop` recursively:
  - `.atom p => M.valuation t p`
  - `.bot => False`
  - `.imp phi psi => Satisfies M t phi -> Satisfies M t psi`
  - `.untl phi psi => exists s, t < s /\ Satisfies M s phi /\ forall r, t < r -> r < s -> Satisfies M r psi` (phi=EVENT, psi=GUARD)
  - `.snce phi psi => exists s, s < t /\ Satisfies M s phi /\ forall r, s < r -> r < t -> Satisfies M r psi` (phi=EVENT, psi=GUARD)
- [ ] Prove `bot_false`: `Satisfies M t .bot <-> False` (or `not (Satisfies M t .bot)`)
- [ ] Prove `atom_iff`: `Satisfies M t (.atom p) <-> M.valuation t p`
- [ ] Prove `imp_iff`: `Satisfies M t (.imp phi psi) <-> (Satisfies M t phi -> Satisfies M t psi)`
- [ ] Prove `untl_iff`: unfold characterization of `Satisfies M t (.untl phi psi)`
- [ ] Prove `snce_iff`: unfold characterization of `Satisfies M t (.snce phi psi)`
- [ ] Prove `neg_iff`: `Satisfies M t (Formula.neg phi) <-> not (Satisfies M t phi)`
- [ ] Prove `top_true`: `Satisfies M t Formula.top`
- [ ] Prove `some_future_iff`: `Satisfies M t (Formula.some_future phi) <-> exists s, t < s /\ Satisfies M s phi`
- [ ] Prove `some_past_iff`: `Satisfies M t (Formula.some_past phi) <-> exists s, s < t /\ Satisfies M s phi`
- [ ] Prove `all_future_iff`: `Satisfies M t (Formula.all_future phi) <-> forall s, t < s -> Satisfies M s phi`
- [ ] Prove `all_past_iff`: `Satisfies M t (Formula.all_past phi) <-> forall s, s < t -> Satisfies M s phi`
- [ ] Add module docstring explaining the Burgess convention (event, guard) for untl/snce
- [ ] Run `lake build Cslib.Logics.Temporal.Semantics.Satisfies` to verify

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Semantics/Satisfies.lean` - new file (~200-250 lines)

**Verification**:
- `lake build Cslib.Logics.Temporal.Semantics.Satisfies` passes with zero errors
- All 11+ lemmas compile without sorry
- `Satisfies` handles structural recursion without manual termination proof

---

### Phase 3: Validity.lean -- Validity, consequence, and reduction lemmas [NOT STARTED]

**Goal**: Define validity quantified over all linear orders, semantic consequence, satisfiability, and prove reduction/relationship lemmas.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Semantics/Validity.lean`
- [ ] Add Apache 2.0 copyright header
- [ ] Import `Cslib.Logics.Temporal.Semantics.Satisfies` and `Cslib.Logics.Temporal.Syntax.Context`
- [ ] Define `Temporal.Valid (phi : Formula Atom) : Prop` quantifying over all `(D : Type) [LinearOrder D] [Nontrivial D]`
- [ ] Define `Temporal.ValidSerial (phi : Formula Atom) : Prop` adding `[NoMaxOrder D] [NoMinOrder D]`
- [ ] Define `Temporal.ValidDense (phi : Formula Atom) : Prop` adding `[DenselyOrdered D]` (on top of Serial constraints)
- [ ] Define `Temporal.ValidDiscrete (phi : Formula Atom) : Prop` adding `[SuccOrder D] [PredOrder D] [IsSuccArchimedean D]` (on top of Serial constraints)
- [ ] Define `Temporal.SemanticConsequence (Gamma : Context Atom) (phi : Formula Atom) : Prop`
- [ ] Define `Temporal.Satisfiable (phi : Formula Atom) : Prop`
- [ ] Define `Temporal.FormulaSatisfiable (phi : Formula Atom) : Prop` (alias or variant if needed)
- [ ] Prove `valid_implies_valid_serial`: `Valid phi -> ValidSerial phi`
- [ ] Prove `valid_implies_valid_dense`: `Valid phi -> ValidDense phi`
- [ ] Prove `valid_implies_valid_discrete`: `Valid phi -> ValidDiscrete phi`
- [ ] Prove `valid_serial_implies_valid_dense`: `ValidSerial phi -> ValidDense phi`
- [ ] Prove `valid_serial_implies_valid_discrete`: `ValidSerial phi -> ValidDiscrete phi`
- [ ] Prove `valid_iff_empty_consequence`: `Valid phi <-> SemanticConsequence [] phi`
- [ ] Prove `consequence_monotone`: monotonicity of semantic consequence with respect to context extension
- [ ] Prove `valid_modus_ponens`: if `Valid (phi.imp psi)` and `Valid phi` then `Valid psi`
- [ ] Prove `satisfiable_not_valid_neg`: `Satisfiable phi -> not (Valid (Formula.neg phi))` (or equivalent)
- [ ] Add module docstring explaining the validity hierarchy (Valid > ValidSerial > ValidDense/ValidDiscrete)
- [ ] Run `lake build Cslib.Logics.Temporal.Semantics.Validity` to verify
- [ ] Run full `lake build` to verify no regressions

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Semantics/Validity.lean` - new file (~150-200 lines)

**Verification**:
- `lake build` passes with zero errors on the full project
- All lemmas compile without sorry
- `grep -rn sorry Cslib/Logics/Temporal/Semantics/` returns no matches
- The validity hierarchy (Valid implies ValidSerial implies ValidDense/ValidDiscrete) is established

## Testing & Validation

- [ ] `lake build Cslib.Logics.Temporal.Semantics.Model` passes after Phase 1
- [ ] `lake build Cslib.Logics.Temporal.Semantics.Satisfies` passes after Phase 2
- [ ] `lake build Cslib.Logics.Temporal.Semantics.Validity` passes after Phase 3
- [ ] Full `lake build` passes with zero errors after Phase 3
- [ ] `grep -rn sorry Cslib/Logics/Temporal/Semantics/` returns no matches
- [ ] `TemporalModel`, `Satisfies`, `Valid`, `SemanticConsequence` are all accessible from the `Cslib.Logic.Temporal` namespace
- [ ] Import chain is clean: `Formula -> Model -> Satisfies -> Validity` with no circular dependencies
- [ ] No dependency on bimodal modules (`Cslib.Logics.Bimodal.*`)
- [ ] No dependency on proof system modules (`Cslib.Logics.Temporal.ProofSystem.*`)

## Artifacts & Outputs

- `Cslib/Logics/Temporal/Semantics/Model.lean` (~60-80 lines)
- `Cslib/Logics/Temporal/Semantics/Satisfies.lean` (~200-250 lines)
- `Cslib/Logics/Temporal/Semantics/Validity.lean` (~150-200 lines)
- Total: ~410-530 lines across 3 files

## Rollback/Contingency

The `Cslib/Logics/Temporal/Semantics/` directory is entirely new with no existing files. Rollback is straightforward: delete the directory and any barrel import additions. No existing files are modified by this task.

If individual lemmas prove difficult (e.g., `all_future_iff` due to double negation and abbrev unfolding), they can be deferred to Task 31 (Temporal Metalogic) without blocking the core definitions. The core deliverables are the three definitions (`TemporalModel`, `Satisfies`, `Valid`) and the basic constructor lemmas.
