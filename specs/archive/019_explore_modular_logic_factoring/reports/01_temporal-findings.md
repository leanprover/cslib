# Temporal Logic Factoring Analysis

**Task**: 19 — Explore modular logic factoring
**Focus**: Temporal components in BimodalLogic that belong in Temporal/
**Date**: 2026-06-08

---

## (a) What Currently Exists in cslib's Temporal Module

`Cslib.Logics.Temporal/` has exactly one file:

### Syntax/Formula.lean (93 lines)
- `Temporal.Formula` inductive with 5 constructors (`atom, bot, imp, untl, snce`)
- Derived operators: `some_future` (F), `all_future` (G), `some_past` (P), `all_past` (H)
- Notation and `TemporalConnectives` instance

**No semantics, no proof infrastructure, no axioms, no derived theorems, no frame conditions.**

### Supporting infrastructure in Foundations/Logic/
- **Connectives.lean**: `TemporalConnectives` extends `PropositionalConnectives` + `HasUntil` + `HasSince`
- **Axioms.lean**: Only 2 temporal axiom `abbrev`s: `SerialFuture` and `SerialPast`. None of the ~20 BX temporal axiom schemas are defined.
- **ProofSystem.lean**: `TemporalBXHilbert` is essentially empty — extends `PropositionalHilbert` + `TemporalNecessitation` with zero temporal axiom requirements. No `HasAxiomSerialFuture`, no `HasAxiomConnectFuture`, etc.

---

## (b) BimodalLogic Components That Are Purely Temporal

Checked each BimodalLogic source file for actual uses of `.box`/`Formula.box`/`□`:

| Component | Box/Modal Refs | Verdict |
|-----------|---------------|---------|
| Theorems/TemporalDerived.lean (~790 lines) | **0** | Purely temporal |
| Theorems/Combinators.lean (propositional core, ~560 lines) | 0 (except one TF derivation at end) | Mostly propositional |
| Theorems/Propositional/{Core,Connectives,Reasoning} (~1100 lines) | **0** | Purely propositional |
| Theorems/ContextualProofs.lean (~500 lines) | Namespace imports only | Purely propositional |
| Theorems/GeneralizedNecessitation.lean (~400 lines) | Uses necessitation rule | Bimodal (two necessitation rules) |
| Theorems/ModalS4.lean, ModalS5.lean (~800 lines) | Heavy box usage | Inherently modal |
| Theorems/Perpetuity/ (~800 lines) | Heavy box usage (22+84+233 refs) | **Inherently bimodal** |
| ProofSystem/Axioms.lean — temporal axioms | 22 purely temporal, 5 modal, 1 interaction | Separable |
| ProofSystem/Derivation.lean — rules | `necessitation` (modal) + `temporal_necessitation` | Separable |
| Metalogic/Core/DeductionTheorem.lean (~500 lines) | **0** box refs in logic | Structurally generic |
| Metalogic/Core/MaximalConsistent.lean (~600 lines) | **0** | Structurally generic |
| Metalogic/Core/MCSProperties.lean (~700 lines) | **0** | Structurally generic |
| FrameConditions/FrameClass.lean (~130 lines) | **0** | Purely temporal (linear orders, density, discreteness) |
| Semantics/Truth.lean — `truth_at` | `.box φ` quantifies over histories | **Inherently bimodal** |
| Semantics/TaskFrame.lean, WorldHistory.lean, TaskModel.lean | Box-related accessibility | **Inherently bimodal** |

---

## (c) What Could Be Factored into Temporal/

### High confidence — purely temporal

1. **Temporal axiom `abbrev`s** (~20 definitions): `serial_future/past`, `connect_future/past`, `left_mono_until_G/since_H`, `right_mono_until/since`, `self_accum_until/since`, `absorb_until/since`, `linear_until/since`, `until_F/since_P`, `temp_linearity/_past`, `F_until_equiv/P_since_equiv`. Only need `HasBot`, `HasImp`, `HasUntil`, `HasSince`. Belong in `Foundations/Logic/Axioms.lean`.

2. **`HasAxiom*` typeclasses for temporal axioms**: `HasAxiomConnectFuture`, `HasAxiomLinearUntil`, etc. in `ProofSystem.lean`. `TemporalBXHilbert` should extend these.

3. **Frame condition typeclasses** (FrameClass.lean, ~130 lines): `LinearTemporalFrame`, `SerialFrame`, `DenseTemporalFrame`, `DiscreteTemporalFrame`. Purely about temporal order properties. Belong in `Temporal/FrameConditions/`.

4. **TemporalDerived.lean** (~790 lines): All derived temporal theorems (temporal K distribution, temporal 4, temporal connectedness, future/past interaction, Until/Since lemmas). Zero `box` — purely temporal. With typeclass signatures `[TemporalBXHilbert S]`, belongs in `Temporal/Theorems/`.

### Medium confidence — structurally generic

5. **DeductionTheorem.lean** (~500 lines): Pattern-matches on derivation rules and handles necessitation cases vacuously (can't occur with non-empty contexts). Could be stated generically.

6. **MaximalConsistent.lean + MCSProperties.lean** (~1300 lines): Zero modal references. MCS construction uses only: formula type (Countable, Encodable), Context (List Formula), Derivable predicate. Could in principle be generic over any formula type.

### Inherently bimodal — must stay in Bimodal/

7. **Semantics/** (~2200 lines): Task frame semantics is inherently bimodal — `□φ` quantifies over world histories. A standalone temporal semantics would require writing a *new* simpler module (truth on a single linear order).

8. **Perpetuity/** (~800 lines): Heavily uses both `□` and temporal operators.

9. **Completeness, Decidability, Separation**: Theorems about the full bimodal system.

---

## (d) The Gap for a Standalone Temporal Logic

| Layer | What Exists | What's Missing | Source |
|-------|------------|----------------|--------|
| **Syntax** | Formula type + derived ops | `complexity`, `atomSet`, `Countable`/`Encodable` instances, `Context`, `BigConj`, `Subformulas`, `SubformulaClosure` | BimodalLogic (but for Temporal formula, not Bimodal) |
| **Axioms** | 2 abbrevs | ~20 more temporal BX axiom abbrevs + `HasAxiom*` classes | BimodalLogic ProofSystem/Axioms.lean |
| **Proof System** | `TemporalBXHilbert` (empty) | Complete the class; create `Temporal.DerivationTree` (5 rules: MP, temporal-nec, temporal-duality, weakening, axiom — NO modal necessitation); create `Temporal.Axiom` inductive (~31 axioms, excluding 5 modal + 1 interaction) | Factored from BimodalLogic |
| **Derived Theorems** | None | Port `TemporalDerived.lean` with `[TemporalBXHilbert S]` | BimodalLogic Theorems/ |
| **Semantics** | None | Write temporal Kripke semantics on linear orders: `truth_at M t φ` where `M = (D, <, V)` with `V : D → Atom → Prop`, no world histories | **New** (not from BimodalLogic) |
| **Frame Conditions** | None | Port `LinearTemporalFrame`, `DenseTemporalFrame`, `DiscreteTemporalFrame` | BimodalLogic FrameConditions |
| **Metalogic** | None | Deduction theorem + MCS theory (structurally generic). Soundness/completeness for temporal fragment needs new semantics. | Partially from BimodalLogic, partially new |

### Key Architectural Insight

BimodalLogic's `DerivationTree` has 7 inference rules. A temporal-only version needs 5 (dropping `necessitation`, keeping `temporal_necessitation` + `temporal_duality`). The `Axiom` inductive has 42 constructors; a temporal-only version needs ~31 (dropping 5 S5 modal axioms + MF interaction axiom). This factoring is clean.

---

## Practical Recommendations

Largest bang-for-buck items that unblock downstream work and avoid misplacing code:

1. **Complete temporal axiom `abbrev`s** in `Foundations/Logic/Axioms.lean` (~20 definitions)
2. **Add corresponding `HasAxiom*` classes** in `ProofSystem.lean` and flesh out `TemporalBXHilbert`
3. **Create `Temporal.Axiom` inductive + `Temporal.DerivationTree`** in `Temporal/ProofSystem/`
4. **Port `TemporalDerived.lean`** into `Temporal/Theorems/`
5. **Port frame condition typeclasses** into `Temporal/FrameConditions/`
6. **Write standalone temporal semantics** (new: truth on linear orders, no world histories)

Items 1-2 are foundation work that task 4 partially needs anyway. Items 3-6 would be new tasks or revisions to existing tasks.
