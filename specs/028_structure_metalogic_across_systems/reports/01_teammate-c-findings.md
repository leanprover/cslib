# Teammate C (Critic) Findings: Task 28 — Metalogic Structure

**Date**: 2026-06-09
**Confidence Level**: High

---

## Key Findings

### 1. The Deduction Theorem Is Fundamentally Non-Generic

The BimodalLogic `DeductionTheorem.lean` (442 lines) performs **structural induction on the concrete `DerivationTree` inductive type**, matching on 7 constructors: `axiom`, `assumption`, `modus_ponens`, `necessitation`, `temporal_necessitation`, `temporal_duality`, `weakening`. The key insight is:

- The necessitation/temporal_necessitation/temporal_duality cases are dispatched with `simp at hA` because they require empty context. This is a **logic-specific property** — different logics have different structural rules.
- The modus ponens case recurses with `DerivationTree.mp_height_gt_left` and `mp_height_gt_right` — these are height lemmas specific to the inductive type.
- The weakening case requires `removeAll` manipulation that is coupled to the concrete context representation.

**Verdict**: The deduction theorem **cannot be made generic** over `[PropositionalHilbert S]`. It requires a concrete `DerivationTree` inductive. Task 20's description already notes "DeductionTheorem stays per-logic" — this is correct, but the existing task descriptions (7, 21, 22) don't all explicitly plan for per-logic deduction theorems. Task 21 (Modal) and Task 22 (Temporal) don't mention deduction theorems at all. If modal/temporal metalogic needs deduction theorems, those tasks need to include them.

### 2. MCS Core Is *Mostly* Logic-Independent — But Not Entirely

Examining `MaximalConsistent.lean` and `MCSProperties.lean`:

**Logic-independent parts** (could be generic):
- `Consistent`, `MaximalConsistent`, `SetConsistent`, `SetMaximalConsistent` definitions — these only depend on `DerivationTree` via `Nonempty (DerivationTree fc Γ Formula.bot)`, i.e., derivability of ⊥.
- `set_lindenbaum` (Lindenbaum's lemma via Zorn) — purely set-theoretic, depends only on finite derivation + chain consistency.
- `consistent_chain_union` — same.
- `SetMaximalConsistent.closed_under_derivation` — only uses derivation weakening.
- `SetMaximalConsistent.implication_property` — only uses assumption + modus_ponens constructors.
- `SetMaximalConsistent.negation_complete` — uses deduction theorem (so logic-specific).

**Logic-specific parts**:
- Everything that uses `deduction_theorem` (which is the core MCS property `negation_complete`).
- The temporal properties at the bottom of MCSProperties.lean (`all_future_all_future`, `all_past_all_past`) which use specific temporal axioms.
- `derives_neg_from_inconsistent_extension` — uses deduction theorem.

**Verdict**: A generic MCS module is possible but ONLY for the parts that don't use the deduction theorem. The most important property — negation completeness — requires the deduction theorem and is thus per-logic. This means ~60% of MCS theory could be generic, but the crucial closure properties remain per-logic.

### 3. Soundness Is Inherently Per-Logic (Semantics-Specific)

The BimodalLogic `Soundness.lean` quantifies over `TaskFrame`, `TaskModel`, `WorldHistory`, `Omega` — all specific to bimodal task semantics. Each axiom validity proof (e.g., `modal_t_valid`, `modal_4_valid`) unpacks the specific semantic structures.

- Modal soundness would quantify over Kripke frames (accessibility relations).
- Temporal soundness would quantify over linear orders.
- Propositional soundness would be trivial (just truth valuations).

**Verdict**: Soundness is **100% per-logic**. There is no shared infrastructure. Each logic defines its own semantic models and proves axiom validity individually. The existing tasks (6 for bimodal) correctly scope this, but there are no corresponding soundness tasks for standalone Modal or Temporal.

### 4. The Typeclass Hierarchy Has a Potential Diamond Problem

Looking at `ProofSystem.lean`:
```
BimodalTMHilbert extends ModalS5Hilbert, TemporalNecessitation, HasAxiomMF
ModalS5Hilbert extends ModalHilbert, HasAxiomT, HasAxiom4, HasAxiomB
ModalHilbert extends PropositionalHilbert, Necessitation, HasAxiomK
```

But `TemporalBXHilbert extends PropositionalHilbert, TemporalNecessitation`.

The `BimodalConnectives` class already avoids the diamond by not extending `TemporalConnectives` (noted in the code comment at line 71 of Connectives.lean). However, `BimodalTMHilbert` doesn't extend `TemporalBXHilbert` — it only extends `ModalS5Hilbert` and adds `TemporalNecessitation` + `HasAxiomMF`. This means:

- A `[BimodalTMHilbert S]` instance does NOT provide `[TemporalBXHilbert S]`.
- Temporal theorems proven over `[TemporalBXHilbert S]` won't automatically apply to bimodal proofs.
- An explicit compatibility instance `BimodalTMHilbert → TemporalBXHilbert` would be needed, but the temporal axioms (BX3–BX10, etc.) present in the bimodal system but not in the `TemporalBXHilbert` class need to be accounted for.

**This is a structural design gap** that isn't addressed by any existing task.

### 5. The Existing Task Structure Has Metalogic Gaps

Examining the current task list:

| Task | Metalogic Coverage | Gap |
|------|-------------------|-----|
| 20 | Propositional theorems (generic) | ✅ Complete (implemented) |
| 21 | Modal proof system + theorems | ❌ No deduction theorem, no MCS, no soundness, no completeness |
| 22 | Temporal infrastructure + theorems | ❌ No deduction theorem, no MCS, no soundness |
| 23 | Temporal semantics | ❌ No soundness (just defines models) |
| 6 | Bimodal soundness | ✅ Scoped correctly |
| 7 | Bimodal deduction/MCS | ✅ Scoped correctly |
| 8 | Bimodal completeness | ✅ Scoped correctly |

**Missing metalogic for Modal**: No task covers modal deduction theorem, modal MCS theory, modal soundness (over Kripke semantics), or modal completeness. Task 21 only covers proof system and derived theorems — it produces no metalogical infrastructure.

**Missing metalogic for Temporal**: No task covers temporal deduction theorem, temporal MCS theory, or temporal soundness (over linear-order semantics). Task 22 covers proof system infrastructure, and task 23 covers semantics, but soundness connecting them is absent.

**Missing metalogic for Propositional**: No task covers propositional soundness (over truth valuations) — but this is typically trivial and may not need a separate task.

---

## Unvalidated Assumptions

1. **"Propositional metalogic can be shared"** — Partially true. Propositional *theorems* (already in Foundations/Logic/Theorems/) are generic via `[PropositionalHilbert S]`. But propositional *metalogic* (deduction theorem, consistency, MCS) requires concrete derivation trees. The assumption that "propositional-level metalogic" exists as a separate reusable layer is **misleading** — what exists generically is the *theorem* layer, not the *metatheorem* layer.

2. **"MCS theory can be parameterized"** — The core definitions (Consistent, MCS, Lindenbaum) could be parameterized over an abstract derivation relation, but this hasn't been validated. The BimodalLogic code uses `DerivationTree` as a `Type` (not `Prop`) for pattern matching in height functions. Whether an abstract interface (`Derivable : Context → Formula → Prop`) suffices for MCS theory hasn't been tested.

3. **"BimodalTMHilbert provides TemporalBXHilbert"** — It currently does NOT. No compatibility instance exists. This assumption may be implicit in tasks 5 and 22 but is unverified.

4. **"Modal and temporal fragments have independent metalogic"** — In BimodalLogic, all metalogic is bimodal. Whether a standalone modal deduction theorem (over a 4-constructor `Modal.DerivationTree`) or a standalone temporal deduction theorem (over a 5-constructor `Temporal.DerivationTree`) actually builds and works has not been validated. The proof strategy should transfer, but constructor-specific cases differ.

5. **"Importing between logics works at the metalogic level"** — At the theorem level, yes (via `[PropositionalHilbert S]` etc.). At the metalogic level (deduction theorem, MCS, soundness, completeness), importing is not straightforward because each metalogic depends on logic-specific derivation trees and semantic structures.

---

## Missing Questions

1. **Do we need standalone modal/temporal metalogic at all?** If the goal is just bimodal completeness/soundness, the standalone fragments don't need their own metalogic — the bimodal metalogic covers them via the embedding. But if the goal is to publish standalone modal/temporal libraries in CSLib, they need their own metalogic.

2. **What is the abstraction boundary for MCS theory?** Specifically: should we define `class HasDeductionTheorem (S : Type*) [InferenceSystem S F]` and build generic MCS on top? Or is the per-logic copy-and-adapt approach better given that each deduction theorem proof is ~400 lines of different structural induction?

3. **What happens to `FrameClass` in the modular architecture?** The BimodalLogic parameterizes `DerivationTree` by `FrameClass` (Base/Dense/Discrete), which gates axiom inclusion. For standalone modal or temporal logic, would a simpler `FrameClass` suffice, or should the same enum be used?

4. **How does the `temp_4_derived` / `all_future_all_future` pattern generalize?** These MCS temporal properties use bimodal-specific derived theorems. In a standalone temporal metalogic, the equivalent theorems would reference `Temporal.DerivationTree` — does this exist, or would it need to be created?

5. **What is the actual priority/scope?** Is the intent to have full metalogic (soundness + completeness) for each of the four systems, or is it acceptable to have full metalogic only for bimodal and lightweight proof-theory-only for modal/temporal?

---

## Risk Assessment

| Risk | Severity | Likelihood | Impact |
|------|----------|------------|--------|
| Deduction theorem can't be made generic | Low | Already confirmed — it's per-logic | Design clarity, not a blocker |
| BimodalTMHilbert → TemporalBXHilbert instance missing | Medium | High (it's verifiably absent) | Temporal theorems won't apply to bimodal proofs without explicit bridging |
| MCS theory partially generic but key properties per-logic | Medium | Confirmed | Code duplication: ~300-400 lines of MCS boilerplate per logic that wants metalogic |
| Standalone modal/temporal metalogic requires new DerivationTree inductives | Medium | High | Each new DerivationTree is ~200 lines + ~400 lines deduction theorem + ~600 lines MCS — substantial work per logic |
| Performance from deep typeclass hierarchy | Low | Medium | Lean 4's typeclass resolution may slow on deeply nested `[BimodalTMHilbert S]` searches |
| Tasks 21/22 don't account for metalogic | High | Confirmed | If metalogic is needed for these systems, tasks must be revised or new tasks created |
| `sorry`-free metalogic at standalone level | Medium | Medium | BimodalLogic has some sorry in completeness (chronicle construction). Standalone systems might have worse sorry situations if metalogic is rushed. |

---

## Recommendations

1. **Clarify scope first**: The user should decide whether standalone Modal/Temporal metalogic is in scope, or if only bimodal metalogic plus generic theorem reuse (via typeclasses) is needed. This decision drastically changes the task structure.

2. **Fix the TemporalBXHilbert gap**: Add a compatibility instance or restructure the typeclass hierarchy so `[BimodalTMHilbert S]` implies `[TemporalBXHilbert S]`. This is a prerequisite for any temporal theorem reuse in bimodal proofs.

3. **If standalone metalogic is needed**: Create DerivationTree inductives for Modal and Temporal logics, then port the deduction theorem and core MCS to each. Estimate ~1,500 lines per logic for basic metalogic (DerivationTree + DeductionTheorem + Consistent/MCS + Lindenbaum).

4. **Don't over-abstract MCS**: The temptation to create a generic `class HasDeductionTheorem` is strong but the payoff is marginal — the generic shell would be ~200 lines, while the per-logic deduction theorem implementation is ~400 lines. Three logic-specific copies (modal, temporal, bimodal) total ~1,200 lines, vs. ~200 generic + ~600 specific = ~800 lines. The savings are modest and the abstraction adds indirection.

5. **Update task 7 description**: It currently says "DeductionTheorem stays in this task (bimodal-specific)" — good. But verify that tasks 21 and 22 don't implicitly assume a deduction theorem exists for their logics.
