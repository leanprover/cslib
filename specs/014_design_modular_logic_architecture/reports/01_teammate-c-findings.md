# Teammate C Findings: Critic — Gaps, Risks, and Blind Spots

**Task**: 14 — Design modular logic architecture for composable modal, temporal, and bimodal syntax and proof systems
**Date**: 2026-06-08
**Angle**: Critical analysis of decomposition feasibility

---

## Key Findings (Gaps and Blind Spots)

### 1. The Interaction Axiom Is Not Separable

The single most important structural observation: BimodalLogic's axiom system contains `modal_future` (MF: `□φ → □(Gφ)`), a modal-temporal *interaction* axiom that fundamentally ties the two modalities together. Its soundness proof (`modal_future_valid` in Soundness.lean) requires `WorldHistory.time_shift` and `TimeShift.time_shift_preserves_truth` — infrastructure that only exists because the semantic framework simultaneously has both modal (box over histories) and temporal (G over time points) structure.

**Critical implication**: You cannot prove soundness of MF in a "pure modal" or "pure temporal" module. The proof requires the combined semantic apparatus. This means the bimodal system is *not* a conservative extension of separate modal and temporal systems — the interaction axiom genuinely requires both semantic structures to coexist.

Furthermore, `temp_future` (TF: `□φ → G□φ`) is *derived* from MF + Modal T + Modal 4 (as noted in Axioms.lean line 294-295). This means the interaction story is even richer than it appears: TF falls out of combining MF with S5 properties, so the interaction layer is tightly woven with the modal layer.

### 2. The Formula Type Mismatch Is Deeper Than It Looks

The task description frames this as "six constructors vs four constructors," but the real problem is **primitive/derived alignment**:

| Feature | cslib Modal | BimodalLogic | Conflict |
|---------|------------|--------------|----------|
| Negation | **primitive** (`neg`) | **derived** (`φ.imp bot`) | Breaking |
| Conjunction | **primitive** (`and`) | **derived** (`¬(φ → ¬ψ)`) | Breaking |
| Diamond | **primitive** (`diamond`) | **derived** (`¬□¬φ`) | Breaking |
| Bottom | absent | **primitive** (`bot`) | Missing |
| Implication | **derived** (`¬φ ∨ φ₂`) | **primitive** (`imp`) | Breaking |
| Box | **derived** (`¬◇¬φ`) | **primitive** (`box`) | Breaking |

cslib's `Proposition Atom` uses `{atom, neg, and, diamond}` as primitives, making it a "diamond-primary" formulation. BimodalLogic uses `{atom, bot, imp, box, untl, snce}`, a "box-primary" formulation. These are not just notational variants — the inductive structure differs, so structural induction proofs (which is how `Satisfies` and all theorems in cslib are proved) do not transfer.

**The `grind` problem**: cslib's modal logic proofs lean heavily on Lean 4's `grind` tactic with `@[scoped grind]` annotations. These annotations are tuned to the specific inductive structure. Changing to a different set of primitives would break most of the automation.

### 3. Semantic Framework Incompatibility Is Severe

cslib's modal semantics uses:
```lean
structure Model (World : Type*) (Atom : Type*) where
  r : World → World → Prop
  v : World → Atom → Prop
```

BimodalLogic's semantics uses:
```lean
def truth_at (M : TaskModel F) (Omega : Set (WorldHistory F))
    (τ : WorldHistory F) (t : D) : Formula → Prop
```

These are fundamentally different:
- **cslib**: Kripke model, single accessibility relation, no time dimension
- **BimodalLogic**: Task frame model with world histories `τ : WorldHistory F`, temporal type `D` polymorphic over `LinearOrderedAddCommGroup`, shift-closed Omega sets `(Omega : Set (WorldHistory F))`

The bimodal box `□φ` quantifies over *all world histories in Omega at the current time*, not over accessible worlds via a relation. There is no `r : World → World → Prop` in BimodalLogic — the modal dimension is handled by quantifying over histories. This is the S5 universal accessibility pattern, but implemented completely differently from cslib's relation-based approach.

**Reconciliation options and their costs**:
- **Adapt cslib to BimodalLogic's framework**: Requires redesigning `Cslib.Logics.Modal` from scratch, breaking all downstream consumers (HML, Cube, Denotation)
- **Adapt BimodalLogic to cslib's framework**: Would require encoding temporal structure in the accessibility relation, losing the elegant time-shift invariance that makes MF/TF soundness proofs clean
- **Abstract over both**: Creates a complex typeclass hierarchy that neither existing codebase actually uses

### 4. The Decidability Proof Cannot Be Modularly Decomposed

BimodalLogic's decidability proof uses a tableau-based procedure (`Decidability/DecisionProcedure.lean`) with:
- `SignedFormula`: signed versions of the full 6-constructor Formula type
- `Tableau`: expansion rules covering propositional, modal, AND temporal cases
- `Closure`: branch closure detection using the full formula language
- `ProofExtraction`: extracts `DerivationTree` (the combined proof system)

The tableau rules for Until/Since interact with modal rules (the saturation procedure handles `□`-formulas and temporal formulas in the same branch). You cannot run "modal tableau" and "temporal tableau" independently and combine results — the branch-closing conditions require seeing both modalities simultaneously.

This is sorry-free and publication-ready. Decomposing it would require reproving everything.

### 5. The Completeness Proof Has a Monolithic Canonical Model

Completeness uses Maximal Consistent Sets (MCS) built from the full axiom system. The `SetMaximalConsistent` type in `Completeness.lean` closes under all 42 axiom constructors simultaneously. The canonical model construction (in `BXCanonical/`) builds chronicles — sequences of MCS states indexed by time — that simultaneously satisfy modal and temporal truth conditions.

The Burgess-Xu completeness architecture fundamentally requires the interaction axiom MF to be present during the MCS construction. Without MF, the canonical model does not validate the combined logic. You cannot build separate "modal MCS" and "temporal MCS" and somehow merge them — the MCS for the combined logic is not the product of component MCS's.

### 6. The FrameClass Architecture Is Actually a Composition Pattern

One bright spot: BimodalLogic already has a modular pattern in its `FrameClass` type:
```lean
inductive FrameClass where
  | Base     -- 37 axioms, valid on all linear orders
  | Dense    -- + density axioms, valid on densely ordered frames
  | Discrete -- + Prior-UZ/SZ + Z1, valid on discrete frames
```

`DerivationTree` is parameterized by `FrameClass`, with `lift` providing monotonicity (`fc₁ ≤ fc₂` implies coercion). The `minFrameClass` function gates axiom usage. This is already a working example of composable proof systems — but it composes *within* the bimodal logic, not *across* separate logics.

This pattern could inform the modular design, but it doesn't solve the cross-logic composition problem.

---

## Unvalidated Assumptions

### A1: "Modal proofs in cslib can be reused"
**Status**: Almost certainly false for concrete proofs, possibly true at a structural level.

cslib's modal proofs use `grind` with `@[scoped grind]` annotations tuned to `{atom, neg, and, diamond}`. These would need complete rewriting for any other primitive set. The theorems (K, T, B, 4, 5, D axioms) are standard and could be reproved, but the actual Lean proof terms are not portable.

### A2: "BimodalLogic's monolithic proofs CAN be factored"
**Status**: Partially true, partially false.

- **Propositional theorems** (`Theorems/Propositional/`): These are self-contained and can be extracted.
- **Pure modal S5 theorems**: Depend only on `box`, `imp`, `bot` constructors + modal axioms. Factoring is theoretically possible.
- **Pure temporal theorems**: Many BX axioms are purely temporal (BX1-BX12, excluding MF). These could potentially be factored.
- **Interaction theorems**: Cannot be factored. MF, TF, perpetuity principles (P1, P2) all require both modalities.
- **Metalogic**: Soundness, completeness, decidability are fundamentally bimodal. Cannot be factored.

### A3: "InferenceSystem framework can unify the proof systems"
**Status**: Promising but untested.

cslib's `InferenceSystem` typeclass (`S⇓a` notation) provides a generic derivation interface. Currently it's used only for semantic derivations (`HasInferenceSystem` for `Judgement`). Using it for syntactic derivations (Hilbert-style proof systems) would require:
- Defining `InferenceSystem` instances for modal axioms, temporal axioms, bimodal axioms
- Handling the fact that necessitation rules restrict to empty context
- Handling `FrameClass` parameterization

This is architecturally attractive but nobody has verified it works in practice.

### A4: "Universe polymorphism won't cause issues"
**Status**: Likely fine but unverified.

cslib's `Proposition (Atom : Type u) : Type u` and BimodalLogic's `Formula : Type` (universe 0, since `Atom = structured type`). Composing logics parameterized at different universe levels could trigger Lean 4 universe issues. The `InferenceSystem` class is already universe-polymorphic (`Sort v` for derivation), which helps.

---

## Fundamental Tensions

### Tension 1: Abstraction Depth vs. Proof Effort
A highly abstract design (typeclasses for formula types, typeclasses for proof systems, typeclasses for semantics) maximizes composability but multiplies the proof burden. Every theorem must be stated in terms of abstract interfaces, and `grind`/`simp` are less effective on typeclass-heavy goals. BimodalLogic's concrete approach (one Formula type, one DerivationTree type) is less composable but makes proofs tractable.

### Tension 2: Fidelity to BimodalLogic vs. Alignment with cslib
BimodalLogic's design choices (box-primary primitives, task frame semantics, Hilbert-style proofs, FrameClass parameterization) are well-motivated by the mathematical content. cslib's design choices (diamond-primary primitives, Kripke semantics, `grind`-based proofs, `InferenceSystem` framework) are well-motivated by generality. These cannot both be preserved in a merged architecture.

### Tension 3: "Compose" vs. "Extend"
Two distinct design strategies exist:
1. **Compose**: Build modal, temporal, bimodal as separate modules with well-defined interfaces, combining them via typeclasses or functors. High abstraction cost, maximum flexibility.
2. **Extend**: Keep BimodalLogic's monolithic Formula type but organize it as `Cslib.Logics.Temporal.TM` that *extends* the existing modal logic. Lower abstraction cost, but "temporal logic" is not independently importable.

The task description asks for option 1, but the evidence suggests option 2 is far more practical.

---

## Questions That Should Be Asked

### Q1: What is the actual use case for independent importability?
Is there a concrete user who needs temporal logic without modal logic? Or is this a "nice to have" architectural property? If the only consumer is the bimodal TM logic, then the decomposition effort may not be justified.

### Q2: Should cslib's modal logic be redesigned, or should BimodalLogic port to cslib's existing modal logic?
These lead to completely different architectures. The current cslib Modal module is relatively small (~270 lines for Basic, ~140 for Cube, ~50 for Denotation) and could be redesigned without catastrophic impact. But BimodalLogic is ~50,000+ lines of proven theorems that would all need updating.

### Q3: What about the Propositional layer?
cslib has `Cslib.Logic.PL.Proposition` with `{atom, and, or, impl}` primitives. BimodalLogic uses `{atom, bot, imp}` as propositional primitives. The propositional layers don't match either. Any modular design needs to reconcile *three* formula types (PL, Modal, Bimodal), not just two.

### Q4: Is the `expose`/`module` system compatible with a typeclass-heavy design?
cslib uses `@[expose] public section` and `module` declarations extensively. These interact with Lean 4's namespace and scoping system. A typeclass-based composable design would need `scoped instance` declarations that play well with the `module` system. Has this been tested?

### Q5: What is the compilation time budget?
BimodalLogic already has significant compilation times (large proofs, many files). Adding abstraction layers (typeclasses, generic frameworks) typically increases compilation time. Is there a time budget constraint?

### Q6: Can the decidability proof be preserved at all under decomposition?
The tableau procedure operates on the full Formula type. Any refactoring of Formula into composed types would require re-implementing the decision procedure from scratch. Is this acceptable?

---

## Recommendations for Research Completeness

The following topics should be investigated but may not be:

1. **Mathlib's algebraic hierarchy as a model**: The task description mentions this, but the relevant comparison is not Mathlib's *algebraic* structures (which compose via inheritance) but Mathlib's *logic-adjacent* structures (e.g., `FirstOrder.Language`, `Syntax.Term`). These have faced similar composition challenges and may provide useful negative examples.

2. **Prior art in multi-modal logic formalization**: Have other Lean/Coq/Isabelle projects attempted modular formalization of combined modal logics? The literature on *combining logics* (fusion, product, fibring) is relevant but may not have been formalized.

3. **The "temporal logic as a special modal logic" approach**: Standard temporal logic can be viewed as a multi-modal logic with two accessibility relations (future, past) on a linearly ordered frame. This would align temporal logic with cslib's modal framework (just add more relations). But BimodalLogic's Until/Since operators are not definable in basic modal logic — they require the full expressive power of first-order quantification over time points. This approach has a hard expressiveness ceiling.

4. **Cost-benefit of partial decomposition**: Instead of full decomposition, consider factoring out only what naturally separates (propositional theorems, pure modal S5 theorems) while keeping the temporal and bimodal core monolithic. Estimate the effort for each option.

---

## Confidence Level

**High confidence** in the following findings:
- Formula primitive mismatch is real and non-trivial
- Semantic frameworks are fundamentally incompatible
- Interaction axiom MF prevents clean factoring of metalogic proofs
- Decidability proof cannot be modularly decomposed

**Medium confidence** in:
- The FrameClass pattern as a model for modular design
- InferenceSystem framework as a potential unification point
- "Extend" being more practical than "Compose"

**Low confidence** in:
- Whether universe polymorphism will cause practical issues
- Whether `expose`/`module` interacts badly with typeclasses
- The exact cost of reproving cslib's modal theorems under a different primitive set
