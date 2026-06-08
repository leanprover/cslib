# Research Report: Task #19

**Task**: Explore modular logic factoring: semantic boundaries, soundness/completeness, and tableau systems
**Date**: 2026-06-08
**Mode**: Team Research (4 teammates)

## Summary

All four teammates converge on a strong, unanimous recommendation: **keep semantics completely separate per logic module**. The proof system typeclass hierarchy (`PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`) is the correct shared layer for cross-logic theorem reuse. Semantics cannot be meaningfully unified because the underlying mathematical structures are fundamentally incompatible (Kripke frames vs. linear orders vs. task frames with world histories). This pattern is confirmed by CSLib's own conventions (HML, Modal, PL, and Linear Logic all define independent semantics), by FormalizedFormalLogic/Foundation (the largest Lean 4 multi-logic formalization), and by the absence of any Lean 4 project that unifies modal and temporal semantics. The existing embedding lattice (`PL->Modal->Bimodal`, `PL->Temporal->Bimodal`) is the correct mechanism for connecting logics across the semantic boundary, via conservative extension / semantic preservation theorems.

## Key Findings

### 1. Separate Semantics Per Logic (Unanimous, High Confidence)

The semantic structures across logics are structurally incompatible:

| Logic | Semantic Structure | Truth Evaluated Over |
|-------|-------------------|---------------------|
| Propositional | Theory-based / truth-value | Valuation `v : Atom -> Prop` |
| Modal | Kripke `Model World Atom` | World `w : World` via accessibility `r` |
| Temporal | Linear order `(D, <, V)` | Time point `t : D` |
| Bimodal | `TaskFrame D` + `WorldHistory F` | Triple `(M, tau, t)` with shift-closed `Omega` |

Modal `Satisfies` pattern-matches on `{atom, bot, imp, box}` over `(Model, World)`. Bimodal `truth_at` pattern-matches on all 6 constructors over `(TaskModel, Omega, WorldHistory, Time)`. No typeclass can abstract both without losing the content that soundness proofs depend on.

**Evidence**: FormalizedFormalLogic/Foundation uses completely separate `Kripke/` directories per logic with no shared semantic infrastructure. LeanLTL (ITP 2025) formalizes temporal logic purely over infinite traces, confirming temporal semantics are fundamentally trace/order-based, not Kripke-frame-based.

### 2. Proof System Typeclasses ARE the Correct Shared Layer (Unanimous)

The existing typeclass hierarchy in `Foundations/Logic/ProofSystem.lean` is where cross-logic generalization pays off:

```
PropositionalHilbert -> ModalHilbert -> ModalS5Hilbert -> BimodalTMHilbert
                     -> TemporalBXHilbert -> BimodalTMHilbert
```

Theorems proved at `[PropositionalHilbert S]` are automatically available to all logics via typeclass inheritance. This is exactly what Tasks 20-22 target, and the design is correct. Foundation's architecture validates this same split: shared proof-theoretic infrastructure via typeclass-parameterized axiom sets, separate semantics per logic family.

### 3. Soundness/Completeness Must Be Per-Logic (Unanimous)

Each logic needs its own soundness and completeness theorems connecting its own proof system to its own semantics. No existing project attempts generic soundness across different kinds of logics. Foundation's soundness is generic only *within* modal logic (across different axiom sets sharing the same Kripke frame structure), not across modal vs. temporal vs. bimodal.

The connection between logics is via **conservative extension theorems** using the existing syntactic embeddings:
- If `phi` is a modal formula and modal-valid, then `embed(phi)` is bimodal-valid
- These bridge theorems use the embedding lattice, not unified semantics

### 4. Temporal Semantics is a Critical Missing Piece (From Critic)

**This is the most important gap the research uncovered.** Temporal semantics does not exist in either repo at the standalone level:
- CSLib has `Temporal.Formula` but no semantics
- BimodalLogic defines temporal truth only within the bimodal `truth_at` function

Standalone temporal semantics on linear orders would be simpler than bimodal task frames:

```lean
structure TemporalModel (D : Type*) [LinearOrder D] (Atom : Type*) where
  valuation : D -> Atom -> Prop

def Temporal.Satisfies (M : TemporalModel D Atom) (t : D) : Temporal.Formula Atom -> Prop
  | .atom p => M.valuation t p
  | .bot => False
  | .imp phi psi => Temporal.Satisfies M t phi -> Temporal.Satisfies M t psi
  | .untl phi psi => exists s, t < s /\ Temporal.Satisfies M s phi /\ forall r, t < r -> r < s -> Temporal.Satisfies M r psi
  | .snce phi psi => exists s, s < t /\ Temporal.Satisfies M s phi /\ forall r, s < r -> r < t -> Temporal.Satisfies M r psi
```

**Recommendation**: Add a new task for standalone temporal semantics (Task 23). This would enable temporal soundness proofs, make Temporal/ a complete standalone module, and is NOT a port from BimodalLogic -- it is new infrastructure.

### 5. TemporalBXHilbert is a Shell -- Task 22 Scope Underestimated (From Critic)

Current `TemporalBXHilbert` extends only `PropositionalHilbert` + empty marker `TemporalNecessitation`. It has **zero temporal axiom requirements**. Filling it requires:

1. **~20 new axiom `abbrev`s** in `Axioms.lean` (only 2 of ~22 exist: `SerialFuture`, `SerialPast`)
2. **~20 new `HasAxiom*` typeclasses** in `ProofSystem.lean`
3. **Restructuring `TemporalBXHilbert`** to extend all of them
4. **Making `TemporalNecessitation` non-empty** -- it's currently a marker class with no derivation rule

The research synthesis estimated "~20 axiom abbrevs" which is roughly correct for the abbrevs alone, but underestimates the total scope (~30% of the actual typeclass infrastructure work).

### 6. BimodalTMHilbert Does NOT Extend TemporalBXHilbert (From Critic)

`BimodalTMHilbert` extends `ModalS5Hilbert` and `TemporalNecessitation` and `HasAxiomMF` -- but NOT `TemporalBXHilbert`. Once Task 22 fills out `TemporalBXHilbert` with ~20 `HasAxiom*` classes, theorems at `[TemporalBXHilbert S]` won't directly apply in `[BimodalTMHilbert S]` contexts.

**Options**:
1. Make `BimodalTMHilbert` extend `TemporalBXHilbert` (risks typeclass diamond with `PropositionalHilbert` -- same avoidance already done in `BimodalConnectives`)
2. Provide a manual instance `[BimodalTMHilbert S] -> TemporalBXHilbert S`
3. Add all temporal `HasAxiom*` directly to `BimodalTMHilbert` (parallel to the `BimodalConnectives` pattern)

**Recommended**: Option 3 (mirror the `BimodalConnectives` pattern that avoids the diamond). `BimodalTMHilbert` should directly extend the individual temporal `HasAxiom*` classes, just as `BimodalConnectives` directly extends `HasUntil`/`HasSince` rather than extending `TemporalConnectives`. Then provide a manual instance deriving `TemporalBXHilbert` from `BimodalTMHilbert`.

### 7. DeductionTheorem Portability Risk (From Critic)

Most propositional theorems (combinators I/B/C/S, `imp_trans`, identity) are mechanically portable -- they only use MP + axiom instantiation. However, the **DeductionTheorem requires structural induction on `DerivationTree`** (inspecting proof structure), which cannot be done at the generic `DerivableIn` (Prop-valued) level.

Options:
- Axiomatize the deduction theorem as a typeclass method (pragmatic, sidesteps the proof structure question)
- Create a generic `DerivationTree` in Foundations (significant new infrastructure)
- Defer DeductionTheorem to per-logic modules where concrete derivation trees exist

**Recommended**: Keep DeductionTheorem in per-logic modules initially. It's the one propositional theorem that resists generic porting, and forcing it into Foundations would require major infrastructure that isn't justified yet.

### 8. Tableau Systems Are Per-Logic (All Teammates)

The user asked about tableau systems for each logic. BimodalLogic's tableau (`Decidability/Tableau.lean`) has ~20 rules that are deeply tied to the bimodal formula structure. Factoring into standalone components:

- **Propositional rules** (and/or/imp/neg decomposition) are universal -- reusable
- **Modal S5 rules** require equivalence-class semantics -- modal-specific
- **Temporal rules** require linear order structure -- temporal-specific
- **Interaction rules** (boxTemporal, denseAxiom) -- bimodal-specific

No existing project has a "generic tableau framework." Rule sets are proper subsets across logics and termination arguments differ. Standalone propositional/modal/temporal tableau systems are possible but would be separate design efforts not in scope for Tasks 20-22.

### 9. Strategic Opportunities (From Horizons)

**Mathlib contribution candidates** (in order of readiness):
1. `Modal/Basic.lean` + `Cube.lean` -- frame correspondence proofs for all 15 cube logics. Already clean, well-documented, Mathlib-style.
2. Propositional Hilbert theorems (Task 20) -- once ported, completely standalone.
3. `Propositional/NaturalDeduction/Basic.lean` -- mature code by Thomas Waring.

**Three independent development tracks** enabled by separate semantics:
1. Modal Kripke semantics -> Modal soundness/completeness (leveraging existing `Cube.lean`)
2. Temporal linear-order semantics -> Temporal soundness (new, uses Mathlib's `LinearOrder`)
3. Bimodal task frame semantics -> Full TM metalogic (tasks 3, 6, 8)

## Synthesis

### Conflicts Resolved

No substantive conflicts between teammates. All four independently reached the same core recommendation (separate semantics) from different angles:
- Teammate A: Structural analysis of existing code
- Teammate B: Prior art survey (Foundation, LeanLTL, Mathlib)
- Teammate C: Gap analysis of the current plan
- Teammate D: Strategic/architectural reasoning

### Gaps Identified

| Gap | Severity | Where Addressed |
|-----|----------|----------------|
| Temporal semantics missing entirely | High | Recommend new Task 23 |
| TemporalBXHilbert is empty (no temporal axioms) | High | Task 22 scope needs revision |
| BimodalTMHilbert does not extend TemporalBXHilbert | Medium | Mirror BimodalConnectives pattern |
| DeductionTheorem doesn't port generically | Medium | Keep in per-logic modules |
| Tableau systems not addressed | Low | Separate future tasks if desired |
| Propositional truth-table semantics missing | Low | Not blocking for Tasks 20-22 |

### Recommendations

1. **Keep semantics separate per logic module.** This is confirmed by code analysis, prior art, mathematical structure, and project conventions. The proof system typeclasses are the correct shared layer.

2. **Add Task 23: Temporal Kripke Semantics on Linear Orders.** Define `Temporal.Model`, `Temporal.Satisfies`, basic validity/frame conditions. This fills the critical gap and enables standalone temporal soundness. Depends on Task 22. Medium effort (~4-6 hours).

3. **Revise Task 22 scope.** The "complete temporal axiom abbrevs" sub-task is ~30% of actual work. Task 22 should explicitly include: ~20 axiom abbrevs, ~20 HasAxiom* typeclasses, TemporalBXHilbert restructuring, TemporalNecessitation non-emptying, and BimodalTMHilbert compatibility instance.

4. **Revise plan to handle BimodalTMHilbert/TemporalBXHilbert relationship.** Use the BimodalConnectives pattern: BimodalTMHilbert directly extends individual temporal HasAxiom* classes (avoiding the diamond), plus a manual instance deriving TemporalBXHilbert.

5. **Keep DeductionTheorem per-logic.** It requires derivation tree induction that can't be done at the generic Prop-valued level. Port it within Modal, Temporal, and Bimodal proof system modules, not in Foundations.

6. **Soundness is per-logic, connected via embedding preservation theorems.** Each logic proves its own `derivable -> valid` theorem. Cross-logic connections use the existing embedding lattice (PL->Modal->Bimodal, PL->Temporal->Bimodal) with semantic preservation lemmas.

7. **Tableau systems are per-logic and out of scope for Tasks 20-22.** If standalone propositional/modal/temporal tableaux are desired, create separate tasks.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Semantic boundaries (primary) | completed | high |
| B | Prior art and alternatives | completed | high |
| C | Critical gaps and blind spots | completed | high |
| D | Strategic horizons | completed | high |

## References

- FormalizedFormalLogic/Foundation: https://github.com/FormalizedFormalLogic/Foundation (separate Kripke semantics per logic)
- LeanLTL (ITP 2025): https://github.com/UCSCFormalMethods/LeanLTL (temporal logic on traces, no Hilbert system)
- CSLib Modal Kripke semantics: `Cslib/Logics/Modal/Basic.lean`, `Cube.lean`, `Denotation.lean`
- BimodalLogic task frame semantics: `Theories/Bimodal/Semantics/TaskFrame.lean`, `Truth.lean`
- BimodalLogic proof system: `Theories/Bimodal/ProofSystem/Axioms.lean` (22 temporal axiom constructors)
- CSLib typeclass hierarchy: `Cslib/Foundations/Logic/ProofSystem.lean`, `Axioms.lean`, `Connectives.lean`
