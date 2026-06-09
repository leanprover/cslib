# Research Report: Task #28

**Task**: Structure metalogic across Propositional, Modal, Temporal, and Bimodal systems
**Date**: 2026-06-09
**Mode**: Team Research (4 teammates)

## Summary

The BimodalLogic repo contains ~20,000 lines of metalogic under a monolithic `Theories/Bimodal/Metalogic/` directory, tightly coupled to bimodal-specific formula types and derivation trees. All four research angles converge on a clear finding: metalogic results are fundamentally per-logic because they depend on concrete derivation tree inductives and logic-specific semantic models. The deduction theorem, soundness, and completeness cannot be meaningfully abstracted across logics. However, a lightweight layer of generic definitions (consistency, maximal consistency, Lindenbaum skeleton) can live in `Foundations/Logic/Metalogic/`, and the existing embedding infrastructure positions the project well for future metalogic transfer theorems. The existing bimodal tasks (3-11) are correctly scoped, but standalone modal and temporal metalogic tasks are missing.

## Key Findings

### 1. Deduction Theorem Is Per-Logic (HIGH confidence, all 4 teammates agree)

The deduction theorem requires structural induction on concrete `DerivationTree` inductives. BimodalLogic's version matches 7 constructors; a modal version would have ~5, temporal ~6. The proof strategy transfers but the constructor-specific cases differ fundamentally. **No generic abstraction is possible or desirable.**

Task 20's research already established this ("DeductionTheorem stays per-logic"). The existing bimodal task 7 correctly scopes the bimodal deduction theorem. However, tasks 21 (Modal) and 22 (Temporal) don't mention deduction theorems — they cover proof systems and derived theorems only.

### 2. MCS Theory Is ~60% Generic (HIGH confidence)

Examining `MaximalConsistent.lean` and `MCSProperties.lean`:

**Generic components** (logic-independent):
- `Consistent`, `MaximalConsistent`, `SetConsistent`, `SetMaximalConsistent` definitions
- `set_lindenbaum` (Lindenbaum's lemma via Zorn — purely set-theoretic)
- `consistent_chain_union` (chain consistency)
- `closed_under_derivation` (uses only weakening + modus ponens)
- `implication_property` (uses only assumption + modus ponens)

**Per-logic components** (depend on deduction theorem):
- `negation_complete` — the most important MCS closure property
- `derives_neg_from_inconsistent_extension`
- Temporal properties (`all_future_all_future`, `all_past_all_past`) — use bimodal-specific axioms
- Modal properties (`box_closure`, `box_box`) — use modal axioms T and 4

**Assessment**: Definitions can be shared (~300 lines in Foundations), but the crucial closure properties (negation completeness) and witness conditions remain per-logic. The benefit of generic MCS infrastructure is moderate — it saves ~200-300 lines of definitions per logic but doesn't eliminate the per-logic proof work.

### 3. Soundness and Completeness Are Inherently Per-Semantics (HIGH confidence)

Soundness proofs quantify over semantics-specific structures:
- **Modal**: Kripke frames with accessibility relations
- **Temporal**: Linear orders
- **Bimodal**: Task frames with world histories and shift-closed omega sets

Each axiom validity proof unpacks specific semantic structures. The completeness proof chain (canonical model construction, truth lemma, witness conditions) is similarly entangled with per-logic semantics. The ~8,000 lines of bimodal soundness + completeness have no reusable component for other logics.

### 4. Existing Tasks Are Correctly Scoped — But Two Gaps Exist (HIGH confidence)

All four teammates agree: tasks 3-11 (bimodal porting) are correctly scoped, and tasks 20-23 (foundations + modal/temporal) are reasonable. But:

**Gap 1 — No standalone modal metalogic**: Task 21 covers `Modal.DerivationTree` + derived theorems but has no deduction theorem, MCS theory, soundness, or completeness for Kripke semantics.

**Gap 2 — No standalone temporal metalogic**: Tasks 22-23 cover temporal proof system + semantics but have no deduction theorem, MCS theory, or soundness over linear orders.

These gaps mean CSLib would have bimodal metalogic but no standalone modal or temporal metalogic — undermining the "each level is a standalone, importable library" principle.

### 5. BimodalTMHilbert → TemporalBXHilbert Instance Is Missing (HIGH confidence, Critic finding)

The typeclass hierarchy has a structural gap: `BimodalTMHilbert` extends `ModalS5Hilbert` and adds `TemporalNecessitation` + `HasAxiomMF`, but does NOT extend or provide `TemporalBXHilbert`. This means temporal theorems proven over `[TemporalBXHilbert S]` won't apply to bimodal proofs without an explicit compatibility instance. No existing task addresses this.

### 6. FormalizedFormalLogic/Foundation Validates CSLib's Architecture (HIGH confidence, Teammate B)

The closest comparable Lean 4 project (Foundation) uses nearly the same pattern CSLib already has: generic connective typeclasses + per-logic metalogic. Foundation shares `LogicSymbol`, `Entailment`, `Embedding`, `LindenbaumAlgebra` but keeps MCS theory, soundness, completeness, and deduction theorems per-logic. CSLib's existing `HasBot`/`HasImp`/`HasBox` → `PropositionalHilbert`/`ModalHilbert` hierarchy parallels Foundation's approach and is well-designed.

## Synthesis

### Conflicts Resolved

**Conflict 1: How much MCS to share in Foundations?**
- Teammate A: LOW confidence on shared MCS (uncertain benefit)
- Teammate B: Add lightweight Sound/Complete typeclasses, keep MCS per-logic
- Teammate C: ~60% generic but key properties per-logic; don't over-abstract
- Teammate D: Extract ~300-500 lines to Foundations/Logic/Metalogic/MCS.lean

**Resolution**: Adopt a minimal approach — place generic *definitions* (Consistent, SetMaximalConsistent, Lindenbaum skeleton) in Foundations (~200-300 lines). Keep *proofs* per-logic. The benefit is modest but real: consistent API surface, reduced boilerplate per new logic, and a shared vocabulary for documentation. Don't create `HasDeductionTheorem` as a typeclass — the payoff is marginal since the proof is per-logic structural induction.

**Conflict 2: Scope of standalone modal/temporal metalogic**
- Teammates A, D: Needed for standalone library principle
- Teammate C: Critical question — user should decide scope
- Teammate B: Foundation model shows per-logic metalogic is standard

**Resolution**: Recommend standalone metalogic for Modal and Temporal as separate tasks. This aligns with CSLib's modular goals, enables independent PR submission (task 12), and follows the Foundation project's pattern. However, this is substantial new development (~1,500 lines per logic) not ported from BimodalLogic.

### Gaps Identified

1. **No tasks for standalone modal/temporal metalogic** (soundness, completeness, deduction theorem, MCS)
2. **No task for generic MCS foundations** in Foundations/Logic/Metalogic/
3. **BimodalTMHilbert → TemporalBXHilbert compatibility instance** not scoped in any task
4. **No embedding-based metalogic transfer theorems** scoped (future work, post tasks 10-11)

### Recommendations

#### Recommended Directory Structure

```
Cslib/
├── Foundations/Logic/
│   ├── Axioms.lean                   # (existing)
│   ├── Connectives.lean              # (existing)
│   ├── InferenceSystem.lean          # (existing)
│   ├── ProofSystem.lean              # (existing)
│   ├── Theorems/                     # (existing, task 20)
│   └── Metalogic/                    # NEW: Generic metalogic definitions
│       └── Consistency.lean          # SetConsistent, SetMaximalConsistent, Lindenbaum skeleton
│
├── Logics/
│   ├── Propositional/
│   │   ├── Defs.lean                 # (existing)
│   │   ├── NaturalDeduction/         # (existing) — PL uses ND, no Hilbert metalogic needed
│   │   └── Embedding.lean            # (existing)
│   │
│   ├── Modal/
│   │   ├── Basic.lean                # (existing) Kripke semantics
│   │   ├── ProofSystem/              # (task 21) Modal.DerivationTree
│   │   ├── Theorems/                 # (task 21) S4/S5 derived theorems
│   │   └── Metalogic/               # NEW TASK: Standalone modal metalogic
│   │       ├── DeductionTheorem.lean
│   │       ├── MCS.lean
│   │       ├── Soundness.lean        # Soundness over Kripke frames
│   │       └── Completeness.lean     # Canonical Kripke model completeness
│   │
│   ├── Temporal/
│   │   ├── Syntax/                   # (existing)
│   │   ├── ProofSystem/              # (task 22) Temporal.DerivationTree
│   │   ├── Theorems/                 # (task 22) Temporal derived theorems
│   │   ├── Semantics/                # (task 23) Models on LinearOrder
│   │   └── Metalogic/               # NEW TASK: Standalone temporal metalogic
│   │       ├── DeductionTheorem.lean
│   │       ├── MCS.lean
│   │       ├── Soundness.lean        # Soundness over linear orders
│   │       └── Completeness.lean     # Canonical linear model completeness
│   │
│   └── Bimodal/
│       ├── Syntax/                   # (existing)
│       ├── Embedding/                # (existing)
│       ├── Semantics/                # (task 3)
│       ├── ProofSystem/              # (task 4)
│       ├── Theorems/                 # (task 5)
│       └── Metalogic/               # (tasks 6-11, correctly scoped)
│           ├── Core/                 # DeductionTheorem, MCS, MCSProperties
│           ├── Soundness.lean
│           ├── SoundnessLemmas/
│           ├── Completeness.lean
│           ├── Bundle/
│           ├── BXCanonical/
│           ├── Algebraic/
│           ├── Decidability/
│           ├── ConservativeExtension/
│           └── WeakCanonical/
```

#### Import Hierarchy

```
Foundations/Logic/Metalogic/        (generic definitions only)
       ↓               ↓
Modal/Metalogic/     Temporal/Metalogic/    (independent, no cross-import)
       ↓                       ↓
            Bimodal/Metalogic/              (imports both via embeddings)
```

#### Task Recommendations

**No existing tasks need revision** — tasks 3-11 and 20-23 are correctly scoped for their current content.

**New tasks needed**:

1. **Generic MCS Foundations** (Small, ~300 lines): Add `Cslib/Foundations/Logic/Metalogic/Consistency.lean` with generic consistency/MCS definitions and Lindenbaum lemma skeleton. This reduces scope of bimodal task 7 and provides foundation for modal/temporal metalogic.

2. **Modal Metalogic** (Large, ~1,500 lines, new development): Create `Modal.DeductionTheorem`, `Modal.MCS`, `Modal.Soundness` (over Kripke semantics), and `Modal.Completeness` (canonical Kripke model for S5). Depends on task 21 (modal proof system). Not a port — new formalization.

3. **Temporal Metalogic** (Large, ~1,500 lines, new development): Create `Temporal.DeductionTheorem`, `Temporal.MCS`, `Temporal.Soundness` (over linear orders), and `Temporal.Completeness`. Depends on tasks 22 + 23 (temporal proof system + semantics). Not a port — new formalization.

4. **BimodalTMHilbert → TemporalBXHilbert Compatibility Instance** (Small, ~50-100 lines): Create an explicit instance so temporal theorems apply to bimodal proofs. Could be folded into task 22 or a standalone fix.

5. **Embedding-Based Metalogic Transfer** (Medium, future): Once standalone metalogic exists at each level and conservative extension (task 11) is complete, prove transfer theorems connecting the levels. Low priority but high strategic value.

#### Approach Summary: "Share Definitions, Not Proofs"

The right abstraction level for metalogic across logics is:
- **Share**: Definitions (Consistent, MCS, Lindenbaum), vocabulary, directory structure patterns
- **Don't share**: Proof strategies (deduction theorem, soundness, completeness, decidability)
- **Don't over-abstract**: No `HasDeductionTheorem` typeclass, no generic soundness framework
- **Future layer**: Embedding-based transfer theorems (post tasks 10-11)

This follows the Foundation project's validated pattern and aligns with CSLib's modular architecture goals.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary structure analysis | completed | high |
| B | Alternative approaches & prior art | completed | high |
| C | Critical assessment & gaps | completed | high |
| D | Strategic alignment & horizons | completed | high |

## References

- FormalizedFormalLogic/Foundation (Lean 4 multi-logic library): Validates shared typeclass + per-logic metalogic pattern
- LeanLTL (ITP 2025): Parameterized temporal logic unification framework
- Mathlib algebraic hierarchy: Forgetful inheritance and instance transfer patterns
- BimodalLogic `Metalogic/Core/` (1,360 lines): DeductionTheorem + MCS source analysis
- CSLib `Foundations/Logic/ProofSystem.lean`: Existing typeclass hierarchy analysis
- Task 20 research report: Established "DeductionTheorem stays per-logic" precedent
