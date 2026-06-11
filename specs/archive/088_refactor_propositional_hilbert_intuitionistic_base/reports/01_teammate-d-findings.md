# Teammate D Findings: Strategic Horizons

**Task**: 88 — Refactor propositional Hilbert system to intuitionistic base
**Angle**: Long-term alignment, strategic direction, extension consistency
**Date**: 2026-06-10

## Key Findings

### 1. The Intuitionistic Base Already Exists in the ND System

The natural deduction system in `Logics/Propositional/Defs.lean` already defines `MPL` (minimal), `IPL` (intuitionistic), and `CPL` (classical) as a proper extension chain: `MPL ⊂ IPL ⊂ CPL`. It has `IsIntuitionistic` and `IsClassical` typeclasses. The task is to bring the Hilbert system into alignment with this existing layered design.

### 2. Current Hilbert Architecture Bakes in Classicality

`PropositionalHilbert` bundles ImplyK + ImplyS + EFQ + Peirce (a classical axiom) as a monolithic class. Every logic that extends it — `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert` — inherits Peirce. This is the architectural issue: no logic in the library can be non-classical, because classicality is welded into the foundation.

### 3. The Concrete Axiom Inductives Duplicate the 4 Propositional Axioms Everywhere

The same 4 propositional axiom constructors (`implyK`, `implyS`, `efq`, `peirce`) are copy-pasted into:
- `PL.PropositionalAxiom` (4 constructors)
- `Modal.ModalAxiom` (first 4 of 8 constructors)
- `Temporal.Axiom` (first 4 of 26 constructors)
- `Bimodal.Axiom` (first 4 of 42 constructors)

This means every new logic type must re-declare these same 4 constructors. An intuitionistic base would amplify this pattern: instead of 4 copies of Peirce (which could become optional), you'd want each logic to specify which propositional fragment it uses.

### 4. Roadmap Focus is Completeness, Not New Logics

The roadmap's remaining work is all about completeness theorems (dense, discrete, continuous) for temporal and bimodal logics, plus shared completeness infrastructure (task 41). There is no planned work on intuitionistic logic, intermediate logics, or non-classical propositional logics. The refactoring is about architectural correctness and future-proofing, not immediate unblocking.

## Strategic Alignment Assessment

### Advances the Project

1. **Correctness**: The extension pattern is conceptually right. Classical propositional logic *is* an extension of intuitionistic logic, just as S5 is an extension of K. Making the Hilbert system reflect this is good formal hygiene.

2. **Consistency with ND system**: The ND system already has the MPL/IPL/CPL hierarchy. The Hilbert system should mirror it.

3. **Future intuitionistic metalogic**: If the project ever pursues Kripke completeness for intuitionistic logic (a natural extension), the infrastructure would be ready.

4. **Enables intuitionistic modal logics**: There is a rich family of intuitionistic modal logics (IK, IS4, etc.) that the current architecture cannot express.

### Risks

1. **No immediate payoff**: The remaining roadmap tasks all use classical logic. This refactoring doesn't unblock anything.

2. **Theorem disruption**: All theorems in `Foundations/Logic/Theorems/` assume `[PropositionalHilbert S]` which includes Peirce. Splitting the class requires auditing every theorem to determine which are intuitionistically valid vs which need the classical extension.

3. **Concrete axiom inductives become more complex**: If `peirce` is optional, each concrete `Axiom` inductive needs a way to optionally include it (or use a sum type).

## Opportunities for Synergy

### With Task 41 (Shared Completeness Infrastructure)

An intuitionistic base would naturally separate the parts of the completeness machinery that are independent of classicality from those that require it. This could inform the abstraction boundaries for task 41.

### With Task 87 (ND ↔ Hilbert Equivalence, Completed)

The completed ND↔Hilbert equivalence (task 87) could be strengthened. Currently both systems are classical. With an intuitionistic Hilbert system, one could prove the equivalence at each level: minimal Hilbert ↔ minimal ND, intuitionistic Hilbert ↔ intuitionistic ND, classical Hilbert ↔ classical ND.

### Axiom Inductive Unification

This refactoring is the right time to address the 4× duplication of propositional axioms across concrete `Axiom` types. Two approaches:

1. **Sum type**: `Axiom F := PropositionalAxiom F ⊕ ModalAxiom F` where `PropositionalAxiom` further decomposes as `MinimalAxiom F ⊕ IntuitionisticAxiom F ⊕ ClassicalAxiom F`.

2. **Parameterized inductive**: A single axiom type parameterized by which layers are active (similar to `FrameClass` in temporal logic).

## Recommended Scope

### Minimum Viable Change (Recommended)

Split the **typeclass hierarchy** only. Don't change concrete axiom inductives yet.

```
-- NEW hierarchy:
class MinimalHilbert     -- MP + ImplyK + ImplyS
class IntuitionisticHilbert extends MinimalHilbert  -- + EFQ
class ClassicalHilbert extends IntuitionisticHilbert  -- + Peirce (or DNE)

-- Rename:
PropositionalHilbert → ClassicalHilbert  (or alias for compatibility)

-- Extension chains:
ModalHilbert extends ClassicalHilbert + Necessitation + HasAxiomK
TemporalBXHilbert extends ClassicalHilbert + ...
```

**Why this scope**: 
- It creates the right conceptual structure
- Existing concrete axiom inductives still work (they just prove `ClassicalHilbert` instead of `PropositionalHilbert`)
- Theorems can be audited and moved to the right level incrementally
- Future work can factor the concrete axiom inductives later

**Effort**: Medium. Main work is splitting theorems in `Foundations/Logic/Theorems/` between `MinimalHilbert`, `IntuitionisticHilbert`, and `ClassicalHilbert`.

### Ideal Change (Future)

All of the above, plus:
- Factor concrete axiom inductives using sum types
- Add tag types for minimal and intuitionistic systems
- Prove ND↔Hilbert at each level
- Add intuitionistic Kripke semantics

### Over-Engineering Boundary

Do NOT pursue:
- Universal formula types with connective flags
- "Logic builder" DSLs
- Substructural logic support
- These are interesting but outside the project's scope

## Confidence Level

**High** on the minimum viable change. The typeclass split is low-risk, aligns with the existing ND layering, and follows the established extension pattern. The main risk is theorem migration effort, which is mechanical and can be done incrementally.

**Medium** on the axiom inductive unification. It would reduce duplication but requires careful design to avoid Lean 4 typeclass resolution issues.

**Low** on whether this unlocks near-term value. The roadmap focuses on completeness theorems that all use classical logic. The value is architectural and forward-looking.
