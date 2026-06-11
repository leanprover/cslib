# Teammate B Findings: Infrastructure, Architecture, and Code Quality

**Task**: 60 — pr2_modal_metalogic
**Date**: 2026-06-10
**Angle**: Alternative Approaches — Infrastructure Review

## Key Findings

### 1. Naming Inconsistency: `Proposition` vs `Formula`

The **Modal** logic uses `Modal.Proposition` as its formula type (in `Basic.lean`), while both **Temporal** and **Bimodal** logics use `Formula` (in `Temporal.Syntax.Formula` and `Bimodal.Syntax.Formula`). Similarly, the **Propositional** layer uses `PL.Proposition`.

This is a design choice worth flagging: `Proposition` and `Formula` are used as synonyms within the codebase. The Modal logic uniquely refers to its formula type as `Proposition`, which may confuse readers who see `Modal.Proposition` and `Temporal.Formula` side by side in embeddings.

**Impact**: Low — both are standard mathematical terms. However, for a PR the inconsistency in naming conventions between logics at the same abstraction level (Modal vs Temporal) is worth noting.

### 2. Missing `Modal.HilbertS5` Instance Registration

The **Propositional** logic registers `ClassicalHilbert` instances for its `Propositional.HilbertCl` tag type. The **Temporal** logic registers `TemporalBXHilbert` for `Temporal.HilbertBX`. The **Bimodal** logic registers `BimodalTMHilbert` for `Bimodal.HilbertTM`.

However, the **Modal** logic has **no** instance registration for `Modal.HilbertK` or `Modal.HilbertS5` through the abstract proof system hierarchy. The tag types are defined in `ProofSystem.lean` but never instantiated. The modal metalogic (soundness/completeness) uses only its concrete `modalDerivationSystem` instance of the `Metalogic.DerivationSystem` class — a different, lower-level abstraction.

This means:
- No `InferenceSystem Modal.HilbertS5 (Modal.Proposition Atom)` instance exists
- No `ModalS5Hilbert Modal.HilbertS5` instance exists
- The rich generic theorem library in `Foundations/Logic/Theorems/Modal/` (which works over abstract `ModalHilbert S` / `ModalS5Hilbert S`) cannot be instantiated for the concrete modal derivation tree
- The `Cube.lean` cannot use typeclass-based theorem reuse

**This is the most significant gap for the PR.** Adding an `Instances.lean` file for Modal (parallel to `Propositional/ProofSystem/Instances.lean` and `Temporal/ProofSystem/Instances.lean`) would unify the modal proof system with the typeclass hierarchy.

### 3. No `sorry` in Modal or Temporal

Zero `sorry` occurrences in `Cslib/Logics/Modal/` and `Cslib/Logics/Temporal/`. All proofs are complete. The only `sorry` instances in the `Logics/` directory are in the **Bimodal** metalogic (blocked on tasks 36 and 37 for advanced completeness work — these are out of scope for this PR).

### 4. Well-Structured Proof System Architecture

The architecture follows a clean layered design:

| Layer | Location | Purpose |
|-------|----------|---------|
| Connective typeclasses | `Foundations/Logic/Connectives.lean` | `PropositionalConnectives`, `ModalConnectives`, etc. |
| Axiom definitions | `Foundations/Logic/Axioms.lean` | Generic axiom formulas |
| Proof system typeclasses | `Foundations/Logic/ProofSystem.lean` | `ClassicalHilbert`, `ModalS5Hilbert`, etc. |
| Generic theorems | `Foundations/Logic/Theorems/` | Reusable theorems over abstract systems |
| Concrete derivation trees | `Logics/*/Metalogic/DerivationTree.lean` | Logic-specific proof trees |
| MCS framework | `Foundations/Logic/Metalogic/Consistency.lean` | Generic Lindenbaum / MCS |
| Concrete metalogic | `Logics/*/Metalogic/` | Soundness, completeness |

This architecture is sound and well-executed. The only gap is the missing Modal → typeclass bridge (Finding #2).

### 5. Model Naming Divergence

- Modal: `Model World Atom` (a bare structure)
- Temporal: `TemporalModel D Atom` (prefixed with `Temporal`)

The `Temporal` prefix is redundant given the namespace `Cslib.Logic.Temporal`. The Modal version uses the cleaner pattern. This is a minor cosmetic issue.

### 6. Cube.lean Frame Condition Definitions Are Semantics-Based, Not Proof-System-Based

The `Cube.lean` file defines modal logics (K, T, D, S4, S5, etc.) as semantic objects — sets of valid formulas over specific model classes. The relationships are proven via set inclusions.

This is a valid approach but stands in contrast with the metalogic, which is entirely syntactic (Hilbert derivation trees). There's no bridge connecting the semantic cube definitions to syntactic derivability. For instance, `K.k_valid` proves the K axiom is semantically valid in K, but there's no corresponding `K.k_derivable` proving it's derivable in the K proof system.

The soundness/completeness theorems in `Metalogic/` only cover S5. A full cube verification would need soundness/completeness for each system.

### 7. Duplicated Derived Connective Definitions

Each formula type (PL.Proposition, Modal.Proposition, Temporal.Formula) independently defines `neg`, `top`, `or`, `and` as `abbrev`s with identical Lukasiewicz encodings. The `LukasiewiczDerived` typeclass in `Connectives.lean` was designed for this but is "intentionally uninstantiated" per its docstring.

This is defensible (each formula type's `abbrev`s unfold to their own constructors, which helps `simp`), but the duplication across 4 formula types is worth noting. No action needed, but it's a conscious architecture trade-off.

### 8. Proof Style Consistency

The Modal metalogic uses a consistent style:
- `DerivationTree` is `Type`-valued (for pattern matching and height functions)
- `Deriv` is the `Prop`-level `Nonempty` wrapper
- The deduction theorem uses well-founded recursion on `height`
- MCS properties follow the generic framework pattern

This matches the Temporal and Bimodal metalogic patterns closely. The style is consistent across all three logics.

### 9. Missing Modal Temporal/Tense Logic Connection

The Modal metalogic proves S5 completeness but doesn't establish any relationship to the Temporal logic. There's no embedding `Modal.Proposition → Temporal.Formula` (only `PL.Proposition → Modal.Proposition` and `PL.Proposition → Temporal.Formula`). The Bimodal logic has `ModalEmbedding.lean` and `TemporalEmbedding.lean` linking both into its unified framework, but a direct Modal ↔ Temporal relationship (e.g., S5 as a fragment of BX temporal logic) is absent.

### 10. Documentation Quality

Documentation is strong:
- Every file has a module docstring with `## Main Results` / `## Design` sections
- Key theorems have inline docstrings
- Cross-references to related files are included
- Copyright headers are present and consistent

Minor note: Some docstrings reference "BimodalLogic" paths that appear to be from an older project structure (e.g., `BimodalLogic/Theories/Bimodal/ProofSystem/Derivation.lean`). These should be updated to current cslib paths.

## Recommended Approach

**Priority 1 (before PR)**: Create `Cslib/Logics/Modal/ProofSystem/` with `Instances.lean` that registers `InferenceSystem`, `ModalS5Hilbert`, and all `HasAxiom*` instances for `Modal.HilbertS5`. This is the critical missing piece that connects the modal concrete system to the abstract typeclass hierarchy. The pattern is established by Propositional, Temporal, and Bimodal — modal is the only logic that lacks this bridge.

**Priority 2 (before PR)**: Update stale cross-references in docstrings (BimodalLogic paths → cslib paths).

**Priority 3 (post-PR, roadmap)**: Consider adding `Modal.HilbertK` instances as well, which would enable theorems from `Foundations/Logic/Theorems/Modal/Basic.lean` to be instantiated at the K level (not just S5).

**Priority 4 (post-PR, roadmap)**: Bridge between semantic `Cube.lean` definitions and syntactic proof systems. This is a substantial undertaking (soundness/completeness for each cube system) but would significantly enhance the mathematical value.

## Evidence/Examples

### Missing Instance Pattern (Finding #2)

Propositional has:
```
-- Cslib/Logics/Propositional/ProofSystem/Instances.lean
instance : InferenceSystem Propositional.HilbertCl (PL.Proposition Atom)
instance : ClassicalHilbert Propositional.HilbertCl (F := PL.Proposition Atom)
```

Temporal has:
```
-- Cslib/Logics/Temporal/ProofSystem/Instances.lean
instance : InferenceSystem Temporal.HilbertBX (Temporal.Formula Atom)
instance : TemporalBXHilbert Temporal.HilbertBX (F := Temporal.Formula Atom)
```

Modal lacks any equivalent. The tag types `Modal.HilbertK` and `Modal.HilbertS5` exist in `ProofSystem.lean` but have no instances.

### Naming Inconsistency (Finding #1)

```lean
-- Modal: uses "Proposition"
inductive Proposition (Atom : Type u) : Type u where  -- Modal/Basic.lean:46

-- Temporal: uses "Formula"
inductive Formula (Atom : Type u) : Type u where      -- Temporal/Syntax/Formula.lean:35

-- Bimodal: uses "Formula"
inductive Formula (Atom : Type u) : Type u where      -- Bimodal/Syntax/Formula.lean:32

-- Propositional: uses "Proposition"
inductive Proposition (Atom : Type u) : Type u where   -- Propositional/Defs.lean:48
```

Pattern: {Propositional, Modal} use `Proposition`; {Temporal, Bimodal} use `Formula`.

## Confidence Level

- **Finding #2 (Missing HilbertS5 instances)**: **High** — verified by searching all `.lean` files for `HilbertK`/`HilbertS5` usage and finding zero instances outside `ProofSystem.lean` definitions
- **Finding #3 (No sorry)**: **High** — confirmed by grep across all Modal and Temporal files
- **Finding #1 (Naming)**: **High** — directly observed in source
- **Finding #6 (Cube gap)**: **Medium** — correct observation, but the scope of remediation is large
- **Finding #9 (Modal-Temporal connection)**: **Medium** — absence confirmed, but may be intentionally out of scope
