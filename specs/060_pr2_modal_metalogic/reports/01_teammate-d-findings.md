# Teammate D (Horizons) Findings — Task 60: pr2_modal_metalogic

**Date**: 2026-06-10
**Angle**: Strategic Direction and Long-Term Vision

## Key Findings

### 1. Modal Cube Coverage: Comprehensive but Only S5 Has Metalogic

The **Cube.lean** file defines all 15 standard modal logics (K, D, T, B, Four, Five, K45, D4, D5, D45, DB, TB, KB5, S4, S5) as sets of valid propositions over the corresponding frame classes. Ordering theorems (e.g., `k_subset_d`, `d_subset_t`) and validity proofs (e.g., `K.k_valid`, `T.t_valid`) are provided.

However, the **metalogical infrastructure** (DerivationTree, DeductionTheorem, MCS, Soundness, Completeness) exists **only for S5**. The axiom set in `ModalAxiom` is hard-coded with all four modal axioms (K, T, 4, B) — there is no parameterization that would allow, e.g., proving completeness for K alone, or for T, or for S4. This is a deliberate and reasonable design choice for the current PR scope, but it means:

- **K, D, T, B, S4**: No Hilbert proof system, no soundness/completeness.
- **S5**: Full metalogic pipeline (Derivation → Deduction Theorem → MCS → Soundness → Completeness).

### 2. Architecture: Well-Stratified but Dual Proof Systems

There are two independent proof system architectures:

1. **Concrete DerivationTree** (in `Logics/Modal/Metalogic/`): An explicit inductive type with pattern-matchable constructors. Used for the actual metalogic proofs (completeness, soundness). S5-specific.

2. **Typeclass-based ProofSystem** (in `Foundations/Logic/ProofSystem.lean`): A hierarchy of typeclasses (`ModalHilbert`, `ModalS5Hilbert`, etc.) with tag types (`Modal.HilbertK`, `Modal.HilbertS5`). Used for the generic theorems in `Foundations/Logic/Theorems/Modal/`. The module docstring says "defines the **interface** only. Concrete instances require derivation trees ... and are future work."

**These two systems are not connected.** The concrete `DerivationTree` does not register `ModalS5Hilbert` instances. The generic theorems in `Foundations/Logic/Theorems/Modal/` are parameterized over `[ModalS5Hilbert S]` and cannot be invoked with the concrete S5 system. This is acknowledged as future work but represents a significant gap.

### 3. Modal Logic Is Sorry-Free

Zero `sorry`s across all Modal and Temporal files. All proofs are complete. This is a strong signal of quality.

### 4. Relationship Between Logics Is Well-Structured

- **Propositional → Modal**: `FromPropositional.lean` provides the embedding with a `Coe` instance and preservation simp lemmas.
- **Modal → Bimodal**: `ModalEmbedding.lean` provides the embedding.
- **Temporal → Bimodal**: `TemporalEmbedding.lean` provides the embedding.
- **Propositional → Bimodal**: Direct path plus commutativity proof (`embedding_commutes`).
- **Shared Infrastructure**: Generic MCS framework in `Foundations/Logic/Metalogic/Consistency.lean` is used by both Modal and Temporal metalogic via `modalDerivationSystem` and the analogous temporal instance.

### 5. PR Sequencing in the Roadmap Makes Sense

The PR sequence (59→60→61→62→63→64) progresses from foundations through modal to temporal to bimodal. Task 60 covers `Logics/Modal/` which is the right unit:

| PR | Content | Status |
|----|---------|--------|
| PR1 (86) | Lint/quality audit | completed |
| **PR2 (60)** | **Modal metalogic** | **researching** |
| PR3 (61) | Temporal proof system | not_started |
| PR4 (62) | Temporal metalogic core | not_started |
| PR5 (63) | Chronicle infrastructure | not_started |
| PR6 (64) | Completeness theorem | not_started |

### 6. Temporal Logic Is Much Larger and More Complex

Temporal metalogic has 22 files including the Chronicle sub-pipeline (11 files). The bimodal metalogic has 80+ files. These are correctly scoped into later PRs. Modal (10 files) is a natural standalone PR.

### 7. Missing Semantic-Side Results for the Modal Cube

`Cube.lean` defines the logics and proves basic validity results, but there are no:
- **Frame correspondence theorems**: e.g., "K is complete w.r.t. all frames" (beyond the semantic direction shown in `Basic.lean` where axiom ↔ frame property is shown for individual axioms).
- **Definability results**: axiom T defines the class of reflexive frames, etc. Some of these are present in `Basic.lean` (e.g., `Satisfies.t_refl` shows T → reflexive, and `Satisfies.t` shows reflexive → T), but they're not connected to the Cube definitions.
- **Finite model property for K** or other systems below S5.

### 8. Natural Deduction Infrastructure

The `Propositional/NaturalDeduction/` directory (5 files including `FromHilbert.lean` and `HilbertDerivedRules.lean`) shows work connecting Hilbert and ND systems at the propositional level. The `HilbertDerivedRules.lean` file is marked as untracked (new file), suggesting it may be part of this PR's scope or a recent development from task 89.

## Recommended Approach

### For This PR (PR2): Modal Metalogic Only

**Scope**: `Cslib/Logics/Modal/` (all 10 files) plus `Cslib/Logics/Modal/FromPropositional.lean` — the complete modal logic module.

**Do NOT include**:
- Temporal logic (covered by PRs 3-6)
- Bimodal logic (much later)
- ProofSystem typeclass wiring (future work noted in the module)

### Before Submitting, Verify:

1. **No sorry** — already confirmed clean.
2. **Build succeeds** — needs `lake build` verification for Modal subtree.
3. **Naming conventions** — Modal follows `mcs_*`, `modal_*`, `canonical_*` patterns consistently.
4. **Documentation** — Module headers are excellent (references, design notes, main results sections).
5. **The `HilbertDerivedRules.lean` file** — This is an untracked file in `Propositional/NaturalDeduction/`. Decide whether to include it in PR2 or hold it for a separate commit.

### Strategic Expansion Opportunities (Post-PR)

In priority order:

1. **Connect ProofSystem typeclasses to DerivationTree**: Register `ModalS5Hilbert` instance on the concrete system. This would unlock all generic theorems for the concrete system.

2. **Parameterize over axiom sets**: Allow `ModalAxiom` to be parameterized (e.g., `ModalAxiom AxiomSet`) so that K, T, S4, S5 completeness can be proven by varying the axiom set. The current hard-coded S5 approach would need refactoring.

3. **Additional systems**:
   - **Epistemic logic**: S5 is already there — just needs naming/framing.
   - **Deontic logic (KD)**: Would need serial frame completeness (simpler than S5).
   - **Provability logic (GL)**: Would need irreflexive, transitive frames and Löb's axiom — substantially different.

4. **Finite model property for K**: The bimodal FMP infrastructure (filtration, Hintikka points) could potentially be adapted for pure modal K, but this is a significant effort.

## Evidence/Examples

- `Cube.lean:28-84` — All 15 modal logics defined
- `DerivationTree.lean:55-80` — S5-hardcoded axiom set
- `Soundness.lean:50-96` — Soundness by induction on DerivationTree
- `Completeness.lean:52-262` — Full canonical model completeness
- `ProofSystem.lean:296-309` — `ModalS5Hilbert` typeclass (uninstantiated)
- `Basic.lean:246-381` — Axiom ↔ frame property correspondences
- `Foundations/Logic/Theorems/Modal/S5.lean` — Generic S5 theorems (not connected to DerivationTree)

## Confidence Level

**High** for the PR scope and readiness assessment. The modal logic module is complete, well-documented, sorry-free, and forms a natural submission unit.

**Medium** for strategic direction. The typeclass connection and axiom parameterization recommendations are architecturally sound but would require significant refactoring effort. The expansion to epistemic/deontic/provability logics depends on research priorities that aren't fully captured in the roadmap.
