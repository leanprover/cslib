# Research Report: Task #60

**Task**: pr2_modal_metalogic
**Date**: 2026-06-10
**Mode**: Team Research (4 teammates)

## Summary

The Hilbert modal logic (S5) and temporal logic (BX) implementations are **complete and sorry-free**, with full metalogical pipelines (soundness, completeness, deduction theorem, MCS theory). The modal logic is a compact, well-documented module (~1,800 lines, 10 files) ready for PR submission with minor improvements. Key findings: (1) the modal Cube defines 15 systems semantically but only S5 has a proof system and metalogic; (2) Modal lacks typeclass instance registration (`Instances.lean`), making it the only logic not bridged to the abstract `ProofSystem` hierarchy; (3) `HilbertDerivedRules.lean` is untracked/unimported and needs a decision; (4) no sorry in Modal or Temporal, 25 in Bimodal (out of scope).

## Key Findings

### Primary Approach (from Teammate A)

**Modal Logic (S5)**: Complete metalogic with zero sorry across ~1,800 lines:
- **Axioms**: K, T, 4, B (equivalent to S5 on reflexive + transitive + Euclidean frames)
- **Semantics** (`Basic.lean`, 394 lines): Model, Proposition, Satisfies with full characterization theorems for all connectives. Axiom ↔ frame property correspondences for K, T, B, 4, 5, D.
- **Modal Cube** (`Cube.lean`, 140 lines): All 15 standard systems defined semantically (K, D, T, B, Four, Five, K45, D4, D5, D45, DB, TB, KB5, S4, S5) with ordering proofs and validity theorems.
- **Metalogic** (5 files, ~1,100 lines): DerivationTree (Type-level, 5 constructors), DeductionTheorem (well-founded recursion on height), MCS (full Lindenbaum + modal-specific properties), Soundness (structural induction), Completeness (canonical model construction).
- **Denotation** (`Denotation.lean`, 85 lines): Formula-to-set mapping with characterization.
- **Embedding** (`FromPropositional.lean`, 56 lines): PL → Modal with coercion and simp lemmas.

**Temporal Logic (BX)**: Complete metalogic with zero sorry:
- 26 axiom constructors (4 propositional + 22 temporal BX1-BX13 with duals)
- Full chronicle limit construction across 11 modules on ℚ subtype
- DeductionTheorem, MCS, Soundness, Completeness all proven
- `Instances.lean` registers all typeclass instances (unlike Modal)

**Propositional**: Complete foundation layer with:
- Core definitions, 4 axiom schemata, derivation trees
- Natural deduction system with Hilbert ↔ ND equivalence
- **New `HilbertDerivedRules.lean`** (447 lines, sorry-free, untracked): derived intro/elim rules for all Lukasiewicz-encoded connectives

### Alternative Approaches (from Teammate B)

**Critical Gap — Missing `Instances.lean` for Modal**:
- Propositional registers `ClassicalHilbert` for `HilbertCl`
- Temporal registers `TemporalBXHilbert` for `HilbertBX`
- Bimodal registers `BimodalTMHilbert` for `HilbertTM`
- **Modal has no instance registration** — tag types `HilbertK` and `HilbertS5` are defined in `ProofSystem.lean` but never instantiated
- Consequence: generic theorems in `Foundations/Logic/Theorems/Modal/` cannot be applied to the concrete derivation tree
- This is the most significant architectural gap for the PR

**Naming Inconsistency**: Modal/Propositional use `Proposition`; Temporal/Bimodal use `Formula`. Low impact but worth noting.

**Cube.lean is Semantics-Only**: No bridge to syntactic derivability. Individual axiom ↔ frame property correspondences exist in `Basic.lean` but aren't connected to the Cube definitions.

**Documentation Quality**: Strong across all files — module docstrings with Main Results, Design, and References sections. Minor issue: some docstrings reference old `BimodalLogic/` paths.

### Gaps and Shortcomings (from Critic)

**Sorry Audit** (exhaustive):
| Logic | Sorry Count | Status |
|-------|-------------|--------|
| Propositional | 0 | Clean |
| Modal | 0 | Clean |
| Temporal | 0 | Clean |
| Bimodal | 25 | All documented, blocked on tasks 36/37 |

**Completeness Coverage**:
| System | Soundness | Completeness | Notes |
|--------|-----------|--------------|-------|
| Modal S5 | Yes | Yes | Full canonical model |
| Temporal BX | Yes | Yes | Chronicle construction |
| Bimodal TM | Yes | Partial | 25 sorries in BXCanonical/Bundle |
| K, T, D, S4, etc. | No | No | Semantic only in Cube.lean |

**PR Blockers Identified**:
1. `HilbertDerivedRules.lean` — untracked and unimported (decision needed)
2. Architectural inconsistency: Modal uses concrete `DerivationTree` without typeclass instances, unlike Temporal/Bimodal
3. No `lake build` verification performed during this review
4. No test/example files for modal logic

### Strategic Horizons (from Horizons)

**PR Scope**: Modal only (`Cslib/Logics/Modal/`, 10 files) is the right cohesive unit. Temporal is covered by PRs 3-6 (tasks 61-64). The PR sequence (59→60→61→62→63→64) from foundations through modal to temporal is well-designed.

**Dual Proof System Architecture**: Two independent systems exist:
1. Concrete `DerivationTree` in `Logics/Modal/Metalogic/` — used for actual proofs
2. Typeclass-based `ProofSystem` in `Foundations/Logic/ProofSystem.lean` — defines interface only

These are not connected. The module docstring in `ProofSystem.lean` acknowledges this: "defines the **interface** only. Concrete instances require derivation trees ... and are future work."

**Expansion Opportunities** (post-PR):
1. Connect ProofSystem typeclasses to DerivationTree (unlock generic theorems)
2. Parameterize axiom sets for K/T/S4 completeness
3. Epistemic logic (S5 is already there, needs framing)
4. Deontic logic (KD — serial frame completeness)
5. Provability logic (GL — substantially different)

**Codebase Scale**:
| Logic | Files | Lines |
|-------|-------|-------|
| Propositional | 11 | ~2,300 |
| Modal | 10 | ~1,800 |
| Temporal | 35 | ~13,800 |
| Bimodal | 127 | ~51,200 |

## Synthesis

### Conflicts Resolved

**1. Missing Instances — Priority for PR?**
- Teammate B: Priority 1 — create `Instances.lean` before PR (the "most significant gap")
- Teammate D: Post-PR roadmap item ("Do NOT include typeclass wiring")
- **Resolution**: This is a judgment call for the PR author. Creating `Instances.lean` is straightforward (follows the Propositional/Temporal pattern exactly) and would resolve the only architectural inconsistency across logics. However, the metalogic works correctly without it — the gap is about typeclass integration, not correctness. **Recommend: include if feasible, document as known limitation if not.**

**2. PR Scope — Modal only vs Modal + Temporal?**
- Teammate A: Reviews both Modal and Temporal extensively
- Teammate D: Recommends Modal only for PR2
- **Resolution**: The task is named "pr2_modal_metalogic" and the roadmap shows Temporal in PRs 3-6 (tasks 61-64). **PR2 should scope to Modal only.** The Temporal review is valuable context for later PRs.

**3. HilbertDerivedRules.lean — Include or Exclude?**
- All teammates flag this file as needing a decision
- **Resolution**: The file is sorry-free and provides useful infrastructure. Since it's in `Propositional/NaturalDeduction/` (not `Modal/`), it's technically out of PR2's modal scope. **Recommend: either include with an import in a prior/concurrent PR, or explicitly defer.**

### Gaps Identified

1. **Build verification**: No `lake build` was run during this review. Must verify before PR submission.
2. **Test coverage**: No example files demonstrating modal S5 derivations exist.
3. **Stale cross-references**: Some docstrings reference old `BimodalLogic/` paths that should be updated to `cslib` paths.
4. **Modal Cube ↔ Proof System bridge**: The 15 semantically-defined systems in `Cube.lean` have no syntactic counterparts. This is substantial future work, not a PR blocker.

### Recommendations

**Before PR submission (blocking)**:
1. Run `lake build` to verify Modal subtree compiles cleanly
2. Decide on `HilbertDerivedRules.lean`: include + import, or exclude
3. Document S5-only scope clearly in `Metalogic.lean` module docstring

**Before PR submission (recommended)**:
4. Create `Modal/ProofSystem/Instances.lean` to bridge concrete and abstract systems (follows established pattern from Temporal/Bimodal)
5. Update any stale `BimodalLogic/` cross-references in docstrings

**Post-PR roadmap**:
6. Parameterize `ModalAxiom` to enable K/T/S4 completeness
7. Bridge `Cube.lean` semantic definitions to syntactic proof systems
8. Explore epistemic/deontic/provability logic extensions
9. Add Modal → Temporal embedding (currently only via Bimodal)

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary implementation review | completed | high |
| B | Infrastructure & architecture | completed | high |
| C | Critic — gaps & blockers | completed | high |
| D | Strategic horizons | completed | high |

## References

- `Cslib/Logics/Modal/Metalogic/Completeness.lean:221` — Main completeness theorem
- `Cslib/Logics/Modal/Metalogic/Soundness.lean:103` — Main soundness theorem
- `Cslib/Logics/Modal/Cube.lean` — All 15 modal systems
- `Cslib/Logics/Modal/Basic.lean:246-381` — Axiom ↔ frame correspondences
- `Foundations/Logic/ProofSystem.lean:296-309` — Uninstantiated `ModalS5Hilbert` typeclass
- `Foundations/Logic/Theorems/Modal/S5.lean` — Generic S5 theorems (not connected to DerivationTree)
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean:101` — Temporal completeness
