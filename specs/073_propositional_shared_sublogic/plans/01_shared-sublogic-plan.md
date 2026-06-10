# Implementation Plan: Task #73

- **Task**: 73 - Make Propositional a shared sub-logic for Modal and Temporal
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: Task 72 (completed -- relocated Propositional/Embedding)
- **Research Inputs**: specs/073_propositional_shared_sublogic/reports/01_shared-sublogic-research.md
- **Artifacts**: plans/01_shared-sublogic-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Establish Propositional as a genuine intermediate dependency layer in the import graph so that Modal and Temporal explicitly build on Propositional rather than importing only from Foundations. Currently, `PL.Proposition.toModal` and `PL.Proposition.toTemporal` live in `Bimodal/Embedding/PropositionalEmbedding.lean`. This plan relocates those embeddings into the target logic modules (`Modal/FromPropositional.lean`, `Temporal/FromPropositional.lean`), making Modal and Temporal directly import from Propositional. The Bimodal embedding file is then simplified to re-export from the new locations. This achieves the desired import DAG: `Foundations -> Propositional -> {Modal, Temporal} -> Bimodal`.

### Research Integration

The research report (01_shared-sublogic-research.md) identified five phases. Phases 1-3 (embedding relocation, Modal imports PL, Temporal imports PL) are low-to-medium risk and establish the dependency flow. Phases 4-5 (eliminate duplicated PropositionalHelpers, register Modal proof system instances) are medium-high risk and deferred to a follow-up task. The research confirmed that Lean 4 cannot extend inductives, so each formula type keeps its own constructors -- "shared sub-logic" means shared import layer with coercions, not literal type inheritance.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

Advances the ROADMAP.md architecture goal: "Propositional, Modal, and Temporal are independent peers that each import only from Foundations." This plan upgrades Propositional from an isolated peer to a genuine intermediate layer that Modal and Temporal build on, strengthening the import hierarchy.

## Goals & Non-Goals

**Goals**:
- Create `Modal/FromPropositional.lean` containing `PL.Proposition.toModal`, its `Coe` instance, and simp lemmas
- Create `Temporal/FromPropositional.lean` containing `PL.Proposition.toTemporal`, its `Coe` instance, and simp lemmas
- Simplify `Bimodal/Embedding/PropositionalEmbedding.lean` to import from the new locations instead of defining embeddings inline
- Achieve import flow: `Foundations -> Propositional -> {Modal, Temporal} -> Bimodal`
- Pass `lake build` with zero errors after all changes

**Non-Goals**:
- Unifying the inductive types (impossible in Lean 4)
- Eliminating duplicated propositional helpers in Temporal metalogic (follow-up task)
- Registering Modal proof system instances with Foundations typeclasses (follow-up task)
- Modifying any inductive type definitions

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Notation conflicts when Modal/Temporal open PL scope | M | M | Use qualified names; do not open PL scope in Modal/Temporal files |
| Import cycle if embedding placed incorrectly | H | L | Embeddings flow one-way: PL->Modal lives in Modal/, PL->Temporal lives in Temporal/ |
| Bimodal downstream breakage from moved definitions | M | L | Bimodal file re-imports from new locations; all names stay in `Cslib.Logic` namespace |
| Build time regression from added import edges | L | L | PL/Defs.lean is small (~163 lines); impact negligible |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Create Modal/FromPropositional.lean [NOT STARTED]

**Goal**: Move the PL-to-Modal embedding from Bimodal into the Modal module, making Modal explicitly depend on Propositional.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/FromPropositional.lean` with `module` keyword
- [ ] Add imports: `public import Cslib.Logics.Propositional.Defs` and `public import Cslib.Logics.Modal.Basic`
- [ ] Move `PL.Proposition.toModal` definition (recursive function on atom/bot/imp)
- [ ] Move `instCoePLToModal` coercion instance
- [ ] Move simp lemmas: `toModal_atom`, `toModal_bot`, `toModal_imp`, `toModal_neg`
- [ ] Verify with `lake build Cslib.Logics.Modal.FromPropositional`

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/FromPropositional.lean` - NEW: PL->Modal embedding
- `Cslib/Logics/Modal/Metalogic.lean` - ADD import of FromPropositional (if barrel file exists)

**Verification**:
- `lake build Cslib.Logics.Modal.FromPropositional` compiles without errors
- `PL.Proposition.toModal` is accessible from the new module

---

### Phase 2: Create Temporal/FromPropositional.lean [NOT STARTED]

**Goal**: Move the PL-to-Temporal embedding from Bimodal into the Temporal module, making Temporal explicitly depend on Propositional.

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/FromPropositional.lean` with `module` keyword
- [ ] Add imports: `public import Cslib.Logics.Propositional.Defs` and `public import Cslib.Logics.Temporal.Syntax.Formula`
- [ ] Move `PL.Proposition.toTemporal` definition (recursive function on atom/bot/imp)
- [ ] Move `instCoePLToTemporal` coercion instance
- [ ] Move simp lemmas: `toTemporal_atom`, `toTemporal_bot`, `toTemporal_imp`, `toTemporal_neg`
- [ ] Verify with `lake build Cslib.Logics.Temporal.FromPropositional`

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/FromPropositional.lean` - NEW: PL->Temporal embedding
- `Cslib/Logics/Temporal/Metalogic.lean` - ADD import of FromPropositional (if barrel file exists)

**Verification**:
- `lake build Cslib.Logics.Temporal.FromPropositional` compiles without errors
- `PL.Proposition.toTemporal` is accessible from the new module

---

### Phase 3: Refactor Bimodal/Embedding/PropositionalEmbedding.lean [NOT STARTED]

**Goal**: Replace inline embedding definitions with imports from the new Modal and Temporal files. Keep `toBimodal` and the commuting diagram theorems in Bimodal.

**Tasks**:
- [ ] Update imports in `PropositionalEmbedding.lean`: replace direct Modal/Temporal formula imports with `Cslib.Logics.Modal.FromPropositional` and `Cslib.Logics.Temporal.FromPropositional`
- [ ] Remove the `toModal` and `toTemporal` definitions (now imported)
- [ ] Remove the `Coe` instances for PL->Modal and PL->Temporal (now imported)
- [ ] Remove the simp lemmas for `toModal_*` and `toTemporal_*` (now imported)
- [ ] Keep `toBimodal`, `instCoePLToBimodal`, `toBimodal_*` lemmas, and commuting diagram theorems (`toModal_toBimodal`, `toTemporal_toBimodal`, `embedding_commutes`)
- [ ] Verify the commuting diagram theorems still compile (they depend on `toModal` and `toTemporal` which are now imported)
- [ ] Run `lake build Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding`

**Timing**: 1.0 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` - MODIFY: remove moved definitions, update imports

**Verification**:
- `lake build Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding` compiles without errors
- Commuting diagram theorems (`embedding_commutes`) still hold
- All downstream Bimodal files that use `toModal`/`toTemporal` still compile

---

### Phase 4: Full Build and Cslib.lean Update [NOT STARTED]

**Goal**: Ensure the full project builds and the new modules are properly registered.

**Tasks**:
- [ ] Run `lake exe mk_all` to update `Cslib.lean` with the two new module files
- [ ] Run full `lake build` to verify zero errors across all modules
- [ ] Run `lake shake` to verify no unused imports in the new files
- [ ] Verify the import graph is correct: `grep -n "import.*Propositional" Cslib/Logics/Modal/FromPropositional.lean Cslib/Logics/Temporal/FromPropositional.lean` shows Propositional imports
- [ ] Verify no reverse imports: `grep -rn "import.*Modal\|import.*Temporal" Cslib/Logics/Propositional/` shows zero results

**Timing**: 1.5 hours (includes build time and debugging)

**Depends on**: 3

**Files to modify**:
- `Cslib.lean` - AUTO: updated by `lake exe mk_all`

**Verification**:
- `lake build` passes with zero errors
- `lake shake` reports no unused imports in new files
- No import from Propositional/ to Modal/ or Temporal/ (only the reverse direction)
- `grep -c "import.*Propositional" Cslib/Logics/Modal/FromPropositional.lean` returns 1
- `grep -c "import.*Propositional" Cslib/Logics/Temporal/FromPropositional.lean` returns 1

## Testing & Validation

- [ ] `lake build` passes with zero errors
- [ ] `lake shake` reports no unused imports in new files
- [ ] Import graph verification: Modal and Temporal import from Propositional (not vice versa)
- [ ] All existing tests and proofs continue to compile
- [ ] `PL.Proposition.toModal` is accessible via `import Cslib.Logics.Modal.FromPropositional`
- [ ] `PL.Proposition.toTemporal` is accessible via `import Cslib.Logics.Temporal.FromPropositional`
- [ ] Commuting diagram (`embedding_commutes`) still holds in Bimodal
- [ ] No `sorry` introduced

## Artifacts & Outputs

- `Cslib/Logics/Modal/FromPropositional.lean` - NEW: PL->Modal embedding with Coe and simp lemmas
- `Cslib/Logics/Temporal/FromPropositional.lean` - NEW: PL->Temporal embedding with Coe and simp lemmas
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` - MODIFIED: simplified to import from above
- `specs/073_propositional_shared_sublogic/plans/01_shared-sublogic-plan.md` - This plan
- `specs/073_propositional_shared_sublogic/summaries/01_shared-sublogic-summary.md` - Execution summary (created at implementation time)

## Rollback/Contingency

All changes are additive file creation plus import refactoring in one existing file. To rollback:
1. Delete `Cslib/Logics/Modal/FromPropositional.lean`
2. Delete `Cslib/Logics/Temporal/FromPropositional.lean`
3. Restore `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` from git
4. Run `lake exe mk_all` and `lake build`

If the Bimodal commuting diagram theorems fail to compile with imported definitions (unlikely since the definitions are identical), the fallback is to keep the definitions in PropositionalEmbedding.lean and add re-export imports in Modal/Temporal instead (weaker layering but still achieves the import edge).
