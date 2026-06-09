# Implementation Plan: Task #15

- **Task**: 15 - Complete embedding lattice: atom simp lemmas, PL.toBimodal, triangle-commutes
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/015_complete_embedding_lattice/reports/01_embedding-lattice.md
- **Artifacts**: plans/01_embedding-lattice-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Add four missing `@[simp]` lemmas for the `atom` constructor across three existing embedding files, create a new `PropositionalEmbedding.lean` file providing the direct PL-to-Bimodal embedding path with Coe instance and simp lemmas, and prove the triangle-commutation lemma showing that both composite paths from PL to Bimodal agree. All proofs are definitional equalities (`rfl`) or simple structural inductions closed by `simp`.

### Research Integration

Integrated findings from `specs/015_complete_embedding_lattice/reports/01_embedding-lattice.md`:
- Four existing embeddings each lack an `@[simp]` lemma for the `atom` case, despite handling atoms in their recursive definitions
- The direct PL.toBimodal path should live in `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` (following the convention that bimodal embeddings live in the bimodal embedding directory)
- The commutation lemma requires imports from all three embedding files and is best co-located with `PL.toBimodal`

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation required for this task.

## Goals & Non-Goals

**Goals**:
- Add `@[simp]` lemma coverage for the `atom` constructor in all four existing embedding functions
- Create the direct `PL.Proposition.toBimodal` embedding function with `Coe` instance
- Prove that the embedding diamond commutes: `PL.toModal.toBimodal = PL.toTemporal.toBimodal`
- Register the new file in `Cslib.lean` root imports
- Zero `lake build` errors

**Non-Goals**:
- Injectivity lemmas for embeddings (separate task scope, needed for task 10)
- Additional derived connective simp lemmas beyond `neg` (already covered where applicable)
- Changes to existing embedding function definitions

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Simp lemma naming conflicts | L | L | Follow established naming convention `{Type}.{function}_{constructor}` |
| Import cycle from new file | M | L | PropositionalEmbedding.lean imports leaf files only; no back-edges possible |
| Commutation proof requires more than `simp` | L | L | Fall back to `induction ... <;> rfl` if simp set is insufficient |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Add Atom Simp Lemmas [NOT STARTED]

**Goal**: Add `@[simp]` lemmas for the `atom` case to all four existing embedding functions, completing simp coverage for every constructor.

**Tasks**:
- [ ] Add `PL.Proposition.toModal_atom` to `Cslib/Logics/Propositional/Embedding.lean`
- [ ] Add `PL.Proposition.toTemporal_atom` to `Cslib/Logics/Propositional/Embedding.lean`
- [ ] Add `Modal.Proposition.toBimodal_atom` to `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean`
- [ ] Add `Temporal.Formula.toBimodal_atom` to `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean`
- [ ] Run `lake build` to verify zero errors

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Embedding.lean` - Add 2 atom simp lemmas (toModal_atom, toTemporal_atom)
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` - Add 1 atom simp lemma (toBimodal_atom)
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` - Add 1 atom simp lemma (toBimodal_atom)

**Exact code to add**:

In `Cslib/Logics/Propositional/Embedding.lean`, after the `instCoePLToTemporal` instance (before `toModal_bot`):
```lean
/-- Embedding preserves atom. -/
@[simp]
theorem PL.Proposition.toModal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toModal = Modal.Proposition.atom p := rfl

/-- Embedding preserves atom (temporal). -/
@[simp]
theorem PL.Proposition.toTemporal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toTemporal = Temporal.Formula.atom p := rfl
```

In `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean`, after `instCoeModalToBimodal` (before `toBimodal_bot`):
```lean
/-- Embedding preserves atom. -/
@[simp]
theorem Modal.Proposition.toBimodal_atom (p : Atom) :
    (Modal.Proposition.atom p : Modal.Proposition Atom).toBimodal = Bimodal.Formula.atom p := rfl
```

In `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean`, after `instCoeTemporalToBimodal` (before `toBimodal_bot`):
```lean
/-- Embedding preserves atom. -/
@[simp]
theorem Temporal.Formula.toBimodal_atom (p : Atom) :
    (Temporal.Formula.atom p : Temporal.Formula Atom).toBimodal = Bimodal.Formula.atom p := rfl
```

**Verification**:
- `lake build Cslib.Logics.Propositional.Embedding` passes
- `lake build Cslib.Logics.Bimodal.Embedding.ModalEmbedding` passes
- `lake build Cslib.Logics.Bimodal.Embedding.TemporalEmbedding` passes

---

### Phase 2: PL.toBimodal and Triangle-Commutes [NOT STARTED]

**Goal**: Create the direct PL-to-Bimodal embedding with Coe instance, simp lemmas for all constructors plus `neg`, and three commutation lemmas proving the embedding diamond commutes.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean`
- [ ] Define `PL.Proposition.toBimodal` (3 cases: atom, bot, imp)
- [ ] Add `Coe` instance `instCoePLToBimodal`
- [ ] Add 4 simp lemmas: `toBimodal_atom`, `toBimodal_bot`, `toBimodal_imp`, `toBimodal_neg`
- [ ] Add `@[simp] theorem PL.Proposition.toModal_toBimodal` (structural induction)
- [ ] Add `@[simp] theorem PL.Proposition.toTemporal_toBimodal` (structural induction)
- [ ] Add `theorem PL.Proposition.embedding_commutes` (follows from the two simp lemmas)
- [ ] Run `lake build Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding` to verify

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` - New file (entire content)

**Exact file content**:
```lean
/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

module

public import Cslib.Logics.Propositional.Embedding
public import Cslib.Logics.Bimodal.Embedding.ModalEmbedding
public import Cslib.Logics.Bimodal.Embedding.TemporalEmbedding

/-! # Propositional to Bimodal Embedding

This module defines the direct structural embedding from propositional logic formulas into
bimodal logic formulas, and proves that the embedding diamond commutes: going through
Modal is the same as going through Temporal.

## Main Definitions

- `PL.Proposition.toBimodal`: Propositional -> Bimodal (maps atom/bot/imp)

## Main Results

- `PL.Proposition.toModal_toBimodal`: PL -> Modal -> Bimodal = PL -> Bimodal
- `PL.Proposition.toTemporal_toBimodal`: PL -> Temporal -> Bimodal = PL -> Bimodal
- `PL.Proposition.embedding_commutes`: both composite paths agree
-/

@[expose] public section

namespace Cslib.Logic

/-- Embed a propositional formula directly into bimodal logic. -/
def PL.Proposition.toBimodal : PL.Proposition Atom -> Bimodal.Formula Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp phi1 phi2 => .imp phi1.toBimodal phi2.toBimodal

/-- Coercion from propositional to bimodal formulas. -/
instance instCoePLToBimodal : Coe (PL.Proposition Atom) (Bimodal.Formula Atom) where
  coe := PL.Proposition.toBimodal

/-- Direct embedding preserves atom. -/
@[simp]
theorem PL.Proposition.toBimodal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toBimodal = Bimodal.Formula.atom p := rfl

/-- Direct embedding preserves bot. -/
@[simp]
theorem PL.Proposition.toBimodal_bot :
    (PL.Proposition.bot : PL.Proposition Atom).toBimodal = Bimodal.Formula.bot := rfl

/-- Direct embedding preserves imp. -/
@[simp]
theorem PL.Proposition.toBimodal_imp (phi1 phi2 : PL.Proposition Atom) :
    (PL.Proposition.imp phi1 phi2).toBimodal =
      Bimodal.Formula.imp phi1.toBimodal phi2.toBimodal := rfl

/-- Direct embedding preserves neg. -/
@[simp]
theorem PL.Proposition.toBimodal_neg (phi : PL.Proposition Atom) :
    (PL.Proposition.neg phi).toBimodal = Bimodal.Formula.neg phi.toBimodal := rfl

/-- The diagram PL -> Modal -> Bimodal commutes with the direct path PL -> Bimodal. -/
@[simp]
theorem PL.Proposition.toModal_toBimodal (phi : PL.Proposition Atom) :
    phi.toModal.toBimodal = phi.toBimodal := by
  induction phi <;> simp [*]

/-- The diagram PL -> Temporal -> Bimodal commutes with the direct path PL -> Bimodal. -/
@[simp]
theorem PL.Proposition.toTemporal_toBimodal (phi : PL.Proposition Atom) :
    phi.toTemporal.toBimodal = phi.toBimodal := by
  induction phi <;> simp [*]

/-- The embedding diamond commutes:
    going through Modal is the same as going through Temporal. -/
theorem PL.Proposition.embedding_commutes (phi : PL.Proposition Atom) :
    phi.toModal.toBimodal = phi.toTemporal.toBimodal := by
  simp

end Cslib.Logic
```

**Verification**:
- `lake build Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding` passes with zero errors
- No `sorry` occurrences

---

### Phase 3: Root Import and Full Build [NOT STARTED]

**Goal**: Register the new file in the root import list and verify the full project builds cleanly.

**Tasks**:
- [ ] Add `public import Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding` to `Cslib.lean`
- [ ] Run `lake build` to verify zero errors across entire project
- [ ] Verify zero `sorry` occurrences in modified/created files

**Timing**: 15 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib.lean` - Add 1 import line after the existing bimodal embedding imports

**Exact edit**: Insert after line `public import Cslib.Logics.Bimodal.Embedding.TemporalEmbedding`:
```
public import Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding
```

**Verification**:
- `lake build` passes with zero errors
- `grep -r sorry Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` returns nothing
- `grep -r sorry Cslib/Logics/Propositional/Embedding.lean` returns nothing

## Testing & Validation

- [ ] All 4 atom simp lemmas compile as `rfl`
- [ ] `PL.Proposition.toBimodal` function compiles and covers all 3 PL constructors
- [ ] Coe instance `instCoePLToBimodal` registers without conflict
- [ ] All 4 new simp lemmas (atom, bot, imp, neg) for `toBimodal` compile as `rfl`
- [ ] `toModal_toBimodal` closes by `induction ... <;> simp [*]`
- [ ] `toTemporal_toBimodal` closes by `induction ... <;> simp [*]`
- [ ] `embedding_commutes` closes by `simp` (using the two preceding simp lemmas)
- [ ] `lake build` passes with zero errors
- [ ] Zero `sorry` occurrences in all modified/created files

## Artifacts & Outputs

- `specs/015_complete_embedding_lattice/plans/01_embedding-lattice-plan.md` (this plan)
- `Cslib/Logics/Propositional/Embedding.lean` (modified: +2 atom simp lemmas)
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` (modified: +1 atom simp lemma)
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` (modified: +1 atom simp lemma)
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` (new file: toBimodal + commutation)
- `Cslib.lean` (modified: +1 import line)

## Rollback/Contingency

All changes are additive (new lemmas, new file, new import). Rollback is straightforward:
1. Delete `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean`
2. Remove the corresponding import from `Cslib.lean`
3. Revert the atom simp lemma additions in the three existing files via `git checkout` of those files
