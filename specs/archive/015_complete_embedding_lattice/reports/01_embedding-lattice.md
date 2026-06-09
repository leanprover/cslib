# Research Report: Complete Embedding Lattice

**Task**: 15 — Complete embedding lattice: atom simp lemmas, PL.toBimodal, triangle-commutes
**Date**: 2026-06-08
**Session**: sess_1780964944_adc2c6_15

## Summary

The embedding lattice connects four formula types in cslib: `PL.Proposition`, `Modal.Proposition`, `Temporal.Formula`, and `Bimodal.Formula`. The current codebase has four embedding functions (PL->Modal, PL->Temporal, Modal->Bimodal, Temporal->Bimodal) with simp lemmas for most constructors, but three specific gaps exist: (1) missing `@[simp]` lemmas for the `atom` constructor across all embedding files, (2) missing direct `PL.toBimodal` path, and (3) missing triangle-commutation lemma proving both composite paths from PL to Bimodal agree.

## Embedding Lattice Structure

The embedding lattice forms a commutative diamond:

```
        PL.Proposition
       /              \
      / toModal        \ toTemporal
     v                  v
Modal.Proposition    Temporal.Formula
     \                  /
      \ toBimodal      / toBimodal
       v              v
      Bimodal.Formula
```

### Existing Files and Functions

| File | Function | Constructors | Coe Instance |
|------|----------|-------------|--------------|
| `Cslib/Logics/Propositional/Embedding.lean` | `PL.Proposition.toModal` | atom, bot, imp | Yes |
| `Cslib/Logics/Propositional/Embedding.lean` | `PL.Proposition.toTemporal` | atom, bot, imp | Yes |
| `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` | `Modal.Proposition.toBimodal` | atom, bot, imp, box | Yes |
| `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` | `Temporal.Formula.toBimodal` | atom, bot, imp, untl, snce | Yes |
| **MISSING** | `PL.Proposition.toBimodal` | atom, bot, imp | No |

### Existing Simp Lemmas

| Embedding | bot | imp | neg | box | diamond | untl | snce | **atom** |
|-----------|-----|-----|-----|-----|---------|------|------|----------|
| PL.toModal | Yes | Yes | Yes | N/A | N/A | N/A | N/A | **NO** |
| PL.toTemporal | Yes | Yes | Yes | N/A | N/A | N/A | N/A | **NO** |
| Modal.toBimodal | Yes | Yes | Yes | Yes | Yes | N/A | N/A | **NO** |
| Temporal.toBimodal | Yes | Yes | Yes | N/A | N/A | Yes | Yes | **NO** |

## Gap Analysis

### Gap 1: Missing Atom Simp Lemmas

All four existing embedding functions handle the `atom` case in their recursive definition but lack a corresponding `@[simp]` lemma. This is inconsistent with the pattern established for `bot`, `imp`, and `neg` and means that `simp` cannot normalize embedding applications on atoms.

**Files needing atom simp lemmas:**
1. `Cslib/Logics/Propositional/Embedding.lean` — needs `PL.Proposition.toModal_atom` and `PL.Proposition.toTemporal_atom`
2. `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` — needs `Modal.Proposition.toBimodal_atom`
3. `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` — needs `Temporal.Formula.toBimodal_atom`

**Pattern** (all are trivially `rfl`):
```lean
@[simp]
theorem PL.Proposition.toModal_atom (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).toModal = Modal.Proposition.atom p := rfl
```

### Gap 2: Missing PL.toBimodal Path

The direct composition `PL -> Bimodal` is currently only achievable by composing two existing embeddings (e.g., `PL.toModal` then `Modal.toBimodal`). A direct function `PL.Proposition.toBimodal` would:
- Complete the embedding lattice with a direct diagonal path
- Provide a `Coe` instance from `PL.Proposition` to `Bimodal.Formula`
- Be definitionally equal to either composition path

**Definition** (3 cases: atom, bot, imp):
```lean
def PL.Proposition.toBimodal : PL.Proposition Atom → Bimodal.Formula Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ₁ φ₂ => .imp φ₁.toBimodal φ₂.toBimodal
```

**Simp lemmas needed**: `toBimodal_atom`, `toBimodal_bot`, `toBimodal_imp`, `toBimodal_neg`

**Coe instance**: `instCoePLToBimodal`

**Placement**: `Cslib/Logics/Propositional/Embedding.lean` — this file already imports both `Modal.Basic` and `Temporal.Syntax.Formula`, and via the Bimodal embedding files (which are imported elsewhere in the project), it has access to `Bimodal.Formula`. However, adding `toBimodal` here requires importing `Cslib.Logics.Bimodal.Syntax.Formula`. The current imports are:
- `Cslib.Logics.Propositional.Defs`
- `Cslib.Logics.Modal.Basic`
- `Cslib.Logics.Temporal.Syntax.Formula`

The `Bimodal.Syntax.Formula` import would need to be added. Alternatively, this could be placed in a new file at `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` following the existing pattern where bimodal embeddings live in the `Bimodal/Embedding/` directory.

**Recommendation**: Place in `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` to follow the existing convention (bimodal embeddings live in the bimodal embedding directory) and avoid adding a bimodal import to the propositional embedding file.

### Gap 3: Missing Triangle-Commutation Lemma

The triangle-commutation (diagram commutativity) lemma proves that both paths from PL to Bimodal agree:

```
Path 1: PL.toModal ∘ Modal.toBimodal = PL.toBimodal
Path 2: PL.toTemporal ∘ Temporal.toBimodal = PL.toBimodal
Combined: PL.toModal ∘ Modal.toBimodal = PL.toTemporal ∘ Temporal.toBimodal
```

**Proof approach**: Simple structural induction on `PL.Proposition` with 3 cases (atom, bot, imp). Each case is `rfl` since all three paths map atom->atom, bot->bot, imp->imp in the same way.

**Statements**:
```lean
/-- The diagram PL -> Modal -> Bimodal commutes with the direct path PL -> Bimodal. -/
@[simp]
theorem PL.Proposition.toModal_toBimodal (φ : PL.Proposition Atom) :
    φ.toModal.toBimodal = φ.toBimodal := by
  induction φ <;> simp [*]

/-- The diagram PL -> Temporal -> Bimodal commutes with the direct path PL -> Bimodal. -/
@[simp]
theorem PL.Proposition.toTemporal_toBimodal (φ : PL.Proposition Atom) :
    φ.toTemporal.toBimodal = φ.toBimodal := by
  induction φ <;> simp [*]

/-- The embedding diamond commutes:
    going through Modal is the same as going through Temporal. -/
theorem PL.Proposition.embedding_commutes (φ : PL.Proposition Atom) :
    φ.toModal.toBimodal = φ.toTemporal.toBimodal := by
  simp
```

**Placement**: In the same file as `PL.toBimodal` (`Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean`), since it requires imports from all three embedding files.

## Additional Considerations

### Injectivity Lemmas (Optional, Not in Scope)

The embeddings are all injective (they preserve distinct constructors), but no injectivity theorems currently exist. These would be useful for the separation theorem (task 10) but are not part of this task's scope.

### Derived Connective Simp Lemmas

The existing files already have simp lemmas for `neg` and (where applicable) `diamond` in the Modal->Bimodal embedding. The PL->Modal and PL->Temporal embeddings also have `neg` lemmas. The new `PL.toBimodal` should follow the same pattern.

### Import Dependencies

The new `PropositionalEmbedding.lean` file will need:
- `Cslib.Logics.Propositional.Defs` (for `PL.Proposition`)
- `Cslib.Logics.Bimodal.Syntax.Formula` (for `Bimodal.Formula`)
- `Cslib.Logics.Bimodal.Embedding.ModalEmbedding` (for `Modal.toBimodal` in commutation lemma)
- `Cslib.Logics.Bimodal.Embedding.TemporalEmbedding` (for `Temporal.toBimodal` in commutation lemma)
- `Cslib.Logics.Propositional.Embedding` (for `PL.toModal` and `PL.toTemporal`)

### Root Import Update

`Cslib.lean` will need a new line:
```
public import Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding
```

## Implementation Plan Overview

The task is small and has no dependencies on other tasks. All proofs are `rfl` or simple induction with `simp`.

### Phase 1: Atom Simp Lemmas (~15 min)

Add `@[simp]` lemmas for the `atom` case to:
1. `Cslib/Logics/Propositional/Embedding.lean` — 2 lemmas (toModal_atom, toTemporal_atom)
2. `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` — 1 lemma (toBimodal_atom)
3. `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` — 1 lemma (toBimodal_atom)

### Phase 2: PL.toBimodal + Triangle-Commutes (~30 min)

Create `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` with:
1. `PL.Proposition.toBimodal` function
2. `Coe` instance
3. Atom/bot/imp/neg simp lemmas
4. `toModal_toBimodal` commutation lemma
5. `toTemporal_toBimodal` commutation lemma
6. `embedding_commutes` combined lemma

### Phase 3: Build + Cleanup (~15 min)

1. Add import to `Cslib.lean`
2. Run `lake build` to verify zero errors
3. Verify zero sorry occurrences

## Risk Assessment

**Low risk**: All proofs are definitional equalities (`rfl`) or simple structural inductions. No dependencies on unfinished tasks. No sorry needed.

## References

- Task 19 research (factoring synthesis): Confirmed embedding lattice is the correct mechanism for connecting logics
- Existing embedding files provide clear patterns to follow
- No literature source referenced; first-principles mode applies
