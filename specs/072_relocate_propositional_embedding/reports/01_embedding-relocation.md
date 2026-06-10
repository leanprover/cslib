# Research Report: Relocate Propositional/Embedding to Fix Dependency Inversion

**Task**: 72
**Date**: 2026-06-09
**Status**: Complete

## 1. Problem Statement

`Cslib/Logics/Propositional/Embedding.lean` imports from `Modal.Basic` and `Temporal.Syntax.Formula`, creating a backwards dependency where the simpler logic (Propositional) imports from more complex ones (Modal, Temporal). The intended dependency flow is:

```
Foundations -> {Propositional, Modal, Temporal} -> Bimodal
```

But the current flow has:

```
Propositional/Embedding -> Modal.Basic, Temporal.Syntax.Formula   (VIOLATION)
Bimodal/Embedding/PropositionalEmbedding -> Propositional/Embedding (transitive violation)
```

## 2. Current File Analysis

### 2.1 Propositional/Embedding.lean (the problematic file)

**Imports**:
- `Cslib.Logics.Propositional.Defs` (valid -- same module)
- `Cslib.Logics.Modal.Basic` (VIOLATION -- upward dependency)
- `Cslib.Logics.Temporal.Syntax.Formula` (VIOLATION -- upward dependency)

**Defines**:
1. `PL.Proposition.toModal` -- structural embedding PL -> Modal
2. `PL.Proposition.toTemporal` -- structural embedding PL -> Temporal
3. `instCoePLToModal` -- Coe instance PL -> Modal
4. `instCoePLToTemporal` -- Coe instance PL -> Temporal
5. Seven `@[simp]` theorems proving the embeddings preserve atom/bot/imp/neg

### 2.2 Bimodal/Embedding/PropositionalEmbedding.lean

**Imports**:
- `Cslib.Logics.Propositional.Embedding` (depends on the violating file)
- `Cslib.Logics.Bimodal.Embedding.ModalEmbedding`
- `Cslib.Logics.Bimodal.Embedding.TemporalEmbedding`

**Defines**:
1. `PL.Proposition.toBimodal` -- structural embedding PL -> Bimodal
2. `instCoePLToBimodal` -- Coe instance
3. Four `@[simp]` theorems for toBimodal
4. Commutativity theorems: `toModal_toBimodal`, `toTemporal_toBimodal`, `embedding_commutes`

The commutativity theorems use `toModal` and `toTemporal` from Propositional/Embedding.lean and `toBimodal` from ModalEmbedding.lean and TemporalEmbedding.lean.

### 2.3 Bimodal/Embedding/ModalEmbedding.lean

**Imports**: `Modal.Basic`, `Bimodal.Syntax.Formula`
**Defines**: `Modal.Proposition.toBimodal`, Coe instance, simp lemmas

This follows the correct pattern: it lives in Bimodal/ and imports from Modal/ (downward only for the embedding target).

### 2.4 Bimodal/Embedding/TemporalEmbedding.lean

**Imports**: `Temporal.Syntax.Formula`, `Bimodal.Syntax.Formula`
**Defines**: `Temporal.Formula.toBimodal`, Coe instance, simp lemmas

Same correct pattern as ModalEmbedding.

## 3. Dependency Impact Analysis

### Who imports Propositional/Embedding.lean?

Only two files:
1. `Cslib.lean` (root module file) -- line 166
2. `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` -- line 9

### Who uses the symbols defined in Propositional/Embedding.lean?

Only `PropositionalEmbedding.lean` uses `toModal` and `toTemporal` (in the commutativity theorems). No other file in the entire codebase references these symbols.

### What about Propositional/Defs.lean and NaturalDeduction/Basic.lean?

Both only import from Foundations -- no dependency issues. They are unaffected.

## 4. Recommended Approach

### Option A (Recommended): Merge into Bimodal/Embedding/PropositionalEmbedding.lean

This is the cleanest approach and is fully consistent with the existing pattern:

**Pattern observed**: Bimodal/Embedding/ already contains ModalEmbedding.lean (Modal -> Bimodal) and TemporalEmbedding.lean (Temporal -> Bimodal). Each file imports the source logic and defines the embedding into Bimodal.

**Proposed change**: Move the entire content of `Propositional/Embedding.lean` into `Bimodal/Embedding/PropositionalEmbedding.lean`, which already imports it. After merging:

- `toModal` and its Coe instance and simp lemmas move into `PropositionalEmbedding.lean`
- `toTemporal` and its Coe instance and simp lemmas move into `PropositionalEmbedding.lean`
- `toBimodal` and commutativity theorems remain where they are
- Delete `Propositional/Embedding.lean`
- Remove `public import Cslib.Logics.Propositional.Embedding` from `Cslib.lean`

**Why this works**: `PropositionalEmbedding.lean` already imports `ModalEmbedding.lean` (which imports `Modal.Basic`) and `TemporalEmbedding.lean` (which imports `Temporal.Syntax.Formula`), so all needed types are already available transitively.

**Result**: Propositional/ only imports from Foundations/. All embedding logic lives in Bimodal/Embedding/, consistent with the other embedding files.

### Option B (Alternative): Split into Modal/ and Temporal/

Split `toModal` into `Modal/Embedding/PropositionalEmbedding.lean` and `toTemporal` into `Temporal/Embedding/PropositionalEmbedding.lean`.

**Drawback**: Creates new `Embedding/` directories in Modal/ and Temporal/ that don't currently exist, adding structural complexity for a single file each. Also fragments the commutativity theorems -- they still need both definitions and must live in Bimodal/ anyway.

**Not recommended** because it adds two new directories and two new files while Option A adds zero directories and zero new files.

## 5. Detailed Implementation Plan for Option A

### Phase 1: Merge content into PropositionalEmbedding.lean

1. Replace `public import Cslib.Logics.Propositional.Embedding` with `public import Cslib.Logics.Propositional.Defs` in the imports of `PropositionalEmbedding.lean`
2. Move all definitions and theorems from `Propositional/Embedding.lean` into `PropositionalEmbedding.lean`, placing them BEFORE the existing `toBimodal` definitions (since the commutativity theorems reference them)
3. Preserve all docstrings, `@[simp]` attributes, and `@[expose]` sections

### Phase 2: Delete source file and update root imports

1. Delete `Cslib/Logics/Propositional/Embedding.lean`
2. In `Cslib.lean`, remove line 166: `public import Cslib.Logics.Propositional.Embedding`

### Phase 3: Update ROADMAP.md flowchart

1. Remove the `P2["Embedding"]` node from the Propositional subgraph
2. Remove edges `M1 --> P2` and `T1 --> P2` and `P2 --> B2`
3. Simplify the Propositional subgraph to just `P1["Defs . NaturalDeduction"]`
4. Update the "Module Dependency Structure" prose paragraph to remove mention of Propositional's Embedding component

### Phase 4: Verify

1. `lake build` to confirm the project still compiles

## 6. Files Changed

| File | Action |
|------|--------|
| `Cslib/Logics/Propositional/Embedding.lean` | DELETE |
| `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` | MODIFY (absorb content) |
| `Cslib.lean` | MODIFY (remove one import line) |
| `specs/ROADMAP.md` | MODIFY (update flowchart and prose) |

## 7. Risk Assessment

**Low risk**: The embedding symbols (`toModal`, `toTemporal`, coercions) are used only within the embedding files themselves. No code outside these files references them. The merge is a pure relocation with no semantic changes to any definitions or theorems.

## 8. Resulting Dependency Flow

After the change:

```
Foundations -> Propositional (Defs, NaturalDeduction only)
Foundations -> Modal
Foundations -> Temporal
Modal + Bimodal.Syntax -> Bimodal/Embedding/ModalEmbedding
Temporal + Bimodal.Syntax -> Bimodal/Embedding/TemporalEmbedding
Propositional.Defs + ModalEmbedding + TemporalEmbedding -> Bimodal/Embedding/PropositionalEmbedding
```

This achieves the clean downward flow: `Foundations -> {Propositional, Modal, Temporal} -> Bimodal`.
