# Sub-PR Spec: 1.5 -- Modal Logical Equivalence + Basic Update

## Task Mapping
- **Task**: 129 - subpr_1_5_modal_logical_equivalence
- **Sub-PR**: 1.5 of 11
- **Wave**: 2
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `modal/logical-equivalence`
- **Base**: upstream `main` after task 125 (sub-PR 1.1) merges

## Files

| File | Type | +Lines | -Lines | Notes |
|------|------|-------:|-------:|-------|
| `Cslib/Logics/Modal/LogicalEquivalence.lean` | NEW | 132 | 0 | `LogicalEquivalence` typeclass instance for modal logic |
| `Cslib/Logics/Modal/Basic.lean` | MOD | +19 | -11 | `MinimalHilbert` variable rename throughout |
| `Cslib/Logics/Modal/Denotation.lean` | MOD | +2 | -2 | Trivial rename (same MinimalHilbert variable update) |
| `Cslib.lean` | MOD | +1 | -0 | Add import for `Modal.LogicalEquivalence` |

- **Total**: ~154 insertions (132 new + 19 mod + 2 mod + 1 import)

## Dependencies
- **Requires merged**: Task 125 (sub-PR 1.1 -- provides `MinimalHilbert` typeclass that `Modal/Basic.lean` uses)
- **Required by**: None (independent leaf -- no other sub-PR depends on this)

## Extraction Instructions

1. Create branch from upstream main after sub-PR 1.1 merges:
   ```bash
   git fetch upstream
   git checkout -b modal/logical-equivalence upstream/main
   ```

2. Copy the new LogicalEquivalence file:
   ```bash
   git checkout pr1/foundations-logic -- Cslib/Logics/Modal/LogicalEquivalence.lean
   ```

3. Apply modifications to Basic.lean and Denotation.lean:
   ```bash
   git checkout pr1/foundations-logic -- Cslib/Logics/Modal/Basic.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Modal/Denotation.lean
   ```

4. Add import to `Cslib.lean`:
   ```bash
   # Add after Modal.Basic import:
   # import Cslib.Logics.Modal.LogicalEquivalence
   ```

5. Verify build passes.

**Key content of LogicalEquivalence.lean**:
- `instance : LogicalEquivalence (ModalFormula α) ModalDerivable` -- registers modal derivability as a logical equivalence relation
- Proves symmetry, transitivity, and substitution properties required by the `LogicalEquivalence` typeclass from `Foundations/Logic/LogicalEquivalence.lean`
- Imports `Foundations/Logic/LogicalEquivalence.lean` (already in upstream main)

**Changes to Basic.lean** (the `+19/-11`):
- Rename variable `[h : PropositionalHilbert ax]` -> `[h : MinimalHilbert ax]` throughout (consistent with sub-PR 1.1 hierarchy)
- No semantic changes to proofs

## PR Description

```markdown
## Summary

Add a `LogicalEquivalence` typeclass instance for modal derivability and update `Modal/Basic.lean` to use the `MinimalHilbert` variable name introduced in sub-PR 1.1.

This is sub-PR 1.5 of 11 in the PR 1 decomposition.

## Changes

- `Logics/Modal/LogicalEquivalence.lean` (NEW): Instance of `Foundations.Logic.LogicalEquivalence` for modal Hilbert derivability; proves symmetry, transitivity, and substitution
- `Logics/Modal/Basic.lean`: Rename `PropositionalHilbert` variable to `MinimalHilbert` (consistency with 3-tier hierarchy from sub-PR 1.1)
- `Logics/Modal/Denotation.lean`: Same trivial rename
- `Cslib.lean`: Add import for `Modal.LogicalEquivalence`

## Dependencies

- Requires: Sub-PR 1.1 (3-tier hierarchy rename; provides `MinimalHilbert`)
- Required by: None (independent leaf)

## Testing

- `lake build` passes
- `lake test` passes
- `lake lint` and `lake exe lint-style` pass
- `lake exe checkInitImports` passes
- No `sorry` in any file

## References

No new bib citations needed.
```

## Bib References
None required.

## Estimated LOC
- Insertions: ~154
- Deletions: ~13

## Verification

```bash
lake build
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
grep -rn "sorry" Cslib/Logics/Modal/LogicalEquivalence.lean \
  Cslib/Logics/Modal/Basic.lean \
  Cslib/Logics/Modal/Denotation.lean
```
