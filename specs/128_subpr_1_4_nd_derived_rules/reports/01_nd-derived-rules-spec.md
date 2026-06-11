# Sub-PR Spec: 1.4 -- ND Derived Connective Rules (Standalone)

## Task Mapping
- **Task**: 128 - subpr_1_4_nd_derived_rules
- **Sub-PR**: 1.4 of 11
- **Wave**: 2
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `propositional/nd-derived-rules`
- **Base**: upstream `main` after task 125 (sub-PR 1.1) merges

## Files

| File | Type | +Lines | -Lines | Notes |
|------|------|-------:|-------:|-------|
| `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` | NEW | 387 | 0 | Derived connective rules for standalone ND system |
| `Cslib.lean` | MOD | +1 | -0 | Add import for `NaturalDeduction.DerivedRules` |

- **Total**: ~388 insertions (387 new file + 1 import)

## Dependencies
- **Requires merged**: Task 125 (sub-PR 1.1 -- needs `MinimalHilbert` typeclass from the updated `NaturalDeduction/Basic.lean` context)
- **Required by**: Task 135 (sub-PR 1.11 -- ND-Hilbert extensional equivalence)

## Extraction Instructions

1. Create branch from upstream main after sub-PR 1.1 merges:
   ```bash
   git fetch upstream
   git checkout -b propositional/nd-derived-rules upstream/main
   ```

2. Copy the new DerivedRules file:
   ```bash
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean
   ```

3. Add import to `Cslib.lean`:
   ```bash
   # Add after NaturalDeduction.Basic import:
   # import Cslib.Logics.Propositional.NaturalDeduction.DerivedRules
   ```

4. Verify build passes.

**Note**: `DerivedRules.lean` imports only `NaturalDeduction/Basic.lean` (already in upstream main). The dependency on sub-PR 1.1 is indirect: the hierarchy renaming in 1.1 changes the variable names used in `Basic.lean`, so this file must be checked out after 1.1 merges to avoid conflicts.

**Key content of DerivedRules.lean**:
- Derived rules for negation: `negI`, `negE`, `exFalso`
- Derived rules for conjunction: `conjI`, `conjE1`, `conjE2`
- Derived rules for disjunction: `disjI1`, `disjI2`, `disjE`
- Derived rules for biconditional: `iffI`, `iffE1`, `iffE2`
- All rules are proved from the axioms of `NaturalDeduction.Basic` (Theory.Derivation system)

## PR Description

```markdown
## Summary

Add derived rules for all propositional connectives (negation, conjunction, disjunction, biconditional) to the standalone natural deduction system. These rules reduce proof verbosity for the ND-based derivability relation.

This is sub-PR 1.4 of 11 in the PR 1 decomposition.

## Changes

- `Logics/Propositional/NaturalDeduction/DerivedRules.lean` (NEW): 387-line file with derived inference rules for ¬, ∧, ∨, ↔ in the `Theory.Derivation` natural deduction system
- `Cslib.lean`: Add import for new `DerivedRules` module

## Dependencies

- Requires: Sub-PR 1.1 (hierarchy refactoring; provides updated `NaturalDeduction/Basic.lean` variable names)
- Required by: Sub-PR 1.11 (ND-Hilbert extensional equivalence)

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
- Insertions: ~388 (387 new file + 1 import)
- Deletions: ~0

## Verification

```bash
lake build
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
grep -rn "sorry" Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean
```
