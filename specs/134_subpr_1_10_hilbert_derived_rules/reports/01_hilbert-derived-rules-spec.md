# Sub-PR Spec: 1.10 -- Hilbert-Style Derived Connective Rules

## Task Mapping
- **Task**: 134 - subpr_1_10_hilbert_derived_rules
- **Sub-PR**: 1.10 of 11
- **Wave**: 4
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `propositional/hilbert-derived-rules`
- **Base**: upstream `main` after task 133 (sub-PR 1.9) merges

## Files

| File | Type | +Lines | -Lines | Notes |
|------|------|-------:|-------:|-------|
| `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` | NEW | 559 | 0 | Derived connective rules at 3 logic levels via `FromHilbert` |
| `Cslib.lean` | MOD | +1 | -0 | Add import for `NaturalDeduction.HilbertDerivedRules` |

- **Total**: ~560 insertions (559 new file + 1 import)
- **Note**: Over the 500-line target (560 vs 500). This is a single file covering one coherent feature (connective rules at 3 logic levels); splitting by connective would create non-buildable partial files.

## Dependencies
- **Requires merged**: Task 133 (sub-PR 1.9 -- parameterized `FromHilbert`; `HilbertDerivedRules` imports `FromHilbert`)
- **Required by**: None (independent leaf)

## Extraction Instructions

1. Create branch from upstream main after sub-PR 1.9 merges:
   ```bash
   git fetch upstream
   git checkout -b propositional/hilbert-derived-rules upstream/main
   ```

2. Copy the new HilbertDerivedRules file:
   ```bash
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean
   ```

3. Add import to `Cslib.lean`:
   ```bash
   # Add after FromHilbert import:
   # import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules
   ```

4. Verify build passes.

**Key content of HilbertDerivedRules.lean** (559 lines):
- Derived rules for **negation** at 3 levels (minimal, intuitionistic, classical): `negI_min`, `negI_int`, `negI_cl`, `negE_cl`, `exFalso_int`
- Derived rules for **top** (`⊤`): `topI_min`, `topI_int`, `topI_cl`
- Derived rules for **conjunction** at 3 levels: `conjI`, `conjE1`, `conjE2` (for each logic level)
- Derived rules for **disjunction** at 3 levels: `disjI1`, `disjI2`, `disjE` (classical, intuitionistic, and minimal variants)
- Derived rules for **biconditional**: `iffI`, `iffE1`, `iffE2` at each logic level
- All rules use `FromHilbert` (from 1.9) to bridge between Hilbert derivability and natural deduction style
- Covers all 5 propositional connectives × 3 logic levels = 15 rule families

**Why it can't be split**: Each logic level's rules depend on the ones at the level below (minimal rules are used in intuitionistic proofs, etc.), and splitting at the connective level would leave inconsistent typeclass instance contexts.

## PR Description

```markdown
## Summary

Add derived inference rules for all propositional connectives (negation, top, conjunction, disjunction, biconditional) at three logic levels (minimal, intuitionistic, classical) using the parameterized `FromHilbert` bridge. This enables ergonomic natural-deduction-style proofs within the Hilbert derivability framework.

This PR is slightly over the 500-line target (560 insertions). Splitting by connective would create non-buildable partial files since each connective's rules at each level depend on the level below.

This is sub-PR 1.10 of 11 in the PR 1 decomposition.

## Changes

- `Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` (NEW): 559-line file with derived rules for ¬, ⊤, ∧, ∨, ↔ at each of minimal/intuitionistic/classical logic levels, using `FromHilbert` bridge
- `Cslib.lean`: Add import for new module

## Dependencies

- Requires: Sub-PR 1.9 (parameterized `FromHilbert`)
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
- Insertions: ~560 (over 500-line target; single coherent file, indivisible)
- Deletions: ~0

## Verification

```bash
lake build
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
grep -rn "sorry" Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean
```
