# Sub-PR Spec: 1.9 -- ND-Hilbert Bridge Parameterization

## Task Mapping
- **Task**: 133 - subpr_1_9_fromhilbert_parameterization
- **Sub-PR**: 1.9 of 11
- **Wave**: 3
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `propositional/fromhilbert-parameterize`
- **Base**: upstream `main` after task 126 (sub-PR 1.2) merges

## Files

| File | Type | +Lines | -Lines | Notes |
|------|------|-------:|-------:|-------|
| `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` | MOD | +146 | -63 | Parameterize over `Axioms` type; add `impI_int`, `impI_min`, etc. |

- **Cslib.lean**: No new import (file already imported)
- **Total**: ~146 insertions, ~63 deletions

## Dependencies
- **Requires merged**: Task 126 (sub-PR 1.2 -- provides `IntPropAxiom`, `MinPropAxiom` definitions used in the new parameterized instances)
- **Required by**: Tasks 134, 135 (sub-PRs 1.10 and 1.11 -- `HilbertDerivedRules` and `ND-Hilbert equivalence` both import the parameterized `FromHilbert`)

## Extraction Instructions

1. Create branch from upstream main after sub-PR 1.2 merges:
   ```bash
   git fetch upstream
   git checkout -b propositional/fromhilbert-parameterize upstream/main
   ```

2. Apply modifications to FromHilbert.lean:
   ```bash
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean
   ```

3. Verify build passes.

**Key changes in FromHilbert.lean** (+146/-63):
- Before: `FromHilbert` had a single generic implementation parameterized only by `ClassicalHilbert ax`
- After: Parameterized over any `ax : Type` with appropriate instance, enabling bridges for `IntPropAxiom` and `MinPropAxiom` as well
- New lemmas: `impI_int` (implication introduction for intuitionistic logic), `impI_min` (for minimal logic), and corresponding elimination rules
- New `instance : FromHilbert IntPropAxiom` and `instance : FromHilbert MinPropAxiom` -- bridges for sub-classical logics
- The file modification is self-contained: it only changes the existing `FromHilbert.lean` (no new files)

## PR Description

```markdown
## Summary

Parameterize `FromHilbert.lean` over axiom sets, extending the ND-Hilbert bridge to work for intuitionistic and minimal logic in addition to classical logic. Adds instances `FromHilbert IntPropAxiom` and `FromHilbert MinPropAxiom`.

This is sub-PR 1.9 of 11 in the PR 1 decomposition.

## Changes

- `Logics/Propositional/NaturalDeduction/FromHilbert.lean`: Generalize `DerivationTree -> HilbertDerivable` bridge over `Axioms` type parameter; add `impI_int`, `impI_min` and other new bridging lemmas; add `FromHilbert IntPropAxiom` and `FromHilbert MinPropAxiom` instances (+146/-63)

## Dependencies

- Requires: Sub-PR 1.2 (IntMin instances -- provides `IntPropAxiom`/`MinPropAxiom` definitions)
- Required by: Sub-PRs 1.10, 1.11 (HilbertDerivedRules and ND-Hilbert equivalence)

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
- Insertions: ~146
- Deletions: ~63

## Verification

```bash
lake build
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
grep -rn "sorry" Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean
```
