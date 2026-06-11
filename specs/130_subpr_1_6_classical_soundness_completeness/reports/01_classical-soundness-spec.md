# Sub-PR Spec: 1.6 -- Classical Soundness + Completeness

## Task Mapping
- **Task**: 130 - subpr_1_6_classical_soundness_completeness
- **Sub-PR**: 1.6 of 11
- **Wave**: 3
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `propositional/classical-soundness-completeness`
- **Base**: upstream `main` after tasks 126 + 127 (sub-PRs 1.2 + 1.3) merge

## Files

| File | Type | +Lines | -Lines | Notes |
|------|------|-------:|-------:|-------|
| `Cslib/Logics/Propositional/Metalogic/Soundness.lean` | NEW | 87 | 0 | Classical soundness: `Derivable -> Tautology` |
| `Cslib/Logics/Propositional/Metalogic/Completeness.lean` | NEW | 295 | 0 | Classical completeness via canonical valuation construction |
| `Cslib.lean` | MOD | +2 | -0 | Add imports for Soundness and Completeness modules |

- **Total**: ~384 insertions (87 + 295 + 2 imports)

## Dependencies
- **Requires merged**: Task 126 (sub-PR 1.2 -- IntMin instances), Task 127 (sub-PR 1.3 -- propositional semantics)
- **Required by**: Tasks 131, 132 (sub-PRs 1.7 and 1.8 -- intuitionistic and minimal soundness/completeness import from Completeness.lean)

## Extraction Instructions

1. Create branch from upstream main after sub-PRs 1.2 + 1.3 merge:
   ```bash
   git fetch upstream
   git checkout -b propositional/classical-soundness-completeness upstream/main
   ```

2. Copy both new metalogic files:
   ```bash
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Metalogic/Soundness.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Metalogic/Completeness.lean
   ```

3. Add imports to `Cslib.lean`:
   ```bash
   # Add after existing Metalogic imports:
   # import Cslib.Logics.Propositional.Metalogic.Soundness
   # import Cslib.Logics.Propositional.Metalogic.Completeness
   ```

4. Verify build passes.

**Key content of Soundness.lean** (87 lines):
- `theorem classical_soundness : Derivable ax φ -> Tautology φ`
- Proof by induction on the derivation tree; each axiom schema is validated semantically
- Imports: `Metalogic/DeductionTheorem` (already in upstream), `Semantics/Basic` (from 1.3)

**Key content of Completeness.lean** (295 lines):
- `theorem classical_completeness : Tautology φ -> Derivable ClassPropAxiom φ`
- Proof via canonical valuation: if `φ` is not derivable, construct a falsifying valuation using `MCS` (from `Metalogic/MCS.lean`)
- `canonical_valuation`: maps propositional variables to `True` iff the variable is in the MCS
- Imports: `Semantics/Basic` (from 1.3), `Metalogic/MCS` (already in upstream + updated by 1.1), `Metalogic/Soundness` (from this PR)

## PR Description

```markdown
## Summary

Prove soundness and completeness of classical propositional Hilbert logic with respect to bivalent (two-valued) semantics. Soundness proceeds by induction on derivations; completeness uses a canonical valuation construction via maximally consistent sets.

This is sub-PR 1.6 of 11 in the PR 1 decomposition.

## Changes

- `Logics/Propositional/Metalogic/Soundness.lean` (NEW): Classical soundness theorem -- `Derivable ClassPropAxiom φ → Tautology φ`; proof by induction on derivation structure
- `Logics/Propositional/Metalogic/Completeness.lean` (NEW): Classical completeness theorem -- `Tautology φ → Derivable ClassPropAxiom φ`; canonical valuation construction using MCS (maximally consistent sets)
- `Cslib.lean`: Add imports for both new modules

## Dependencies

- Requires: Sub-PR 1.2 (IntMin instances -- axiom infrastructure), Sub-PR 1.3 (semantics -- `Tautology` definition)
- Required by: Sub-PRs 1.7, 1.8 (intuitionistic and minimal completeness reference `Soundness.lean`)

## Testing

- `lake build` passes
- `lake test` passes
- `lake lint` and `lake exe lint-style` pass
- `lake exe checkInitImports` passes
- No `sorry` in any file

## References

See [ChagrovZakharyaschev1997] for the canonical model approach used in the completeness proof.
```

## Bib References
- **ChagrovZakharyaschev1997**: Chagrov, A. and Zakharyaschev, M. (1997). *Modal Logic*. Oxford Logic Guides 35. -- For the canonical valuation/completeness methodology (added by task 123)

## Estimated LOC
- Insertions: ~384
- Deletions: ~0

## Verification

```bash
lake build
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
grep -rn "sorry" Cslib/Logics/Propositional/Metalogic/Soundness.lean \
  Cslib/Logics/Propositional/Metalogic/Completeness.lean
```
