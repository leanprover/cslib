# Sub-PR Spec: 1.1 -- 3-Tier Hilbert Hierarchy Refactoring

## Task Mapping
- **Task**: 125 - subpr_1_1_hilbert_hierarchy_refactoring
- **Sub-PR**: 1.1 of 11
- **Wave**: 1
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `propositional/hilbert-hierarchy-refactor`
- **Base**: upstream `main` (no dependencies -- this PR can be submitted immediately)

## Files

| File | Type | +Lines | -Lines | Notes |
|------|------|-------:|-------:|-------|
| `Cslib/Foundations/Logic/ProofSystem.lean` | MOD | +35 | -17 | 3-tier bundled typeclass: MinimalHilbert/IntuitionisticHilbert/ClassicalHilbert |
| `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` | MOD | +94 | -72 | Theorems stratified by logic strength (LEM/DNE/RAA) |
| `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` | MOD | +63 | -60 | Theorems stratified by logic strength (De Morgan etc.) |
| `Cslib/Foundations/Logic/Theorems.lean` | MOD | +15 | -4 | Barrel doc update |
| `Cslib/Foundations/Logic/Theorems/BigConj.lean` | MOD | +2 | -2 | Variable rename: PropositionalHilbert -> ClassicalHilbert |
| `Cslib/Foundations/Logic/Theorems/Combinators.lean` | MOD | +2 | -2 | Variable rename: PropositionalHilbert -> MinimalHilbert |
| `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean` | MOD | +0 | -1 | Import cleanup (removes unused import) |
| `Cslib/Foundations/Data/ListHelpers.lean` | MOD | +7 | -4 | `simp` -> `simp only` lint fixes |
| `Cslib/Logics/Propositional/Defs.lean` | MOD | +4 | -0 | Add `Proposition.iff` abbreviation |
| `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` | MOD | +58 | -42 | Parameterize DerivationTree over Axioms type |
| `Cslib/Logics/Propositional/ProofSystem/Instances.lean` | MOD | +5 | -5 | ClassicalHilbert rename |
| `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` | MOD | +73 | -36 | Parameterize over Axioms type |
| `Cslib/Logics/Propositional/Metalogic/MCS.lean` | MOD | +74 | -42 | Parameterize MCS properties |

- **Cslib.lean**: No new import lines (all files already imported; this PR only modifies existing files)
- **Total**: ~483 insertions, ~287 deletions

## Dependencies
- **Requires merged**: None (Wave 1 -- can be submitted immediately)
- **Required by**: Tasks 126, 127, 128, 129 (all Wave 2 sub-PRs), and transitively all Wave 3 and 4 sub-PRs

## Extraction Instructions

This PR consists entirely of modifications to files already in upstream main. Extraction procedure:

1. Create branch from upstream main:
   ```bash
   git fetch upstream
   git checkout -b propositional/hilbert-hierarchy-refactor upstream/main
   ```

2. For each modified file, cherry-pick only the relevant hunks from `pr1/foundations-logic`:
   ```bash
   # Use git checkout with patch mode to selectively apply hunks
   git checkout pr1/foundations-logic -- Cslib/Foundations/Logic/ProofSystem.lean
   git checkout pr1/foundations-logic -- Cslib/Foundations/Logic/Theorems/Propositional/Core.lean
   git checkout pr1/foundations-logic -- Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean
   git checkout pr1/foundations-logic -- Cslib/Foundations/Logic/Theorems.lean
   git checkout pr1/foundations-logic -- Cslib/Foundations/Logic/Theorems/BigConj.lean
   git checkout pr1/foundations-logic -- Cslib/Foundations/Logic/Theorems/Combinators.lean
   git checkout pr1/foundations-logic -- Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean
   git checkout pr1/foundations-logic -- Cslib/Foundations/Data/ListHelpers.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Defs.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/ProofSystem/Derivation.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/ProofSystem/Instances.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Metalogic/MCS.lean
   ```

3. Verify no new files were added (this PR is modifications-only):
   ```bash
   git status --short | grep "^A "  # should return empty
   ```

4. Verify build passes before opening PR.

**Note**: These 13 files are entirely self-contained in their modifications. No sub-PR 1.2-1.11 files need to be present for this PR to build.

## PR Description

```markdown
## Summary

Introduce a 3-tier Hilbert proof system hierarchy (`MinimalHilbert` < `IntuitionisticHilbert` < `ClassicalHilbert`), replacing the previous flat `PropositionalHilbert` typeclass. This refactoring stratifies existing theorems by the weakest logic that proves them, enabling sound soundness and completeness results for sub-classical logics in subsequent PRs.

This is sub-PR 1.1 of 11 in the PR 1 decomposition (see [tracking comment] for full plan).

## Changes

- `Foundations/Logic/ProofSystem.lean`: Add 3-tier bundled typeclass hierarchy with `HilbertMin`/`HilbertInt`/`HilbertCl` axiom tags; rename `PropositionalHilbert` -> `MinimalHilbert`/`ClassicalHilbert` as appropriate
- `Foundations/Logic/Theorems/Propositional/Core.lean`: Stratify `LEM`, `DNE`, `RAA` as classical-only; move minimal/intuitionistic-provable theorems to weaker typeclass assumptions
- `Foundations/Logic/Theorems/Propositional/Connectives.lean`: Stratify De Morgan laws, double negation, etc. by logic strength
- `Foundations/Logic/Theorems.lean`: Update barrel doc
- `Foundations/Logic/Theorems/BigConj.lean`, `Combinators.lean`: Variable rename (`PropositionalHilbert` -> `ClassicalHilbert`/`MinimalHilbert`)
- `Foundations/Logic/Theorems/Temporal/FrameConditions.lean`: Remove unused import
- `Foundations/Data/ListHelpers.lean`: Replace bare `simp` with `simp only` (lint fix)
- `Logics/Propositional/Defs.lean`: Add `Proposition.iff` abbreviation for biconditional
- `Logics/Propositional/ProofSystem/Derivation.lean`: Parameterize `DerivationTree` over `Axioms` type variable
- `Logics/Propositional/ProofSystem/Instances.lean`: Update for `ClassicalHilbert` rename
- `Logics/Propositional/Metalogic/DeductionTheorem.lean`: Parameterize deduction theorem proof over `Axioms` type
- `Logics/Propositional/Metalogic/MCS.lean`: Parameterize MCS properties over `Axioms` type

## Dependencies

- Requires: None (Wave 1)
- Required by: Sub-PRs 1.2-1.11 (all subsequent PRs depend on this hierarchy)

## Testing

- `lake build` passes
- `lake test` passes
- `lake lint` and `lake exe lint-style` pass
- `lake exe checkInitImports` passes
- `lake exe shake --add-public --keep-implied --keep-prefix` passes (no unused imports)
- No `sorry` in any modified file

## References

No new bib citations needed for this refactoring PR.
```

## Bib References
None required for this PR (pure refactoring, no new mathematical content requiring citations).

## Estimated LOC
- Insertions: ~483
- Deletions: ~287

## Verification

Run before submitting:
```bash
lake build
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
lake exe mk_all --module --check
lake exe shake --add-public --keep-implied --keep-prefix
grep -rn "sorry" Cslib/Foundations/Logic/ProofSystem.lean \
  Cslib/Foundations/Logic/Theorems/Propositional/ \
  Cslib/Logics/Propositional/ProofSystem/ \
  Cslib/Logics/Propositional/Metalogic/
```
