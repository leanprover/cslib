# Sub-PR Spec: 1.8 -- Minimal Soundness + Completeness

## Task Mapping
- **Task**: 132 - subpr_1_8_minimal_soundness_completeness
- **Sub-PR**: 1.8 of 11
- **Wave**: 3
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `propositional/minimal-soundness-completeness`
- **Base**: upstream `main` after tasks 127 + 130 (sub-PRs 1.3 + 1.6) merge

## Files

| File | Type | +Lines | -Lines | Notes |
|------|------|-------:|-------:|-------|
| `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` | NEW | 96 | 0 | Minimal soundness w.r.t. Kripke models |
| `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` | NEW | 275 | 0 | DCCS extension lemma for minimal logic |
| `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` | NEW | 143 | 0 | Minimal completeness via Kripke canonical model |
| `Cslib.lean` | MOD | +3 | -0 | Add imports for all three new modules |

- **Total**: ~517 insertions (96 + 275 + 143 + 3 imports)
- **Note**: Slightly over the 500-line target (517 vs 500). Structurally mirrors sub-PR 1.7 and is logically indivisible for the same reasons.

## Dependencies
- **Requires merged**: Task 127 (sub-PR 1.3 -- Kripke semantics), Task 130 (sub-PR 1.6 -- classical soundness infrastructure; `MinLindenbaum` imports `Soundness.lean`)
- **Required by**: None (independent leaf -- can be submitted in parallel with 1.7 after same Wave 3 prerequisites merge)

## Extraction Instructions

1. Create branch from upstream main after sub-PRs 1.3 + 1.6 merge:
   ```bash
   git fetch upstream
   git checkout -b propositional/minimal-soundness-completeness upstream/main
   ```

2. Copy all three new metalogic files:
   ```bash
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Metalogic/MinSoundness.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean
   ```

3. Add imports to `Cslib.lean`:
   ```bash
   # Add after existing Metalogic imports:
   # import Cslib.Logics.Propositional.Metalogic.MinSoundness
   # import Cslib.Logics.Propositional.Metalogic.MinLindenbaum
   # import Cslib.Logics.Propositional.Metalogic.MinCompleteness
   ```

4. Verify build passes.

**Note on parallel submission**: Sub-PRs 1.7 (intuitionistic) and 1.8 (minimal) can be submitted in parallel after sub-PRs 1.3 and 1.6 merge. `MinLindenbaum.lean` imports `Soundness.lean` (from 1.6) only, not `IntLindenbaum.lean` -- so 1.7 and 1.8 are independent of each other.

**Key content of MinSoundness.lean** (96 lines):
- `theorem min_soundness : Derivable MinPropAxiom φ -> MValid φ`
- Proof by induction on derivation; minimal axioms validated in all Kripke models
- Imports: `Semantics/Kripke` (from 1.3), minimal axiom instances (from 1.2)

**Key content of MinLindenbaum.lean** (275 lines):
- `theorem min_dccs_extension : MinConsistent S -> ∃ T, S ⊆ T ∧ MinDCCS T`
- Minimal logic version of the DCCS extension (no ex falso available)
- Imports: `DeductionTheorem` and `Soundness` (from 1.6) -- note: imports Soundness, not IntSoundness

**Key content of MinCompleteness.lean** (143 lines):
- `theorem min_completeness : MValid φ -> Derivable MinPropAxiom φ`
- Same canonical Kripke model construction as intuitionistic case, specialized to minimal logic
- Imports: `Semantics/Kripke` (from 1.3), `MinSoundness` and `MinLindenbaum` (from this PR)

## PR Description

```markdown
## Summary

Prove soundness and completeness of minimal propositional Hilbert logic (no ex falso, no excluded middle) with respect to Kripke semantics. The proof structure mirrors the intuitionistic case (sub-PR 1.7) and the two PRs can be reviewed in parallel.

This PR is slightly over the 500-line target (517 insertions) but the three files are logically indivisible.

This is sub-PR 1.8 of 11 in the PR 1 decomposition.

## Changes

- `Logics/Propositional/Metalogic/MinSoundness.lean` (NEW): Minimal soundness -- `Derivable MinPropAxiom φ → MValid φ`; proof by induction on derivation
- `Logics/Propositional/Metalogic/MinLindenbaum.lean` (NEW): DCCS extension lemma for minimal logic -- every minimally consistent set extends to a minimal DCCS
- `Logics/Propositional/Metalogic/MinCompleteness.lean` (NEW): Minimal completeness -- `MValid φ → Derivable MinPropAxiom φ`; via canonical Kripke model
- `Cslib.lean`: Add imports for all three new modules

## Dependencies

- Requires: Sub-PR 1.3 (Kripke semantics), Sub-PR 1.6 (classical soundness infrastructure)
- Required by: None (independent leaf; parallel to sub-PR 1.7)

## Testing

- `lake build` passes
- `lake test` passes
- `lake lint` and `lake exe lint-style` pass
- `lake exe checkInitImports` passes
- No `sorry` in any file

## References

See [ChagrovZakharyaschev1997] for the general canonical model methodology applied to sub-classical logics.
```

## Bib References
- **ChagrovZakharyaschev1997**: Chagrov, A. and Zakharyaschev, M. (1997). *Modal Logic*. Oxford Logic Guides 35. -- Canonical model approach for sub-classical logics (added by task 123)

## Estimated LOC
- Insertions: ~517 (over 500-line target; indivisible unit)
- Deletions: ~0

## Verification

```bash
lake build
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
grep -rn "sorry" Cslib/Logics/Propositional/Metalogic/MinSoundness.lean \
  Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean \
  Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean
```
