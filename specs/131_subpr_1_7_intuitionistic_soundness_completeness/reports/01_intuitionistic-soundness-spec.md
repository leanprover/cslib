# Sub-PR Spec: 1.7 -- Intuitionistic Soundness + Completeness

## Task Mapping
- **Task**: 131 - subpr_1_7_intuitionistic_soundness_completeness
- **Sub-PR**: 1.7 of 11
- **Wave**: 3
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `propositional/intuitionistic-soundness-completeness`
- **Base**: upstream `main` after tasks 127 + 130 (sub-PRs 1.3 + 1.6) merge

## Files

| File | Type | +Lines | -Lines | Notes |
|------|------|-------:|-------:|-------|
| `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` | NEW | 103 | 0 | Intuitionistic soundness w.r.t. Kripke models |
| `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` | NEW | 325 | 0 | DCCS extension lemma (deductively closed consistent set extension) |
| `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` | NEW | 127 | 0 | Intuitionistic completeness via Kripke canonical model |
| `Cslib.lean` | MOD | +3 | -0 | Add imports for all three new modules |

- **Total**: ~558 insertions (103 + 325 + 127 + 3 imports)
- **Note**: Slightly over the 500-line target (558 vs 500). The three files form a single logical unit: IntLindenbaum is the key lemma required by IntCompleteness, and splitting further would leave non-buildable partial proofs.

## Dependencies
- **Requires merged**: Task 127 (sub-PR 1.3 -- Kripke semantics), Task 130 (sub-PR 1.6 -- classical soundness/completeness infrastructure)
- **Required by**: None (independent leaf -- no other sub-PR depends on this)

## Extraction Instructions

1. Create branch from upstream main after sub-PRs 1.3 + 1.6 merge:
   ```bash
   git fetch upstream
   git checkout -b propositional/intuitionistic-soundness-completeness upstream/main
   ```

2. Copy all three new metalogic files:
   ```bash
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Metalogic/IntSoundness.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean
   ```

3. Add imports to `Cslib.lean`:
   ```bash
   # Add after existing Metalogic imports:
   # import Cslib.Logics.Propositional.Metalogic.IntSoundness
   # import Cslib.Logics.Propositional.Metalogic.IntLindenbaum
   # import Cslib.Logics.Propositional.Metalogic.IntCompleteness
   ```

4. Verify build passes.

**Key content of IntSoundness.lean** (103 lines):
- `theorem int_soundness : Derivable IntPropAxiom φ -> IValid φ`
- Proof by induction on derivation; intuitionistic axioms are validated at all Kripke worlds
- Imports: `Semantics/Kripke` (from 1.3), `Derivation` (updated by 1.1), `Axioms` (updated by 1.2)

**Key content of IntLindenbaum.lean** (325 lines):
- `theorem dccs_extension : Consistent S -> ∃ T, S ⊆ T ∧ DCCS T`
- where DCCS = deductively closed consistent set (intuitionistic analogue of MCS)
- Implication witness construction: if `φ → ψ ∉ T`, find a consistent extension containing `φ` but not `ψ`
- Imports: `DeductionTheorem` and `MCS` (both in upstream, updated by 1.1)

**Key content of IntCompleteness.lean** (127 lines):
- `theorem int_completeness : IValid φ -> Derivable IntPropAxiom φ`
- Canonical Kripke model: worlds = DCCS sets, accessibility = subset relation, valuation = membership
- Imports: `Semantics/Kripke` (from 1.3), `IntSoundness` (from this PR), `IntLindenbaum` (from this PR)

## PR Description

```markdown
## Summary

Prove soundness and completeness of intuitionistic propositional Hilbert logic (IPC) with respect to Kripke semantics. The completeness proof uses a canonical Kripke model whose worlds are deductively closed consistent sets (DCCS), with accessibility given by set inclusion.

This PR is slightly over the 500-line target (558 insertions) but the three files are logically indivisible: `IntLindenbaum.lean` is the key extension lemma required by `IntCompleteness.lean`.

This is sub-PR 1.7 of 11 in the PR 1 decomposition.

## Changes

- `Logics/Propositional/Metalogic/IntSoundness.lean` (NEW): Intuitionistic soundness -- `Derivable IntPropAxiom φ → IValid φ`; proof by induction on derivation
- `Logics/Propositional/Metalogic/IntLindenbaum.lean` (NEW): DCCS extension lemma (intuitionistic Lindenbaum lemma) -- every consistent set extends to a DCCS; includes implication witness construction
- `Logics/Propositional/Metalogic/IntCompleteness.lean` (NEW): Intuitionistic completeness -- `IValid φ → Derivable IntPropAxiom φ`; via canonical Kripke model
- `Cslib.lean`: Add imports for all three new modules

## Dependencies

- Requires: Sub-PR 1.3 (Kripke semantics), Sub-PR 1.6 (classical soundness/completeness infrastructure)
- Required by: None (independent leaf)

## Testing

- `lake build` passes
- `lake test` passes
- `lake lint` and `lake exe lint-style` pass
- `lake exe checkInitImports` passes
- No `sorry` in any file

## References

See [ChagrovZakharyaschev1997] for the general canonical model approach and [TroelstraVanDalen1988] for the intuitionistic Lindenbaum construction.
```

## Bib References
- **ChagrovZakharyaschev1997**: Chagrov, A. and Zakharyaschev, M. (1997). *Modal Logic*. Oxford Logic Guides 35. -- Canonical model methodology
- **TroelstraVanDalen1988**: Troelstra, A.S. and van Dalen, D. (1988). *Constructivism in Mathematics, Vol. I*. -- Intuitionistic Lindenbaum/completeness construction (added by task 123)

## Estimated LOC
- Insertions: ~558 (over 500-line target; indivisible unit)
- Deletions: ~0

## Verification

```bash
lake build
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
grep -rn "sorry" Cslib/Logics/Propositional/Metalogic/IntSoundness.lean \
  Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean \
  Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean
```
