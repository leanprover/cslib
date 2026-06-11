# Sub-PR Spec: 1.3 -- Propositional Semantics (Bivalent + Kripke)

## Task Mapping
- **Task**: 127 - subpr_1_3_propositional_semantics
- **Sub-PR**: 1.3 of 11
- **Wave**: 2
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `propositional/semantics`
- **Base**: upstream `main` after task 125 (sub-PR 1.1) merges

## Files

| File | Type | +Lines | -Lines | Notes |
|------|------|-------:|-------:|-------|
| `Cslib/Logics/Propositional/Semantics/Basic.lean` | NEW | 47 | 0 | `Valuation`, `Evaluate`, `Tautology` -- bivalent semantics |
| `Cslib/Logics/Propositional/Semantics/Kripke.lean` | NEW | 134 | 0 | `KripkeModel`, `IForces`, `IValid`, `MValid`, persistence lemma |
| `Cslib.lean` | MOD | +2 | -0 | Add imports for both new Semantics modules |

- **Total**: ~183 insertions (47 + 134 + 2 imports)

## Dependencies
- **Requires merged**: Task 125 (sub-PR 1.1 -- imports `Proposition.iff` from updated `Defs.lean`)
- **Required by**: Tasks 130, 131, 132 (classical, intuitionistic, and minimal soundness/completeness)

## Extraction Instructions

1. Create branch from upstream main after sub-PR 1.1 merges:
   ```bash
   git fetch upstream
   git checkout -b propositional/semantics upstream/main
   ```

2. Copy both new semantics files:
   ```bash
   # Create directory first if needed
   mkdir -p Cslib/Logics/Propositional/Semantics
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Semantics/Basic.lean
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/Semantics/Kripke.lean
   ```

3. Add imports to `Cslib.lean`:
   ```bash
   # Add after Instances import:
   # import Cslib.Logics.Propositional.Semantics.Basic
   # import Cslib.Logics.Propositional.Semantics.Kripke
   ```

4. Verify build passes.

**Key content of Basic.lean**:
- `Valuation`: propositional variable assignment `PropVar -> Bool`
- `Evaluate`: recursive semantic evaluation under a valuation
- `Tautology`: `∀ v, Evaluate v φ = true`

**Key content of Kripke.lean**:
- `KripkeModel`: worlds `W`, accessibility relation `R`, valuation `V : W -> PropVar -> Prop`
- `IForces` (`⊩`): intuitionistic forcing relation (monotone)
- `IValid`: validity in all Kripke models (`∀ M w, M ⊩ φ at w`)
- `MValid`: minimal forcing validity
- Persistence lemma: `w ≤ w' -> M ⊩ φ at w -> M ⊩ φ at w'`

## PR Description

```markdown
## Summary

Introduce bivalent (two-valued) and Kripke semantics for propositional logic, providing the semantic foundations for subsequent soundness and completeness proofs.

This is sub-PR 1.3 of 11 in the PR 1 decomposition.

## Changes

- `Logics/Propositional/Semantics/Basic.lean` (NEW): Classical two-valued semantics with `Valuation`, `Evaluate`, `Tautology`
- `Logics/Propositional/Semantics/Kripke.lean` (NEW): Kripke semantics with `KripkeModel`, intuitionistic forcing `IForces`, validity `IValid`/`MValid`, and the persistence (monotonicity) lemma
- `Cslib.lean`: Add imports for both new modules

## Dependencies

- Requires: Sub-PR 1.1 (3-tier hierarchy, updated `Proposition.iff`)
- Required by: Sub-PRs 1.6, 1.7, 1.8 (soundness/completeness for classical, intuitionistic, minimal logic)

## Testing

- `lake build` passes
- `lake test` passes
- `lake lint` and `lake exe lint-style` pass
- `lake exe checkInitImports` passes
- No `sorry` in any file

## References

No bib citations required in the semantics definitions themselves (citations appear in the completeness files that use these definitions).
```

## Bib References
None required for the semantics modules themselves. The soundness/completeness files (sub-PRs 1.6, 1.7, 1.8) will carry the relevant citations.

## Estimated LOC
- Insertions: ~183 (47 + 134 + 2 imports)
- Deletions: ~0

## Verification

```bash
lake build
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
grep -rn "sorry" Cslib/Logics/Propositional/Semantics/
```
