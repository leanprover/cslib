# Sub-PR Spec: 1.2 -- Propositional Axiom Extensions + IntMin Instances

## Task Mapping
- **Task**: 126 - subpr_1_2_intmin_instances
- **Sub-PR**: 1.2 of 11
- **Wave**: 2
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `propositional/intmin-instances`
- **Base**: upstream `main` after task 125 (sub-PR 1.1) merges

## Files

| File | Type | +Lines | -Lines | Notes |
|------|------|-------:|-------:|-------|
| `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` | MOD | +51 | -0 | Add `IntPropAxiom`, `MinPropAxiom`, subsumption lemmas |
| `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` | NEW | 109 | 0 | `IntuitionisticHilbert` and `MinimalHilbert` instance registrations |
| `Cslib.lean` | MOD | +1 | -0 | Add import: `import Cslib.Logics.Propositional.ProofSystem.IntMinInstances` |

- **Total**: ~161 insertions (109 new file + 51 modifications + 1 import)

## Dependencies
- **Requires merged**: Task 125 (sub-PR 1.1 -- 3-tier hierarchy must be in place)
- **Required by**: Tasks 130, 131, 132, 133 (Wave 3 classical/intuitionistic/minimal soundness-completeness and FromHilbert parameterization)

## Extraction Instructions

1. Create branch from upstream main after sub-PR 1.1 merges:
   ```bash
   git fetch upstream
   git checkout -b propositional/intmin-instances upstream/main
   ```

2. Copy the new file from `pr1/foundations-logic`:
   ```bash
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean
   ```

3. Apply modifications to Axioms.lean (add IntPropAxiom, MinPropAxiom, and subsumption lemmas from the pr1/foundations-logic version):
   ```bash
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/ProofSystem/Axioms.lean
   ```
   Note: Only apply the `+51` lines of new axiom content; do not include changes that belong to sub-PR 1.1.

4. Add the import to `Cslib.lean`:
   ```bash
   # Add: import Cslib.Logics.Propositional.ProofSystem.IntMinInstances
   # (after the existing Instances import line)
   ```

5. Verify build passes.

**Key content of IntMinInstances.lean**:
- `instance : IntuitionisticHilbert IntPropAxiom` -- registers `IntPropAxiom` as the axiom set for intuitionistic propositional Hilbert logic
- `instance : MinimalHilbert MinPropAxiom` -- registers `MinPropAxiom` as the axiom set for minimal propositional Hilbert logic
- Subsumption: `instance : ClassicalHilbert IntPropAxiom` and `instance : IntuitionisticHilbert MinPropAxiom`

## PR Description

```markdown
## Summary

Register `IntuitionisticHilbert` and `MinimalHilbert` typeclass instances for the propositional axiom sets introduced in the 3-tier hierarchy (sub-PR 1.1). This enables downstream files to derive intuitionistic and minimal logic results by typeclass synthesis without explicit axiom set arguments.

This is sub-PR 1.2 of 11 in the PR 1 decomposition.

## Changes

- `Logics/Propositional/ProofSystem/Axioms.lean`: Add `IntPropAxiom` (intuitionistic propositional axioms: IPC without `em`), `MinPropAxiom` (minimal propositional axioms: no `em` or `exfalso`), and subsumption instance declarations
- `Logics/Propositional/ProofSystem/IntMinInstances.lean` (NEW): Instance registrations for `IntuitionisticHilbert IntPropAxiom` and `MinimalHilbert MinPropAxiom`, plus upward subsumption (`ClassicalHilbert IntPropAxiom` etc.)
- `Cslib.lean`: Add import for new `IntMinInstances` module

## Dependencies

- Requires: Sub-PR 1.1 (3-tier hierarchy)
- Required by: Sub-PRs 1.6, 1.7, 1.8, 1.9 (soundness/completeness and FromHilbert)

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
- Insertions: ~161 (51 modifications + 109 new file lines + 1 import)
- Deletions: ~0

## Verification

```bash
lake build
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
grep -rn "sorry" Cslib/Logics/Propositional/ProofSystem/Axioms.lean \
  Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean
```
