# Sub-PR Spec: 1.11 -- ND-Hilbert Extensional Equivalence

## Task Mapping
- **Task**: 135 - subpr_1_11_nd_hilbert_equivalence
- **Sub-PR**: 1.11 of 11
- **Wave**: 4
- **Parent Task**: 124 (PR 1 Decomposition)
- **Source Branch**: `pr1/foundations-logic`

## Branch
- **Name**: `propositional/nd-hilbert-equivalence`
- **Base**: upstream `main` after tasks 128 + 133 (sub-PRs 1.4 + 1.9) merge

## Files

| File | Type | +Lines | -Lines | Notes |
|------|------|-------:|-------:|-------|
| `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` | NEW | 231 | 0 | Hilbert-ND extensional equivalence + instances for 3 logics |
| `Cslib.lean` | MOD | +1 | -0 | Add import for `NaturalDeduction.Equivalence` |

- **Total**: ~232 insertions (231 new file + 1 import)

## Dependencies
- **Requires merged**: Task 128 (sub-PR 1.4 -- standalone ND derived rules), Task 133 (sub-PR 1.9 -- parameterized `FromHilbert`)
- **Required by**: None (independent leaf -- capstone result of the ND/Hilbert development)

## Extraction Instructions

1. Create branch from upstream main after sub-PRs 1.4 + 1.9 merge:
   ```bash
   git fetch upstream
   git checkout -b propositional/nd-hilbert-equivalence upstream/main
   ```

2. Copy the new Equivalence file:
   ```bash
   git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean
   ```

3. Add import to `Cslib.lean`:
   ```bash
   # Add after NaturalDeduction imports:
   # import Cslib.Logics.Propositional.NaturalDeduction.Equivalence
   ```

4. Verify build passes.

**Key content of Equivalence.lean** (231 lines):
- `theorem nd_iff_hilbert_cl : Theory.Derivable φ ↔ Derivable ClassPropAxiom φ`
- `theorem nd_iff_hilbert_int : Theory.Derivable φ ↔ Derivable IntPropAxiom φ` (restricted to intuitionistic logic)
- `theorem nd_iff_hilbert_min : Theory.Derivable φ ↔ Derivable MinPropAxiom φ` (restricted to minimal logic)
- Instances of an `NDHilbertEquivalent` typeclass for each of the three logic levels
- Forward direction (`ND -> Hilbert`): uses `FromHilbert` (from 1.9) plus cases for each derived rule
- Backward direction (`Hilbert -> ND`): uses `DerivedRules` (from 1.4) to simulate Hilbert axiom applications

**Significance**: This is the capstone result of the entire ND development -- it establishes that the standalone ND system and the Hilbert system are definitionally equivalent as proof systems, enabling free transfer of results between them.

## PR Description

```markdown
## Summary

Prove that the standalone natural deduction (ND) derivability relation and the Hilbert derivability relation are extensionally equivalent for classical, intuitionistic, and minimal propositional logic. This capstone result enables transfer of proofs between the two proof systems.

This is sub-PR 1.11 of 11 in the PR 1 decomposition.

## Changes

- `Logics/Propositional/NaturalDeduction/Equivalence.lean` (NEW): Extensional equivalence `Theory.Derivable φ ↔ Derivable ax φ` for each axiom set (`ClassPropAxiom`, `IntPropAxiom`, `MinPropAxiom`); includes `NDHilbertEquivalent` typeclass instances
- `Cslib.lean`: Add import for new module

## Dependencies

- Requires: Sub-PR 1.4 (standalone ND derived rules), Sub-PR 1.9 (parameterized `FromHilbert`)
- Required by: None (independent leaf; capstone of ND/Hilbert development)

## Testing

- `lake build` passes
- `lake test` passes
- `lake lint` and `lake exe lint-style` pass
- `lake exe checkInitImports` passes
- No `sorry` in any file

## References

No new bib citations needed (equivalence result follows from sub-PRs 1.4 and 1.9).
```

## Bib References
None required. The Curry-Howard correspondence background is already established in earlier files; this PR proves a concrete equivalence result with no new mathematical framework.

## Estimated LOC
- Insertions: ~232 (231 new file + 1 import)
- Deletions: ~0

## Verification

```bash
lake build
lake test
lake lint
lake exe lint-style
lake exe checkInitImports
grep -rn "sorry" Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean
```
