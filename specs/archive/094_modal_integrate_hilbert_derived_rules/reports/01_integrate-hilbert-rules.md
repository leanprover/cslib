# Research Report: Integrate HilbertDerivedRules into Module Graph

**Task**: 94 -- Add untracked HilbertDerivedRules.lean to the build
**Status**: Researched
**Date**: 2026-06-10

## Summary

HilbertDerivedRules.lean (447 lines, sorry-free) compiles cleanly and has zero namespace conflicts. It needs a single import line added to `Cslib.lean` (the root aggregator). Two sibling files (DerivedRules.lean, Equivalence.lean) are also missing from the root aggregator and should be added in the same change for completeness.

## File Location

```
Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean
```

## What HilbertDerivedRules.lean Provides

The file lives in namespace `Cslib.Logic.PL` and provides derived introduction/elimination rules for Lukasiewicz-encoded connectives (negation, top, conjunction, disjunction, biconditional) in the Hilbert-style proof system (`DerivationTree` with `List` contexts).

### Type-level definitions (26 total):
- **Negation**: `hilbertNegI` (noncomputable), `hilbertNegE`
- **Verum**: `hilbertTopI`
- **Double Negation**: `hilbertDne`
- **Conjunction**: `hilbertAndI` (noncomputable), `hilbertAndE1`, `hilbertAndE2`
- **Disjunction**: `hilbertOrI1` (noncomputable), `hilbertOrI2`, `hilbertOrE` (noncomputable)
- **Biconditional**: `hilbertIffI` (noncomputable), `hilbertIffE1`, `hilbertIffE2`
- **Deriv-level wrappers**: All of the above with `Deriv` suffix (13 theorems)

### Import chain:
```
HilbertDerivedRules -> FromHilbert -> DeductionTheorem -> ProofSystem/Derivation
```

## Current Module Graph Status

### Files in NaturalDeduction directory:
| File | In Cslib.lean? | Imports |
|------|---------------|---------|
| Basic.lean | YES (line 294) | Defs, InferenceSystem, Mathlib.Data.Finset.* |
| DerivedRules.lean | NO | Basic |
| Equivalence.lean | NO | Basic, FromHilbert |
| FromHilbert.lean | YES (line 295) | DeductionTheorem |
| HilbertDerivedRules.lean | NO | FromHilbert |

### Key finding: Three files are orphaned
Not just HilbertDerivedRules -- `DerivedRules.lean` and `Equivalence.lean` are also absent from `Cslib.lean`. All three compile successfully when built individually (641 jobs total, zero errors).

## Verification Results

### Build verification:
```
lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules
# Build completed successfully (583 jobs)
```

### Namespace conflict check:
All 26 definitions in HilbertDerivedRules.lean have unique names across the entire codebase. No conflicts.

### Usage check:
No file in the codebase currently imports or references definitions from HilbertDerivedRules.lean, DerivedRules.lean, or Equivalence.lean (outside of NaturalDeduction directory internal imports).

### Linter warnings:
One pre-existing linter warning in FromHilbert.lean (unused `[DecidableEq Atom']` in `hilbertSubstitutionDeriv`) -- not related to HilbertDerivedRules.

## Recommended Implementation

### Option A (Minimal -- task scope): Add only HilbertDerivedRules.lean
Add one line to `Cslib.lean` after line 295:
```lean
public import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules
```

### Option B (Complete -- recommended): Add all three orphaned files
Add three lines to `Cslib.lean`, maintaining alphabetical order after line 294:
```lean
public import Cslib.Logics.Propositional.NaturalDeduction.Basic          -- existing (line 294)
public import Cslib.Logics.Propositional.NaturalDeduction.DerivedRules   -- NEW
public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence    -- NEW
public import Cslib.Logics.Propositional.NaturalDeduction.FromHilbert    -- existing (line 295)
public import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules  -- NEW
```

### Rationale for Option B:
1. All three files are already sorry-free and compile cleanly
2. DerivedRules and Equivalence contain important theorems (ND-Hilbert equivalence, derived connective rules) that should be in the build
3. The convention in Cslib.lean is to list all project Lean files -- these were likely omitted by oversight when created
4. Adding all three at once avoids future cleanup tasks

## Risks and Blockers

- **Risk**: None identified. All files compile, no namespace conflicts, no sorry.
- **Blockers**: None.
- **Build time impact**: Minimal. HilbertDerivedRules adds ~1 build job (its transitive deps are already in the graph via FromHilbert). DerivedRules and Equivalence similarly add ~2 jobs.

## Implementation Complexity

Single-phase task: edit `Cslib.lean` to add import lines, then run `lake build` to verify. Estimated effort: trivial (< 5 minutes).
