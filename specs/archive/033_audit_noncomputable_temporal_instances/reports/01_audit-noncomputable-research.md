# Task 33: Audit Noncomputable Temporal Instances -- Research Report

**Session**: sess_1780979445_1b23fa
**Date**: 2026-06-08
**File under audit**: `Cslib/Logics/Temporal/ProofSystem/Instances.lean`

## 1. Noncomputable Count

The file contains **31 `noncomputable instance` declarations** (the task description estimated 35).

### Breakdown by Category

| Category | Count | Lines |
|----------|-------|-------|
| InferenceSystem | 1 | 36 |
| ModusPonens | 1 | 42 |
| HasAxiomImplyK | 1 | 51 |
| HasAxiomImplyS | 1 | 55 |
| HasAxiomEFQ | 1 | 59 |
| HasAxiomPeirce | 1 | 63 |
| PropositionalHilbert (bundled) | 1 | 69 |
| TemporalNecessitation | 1 | 74 |
| HasAxiomSerialFuture | 1 | 95 |
| HasAxiomSerialPast | 1 | 99 |
| HasAxiomLeftMonoUntilG | 1 | 103 |
| HasAxiomLeftMonoSinceH | 1 | 108 |
| HasAxiomRightMonoUntil | 1 | 113 |
| HasAxiomRightMonoSince | 1 | 118 |
| HasAxiomConnectFuture | 1 | 123 |
| HasAxiomConnectPast | 1 | 128 |
| HasAxiomEnrichmentUntil | 1 | 133 |
| HasAxiomEnrichmentSince | 1 | 138 |
| HasAxiomSelfAccumUntil | 1 | 143 |
| HasAxiomSelfAccumSince | 1 | 148 |
| HasAxiomAbsorbUntil | 1 | 153 |
| HasAxiomAbsorbSince | 1 | 158 |
| HasAxiomLinearUntil | 1 | 163 |
| HasAxiomLinearSince | 1 | 168 |
| HasAxiomUntilF | 1 | 173 |
| HasAxiomSinceP | 1 | 178 |
| HasAxiomTempLinearity | 1 | 183 |
| HasAxiomTempLinearityPast | 1 | 188 |
| HasAxiomFUntilEquiv | 1 | 193 |
| HasAxiomPSinceEquiv | 1 | 198 |
| TemporalBXHilbert (bundled) | 1 | 206 |

## 2. Root Cause Analysis: Why `noncomputable` Was Added

The original author likely added `noncomputable` based on the following reasoning:

- `DerivableIn S a` is defined as `Nonempty (S⇓a)` (see `InferenceSystem.lean:45`)
- `Nonempty` is a `Prop` that wraps a `Type`-level value
- Extracting from `Nonempty` requires `Classical.choice`, which IS noncomputable
- `DerivableIn.toDerivation` at line 57 of `InferenceSystem.lean` explicitly uses `Classical.choice` and is correctly marked `noncomputable`

**However, this reasoning is incorrect for the instances in Instances.lean.** The key distinction:

- **Extracting** from `Nonempty` (Prop -> Type): requires `Classical.choice`, noncomputable
- **Constructing** `Nonempty` via `⟨value⟩` (Type -> Prop): always computable
- **Eliminating** `Nonempty` into another `Prop` (Prop -> Prop): computable via small elimination

All 31 instances in this file only perform:
1. Construction: `⟨DerivationTree.axiom ...⟩` wraps a tree in `Nonempty` (computable)
2. Small elimination: `obtain ⟨d⟩ := h` pattern-matches `Nonempty` but targets a `Prop` output (computable)

None use `Classical.choice`, `Nonempty.some`, or `DerivableIn.toDerivation`.

## 3. Verification: All 31 Markers Are Removable

All 31 instances were tested in a standalone `lean_run_code` snippet that reproduces the entire file without any `noncomputable` annotations. The result: **all compile successfully** with zero errors (only cosmetic long-line warnings).

The test covered:
- The `InferenceSystem` instance (line 36)
- `ModusPonens` with `obtain ⟨d⟩ := h` elimination (line 42)
- All 4 propositional axiom instances (lines 51-65)
- `PropositionalHilbert` bundled instance (line 69)
- `TemporalNecessitation` with complex proof including `simp` and `rwConclusion` (line 74)
- All 22 temporal axiom instances (lines 95-201)
- `TemporalBXHilbert` bundled instance (line 206)

### Why the TemporalNecessitation Instance Is Also Computable

The `tempNecPast` field has the most complex proof in the file, involving:
- `obtain ⟨d⟩ := h` -- small elimination (Prop -> Prop), computable
- `Temporal.DerivationTree.temporal_duality` -- inductive constructor, computable
- `Temporal.DerivationTree.temporal_necessitation` -- inductive constructor, computable
- `simp only [...]` -- computable rewriting
- `InferenceSystem.rwConclusion` -- defined as `h ▸ p`, computable

No step requires classical reasoning.

## 4. The DerivableIn Pattern

```lean
def DerivableIn S [InferenceSystem S α] (a : α) := Nonempty (S⇓a)
```

`DerivableIn` wraps a Type-valued derivation (`S⇓a : Sort v`) in `Nonempty` to produce a `Prop`. This is a standard pattern for "proof-irrelevant derivability" -- we care that a derivation EXISTS, not what it is.

Key computability properties:
- `Nonempty.intro : α → Nonempty α` -- always computable
- Pattern matching on `Nonempty` into `Prop` -- computable (small elimination)
- `Classical.choice : Nonempty α → α` -- the ONLY noncomputable operation on `Nonempty`

Since the typeclass fields (`mp`, `tempNec`, `implyK`, etc.) all have return type `DerivableIn S (...)` which is `Prop`, they never need to extract a TYPE-valued witness from `Nonempty`. They only construct new `Nonempty` values or pattern-match to build other `Nonempty` values.

## 5. Comparison with Modal Instances

There are **no modal instance files** in `Cslib/Logics/Modal/ProofSystem/`. The modal logic modules (`Modal/Basic.lean`, `Modal/Cube.lean`, `Modal/Denotation.lean`) do not include proof system instances. Therefore no comparison with modal instances is possible.

However, the Foundation-level theorem files for modal logic DO use `noncomputable section`:
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` (line 52)
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` (line 74)

These are likely also unnecessarily noncomputable, following the same pattern.

## 6. Broader Scope: Noncomputable Sections Across the Proof System

The `noncomputable` issue extends beyond Instances.lean. There are **8 additional files** using `noncomputable section` in the proof system theorem layer:

| File | Lines | Likely Removable? |
|------|-------|-------------------|
| `Foundations/Logic/Theorems/Combinators.lean` | 48-330 | Yes (verified) |
| `Foundations/Logic/Theorems/Propositional/Core.lean` | 49-284 | Very likely |
| `Foundations/Logic/Theorems/Propositional/Connectives.lean` | 48-544 | Very likely |
| `Foundations/Logic/Theorems/Propositional/Reasoning.lean` | 28-43 | Very likely |
| `Foundations/Logic/Theorems/Modal/Basic.lean` | 52-199 | Very likely |
| `Foundations/Logic/Theorems/Modal/S5.lean` | 74-583 | Very likely |
| `Foundations/Logic/Theorems/BigConj.lean` | 88-136 | Very likely |
| `Logics/Temporal/Theorems/TemporalDerived.lean` | 33-268 | Very likely |

All these files work with `DerivableIn` (Prop-valued) using `ModusPonens.mp` and similar typeclass methods. They never extract Type-valued derivations from `Nonempty`. I verified the `Combinators.lean` case via `lean_run_code`.

**Note**: The files in `Crypto/` (`Shamir.lean`, `Shamir/Polynomial.lean`) also use `noncomputable section` but these are unrelated -- they likely genuinely need noncomputable for Galois field arithmetic.

## 7. Genuinely Noncomputable Definitions (Correctly Marked)

For reference, the following definitions in the inference system ARE correctly `noncomputable`:

| Definition | File | Reason |
|-----------|------|--------|
| `DerivableIn.toDerivation` | InferenceSystem.lean:57 | Uses `Classical.choice` to extract `S⇓a` from `Nonempty (S⇓a)` |
| `Coe (DerivableIn S a) (S⇓a)` | InferenceSystem.lean:61 | Delegates to `toDerivation` |
| `encodeNat` | Temporal/Syntax/Formula.lean:130 | Uses `Encodable` which may require classical choice |
| `Countable/Infinite` instance | Temporal/Syntax/Formula.lean:207 | Depends on `encodeNat` |

These should NOT be modified.

## 8. Downstream Impact Assessment

### Direct Dependents of Instances.lean

Only one file directly imports Instances.lean:
- `Cslib/Logics/Temporal/ProofSystem.lean` (barrel/re-export file)

### Indirect Impact

Removing `noncomputable` from instances makes them available for computable code. This is strictly a relaxation -- any code that currently works will continue to work. The only possible issue would be if some downstream code relied on the instances being noncomputable to suppress certain Lean elaboration paths, which is extremely unlikely and would be a bug in itself.

### TemporalDerived.lean

This file uses `noncomputable section` independently. It does NOT import Instances.lean -- it works at the generic typeclass level. Removing `noncomputable` from Instances.lean has zero effect on it.

## 9. Recommendations

### Primary Recommendation: Remove All 31 `noncomputable` Markers

**Action**: Remove the `noncomputable` keyword from all 31 instance declarations in `Cslib/Logics/Temporal/ProofSystem/Instances.lean`.

**Risk**: None. Verified by complete standalone reproduction. The change is strictly a relaxation.

**Verification**: After removal, run `lake build Cslib.Logics.Temporal.ProofSystem.Instances` to confirm.

### Implementation Approach

This is a pure text-removal task. For each of the 31 instances, change:
```lean
noncomputable instance : SomeClass ... where
```
to:
```lean
instance : SomeClass ... where
```

### Estimated Effort

- **Implementation**: Low (10-15 minutes). Pure mechanical text removal -- 31 occurrences of the word `noncomputable`.
- **Verification**: Low (5 minutes). Single `lake build` of the module.
- **Risk**: None.

### Follow-Up Recommendation (Out of Scope)

Consider a separate task to audit the 8 `noncomputable section` blocks in the theorem layer files listed in Section 6. These are almost certainly also removable, which would clean up approximately 2000 lines worth of `noncomputable` scope across the proof system. This would improve the codebase by:
1. Accurately reflecting the computability status of these definitions
2. Making the definitions available for potential future use in computable contexts
3. Removing a source of confusion for developers who might incorrectly assume these proofs require classical reasoning
