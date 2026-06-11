# Implementation Summary: Task #120

- **Task**: 120 - Parameterize Natural Deduction Equivalence
- **Status**: Implemented
- **Session**: sess_1781189480_732247
- **Date**: 2026-06-11

## Changes Made

### Phase 1: Parameterize FromHilbert.lean
- Replaced all hardcoded `PropositionalAxiom` references with generic `{Axioms : PL.Proposition Atom -> Prop}` parameter
- Added explicit axiom parameters (`h_K`, `h_S`, `h_EFQ`) following the `deductionTheorem` pattern from DeductionTheorem.lean
- `impI`, `hilbertCut`: take `h_K` and `h_S` (for deduction theorem)
- `impE`, `assume`, `axiomRule`, `hilbertWeakening`: no axiom parameters needed
- `botE`: takes `h_EFQ`
- Added `subst_preserves_intAxiom` (3 cases: implyK, implyS, efq) and `subst_preserves_minAxiom` (2 cases: implyK, implyS)
- Kept original `subst_preserves_axiom` for classical (4 cases)
- Generalized `hilbertSubstitution` to work across different axiom predicates via `h_subst` witness
- Updated all Deriv-level wrappers with matching parameters

### Phase 2: Split and Parameterize HilbertDerivedRules.lean
- Organized rules into Intuitionistic (K, S, EFQ) and Classical (K, S, EFQ, Peirce) layers
- Intuitionistic rules: `hilbertNegI`, `hilbertNegE`, `hilbertTopI`, `hilbertAndI`, `hilbertOrI1`, `hilbertOrI2`, `hilbertIffI`
- Classical rules: `hilbertDne`, `hilbertAndE1`, `hilbertAndE2`, `hilbertOrE`, `hilbertIffE1`, `hilbertIffE2`
- Used explicit parameters on each definition (not section variables) for reliable parameter threading
- All Deriv-level wrappers updated with matching parameters

### Phase 3: Parameterize Equivalence.lean
- Added generic `AxiomTheory Axioms := { phi | Axioms phi }` with simp lemma `mem_axiomTheory`
- Kept `HilbertAxiomTheory` as `abbrev` for backward compatibility
- `hilbertToND`: purely structural (no axiom params needed), parameterized over generic `Axioms`
- `ndToHilbert`: takes `h_K`, `h_S`, `h_EFQ` for deduction theorem and botE cases
- `hilbert_iff_nd`: generic equivalence for any `Axioms` with K, S, EFQ
- Added `hilbert_iff_nd_int` (instantiates at `IntPropAxiom`) and `hilbert_iff_nd_cl` (instantiates at `PropositionalAxiom`)

### Phase 4: Docstring Cleanup and Final Verification
- Fixed stale backward-compat alias docstring in Derivation.lean
- Full `lake build` succeeds (2954 jobs, zero errors)
- `lean_verify` on all three equivalence theorems: only standard Lean axioms (propext, Classical.choice, Quot.sound)
- Zero sorries, zero vacuous definitions, zero new axioms

## Files Modified
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` -- Parameterized all definitions
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` -- Split into intuitionistic/classical, parameterized
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` -- Parameterized equivalence, added corollaries
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- Fixed stale docstring

## Plan Deviations
- Intuitionistic/Classical split uses explicit parameters on each definition rather than Lean `section` blocks with `variable` declarations. The `section` approach had issues with section variable auto-inclusion in the `module` system. The explicit parameter approach is consistent with FromHilbert.lean and DeductionTheorem.lean.
- `hilbertSubstitution` was generalized more broadly than planned: it now works across different axiom predicates (source `Axioms` to target `Axioms'`) via a substitution-closure witness `h_subst`, rather than requiring source and target to use the same predicate. This is a strictly more general signature.

## Verification
- `lake build`: Pass (zero errors)
- `grep sorry`: 0 occurrences
- `grep vacuous`: 0 occurrences
- `grep axiom`: 0 new axioms
- `lean_verify hilbert_iff_nd`: propext, Classical.choice, Quot.sound only
- `lean_verify hilbert_iff_nd_int`: propext, Classical.choice, Quot.sound only
- `lean_verify hilbert_iff_nd_cl`: propext, Classical.choice, Quot.sound only
