# Phase 4 Handoff: Propositional Metalogic Refactor Complete

## Summary

Phase 4 of the syntactic sugar refactor (task 165) is complete. All Propositional/Metalogic
files have been processed and the full PL CI pipeline passes.

## Files Modified

### MinCompleteness.lean
- `Proposition.bot ∈ w.val` → `⊥ ∈ w.val` (minBotForces definition)
- `φ.imp ψ ∈ T.val` → `(φ → ψ) ∈ T.val` (min_truth_lemma backward case)

### MinLindenbaum.lean
- `Proposition.bot` → `(⊥ : PL.Proposition Atom)` in min_consistent type signature
- `(a.imp φ)` → `(a → φ)` in min_deriv_from_closure_to_S IH call
- `(φ.imp ψ)` → `(φ → ψ)` in deductionWithMem explicit arg
- `(propDerivationSystem MinPropAxiom).Deriv L' (φ.imp ψ)` → `... (φ → ψ)` in return type of min_deriv_imp_of_union

### IntLindenbaum.lean
- `(a.imp φ)` → `(a → φ)` in int_deriv_from_closure_to_S IH call
- `(φ.imp ψ)` → `(φ → ψ)` in deductionWithMem explicit arg
- `(propDerivationSystem IntPropAxiom).Deriv L' (φ.imp ψ)` → `... (φ → ψ)` in return type of int_deriv_imp_of_union

### Completeness.lean
- `h_mcs (φ.imp ψ) with h | h` → `h_mcs (φ → ψ) with h | h` in prop_negation_complete call

## Files Skipped (and Why)

- **MCS.lean**: All `.imp` in `∀`-quantified function parameter types (SKIP ALL per constraints)
- **DeductionTheorem.lean**: All `.imp` in `∀`-quantified function parameter types (SKIP ALL)
- **Soundness.lean**: No occurrences (already clean)
- **IntSoundness.lean**: No occurrences (already clean)
- **MinSoundness.lean**: No occurrences (already clean)
- **IntCompleteness.lean**: `.bot =>` and `.imp φ ψ =>` are pattern match arms (SKIP)
- **intNegPhiImpPsi body** (IntLindenbaum): Explicit DerivationTree type ascriptions - attempting replacement broke `.implyK`/`.implyS` dot notation resolution
- **Dense DerivationTree sections** (Completeness, IntLindenbaum, MinLindenbaum lines 155-186): Complex type ascriptions where notation change risks breaking dot-notation type inference

## CI Results

- `lake build Cslib.Logics.Propositional.Metalogic.*` - PASSED
- `lake exe checkInitImports` - PASSED
- `lake exe lint-style` - PASSED
- `lake lint` - Pre-existing errors in Bimodal and Temporal (out of scope)
- `lake shake` - Pre-existing warnings in Temporal (out of scope)
- Zero sorries in modified files

## Remaining Phases

- Phase 5: Modal/Basic, Cube, Denotation, LogicalEquivalence [NOT STARTED]
- Phase 6: Modal/ProofSystem/Instances (16 files) [NOT STARTED]
- Phase 7: Modal/Metalogic and Systems, Full Modal CI [NOT STARTED]
- Phase 8: Temporal/Syntax, Semantics, ProofSystem, Theorems [NOT STARTED]
- Phase 9: Temporal/Metalogic and Full Temporal CI [NOT STARTED]

## Key Lesson Learned

When replacing `.imp` with `→` in DerivationTree explicit type ascriptions, type inference
for dot-notation constructors (`.implyK`, `.implyS`, etc.) can break because Lean uses
the explicit formula type to disambiguate the axiom typeclass. The safest replacements are:
- Formula terms in function call positions (not type ascriptions)
- Set membership contexts (`φ.imp ψ ∈ S` → `(φ → ψ) ∈ S`)
- Return type existentials (`Deriv L (φ.imp ψ)` → `Deriv L (φ → ψ)`)
- IH argument positions
