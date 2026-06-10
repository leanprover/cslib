# Noncomputable Usage Audit

**Task**: 77 - audit_noncomputable_usage
**Date**: 2026-06-10
**Session**: sess_1749572400_a3b7c1

## Executive Summary

The Cslib codebase contains **390 occurrences** of `noncomputable` across **99 files** (out of 333 total `.lean` files, i.e., 30% of files). The vast majority (**327/378**, excluding comments/end markers) are in the `Logics/` module, and nearly all are **genuinely necessary** due to fundamental reliance on classical axioms (`Classical.choice`, `Classical.propDecidable`) inherent to the mathematical domains being formalized.

Only a small number of cases (estimated 5-10 declarations) are potentially removable with targeted refactoring.

## Quantitative Breakdown

### By Declaration Type

| Type | Count |
|------|-------|
| `noncomputable def` | 354 |
| `noncomputable section` | 12 (24 lines including `end` markers) |
| `noncomputable instance` | 9 |
| **Total meaningful** | ~375 |

### By Top-Level Module

| Module | Count | % of Total |
|--------|-------|------------|
| `Logics/` | 327 | 86.5% |
| `Crypto/` | 19 | 5.0% |
| `Computability/` | 12 | 3.2% |
| `MachineLearning/` | 10 | 2.6% |
| `Foundations/` | 9 | 2.4% |
| `Probability/` | 1 | 0.3% |

### By Logics Submodule

| Submodule | Count |
|-----------|-------|
| `Bimodal/Metalogic/` | 177 |
| `Temporal/Metalogic/` | 77 |
| `Bimodal/Theorems/` | 49 |
| `Modal/Metalogic/` | 8 |
| `Propositional/Metalogic/` | 6 |
| `Propositional/NaturalDeduction/` | 4 |
| `Temporal/Syntax/` | 2 |
| `LinearLogic/CLL/` | 2 |
| `HML/` | 1 |
| `Bimodal/ProofSystem/` | 1 |

### Top 10 Files by Noncomputable Count

| File | Count |
|------|-------|
| `Bimodal/Theorems/TemporalDerived.lean` | 37 |
| `Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` | 24 |
| `Temporal/Metalogic/Chronicle/PointInsertion.lean` | 22 |
| `Bimodal/Metalogic/BXCanonical/CanonicalModel.lean` | 19 |
| `Bimodal/Metalogic/BXCanonical/Quasimodel/Construction.lean` | 12 |
| `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` | 12 |
| `Bimodal/Metalogic/BXCanonical/Frame.lean` | 11 |
| `Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` | 10 |
| `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 10 |
| `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` | 10 |

## Root Cause Analysis

### Category 1: Classical Axiom Dependency (DerivationTree extraction) -- ~220 declarations

**This is the dominant pattern.** The Hilbert-style proof system uses an `InferenceSystem` typeclass where derivability is expressed via `Nonempty` (proof-irrelevant existential). To actually construct derivation trees (`DerivationTree`), the codebase uses:

```lean
def unwrap {phi : Formula Atom}
    (h : InferenceSystem.DerivableIn Bimodal.HilbertTM phi) :
    DerivationTree FrameClass.Base [] phi := h.some
```

The `.some` call on `Nonempty` is `Classical.choice` under the hood, making `unwrap` noncomputable. Every definition that transitively calls `unwrap` (or its variants `unwrap'`) inherits noncomputability.

**Affected areas**: All `Theorems/` modules (Combinators, Propositional/Core, Propositional/Connectives, TemporalDerived, GeneralizedNecessitation, Perpetuity/*), plus all Metalogic modules that build derivation trees.

**Removability**: **Not removable without fundamental redesign.** The proof-irrelevant `Nonempty` wrapping is an architectural choice that separates the statement "a derivation exists" from "here is a specific derivation." Classical extraction is mathematically correct and standard in this domain. To remove it, the `InferenceSystem` typeclass would need to use proof-relevant witnesses everywhere, which would be a massive refactor with unclear benefits (derivation trees are not intended to be computed).

### Category 2: Classical.propDecidable for Case Splits -- ~60 declarations

Many metalogic files use `attribute [local instance] Classical.propDecidable` to enable `if...then...else` and `by_cases` on undecidable propositions (e.g., formula membership in sets). This is used in:

- **Deduction theorems** (Bimodal, Temporal, Modal, Propositional): Case split on `A in Gamma` during structural induction on derivation trees
- **MCS properties**: Checking membership in maximal consistent sets
- **Canonical model construction**: Checking set containment for modal witnesses
- **Chronicle construction**: Point insertion and counterexample elimination

**Files**: 32 files use `attribute [local instance] Classical.propDecidable`

**Removability**: **Not removable.** These case splits are over propositions like "formula phi is in set Omega" where `Omega` is an arbitrary set of formulas with no decidable membership. This is inherent to the mathematics of Lindenbaum lemma and canonical model constructions in modal logic.

### Category 3: Classical.choose for Existential Witnesses -- ~40 declarations

Several definitions extract witnesses from existential proofs using `Classical.choose`:

- **Lindenbaum MCS construction**: `set_lindenbaum(...).choose` to obtain maximal consistent extensions
- **Canonical chain construction**: `fwd_succ`, `bwd_pred`, `fwd_chain`, `bwd_chain` using `.choose` on witness seeds
- **Counterexample elimination**: Walking through chronicles extracting witnesses
- **URM evaluation**: `Classical.choose` on halting proofs
- **Fresh element selection**: `Infinite.exists_notMem_finset |>.choose`
- **Buchi congruence parameterization**: `Classical.choose h` for quotient representatives

**Removability**: Mostly **not removable**. The existentials being witnessed are inherently nonconstructive (Lindenbaum's lemma uses Zorn's lemma, which is equivalent to the axiom of choice). The URM `evalState` case uses `Classical.choose` on halting proofs, which is a design choice -- but since halting is undecidable in general, this too is inherently noncomputable.

### Category 4: Classical.choice for Instance Construction -- ~10 declarations

- `Denumerable PotentialCounterexample`: Uses `Classical.choice (nonempty_denumerable _)` (2 files)
- `Countable/Infinite Formula`: `Classical.choice (nonempty_denumerable (Formula Atom))` (1 file)
- `DerivableIn.toDerivation`: `Classical.choice d` to extract derivation from `Nonempty` (1 file)
- Order isomorphism for dense linear orders: `Classical.choice (Order.iso_of_countable_dense ...)` (1 file)

**Removability**: **Not removable.** These are standard uses of classical axioms to construct instances where the type is provably denumerable/countable but no constructive enumeration is available.

### Category 5: Measure/Probability Theory -- ~15 declarations

Definitions involving `Measure`, `PMF`, or probability distributions:

- `error`, `optimalError`, `hypothesisError`, `falsePositiveError`, `falseNegativeError` (PAC learning)
- `sampleComplexity`, `rsampleComplexity` (PAC learning)
- `empiricalMeasure`, `empiricalError` (version space)
- `ciphertextDist`, `jointDist`, `marginalCiphertextDist`, `posteriorMsgDist` (perfect secrecy)
- `posteriorDist` (PMF)
- `vcDim` (VC dimension via `sSup`)

**Removability**: **Not removable.** These use Mathlib's `MeasureTheory.Measure` and `PMF` types, which are inherently noncomputable in Lean 4's Mathlib (they involve real-valued measures on sigma-algebras). The `vcDim` definition uses `sSup` on natural numbers, which is also noncomputable.

### Category 6: Polynomial/Field Operations -- ~10 declarations

Shamir secret sharing uses `noncomputable section` because polynomial operations over abstract `Field F` are noncomputable in Mathlib:

- `share`, `reconstruct`, `uniformTailSampler`, `privacyCorrectionPolynomial`, `privacyCorrection`, `schemeWith`, `scheme`
- `tailPolynomial` and related operations

**Removability**: **Not removable without specializing to concrete fields.** Mathlib's polynomial ring over an abstract field uses classical operations. One could potentially specialize to computable fields (like `ZMod p`), but this would sacrifice generality.

### Category 7: Miscellaneous Inherently Noncomputable -- ~20 declarations

- `Nat.segment` / `segment'`: Uses `Nat.count` with `open scoped Classical` (membership in range is not decidable in general)
- `flatten` (OmegaSequence): Uses `segment` which is noncomputable
- `chooseFLTS` / `chooseOmegaExecution` (LTS): Classical.choose on total LTS witnesses
- `goodSelection_seq` (Ramsey theory): Classical.choose on infinite graph coloring
- `histTrans` / `interNA` (Buchi intersection): Classical decidability for acceptance conditions
- `propositions` (HML): `Fintype.elems.toList.map` with noncomputable Fintype instance
- `iter_helper` (omega languages): Classical reasoning on infinite sequences
- `fresh_atoms` / `fresh_atom` (formula operations): `.choose` on infinite type existence
- `chooseEquiv` (linear logic): Extracts proof-relevant from proof-irrelevant equivalence
- `restrict_atoms` / `extract_U_type` / `extract_innermost_U_type` (separation hierarchy): Classical case analysis
- `PolyTimeComputable.id` / `.comp`: Polynomial evaluation over `Nat` is noncomputable in Mathlib
- `numProcFaulty` (FLP): Classical counting of faulty processes

## Potentially Removable Cases

After careful analysis, only a small number of cases **might** be removable:

### 1. `propositions` in `HML/Basic.lean` (line 183)

```lean
noncomputable def propositions : List (Proposition Label) :=
  finImage.elems.toList.map stateMap
```

This might be computable if the `Fintype` instance on `lts.image s mu` were made computable (via `DecidableEq` and decidable transitions). However, this depends on whether the LTS transition relation is decidable, which is an architectural question.

**Effort**: Medium. Requires adding `DecidableEq` constraints and potentially restructuring the `image` type.

### 2. `chooseEquiv` in `LinearLogic/CLL/Basic.lean` (line 273)

```lean
noncomputable def chooseEquiv (h : a = b) : a =downarrow b := <h.1, h.2>
```

This extracts proof-relevant equivalence from proof-irrelevant equivalence. The function body `<h.1, h.2>` suggests the data is already available -- the noncomputability comes from destructuring the `And` in `Prop`. If the equivalence type used `PSigma` instead of `And`, this could be computable. However, this would require changing the `Equiv` definition.

**Effort**: Low-medium. Changing `Equiv` to use `PSigma` has ripple effects.

### 3. Some `theorem_in_mcs_fc` duplicates

The pattern `theorem_in_mcs_fc` appears **34 times** across different files, always as a local abbreviation for "theorems are in maximal consistent sets." While the function itself must be noncomputable (it depends on `bimodal_closed_under_derivation` which depends on the deduction theorem), the **duplication** could be reduced. Currently each file defines its own local copy.

**Effort**: Low refactoring (consolidate into one shared definition), but no reduction in noncomputable count (the shared definition would still be noncomputable).

### 4. `Nat.segment` / `segment'`

Uses `open scoped Classical` with `Nat.count`. If the function `f` were required to be computable (via `DecidablePred`), `Nat.count` would be computable. However, the mathematical theorems proven about `segment` work with arbitrary `StrictMono f`, so adding a `DecidablePred` constraint would restrict generality.

**Effort**: Medium. Could provide a computable variant alongside the general noncomputable one.

## Patterns and Observations

### 1. Noncomputability is Concentrated in Metalogic

86.5% of all noncomputable usage is in `Logics/`, and within that, almost all is in `Metalogic/` subdirectories. This is expected: metalogic (completeness proofs, canonical models, Lindenbaum constructions) inherently requires classical reasoning.

### 2. The Theorem-Building Pipeline is the Primary Driver

The flow `InferenceSystem.DerivableIn` (Nonempty) -> `unwrap` (Classical.choice) -> `DerivationTree` construction causes a cascade of noncomputability through all derived theorems. This is a fundamental architectural decision, not a bug.

### 3. noncomputable section is Used Correctly

The 12 `noncomputable section` blocks are used in files where most or all definitions within the section are genuinely noncomputable. This is appropriate usage to avoid annotating each definition individually.

### 4. No Gratuitous Usage Found

No cases were found where `noncomputable` was added unnecessarily to definitions that could work without it. The codebase is disciplined about this -- computable definitions (like `top_and_intro`, `F_mono`, `until_implies_someFuture`) correctly omit the annotation even when neighboring definitions require it.

### 5. `Classical.propDecidable` is the Enabler, Not the Root Cause

Many files use `attribute [local instance] Classical.propDecidable` (32 files). This does not by itself force definitions to be noncomputable -- it only does so when combined with `if/then/else` in definition bodies (as opposed to proof terms). The actual noncomputability often comes from the deduction theorem's structural recursion which uses `by_cases` on formula membership.

## Recommendations

### 1. No Bulk Removal Campaign

The analysis shows that the overwhelming majority of `noncomputable` annotations are genuinely necessary. A removal campaign would be counterproductive.

### 2. Consolidate `theorem_in_mcs_fc` Duplicates

The 34 copies of `theorem_in_mcs_fc` / `theorem_in_mcs_fc'` / `theorem_in_mcs` across different files could be consolidated into a single shared definition (or at most one per logic system). This would not reduce noncomputable count but would reduce code duplication.

**Files to consolidate**:
- `Bimodal/Metalogic/Core/MaximalConsistent.lean` (canonical location)
- 20+ files with local copies

### 3. Consider Computable Specializations Where Useful

For `Nat.segment` and `HML.propositions`, consider providing both:
- A general noncomputable version (current, for theorems)
- A computable specialization with decidability constraints (for potential computation)

### 4. Document the Architectural Decision

Add a brief note in the project documentation explaining why noncomputability is pervasive in the Logics modules. This would help new contributors understand that the `noncomputable` annotations are by design, not technical debt.

### 5. Monitor New Additions

When adding new definitions, verify that `noncomputable` is truly needed by attempting to compile without it first. Lean 4 will emit an error if a definition uses noncomputable dependencies without the annotation, so false positives are not a concern -- the risk is only in using `noncomputable section` too broadly, which could mask unnecessarily noncomputable definitions within the section.

## Conclusion

The Cslib codebase's use of `noncomputable` is overwhelmingly correct and necessary. The root causes are:
1. Classical axiom usage inherent to metalogic (completeness, canonical models)
2. Proof-irrelevant to proof-relevant extraction (DerivationTree from Nonempty)
3. Mathlib types that are inherently noncomputable (Measure, PMF, Polynomial over abstract fields)

The only actionable improvement is consolidating the ~34 duplicated `theorem_in_mcs_fc` definitions, which is a code quality improvement rather than a noncomputability reduction.
