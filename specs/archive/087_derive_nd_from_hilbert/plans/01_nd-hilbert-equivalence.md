# Implementation Plan: ND-Hilbert Extensional Equivalence

- **Task**: 87 - Derive natural deduction from Hilbert system or prove extensional equivalence
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/087_derive_nd_from_hilbert/reports/01_nd-hilbert-equivalence.md
- **Artifacts**: plans/01_nd-hilbert-equivalence.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

This plan bridges the two unconnected propositional proof systems in the codebase: the Hilbert-style `DerivationTree` (List-based contexts, baked-in axiom schemata) and the standalone natural deduction `Theory.Derivation` (Finset-based contexts, parameterized Theory). The approach defines `HilbertAxiomTheory` as the ND theory matching the Hilbert axiom schemata, then proves direct syntactic translations in both directions, culminating in an extensional equivalence theorem for closed derivability.

### Research Integration

The research report (01_nd-hilbert-equivalence.md) identified the key structural mismatches (List vs Finset contexts, baked-in vs parameterized axioms, primitive vs derived weakening/impI) and recommended the extensional equivalence approach as cleanest. The `impI` case of ND-to-Hilbert translation is the hardest part, requiring the existing `deductionTheorem` plus context membership bridges between `Finset.insert` and `List.cons`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define `HilbertAxiomTheory : Theory Atom` as the set of all Hilbert axiom instances
- Prove `hilbertToND`: translate `DerivationTree Gamma phi` to `HilbertAxiomTheory.Derivation Gamma.toFinset phi`
- Prove `ndToHilbert`: translate `HilbertAxiomTheory.Derivation Gamma phi` to `DerivationTree Gamma.toList phi`
- Prove top-level `hilbert_iff_nd : Derivable phi <-> DerivableIn HilbertAxiomTheory (empty turnstile phi)`

**Non-Goals**:
- Contextual equivalence for non-empty contexts (secondary goal, deferred)
- Connecting to the existing `FromHilbert.lean` wrappers (orthogonal)
- Proving completeness or soundness for either system
- Modifying existing files (pure additive work)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Finset.insert vs List.cons membership bridge difficult | M | M | Mathlib has `Finset.mem_toList` and `List.mem_toFinset`; test with `lean_multi_attempt` first |
| `deductionTheorem` API mismatch with needed form | H | L | Already verified signature: takes `A :: Gamma` context and produces `Gamma turnstile A imp B` |
| Universe polymorphism issues between the two systems | M | L | Both ultimately in universe `u`; ND has explicit `Type u`, Hilbert uses `Type*` |
| `noncomputable` propagation from deduction theorem | L | H | Expected and acceptable: the goal is logical equivalence, not computation |
| `DecidableEq Atom` requirement mismatch | M | L | ND requires it (Finset operations); Hilbert does not; equivalence file will add the constraint |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Theory Definition and Context Membership Lemmas [COMPLETED]

**Goal**: Create the equivalence file with imports, define `HilbertAxiomTheory`, and prove context conversion lemmas needed by both directions.

**Tasks**:
- [x] **Task 1.1**: Create file `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` with imports from `NaturalDeduction.Basic` and `Metalogic.DeductionTheorem` *(deviation: altered -- also imports FromHilbert for the botE combinator)*
- [x] **Task 1.2**: Define `HilbertAxiomTheory : Theory Atom := { phi | PropositionalAxiom phi }`
- [x] **Task 1.3**: Prove `mem_hilbertAxiomTheory` as an iff (combines both directions) *(deviation: altered -- single iff lemma instead of two separate lemmas)*
- [x] **Task 1.4**: (merged into Task 1.3)
- [x] **Task 1.5**: Prove `finset_insert_toList_mem_cons` (membership bridge for `impI` case)
- [x] **Task 1.6**: Prove `list_cons_mem_finset_insert_toList` (reverse bridge)
- [x] **Task 1.7**: Verify phase compiles with `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence`

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - new file

**Verification**:
- File compiles with no errors or sorries
- `HilbertAxiomTheory` defined and membership lemmas proven
- Context bridge lemmas compile

---

### Phase 2: Hilbert to ND Translation [COMPLETED]

**Goal**: Prove `hilbertToND` by structural induction on `DerivationTree`, translating each constructor to its ND counterpart.

**Tasks**:
- [x] **Task 2.1**: Define `hilbertToND` with explicit type annotations for `@Theory.Derivation`
- [x] **Task 2.2**: Handle `ax` case via `mem_hilbertAxiomTheory.mpr`
- [x] **Task 2.3**: Handle `assumption` case via `List.mem_toFinset.mpr`
- [x] **Task 2.4**: Handle `modus_ponens` case via `Theory.Derivation.impE`
- [x] **Task 2.5**: Handle `weakening` case via `Theory.Derivation.weakCtx`
- [x] **Task 2.6**: Prove `hilbert_to_nd_deriv` (Prop-level wrapper)
- [x] **Task 2.7**: Verify phase compiles

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - additions

**Verification**:
- `hilbertToND` compiles without sorry
- All four constructor cases handled
- Prop-level wrapper compiles

---

### Phase 3: ND to Hilbert Translation [COMPLETED]

**Goal**: Prove `ndToHilbert` by structural induction on `Theory.Derivation`, translating each constructor to its Hilbert counterpart. This is the harder direction due to the `impI` case requiring the deduction theorem.

**Tasks**:
- [x] **Task 3.1**: Define `ndToHilbert` (noncomputable) with explicit `@Theory.Derivation` type
- [x] **Task 3.2**: Handle `ax` case via `mem_hilbertAxiomTheory.mp`
- [x] **Task 3.3**: Handle `ass` case via `Finset.mem_toList.mpr`
- [x] **Task 3.4**: Handle `impE` case via `DerivationTree.modus_ponens`
- [x] **Task 3.5**: Handle `botE` case via `PL.botE` from FromHilbert *(deviation: altered -- used existing botE combinator from FromHilbert.lean instead of inlining EFQ axiom + modus ponens)*
- [x] **Task 3.6**: Handle `impI` case: recursive call + weakening via bridge lemma + deductionTheorem
- [x] **Task 3.7**: Prove `nd_to_hilbert_deriv` (Prop-level wrapper)
- [x] **Task 3.8**: Verify phase compiles

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - additions

**Verification**:
- `ndToHilbert` compiles without sorry
- All five constructor cases handled, especially `impI`
- `noncomputable` annotation present (inherited from `deductionTheorem`)
- Prop-level wrapper compiles

---

### Phase 4: Top-Level Equivalence Theorem [COMPLETED]

**Goal**: Combine the two translations to prove the top-level extensional equivalence for closed derivability, handling the empty-context edge case.

**Tasks**:
- [x] **Task 4.1**: Forward direction uses `List.toFinset_nil` rewrite
- [x] **Task 4.2**: Backward direction uses membership-based weakening instead of `Finset.toList_empty` *(deviation: altered -- Finset.toList is noncomputable so toList = [] is not definitionally true; used weakening with vacuous membership proof instead)*
- [x] **Task 4.3**: Prove `hilbert_iff_nd`
- [x] **Task 4.4**: Add module docstring documenting the equivalence
- [x] **Task 4.5**: Final build verification with `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence`

**Timing**: 30 minutes

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - additions

**Verification**:
- `hilbert_iff_nd` compiles without sorry
- Full file compiles clean
- `lean_verify` confirms no sorry or axiom usage beyond standard Lean axioms and `Classical.propDecidable`

## Testing & Validation

- [x] `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` succeeds
- [x] `lean_verify` on `hilbertToND`, `ndToHilbert`, `hilbert_iff_nd` shows no sorry
- [x] `lake build` full project succeeds (no regressions)
- [x] No modifications to existing files required

## Artifacts & Outputs

- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - new file with the equivalence proof
- `specs/087_derive_nd_from_hilbert/plans/01_nd-hilbert-equivalence.md` - this plan
- `specs/087_derive_nd_from_hilbert/summaries/01_nd-hilbert-equivalence-summary.md` - implementation summary (post-implementation)

## Rollback/Contingency

Since this is purely additive (single new file, no modifications to existing files), rollback is trivial: delete `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`. If the `impI` case proves harder than expected, the Hilbert-to-ND direction can be delivered as a standalone partial result (it is independently useful).
