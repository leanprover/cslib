# Research Report: PR4 Temporal Metalogic Core Subdivision

- **Task**: 62 - pr4_temporal_metalogic_core
- **Started**: 2026-06-11T12:00:00Z
- **Completed**: 2026-06-11T12:45:00Z
- **Effort**: ~45 minutes
- **Dependencies**: Task 61 (PR3 temporal proof system)
- **Sources/Inputs**:
  - PR 1 subdivision pattern (tasks 125-135, 138-144)
  - PR 2 subdivision pattern (tasks 145-158, research report `specs/060_pr2_modal_metalogic/reports/02_pr2-preparation.md`)
  - Temporal/Metalogic/ source files (line counts and import analysis)
  - Cslib.lean barrel file (current Temporal imports)
- **Artifacts**:
  - `specs/062_pr4_temporal_metalogic_core/reports/01_pr4-subdivision.md` (this file)
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

## Project Context

- **Upstream Dependencies**: PR3 (task 61) provides Syntax/, Semantics/, ProofSystem/, Theorems.lean, FromPropositional.lean
- **Downstream Dependents**: PR5 (task 63, Chronicle infrastructure), PR6 (task 64, completeness theorem + dense variants)
- **Alternative Paths**: None — the dependency chain PR3 → PR4 → PR5 → PR6 is fixed by import structure

## Executive Summary

- PR4 scope covers 9 core Temporal/Metalogic/ files totaling **2,269 lines**, establishing the metatheoretic infrastructure (derivation trees, deduction theorem, MCS, soundness, completeness helpers) needed by the Chronicle construction (PR5) and final completeness theorem (PR6).
- Following the PR 1 pattern (first sub-PR ~300 LOC gateway, subsequent ~400-500 LOC), the recommended subdivision is **6 sub-PRs** ranging from 252 to 494 lines.
- The dependency DAG has two independent branches from DerivationTree: the MCS chain (DeductionTheorem → MCS → helpers) and the Soundness chain, which merge at CompletenessHelpers.
- Sub-PR 4.1 (DerivationTree + DeductionTheorem, ~309 lines) is the gateway PR, directly paralleling Modal PR 2.3.
- The Metalogic.lean barrel file (28 lines) and Completeness.lean (129 lines, imports Chronicle.TruthLemma) belong to PR6, not PR4.

## Context & Scope

### PR Numbering Context

| PR | Task | Name | Scope | Lines |
|----|------|------|-------|-------|
| PR3 | 61 | temporal proof system | Syntax/, Semantics/, ProofSystem/, Theorems, FromPropositional | ~2,129 |
| PR4 | 62 | temporal metalogic core | Core Metalogic/ (this report) | ~2,269 |
| PR5 | 63 | chronicle infrastructure | Metalogic/Chronicle/ (10 files) | ~9,246 |
| PR6 | 64 | completeness theorem | Completeness.lean, Dense*, Metalogic.lean barrel | ~1,008 |

### PR 1 Subdivision Pattern (Reference)

PR 1 (Propositional) was divided into 11 sub-PRs (tasks 125-135), with sub-PR 1.1 further expanded into 7 sub-sub-PRs (tasks 138-144):

| Sub-PR | Lines | Description |
|--------|-------|-------------|
| 1.1.1 | ~300 | Gateway: Proposition type refactor (Lukasiewicz primitives) |
| 1.1.2 | ~300 | Polymorphic axiom definitions |
| 1.1.3 | ~490 | Proof system typeclass hierarchy |
| 1.1.4 | ~430 | Propositional Hilbert instances + derivation trees |
| 1.1.5 | ~498 | Core theorems + barrel file |
| 1.1.6 | ~428-539 | Connective + combinator theorems |
| 1.1.7 | ~776 | Metalogic foundations (noted as needing splitting) |

Key pattern: **first sub-PR is ~300 LOC gateway** establishing primitives; subsequent sub-PRs are 400-500 LOC; items over 500 are flagged for splitting.

### PR 2 Subdivision Pattern (Reference)

PR 2 (Modal metalogic, task 60 expanded into tasks 145-158) used a similar pattern:

| Sub-PR | Lines | Description |
|--------|-------|-------------|
| 2.1 | ~440 | Gateway: Lukasiewicz primitive refactoring |
| 2.2 | ~280 | Proof system hierarchy + PL embedding |
| 2.3 | ~433 | Derivation trees + deduction theorem |
| 2.4 | ~476 | MCS + generic soundness framework |
| 2.5 | ~475 | Generic completeness framework |
| 2.6-2.14 | 485-759 | System-specific soundness/completeness |

Key pattern: infrastructure sub-PRs (2.1-2.5) are 280-476 LOC; system-specific sub-PRs pair related systems and sometimes exceed 500 LOC when logically indivisible.

## Findings

### Finding 1: PR4 File Manifest and Line Counts

All files in `Cslib/Logics/Temporal/Metalogic/` (excluding Chronicle/ and Dense*):

| File | Lines | Role |
|------|-------|------|
| DerivationTree.lean | 134 | Height measure, Deriv wrapper, DerivationSystem instance |
| DeductionTheorem.lean | 175 | Deduction theorem by well-founded recursion on height |
| MCS.lean | 483 | Lindenbaum's lemma, temporal MCS properties, G/H witnesses |
| PropositionalHelpers.lean | 117 | Bridge from Foundation theorems to temporal level |
| GeneralizedNecessitation.lean | 157 | Temporal K distribution, past necessitation |
| TemporalContent.lean | 220 | gContent/hContent/fContent/pContent/uContent/sContent definitions |
| WitnessSeed.lean | 252 | Witness seed definitions + consistency proofs |
| Soundness.lean | 421 | All 26 BX axiom schemata valid over serial linear orders |
| CompletenessHelpers.lean | 310 | Canonical world types, G/H truth lemma for canonical model |
| **Total** | **2,269** | |

**Excluded from PR4** (belong to later PRs):

| File | Lines | PR | Reason |
|------|-------|----|--------|
| Completeness.lean | 129 | PR6 | Imports Chronicle.TruthLemma (PR5) |
| DenseMCS.lean | 400 | PR6 | Dense variant of MCS |
| DenseSoundness.lean | 183 | PR6 | Dense variant of soundness |
| DenseCompleteness.lean | 268 | PR6 | Imports Completeness.lean |
| Metalogic.lean (barrel) | 28 | PR6 | Imports all Metalogic/ including Chronicle/ |

### Finding 2: Dependency DAG Within PR4

```
DerivationTree (134)
├── DeductionTheorem (175)
│   └── MCS (483)
│       ├── PropositionalHelpers (117)  [also imports ProofSystem.Instances, Foundation theorems]
│       │   └── GeneralizedNecessitation (157)  [also imports MCS]
│       │       └── WitnessSeed (252)  [also imports TemporalContent, PropositionalHelpers]
│       ├── TemporalContent (220)
│       │   └── WitnessSeed (252)
│       └── CompletenessHelpers (310)  [also imports Soundness]
└── Soundness (421)  [also imports Semantics.Validity, Mathlib.Order.Max]
    └── CompletenessHelpers (310)
```

Two independent branches from DerivationTree:
- **MCS chain**: DerivationTree → DeductionTheorem → MCS → {PropositionalHelpers, TemporalContent, GeneralizedNecessitation, WitnessSeed}
- **Soundness chain**: DerivationTree → Soundness

These merge at CompletenessHelpers (depends on both MCS and Soundness).

### Finding 3: Proposed Sub-PR Subdivision

**Sub-PR 4.1: Derivation infrastructure (~309 lines)** — Gateway PR

| File | Lines |
|------|-------|
| DerivationTree.lean | 134 |
| DeductionTheorem.lean | 175 |
| **Total** | **309** |

Rationale: Direct parallel to Modal PR 2.3 (derivation trees + deduction theorem, 433 lines). Establishes the height measure for well-founded recursion and proves the deduction theorem. Pure proof infrastructure with no metalogic content. Imports only PR3 files (ProofSystem.Derivation) and Foundation files (Metalogic.Consistency, ListHelpers, DeductionHelpers). ~300 LOC target met.

**Sub-PR 4.2: Soundness theorem (~421 lines)** — Independent branch

| File | Lines |
|------|-------|
| Soundness.lean | 421 |
| **Total** | **421** |

Rationale: Soundness depends only on DerivationTree (Sub-PR 4.1) and PR3's Semantics.Validity — it is completely independent of the MCS chain. Proves all 26 BX axiom schemata valid over serial linear orders. Placing it second allows parallel review with the MCS sub-PR (4.3), since both only depend on 4.1.

**Sub-PR 4.3: MCS framework (~483 lines)** — Core metatheorem infrastructure

| File | Lines |
|------|-------|
| MCS.lean | 483 |
| **Total** | **483** |

Rationale: Direct parallel to Modal PR 2.4 (MCS + generic soundness, 476 lines). Instantiates the generic MCS framework for temporal logic, proves Lindenbaum's lemma, and establishes temporal-specific MCS properties (G/H witnesses, negation lemmas). Single file, fits within 500 LOC. Depends only on DeductionTheorem (Sub-PR 4.1).

**Sub-PR 4.4: Propositional helpers + temporal content + generalized necessitation (~494 lines)** — Bridge infrastructure

| File | Lines |
|------|-------|
| PropositionalHelpers.lean | 117 |
| TemporalContent.lean | 220 |
| GeneralizedNecessitation.lean | 157 |
| **Total** | **494** |

Rationale: All three files depend on MCS (Sub-PR 4.3) and provide definitions/lemmas consumed by WitnessSeed and the Chronicle construction (PR5). PropositionalHelpers bridges Foundation theorems to temporal level. TemporalContent defines content operators (gContent, hContent, etc.). GeneralizedNecessitation provides temporal K distribution. Grouping stays under 500 LOC and respects the dependency ordering (GeneralizedNecessitation imports PropositionalHelpers).

**Sub-PR 4.5: Witness seed (~252 lines)** — Completeness infrastructure

| File | Lines |
|------|-------|
| WitnessSeed.lean | 252 |
| **Total** | **252** |

Rationale: Defines witness seeds and proves their consistency. Depends on all three files in Sub-PR 4.4 (TemporalContent, GeneralizedNecessitation, PropositionalHelpers). Consumed directly by Chronicle/Frame.lean and Chronicle/OrderedSeedConsistency.lean in PR5. Smaller than typical sub-PRs but logically distinct — witness seeds are the key abstraction bridging MCS theory to the chronicle construction.

**Sub-PR 4.6: Completeness helpers (~310 lines)** — Canonical model preparation

| File | Lines |
|------|-------|
| CompletenessHelpers.lean | 310 |
| **Total** | **310** |

Rationale: This is where the MCS chain and Soundness chain merge — CompletenessHelpers imports both MCS (Sub-PR 4.3) and Soundness (Sub-PR 4.2). Defines CanonicalWorld and canonicalAcc types, proves G/H-transitivity in MCS, and establishes the G/H truth lemma for the canonical model. Required by both Completeness.lean (PR6) and Chronicle files (PR5). Placing it last in PR4 ensures all prerequisites are available.

### Finding 4: Sub-PR Dependency Structure

```
4.1 (DerivTree + DedThm, 309)
├── 4.2 (Soundness, 421)
│   └── 4.6 (CompletenessHelpers, 310)  ← merges both chains
└── 4.3 (MCS, 483)
    ├── 4.4 (PropHelpers + Content + GenNec, 494)
    │   └── 4.5 (WitnessSeed, 252)
    └── 4.6 (CompletenessHelpers, 310)  ← merges both chains
```

**Dependency waves**:

| Wave | Sub-PRs | Blocked by |
|------|---------|------------|
| 1 | 4.1 | PR3 (task 61) |
| 2 | 4.2, 4.3 | 4.1 |
| 3 | 4.4 | 4.3 |
| 4 | 4.5, 4.6 | 4.4 (for 4.5), 4.2+4.3 (for 4.6) |

**Linear submission order**: 4.1 → 4.2 → 4.3 → 4.4 → 4.5 → 4.6

This order is valid because at each step all dependencies are satisfied by prior sub-PRs. Sub-PRs 4.2 and 4.3 could theoretically be submitted in parallel (both only depend on 4.1), but linear ordering simplifies review.

### Finding 5: Cslib.lean Import Management

Each sub-PR should add its files to Cslib.lean incrementally. The current Cslib.lean lists all Temporal/Metalogic imports individually (not via the barrel file). Sub-PR imports to add:

| Sub-PR | Cslib.lean imports to add |
|--------|---------------------------|
| 4.1 | `Cslib.Logics.Temporal.Metalogic.DerivationTree`, `...DeductionTheorem` |
| 4.2 | `Cslib.Logics.Temporal.Metalogic.Soundness` |
| 4.3 | `Cslib.Logics.Temporal.Metalogic.MCS` |
| 4.4 | `...PropositionalHelpers`, `...TemporalContent`, `...GeneralizedNecessitation` |
| 4.5 | `...WitnessSeed` |
| 4.6 | `...CompletenessHelpers` |

The Metalogic.lean barrel file should NOT be added until PR6 (it imports Chronicle/ files).

### Finding 6: Branch Strategy

Following the PR 2 pattern, the branch strategy should be:

1. Create `pr4/temporal-metalogic-core` from the HEAD of the PR3 branch (once PR3 exists)
2. Each sub-PR branch (`pr4.1/derivation-infrastructure`, etc.) should be based on the previous sub-PR branch
3. Files can be checked out from `main` since all code already exists and is sorry-free
4. Each sub-PR targets the previous sub-PR's branch (4.2 targets 4.1, etc.)

## Decisions

- PR4 scope is the 9 core Metalogic/ files (2,269 lines), excluding Chronicle/, Dense*, Completeness.lean, and the barrel file
- 6 sub-PRs following the PR 1 gateway pattern (~300 LOC first, ~250-494 LOC subsequent)
- Soundness placed as Sub-PR 4.2 (before MCS) to enable parallel review with the MCS chain
- Three small files (PropositionalHelpers + TemporalContent + GeneralizedNecessitation) grouped into one sub-PR to stay near 500 LOC
- WitnessSeed kept as a standalone sub-PR despite being only 252 lines, because it is the key abstraction bridging MCS theory to chronicle construction

## Recommendations

1. **Expand task 62 into 6 sub-tasks** (tasks for sub-PRs 4.1 through 4.6) with the file assignments and line counts documented above
2. **Keep the linear dependency chain** (4.1 → 4.2 → 4.3 → 4.4 → 4.5 → 4.6) for simplicity, even though 4.2 and 4.3 could be parallel
3. **Start sub-PR 4.1 implementation first** as it is the smallest (309 lines) and establishes the foundation for everything else
4. **Consider merging 4.5 (252) and 4.6 (310) into a single sub-PR** (~562 lines) if the reviewer prefers fewer, slightly larger sub-PRs — they have no mutual dependency but share the same wave in the DAG
5. **Verify PR3 (task 61) scope first** — PR4's subdivision assumes PR3 provides all Syntax/, Semantics/, ProofSystem/, Theorems.lean, and FromPropositional.lean

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR3 scope differs from assumed | H | M | Verify PR3 file manifest before creating sub-tasks |
| MCS.lean (483 lines) hard to review as single file | M | L | It's a single logical unit; splitting would break coherence |
| CompletenessHelpers (4.6) blocks PR5 start | H | L | Submit 4.6 early; PR5 Chronicle files also need WitnessSeed (4.5) |
| Soundness imports Mathlib.Order.Max not available on PR branch | M | L | Verify Mathlib dependency is in lakefile before branching |

## Appendix

### Line Count Summary

| Sub-PR | Files | Lines | Target |
|--------|-------|-------|--------|
| 4.1 | 2 | 309 | ~300 |
| 4.2 | 1 | 421 | ~500 |
| 4.3 | 1 | 483 | ~500 |
| 4.4 | 3 | 494 | ~500 |
| 4.5 | 1 | 252 | ~500 |
| 4.6 | 1 | 310 | ~500 |
| **Total** | **9** | **2,269** | |

### Comparison with PR 1 and PR 2 Patterns

| Metric | PR 1 (1.1.x) | PR 2 (2.x) | PR 4 (proposed) |
|--------|---------------|-------------|------------------|
| Total lines | ~3,222 | ~6,772 | ~2,269 |
| Sub-PRs | 7 | 14 | 6 |
| Gateway LOC | ~300 | ~440 | ~309 |
| Avg LOC | ~460 | ~484 | ~378 |
| Max LOC | ~776 | ~759 | ~494 |
| Min LOC | ~300 | ~280 | ~252 |
