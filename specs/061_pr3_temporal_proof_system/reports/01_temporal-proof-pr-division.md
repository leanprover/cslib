# Research Report: Task #61

**Task**: 61 - pr3_temporal_proof_system
**Date**: 2026-06-11
**Session**: sess_1781244674_55e8cd
**Focus**: Divide the temporal proof system PR into sub-PRs following the PR1/PR2 decomposition pattern

## Executive Summary

- PR3 covers 14 files totaling **2,129 lines** across four subdirectories (Syntax/, Semantics/, ProofSystem/) plus Theorems.lean and FromPropositional.lean. This is the **first PR to touch any Temporal/** files on upstream.
- Following the established PR1/PR2 pattern (first sub-PR ~300 LOC gateway, subsequent ~400-500 LOC), the recommended subdivision is **5 sub-PRs** ranging from 250 to 549 lines.
- All PR3 files depend on PR1 Foundation files (Connectives.lean, ProofSystem.lean, TemporalDerived.lean, FrameConditions.lean) that are already on the `pr1/foundations-logic` branch. PR3 cannot be submitted until the relevant PR1 sub-PRs merge.
- The dependency DAG is clean: Syntax is the root, Semantics and ProofSystem branch independently from Syntax, and they merge at Theorems.lean/FromPropositional.lean.
- No modifications to existing upstream files are needed -- all PR3 content is new files.

## Context & Scope

### PR Numbering and Relationship

| PR | Task | Name | Scope | Lines | Status |
|----|------|------|-------|-------|--------|
| PR1 | 124 | foundations_logic | Propositional proof system, Foundation refactoring | ~3,729 | Expanded into 11 sub-PRs (125-135), sub-PR 1.1 further into 7 (138-144) |
| PR2 | 60 | modal_metalogic | Modal soundness/completeness for 15 cube systems | ~6,772 | Expanded into 14 sub-PRs (145-158) |
| **PR3** | **61** | **temporal_proof_system** | **Temporal Syntax, Semantics, ProofSystem** | **~2,129** | **This report** |
| PR4 | 62 | temporal_metalogic_core | Core Metalogic/ (9 files) | ~2,269 | Subdivided (6 sub-PRs) |
| PR5 | 63 | chronicle_infrastructure | Chronicle/ (10 files) | ~9,246 | Not started |
| PR6 | 64 | completeness_theorem | Completeness + Dense variants | ~1,008 | Not started |

### Upstream Status

Upstream (`leanprover/cslib` main) has **zero** Temporal/ files. The following are already upstream:

- `Cslib/Foundations/Data/OmegaSequence/Temporal.lean` (106 lines) -- unrelated to temporal logic proof system
- `Cslib/Logics/Propositional/Defs.lean` -- needed by FromPropositional.lean

The following PR1 Foundation files are **NOT on upstream** but ARE on `pr1/foundations-logic`:

| File | Lines | Needed by |
|------|-------|-----------|
| `Foundations/Logic/Connectives.lean` | 98 | Formula.lean (all Temporal files transitively) |
| `Foundations/Logic/ProofSystem.lean` | ~486 | Instances.lean |
| `Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` | 292 | Theorems.lean |
| `Foundations/Logic/Theorems/Temporal/FrameConditions.lean` | 89 | Theorems.lean |
| `Foundations/Logic/Theorems/Propositional/Core.lean` | ~289 | TemporalDerived.lean (transitive) |
| `Foundations/Logic/Theorems/Propositional/Connectives.lean` | ~536 | TemporalDerived.lean (transitive) |

**PR3 cannot be submitted until the PR1 sub-PRs providing these Foundation files are merged.** Specifically:
- Sub-PR 1.1.1 (Connectives.lean) must merge for any PR3 sub-PR
- Sub-PR 1.1.3 (ProofSystem.lean hierarchy) must merge for sub-PR 3.3 (Instances)
- Sub-PR 1.1.5 or 1.1.6 (Propositional theorems) must merge for sub-PR 3.5 (Theorems)

### PR1 Decomposition Pattern (Reference)

PR1 was divided into 11 sub-PRs, with sub-PR 1.1 further expanded into 7:

| Pattern Element | PR1 Approach |
|----------------|--------------|
| Gateway sub-PR | ~300 LOC, pure refactoring/foundations |
| Subsequent sub-PRs | 400-500 LOC each |
| Over 500 LOC | Justified as logically indivisible units |
| Dependency order | Modifications-first, then new files in DAG order |
| Wave plan | 4 dependency waves |

### PR2 Decomposition Pattern (Reference)

PR2 was divided into 14 sub-PRs:

| Pattern Element | PR2 Approach |
|----------------|--------------|
| Gateway sub-PR | ~440 LOC (Lukasiewicz primitive refactoring) |
| Infrastructure sub-PRs | 280-476 LOC (2.1-2.5) |
| System-specific sub-PRs | 485-759 LOC (2.6-2.14, pairing related systems) |
| Dependency order | Linear chain for infrastructure, then parallel system pairs |

## Findings

### Finding 1: PR3 Complete File Manifest

All 14 files are **new** (none exist on upstream):

| File | Lines | Category | Imports Within PR3 |
|------|-------|----------|-------------------|
| **Syntax/** | | | |
| `Formula.lean` | 549 | Syntax | (root -- imports Connectives from PR1) |
| `Context.lean` | 131 | Syntax | Formula |
| `BigConj.lean` | 52 | Syntax | Formula |
| `Subformulas.lean` | 218 | Syntax | Formula |
| **Semantics/** | | | |
| `Model.lean` | 60 | Semantics | Formula |
| `Satisfies.lean` | 177 | Semantics | Model |
| `Validity.lean` | 198 | Semantics | Satisfies, Context |
| **ProofSystem/** | | | |
| `Axioms.lean` | 235 | ProofSystem | Formula |
| `Derivation.lean` | 98 | ProofSystem | Axioms, Context |
| `Derivable.lean` | 99 | ProofSystem | Derivation |
| `Instances.lean` | 214 | ProofSystem | Derivable, (Foundation ProofSystem from PR1) |
| `ProofSystem.lean` | 23 | Barrel | Axioms, Derivation, Derivable, Instances |
| **Top-level** | | | |
| `Theorems.lean` | 19 | Barrel | (Foundation TemporalDerived + FrameConditions from PR1) |
| `FromPropositional.lean` | 56 | Embedding | Formula, (PL.Defs from upstream) |
| **Total** | **2,129** | | |

### Finding 2: Internal Dependency DAG

```
Formula (549)  ← ROOT (imports Connectives from PR1)
├── Context (131)
│   ├── Validity (198) ← also imports Satisfies
│   └── Derivation (98) ← also imports Axioms
├── BigConj (52)
├── Subformulas (218)
├── Model (60)
│   └── Satisfies (177)
│       └── Validity (198)
├── Axioms (235)
│   └── Derivation (98) ← also imports Context
│       └── Derivable (99)
│           └── Instances (214) ← also imports Foundation ProofSystem (PR1)
└── FromPropositional (56) ← also imports PL.Defs (upstream)

ProofSystem.lean (23) ← barrel importing Axioms, Derivation, Derivable, Instances
Theorems.lean (19)    ← barrel importing TemporalDerived + FrameConditions (PR1)
```

Two independent branches from Formula:
- **Semantics branch**: Formula -> Model -> Satisfies -> Validity (also needs Context)
- **ProofSystem branch**: Formula -> Axioms -> Derivation -> Derivable -> Instances

These branches do NOT cross-import within PR3 scope. They merge only at the Metalogic level (PR4), where Soundness imports both Validity and Derivation.

### Finding 3: Proposed Sub-PR Subdivision

**Sub-PR 3.1: Temporal formula and syntax foundations (~300 LOC)** -- Gateway PR

| File | Lines |
|------|-------|
| `Syntax/Formula.lean` | 549 |
| **Total** | **549** |

**Wait** -- Formula.lean alone is 549 lines, which exceeds the ~300 LOC target. However, this is the foundational type definition that EVERY other file depends on. It defines the `Formula` inductive, all derived connectives (neg, top, or, and, iff, allFuture, someFuture, allPast, somePast, swapTemporal), DecidableEq, BEq, Encodable/Denumerable instances, and Connective typeclass instances (HasBot, HasImp, HasUntil, HasSince, TemporalConnectives). Splitting it would be semantically meaningless.

**Revised approach**: Make the gateway PR the Syntax directory minus Formula.lean, since Formula.lean is an indivisible unit.

Actually, looking more carefully at Formula.lean's 549 lines, it contains:
- The inductive type definition (~15 lines)
- 15+ derived connectives as `abbrev` (~30 lines)
- swapTemporal recursive function + involution proof (~50 lines)
- Encodable/Denumerable instances (~80 lines)
- Connective typeclass instances (~50 lines)
- Helper lemmas and simp lemmas (~300+ lines)

Formula.lean at 549 lines is comparable to PR1's sub-PR 1.8 (HilbertDerivedRules, 559 lines) which was accepted as logically indivisible. Let me reconsider the division.

**Revised Sub-PR 3.1: Temporal syntax (~350 LOC)** -- Gateway PR

Since Formula.lean (549) is too large for a gateway, we split the syntax into two sub-PRs:

| File | Lines | Notes |
|------|-------|-------|
| `Syntax/Formula.lean` (core portion) | ~250 | Type definition, derived connectives, swapTemporal |
| `Syntax/Context.lean` | 131 | Context = List (Formula Atom) |
| **Estimated diff** | **~300-350** | |

But wait -- Formula.lean is a single file. Splitting it into two files would mean creating a new file (e.g., `Formula/Basic.lean` and `Formula/Instances.lean`), which would be a refactoring not present in the current codebase.

**Final revised approach**: Accept that Formula.lean is an indivisible unit and make it the gateway PR as-is.

---

**Sub-PR 3.1: Temporal formula type (~549 LOC)** -- Gateway PR

| File | Lines |
|------|-------|
| `Syntax/Formula.lean` | 549 |
| **Total** | **549** |

Rationale: Formula.lean defines the core `Formula` inductive type, all derived connectives, the `swapTemporal` function with its involution proof, Encodable/Denumerable instances, and all connective typeclass registrations. Every other temporal file imports it. While 549 lines exceeds the typical ~300 LOC gateway target, the file is an indivisible semantic unit -- the Formula type plus its API. This parallels PR1's acceptance of sub-PR 1.8 (559 lines) as indivisible. The file contains no proofs that could be deferred; all content is definitional.

Note: If the reviewer requires a split, the file could be divided into `Formula/Basic.lean` (type + derived connectives, ~200 lines) and `Formula/Instances.lean` (Encodable, Denumerable, connective typeclasses, simp lemmas, ~350 lines). This is a contingency, not the primary recommendation.

External dependencies: `Cslib.Foundations.Logic.Connectives` (from PR1 sub-PR 1.1.1), Mathlib (Encodable, Denumerable, Finset).

Suggested branch: `temporal/formula-type`

---

**Sub-PR 3.2: Temporal syntax utilities (~401 LOC)**

| File | Lines |
|------|-------|
| `Syntax/Context.lean` | 131 |
| `Syntax/BigConj.lean` | 52 |
| `Syntax/Subformulas.lean` | 218 |
| **Total** | **401** |

Rationale: These three files all depend only on Formula.lean (Sub-PR 3.1) and provide syntactic utilities: Context (assumption lists), BigConj (conjunction over lists), and Subformulas (subformula closure). They are consumed by both the Semantics and ProofSystem branches. Grouping them keeps the sub-PR under 500 LOC and creates a clean "syntax complete" checkpoint.

Suggested branch: `temporal/syntax-utilities`

---

**Sub-PR 3.3: Temporal proof system (~669 LOC)**

| File | Lines |
|------|-------|
| `ProofSystem/Axioms.lean` | 235 |
| `ProofSystem/Derivation.lean` | 98 |
| `ProofSystem/Derivable.lean` | 99 |
| `ProofSystem/Instances.lean` | 214 |
| `ProofSystem.lean` (barrel) | 23 |
| **Total** | **669** |

This grouping exceeds 500 LOC. However, the alternative of splitting it has a dependency constraint: Instances.lean depends on Derivable which depends on Derivation which depends on Axioms. The only viable split would be:
- 3.3a: Axioms + Derivation + Derivable (432 lines)
- 3.3b: Instances + barrel (237 lines)

**Recommended split**:

**Sub-PR 3.3: Temporal axioms and derivation (~432 LOC)**

| File | Lines |
|------|-------|
| `ProofSystem/Axioms.lean` | 235 |
| `ProofSystem/Derivation.lean` | 98 |
| `ProofSystem/Derivable.lean` | 99 |
| **Total** | **432** |

Rationale: Defines the 26 BX axiom constructors (with FrameClass classification), the Type-valued DerivationTree with 6 inference rules, and the Prop-valued Derivable wrapper. These three files form the syntactic proof system core. Depends on Formula (3.1) and Context (3.2).

External dependencies: None beyond PR3 predecessors.

Suggested branch: `temporal/axioms-derivation`

---

**Sub-PR 3.4: Temporal proof system instances + barrel (~237 LOC)**

| File | Lines |
|------|-------|
| `ProofSystem/Instances.lean` | 214 |
| `ProofSystem.lean` (barrel) | 23 |
| **Total** | **237** |

Rationale: Registers InferenceSystem, ModusPonens, ClassicalHilbert, TemporalNecessitation, all 22 HasAxiom* instances, and the bundled TemporalBXHilbert instance for the `HilbertBX` tag type. This bridges the abstract typeclass hierarchy (from Foundation/ProofSystem.lean, PR1) to the concrete derivation tree. The barrel file re-exports all ProofSystem modules.

External dependencies: `Cslib.Foundations.Logic.ProofSystem` (from PR1).

Suggested branch: `temporal/proof-system-instances`

---

**Sub-PR 3.5: Temporal semantics + embedding + theorems (~510 LOC)**

| File | Lines |
|------|-------|
| `Semantics/Model.lean` | 60 |
| `Semantics/Satisfies.lean` | 177 |
| `Semantics/Validity.lean` | 198 |
| `FromPropositional.lean` | 56 |
| `Theorems.lean` (barrel) | 19 |
| **Total** | **510** |

Rationale: These five files form the semantic side of temporal logic. Model defines `TemporalModel` on linear orders. Satisfies defines the recursive satisfaction relation. Validity defines the validity hierarchy (Valid, ValidSerial, ValidDense, ValidDiscrete). FromPropositional provides the structural embedding from propositional to temporal logic. Theorems.lean is a barrel re-exporting the Foundation-level temporal derived theorems.

The semantics chain (Model -> Satisfies -> Validity) is independent of the ProofSystem chain within PR3. Grouping them with FromPropositional and Theorems.lean keeps everything at ~510 LOC, slightly above the 500 target but logically cohesive.

Alternative: Split into 3.5a (Semantics, 435 lines) and 3.5b (FromPropositional + Theorems, 75 lines). However, the 75-line sub-PR would be too small to justify its own review cycle.

External dependencies:
- `Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived` (from PR1, for Theorems.lean)
- `Cslib.Foundations.Logic.Theorems.Temporal.FrameConditions` (from PR1, for Theorems.lean)
- `Cslib.Logics.Propositional.Defs` (upstream, for FromPropositional.lean)
- Mathlib: `Order.SuccPred.Basic`, `Order.SuccPred.Archimedean` (for Validity.lean)

Suggested branch: `temporal/semantics-embedding`

---

### Finding 4: Sub-PR Dependency Structure

```
3.1 (Formula, 549)
├── 3.2 (Context + BigConj + Subformulas, 401)
│   ├── 3.3 (Axioms + Derivation + Derivable, 432)
│   │   └── 3.4 (Instances + barrel, 237)
│   └── 3.5 (Semantics + FromProp + Theorems, 510)
└── 3.5 also depends on 3.1 directly (Model imports Formula)
```

**Dependency waves**:

| Wave | Sub-PRs | Blocked by |
|------|---------|------------|
| 1 | 3.1 | PR1 sub-PR 1.1.1 (Connectives.lean) |
| 2 | 3.2 | 3.1 |
| 3 | 3.3, 3.5 | 3.2 (can be parallel) |
| 4 | 3.4 | 3.3 (also needs PR1 sub-PR 1.1.3 for Foundation ProofSystem) |

**Linear submission order**: 3.1 -> 3.2 -> 3.3 -> 3.4 -> 3.5

Note: Sub-PRs 3.3 and 3.5 could theoretically be submitted in parallel (both depend only on 3.2, with no mutual dependency), but linear ordering simplifies review. Sub-PR 3.5 is placed last because its Theorems.lean barrel depends on the most PR1 sub-PRs (the Propositional theorem files must be merged first).

### Finding 5: Cslib.lean Import Management

Each sub-PR should add its files to Cslib.lean incrementally:

| Sub-PR | Cslib.lean imports to add |
|--------|---------------------------|
| 3.1 | `Cslib.Logics.Temporal.Syntax.Formula` |
| 3.2 | `...Syntax.Context`, `...Syntax.BigConj`, `...Syntax.Subformulas` |
| 3.3 | `...ProofSystem.Axioms`, `...ProofSystem.Derivation`, `...ProofSystem.Derivable` |
| 3.4 | `...ProofSystem.Instances`, `...ProofSystem` |
| 3.5 | `...Semantics.Model`, `...Semantics.Satisfies`, `...Semantics.Validity`, `...FromPropositional`, `...Theorems` |

### Finding 6: Branch Strategy

Following the established pattern:

1. Each sub-PR branches from the HEAD of the previous sub-PR's branch (or from main after preceding PR1 sub-PRs merge).
2. Files can be checked out from `main` since all temporal code already exists and is sorry-free.
3. Each sub-PR targets the previous sub-PR's branch for review, then rebases to main when predecessors merge.

**Practical approach**: Since all files already exist on `main` (the local fork), each sub-PR branch can `git checkout main -- <files>` to extract the needed files, then update Cslib.lean.

### Finding 7: Comparison with PR1 and PR2 Patterns

| Metric | PR1 (1.1.x) | PR2 (2.x) | PR3 (proposed) | PR4 (existing) |
|--------|-------------|-----------|----------------|----------------|
| Total lines | ~3,222 | ~6,772 | **~2,129** | ~2,269 |
| Sub-PRs | 7 | 14 | **5** | 6 |
| Gateway LOC | ~300 | ~440 | **~549** | ~309 |
| Avg LOC | ~460 | ~484 | **~426** | ~378 |
| Max LOC | ~776 | ~759 | **~549** | ~494 |
| Min LOC | ~300 | ~280 | **~237** | ~252 |

The PR3 gateway is larger than PR1/PR2 gateways because `Formula.lean` (549 lines) is an indivisible semantic unit (the core type definition). PR1's gateway was a refactoring of existing files; PR2's was a primitive convention change. PR3's gateway creates the fundamental type from scratch, which inherently requires more content.

## Decisions

- **5 sub-PRs** is the recommended count. Fewer would exceed 500 LOC limits; more would create unnecessarily small PRs (e.g., a 52-line BigConj PR).
- **Formula.lean as gateway** despite 549 lines. It is the root dependency for all temporal files and cannot be meaningfully split without creating artificial file boundaries.
- **ProofSystem split into two sub-PRs** (3.3 and 3.4) to keep each under 500 LOC and to isolate the Foundation ProofSystem dependency (only needed by Instances.lean).
- **Semantics grouped with FromPropositional and Theorems** since these are all leaf nodes with no downstream dependents within PR3.
- **Foundation files NOT included in PR3 scope** -- TemporalDerived.lean and FrameConditions.lean are on the PR1 branch and will be merged via PR1 sub-PRs.

## Proposed Task Descriptions

### Task: subpr_3_1_temporal_formula

**Title**: Sub-PR 3.1: Temporal formula type

**Description**: Sub-PR 3.1: Temporal formula type. Introduces Syntax/Formula.lean (549 lines) defining the temporal logic Formula inductive with primitives {atom, bot, imp, untl, snce}, all derived connectives (neg, top, or, and, iff, allFuture/G, someFuture/F, allPast/H, somePast/P), the swapTemporal involution, Encodable/Denumerable instances, and connective typeclass registrations (HasBot, HasImp, HasUntil, HasSince, TemporalConnectives). Gateway PR for all temporal logic. ~549 diff lines.

**Dependencies**: PR1 sub-PR 1.1.1 (Connectives.lean must be on upstream)

### Task: subpr_3_2_syntax_utilities

**Title**: Sub-PR 3.2: Temporal syntax utilities

**Description**: Sub-PR 3.2: Temporal syntax utilities. Adds Context.lean (131 lines, Context = List (Formula Atom) with map/membership lemmas), BigConj.lean (52 lines, big conjunction over formula lists), and Subformulas.lean (218 lines, subformula closure with membership and transitivity lemmas). ~401 diff lines.

**Dependencies**: Sub-PR 3.1

### Task: subpr_3_3_axioms_derivation

**Title**: Sub-PR 3.3: Temporal axioms and derivation trees

**Description**: Sub-PR 3.3: Temporal axioms and derivation trees. Adds Axioms.lean (235 lines, 26 BX axiom constructors with FrameClass classification: Base/Dense/Discrete), Derivation.lean (98 lines, Type-valued DerivationTree with 6 inference rules: axiom, assumption, modus_ponens, temporal_necessitation, temporal_duality, weakening), and Derivable.lean (99 lines, Prop-valued Nonempty wrapper with constructor-mirroring lemmas). ~432 diff lines.

**Dependencies**: Sub-PR 3.2

### Task: subpr_3_4_proof_system_instances

**Title**: Sub-PR 3.4: Temporal proof system instances

**Description**: Sub-PR 3.4: Temporal proof system instances. Adds Instances.lean (214 lines, registers InferenceSystem, ModusPonens, ClassicalHilbert, TemporalNecessitation, 22 HasAxiom* instances, and TemporalBXHilbert for HilbertBX tag type) and ProofSystem.lean barrel (23 lines). Bridges abstract Foundation typeclass hierarchy to concrete derivation tree. ~237 diff lines.

**Dependencies**: Sub-PR 3.3, PR1 sub-PR providing Foundation/Logic/ProofSystem.lean

### Task: subpr_3_5_semantics_embedding

**Title**: Sub-PR 3.5: Temporal semantics and PL embedding

**Description**: Sub-PR 3.5: Temporal semantics and PL embedding. Adds Model.lean (60 lines, TemporalModel structure on LinearOrder), Satisfies.lean (177 lines, recursive satisfaction relation with Burgess convention), Validity.lean (198 lines, validity hierarchy: Valid/ValidSerial/ValidDense/ValidDiscrete), FromPropositional.lean (56 lines, structural PL -> Temporal embedding with coercion), and Theorems.lean barrel (19 lines, re-exports Foundation temporal derived theorems). ~510 diff lines.

**Dependencies**: Sub-PR 3.2, PR1 sub-PRs providing Foundation temporal theorem files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Sub-PR 3.1 (549 LOC) exceeds 300 LOC gateway target | M | H | Justify as indivisible unit; offer contingency split (Formula/Basic + Formula/Instances) if reviewer requests |
| PR1 Foundation files not merged when PR3 is ready | H | M | Submit PR3 sub-PRs targeting the PR1 branch; rebase after PR1 merges |
| Sub-PR 3.5 (510 LOC) slightly exceeds 500 target | L | H | 10 lines over is negligible; could move Theorems.lean barrel to a separate micro-PR if needed |
| PR4 scope assumption (PR3 provides all Syntax/Semantics/ProofSystem) | M | L | This report confirms the assumption: PR3 covers exactly those files |
| Formula.lean may need modifications when Connectives.lean changes in PR1 | M | L | Verify Formula.lean builds against the PR1 version of Connectives.lean before submitting |

## Appendix

### Verification Commands for Each Sub-PR

Before submitting each sub-PR, run from a branch containing only those files:

```bash
lake build                              # must exit 0
lake test                               # must pass
lake exe checkInitImports               # must pass
lake exe lint-style                     # must pass
lake exe mk_all --module --check        # must report no update
lake shake --add-public --keep-implied --keep-prefix  # check for unused imports
grep -rn "sorry" <files>               # must return zero hits
grep -rn "#check\|#eval\|dbg_trace" <files>  # must return zero hits
```

### Complete Line Count Summary

| Sub-PR | Files | Lines | Target | Within Target? |
|--------|-------|-------|--------|----------------|
| 3.1 | 1 | 549 | ~300 | Over (indivisible unit) |
| 3.2 | 3 | 401 | ~500 | Yes |
| 3.3 | 3 | 432 | ~500 | Yes |
| 3.4 | 2 | 237 | ~500 | Yes (small but clean scope) |
| 3.5 | 5 | 510 | ~500 | Marginal (10 over) |
| **Total** | **14** | **2,129** | | |

### PR1 Dependency Map for PR3 Sub-PRs

| PR3 Sub-PR | Requires from PR1 | PR1 Sub-PR |
|------------|-------------------|------------|
| 3.1 | Connectives.lean | 1.1.1 (task 138) |
| 3.2 | (via 3.1) | 1.1.1 |
| 3.3 | (via 3.1) | 1.1.1 |
| 3.4 | Foundation/ProofSystem.lean | 1.1.3 (task 140) |
| 3.5 | TemporalDerived.lean, FrameConditions.lean | 1.1.5 or 1.1.6 (tasks 142-143) |
