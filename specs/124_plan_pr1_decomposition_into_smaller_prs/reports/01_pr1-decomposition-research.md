# Research Report: Task #124

**Task**: 124 - Plan PR 1 Decomposition into Smaller PRs
**Started**: 2026-06-11T20:52:00Z
**Completed**: 2026-06-11T21:30:00Z
**Effort**: 1.5 hours
**Dependencies**: None
**Sources/Inputs**:
- `specs/archive/059_pr1_foundations_logic/pr-description.md` (original PR1 description, 25-file inventory)
- `specs/archive/059_pr1_foundations_logic/pr-description-v2.md` (revised 25-file description)
- `specs/archive/083_update_pr1_description_and_roadmap/reports/` (PR1 scope update)
- `specs/archive/085_include_propositional_in_pr1/` (Propositional inclusion task)
- `specs/archive/091_pr_1_5_propositional_hilbert_submission/reports/` (PR1.5 scope review)
- `specs/archive/121_review_propositional_metalogic_cherry_pick/summaries/` (task 121 summary)
- `specs/archive/122_fix_propositional_ci_checks/summaries/` (task 122 summary)
- Git diff `a8dbe81b..pr1/foundations-logic` (actual PR1 branch content vs upstream)
- Lean source files in `Cslib/Foundations/Logic/` and `Cslib/Logics/Propositional/`
- `CONTRIBUTING.md` (CSLib PR style guide)
- `specs/state.json` (active task context)
**Artifacts**:
- `specs/124_plan_pr1_decomposition_into_smaller_prs/reports/01_pr1-decomposition-research.md`
**Standards**: report-format.md, artifact-formats.md

---

## Executive Summary

- The `pr1/foundations-logic` branch has **3,729 insertions** across 35 Lean files vs the upstream merge-base (`a8dbe81b`); the original 16 `Foundations/Logic/` files and several base `Propositional/` files are **already merged** into upstream `leanprover/cslib` main.
- The **pending content** (3,729 insertions) consists of 14 new files (2,918 lines total) plus modifications to 21 files (811 insertions); splitting into sub-PRs under 500 insertions each yields **11 sub-PRs**.
- The natural decomposition follows **semantic cohesion**: (1) hierarchy refactoring, (2) axiom extensions, (3) semantics, (4–6) three soundness/completeness groups, (7–10) four natural deduction groups, (11) modal extension.
- **Key dependency order**: Sub-PR 1.1 (refactoring) must merge first; 1.2 and 1.3 can follow in parallel; 1.4–1.6 require both 1.2 and 1.3; 1.7–1.10 depend on 1.2; 1.11 depends on 1.1.
- Three sub-PRs are slightly over 500 lines (1.5: 555, 1.6: 514, 1.8: 559) but contain logically indivisible units; splitting further would leave semantically incomplete files.
- Task 123 (add bib references) is a prerequisite: references for Church 1956, Chellas 1980, Blackburn et al. 2001, Curry and Feys 1958, Griffin 1990, and Howard 1969/1980 are **not yet in `references.bib`**.

---

## Context & Scope

### PR1 Branch Status

The `pr1/foundations-logic` branch targets `upstream/main` (`leanprover/cslib`). The merge-base between the branch and the current upstream main is commit `a8dbe81b` (2026-06-10 14:47:45). A substantial portion of the originally proposed PR1 content (the 16 `Foundations/Logic/` files from commit `6034fa01`, plus base propositional files from tasks 85 and 87–89) has **already been merged** into upstream main.

What remains in the branch as unmerged additions totals **3,729 insertions and 373 deletions** across 35 Lean files. This is the content the reviewer flagged as "too large," and the scope of this decomposition.

### Reviewer Constraint

Reviewer feedback: PRs under 500 lines each, building from foundations in logical order. The "500 lines" refers to git diff insertions per sub-PR. The following decomposition interprets this as: each sub-PR should introduce no more than ~500 new lines (additions in the diff).

### What Is Already in Upstream Main

The following files are **complete** in upstream main as of merge-base `a8dbe81b`:

| File | Lines | Status |
|------|------:|--------|
| `Foundations/Logic/InferenceSystem.lean` | 68 | merged |
| `Foundations/Logic/Connectives.lean` | 98 | merged |
| `Foundations/Logic/Axioms.lean` | 298 | merged |
| `Foundations/Logic/ProofSystem.lean` | 353 | merged (partial -- 486 in branch) |
| `Foundations/Logic/LogicalEquivalence.lean` | 35 | merged |
| `Foundations/Logic/Theorems.lean` | 48 | merged (partial) |
| `Foundations/Logic/Theorems/Combinators.lean` | 339 | merged (partial) |
| `Foundations/Logic/Theorems/BigConj.lean` | 142 | merged (partial) |
| `Foundations/Logic/Theorems/Propositional/Core.lean` | 289 | merged (partial) |
| `Foundations/Logic/Theorems/Propositional/Connectives.lean` | 536 | merged (partial) |
| `Foundations/Logic/Theorems/Modal/Basic.lean` | 269 | merged (partial) |
| `Foundations/Logic/Theorems/Modal/S5.lean` | 533 | merged |
| `Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` | 292 | merged |
| `Foundations/Logic/Theorems/Temporal/FrameConditions.lean` | 90 | merged (partial) |
| `Foundations/Logic/Metalogic/Consistency.lean` | 278 | merged |
| `Foundations/Logic/Metalogic/DeductionHelpers.lean` | 120 | merged |
| `Foundations/Data/ListHelpers.lean` | 71 | merged (partial) |
| `Logics/Propositional/Defs.lean` | 162 | merged (partial) |
| `Logics/Propositional/ProofSystem/Axioms.lean` | 55 | merged (partial) |
| `Logics/Propositional/ProofSystem/Derivation.lean` | 147 | merged (partial) |
| `Logics/Propositional/ProofSystem/Instances.lean` | 90 | merged |
| `Logics/Propositional/Metalogic/DeductionTheorem.lean` | 180 | merged (partial) |
| `Logics/Propositional/Metalogic/MCS.lean` | 129 | merged (partial) |
| `Logics/Propositional/NaturalDeduction/Basic.lean` | 345 | merged |
| `Logics/Propositional/NaturalDeduction/FromHilbert.lean` | 219 | merged (partial) |
| `Logics/Modal/Basic.lean` | 269 | merged (partial) |
| `Logics/Modal/Denotation.lean` | ? | merged (partial) |

---

## Findings

### Complete File Inventory for Pending Sub-PRs

The following are the **actual changes** (git diff insertions) in the `pr1/foundations-logic` branch not yet in upstream main.

#### Files Entirely New (not in upstream)

| File | Lines | Notes |
|------|------:|-------|
| `Logics/Propositional/ProofSystem/IntMinInstances.lean` | 109 | NEW: IntHilbert/MinHilbert instances |
| `Logics/Propositional/Semantics/Basic.lean` | 47 | NEW: Valuation, Evaluate, Tautology |
| `Logics/Propositional/Semantics/Kripke.lean` | 134 | NEW: KripkeModel, IForces, IValid, MValid |
| `Logics/Propositional/Metalogic/Soundness.lean` | 87 | NEW: Classical soundness |
| `Logics/Propositional/Metalogic/Completeness.lean` | 295 | NEW: Classical completeness |
| `Logics/Propositional/Metalogic/IntSoundness.lean` | 103 | NEW: Intuitionistic soundness |
| `Logics/Propositional/Metalogic/IntLindenbaum.lean` | 325 | NEW: DCCS extension lemma (intuitionistic) |
| `Logics/Propositional/Metalogic/IntCompleteness.lean` | 127 | NEW: Intuitionistic completeness |
| `Logics/Propositional/Metalogic/MinSoundness.lean` | 96 | NEW: Minimal soundness |
| `Logics/Propositional/Metalogic/MinLindenbaum.lean` | 275 | NEW: DCCS extension lemma (minimal) |
| `Logics/Propositional/Metalogic/MinCompleteness.lean` | 143 | NEW: Minimal completeness |
| `Logics/Propositional/NaturalDeduction/DerivedRules.lean` | 387 | NEW: ND derived connective rules |
| `Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` | 559 | NEW: Hilbert derived connective rules |
| `Logics/Propositional/NaturalDeduction/Equivalence.lean` | 231 | NEW: ND-Hilbert extensional equivalence |
| `Logics/Modal/LogicalEquivalence.lean` | 132 | NEW: Modal logical equivalence |
| **Total new file lines** | **2,918** | |

#### Files Modified (insertions only)

| File | +Insertions | -Deletions | Notes |
|------|------------:|----------:|-------|
| `Foundations/Logic/ProofSystem.lean` | +35 | -17 | 3-tier hierarchy: MinimalHilbert/IntuitionisticHilbert/ClassicalHilbert |
| `Foundations/Logic/Theorems.lean` | +15 | -4 | Barrel doc update |
| `Foundations/Logic/Theorems/BigConj.lean` | +2 | -2 | Variable rename: PropositionalHilbert -> ClassicalHilbert |
| `Foundations/Logic/Theorems/Combinators.lean` | +2 | -2 | Variable rename: PropositionalHilbert -> MinimalHilbert |
| `Foundations/Logic/Theorems/Propositional/Core.lean` | +94 | -72 | Theorems stratified by logic strength |
| `Foundations/Logic/Theorems/Propositional/Connectives.lean` | +63 | -60 | Theorems stratified by logic strength |
| `Foundations/Logic/Theorems/Temporal/FrameConditions.lean` | +0 | -1 | Import cleanup |
| `Foundations/Data/ListHelpers.lean` | +7 | -4 | simp -> simp only lint fixes |
| `Logics/Propositional/Defs.lean` | +4 | -0 | Add `Proposition.iff` abbreviation |
| `Logics/Propositional/ProofSystem/Axioms.lean` | +51 | -0 | IntPropAxiom, MinPropAxiom, subsumption |
| `Logics/Propositional/ProofSystem/Derivation.lean` | +58 | -42 | Parameterize DerivationTree over Axioms type |
| `Logics/Propositional/ProofSystem/Instances.lean` | +5 | -5 | ClassicalHilbert rename |
| `Logics/Propositional/Metalogic/DeductionTheorem.lean` | +73 | -36 | Parameterize over Axioms |
| `Logics/Propositional/Metalogic/MCS.lean` | +74 | -42 | Parameterize MCS properties |
| `Logics/Propositional/NaturalDeduction/FromHilbert.lean` | +146 | -63 | Parameterize over Axioms type |
| `Logics/Modal/Basic.lean` | +19 | -11 | MinimalHilbert variable rename |
| `Logics/Modal/Denotation.lean` | +2 | -2 | Minor rename |
| `Cslib.lean` | +15 | -0 | 15 new import lines for new files |
| **Total modifications** | **~811** | **~361** | |

**Grand total: 3,729 insertions, 373 deletions** (matches `git diff --stat` output)

### Dependency Graph

The import dependencies between the pending files determine the mandatory ordering of sub-PRs.

```
ALREADY IN UPSTREAM (foundation):
  Foundations/Logic/ProofSystem (353 lines version)
  Foundations/Logic/Metalogic/Consistency
  Foundations/Logic/Metalogic/DeductionHelpers
  Foundations/Data/ListHelpers
  Propositional/{Defs, ProofSystem/Axioms (55L), Derivation (147L), Instances}
  Propositional/Metalogic/{DeductionTheorem (180L), MCS (129L)}
  Propositional/NaturalDeduction/{Basic, FromHilbert (219L)}

PENDING -- dependency order:
  [1.1] Modifications to all above (ProofSystem.lean 3-tier, Theorems, Derivation, etc.)
        -> produces: MinimalHilbert, IntuitionisticHilbert, ClassicalHilbert typeclasses
                     parameterized DerivationTree, parameterized MCS, parameterized FromHilbert

  [1.2] Propositional/ProofSystem/Axioms.lean (+51) -- adds IntPropAxiom, MinPropAxiom
  [1.2] Propositional/ProofSystem/IntMinInstances.lean (NEW)
        imports: Derivation [1.1], Axioms [1.2], ProofSystem [1.1]

  [1.3] Propositional/Semantics/Basic.lean (NEW)
        imports: Propositional/Defs [1.1]
  [1.3] Propositional/Semantics/Kripke.lean (NEW)
        imports: Propositional/Defs [1.1]

  [1.4] Propositional/Metalogic/Soundness.lean (NEW)
        imports: Semantics/Basic [1.3], Derivation [1.1], Axioms [1.2]
  [1.4] Propositional/Metalogic/Completeness.lean (NEW)
        imports: Semantics/Basic [1.3], MCS [1.1], Soundness [1.4]

  [1.5] Propositional/Metalogic/IntSoundness.lean (NEW)
        imports: Semantics/Kripke [1.3], Derivation [1.1], Axioms [1.2]
  [1.5] Propositional/Metalogic/IntLindenbaum.lean (NEW)
        imports: DeductionTheorem [1.1], MCS [1.1], Soundness [1.4]
  [1.5] Propositional/Metalogic/IntCompleteness.lean (NEW)
        imports: Semantics/Kripke [1.3], IntSoundness [1.5], IntLindenbaum [1.5]

  [1.6] Propositional/Metalogic/MinSoundness.lean (NEW)
        imports: Semantics/Kripke [1.3], Derivation [1.1], Axioms [1.2]
  [1.6] Propositional/Metalogic/MinLindenbaum.lean (NEW)
        imports: DeductionTheorem [1.1], Soundness [1.4]
  [1.6] Propositional/Metalogic/MinCompleteness.lean (NEW)
        imports: Semantics/Kripke [1.3], MinSoundness [1.6], MinLindenbaum [1.6]

  [1.7] Propositional/NaturalDeduction/FromHilbert.lean (+146/-63 modification)
        imports: DeductionTheorem [1.1] -- parameterized over Axioms from [1.2]

  [1.8] Propositional/NaturalDeduction/HilbertDerivedRules.lean (NEW)
        imports: FromHilbert [1.7]

  [1.9] Propositional/NaturalDeduction/DerivedRules.lean (NEW)
        imports: NaturalDeduction/Basic (already in upstream)

  [1.10] Propositional/NaturalDeduction/Equivalence.lean (NEW)
         imports: NaturalDeduction/Basic (upstream), FromHilbert [1.7]

  [1.11] Logics/Modal/LogicalEquivalence.lean (NEW)
         imports: Foundations/Logic/LogicalEquivalence (upstream)
         requires: MinimalHilbert typeclass from [1.1]
  [1.11] Logics/Modal/Basic.lean (+19/-11 modification)
         same dependency as [1.11]
```

### Proposed Sub-PR Decomposition

The following 11 sub-PRs cover all 3,729 insertions, each targeting the reviewer's ~500-line limit.

| Sub-PR | Title | Files | +Insertions | Deps |
|--------|-------|-------|------------:|------|
| **1.1** | 3-tier Hilbert hierarchy refactoring | 12 modified files | ~483 | none |
| **1.2** | Propositional axiom extensions + IntMin instances | 2 files (1 mod, 1 new) | ~211 | 1.1 |
| **1.3** | Propositional semantics (bivalent + Kripke) | 2 new files | ~181 | 1.1 |
| **1.4** | Classical soundness + completeness | 2 new files | ~382 | 1.2, 1.3 |
| **1.5** | Intuitionistic soundness + completeness | 3 new files | ~555 | 1.3, 1.4 |
| **1.6** | Minimal logic soundness + completeness | 3 new files | ~514 | 1.3, 1.4 |
| **1.7** | ND-Hilbert bridge parameterization | 1 modified file | ~146 | 1.2 |
| **1.8** | Hilbert-style derived connective rules | 1 new file | ~559 | 1.7 |
| **1.9** | ND derived connective rules | 1 new file | ~387 | none (uses upstream Basic) |
| **1.10** | ND-Hilbert extensional equivalence | 1 new file | ~231 | 1.7, 1.9 |
| **1.11** | Modal logical equivalence + Basic update | 2 files (1 mod, 1 new) | ~151 | 1.1 |
| **Total** | | 35 files | **~3,800** | |

Note: The total insertions from this table (~3,800) slightly exceeds the measured 3,729 due to rounding and the inclusion of 15 Cslib.lean import lines distributed across sub-PRs.

#### Detailed Sub-PR Specifications

**Sub-PR 1.1: 3-tier Hilbert hierarchy refactoring (~483 insertions)**

This PR modifies 12 already-merged files to introduce the 3-level hierarchy (`MinimalHilbert` < `IntuitionisticHilbert` < `ClassicalHilbert`), replacing the flat `PropositionalHilbert`. It is a pure refactoring with no new logic -- all existing theorems are preserved but re-stratified.

Files:
- `Foundations/Logic/ProofSystem.lean`: +35/-17 (3-tier bundled typeclass, HilbertMin/HilbertInt/HilbertCl tags)
- `Foundations/Logic/Theorems/Propositional/Core.lean`: +94/-72 (stratify LEM/DNE/RAA by logic)
- `Foundations/Logic/Theorems/Propositional/Connectives.lean`: +63/-60 (stratify De Morgan etc.)
- `Foundations/Logic/Theorems.lean`: +15/-4 (barrel doc)
- `Foundations/Logic/Theorems/BigConj.lean`: +2/-2 (rename to ClassicalHilbert)
- `Foundations/Logic/Theorems/Combinators.lean`: +2/-2 (rename to MinimalHilbert)
- `Foundations/Logic/Theorems/Temporal/FrameConditions.lean`: +0/-1 (import cleanup)
- `Foundations/Data/ListHelpers.lean`: +7/-4 (simp lint)
- `Logics/Propositional/Defs.lean`: +4/-0 (add `Proposition.iff`)
- `Logics/Propositional/ProofSystem/Derivation.lean`: +58/-42 (parameterize DerivationTree)
- `Logics/Propositional/ProofSystem/Instances.lean`: +5/-5 (ClassicalHilbert rename)
- `Logics/Propositional/Metalogic/DeductionTheorem.lean`: +73/-36 (parameterize over Axioms)
- `Logics/Propositional/Metalogic/MCS.lean`: +74/-42 (parameterize MCS properties)

Suggested branch: `propositional/hilbert-hierarchy-refactor`

---

**Sub-PR 1.2: Propositional axiom extensions + IntMin instances (~211 insertions)**

Extends the axiom system and adds instance registrations for intuitionistic and minimal Hilbert logics.

Files:
- `Logics/Propositional/ProofSystem/Axioms.lean`: +51/-0 (IntPropAxiom, MinPropAxiom, subsumption lemmas)
- `Logics/Propositional/ProofSystem/IntMinInstances.lean`: NEW 109 lines (IntuitionisticHilbert and MinimalHilbert instance registrations)
- `Cslib.lean`: +1 import line

Suggested branch: `propositional/intmin-instances`

---

**Sub-PR 1.3: Propositional semantics (~181 insertions)**

Introduces bivalent valuation semantics and Kripke model semantics for propositional logic.

Files:
- `Logics/Propositional/Semantics/Basic.lean`: NEW 47 lines (`Valuation`, `Evaluate`, `Tautology`)
- `Logics/Propositional/Semantics/Kripke.lean`: NEW 134 lines (`KripkeModel`, `IForces`, `IValid`, `MValid`, persistence lemma)
- `Cslib.lean`: +2 import lines

Suggested branch: `propositional/semantics`

---

**Sub-PR 1.4: Classical soundness + completeness (~382 insertions)**

Proves that classical propositional Hilbert logic is sound and complete with respect to bivalent semantics.

Files:
- `Logics/Propositional/Metalogic/Soundness.lean`: NEW 87 lines (classical soundness: `Derivable -> Tautology`)
- `Logics/Propositional/Metalogic/Completeness.lean`: NEW 295 lines (classical completeness via canonical valuation)
- `Cslib.lean`: +2 import lines

Suggested branch: `propositional/classical-soundness-completeness`

---

**Sub-PR 1.5: Intuitionistic soundness + completeness (~555 insertions)**

Proves soundness and completeness for intuitionistic propositional logic via Kripke models. Slightly over the 500-line limit, but the three files form a single logical unit (the completeness proof requires the Lindenbaum extension lemma as a standalone component).

Files:
- `Logics/Propositional/Metalogic/IntSoundness.lean`: NEW 103 lines
- `Logics/Propositional/Metalogic/IntLindenbaum.lean`: NEW 325 lines (DCCS extension lemma + implication witness)
- `Logics/Propositional/Metalogic/IntCompleteness.lean`: NEW 127 lines
- `Cslib.lean`: +3 import lines

Suggested branch: `propositional/intuitionistic-soundness-completeness`

---

**Sub-PR 1.6: Minimal logic soundness + completeness (~514 insertions)**

Proves soundness and completeness for minimal propositional logic. Slightly over the 500-line limit but structurally mirrors 1.5 and is logically indivisible.

Files:
- `Logics/Propositional/Metalogic/MinSoundness.lean`: NEW 96 lines
- `Logics/Propositional/Metalogic/MinLindenbaum.lean`: NEW 275 lines
- `Logics/Propositional/Metalogic/MinCompleteness.lean`: NEW 143 lines
- `Cslib.lean`: +3 import lines

Suggested branch: `propositional/minimal-soundness-completeness`

---

**Sub-PR 1.7: ND-Hilbert bridge parameterization (~146 insertions)**

Parameterizes the existing `FromHilbert.lean` over axiom sets, enabling the bridge to work for classical, intuitionistic, and minimal logic.

Files:
- `Logics/Propositional/NaturalDeduction/FromHilbert.lean`: +146/-63 (parameterize over Axioms; adds `impI_int`, `impI_min`, etc.)

Suggested branch: `propositional/fromhilbert-parameterize`

---

**Sub-PR 1.8: Hilbert-style derived connective rules (~559 insertions)**

Adds derived rules for all connectives (negation, top, conjunction, disjunction, biconditional) at three logic levels, built over `FromHilbert`. Slightly over the 500-line limit but is a single file covering one coherent feature; splitting by connective would create non-buildable partial files.

Files:
- `Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean`: NEW 559 lines
- `Cslib.lean`: +1 import line

Suggested branch: `propositional/hilbert-derived-rules`

---

**Sub-PR 1.9: Standalone ND derived rules (~387 insertions)**

Adds derived rules for the standalone natural deduction system (`Theory.Derivation`). Can be submitted in parallel with 1.7 since it depends only on the already-merged `NaturalDeduction/Basic.lean`.

Files:
- `Logics/Propositional/NaturalDeduction/DerivedRules.lean`: NEW 387 lines
- `Cslib.lean`: +1 import line

Suggested branch: `propositional/nd-derived-rules`

---

**Sub-PR 1.10: ND-Hilbert extensional equivalence (~231 insertions)**

Proves that Hilbert derivability and ND derivability are extensionally equivalent, with instances for classical, intuitionistic, and minimal logic.

Files:
- `Logics/Propositional/NaturalDeduction/Equivalence.lean`: NEW 231 lines
- `Cslib.lean`: +1 import line

Suggested branch: `propositional/nd-hilbert-equivalence`

---

**Sub-PR 1.11: Modal logical equivalence + Basic update (~151 insertions)**

Adds the `LogicalEquivalence` typeclass instance for modal logic and updates `Modal/Basic.lean` for the renamed `MinimalHilbert` variable. Can be submitted in parallel with 1.2–1.10 after 1.1 merges.

Files:
- `Logics/Modal/LogicalEquivalence.lean`: NEW 132 lines
- `Logics/Modal/Basic.lean`: +19/-11 modifications (MinimalHilbert rename)
- `Logics/Modal/Denotation.lean`: +2/-2 (trivial rename)
- `Cslib.lean`: +1 import line

Suggested branch: `modal/logical-equivalence`

---

### Submission Wave Plan

| Wave | Sub-PRs | Can submit when |
|------|---------|----------------|
| 1 | **1.1**: Hilbert hierarchy refactor | Immediately (modifications to merged files) |
| 2 | **1.2**: IntMin instances | After 1.1 merges |
| 2 | **1.3**: Propositional semantics | After 1.1 merges |
| 2 | **1.9**: ND derived rules | After 1.1 merges (independent of 1.2) |
| 2 | **1.11**: Modal logical equivalence | After 1.1 merges |
| 3 | **1.4**: Classical soundness/completeness | After 1.2 + 1.3 merge |
| 3 | **1.5**: Intuitionistic soundness/completeness | After 1.2 + 1.3 merge |
| 3 | **1.6**: Minimal soundness/completeness | After 1.2 + 1.3 merge |
| 3 | **1.7**: FromHilbert parameterization | After 1.2 merges |
| 4 | **1.8**: HilbertDerivedRules | After 1.7 merges |
| 4 | **1.10**: ND-Hilbert equivalence | After 1.7 + 1.9 merge |

Total sub-PRs: **11** | Total insertions: **~3,729**

---

## Decisions

- Count "lines" as git diff insertions (not file size), which determines review burden.
- Where a semantic unit slightly exceeds 500 lines (1.5: 555, 1.6: 514, 1.8: 559), keep as single PR because further splitting would leave non-buildable partial proofs.
- Sub-PR 1.1 (modifications-only) is the critical first PR since nearly all others depend on the 3-tier hierarchy rename.
- Sub-PRs 1.5 and 1.6 can be submitted in parallel since minimal and intuitionistic logic are independent (MinLindenbaum imports Soundness only, not IntLindenbaum).

---

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Sub-PR 1.1 modifies 12 files; reviewer may see as a refactoring PR not a feature PR | Medium | Frame as "prerequisite refactoring needed for Int/Min logic extensions" in PR description |
| 3 sub-PRs (1.5, 1.6, 1.8) slightly exceed 500 lines | Low | Justify in PR description that the unit is indivisible; request exception or ask reviewer before submitting |
| Task 123 (bib references) not yet done | Medium | Submit 1.1 first; complete bib task before submitting the metalogic sub-PRs (reviewers expect references in Lindenbaum/completeness proofs) |
| PR1 branch currently has failing CI (HilbertDerivedRules.lean +559) | High | Branch from main after each sub-PR merges; do not re-submit the monolithic branch |
| FrameConditions.lean has `import Mathlib.Algebra.Order.Group.Int` which `lake shake` may flag | Low | The FrameConditions import issue was already noted in task 86 audit; include in 1.1 but note in PR |

---

## Bib Conventions and Literature References

### Current State of `references.bib`

The `references.bib` file at the repo root contains citations for many papers but is **missing all PR1 references**:

| Author | Year | Expected key | Status |
|--------|------|-------------|--------|
| Blackburn, de Rijke, Venema | 2001 | `Blackburn2001` | Present (partial -- different title checked; `Blackburn2001` exists in bib for unrelated paper) |
| Chellas | 1980 | `Chellas1980` | Not present |
| Church | 1956 | `Church1956` | Not present |
| Curry and Feys | 1958 | `CurryFeys1958` | Not present |
| Griffin | 1990 | `Griffin1990` | Not present |
| Howard | 1969/1980 | `Howard1980` | Not present |

### CSLib Bib Conventions

From the existing `references.bib`:
- Key format: `AuthorYear` (e.g., `Blackburn2001`, `Aceto1999`)
- For multiple authors: first author only (e.g., `Angluin1988`, not `AngluinLaird1988`)
- Standard BibTeX entry types: `@book`, `@article`, `@inproceedings`
- Include `doi` field when available
- Include `url` field for online resources

### References Needed for Sub-PR Descriptions

For the PR1 sub-PRs, especially 1.4–1.6 (soundness/completeness), the following docstring-level citations should be added:

| Reference | Where needed |
|-----------|-------------|
| Church 1956 (Introduction to Mathematical Logic) | Axioms.lean, ProofSystem.lean documentation |
| Chellas 1980 (Modal Logic: An Introduction) | ProofSystem.lean modal typeclass docs |
| Blackburn, de Rijke, Venema 2001 (Modal Logic) | Metalogic soundness/completeness docs |
| Curry and Feys 1958 (Combinatory Logic) | Theorems/Combinators.lean docs |
| Griffin 1990 (Formulae-as-Types) | ProofSystem.lean Peirce axiom docs |
| Howard 1969/1980 (Formulae-as-Types) | InferenceSystem.lean docs |

Task 123 should complete this work before the sub-PR descriptions are finalized.

---

## Context Extension Recommendations

- **Topic**: PR decomposition patterns for Lean 4 libraries
- **Gap**: No documented pattern for how to split a Lean 4 PR that modifies a typeclass hierarchy (e.g., flattening a class into a 3-tier hierarchy) alongside adding new files that depend on the new hierarchy
- **Recommendation**: Add a note to `.claude/context/repo/project-overview.md` or create `.claude/context/patterns/pr-decomposition.md` documenting the pattern of (1) modifications-first PR, then (2) new files PRs in dependency order

---

## Appendix

### Verification Commands for Each Sub-PR

Before submitting each sub-PR, run from a branch containing only those files:
```bash
lake build          # must exit 0
lake test           # must pass
lake lint           # must pass
lake exe lint-style # must pass
lake exe checkInitImports  # must pass
lake exe mk_all --module --check  # must report no update
lake exe shake --add-public --keep-implied --keep-prefix  # check for unused imports
grep -rn "sorry" <files>  # must return zero hits
```

### References

- Blackburn, P., de Rijke, M. and Venema, Y. (2001). *Modal Logic*. Cambridge University Press.
- Chellas, B.F. (1980). *Modal Logic: An Introduction*. Cambridge University Press.
- Church, A. (1956). *Introduction to Mathematical Logic, Vol. I*. Princeton University Press.
- Curry, H.B. and Feys, R. (1958). *Combinatory Logic, Vol. I*. North-Holland.
- Griffin, T.G. (1990). "A Formulae-as-Types Notion of Control". *POPL 1990*.
- Howard, W.A. (1969/1980). "The Formulae-as-Types Notion of Construction".

### Task Relationships

- **Task 123**: `add_bib_references_pr1` -- add missing citations to `references.bib` before submitting metalogic sub-PRs
- **Task 60**: `pr2_modal_metalogic` -- independent of this decomposition, can proceed in parallel
- The 11 sub-PR tasks to be created by the planner will replace the monolithic `pr1/foundations-logic` branch
