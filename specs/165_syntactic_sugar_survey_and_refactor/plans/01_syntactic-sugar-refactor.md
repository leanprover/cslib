# Implementation Plan: Syntactic Sugar Survey and Refactor

- **Task**: 165 - Syntactic sugar survey and refactor
- **Status**: [IN PROGRESS]
- **Effort**: 11 hours
- **Dependencies**: None (can proceed on current branch; coordinate PL fixes with PR #633 if desired)
- **Research Inputs**: specs/165_syntactic_sugar_survey_and_refactor/reports/01_team-research.md
- **Artifacts**: plans/01_syntactic-sugar-refactor.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/context/formats/plan-format.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Systematically replace raw constructor calls (`.imp`, `.bot`, `.neg`, `.and`, `.or`, `.box`, `.diamond`, `.untl`, `.snce`, `.someFuture`, `.allFuture`, `.somePast`, `.allPast`) with their scoped notation equivalents (`→ ∧ ∨ ¬ ⊥ □ ◇ U S` and temporal operators) across Propositional/ (~320 occurrences, 22 files), Modal/ (~435 occurrences, 57 files), and Temporal/ (~1,845 occurrences, 38 files). This answers the PR #633 reviewer convention: use notation wherever available and unambiguous. A prerequisite phase adds the missing PL `↔` notation. Foundations/Logic/ and Bimodal/ are explicitly out of scope.

### Research Integration

The team research report (`01_team-research.md`, 4 teammates) provided:
- Complete per-file occurrence catalogs for Propositional and Modal, with file-level estimates for Temporal
- Precise exclusion rules: pattern-match arms, `congrArg2`, `simp only`/`unfold` tactic arguments, typeclass field assignments, abbrev definition sites, 3 namespace-conflict files, all of Foundations/Logic
- Missing notation discovery: PL `↔` has no scoped infix despite `Proposition.iff` existing
- Confirmation that all derived connectives are `abbrev`s, so replacements are definitionally invisible to the kernel

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances code quality and readability across the logic modules listed in the ROADMAP.md Completed section. Specifically, it improves readability of:
- Propositional proof system, NaturalDeduction, and Metalogic
- Modal proof system instances, Metalogic (DeductionTheorem, MCS, Soundness, Completeness)
- Temporal syntax, proof system, theorems, semantics, and metalogic (including Chronicle pipeline)

## Goals & Non-Goals

**Goals**:
- Add missing PL `↔` notation and replace all `Proposition.iff` expression-position usages
- Replace all safe expression-position constructor calls with notation across Propositional/, Modal/, and Temporal/
- Maintain exact definitional equality (zero semantic changes)
- Pass full CI pipeline (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`) after each directory

**Non-Goals**:
- Refactoring Foundations/Logic/ (polymorphic typeclass layer, no notation by design)
- Refactoring Bimodal/ (not in task scope per user decision)
- Replacing constructor names in pattern-match arms (`| .imp A B =>`)
- Replacing constructor names in tactic arguments (`simp only [Formula.neg]`, `unfold Proposition.diamond`, `congrArg2 Formula.imp`)
- Replacing constructor names in typeclass field assignments or abbrev definition sites
- Adding new notation beyond the missing PL `↔`
- Touching `Modal/FromPropositional.lean` (cross-namespace, leave fully qualified)
- Touching `Temporal/ProofSystem/Instances.lean` (namespace conflict with single-letter operators)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Precedence/parenthesization errors after replacing `.imp` with `→` | M | M | Build after each file; fix parenthesization immediately; `→` is right-associative at precedence 30 matching `.imp` |
| `→` notation confused with function arrow by elaborator | M | L | Type inference resolves this in context; tested extensively in existing notation usage |
| PR #635/#637 churn invalidates Modal line numbers | L | M | Re-verify files at implementation time; replacements are pattern-based, not line-based |
| Large Temporal files (PointInsertion: 664 occurrences) cause merge conflicts with ongoing work | M | L | Work on current branch; keep commits atomic per-file |
| Recursive function body replacements reduce visual alignment with match patterns | L | L | Use judgment: replace only when it improves readability; keep raw constructors where body mirrors pattern |
| Missing parentheses around negation (`¬φ → ψ` vs `¬(φ → ψ)`) | H | L | `¬` prefix at precedence 40 binds tighter than `→` at 30, matching the original `.neg` semantics; verify each site |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5 | 2 |
| 4 | 6, 7 | 3 |
| 5 | 8 | 4 |
| 6 | 9 | 6, 7, 8 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Add Missing PL Biconditional Notation [COMPLETED]

**Goal**: Add scoped `↔` infix notation for `Proposition.iff` in PL `Defs.lean`, aligning PL with Modal and Temporal which already have it.

**Tasks**:
- [ ] Add `@[inherit_doc] scoped infix:30 " ↔ " => Proposition.iff` to `Cslib/Logics/Propositional/Defs.lean` (after line 86, alongside existing notation block)
- [ ] Verify precedence 30 matches Modal/Temporal `↔` declarations
- [ ] Run `lake build Cslib.Logics.Propositional.Defs` to confirm no errors

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` -- add one notation declaration

**Verification**:
- `lake build Cslib.Logics.Propositional.Defs` succeeds
- Notation `↔` resolves to `Proposition.iff` in PL namespace

---

### Phase 2: Refactor Propositional/Defs and ProofSystem [COMPLETED]

**Goal**: Replace raw constructors with notation in PL definition and proof system files (highest readability impact, foundational files).

**Tasks**:
- [ ] Refactor `Cslib/Logics/Propositional/Defs.lean` -- replace expression-position `.imp`, `.bot`, `.neg`, `.and`, `.or`, `.iff` with `→ ⊥ ¬ ∧ ∨ ↔` (~15 occurrences); preserve abbrev definition sites and pattern-match arms
- [ ] Refactor `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- axiom schemas (~20 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- derivation rules (~10 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/ProofSystem/Instances.lean` -- instance definitions (~15 occurrences); preserve typeclass field assignments
- [ ] Refactor `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` -- intuitionistic/minimal instances (~10 occurrences)
- [ ] Run `lake build Cslib.Logics.Propositional.ProofSystem` after each file

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` -- expression-position constructors (~15)
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- axiom schemas (~20)
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- derivation rules (~10)
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` -- instances (~15)
- `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` -- instances (~10)

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem` succeeds after each file
- No raw expression-position `.imp`/`.bot`/`.neg`/`.and`/`.or` remains (excluding exclusion categories)

---

### Phase 3: Refactor Propositional/Semantics and NaturalDeduction [COMPLETED]

**Goal**: Replace raw constructors in PL semantics and natural deduction files.

**Tasks**:
- [ ] Refactor `Cslib/Logics/Propositional/Semantics/Basic.lean` -- semantic evaluation (~10 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/Semantics/Kripke.lean` -- Kripke semantics (~10 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- ND rules (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` -- derived rules (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` -- equivalence proofs (~10 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` -- Hilbert-to-ND (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` -- derived Hilbert rules (~40 occurrences)
- [ ] Run `lake build` after each file

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Basic.lean` (~10)
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` (~10)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (~15)
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` (~15)
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (~10)
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` (~15)
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` (~40)

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction` succeeds
- `lake build Cslib.Logics.Propositional.Semantics` succeeds

---

### Phase 4: Refactor Propositional/Metalogic and Full PL CI [COMPLETED]

**Goal**: Replace raw constructors in all PL metalogic files and run full CI for the Propositional directory.

**Tasks**:
- [ ] Refactor `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` (~20 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/Metalogic/MCS.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/Metalogic/Soundness.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/Metalogic/Completeness.lean` (~60 occurrences, densest PL file)
- [ ] Refactor `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` (~40 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` (~10 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` (~35 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` (~10 occurrences)
- [ ] Run `lake build Cslib.Logics.Propositional` after each file
- [ ] Run full PL CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` (~20)
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` (~15)
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` (~15)
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` (~60)
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` (~40)
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` (~15)
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` (~10)
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` (~35)
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` (~15)
- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` (~10)

**Verification**:
- `lake build Cslib.Logics.Propositional` succeeds
- Full CI pipeline passes
- Zero raw expression-position constructors remain in Propositional/ (excluding exclusion categories)

---

### Phase 5: Refactor Modal/Basic, Cube, Denotation, LogicalEquivalence [COMPLETED]

**Goal**: Replace raw constructors in core Modal definition and utility files with `→ ∧ ∨ ¬ ⊥ □ ◇` notation.

**Tasks**:
- [ ] Refactor `Cslib/Logics/Modal/Basic.lean` -- core definitions, notation usage (~15 occurrences); preserve abbrev sites and pattern-match arms
- [ ] Refactor `Cslib/Logics/Modal/Cube.lean` -- modal cube definitions (~20 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/Denotation.lean` -- denotation semantics (~10 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/LogicalEquivalence.lean` -- logical equivalence (~10 occurrences)
- [ ] **Skip** `Cslib/Logics/Modal/FromPropositional.lean` -- cross-namespace, leave fully qualified
- [ ] Run `lake build` after each file

**Timing**: 0.75 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` (~15)
- `Cslib/Logics/Modal/Cube.lean` (~20)
- `Cslib/Logics/Modal/Denotation.lean` (~10)
- `Cslib/Logics/Modal/LogicalEquivalence.lean` (~10)

**Verification**:
- `lake build Cslib.Logics.Modal.Basic` succeeds
- `lake build Cslib.Logics.Modal.Cube` succeeds
- `FromPropositional.lean` untouched

---

### Phase 6: Refactor Modal/ProofSystem Instances [COMPLETED]

**Goal**: Replace raw constructors in the 15 ProofSystem/Instances files -- the highest-value Modal targets where axiom schemas become dramatically more readable (e.g., `KAxiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ)) (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))` becomes `KAxiom (□(φ → ψ) → □φ → □ψ)`).

**Tasks**:
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances.lean` -- umbrella file (~5 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/K.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/T.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/D.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/B.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/K4.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/K5.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/K45.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/KB5.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/D4.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/D5.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/D45.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/DB.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/TB.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/S4.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/ProofSystem/Instances/S5.lean` (~15 occurrences)
- [ ] Run `lake build Cslib.Logics.Modal.ProofSystem` after each file; preserve typeclass field assignments

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/Instances.lean` (~5)
- `Cslib/Logics/Modal/ProofSystem/Instances/K.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/T.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/D.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/B.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/K4.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/K5.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/K45.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/KB5.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/D4.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/D5.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/D45.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/DB.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/TB.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/S4.lean` (~15)
- `Cslib/Logics/Modal/ProofSystem/Instances/S5.lean` (~15)

**Verification**:
- `lake build Cslib.Logics.Modal.ProofSystem` succeeds
- Axiom schemas are now human-readable (e.g., `□(φ → ψ) → □φ → □ψ`)

---

### Phase 7: Refactor Modal/Metalogic and Systems, Full Modal CI [COMPLETED]

**Goal**: Replace raw constructors in all Modal metalogic files (core + per-system Soundness/Completeness) and run full CI for Modal.

**Tasks**:
- [ ] Refactor `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` (~20 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` (~25 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/Metalogic/MCS.lean` (~20 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/Metalogic/Soundness.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/Metalogic/Completeness.lean` (~25 occurrences)
- [ ] Refactor `Cslib/Logics/Modal/Metalogic.lean` -- umbrella file (~5 occurrences)
- [ ] Refactor all 15 `Cslib/Logics/Modal/Metalogic/Systems/*/Soundness.lean` files (~5 each, ~75 total)
- [ ] Refactor all 15 `Cslib/Logics/Modal/Metalogic/Systems/*/Completeness.lean` files (~5 each, ~75 total)
- [ ] Run `lake build Cslib.Logics.Modal` after completing all files
- [ ] Run full Modal CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` (~20)
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` (~25)
- `Cslib/Logics/Modal/Metalogic/MCS.lean` (~20)
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` (~15)
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` (~25)
- `Cslib/Logics/Modal/Metalogic.lean` (~5)
- 15x `Cslib/Logics/Modal/Metalogic/Systems/{K,T,D,B,K4,K5,K45,KB5,D4,D5,D45,DB,TB,S4,S5}/Soundness.lean` (~75 total)
- 15x `Cslib/Logics/Modal/Metalogic/Systems/{K,T,D,B,K4,K5,K45,KB5,D4,D5,D45,DB,TB,S4,S5}/Completeness.lean` (~75 total)

**Verification**:
- `lake build Cslib.Logics.Modal` succeeds
- Full CI pipeline passes
- Zero raw expression-position constructors remain in Modal/ (excluding `FromPropositional.lean` and exclusion categories)

---

### Phase 8: Refactor Temporal/Syntax, Semantics, ProofSystem, Theorems [COMPLETED]

**Goal**: Replace raw constructors in Temporal definition, syntax, semantics, proof system, and theorem files with `→ ∧ ∨ ¬ ⊥ □ ◇ U S` and temporal operator notation (`F G P H`).

**Tasks**:
- [x] Refactor `Cslib/Logics/Temporal/Syntax/Formula.lean` -- replaced def bodies for weakFuture/weakPast/always/sometimes/release/trigger/weakUntil/weakSince/strongRelease/strongTrigger; skipped abbrev bodies, pattern match arms, simp tactic args, congrArg₂ calls
- [x] Refactor `Cslib/Logics/Temporal/Syntax/Context.lean` *(deviation: skipped -- 0 occurrences)*
- [x] Refactor `Cslib/Logics/Temporal/Syntax/BigConj.lean` -- all occurrences are in pattern match arms or `rfl` theorem statements; no safe replacements
- [x] Refactor `Cslib/Logics/Temporal/Syntax/Subformulas.lean` -- replaced in theorem type positions: allPast/allFuture/imp/untl/snce in set membership hypotheses
- [x] Refactor `Cslib/Logics/Temporal/Semantics/Model.lean` *(deviation: skipped -- 0 occurrences)*
- [x] Refactor `Cslib/Logics/Temporal/Semantics/Satisfies.lean` -- replaced Formula.neg/someFuture/somePast/allFuture/allPast in theorem type positions
- [x] Refactor `Cslib/Logics/Temporal/Semantics/Validity.lean` -- replaced 1 Formula.neg in theorem type position
- [x] Refactor `Cslib/Logics/Temporal/ProofSystem.lean` *(deviation: skipped -- 0 occurrences)*
- [x] Refactor `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` *(deviation: skipped -- all occurrences are in inductive constructor return types)*
- [x] Refactor `Cslib/Logics/Temporal/ProofSystem/Derivation.lean` *(deviation: skipped -- 0 occurrences)*
- [x] Refactor `Cslib/Logics/Temporal/ProofSystem/Derivable.lean` *(deviation: skipped -- 0 occurrences)*
- [x] **Skip** `Cslib/Logics/Temporal/ProofSystem/Instances.lean` -- namespace conflict with single-letter temporal operators
- [x] Refactor `Cslib/Logics/Temporal/Theorems.lean` *(deviation: skipped -- 0 occurrences)*
- [x] Refactor `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` *(deviation: skipped -- directory does not exist; Theorems.lean is a single file)*
- [x] Refactor `Cslib/Logics/Temporal/Theorems/FrameConditions.lean` *(deviation: skipped -- directory does not exist)*
- [x] Refactor `Cslib/Logics/Temporal/FromPropositional.lean` *(deviation: skipped -- cross-namespace conflict: in Cslib.Logic not Cslib.Logic.Temporal, scoped notations not active)*
- [x] Run `lake build` after each file

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` (~30)
- `Cslib/Logics/Temporal/Syntax/Context.lean` (~15)
- `Cslib/Logics/Temporal/Syntax/BigConj.lean` (~20)
- `Cslib/Logics/Temporal/Syntax/Subformulas.lean` (~25)
- `Cslib/Logics/Temporal/Semantics/Model.lean` (~10)
- `Cslib/Logics/Temporal/Semantics/Satisfies.lean` (~20)
- `Cslib/Logics/Temporal/Semantics/Validity.lean` (~10)
- `Cslib/Logics/Temporal/ProofSystem.lean` (~5)
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` (~50)
- `Cslib/Logics/Temporal/ProofSystem/Derivation.lean` (~15)
- `Cslib/Logics/Temporal/ProofSystem/Derivable.lean` (~15)
- `Cslib/Logics/Temporal/Theorems.lean` (~5)
- `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean` (~30)
- `Cslib/Logics/Temporal/Theorems/FrameConditions.lean` (~20)
- `Cslib/Logics/Temporal/FromPropositional.lean` (~10, conditional)

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax` succeeds
- `lake build Cslib.Logics.Temporal.Semantics` succeeds
- `lake build Cslib.Logics.Temporal.ProofSystem` succeeds
- `lake build Cslib.Logics.Temporal.Theorems` succeeds

---

### Phase 9: Refactor Temporal/Metalogic and Full Temporal CI [NOT STARTED]

**Goal**: Replace raw constructors in all Temporal metalogic files (the largest single concentration of occurrences, including the Chronicle pipeline with PointInsertion at 664 occurrences) and run full CI.

**Tasks**:
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean` (~20 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` (~30 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` (~20 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/MCS.lean` (~123 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean` (~30 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean` (~25 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Soundness.lean` (~30 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean` (~25 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Completeness.lean` (~30 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` (~20 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean` (~15 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` (~20 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic.lean` -- umbrella (~5 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` (~20 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` (~139 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` (~30 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Chronicle/CanonicalChain.lean` (~40 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean` (~30 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` (~664 occurrences, largest single file)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` (~40 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` (~173 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean` (~50 occurrences)
- [ ] Refactor `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean` (~20 occurrences)
- [ ] Run `lake build` after each file; exercise special care with PointInsertion (build after every ~100 replacements if possible)
- [ ] Run full Temporal CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`

**Timing**: 2 hours

**Depends on**: 6, 7, 8

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean` (~20)
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` (~30)
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` (~15)
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` (~20)
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` (~123)
- `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean` (~30)
- `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean` (~25)
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean` (~30)
- `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean` (~25)
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` (~30)
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` (~20)
- `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean` (~15)
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` (~20)
- `Cslib/Logics/Temporal/Metalogic.lean` (~5)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` (~20)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` (~139)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` (~30)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CanonicalChain.lean` (~40)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean` (~30)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` (~664)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` (~40)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` (~173)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean` (~50)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean` (~20)

**Verification**:
- `lake build Cslib.Logics.Temporal` succeeds
- Full CI pipeline passes: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`
- Zero raw expression-position constructors remain in Temporal/ (excluding `ProofSystem/Instances.lean` and exclusion categories)

---

## Testing & Validation

- [ ] `lake build` succeeds (full project build, no errors)
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes (Cslib.Init imports verified)
- [ ] `lake exe lint-style` passes (style linting)
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (dependency analysis)
- [ ] Spot-check: no raw expression-position `.imp`, `.bot`, `.neg`, `.and`, `.or`, `.box`, `.diamond`, `.untl`, `.snce`, `.someFuture`, `.allFuture`, `.somePast`, `.allPast` in Propositional/, Modal/, or Temporal/ (excluding known exclusion categories)
- [ ] Verify excluded files remain untouched: `Modal/FromPropositional.lean`, `Temporal/ProofSystem/Instances.lean`, all of `Foundations/Logic/`, all of `Bimodal/`

## Artifacts & Outputs

- `specs/165_syntactic_sugar_survey_and_refactor/plans/01_syntactic-sugar-refactor.md` (this plan)
- Modified files: ~115 `.lean` files across Propositional/ (22), Modal/ (55, excluding FromPropositional), Temporal/ (36, excluding ProofSystem/Instances)
- `specs/165_syntactic_sugar_survey_and_refactor/summaries/01_syntactic-sugar-refactor-summary.md` (post-implementation)

## Rollback/Contingency

All replacements are definitionally invisible to the Lean kernel (derived connectives are `abbrev`s that unfold to the same terms). If any replacement causes an unexpected build failure:

1. **Per-file rollback**: `git checkout -- <file>` to restore the pre-refactored version
2. **Per-directory rollback**: `git stash` all changes since the last CI-passing commit
3. **Full rollback**: `git reset --soft` to the pre-task commit; no semantic changes were introduced, so no downstream breakage possible

If precedence/parenthesization issues arise during replacement, add explicit parentheses around the notation expression rather than reverting to raw constructors.
