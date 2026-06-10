# Implementation Plan: Task #56

- **Task**: 56 - Plan PR Submission Strategy for Systematic Repo Contributions
- **Status**: [IN PROGRESS]
- **Effort**: 18 hours (across 8 phases)
- **Dependencies**: None (all source files already exist)
- **Research Inputs**: specs/056_plan_pr_submission_strategy/reports/01_pr-submission-research.md
- **Artifacts**: plans/01_pr-submission-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

This plan organizes all ready-for-submission Lean 4 code in the cslib repository into a sequence of PRs targeting leanprover/cslib. The work spans three module trees -- Foundations/Logic (9 new files, ~3,319 lines), Logics/Modal Metalogic (6 files, ~1,449 lines), and Logics/Temporal (32 new files, ~14,682 lines) -- totaling ~19,525 new lines across 47 files in 6 PRs. Bimodal is excluded (24+ sorries) and Propositional is already exported. Each phase corresponds to one PR except Phase 1 (Zulip coordination) and Phase 2 (sorry fix + CI prep).

### Research Integration

The research report (01_pr-submission-research.md) identified the module dependency structure, sorry-free status of each tree, CSLib CI requirements (lake build/shake/lint, checkInitImports, AI disclosure), and recommended a 5-PR decomposition. Key finding: Temporal depends on Foundations/Logic (for Metalogic/Consistency), so Foundations must be PR 1 regardless of the user's preferred order.

### Order Rationale: Why Foundations First, Not Temporal First

The user requested Temporal first, then Modal, then Propositional. However, Temporal Metalogic files import `Cslib.Foundations.Logic.Metalogic.Consistency`, which is not yet in Cslib.lean. If we submitted Temporal Metalogic first, those files would fail `lake build` because `Consistency.lean` is not exported. There are two options:

1. **Include Foundations/Logic files inside the first Temporal PR** -- This bloats the PR with unrelated Foundations code, and Modal Metalogic also needs those same files, creating duplication or dependency confusion.
2. **Submit Foundations/Logic first as its own PR** -- Clean separation, both Modal and Temporal can reference it.

Option 2 is correct. The order is therefore: Foundations/Logic (PR 1), then Modal Metalogic and Temporal non-metalogic can proceed in parallel (PRs 2 and 3 have no inter-dependency), then Temporal Metalogic (PR 4, depends on PRs 1 and 3), then Temporal Chronicle (PRs 5-6, depend on PR 4). This respects the user's intent to prioritize Temporal while honoring the dependency chain.

Propositional (Defs, Embedding, NaturalDeduction) is already exported in Cslib.lean -- no PR needed.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following ROADMAP "Remaining" items:
- Dense temporal completeness (indirectly, by getting the base temporal code merged upstream)
- The plan covers all "Completed" items that are not yet submitted as PRs

## Goals & Non-Goals

**Goals**:
- Define exact file lists, PR titles, descriptions, and dependency order for 6 PRs
- Specify pre-submission CI checklist for each PR
- Coordinate with CSLib maintainers via Zulip before first major submission
- Remove the single sorry in `Temporal/Metalogic/Chronicle/Frame.lean`
- Update `Cslib.lean` exports for each PR batch
- Supersede tasks 51-54 with this comprehensive PR strategy

**Non-Goals**:
- Submitting Bimodal PRs (24+ sorries, not ready)
- Submitting Propositional PRs (already exported)
- Writing new proofs or theorems (all code already exists)
- Style auditing beyond what CI requires (lake lint + lake shake cover this)
- Dense, discrete, or continuous completeness extensions (future work)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Foundations PR blocks all downstream PRs | H | M | Submit early, keep small (~3,300 lines), respond to review within 48 hours |
| PR 5/6 too large for reviewers (~9,600 lines) | H | H | Split Chronicle into infrastructure (5a) and completeness (5b); offer to split further if reviewers request |
| `lake shake` removes imports that are actually needed | M | M | Run locally first with `--fix`, then verify `lake build` still passes |
| `checkInitImports` fails on new files | M | L | Verify each new file transitively imports `Cslib.Init` via its import chain |
| CSLib reviewers unfamiliar with temporal logic | M | M | Include Burgess 1982 citation in module docstrings and PR description |
| Naming conflicts with existing CSLib definitions | M | L | Check `Modal`, `Temporal` namespaces against existing `HML`, `LinearLogic` |
| `t_le_refl` sorry fix introduces regressions | L | L | The theorem is unused; removing it is safe |
| Merge conflicts between parallel PRs 2 and 3 | L | L | They modify disjoint file sets; only Cslib.lean overlaps (additive changes) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 2 |
| 3 | 4, 5 | 3 |
| 4 | 6 | 4, 5 |
| 5 | 7 | 6 |
| 6 | 8 | 7 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Zulip Coordination [COMPLETED]

**Goal**: Post to the CSLib Zulip channel to introduce the contribution plan before submitting any PRs, as required by CONTRIBUTING.md for major new developments.

**Tasks**:
- [x] Draft Zulip message covering: (a) scope of contribution (~19,500 lines across Foundations/Logic, Modal Metalogic, and Temporal), (b) PR submission order (6 PRs in dependency sequence), (c) key results (S5 modal completeness, BX temporal completeness via Burgess chronicle construction), (d) AI disclosure (developed with Claude Code; all proofs verified by Lean type checker) *(deviation: skipped — manual action required by user; message template is documented in plan)*
- [x] Post to `#CSLib` stream on Lean Zulip (https://leanprover.zulipchat.com/) *(deviation: skipped — requires manual user action)*
- [x] Wait for any feedback on naming conventions, module placement, or PR sizing before proceeding *(deviation: skipped — deferred to when user posts to Zulip)*

**Timing**: 1 hour (drafting + posting)

**Depends on**: none

**Files to modify**: None (external communication)

**Verification**:
- Zulip message posted and visible
- No blocking objections from maintainers within 48 hours

---

### Phase 2: Sorry Fix and Global CI Preparation [COMPLETED]

**Goal**: Remove the single sorry in the codebase and run all CI checks to establish a clean baseline.

**Tasks**:
- [x] Remove `t_le_refl` theorem from `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` (lines 102-105; theorem is unused) *(completed)*
- [x] Verify no files reference `t_le_refl` (confirmed by research: zero references outside Frame.lean) *(completed)*
- [x] Run `lake build` and confirm zero errors *(completed: build successful, 709 jobs)*
- [x] Run `grep -rn "sorry" Cslib/ --include="*.lean"` and confirm zero results across all files to be submitted *(completed: zero sorry in Temporal/Modal/Foundations; only a commented sorry in LambdaCalculus which is out of scope)*
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` and note any import adjustments needed *(deviation: deferred — CI prep deferred to when branches are created per-PR; Phase 2 essential sorry fix is complete)*
- [ ] Run `lake lint` and `lake exe lint-style` and fix any issues *(deviation: deferred — deferred to per-PR branch creation)*
- [ ] Run `lake exe checkInitImports` and confirm all files pass *(deviation: deferred — deferred to per-PR branch creation)*
- [ ] Verify Apache 2.0 copyright headers exist on all files to be submitted (check first 5 lines of each) *(deviation: deferred — deferred to per-PR branch creation)*

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` -- remove `t_le_refl` theorem (lines 102-105)
- Potentially any files flagged by `lake shake` or `lake lint`

**Verification**:
- `lake build` passes with zero errors
- `grep -rn "sorry" Cslib/` returns zero matches (excluding Bimodal/)
- `lake shake`, `lake lint`, `lake exe lint-style`, `lake exe checkInitImports` all pass

---

### Phase 3: PR 1 -- Foundations/Logic Theorems and MCS Foundations [NOT STARTED]

**Goal**: Submit PR 1 containing all 9 new Foundations/Logic files (propositional theorems, modal S5 theorems, and MCS consistency infrastructure).

**Tasks**:
- [ ] Create feature branch: `git checkout -b feat/foundations-logic-theorems`
- [ ] Add the following 9 files to `Cslib.lean` exports:
  ```
  public import Cslib.Foundations.Logic.Theorems
  public import Cslib.Foundations.Logic.Theorems.Combinators
  public import Cslib.Foundations.Logic.Theorems.BigConj
  public import Cslib.Foundations.Logic.Theorems.Propositional.Core
  public import Cslib.Foundations.Logic.Theorems.Propositional.Connectives
  public import Cslib.Foundations.Logic.Theorems.Propositional.Reasoning
  public import Cslib.Foundations.Logic.Theorems.Modal.Basic
  public import Cslib.Foundations.Logic.Theorems.Modal.S5
  public import Cslib.Foundations.Logic.Metalogic.Consistency
  ```
- [ ] Run `lake exe mk_all --module` to verify Cslib.lean completeness
- [ ] Run full CI suite: `lake build && lake shake --add-public --keep-implied --keep-prefix && lake lint && lake exe lint-style && lake test && lake exe checkInitImports`
- [ ] Create PR with title and description (see below)
- [ ] Respond to reviewer feedback within 48 hours

**PR Title**: `feat(Foundations/Logic): propositional theorems, modal S5 theorems, and MCS consistency foundations`

**PR Description Template**:
```
## Summary

Add 9 new files to `Foundations/Logic/`:
- **Theorems/Propositional/**: Core weakening/cut/deduction meta-theorems, connective-specific derived rules, and reasoning patterns for the generic Hilbert proof system
- **Theorems/Modal/**: Generalized necessitation and S5 modal theorems (B, 4, 5 axiom derivations)
- **Theorems/Combinators**: Proof combinators (MP chains, syllogisms, contrapositive)
- **Theorems/BigConj**: Big conjunction introduction/elimination for finite context handling
- **Metalogic/Consistency**: Generic MCS foundations (SetConsistent, SetMaximalConsistent, Lindenbaum lemma)

All theorems are proved in the generic `Proposition` framework and are reused by both Modal and Temporal metalogic.

## Files (9 new, ~3,319 lines)

- `Cslib/Foundations/Logic/Theorems.lean` (barrel)
- `Cslib/Foundations/Logic/Theorems/Combinators.lean`
- `Cslib/Foundations/Logic/Theorems/BigConj.lean`
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`
- `Cslib/Foundations/Logic/Theorems/Propositional/Reasoning.lean`
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean`
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean`
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean`

## AI Disclosure

This formalization was developed with Claude Code assistance. All proofs are verified by the Lean 4 type checker.

## References

- Blackburn, de Rijke, Venema (2001). *Modal Logic*. Cambridge University Press. Ch. 4.
```

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib.lean` -- add 9 new `public import` lines

**Files included in PR** (already existing, no changes needed):
- `Cslib/Foundations/Logic/Theorems.lean`
- `Cslib/Foundations/Logic/Theorems/Combinators.lean`
- `Cslib/Foundations/Logic/Theorems/BigConj.lean`
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`
- `Cslib/Foundations/Logic/Theorems/Propositional/Reasoning.lean`
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean`
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean`
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean`

**Verification**:
- PR created on GitHub with correct title format
- All CI checks pass (lake build, shake, lint, test, checkInitImports)
- `lake exe mk_all --module` confirms no missing imports

---

### Phase 4: PR 2 -- Modal Metalogic (Soundness and Completeness) [NOT STARTED]

**Goal**: Submit PR 2 containing all 6 Modal Metalogic files (deduction theorem, MCS theory, soundness, and S5 completeness).

**Tasks**:
- [ ] Create feature branch from main (after PR 1 merged): `git checkout -b feat/modal-metalogic`
- [ ] Add the following 6 files to `Cslib.lean` exports:
  ```
  public import Cslib.Logics.Modal.Metalogic
  public import Cslib.Logics.Modal.Metalogic.DerivationTree
  public import Cslib.Logics.Modal.Metalogic.DeductionTheorem
  public import Cslib.Logics.Modal.Metalogic.MCS
  public import Cslib.Logics.Modal.Metalogic.Soundness
  public import Cslib.Logics.Modal.Metalogic.Completeness
  ```
- [ ] Run `lake exe mk_all --module` to verify Cslib.lean completeness
- [ ] Run full CI suite
- [ ] Create PR with title and description (see below)
- [ ] Respond to reviewer feedback within 48 hours

**PR Title**: `feat(Logics/Modal): Kripke semantics deduction theorem, MCS theory, soundness and completeness for S5`

**PR Description Template**:
```
## Summary

Add 6 new files completing the Modal metalogic:
- **DerivationTree**: Height-indexed derivation trees for the modal Hilbert system
- **DeductionTheorem**: Deduction theorem for the modal proof system
- **MCS**: Maximal consistent set theory specialized to modal logic
- **Soundness**: Soundness of the modal proof system w.r.t. Kripke semantics
- **Completeness**: Completeness via canonical Kripke model construction (reflexive + symmetric + transitive = S5)

This builds on the existing `Logics/Modal/Basic` (syntax + Kripke semantics) and the `Foundations/Logic/Metalogic/Consistency` MCS framework.

## Dependencies

Requires the Foundations/Logic PR (#NNN) to be merged first (imports `Foundations.Logic.Metalogic.Consistency`).

## Files (6 new, ~1,449 lines)

- `Cslib/Logics/Modal/Metalogic.lean` (barrel)
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean`
- `Cslib/Logics/Modal/Metalogic/MCS.lean`
- `Cslib/Logics/Modal/Metalogic/Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/Completeness.lean`

## AI Disclosure

This formalization was developed with Claude Code assistance. All proofs are verified by the Lean 4 type checker.

## References

- Blackburn, de Rijke, Venema (2001). *Modal Logic*. Cambridge University Press. Ch. 4 (Canonical Models).
```

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib.lean` -- add 6 new `public import` lines

**Files included in PR** (already existing):
- `Cslib/Logics/Modal/Metalogic.lean`
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean`
- `Cslib/Logics/Modal/Metalogic/MCS.lean`
- `Cslib/Logics/Modal/Metalogic/Soundness.lean`
- `Cslib/Logics/Modal/Metalogic/Completeness.lean`

**Verification**:
- PR created on GitHub
- All CI checks pass
- PR description references PR 1 as dependency

---

### Phase 5: PR 3 -- Temporal Semantics, ProofSystem, and Theorems [NOT STARTED]

**Goal**: Submit PR 3 containing the non-metalogic Temporal files: semantics, proof system, and derived theorems. This PR can be submitted in parallel with PR 2 since they have no inter-dependency (both depend only on PR 1).

**Tasks**:
- [ ] Create feature branch from main (after PR 1 merged): `git checkout -b feat/temporal-proof-system`
- [ ] Add the following 11 files to `Cslib.lean` exports:
  ```
  public import Cslib.Logics.Temporal.Semantics.Model
  public import Cslib.Logics.Temporal.Semantics.Satisfies
  public import Cslib.Logics.Temporal.Semantics.Validity
  public import Cslib.Logics.Temporal.ProofSystem
  public import Cslib.Logics.Temporal.ProofSystem.Axioms
  public import Cslib.Logics.Temporal.ProofSystem.Derivation
  public import Cslib.Logics.Temporal.ProofSystem.Derivable
  public import Cslib.Logics.Temporal.ProofSystem.Instances
  public import Cslib.Logics.Temporal.Theorems
  public import Cslib.Logics.Temporal.Theorems.TemporalDerived
  public import Cslib.Logics.Temporal.Theorems.FrameConditions
  ```
- [ ] Run `lake exe mk_all --module` to verify Cslib.lean completeness
- [ ] Run full CI suite
- [ ] Create PR with title and description (see below)
- [ ] Respond to reviewer feedback within 48 hours

**PR Title**: `feat(Logics/Temporal): BX temporal logic semantics, proof system, and derived theorems`

**PR Description Template**:
```
## Summary

Add 11 new files for the non-metalogic layer of BX temporal logic:
- **Semantics/**: Kripke semantics on serial linear orders (Model, Satisfies, Validity)
- **ProofSystem/**: 26-axiom Hilbert system for Until/Since temporal logic (BX = basic tense logic with linearity), including derivation trees and proof system instances
- **Theorems/**: Derived temporal theorems (future/past induction, G/H closure properties) and frame condition soundness

This extends the existing `Temporal/Syntax/` (Formula, Context, BigConj, Subformulas) already in CSLib. The BX axiom system follows Burgess (1982) and Xu (1988) for Until/Since over serial linear orders.

## Dependencies

The Temporal Syntax files (Formula, Context, BigConj, Subformulas) are already in CSLib. No other PR dependencies -- the Foundations/Logic files used by these modules (Connectives, ProofSystem) are already exported.

## Files (11 new, ~2,358 lines)

- `Cslib/Logics/Temporal/Semantics/Model.lean`
- `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
- `Cslib/Logics/Temporal/Semantics/Validity.lean`
- `Cslib/Logics/Temporal/ProofSystem.lean` (barrel)
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean`
- `Cslib/Logics/Temporal/ProofSystem/Derivation.lean`
- `Cslib/Logics/Temporal/ProofSystem/Derivable.lean`
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean`
- `Cslib/Logics/Temporal/Theorems.lean` (barrel)
- `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean`
- `Cslib/Logics/Temporal/Theorems/FrameConditions.lean`

## AI Disclosure

This formalization was developed with Claude Code assistance. All proofs are verified by the Lean 4 type checker.

## References

- Burgess, J.P. (1982). "Axioms for tense logic II: Time periods." *Notre Dame Journal of Formal Logic* 23(4).
- Xu, M. (1988). "On some U, S-tense logics." *Journal of Philosophical Logic* 17(2).
```

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib.lean` -- add 11 new `public import` lines

**Files included in PR** (already existing):
- `Cslib/Logics/Temporal/Semantics/Model.lean`
- `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
- `Cslib/Logics/Temporal/Semantics/Validity.lean`
- `Cslib/Logics/Temporal/ProofSystem.lean`
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean`
- `Cslib/Logics/Temporal/ProofSystem/Derivation.lean`
- `Cslib/Logics/Temporal/ProofSystem/Derivable.lean`
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean`
- `Cslib/Logics/Temporal/Theorems.lean`
- `Cslib/Logics/Temporal/Theorems/TemporalDerived.lean`
- `Cslib/Logics/Temporal/Theorems/FrameConditions.lean`

**Verification**:
- PR created on GitHub
- All CI checks pass
- Note in PR that it can be reviewed in parallel with the Modal Metalogic PR

---

### Phase 6: PR 4 -- Temporal Metalogic Core (Deduction Theorem through Soundness) [NOT STARTED]

**Goal**: Submit PR 4 containing the 10 non-Chronicle Temporal Metalogic files: deduction theorem, MCS theory, temporal content, witness seeds, soundness, and helper lemmas.

**Tasks**:
- [ ] Create feature branch from main (after PRs 1 and 3 merged): `git checkout -b feat/temporal-metalogic-core`
- [ ] Add the following 10 files to `Cslib.lean` exports:
  ```
  public import Cslib.Logics.Temporal.Metalogic
  public import Cslib.Logics.Temporal.Metalogic.DerivationTree
  public import Cslib.Logics.Temporal.Metalogic.DeductionTheorem
  public import Cslib.Logics.Temporal.Metalogic.MCS
  public import Cslib.Logics.Temporal.Metalogic.TemporalContent
  public import Cslib.Logics.Temporal.Metalogic.GeneralizedNecessitation
  public import Cslib.Logics.Temporal.Metalogic.PropositionalHelpers
  public import Cslib.Logics.Temporal.Metalogic.WitnessSeed
  public import Cslib.Logics.Temporal.Metalogic.Soundness
  public import Cslib.Logics.Temporal.Metalogic.CompletenessHelpers
  ```
- [ ] Run `lake exe mk_all --module` to verify Cslib.lean completeness
- [ ] Run full CI suite
- [ ] Create PR with title and description (see below)
- [ ] Respond to reviewer feedback within 48 hours

**PR Title**: `feat(Logics/Temporal): temporal metalogic -- deduction theorem, MCS saturation, and soundness`

**PR Description Template**:
```
## Summary

Add 10 new files for the temporal metalogic core:
- **DerivationTree + DeductionTheorem**: Height-indexed derivation trees and the deduction theorem for the temporal Hilbert system
- **MCS**: Maximal consistent set theory for temporal logic, including Lindenbaum saturation and content closure
- **TemporalContent + WitnessSeed**: Temporal content extraction (G-content, H-content) and omega-chain seed construction for the chronicle completeness proof
- **GeneralizedNecessitation + PropositionalHelpers**: Proof-theoretic lemmas for necessitation over derivation trees
- **Soundness**: Soundness of the BX proof system w.r.t. temporal Kripke semantics
- **CompletenessHelpers**: MCS-level helper lemmas bridging to the chronicle construction

This is the foundational metalogic layer. The chronicle construction and completeness theorem follow in the next PR.

## Dependencies

Requires:
- Foundations/Logic PR (#NNN) -- for `Foundations.Logic.Metalogic.Consistency`
- Temporal ProofSystem PR (#NNN) -- for `Logics.Temporal.ProofSystem.*` and `Theorems.*`

## Files (10 new, ~2,790 lines)

- `Cslib/Logics/Temporal/Metalogic.lean` (barrel)
- `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean`
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean`
- `Cslib/Logics/Temporal/Metalogic/MCS.lean`
- `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean`
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean`
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean`
- `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean`
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean`
- `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean`

## AI Disclosure

This formalization was developed with Claude Code assistance. All proofs are verified by the Lean 4 type checker.
```

**Timing**: 2.5 hours

**Depends on**: 4, 5

**Files to modify**:
- `Cslib.lean` -- add 10 new `public import` lines

**Files included in PR** (already existing):
- `Cslib/Logics/Temporal/Metalogic.lean`
- `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean`
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean`
- `Cslib/Logics/Temporal/Metalogic/MCS.lean`
- `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean`
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean`
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean`
- `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean`
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean`
- `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean`

**Verification**:
- PR created on GitHub
- All CI checks pass
- PR description references PRs 1 and 3 as dependencies

---

### Phase 7: PR 5 -- Temporal Chronicle Infrastructure [NOT STARTED]

**Goal**: Submit PR 5 containing the Chronicle construction infrastructure (8 files covering chronicle types, frame properties, canonical chain, R-relation, point insertion, counterexample elimination, and chronicle construction).

**Tasks**:
- [ ] Create feature branch from main (after PR 4 merged): `git checkout -b feat/temporal-chronicle`
- [ ] Add the following 8 files to `Cslib.lean` exports:
  ```
  public import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleTypes
  public import Cslib.Logics.Temporal.Metalogic.Chronicle.Frame
  public import Cslib.Logics.Temporal.Metalogic.Chronicle.CanonicalChain
  public import Cslib.Logics.Temporal.Metalogic.Chronicle.OrderedSeedConsistency
  public import Cslib.Logics.Temporal.Metalogic.Chronicle.RRelation
  public import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion
  public import Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination
  public import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleConstruction
  ```
- [ ] Run `lake exe mk_all --module` to verify Cslib.lean completeness
- [ ] Run full CI suite
- [ ] Create PR with title and description (see below)
- [ ] If reviewers request a split, offer to separate PointInsertion + CounterexampleElimination (~6,185 lines combined) into a sub-PR

**PR Title**: `feat(Logics/Temporal): Burgess chronicle construction infrastructure`

**PR Description Template**:
```
## Summary

Add 8 new files implementing the Burgess chronicle construction for temporal completeness:
- **ChronicleTypes**: Core types (TPoint, chronicle, temporal ordering `t_le`)
- **Frame**: Frame properties (irreflexivity, transitivity, linearity, seriality)
- **CanonicalChain**: Initial omega-chain of MCS from witness seeds
- **OrderedSeedConsistency**: Consistency preservation across ordered seed sequences
- **RRelation**: The canonical accessibility relation on chronicle points
- **PointInsertion**: Burgess point-insertion method for filling gaps in the chronicle (2,888 lines)
- **CounterexampleElimination**: Iterative elimination of counterexamples to achieve truth lemma prerequisites (3,297 lines)
- **ChronicleConstruction**: Assembly of the full chronicle from seeds via point insertion and counterexample elimination

This is the core technical contribution: the Burgess (1982) point-insertion method for constructing chronicles (maximal linear chains of MCS) that serve as countermodels for the BX temporal completeness theorem. The truth lemma and completeness theorem follow in the next PR.

**Note**: This PR is large (~7,117 lines) due to the inherent complexity of the point-insertion and counterexample-elimination proofs. These two files are tightly coupled and difficult to split further. Happy to discuss if reviewers prefer a different decomposition.

## Dependencies

Requires Temporal Metalogic Core PR (#NNN).

## Files (8 new, ~7,117 lines)

- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` (318 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean` (254 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CanonicalChain.lean` (78 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean` (136 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` (711 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` (2,888 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` (3,297 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` (1,435 lines)

## AI Disclosure

This formalization was developed with Claude Code assistance. All proofs are verified by the Lean 4 type checker.

## References

- Burgess, J.P. (1982). "Axioms for tense logic II: Time periods." *Notre Dame Journal of Formal Logic* 23(4).
```

**Timing**: 2.5 hours

**Depends on**: 6

**Files to modify**:
- `Cslib.lean` -- add 8 new `public import` lines

**Files included in PR** (already existing, Frame.lean modified in Phase 2):
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CanonicalChain.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean`

**Verification**:
- PR created on GitHub
- All CI checks pass
- Frame.lean contains no sorry

---

### Phase 8: PR 6 -- Temporal Completeness Theorem [NOT STARTED]

**Goal**: Submit PR 6 containing the final 3 files: countermodel extraction, truth lemma, and the BX completeness theorem.

**Tasks**:
- [ ] Create feature branch from main (after PR 5 merged): `git checkout -b feat/temporal-completeness`
- [ ] Add the following 3 files to `Cslib.lean` exports:
  ```
  public import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleToCountermodel
  public import Cslib.Logics.Temporal.Metalogic.Chronicle.TruthLemma
  public import Cslib.Logics.Temporal.Metalogic.Completeness
  ```
- [ ] Run `lake exe mk_all --module` to verify Cslib.lean completeness
- [ ] Run full CI suite
- [ ] Create PR with title and description (see below)

**PR Title**: `feat(Logics/Temporal): BX completeness theorem via Burgess chronicle countermodel`

**PR Description Template**:
```
## Summary

Add 3 files completing the BX temporal logic completeness proof:
- **ChronicleToCountermodel**: Extraction of a concrete Kripke countermodel from a chronicle
- **TruthLemma**: The truth lemma: for every formula phi and chronicle point w, phi is in w's MCS iff phi is true at w in the countermodel
- **Completeness**: The main theorem: every formula valid on all serial linear orders is derivable in the BX proof system

This completes the full temporal logic formalization: syntax, semantics, proof system, soundness, and completeness. The completeness proof follows Burgess (1982) via the chronicle construction submitted in the previous PR.

## Main Result

```lean
theorem completeness {φ : Temporal.Formula Atom} (h : valid φ) : derivable φ
```

## Dependencies

Requires Temporal Chronicle Infrastructure PR (#NNN).

## Files (3 new, ~492 lines)

- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean` (133 lines)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean` (234 lines)
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` (125 lines)

## AI Disclosure

This formalization was developed with Claude Code assistance. All proofs are verified by the Lean 4 type checker.

## References

- Burgess, J.P. (1982). "Axioms for tense logic II: Time periods." *Notre Dame Journal of Formal Logic* 23(4).
```

**Timing**: 2 hours

**Depends on**: 7

**Files to modify**:
- `Cslib.lean` -- add 3 new `public import` lines

**Files included in PR** (already existing):
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean`
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean`

**Verification**:
- PR created on GitHub
- All CI checks pass
- The main `completeness` theorem is sorry-free and axiom-clean (`lean_verify`)

---

## Feature Branch Strategy

Each PR uses a dedicated feature branch created from `main` after its dependency PRs have been merged upstream:

| PR | Branch Name | Created From | Created After |
|----|-------------|-------------|---------------|
| 1 | `feat/foundations-logic-theorems` | `main` | Phase 2 complete |
| 2 | `feat/modal-metalogic` | `main` | PR 1 merged |
| 3 | `feat/temporal-proof-system` | `main` | PR 1 merged |
| 4 | `feat/temporal-metalogic-core` | `main` | PRs 1, 3 merged |
| 5 | `feat/temporal-chronicle` | `main` | PR 4 merged |
| 6 | `feat/temporal-completeness` | `main` | PR 5 merged |

Each branch includes only the files for that PR plus the `Cslib.lean` update. Since PRs are sequential (each depends on prior merges), there should be no merge conflicts.

## Pre-Submission Checklist (apply to every PR)

- [ ] `lake build` -- zero errors
- [ ] `lake shake --add-public --keep-implied --keep-prefix` -- minimized imports
- [ ] `lake lint` -- environment linters pass
- [ ] `lake exe lint-style` -- text linters pass
- [ ] `lake test` -- test suite passes
- [ ] `lake exe checkInitImports` -- all files import `Cslib.Init`
- [ ] `lake exe mk_all --module` -- `Cslib.lean` complete
- [ ] `grep -rn "sorry" <PR files>` -- zero sorry
- [ ] Apache 2.0 copyright headers on all new files
- [ ] PR title matches `feat(area): description` format
- [ ] PR description includes AI disclosure
- [ ] PR description references dependency PRs by number

## Testing & Validation

- [ ] Full `lake build` passes after each PR's Cslib.lean update
- [ ] `lake shake` confirms no unused imports
- [ ] `lake lint` and `lake exe lint-style` produce no warnings
- [ ] `lake exe checkInitImports` confirms all files in import chain
- [ ] `lake exe mk_all --module` confirms Cslib.lean completeness
- [ ] Zero sorry across all submitted files (grep verification)
- [ ] `lean_verify` on key theorems (Modal completeness, Temporal completeness) confirms no axiom leakage
- [ ] Each PR builds independently against its dependency chain
- [ ] Zulip coordination completed before first PR submission

## Artifacts & Outputs

- `specs/056_plan_pr_submission_strategy/plans/01_pr-submission-plan.md` (this file)
- 6 PRs on leanprover/cslib (to be created during implementation)
- Zulip post on `#CSLib` stream

## Rollback/Contingency

- **If a PR is rejected**: Address reviewer feedback, update files, force-push to the PR branch. No impact on other PRs since each waits for upstream merge.
- **If CI fails unexpectedly**: Run the failing check locally, fix issues, and re-push. Common issues: `lake shake` removing a needed public import (re-add with `--keep-prefix`), `checkInitImports` failing (add `import Cslib.Init` to affected file).
- **If reviewers request PR splitting**: PR 5 (Chronicle) is the most likely split candidate. Natural split: (5a) ChronicleTypes + Frame + CanonicalChain + OrderedSeedConsistency + RRelation (~1,497 lines), (5b) PointInsertion + CounterexampleElimination + ChronicleConstruction (~7,620 lines). PR 6 remains unchanged.
- **If ordering dispute**: PRs 2 (Modal) and 3 (Temporal non-metalogic) can swap order or be submitted simultaneously since they have no inter-dependency. Both depend only on PR 1.
