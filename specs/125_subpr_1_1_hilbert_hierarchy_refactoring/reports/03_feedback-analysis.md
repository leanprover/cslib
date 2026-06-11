# Research Report: Reviewer Feedback Analysis for Sub-PR 1.1

- **Task**: 125 - Sub-PR 1.1: 3-tier Hilbert hierarchy refactoring
- **Started**: 2026-06-11T23:30:00Z
- **Completed**: 2026-06-12T00:30:00Z
- **Effort**: ~1 hour
- **Dependencies**: Task 124 (completed), Round 1 research (report 02)
- **Sources/Inputs**:
  - PR #633 reviewer feedback (Alexandre, Chris, Ching-Tsun)
  - `specs/125_subpr_1_1_hilbert_hierarchy_refactoring/reports/02_research-report.md`
  - Upstream CONTRIBUTING.md (AI policy, PR titles, CI requirements)
  - `git diff upstream/main..main` for all candidate files
  - Upstream file inventory via `git ls-tree upstream/main`
- **Artifacts**:
  - `specs/125_subpr_1_1_hilbert_hierarchy_refactoring/reports/03_feedback-analysis.md` (this file)
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The current sub-PR 1.1 scope (21 files, ~3,887 insertions) is **nearly 8x the 500-line limit** that Chris specified for new contributors, especially when AI is involved. It must be significantly reduced.
- The optimal first PR is a **Proposition type refactoring** that introduces `Connectives.lean` (98 new lines), refactors `Defs.lean` and `NaturalDeduction/Basic.lean` to use `bot/imp` primitives, totaling ~302 diff lines across 6 files (1 new, 5 modified). This is well under the 500-line limit.
- The original 21-file sub-PR 1.1 should be re-decomposed into 4-5 smaller PRs that build on each other sequentially.
- The Zulip topic should be created **before** submitting the first PR, presenting the overall plan and requesting design feedback on the Lukasiewicz convention.
- Each reviewer's concern maps to specific actions: Chris gets small PRs, Ching-Tsun gets references, Alexandre gets the Zulip coordination.

## Reviewer Feedback Analysis

### Alexandre

**What he said**: Don't close PRs, push new commits; mark as draft; create a Zulip topic to present the overall plan.

**What this means**:
- PR #633 should remain open as a reference/working draft. New sub-PRs are opened separately.
- The Zulip topic is not optional -- it is the mechanism for "coordinating major developments" per CONTRIBUTING.md. The Logics section explicitly welcomes modal and temporal logic.
- Alexandre will start reviewing soon, so timing matters.

**Recommended action**: Create Zulip topic FIRST, before submitting the first sub-PR. This demonstrates awareness of the contribution model and gives reviewers context for what's coming.

### Chris

**What he said**: PR #633 is too large. New contributors, especially with AI involvement, should keep PRs under 500 lines. Leave PR #633 open for reference, extract smaller PRs.

**What this means**:
- The 500-line limit likely refers to the GitHub diff stat (insertions + deletions).
- "Especially with AI involvement" signals heightened scrutiny. Every line will be inspected.
- This is about building trust incrementally. The first PR establishes a baseline for review quality.

**Quantitative analysis of current sub-PR 1.1**:
- 17 new files: 3,570 insertions
- 4 modified files: 317 insertions, 109 deletions
- Total diff: **3,887 insertions + 109 deletions = 3,996 diff lines**
- This is nearly **8x** the stated limit.

**Recommended action**: Reduce the first PR to ~300 diff lines. Build subsequent PRs as a chain.

### Ching-Tsun

**What he said**: Point out exactly where each reference is used in the code. Read the CONTRIBUTING.md, especially the AI policy.

**What this means**:
- References are not decorative -- they must be tied to specific definitions and design decisions.
- The AI policy requires explicit disclosure in the PR description.
- CONTRIBUTING.md says "When formalising a concept that is explained in a published resource, please reference the resource in your documentation."

**For the first PR specifically**:
- The Lukasiewicz convention (bot + imp as primitives, derived and/or/neg/top) is a well-established approach in mathematical logic. The relevant reference is Chagrov & Zakharyaschev, *Modal Logic* (1997), Chapter 1.
- This reference is NOT in upstream's `references.bib` but IS in our local copy.
- The reference should be added to `Defs.lean`'s module docstring AND to `references.bib`.
- The `NaturalDeduction/Basic.lean` changes are a consequence of the Proposition refactor (removing conjunction/disjunction as primitives), not independently motivated by literature. The existing Prawitz and Troelstra & van Dalen references remain appropriate.

## Scope Assessment

### Why Sub-PR 1.1 at 21 Files Is the Wrong Scope

The 21-file sub-PR 1.1 fails every criterion:

| Criterion | Limit | Sub-PR 1.1 | Status |
|-----------|-------|------------|--------|
| Diff lines | <500 | ~3,996 | FAIL (8x over) |
| File count | reasonable | 21 (17 new) | FAIL |
| New contributor trust | conservative | massive new codebase | FAIL |
| AI involvement factor | extra conservative | yes | FAIL |

### Why a ~300-Line First PR Is Correct

The recommended first PR (Proposition refactor) satisfies all criteria:

| Criterion | Limit | Recommended PR | Status |
|-----------|-------|----------------|--------|
| Diff lines | <500 | ~302 | PASS |
| File count | reasonable | 6 (1 new, 5 modified) | PASS |
| Modifies existing code | shows engagement | yes (Defs.lean, NatDeduction) | PASS |
| Design decision surface | reviewable | 1 key decision (Lukasiewicz) | PASS |
| Literature reference | required | Chagrov & Zakharyaschev | PASS |
| AI disclosure | required | in PR description | PASS |

### Key Insight: ProofSystem.lean Does Not Depend on Defs.lean

The import chain analysis reveals that the foundations hierarchy and the Proposition refactor are **independent dependency chains**:

```
Chain A (Proposition refactor):
  Connectives.lean -> Defs.lean -> NaturalDeduction/Basic.lean

Chain B (Hierarchy interfaces):
  Connectives.lean -> Axioms.lean -> ProofSystem.lean
```

Both chains start from `Connectives.lean` but otherwise have no mutual dependencies. This means they can be submitted as separate PRs. The first PR introduces `Connectives.lean` and applies Chain A; subsequent PRs add Chain B.

## Alternative Decomposition Options

### Recommended: 5-PR Chain (Replacing Single Sub-PR 1.1)

**PR 1.1a: "refactor: Proposition type to Lukasiewicz convention"** (~302 diff lines)

| File | Action | Lines |
|------|--------|-------|
| `Cslib/Foundations/Logic/Connectives.lean` | NEW | 98 |
| `Cslib/Logics/Propositional/Defs.lean` | MODIFY | +50/-35 |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | MODIFY | +31/-69 |
| `Cslib/Foundations/Logic/InferenceSystem.lean` | MODIFY | +3/-3 |
| `references.bib` | MODIFY | +10 |
| `Cslib.lean` | MODIFY | +1 |

Narrative: Refactors Proposition to use `bot`/`imp` as primitives with derived connectives following the Lukasiewicz convention. Introduces connective typeclasses for cross-logic reuse. Updates NaturalDeduction to match. References: Chagrov & Zakharyaschev (1997), Ch. 1.

**PR 1.1b: "feat: polymorphic axiom definitions"** (~300 diff lines)

| File | Action | Lines |
|------|--------|-------|
| `Cslib/Foundations/Logic/Axioms.lean` | NEW | 298 |
| `Cslib.lean` | MODIFY | +1 |

Narrative: Defines axiom formulas (ImplyK, ImplyS, EFQ, Peirce, modal K/T/4/B/5/D, temporal BX1-BX13) as polymorphic abbreviations over connective typeclasses. Pure definitions, no proofs.

**PR 1.1c: "feat: Hilbert proof system typeclass hierarchy"** (~490 diff lines)

| File | Action | Lines |
|------|--------|-------|
| `Cslib/Foundations/Logic/ProofSystem.lean` | NEW | 486 |
| `Cslib.lean` | MODIFY | +1 |

Narrative: Defines the 3-tier propositional hierarchy (MinimalHilbert, IntuitionisticHilbert, ClassicalHilbert), modal extensions (K through S5 and D-family), temporal BX system, and bimodal TM system. Pure interface -- concrete instances are future work.

Note: At 486 lines this is close to the 500-line limit. Since it is a single new file of well-documented typeclass definitions with no complex proofs, this should be acceptable. If reviewers object, it could be split into propositional-only (~100 lines) and modal/temporal (~386 lines).

**PR 1.1d: "feat: propositional Hilbert instances and derivation trees"** (~430 diff lines)

| File | Action | Lines |
|------|--------|-------|
| `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` | NEW | 106 |
| `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` | NEW | 163 |
| `Cslib/Logics/Propositional/ProofSystem/Instances.lean` | NEW | 90 |
| `Cslib/Foundations/Data/ListHelpers.lean` | NEW | 74 |
| `Cslib.lean` | MODIFY | +4 |

Narrative: Concrete propositional Hilbert system: axiom inductive, derivation trees, instances for HilbertCl/HilbertInt/HilbertMin.

**PR 1.1e: "feat: theorem stratification and metalogic"** (~remaining)

| File | Action | Lines |
|------|--------|-------|
| `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` | NEW | 311 |
| `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` | NEW | 539 |
| `Cslib/Foundations/Logic/Theorems/BigConj.lean` | NEW | 142 |
| `Cslib/Foundations/Logic/Theorems/Combinators.lean` | NEW | 339 |
| `Cslib/Foundations/Logic/Theorems.lean` | NEW | ~45 (reduced) |
| `Cslib/Foundations/Logic/Metalogic/Consistency.lean` | NEW | 278 |
| `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` | NEW | 120 |
| `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` | NEW | 217 |
| `Cslib/Logics/Propositional/Metalogic/MCS.lean` | NEW | 161 |
| `Cslib.lean` | MODIFY | +9 |

Note: At ~2,150 lines this exceeds 500. It should be split further, perhaps into:
- 1.1e: Theorem files only (Core + Connectives + BigConj + Combinators + barrel = ~1,376)
- 1.1f: Metalogic files (Consistency + DeductionHelpers + DeductionTheorem + MCS = ~776)

Each of those still exceeds 500 lines. The theorem and metalogic files may need even finer splitting, but these are substantive mathematical content that benefits from review context -- submitting Core.lean alone (311 lines) without the Connectives theorems it connects to would lose review coherence. This is a reasonable discussion point for the Zulip topic.

### Files Excluded from All Sub-PR 1.1 Variants

| File | Reason | Belongs to |
|------|--------|------------|
| `Theorems/Temporal/FrameConditions.lean` | Only imported by Temporal/Bimodal files | Sub-PR 1.5+ |
| `Theorems/Modal/Basic.lean` | Modal-specific | Sub-PR 1.5 |
| `Theorems/Modal/S5.lean` | Modal-specific | Sub-PR 1.5 |

## PR Presentation Strategy

### Title Format

Per CONTRIBUTING.md, titles must begin with one of: `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`.

Recommended title for the first PR:
```
refactor: Proposition type to Lukasiewicz convention
```

This uses `refactor` because it changes the internal structure of an existing type without adding new mathematical content. Alternative: `feat` if reviewers view the connective typeclasses as new functionality.

### AI Disclosure

Per CONTRIBUTING.md and Mathlib policy, the PR description must disclose AI usage. Recommended language:

> **AI Disclosure**: This PR was developed with assistance from Claude (Anthropic). The AI was used for: exploring Mathlib API compatibility, drafting typeclass definitions, and generating proof cases. All mathematical design decisions (Lukasiewicz convention, derived connective definitions, NaturalDeduction refactoring) were made by the human author. The code was manually reviewed and verified with `lake build`.

### PR Description Structure

```markdown
## Summary

Refactors `Proposition` to use `bot` (falsum) and `imp` (implication) as the only
primitive constructors, following the Lukasiewicz convention. Conjunction, disjunction,
negation, and verum are defined as abbreviations.

Introduces `Connectives.lean` with shared connective typeclasses (`HasBot`, `HasImp`,
etc.) that enable polymorphic axiom definitions across propositional, modal, temporal,
and bimodal logics.

Updates `NaturalDeduction/Basic.lean` to replace the 8 primitive rules (andI, andE1, andE2,
orI1, orI2, orE, implI, implE) with 3 (impI, impE, botE). This resolves the open design
question noted in the existing implementation notes about whether EFQ should be a rule or
an axiom.

**References**: Chagrov & Zakharyaschev, *Modal Logic* (1997), Chapter 1.

## Context

This is the first in a series of PRs building a 3-tier Hilbert proof system hierarchy
for propositional, modal, temporal, and bimodal logics. The full plan is described in
[Zulip topic link]. PR #633 contains the complete development for reference.

## Test plan

- [ ] `lake build` passes
- [ ] `lake test` passes
- [ ] `lake lint` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe mk_all --module --check` passes
- [ ] `lake shake` passes
- [ ] No `sorry` in modified files

AI Disclosure: [see above]
```

### Linking Strategy

- PR #633: Leave open, mark as draft with a note: "Extracting as a series of smaller PRs. See [Zulip topic]."
- Each sub-PR references the Zulip topic and PR #633 for full context.
- Sub-PRs reference their dependencies (e.g., "Depends on PR #XXX").

### Zulip Topic Strategy

**Where**: CSLib channel (or a dedicated "CSLib > Logics" subtopic if one exists). The CONTRIBUTING.md links to `https://leanprover.zulipchat.com/`.

**Title**: "Propositional/Modal/Temporal logic hierarchy: development plan"

**Content structure**:

1. **Introduction**: Brief background -- formalizing propositional, modal (K through S5), temporal (BX), and bimodal (TM) logics with reusable infrastructure.

2. **Design approach**: The 4-layer architecture:
   - Connective typeclasses (HasBot, HasImp, HasBox, etc.)
   - Polymorphic axiom definitions
   - 3-tier Hilbert hierarchy (Minimal -> Intuitionistic -> Classical -> Modal -> Temporal)
   - Concrete instantiation per logic

3. **Reuse story**: How the same axiom definitions and theorem proofs are shared across all 4 logic types. This aligns with CSLib's "reuse" design principle.

4. **PR plan**: List the planned sub-PRs with estimated sizes.

5. **Request for feedback**: Specifically ask about:
   - Whether the Lukasiewicz convention (bot+imp primitives) is the right design choice
   - Whether the connective typeclass approach aligns with CSLib's vision
   - Whether the PR decomposition is reasonable
   - Any existing work in CSLib that this should coordinate with

**Timing**: Post the Zulip topic, wait 1-2 days for initial reactions, then submit the first PR.

## Recommendations

### R1: Submit a ~300-Line First PR (Priority: Critical)

The recommended first PR is the Proposition type refactoring (PR 1.1a above). It touches existing upstream code, introduces one new file, addresses a documented design question, and stays well under the 500-line limit.

### R2: Create the Zulip Topic Before the First PR (Priority: Critical)

Per CONTRIBUTING.md and Alexandre's advice, coordinate major developments on Zulip. The topic should present the overall plan and solicit design feedback. This builds goodwill and may surface concerns early.

### R3: Add the Chagrov Reference (Priority: High)

Include the `ChagrovZakharyaschev1997` entry in `references.bib` and cite it in `Defs.lean`'s module docstring. This directly addresses Ching-Tsun's concern and follows CONTRIBUTING.md documentation requirements.

### R4: Re-Decompose Sub-PR 1.1 into 5+ Smaller PRs (Priority: High)

The original 21-file scope must be split into a chain of 5+ PRs each under 500 lines. The chain is: Proposition refactor -> Axiom definitions -> Hierarchy typeclasses -> Propositional instances -> Theorems and metalogic.

### R5: Include AI Disclosure in Every PR (Priority: High)

Per CONTRIBUTING.md and Mathlib policy, each PR description must disclose AI usage with specifics about what the AI was used for and what decisions were made by the human.

### R6: Address the NaturalDeduction Design Question (Priority: Medium)

The upstream `NaturalDeduction/Basic.lean` has an implementation note about an ongoing Zulip discussion on whether EFQ should be a rule or an axiom. Our refactoring resolves this by making `botE` a primitive rule. The PR description should explicitly reference this discussion and explain the design choice.

### R7: Exclude FrameConditions.lean from Foundation PRs (Priority: Medium)

Round 1 research included `Theorems/Temporal/FrameConditions.lean` in the scope. This file is only imported by Temporal and Bimodal files, not by any propositional file. It belongs in a later temporal-specific PR.

## Risks and Mitigations

### Risk 1: Lukasiewicz Convention Rejected (MEDIUM)

- **Risk**: Reviewers may prefer keeping `and`/`or`/`impl` as primitives (the current upstream design). The Lukasiewicz convention is standard in algebraic logic but less common in proof-theory-oriented formalizations.
- **Mitigation**: Present the rationale on Zulip before submitting. The key argument is reusability: with bot+imp as primitives, the Proposition type shares structure with Modal, Temporal, and Bimodal formula types, enabling code reuse via the connective typeclasses. The existing Zulip discussion about EFQ-as-rule-vs-axiom is also relevant.

### Risk 2: NaturalDeduction/Basic.lean Changes Contentious (MEDIUM)

- **Risk**: Removing 8 primitive rules and replacing with 3 is a significant structural change to existing upstream code authored by Thomas Waring. Reviewers may want the original author's input.
- **Mitigation**: The change is mathematically equivalent (conjunction/disjunction rules are derivable from bot+imp+botE). The PR description should be explicit about this equivalence. The existing implementation notes reference an ongoing discussion, so this is expected territory.

### Risk 3: Connective Typeclasses Seen as Over-Engineering (LOW)

- **Risk**: Reviewers may question why `HasBot`, `HasImp`, `HasBox` etc. need their own typeclasses for what could be direct type definitions.
- **Mitigation**: The typeclasses are the mechanism that enables polymorphic axiom definitions. Without them, axiom formulas would need to be defined separately for each logic type. This is the reuse infrastructure that CSLib values.

### Risk 4: Sequential PR Chain Creates Review Bottleneck (LOW)

- **Risk**: If each PR waits for the previous one to be merged, the full foundation layer could take months.
- **Mitigation**: Each PR is self-contained and can be reviewed independently. Stacking PRs (each targeting the previous PR's branch) is common in large projects. Alternatively, submit them against a shared integration branch.

## Appendix: Complete First PR File Manifest

### New Files (1)

| File | Lines | Description |
|------|-------|-------------|
| `Cslib/Foundations/Logic/Connectives.lean` | 98 | Connective typeclasses: HasBot, HasImp, HasBox, HasUntil, HasSince, bundle classes, LukasiewiczDerived |

### Modified Files (5)

| File | Insertions | Deletions | Description |
|------|-----------|-----------|-------------|
| `Cslib/Logics/Propositional/Defs.lean` | ~50 | ~35 | Proposition to bot/imp; derived connectives; PropositionalConnectives instance; remove Bot/Inhabited constraints |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | ~31 | ~69 | Remove and/or rules; add botE; rename implI/E to impI/E; update weak/subs/substAtom/cut |
| `Cslib/Foundations/Logic/InferenceSystem.lean` | 3 | 3 | Import visibility; module docstring |
| `references.bib` | ~10 | 0 | Add ChagrovZakharyaschev1997 |
| `Cslib.lean` | 1 | 0 | Add Connectives import |

### Total Diff

- Insertions: ~193
- Deletions: ~107
- Total diff lines: ~300
