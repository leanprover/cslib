# Implementation Plan: PR 1 Citation Conformance

- **Task**: 136 - PR 1 citation conformance
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/136_pr1_citation_conformance/reports/01_citation-conformance.md
- **Artifacts**: plans/01_citation-conformance-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Revise citations across 5 files and references.bib on the `pr1/foundations-logic` branch to conform to the canonical citation conventions in `.claude/context/standards/citation-conventions.md`. The research audit found 21 of 26 files already conformant. Remaining work: remove one orphaned bib entry, add one missing bib entry, split one compound citation bullet into two proper BibKey citations, and convert 8 backtick-wrapped internal cross-references to bare paths across 3 files. Documentation-only changes -- no Lean code modifications.

### Research Integration

The research report (`reports/01_citation-conformance.md`) provides a complete per-file audit of all 26 Propositional and Modal files. Key findings:
- 21/26 files fully conformant
- 5 files need edits plus references.bib
- 12 total edits needed: 1 orphaned bib removal, 1 bib addition, 1 citation split, 8 backtick-to-bare conversions, 1 inline prose conversion

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances citation hygiene for PR 1 (Propositional and Modal modules), supporting the broader porting effort described in ROADMAP.md.

## Goals & Non-Goals

**Goals**:
- All 26 PR 1 files pass citation convention audit
- references.bib contains no orphaned entries and all required entries
- Internal cross-references use bare paths (no backticks)
- Each external citation has its own properly formatted BibKey bullet

**Non-Goals**:
- Modifying any Lean source code (proofs, definitions, imports)
- Auditing files outside the PR 1 scope (Temporal, Bimodal, Foundations)
- Reformatting conformant citations that already pass the standard

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Edit breaks Lean module docstring syntax | M | L | Verify `/-!` and `-/` delimiters preserved; check with lean_diagnostic_messages |
| Alphabetical ordering error in references.bib | L | L | Research report specifies exact insertion point (after Sangiorgi2011, before ShepherdsonSturgis1963) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Update references.bib and NaturalDeduction/Basic.lean [NOT STARTED]

**Goal**: Fix the bib-level issues (orphaned entry removal, new entry addition) and the citation split in Basic.lean. These must come first because Phase 2 files may reference the new BibKey.

**Tasks**:
- [ ] Checkout `pr1/foundations-logic` branch
- [ ] Remove the orphaned `@book{HughesCresswell1996, ...}` entry from `references.bib`
- [ ] Add `@book{SorensenUrzyczyn2006, ...}` entry to `references.bib` in alphabetical order (after `Sangiorgi2011`, before `ShepherdsonSturgis1963`)
- [ ] In `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`, split the Troelstra bullet: replace the compound citation with two separate bullets -- TroelstraVanDalen1988 (Section 10.4) and SorensenUrzyczyn2006 (Section 2.2)

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `references.bib` -- remove HughesCresswell1996, add SorensenUrzyczyn2006
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- split compound citation into two BibKey bullets

**Verification**:
- `grep -c HughesCresswell1996 references.bib` returns 0
- `grep -c SorensenUrzyczyn2006 references.bib` returns 1
- `grep SorensenUrzyczyn2006 Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` returns a match

---

### Phase 2: Convert Backtick Cross-References [NOT STARTED]

**Goal**: Convert all 8 backtick-wrapped internal cross-reference paths to bare paths across 3 NaturalDeduction files.

**Tasks**:
- [ ] In `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean`, convert 2 backtick-wrapped cross-refs to bare paths
- [ ] In `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`, convert 3 backtick-wrapped cross-refs to bare paths
- [ ] In `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean`, convert 3 backtick-wrapped cross-refs to bare paths

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` -- 2 backtick removals
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` -- 3 backtick removals
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` -- 3 backtick removals

**Verification**:
- `git grep -c '^\* \x60Cslib/' -- '*.lean'` returns 0 (no remaining backtick cross-refs in scope)
- All 26 files pass a final conformance spot-check: no `-` bullets in reference sections, no backtick cross-refs, all BibKeys resolve in references.bib

## Testing & Validation

- [ ] No remaining backtick-wrapped internal cross-references across all 26 PR 1 files
- [ ] No orphaned bib entries (every entry in references.bib is cited by at least one file)
- [ ] SorensenUrzyczyn2006 entry present in references.bib and cited in Basic.lean
- [ ] All `*` bullet format preserved (no `-` bullets in reference sections)
- [ ] Lean module docstring syntax intact (no `/-!` / `-/` breakage)

## Artifacts & Outputs

- `specs/136_pr1_citation_conformance/plans/01_citation-conformance-plan.md` (this plan)
- `specs/136_pr1_citation_conformance/summaries/01_citation-conformance-summary.md` (post-implementation)

## Rollback/Contingency

All changes are documentation-only edits to Lean module docstrings and references.bib. Revert with `git checkout pr1/foundations-logic -- references.bib Cslib/Logics/Propositional/NaturalDeduction/`.
