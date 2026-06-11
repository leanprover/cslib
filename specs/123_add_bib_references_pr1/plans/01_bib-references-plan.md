# Implementation Plan: Add Bibliographic References for PR 1

- **Task**: 123 - Add bibliographic references for PR 1
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: Must work on `pr1/foundations-logic` branch
- **Research Inputs**: specs/123_add_bib_references_pr1/reports/01_bib-references-research.md
- **Artifacts**: plans/01_bib-references-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Add proper Mathlib-style bibliographic references to all PR 1 Lean files on the `pr1/foundations-logic` branch. This involves adding 4 missing entries to the root `references.bib`, replacing informal "CZ" abbreviations with proper `[ChagrovZakharyaschev1997]` citations across 14 Propositional logic files, fixing the Natural Deduction citation format, and adding `## References` sections to files that lack them. All changes are documentation-only -- no Lean code is modified.

### Research Integration

The research report (01_bib-references-research.md) provided a complete per-file mapping of current vs. target references, identified 4 missing bib entries (ChagrovZakharyaschev1997, Prawitz1965, TroelstraVanDalen1988, HughesCresswell1996), catalogued 14 files using the informal "CZ" abbreviation, and confirmed that Modal/Basic.lean and Modal/Cube.lean already have correct Blackburn2001 references.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly pertain to this documentation task.

## Goals & Non-Goals

**Goals**:
- Add 4 missing bibliography entries to `references.bib`
- Replace all informal "CZ" abbreviations with Mathlib-style `[ChagrovZakharyaschev1997]` citations
- Fix Natural Deduction citation format (dash bullets to star bullets, add BibKeys)
- Add `## References` sections to files that reference standard material but lack them
- Ensure all citations follow the CSLib convention: `* [Author, *Title*][BibKey]`

**Non-Goals**:
- Modifying any Lean code, proofs, or definitions
- Adding references to files on `main` that are not on the `pr1/foundations-logic` branch
- Adding references to files with only internal cross-references (ProofSystem/*, MCS, DeductionTheorem)
- Changing the Modal/Basic.lean or Modal/Cube.lean references (already correct)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Branch divergence -- `pr1/foundations-logic` may have changed since research | M | L | Check out branch fresh and verify file list before editing |
| Incorrect BibTeX entry data (typos in authors, ISBNs) | L | L | Cross-check against standard bibliography databases |
| Module docstring format varies across files | M | M | Read each file's existing docstring structure before editing; preserve existing formatting |
| Missing files -- some files may have been renamed or moved | M | L | Verify each file exists on branch before editing |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Add Missing BibTeX Entries [COMPLETED]

**Goal**: Add 4 new bibliography entries to the root `references.bib` file so that all BibKeys referenced in PR 1 files resolve correctly.

**Tasks**:
- [ ] Check out or confirm working on `pr1/foundations-logic` branch
- [ ] Read current `references.bib` to identify insertion points (alphabetical order)
- [ ] Add `ChagrovZakharyaschev1997` entry (Chagrov & Zakharyaschev, *Modal Logic*, Oxford Logic Guides 35, 1997)
- [ ] Add `Prawitz1965` entry (Prawitz, *Natural Deduction: A Proof-Theoretical Study*, Almqvist & Wiksell, 1965)
- [ ] Add `TroelstraVanDalen1988` entry (Troelstra & van Dalen, *Constructivism in Mathematics* Vol 1, North-Holland, 1988)
- [ ] Add `HughesCresswell1996` entry (Hughes & Cresswell, *A New Introduction to Modal Logic*, Routledge, 1996)
- [ ] Verify no duplicate keys exist

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `references.bib` -- Add 4 new @book entries in alphabetical order

**Verification**:
- All 4 BibKeys appear in `references.bib`
- Entries are alphabetically sorted among existing entries
- No duplicate keys

---

### Phase 2: Update Propositional Logic Files [NOT STARTED]

**Goal**: Replace all informal "CZ" references with proper Mathlib-style citations in the 14 Propositional logic files, and add a `## References` section to `Defs.lean` which currently has none.

**Tasks**:
- [ ] Update `Cslib/Logics/Propositional/Defs.lean` -- Add new `## References` section with `[ChagrovZakharyaschev1997]` Chapter 1
- [ ] Update `Cslib/Logics/Propositional/Semantics/Basic.lean` -- Replace `CZ Section 1.2, Definition 1.5` with proper citation format
- [ ] Update `Cslib/Logics/Propositional/Semantics/Kripke.lean` -- Replace `CZ Section 2.2, Proposition 2.1` with proper citation format
- [ ] Update `Cslib/Logics/Propositional/Metalogic/Soundness.lean` -- Replace `CZ Theorem 1.16` with proper citation
- [ ] Update `Cslib/Logics/Propositional/Metalogic/Completeness.lean` -- Replace `CZ Theorem 1.16, Section 5.1` with proper citation
- [ ] Update `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` -- Replace `CZ Theorem 2.43, Proposition 2.1` with proper citation
- [ ] Update `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` -- Replace `CZ Theorem 2.43` with proper citation
- [ ] Update `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` -- Replace `CZ Section 5.1, Theorem 2.43` with proper citation
- [ ] Update `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` -- Replace `CZ Theorem 2.43, Proposition 2.1` with proper citation
- [ ] Update `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` -- Replace `CZ Theorem 2.43` with proper citation
- [ ] Update `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` -- Replace `CZ Section 5.1` with proper citation
- [ ] Update `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- Fix dash-style to star-style bullets, add `[Prawitz1965]` and `[TroelstraVanDalen1988]` BibKeys

**Timing**: 1 hour

**Depends on**: 1 (BibKeys must exist in references.bib before being referenced)

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` -- Add `## References` section
- `Cslib/Logics/Propositional/Semantics/Basic.lean` -- Replace CZ citation
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` -- Replace CZ citation
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` -- Replace CZ citation
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` -- Replace CZ citation
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` -- Replace CZ citation
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` -- Replace CZ citation
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` -- Replace CZ citation
- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` -- Replace CZ citation
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` -- Replace CZ citation
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` -- Replace CZ citation
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- Fix format and add BibKeys

**Citation format for CZ files**:
Replace patterns like `* CZ Theorem 1.16` or `* CZ Section 2.2` with:
```
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16
```

**Citation format for ND/Basic.lean**:
Replace:
```
- Dag Prawitz, *Natural Deduction: a proof-theoretical study*.
- Troelstra & van Dalen's *Constructivism in Mathematics*
```
With:
```
* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
* [A. S. Troelstra, D. van Dalen, *Constructivism in Mathematics*][TroelstraVanDalen1988]
```

**Verification**:
- `grep -r "CZ " Cslib/Logics/Propositional/` returns no matches (all CZ abbreviations replaced)
- All modified files use `* [Author, *Title*][BibKey]` format
- No dash-style bullets remain in reference sections

---

### Phase 3: Update Modal Logic and Foundation Files [NOT STARTED]

**Goal**: Add missing `## References` sections to Modal files that lack them, and confirm existing correct references are untouched.

**Tasks**:
- [ ] Update `Cslib/Logics/Modal/Denotation.lean` -- Add `## References` section with `[Blackburn2001]`
- [ ] Update `Cslib/Logics/Modal/LogicalEquivalence.lean` -- Add `## References` section with `[Blackburn2001]`
- [ ] Verify `Cslib/Logics/Modal/Basic.lean` already has correct `[Blackburn2001]` (no change needed)
- [ ] Verify `Cslib/Logics/Modal/Cube.lean` already has correct `[Blackburn2001]` (no change needed)

**Timing**: 20 minutes

**Depends on**: 1 (Blackburn2001 already exists in references.bib, but branch checkout from Phase 1 is needed)

**Files to modify**:
- `Cslib/Logics/Modal/Denotation.lean` -- Add `## References` section
- `Cslib/Logics/Modal/LogicalEquivalence.lean` -- Add `## References` section

**Verification**:
- `Denotation.lean` and `LogicalEquivalence.lean` each have a `## References` section with proper `[Blackburn2001]` citation
- `Basic.lean` and `Cube.lean` remain unchanged

---

### Phase 4: Verification and Consistency Check [NOT STARTED]

**Goal**: Verify all references are properly formatted, all BibKeys resolve, and no regressions exist.

**Tasks**:
- [ ] Run `grep -r "CZ " Cslib/Logics/Propositional/` to confirm no informal CZ references remain
- [ ] Run `grep -rn "## References" Cslib/Logics/Propositional/ Cslib/Logics/Modal/` to list all reference sections
- [ ] For each BibKey used in Lean files, verify it exists in `references.bib`
- [ ] Verify bullet format consistency: all references use `*` bullets (not `-`)
- [ ] Verify all Lean files still parse correctly (documentation changes should not affect Lean compilation, but confirm no unclosed comments or syntax issues)
- [ ] Run `lake build` to ensure no Lean compilation errors introduced

**Timing**: 20 minutes

**Depends on**: 2, 3

**Files to modify**:
- None (verification only)

**Verification**:
- Zero matches for informal CZ references
- All BibKeys in Lean files have corresponding entries in `references.bib`
- `lake build` succeeds with no new errors

## Testing & Validation

- [ ] `grep -r "CZ " Cslib/Logics/Propositional/` returns empty (no informal CZ references)
- [ ] `grep -rn "\[ChagrovZakharyaschev1997\]" Cslib/Logics/Propositional/` matches all expected files
- [ ] `grep -rn "\[Prawitz1965\]" Cslib/Logics/Propositional/NaturalDeduction/` matches Basic.lean
- [ ] `grep -rn "\[TroelstraVanDalen1988\]" Cslib/Logics/Propositional/NaturalDeduction/` matches Basic.lean
- [ ] `grep -rn "\[Blackburn2001\]" Cslib/Logics/Modal/` matches Basic, Cube, Denotation, LogicalEquivalence
- [ ] All `## References` sections use `*` bullet format
- [ ] `lake build` compiles successfully

## Artifacts & Outputs

- `specs/123_add_bib_references_pr1/plans/01_bib-references-plan.md` (this file)
- `references.bib` (4 new entries added)
- ~16 modified `.lean` files (documentation-only changes)

## Rollback/Contingency

Since all changes are documentation-only (module docstrings and bib entries), rollback is straightforward:
- `git checkout pr1/foundations-logic -- references.bib` to restore original bib file
- `git checkout pr1/foundations-logic -- Cslib/Logics/Propositional/ Cslib/Logics/Modal/` to restore original docstrings
- No code logic is affected, so there is zero risk of breaking proofs or compilation
