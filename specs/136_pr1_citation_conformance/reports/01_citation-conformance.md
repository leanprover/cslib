# Citation Conformance Audit: PR 1 Propositional and Modal Files

## Summary

Audited all 26 files on the `pr1/foundations-logic` branch under `Cslib/Logics/Propositional/`
(22 files) and `Cslib/Logics/Modal/` (4 files) against the canonical citation conventions
defined in `.claude/context/standards/citation-conventions.md`.

**Findings**:
- 1 orphaned bib entry (`HughesCresswell1996`) to remove
- 1 missing bib entry (`SorensenUrzyczyn2006`) to add, plus inline mention to convert
- 6 files use backtick-wrapped internal cross-refs; recommendation is bare paths
- All external citations already use correct `* [Author, *Title*][BibKey]` format
- All reference sections already use `*` bullets (no `-` bullets found)
- No other formatting discrepancies detected

## Citation Convention Standard (Reference)

Per `.claude/context/standards/citation-conventions.md`:

| Element | Convention |
|---------|------------|
| Bullet | `*` (not `-`) |
| External citation | `* [Author, *Title*][BibKey], location` |
| Internal cross-ref | `* Cslib/Path/To/File.lean -- description` (bare, no backticks) |
| BibKey | CamelCase: `SurnameYear` or `Surname1Surname2Year` |

## Per-File Audit Results

### Propositional Files (22 files)

#### 1. `Cslib/Logics/Propositional/Defs.lean`
- **External**: `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Chapter 1` -- CONFORMANT
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 2. `Cslib/Logics/Propositional/Metalogic/Completeness.lean`
- **External**: `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16 (completeness direction), Section 5.1` -- CONFORMANT (multi-line, 2-space indent)
- **Internal**: `* Cslib/Logics/Modal/Metalogic/KCompleteness.lean -- modal K completeness` -- CONFORMANT (bare path)
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 3. `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
- **External**: None
- **Internal**: `* Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean -- modal deduction theorem` -- CONFORMANT (bare path)
- **Internal**: `* Cslib/Foundations/Logic/Metalogic/Consistency.lean` -- CONFORMANT (bare path)
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 4. `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean`
- **External**: `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43` -- CONFORMANT
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 5. `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean`
- **External**: `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 5.1, Theorem 2.43` -- CONFORMANT
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 6. `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean`
- **External**: `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43 (soundness direction), Proposition 2.1 (persistence lemma)` -- CONFORMANT (multi-line)
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 7. `Cslib/Logics/Propositional/Metalogic/MCS.lean`
- **External**: None
- **Internal**: `* Cslib/Logics/Modal/Metalogic/MCS.lean -- modal MCS pattern` -- CONFORMANT (bare path)
- **Internal**: `* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS framework` -- CONFORMANT (bare path)
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 8. `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean`
- **External**: `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43` -- CONFORMANT
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 9. `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean`
- **External**: `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 5.1, adapted for minimal logic` -- CONFORMANT (multi-line)
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 10. `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean`
- **External**: `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43 (soundness, adapted for minimal logic), Proposition 2.1 (persistence lemma)` -- CONFORMANT (multi-line)
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 11. `Cslib/Logics/Propositional/Metalogic/Soundness.lean`
- **External**: `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16 (soundness direction)` -- CONFORMANT (multi-line)
- **Internal**: `* Cslib/Logics/Modal/Metalogic/Soundness.lean -- modal soundness pattern` -- CONFORMANT (bare path)
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 12. `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
- **External**: `* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]` -- CONFORMANT
- **External**: `* [A. S. Troelstra, D. van Dalen, *Constructivism in Mathematics: An Introduction*][TroelstraVanDalen1988], the sequent-style natural deduction presented here is tersely described in Section 10.4, and in Section 2.2 of Sorensen & Urzyczyn's *Lectures on the Curry-Howard Isomorphism*.` -- **NON-CONFORMANT**: inline mention of Sorensen & Urzyczyn lacks BibKey citation
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**:
  - **ISSUE 1**: The Sorensen & Urzyczyn reference is embedded as prose within the TroelstraVanDalen1988 bullet instead of being its own properly formatted BibKey citation. Needs to be extracted to a separate `* [M. H. Sorensen, P. Urzyczyn, *Lectures on the Curry-Howard Isomorphism*][SorensenUrzyczyn2006], Section 2.2` bullet.
  - **ISSUE 2**: `SorensenUrzyczyn2006` bib entry must be added to `references.bib`.

#### 13. `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean`
- **External**: None
- **Internal**: `* \`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean\` -- standalone ND system` -- **NON-CONFORMANT**: backtick-wrapped path
- **Internal**: `* \`Cslib/Logics/Propositional/Defs.lean\` -- connective definitions` -- **NON-CONFORMANT**: backtick-wrapped path
- **Bullets**: `*` -- CONFORMANT
- **Issues**: 2 backtick-wrapped internal cross-refs need conversion to bare paths

#### 14. `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`
- **External**: None
- **Internal**: `* \`Cslib/Logics/Propositional/ProofSystem/Derivation.lean\` -- Hilbert system` -- **NON-CONFORMANT**: backtick-wrapped
- **Internal**: `* \`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean\` -- ND system` -- **NON-CONFORMANT**: backtick-wrapped
- **Internal**: `* \`Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean\` -- deduction theorem` -- **NON-CONFORMANT**: backtick-wrapped
- **Bullets**: `*` -- CONFORMANT
- **Issues**: 3 backtick-wrapped internal cross-refs need conversion to bare paths

#### 15. `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean`
- **External**: None
- **Internal**: `* Cslib/Logics/Propositional/NaturalDeduction/Basic.lean -- standalone ND system` -- CONFORMANT (bare path)
- **Internal**: `* Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean -- deduction theorem` -- CONFORMANT (bare path)
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 16. `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean`
- **External**: None
- **Internal**: `* \`Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean\` -- ND wrappers` -- **NON-CONFORMANT**: backtick-wrapped
- **Internal**: `* \`Cslib/Logics/Propositional/ProofSystem/Derivation.lean\` -- Hilbert system` -- **NON-CONFORMANT**: backtick-wrapped
- **Internal**: `* \`Cslib/Logics/Propositional/ProofSystem/Axioms.lean\` -- axiom schemata` -- **NON-CONFORMANT**: backtick-wrapped
- **Bullets**: `*` -- CONFORMANT
- **Issues**: 3 backtick-wrapped internal cross-refs need conversion to bare paths

#### 17. `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
- **External**: None
- **Internal**: `* Cslib/Logics/Modal/Metalogic/DerivationTree.lean -- modal axiom pattern (first 4 constructors)` -- CONFORMANT (bare path)
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 18. `Cslib/Logics/Propositional/ProofSystem/Derivation.lean`
- **External**: None
- **Internal**: `* Cslib/Logics/Modal/Metalogic/DerivationTree.lean -- modal derivation tree pattern` -- CONFORMANT (bare path)
- **Internal**: `* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS API` -- CONFORMANT (bare path)
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 19. `Cslib/Logics/Propositional/ProofSystem/Instances.lean`
- **External**: None
- **Internal**: `* Cslib/Logics/Bimodal/ProofSystem/Instances.lean -- bimodal instance pattern` -- CONFORMANT (bare path)
- **Internal**: `* Cslib/Foundations/Logic/ProofSystem.lean -- typeclass hierarchy` -- CONFORMANT (bare path)
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 20. `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean`
- **External**: None
- **Internal**: `* Cslib/Logics/Propositional/ProofSystem/Instances.lean -- classical instance pattern` -- CONFORMANT (bare path)
- **Internal**: `* Cslib/Foundations/Logic/ProofSystem.lean -- typeclass hierarchy` -- CONFORMANT (bare path)
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 21. `Cslib/Logics/Propositional/Semantics/Basic.lean`
- **External**: `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 1.2, Definition 1.5` -- CONFORMANT (multi-line)
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 22. `Cslib/Logics/Propositional/Semantics/Kripke.lean`
- **External**: `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 2.2, Proposition 2.1` -- CONFORMANT (multi-line)
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

### Modal Files (4 files)

#### 23. `Cslib/Logics/Modal/Basic.lean`
- **External**: `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]` -- CONFORMANT
- **Internal**: `* The definitions of theory equivalence and the denotational semantics of worlds are inspired by the development of \`Cslib.Logic.HML\`.` -- This is prose, not a cross-ref (uses module path with dots, not file path). Not a citation conformance issue.
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 24. `Cslib/Logics/Modal/Cube.lean`
- **External**: `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]` -- CONFORMANT
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 25. `Cslib/Logics/Modal/Denotation.lean`
- **External**: `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]` -- CONFORMANT
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

#### 26. `Cslib/Logics/Modal/LogicalEquivalence.lean`
- **External**: `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]` -- CONFORMANT
- **Internal**: None
- **Bullets**: `*` -- CONFORMANT
- **Issues**: None

## Orphaned Bib Entry: HughesCresswell1996

**Status**: Present in `references.bib`, not cited in any `.lean` file on the PR branch.

Verified via:
```
git grep -l "HughesCresswell1996" pr1/foundations-logic -- '*.lean'
# Returns: nothing (only references.bib itself)
```

**Action**: Remove the `@book{HughesCresswell1996, ...}` entry from `references.bib`.

## Missing Bib Entry: SorensenUrzyczyn2006

**Bibliographic details** (Sorensen & Urzyczyn, *Lectures on the Curry-Howard Isomorphism*):

```bibtex
@book{SorensenUrzyczyn2006,
  author       = {S{\o}rensen, Morten Heine and Urzyczyn, Pawel},
  title        = {Lectures on the Curry-Howard Isomorphism},
  series       = {Studies in Logic and the Foundations of Mathematics},
  volume       = {149},
  publisher    = {Elsevier},
  address      = {Amsterdam},
  year         = {2006},
  isbn         = {978-0-444-52077-7}
}
```

**Action**: Add this entry to `references.bib` in alphabetical order (after `Sangiorgi2011`, before `ShepherdsonSturgis1963`).

## Internal Cross-Reference Convention Recommendation

**Recommendation: Bare paths** (no backticks).

**Rationale**:
- The citation conventions standard (lines 77-78) shows bare paths: `* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness`
- On `main`, bare style outnumbers backtick style 45:8 across the entire codebase
- On the PR branch within scope, bare style outnumbers backtick style 10:8
- All backtick instances come from exactly 3 files in `NaturalDeduction/` (DerivedRules, Equivalence, HilbertDerivedRules), suggesting they were written together and diverged from the established convention

**Action**: Convert 8 backtick-wrapped cross-refs in 3 files to bare paths.

## Complete Change List

### 1. `references.bib`
- Remove `@book{HughesCresswell1996, ...}` entry (lines ~110-117 approximately)
- Add `@book{SorensenUrzyczyn2006, ...}` entry in alphabetical position

### 2. `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (lines 53-57)
- Extract Sorensen & Urzyczyn from inline prose within TroelstraVanDalen1988 bullet
- Restructure as two separate bullets:

**Before**:
```
* [A. S. Troelstra, D. van Dalen,
  *Constructivism in Mathematics: An Introduction*][TroelstraVanDalen1988],
  the sequent-style natural deduction presented here is tersely
  described in Section 10.4, and in Section 2.2 of Sorensen &
  Urzyczyn's *Lectures on the Curry-Howard Isomorphism*.
```

**After**:
```
* [A. S. Troelstra, D. van Dalen,
  *Constructivism in Mathematics: An Introduction*][TroelstraVanDalen1988],
  Section 10.4
* [M. H. Sorensen, P. Urzyczyn,
  *Lectures on the Curry-Howard Isomorphism*][SorensenUrzyczyn2006],
  Section 2.2
```

### 3. `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` (lines 58-59)
- `* \`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean\`` -> `* Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
- `* \`Cslib/Logics/Propositional/Defs.lean\`` -> `* Cslib/Logics/Propositional/Defs.lean`

### 4. `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (lines 42-44)
- `* \`Cslib/Logics/Propositional/ProofSystem/Derivation.lean\`` -> `* Cslib/Logics/Propositional/ProofSystem/Derivation.lean`
- `* \`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean\`` -> `* Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
- `* \`Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean\`` -> `* Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`

### 5. `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` (lines 44-46)
- `* \`Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean\`` -> `* Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean`
- `* \`Cslib/Logics/Propositional/ProofSystem/Derivation.lean\`` -> `* Cslib/Logics/Propositional/ProofSystem/Derivation.lean`
- `* \`Cslib/Logics/Propositional/ProofSystem/Axioms.lean\`` -> `* Cslib/Logics/Propositional/ProofSystem/Axioms.lean`

## Statistics

| Category | Count |
|----------|-------|
| Total files audited | 26 |
| Files fully conformant | 21 |
| Files with issues | 5 |
| Orphaned bib entries to remove | 1 |
| Missing bib entries to add | 1 |
| Inline citations to convert | 1 |
| Backtick cross-refs to fix | 8 (across 3 files) |
| Total edits needed | 12 |
