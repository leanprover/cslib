# Research Report: Bibliographic References for PR 1

- **Task**: 123 - Add bibliographic references for PR 1
- **Started**: 2026-06-11T14:00:00Z
- **Completed**: 2026-06-11T14:30:00Z
- **Effort**: Small-medium (documentation-only changes across ~25 files)
- **Dependencies**: None
- **Sources/Inputs**: references.bib, CONTRIBUTING.md, existing CSLib docstrings, specs/literature/
- **Artifacts**: specs/123_add_bib_references_pr1/reports/01_bib-references-research.md
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

## Executive Summary

- CSLib follows the **Mathlib citation convention**: `* [Author, *Title*][BibKey]` in `## References` sections of module docstrings, with `BibKey` matching entries in the root `references.bib` file.
- PR 1 branch (`pr1/foundations-logic`) contains **Propositional logic** files (semantics, metalogic, natural deduction, proof system) and **Modal logic** files (Basic, Cube, Denotation, LogicalEquivalence). It does NOT include the Modal Metalogic files (K/T/S4/S5 soundness/completeness) or Temporal/Bimodal files -- those are on `main`.
- Many PR 1 files use an informal "CZ" abbreviation for Chagrov & Zakharyaschev instead of the proper `[BibKey]` format, and this book is **missing from `references.bib`**.
- Some files have no `## References` section at all despite referencing standard textbook material.
- **Key action**: Add Chagrov & Zakharyaschev to `references.bib`, then update all PR 1 Propositional files to use the Mathlib-style `[ChagrovZakharyaschev1997]` citation format. The Modal files already have correct Blackburn references.

## Context & Scope

### Task Scope

Task 123 is about adding proper bibliographic references to files on the `pr1/foundations-logic` branch. The PR 1 branch contains changes to:

1. **Cslib/Logics/Propositional/** (22 files): Full propositional logic formalization including:
   - `Defs.lean` -- Formula type, theories
   - `Semantics/Basic.lean` -- Bivalent truth-value semantics
   - `Semantics/Kripke.lean` -- Kripke semantics for intuitionistic logic
   - `ProofSystem/Axioms.lean` -- Hilbert-style axiom schemata
   - `ProofSystem/Derivation.lean` -- Derivation trees
   - `ProofSystem/Instances.lean` -- Proof system instances
   - `ProofSystem/IntMinInstances.lean` -- Intuitionistic/minimal instances
   - `Metalogic/Soundness.lean` -- Classical soundness
   - `Metalogic/Completeness.lean` -- Classical completeness (Henkin construction)
   - `Metalogic/MCS.lean` -- Maximal consistent sets
   - `Metalogic/DeductionTheorem.lean` -- Deduction theorem
   - `Metalogic/IntSoundness.lean` -- Intuitionistic soundness
   - `Metalogic/IntCompleteness.lean` -- Intuitionistic completeness
   - `Metalogic/IntLindenbaum.lean` -- Intuitionistic Lindenbaum lemma
   - `Metalogic/MinSoundness.lean` -- Minimal logic soundness
   - `Metalogic/MinCompleteness.lean` -- Minimal logic completeness
   - `Metalogic/MinLindenbaum.lean` -- Minimal logic Lindenbaum lemma
   - `NaturalDeduction/Basic.lean` -- ND system
   - `NaturalDeduction/DerivedRules.lean` -- Derived ND rules
   - `NaturalDeduction/Equivalence.lean` -- Hilbert-ND equivalence
   - `NaturalDeduction/FromHilbert.lean` -- Translation from Hilbert
   - `NaturalDeduction/HilbertDerivedRules.lean` -- Derived Hilbert rules

2. **Cslib/Logics/Modal/** (4 files on PR 1 branch):
   - `Basic.lean` -- Formula type, Kripke semantics, axiom schemata
   - `Cube.lean` -- Modal logic cube
   - `Denotation.lean` -- Denotational semantics
   - `LogicalEquivalence.lean` -- Logical equivalence

3. **Cslib/Foundations/Logic/ProofSystem.lean** (modified)
4. **Cslib/Foundations/Data/HasFresh.lean** (modified)

### Out of Scope

The following are on `main` but NOT on the `pr1/foundations-logic` branch:
- `Cslib/Logics/Modal/Metalogic/` (K/T/S4/S5/KB5 etc. soundness/completeness files)
- `Cslib/Logics/Temporal/` (temporal logic files)
- `Cslib/Logics/Bimodal/` (bimodal logic files)

These files reference Blackburn, Burgess, Xu, and GHR94 and will need their own reference passes in separate PRs.

## Findings

### 1. CSLib Citation Convention

The CSLib project follows the **Mathlib documentation style** (per CONTRIBUTING.md: "We generally follow the mathlib style for coding and documentation"). The Mathlib citation format is:

```
## References

* [Author1, Author2, *Title*][BibKey]
```

Where `BibKey` matches an entry in the root `references.bib` file. Examples from existing CSLib files:

- `Cslib/Languages/CCS/Basic.lean`:
  ```
  * [R. Milner, *A Calculus of Communicating Systems*][Milner80]
  * [D. Sangiorgi, *Introduction to Bisimulation and Coinduction*][Sangiorgi2011]
  ```

- `Cslib/Logics/HML/Basic.lean`:
  ```
  * [M. Hennessy, R. Milner, *Algebraic Laws for Nondeterminism and Concurrency*][Hennessy1985]
  * [L. Aceto, A. Ingolfsdottir, *Testing Hennessy-Milner Logic with Recursion*][Aceto1999]
  ```

- `Cslib/Logics/Modal/Basic.lean`:
  ```
  * [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
  ```

- `Cslib/Logics/LinearLogic/CLL/Basic.lean`:
  ```
  * [J.-Y. Girard, *Linear Logic: its syntax and semantics*][Girard1995]
  ```

**Key Convention Details**:
- Use `*` bullets (not `-` bullets) in the References section
- Author names: first initial + last name
- Titles in italics using `*...*`
- BibKey in square brackets `[...]` linking to `references.bib`
- Internal cross-references (to other CSLib files) can use plain text without `[BibKey]`

### 2. Literature Sources in specs/literature/

The `specs/literature/` directory contains:

| File | Description |
|------|-------------|
| `blackburn.pdf` | Blackburn, de Rijke, Venema - "Modal Logic" (full book) |
| `blackburn_1.pdf` / `.md` | Chapter 1 (Basic Modal Logic) |
| `blackburn_2.pdf` / `.md` | Chapter 2 (Models) |
| `blackburn_3.pdf` / `.md` | Chapter 3 (Proof Theory) |
| `blackburn_4.pdf` / `.md` | Chapter 4 (Completeness) |
| `blackburn-ch4-completeness.md` | Completeness chapter notes |
| `advanced_modal_logic.pdf` / `.md` | Advanced topics (Part 1) |
| `advanced_modal_logic_2.pdf` / `.md` | Advanced topics (Part 2) |
| `modal_logic.djvu` / `.md` | Hughes & Cresswell - "A New Introduction to Modal Logic" |
| `A New Introduction to Modal Logic...pdf` | Hughes & Cresswell (PDF version) |

These are the primary sources used for the modal logic and metalogic proofs.

### 3. Current Reference Problems in PR 1 Files

#### Problem A: "CZ" abbreviation not in references.bib

14 Propositional files use `CZ` as a shorthand (e.g., "CZ Theorem 1.16", "CZ Section 2.2") for what is almost certainly **Chagrov & Zakharyaschev, "Modal Logic" (1997)**, Oxford Logic Guides. This book is NOT in `references.bib`.

Files using "CZ":
- `Semantics/Basic.lean` -- "CZ Section 1.2, Definition 1.5"
- `Semantics/Kripke.lean` -- "CZ Section 2.2, Proposition 2.1"
- `Metalogic/Soundness.lean` -- "CZ Theorem 1.16"
- `Metalogic/Completeness.lean` -- "CZ Theorem 1.16, Section 5.1"
- `Metalogic/IntSoundness.lean` -- "CZ Theorem 2.43, Proposition 2.1"
- `Metalogic/IntCompleteness.lean` -- "CZ Theorem 2.43"
- `Metalogic/IntLindenbaum.lean` -- "CZ Section 5.1, Theorem 2.43"
- `Metalogic/MinSoundness.lean` -- "CZ Theorem 2.43, Proposition 2.1"
- `Metalogic/MinCompleteness.lean` -- "CZ Theorem 2.43"
- `Metalogic/MinLindenbaum.lean` -- "CZ Section 5.1"

#### Problem B: Non-standard citation format

Even where references exist, they often use an informal style instead of the Mathlib convention:
- `* CZ Theorem 1.16` should be `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997]`
- `* Cslib/Logics/Modal/Metalogic/Soundness.lean` (plain path, acceptable as internal cross-reference)

#### Problem C: Missing references sections

Several PR 1 files have NO `## References` section at all despite covering standard textbook material:
- `Propositional/Defs.lean` -- Formula definitions (standard PL)
- `Propositional/NaturalDeduction/DerivedRules.lean`
- `Propositional/NaturalDeduction/FromHilbert.lean`
- `Modal/Denotation.lean`
- `Modal/LogicalEquivalence.lean`
- `Foundations/Logic/ProofSystem.lean`

#### Problem D: ND/Basic.lean uses non-standard format

`NaturalDeduction/Basic.lean` uses dashes (`-`) instead of bullets (`*`):
```
- Dag Prawitz, *Natural Deduction: a proof-theoretical study*.
- Troelstra & van Dalen's *Constructivism in Mathematics*
```
These also lack `[BibKey]` references in `references.bib`.

### 4. Existing Correct References (No Changes Needed)

- `Cslib/Logics/Modal/Basic.lean` -- Already has correct `[Blackburn2001]` reference
- `Cslib/Logics/Modal/Cube.lean` -- Already has correct `[Blackburn2001]` reference

### 5. Books Needed in references.bib

The following entries need to be added to `references.bib`:

1. **Chagrov & Zakharyaschev** (referenced as "CZ" throughout Propositional files):
   ```bibtex
   @book{ChagrovZakharyaschev1997,
     author    = {Chagrov, Alexander and Zakharyaschev, Michael},
     title     = {Modal Logic},
     series    = {Oxford Logic Guides},
     volume    = {35},
     publisher = {Clarendon Press},
     address   = {Oxford},
     year      = {1997},
     isbn      = {978-0-19-853779-3}
   }
   ```

2. **Prawitz** (referenced in NaturalDeduction/Basic.lean):
   ```bibtex
   @book{Prawitz1965,
     author    = {Prawitz, Dag},
     title     = {Natural Deduction: A Proof-Theoretical Study},
     publisher = {Almqvist \& Wiksell},
     address   = {Stockholm},
     year      = {1965},
     note      = {Reprinted by Dover Publications, 2006}
   }
   ```

3. **Troelstra & van Dalen** (referenced in NaturalDeduction/Basic.lean):
   ```bibtex
   @book{TroelstraVanDalen1988,
     author    = {Troelstra, Anne Sjerp and van Dalen, Dirk},
     title     = {Constructivism in Mathematics: An Introduction},
     volume    = {1},
     series    = {Studies in Logic and the Foundations of Mathematics},
     publisher = {North-Holland},
     address   = {Amsterdam},
     year      = {1988},
     isbn      = {978-0-444-70506-8}
   }
   ```

4. **Hughes & Cresswell** (referenced in specs/literature/ but not yet in any code file; may be useful for some modal files):
   ```bibtex
   @book{HughesCresswell1996,
     author    = {Hughes, G. E. and Cresswell, M. J.},
     title     = {A New Introduction to Modal Logic},
     publisher = {Routledge},
     address   = {London},
     year      = {1996},
     isbn      = {978-0-415-12599-4}
   }
   ```

## Decisions

1. **Scope**: Focus on files present on the `pr1/foundations-logic` branch. Files on `main` only (Modal Metalogic, Temporal, Bimodal) will be handled in separate PRs.

2. **Format**: All references must use the Mathlib-style convention: `* [Author, *Title*][BibKey]`.

3. **Internal cross-references**: References to other CSLib files (e.g., `* Cslib/Logics/Modal/Metalogic/Soundness.lean`) are acceptable as secondary references without `[BibKey]` format, following existing CSLib practice.

4. **CZ resolution**: "CZ" references will be replaced with the proper `[ChagrovZakharyaschev1997]` bibkey with specific section/theorem citations preserved in parentheses.

## Recommendations

### Step 1: Add entries to references.bib

Add the 4 new bib entries listed in Finding 5 above:
- `ChagrovZakharyaschev1997`
- `Prawitz1965`
- `TroelstraVanDalen1988`
- `HughesCresswell1996`

### Step 2: Update Propositional files (14 files with "CZ" references)

Replace informal "CZ" references with proper format. For each file:

**`Semantics/Basic.lean`**: Replace:
```
* CZ Section 1.2 (truth tables), Definition 1.5 (tautology)
```
With:
```
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 1.2, Definition 1.5
```

**`Semantics/Kripke.lean`**: Replace CZ Section 2.2 reference similarly.

**`Metalogic/Soundness.lean`**: Replace CZ Theorem 1.16 reference.

**`Metalogic/Completeness.lean`**: Replace CZ Theorem 1.16, Section 5.1 reference.

**`Metalogic/IntSoundness.lean`**: Replace CZ Theorem 2.43, Proposition 2.1 references.

**`Metalogic/IntCompleteness.lean`**: Replace CZ Theorem 2.43 reference.

**`Metalogic/IntLindenbaum.lean`**: Replace CZ Section 5.1, Theorem 2.43 reference.

**`Metalogic/MinSoundness.lean`**: Replace CZ Theorem 2.43, Proposition 2.1 references.

**`Metalogic/MinCompleteness.lean`**: Replace CZ Theorem 2.43 reference.

**`Metalogic/MinLindenbaum.lean`**: Replace CZ Section 5.1 reference.

### Step 3: Update Natural Deduction files

**`NaturalDeduction/Basic.lean`**: Change dash-style to bullet-style and add bibkeys:
```
* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
* [A. S. Troelstra, D. van Dalen, *Constructivism in Mathematics*][TroelstraVanDalen1988], Section 10.4
```

### Step 4: Add missing References sections

For files with standard textbook content but no References section:
- `Propositional/Defs.lean` -- Add reference to CZ Chapter 1 (propositional syntax)
- `Modal/Denotation.lean` -- Add reference to Blackburn2001 (Kripke semantics)
- `Modal/LogicalEquivalence.lean` -- Add reference to Blackburn2001

### Step 5: Verify existing correct references

Confirm that `Modal/Basic.lean` and `Modal/Cube.lean` already have correct `[Blackburn2001]` format (they do -- no changes needed).

### Per-File Reference Mapping

| File | Current Refs | Target Refs |
|------|-------------|-------------|
| `Propositional/Defs.lean` | None | `[ChagrovZakharyaschev1997]` Ch. 1 |
| `Propositional/Semantics/Basic.lean` | CZ 1.2 | `[ChagrovZakharyaschev1997]` Sec 1.2 |
| `Propositional/Semantics/Kripke.lean` | CZ 2.2 | `[ChagrovZakharyaschev1997]` Sec 2.2 |
| `Propositional/ProofSystem/Axioms.lean` | Internal only | Keep internal ref |
| `Propositional/ProofSystem/Derivation.lean` | Internal only | Keep internal ref |
| `Propositional/ProofSystem/Instances.lean` | Internal only | Keep internal ref |
| `Propositional/ProofSystem/IntMinInstances.lean` | Internal only | Keep internal ref |
| `Propositional/Metalogic/Soundness.lean` | CZ 1.16 | `[ChagrovZakharyaschev1997]` Thm 1.16 |
| `Propositional/Metalogic/Completeness.lean` | CZ 1.16 | `[ChagrovZakharyaschev1997]` Thm 1.16, Sec 5.1 |
| `Propositional/Metalogic/MCS.lean` | Internal only | Keep internal ref |
| `Propositional/Metalogic/DeductionTheorem.lean` | Internal only | Keep internal ref |
| `Propositional/Metalogic/IntSoundness.lean` | CZ 2.43 | `[ChagrovZakharyaschev1997]` Thm 2.43 |
| `Propositional/Metalogic/IntCompleteness.lean` | CZ 2.43 | `[ChagrovZakharyaschev1997]` Thm 2.43 |
| `Propositional/Metalogic/IntLindenbaum.lean` | CZ 5.1 | `[ChagrovZakharyaschev1997]` Sec 5.1 |
| `Propositional/Metalogic/MinSoundness.lean` | CZ 2.43 | `[ChagrovZakharyaschev1997]` Thm 2.43 |
| `Propositional/Metalogic/MinCompleteness.lean` | CZ 2.43 | `[ChagrovZakharyaschev1997]` Thm 2.43 |
| `Propositional/Metalogic/MinLindenbaum.lean` | CZ 5.1 | `[ChagrovZakharyaschev1997]` Sec 5.1 |
| `NaturalDeduction/Basic.lean` | Prawitz, T&vD | `[Prawitz1965]`, `[TroelstraVanDalen1988]` |
| `NaturalDeduction/DerivedRules.lean` | None | (optional: keep as-is) |
| `NaturalDeduction/Equivalence.lean` | Internal only | Keep internal ref |
| `NaturalDeduction/FromHilbert.lean` | None | (optional: keep as-is) |
| `NaturalDeduction/HilbertDerivedRules.lean` | Internal only | Keep internal ref |
| `Modal/Basic.lean` | Blackburn2001 (correct) | No change |
| `Modal/Cube.lean` | Blackburn2001 (correct) | No change |
| `Modal/Denotation.lean` | None | `[Blackburn2001]` |
| `Modal/LogicalEquivalence.lean` | None | `[Blackburn2001]` |
| `Foundations/Logic/ProofSystem.lean` | None | (optional: keep as-is, generic framework) |

## Appendix

### Reference List (to add to references.bib)

1. **ChagrovZakharyaschev1997**: Chagrov, A. & Zakharyaschev, M. (1997). *Modal Logic*. Oxford Logic Guides 35. Clarendon Press.
2. **Prawitz1965**: Prawitz, D. (1965). *Natural Deduction: A Proof-Theoretical Study*. Almqvist & Wiksell.
3. **TroelstraVanDalen1988**: Troelstra, A. S. & van Dalen, D. (1988). *Constructivism in Mathematics*, Vol. 1. North-Holland.
4. **HughesCresswell1996**: Hughes, G. E. & Cresswell, M. J. (1996). *A New Introduction to Modal Logic*. Routledge.
5. **Blackburn2001** (already in references.bib): Blackburn, P., de Rijke, M., & Venema, Y. (2001). *Modal Logic*. Cambridge Tracts in Theoretical Computer Science.

### Estimated Edit Count

- 4 new entries in `references.bib`
- ~14 files with CZ -> ChagrovZakharyaschev1997 replacement
- 1 file (ND/Basic.lean) with format correction
- 2-4 files with new References sections added
- **Total**: ~20 file edits, all documentation-only (no code changes)
