# Teammate B Findings: Proof Quality, Structure, and Infrastructure

**Task**: 82 — Systematic codebase review of Logics/ and Foundations/ for publication quality
**Angle**: Proof quality, structural organization, and infrastructure patterns
**Date**: 2026-06-10

## Key Findings

### 1. Unnamed Sections Throughout Foundations/Logic/Theorems/ (Medium Severity)

**Files affected**:
- `Cslib/Foundations/Logic/Theorems/Combinators.lean:49` — `section` (unnamed)
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean:51` — `section` (unnamed)
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean:50` — `section` (unnamed)
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean:53` — `section` (unnamed)
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean:72` — `section` (unnamed)
- `Cslib/Foundations/Logic/Theorems/BigConj.lean:91` — `section` (unnamed)
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean:36` — `section` (unnamed)

**Issue**: All theorem files in Foundations use bare `section` without names. Mathlib style recommends named sections for clarity, especially when the section spans the entire file body. Named sections make it clearer what variables are being scoped.

**Suggestion**: Name these sections descriptively (e.g., `section Combinators`, `section CoreTheorems`, `section ModalBasic`). The Axioms.lean file in the same directory already uses good named sections (`section Abbreviations`, `section Propositional`, `section Modal`, etc.) — these theorem files should follow the same pattern.

**Confidence**: High

---

### 2. Naming Convention Inconsistencies: snake_case Definitions (High Severity)

Mathlib convention uses `camelCase` for definitions and `snake_case` for theorem/lemma names. Several definitions use snake_case where camelCase is expected.

**Definitions that should be camelCase**:
- `Cslib/Foundations/Logic/Theorems/BigConj.lean:51` — `def bigconj` → should be `def bigConj`
- `Cslib/Foundations/Logic/Theorems/BigConj.lean:61` — `def negBigconj` → should be `def negBigConj`
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean:82` — `def deduction_axiom` → should be `def deductionAxiom`
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean:91` — `def deduction_imp_self` → should be `def deductionImpSelf`
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean:101` — `def deduction_assumption_other` → should be `def deductionAssumptionOther`
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean:110` — `def deduction_mp_under_imp` → should be `def deductionMpUnderImp`

**Theorems using camelCase where snake_case is expected** (less critical since Mathlib allows some flexibility here):
- `Cslib/Foundations/Logic/Theorems/BigConj.lean:94` — `theorem bigconj_mem_derivable` — inconsistent casing (`bigconj` vs `bigConj`)
- `Cslib/Foundations/Logic/Theorems/BigConj.lean:64-79` — `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`, `negBigconj_def` — all reference the uncapitalized `bigconj` form

**Confidence**: High

---

### 3. Sorry Stubs Remaining in Bimodal Metalogic (High Severity)

23 `sorry` instances remain across the codebase. Most are in Bimodal metalogic files blocked on task dependencies (tasks 36-37), but they should be inventoried and clearly documented.

**Files with sorry**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` — 9 sorries (task 36 dependency)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Completeness/Dense.lean` — 1 sorry (universe mismatch)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` — 1 sorry
- `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` — 2 sorries
- `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` — 7 sorries
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` — 1 sorry

**Note**: While these sorries are documented as task-blocked, they are a publication quality concern. Each should have a clear `-- sorry: blocked on task N` annotation (most already do, but some are bare `sorry`).

**Confidence**: High

---

### 4. Very Large Files Need Splitting (Medium Severity)

Several files exceed 1000 lines, which makes them difficult to review and maintain:

| File | Lines | Notes |
|------|-------|-------|
| `Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` | 3553 | Extremely large |
| `Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` | 3526 | Extremely large |
| `Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` | 3234 | Extremely large |
| `Temporal/Metalogic/Chronicle/PointInsertion.lean` | 2717 | Very large |
| `Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean` | 1692 | Large |
| `Bimodal/Metalogic/Separation/DedekindZ/Cases.lean` | 1660 | Large |
| `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` | 1529 | Large |

**Suggestion**: Files over ~1000 lines should be considered for splitting along logical boundaries (e.g., separate helper lemmas from main theorems, split by case analysis). The PointInsertion files at 3500+ lines are especially ripe for this.

**Confidence**: Medium (splitting may not be practical if proofs are deeply interconnected)

---

### 5. Verbose Raw-Encoding Proofs in Foundations Theorems (Low Severity)

The Hilbert-style proof system theorems in `Foundations/Logic/Theorems/` use raw `HasImp.imp` and `HasBot.bot` encoding throughout, making proofs extremely verbose and hard to follow. For example, `Theorems/Modal/S5.lean` has type signatures spanning 20+ lines (e.g., `diamond_disj_iff` at lines 327-366, `s5_diamond_conj_diamond` at lines 536-547).

This is somewhat inherent to the Lukasiewicz encoding approach (no notation), but:

**Specific concerns**:
- Type signatures are so long they obscure the mathematical content
- The `let` abbreviations in S5.lean (e.g., `diamond'`, `iff'` at lines 67-70) are defined at file scope but not used in the theorems themselves — they exist only as documentation
- The `demorgan_conj_neg` biconditional at line 407 has a statement spanning 27 lines of raw encoding

**Suggestion**: Consider adding a notation scope or typeclass-driven abbreviations (using `LukasiewiczDerived` which already exists but is uninstantiated) to reduce verbosity. At minimum, the existing `abbrev` abbreviations in Axioms.lean (`neg'`, `conj'`, `disj'`, `top'`) could be used consistently in theorem *statements* even if proofs must use raw encoding.

**Confidence**: Medium (the verbosity may be intentional to avoid notation clashes)

---

### 6. Inconsistent Attribute Usage (Low Severity)

The `Modal/Basic.lean` file uses both `@[simp]` and `@[scoped grind]` attributes, sometimes on the same definition. The pattern is:
- `@[simp, scoped grind =]` for `valid` and `logic` definitions
- `@[scoped grind =]` for satisfaction characterization lemmas
- `@[scoped grind →]` for directional lemmas

Meanwhile `Modal/FromPropositional.lean` uses plain `@[simp]` (3 occurrences, no `grind`).

**Suggestion**: Establish a clear convention for when to use `@[simp]` vs `@[scoped grind]` vs both. The scoped `grind` attributes appear to be the newer preferred style in `Basic.lean`; `FromPropositional.lean` should be updated to match.

**Confidence**: Medium

---

### 7. Documentation Quality Is Generally Good But Inconsistent (Low Severity)

Most files have excellent module-level documentation with `/-! # ... -/` docstrings, `## Main Results` sections, and references. This is publication-quality.

**Good examples**: `Foundations/Logic/Axioms.lean`, `Foundations/Logic/ProofSystem.lean`, `Logics/Modal/Basic.lean`, `Logics/Propositional/NaturalDeduction/Basic.lean`

**Gaps**:
- `Foundations/Logic/LogicalEquivalence.lean` — has minimal documentation (only basic module doc without Main Results)
- Some theorem-level docstrings in the S5 file repeat information already in the proof comments (minor redundancy)
- The `Foundations/Logic/Theorems/BigConj.lean` module doc is adequate but less detailed than peer files

**Confidence**: High

---

### 8. Proof Term vs. Tactic Proof Consistency (Low Severity)

The codebase shows a mostly consistent preference for tactic-mode proofs (`by ... exact ...`) for non-trivial theorems and term-mode for simple definitions. However, some files mix approaches inconsistently:

- `Foundations/Logic/Theorems/Combinators.lean`: `b_combinator` (line 80) uses term-mode while most others use tactic-mode
- `Foundations/Logic/Theorems/Propositional/Core.lean`: `lem` (line 280) is a pure term-mode proof while all others are tactic-mode
- `Foundations/Logic/Theorems/Propositional/Connectives.lean`: `demorgan_conj_neg` (line 407) and `demorgan_disj_neg` (line 505) use term-mode (just `iff_intro ...`) while their component lemmas use tactic-mode

This is actually acceptable and arguably the right pattern (simple applications in term-mode, complex proofs in tactic-mode), so this is informational rather than actionable.

**Confidence**: High (but severity is low — this is fine as-is)

---

### 9. ORGANISATION.md vs Actual Code Structure Discrepancy (Medium Severity)

`ORGANISATION.md` describes the logics namespace as `Cslib.Logic` but the actual codebase uses `Cslib.Logics` (plural) for domain-specific logic files, while `Cslib.Logic` is used for Foundations-level abstractions. The namespace mapping is:

- `Cslib.Logic` → `Cslib/Foundations/Logic/` (InferenceSystem, Connectives, Axioms, etc.)
- `Cslib.Logic.Modal` → `Cslib/Logics/Modal/` (concrete modal logic)
- `Cslib.Logic.PL` → `Cslib/Logics/Propositional/` (concrete propositional logic)

The ORGANISATION.md says `Cslib.Logic` houses logics (HoareLogic, LinearLogic, etc.), but the directory structure has `Cslib/Logics/` (plural) for concrete logics and `Cslib/Foundations/Logic/` for shared infrastructure.

**Suggestion**: Either update ORGANISATION.md to reflect the actual dual structure (Foundations.Logic for infrastructure, Logics.{Modal,Propositional,...} for concrete logics), or note that the namespace (`Cslib.Logic.Modal`) doesn't directly match the file path (`Cslib/Logics/Modal/`).

**Confidence**: High

---

### 10. Infrastructure Patterns: Good Typeclass Design (Positive Finding)

The typeclass hierarchy is well-designed and consistent:
- **Connective typeclasses** (`HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`) compose cleanly into bundled classes
- **Proof system typeclasses** (`PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`) use `extends` properly
- **Individual axiom typeclasses** (`HasAxiomImplyK`, `HasAxiomT`, etc.) enable fine-grained composition
- **Generic MCS framework** (`DerivationSystem`, `SetConsistent`, `SetMaximalConsistent`) is properly parameterized
- **Generic deduction helpers** (`HasHilbertTree`) abstract over 4 concrete logics cleanly
- `InferenceSystem` typeclass provides the shared derivation interface

This is publication-quality infrastructure design. The main improvement would be to ensure all concrete logics consistently instantiate these typeclasses (the `ProofSystem.lean` notes that concrete instances are "future work" for some tag types).

**Confidence**: High

---

## Recommended Approach

### Priority 1 (High impact, low effort):
1. **Rename snake_case definitions** in `DeductionHelpers.lean` and `BigConj.lean` to follow Mathlib camelCase convention
2. **Name unnamed sections** across `Foundations/Logic/Theorems/` files
3. **Annotate bare sorry stubs** with task-blocking context where missing

### Priority 2 (Medium impact, medium effort):
4. **Update ORGANISATION.md** to match actual directory/namespace structure
5. **Harmonize attribute usage** (`@[simp]` vs `@[scoped grind]`) in Modal files
6. **Consider splitting** the largest files (3500+ lines)

### Priority 3 (Lower priority):
7. **Evaluate notation/abbreviation usage** in theorem statements to reduce verbosity
8. **Fill documentation gaps** in LogicalEquivalence.lean and BigConj.lean

## Evidence/Examples

### Naming Convention Violation Example (DeductionHelpers.lean:82-117):
```lean
-- Current (snake_case — violates Mathlib convention for defs):
noncomputable def deduction_axiom (Γ : List F) (A : F) ...
noncomputable def deduction_imp_self (Γ : List F) (A : F) ...
noncomputable def deduction_assumption_other (Γ : List F) (A B : F) ...
noncomputable def deduction_mp_under_imp (Γ : List F) (A C D : F) ...

-- Should be:
noncomputable def deductionAxiom (Γ : List F) (A : F) ...
noncomputable def deductionImpSelf (Γ : List F) (A : F) ...
noncomputable def deductionAssumptionOther (Γ : List F) (A B : F) ...
noncomputable def deductionMpUnderImp (Γ : List F) (A C D : F) ...
```

### Unnamed Section Example (Combinators.lean:49):
```lean
-- Current:
section
-- Should be:
section Combinators
```

### Verbose Type Signature Example (S5.lean:327-366):
The `diamond_disj_iff` theorem statement spans 40 lines of raw `HasImp.imp`/`HasBox.box`/`HasBot.bot` encoding, making the mathematical content nearly unreadable. The mathematical statement is simply `◇(φ ∨ ψ) ↔ (◇φ ∨ ◇ψ)`.

## Confidence Level

**Overall confidence**: High for naming and structural findings, medium for proof style and verbosity findings. The naming issues are clear convention violations. The verbosity concern depends on project design decisions about notation vs. raw encoding.
