# PR 1 Foundations Logic Code Review

## Overview

This review covers the 16 files in `Cslib/Foundations/Logic/` (including `Helpers/ListHelpers.lean`), totaling approximately 3,800 lines. All files build cleanly with zero sorries, zero `set_option` directives, and all lines under 100 characters.

The overall code quality is high. The architecture is well-designed, the typeclass hierarchy is clean, documentation is thorough, and proofs are correct. The findings below are organized into actionable items with resolved decisions.

---

## 1. Trim Redundant Imports

**Decision**: Trim redundant imports. Remove imports that are already transitively available.

**ProofSystem.lean** (lines 9-12): Remove `public import Cslib.Init` (available via Axioms) and `public import Cslib.Foundations.Logic.Connectives` (available via Axioms). Keep `InferenceSystem` and `Axioms`.

**Axioms.lean** (lines 9-10): Remove `public import Cslib.Init` (available via Connectives). Keep `Connectives`.

**Modal/Basic.lean** (lines 9-12): Remove `public import Cslib.Foundations.Logic.ProofSystem` (available via Combinators). Keep `Combinators`, `Core`, and `Connectives`.

**Modal/S5.lean** (lines 9-13): Remove `public import Cslib.Foundations.Logic.ProofSystem` (available via Combinators). Additionally, `Combinators`, `Core`, and `Connectives` are all available via `Modal.Basic` — verify whether these can also be trimmed without breaking anything.

---

## 2. Move `Helpers/ListHelpers.lean` to `Foundations/Data/`

**Decision**: Move in this PR.

`Cslib/Foundations/Logic/Helpers/ListHelpers.lean` is a pure list utility with no logic-specific content. Move it to `Cslib/Foundations/Data/ListHelpers.lean` (or similar). Update all import paths — the file is imported by DeductionTheorem files in `Cslib/Logics/` (Propositional, Modal, Temporal, Bimodal).

---

## 3. Remove Double Blank Lines

Reduce consecutive blank lines to single blank lines in:
- `Theorems/Modal/S5.lean` (lines 168-169, 236-237, 266-267, 333-334, 441-442, 543-544)
- `Theorems/Temporal/TemporalDerived.lean` (lines 120-121, 209-210, 234-235, 253-254, 275-276, 290-291 approximately)

---

## 4. Remove `-- section` Comments from `end`

**Decision**: Keep unnamed sections, just remove the non-standard `-- section` annotation from `end` lines.

Files affected:
- `Theorems/Combinators.lean` (line 331: `end -- section` → `end`)
- `Theorems/Propositional/Core.lean` (line 286)
- `Theorems/Propositional/Connectives.lean` (line 544)
- `Theorems/Propositional/BigConj.lean` (line 139)
- `Theorems/Modal/Basic.lean` (line 201)
- `Theorems/Modal/S5.lean` (line 637)
- `Theorems/Temporal/TemporalDerived.lean` (line 291)

---

## 5. Fix Empty Module Docstring

**InferenceSystem.lean** (line 11): Replace `/-! -/` with a descriptive module docstring, e.g., `/-! # Inference System Typeclass -/` describing the `InferenceSystem` class and `DerivableIn` predicate.

---

## 6. Clean Up Draft Comment

**Decision**: Replace the multi-line draft docstring with a minimal one-line docstring.

**Theorems/Propositional/Connectives.lean** (lines 279-290): Replace the entire docstring block (which contains "wait, this does not type-check as stated. Let me reconsider." and the subsequent working-out notes) with:

```lean
/-- De Morgan 1 backward: `⊢ (¬φ ∨ ¬ψ) → ¬(φ ∧ ψ)`. -/
```

---

## 7. Standardize Variable Names in S5.lean

Rename `A B` back to `φ ψ` in all theorem signatures that use them:
- Line 445: `{A B : F}` → `{φ ψ : F}`
- Line 503: `{A B : F}` → `{φ ψ : F}`
- Line 513: `{A : F}` → `{φ : F}`
- Line 546: `{A B : F}` → `{φ ψ : F}`

Update all references to `A`/`B` within the corresponding proof bodies to `φ`/`ψ`.

---

## 8. Rename `theorem_flip` / `theorem_app1` / `theorem_app2`

**Decision**: Rename to `flip` / `app1` / `app2`.

In `Theorems/Combinators.lean`:
- `theorem_flip` → `flip` (line 89)
- `theorem_app1` → `app1` (line 128)
- `theorem_app2` → `app2` (line 139)

This requires a coordinated rename across all downstream files that reference these names. Search for `theorem_flip`, `theorem_app1`, `theorem_app2`, and `@theorem_flip`, `@theorem_app1`, `@theorem_app2` across the entire codebase.

---

## 9. Align LeftMono/RightMono Variable Ordering

**Decision**: Align variable ordering to a consistent convention.

Current state in `Axioms.lean`:
- `LeftMonoUntilG (φ χ ψ : F)`: formula is `G(φ → χ) → (ψ U φ → ψ U χ)`
- `LeftMonoSinceH (φ χ ψ : F)`: formula is `H(φ → χ) → (ψ S φ → ψ S χ)`
- `RightMonoUntil (φ ψ χ : F)`: formula is `G(φ → ψ) → (φ U χ → ψ U χ)`
- `RightMonoSince (φ ψ χ : F)`: formula is `H(φ → ψ) → (φ S χ → ψ S χ)`

Both currently list the G/H-guarded implication pair first, then the fixed variable — which is actually already internally consistent. However, the variable *names* differ in position (`χ` is the 2nd arg in LeftMono but the 3rd in RightMono). Adopt a uniform convention where all four use `(φ ψ χ)` with consistent role assignment:
- `φ`, `ψ` = the pair under the G/H guard (the implication `φ → ψ`)
- `χ` = the fixed operand in the Until/Since

This means `LeftMonoUntilG` and `LeftMonoSinceH` need reordering from `(φ χ ψ)` to `(φ ψ χ)` with corresponding body updates. Check downstream usage in `TemporalDerived.lean` and instance files.

---

## 10. Remove Trailing Apostrophe from `G_imp_trans'` / `H_imp_trans'`

In `Theorems/Temporal/TemporalDerived.lean`:
- `G_imp_trans'` → `G_imp_trans` (line 239)
- `H_imp_trans'` → `H_imp_trans` (line 258)

No unprimed variants exist, so the `'` serves no purpose. Search for downstream references.

---

## 11. Use `diamond'`/`iff'` Abbreviations in S5.lean Theorems

**Decision**: Refactor S5.lean to use the existing `diamond'` and `iff'` abbreviations in theorem statements and proofs where applicable.

Currently `S5.lean` defines (lines 71-74):
```lean
abbrev diamond' (φ : F) : F :=
  HasImp.imp (HasBox.box (neg' φ)) HasBot.bot
abbrev iff' (a b : F) : F :=
  conj' (HasImp.imp a b) (HasImp.imp b a)
```

These are never used — all theorems spell out the full `HasImp.imp (HasBox.box ...) HasBot.bot` form. Refactor theorem type signatures to use `diamond'` and `iff'` where they match the expanded form. This will significantly improve readability of theorems like `diamond_disj_iff`, `s5_diamond_conj_diamond`, etc.

Note: since these are `abbrev`, the change is definitionally transparent — proofs should still work after substitution, but verify with `lake build`.

---

## 12. Add Triviality Note to `FUntilEquiv` Docstring

In `Axioms.lean`, `FUntilEquiv` (line 269) reduces to `P → P` (identity) but lacks the explanatory note that its dual `PSinceEquiv` has. Add a note like: "Under the Burgess 1982 convention, this is trivially F(φ) → F(φ)."

---

## 13. Add Section Comments to `app2` Proof

The `app2` proof (currently `theorem_app2`, lines 139-265 in `Combinators.lean`, 127 lines) is the longest proof in the PR. Add brief section comments within the proof marking major milestones to aid readability. The proof builds the Vireo combinator through deeply nested modus ponens — marking key intermediate goals would help future readers.

---

## Items Kept As-Is (No Action)

| Item | Rationale |
|------|-----------|
| `LukasiewiczDerived` class | Keep as specification artifact. Well-documented, harmless. |
| `someFuture`/`allFuture` camelCase | Keep camelCase. Readable as English abbreviations. |
| Proof style mix (tactic vs term) | Already well-balanced. |
| Explicit `@` for instance resolution | Inherent to the typeclass design; not worth refactoring for this PR. |
| Broad `open` declarations | Acceptable given unique namespacing. |

---

## Summary of All Actions

| # | Action | Files | Scope |
|---|--------|-------|-------|
| 1 | Trim redundant imports | ProofSystem, Axioms, Modal/Basic, Modal/S5 | Remove ~5 import lines |
| 2 | Move ListHelpers to Foundations/Data/ | Helpers/ListHelpers + 4 DeductionTheorem importers | File move + import update |
| 3 | Remove double blank lines | S5, TemporalDerived | ~12 blank line deletions |
| 4 | Remove `-- section` from `end` | 7 theorem files | 7 line edits |
| 5 | Fix empty module docstring | InferenceSystem | 1 line edit |
| 6 | Clean up draft comment | Theorems/Propositional/Connectives | Replace multi-line docstring |
| 7 | Standardize variable names | S5 | 4 theorem signatures + proof bodies |
| 8 | Rename theorem_flip/app1/app2 | Combinators + all downstream | Coordinated rename |
| 9 | Align LeftMono/RightMono var order | Axioms + downstream | 2 axiom signatures + usages |
| 10 | Remove trailing apostrophe | TemporalDerived | 2 renames + downstream refs |
| 11 | Use diamond'/iff' abbreviations | S5 | Refactor theorem signatures/proofs |
| 12 | Add FUntilEquiv triviality note | Axioms | 1 docstring addition |
| 13 | Add section comments to app2 proof | Combinators | Inline comments only |
