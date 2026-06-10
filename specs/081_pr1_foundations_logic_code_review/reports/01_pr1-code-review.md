# PR 1 Foundations Logic Code Review

## Overview

This review covers the 16 files in `Cslib/Foundations/Logic/` (including `Helpers/ListHelpers.lean`), totaling approximately 3,800 lines. All files build cleanly with zero sorries, zero `set_option` directives, and all lines under 100 characters.

The overall code quality is high. The architecture is well-designed, the typeclass hierarchy is clean, documentation is thorough, and proofs are correct. The findings below are organized by severity and category.

---

## 1. Infrastructure

### 1.1 Redundant Imports (Low Priority)

Several files import modules that are already transitively available via other imports:

**ProofSystem.lean** (lines 9-12):
```
public import Cslib.Init                            -- redundant (via InferenceSystem, Connectives, Axioms)
public import Cslib.Foundations.Logic.InferenceSystem -- needed directly
public import Cslib.Foundations.Logic.Connectives     -- redundant (via Axioms)
public import Cslib.Foundations.Logic.Axioms          -- needed directly
```
Since all imports are `public import`, transitivity means `Cslib.Init` and `Connectives` are already available via `Axioms`. However, some projects prefer explicit imports for documentation clarity. This is a style choice.

**Axioms.lean** (lines 9-10):
```
public import Cslib.Init        -- redundant (via Connectives)
public import Cslib.Foundations.Logic.Connectives  -- needed
```

**Modal/Basic.lean** (lines 9-12):
```
public import Cslib.Foundations.Logic.ProofSystem                      -- redundant (via Combinators)
public import Cslib.Foundations.Logic.Theorems.Combinators             -- needed (via Core)
public import Cslib.Foundations.Logic.Theorems.Propositional.Core      -- needed
public import Cslib.Foundations.Logic.Theorems.Propositional.Connectives -- needed
```
`ProofSystem` is transitively imported through `Combinators`.

**Modal/S5.lean** (lines 9-13): Same pattern as Modal/Basic, plus the redundant `ProofSystem` import. All of `Combinators`, `Core`, and `Connectives` are also available via `Modal.Basic`.

**Recommendation**: Consider trimming redundant imports in a follow-up pass. The `public import` chain means redundant imports are harmless but add visual noise. Given the PR description explicitly notes "public import Cslib.Init remains in all 4 core definition files" by design, this may be intentional.

### 1.2 Helpers Directory Placement

`Cslib/Foundations/Logic/Helpers/ListHelpers.lean` defines `removeAll` and supporting lemmas. This is a thin wrapper around `List.filter (· != a)`.

Observations:
- The name `removeAll` duplicates the concept of `List.eraseAll` (Lean 4 built-in for `BEq`) or `List.filter (· != a)` (requires `DecidableEq`)
- The file lives under `Logic/` but is purely a list utility with no logic-specific content
- It is imported only by DeductionTheorem files in `Cslib/Logics/` (Propositional, Modal, Temporal, Bimodal), not by any file in this PR

**Recommendation**: This file is correctly included in the PR since it lives under `Foundations/Logic/`, but consider whether it should live under `Foundations/Data/` given its purely list-theoretic content. This is a minor organizational point.

---

## 2. Organization

### 2.1 Double Blank Lines

`S5.lean` and `TemporalDerived.lean` each contain 6 instances of consecutive blank lines. While not a build issue, standard Lean style uses single blank lines between declarations.

**Files affected**: 
- `Theorems/Modal/S5.lean` (lines 168-169, 236-237, 266-267, 333-334, 441-442, 543-544)
- `Theorems/Temporal/TemporalDerived.lean` (lines 120-121, 209-210, 234-235, 253-254, 275-276, 290-291 approximately)

**Recommendation**: Reduce consecutive blank lines to single blank lines.

### 2.2 Unnamed Sections

Multiple files wrap their theorems in an anonymous `section` / `end -- section` block:
- `Combinators.lean` (line 49 / 331)
- `Core.lean` (line 51 / 286)
- `Connectives.lean` (line 50 / 544)
- `BigConj.lean` (line 91 / 139)
- `Modal/Basic.lean` (line 54 / 201)
- `Modal/S5.lean` (line 76 / 637)
- `TemporalDerived.lean` (line 36 / 291)

The comment `-- section` on `end` is non-standard. If the section is unnamed, `end` suffices. If naming is desired for clarity, use a named section instead.

**Recommendation**: Either name the sections or remove the `-- section` comments from `end`.

### 2.3 Module Doc String Issues

**InferenceSystem.lean** (line 11): Contains an empty module docstring `/-! -/`. This should either have content or be removed.

**Recommendation**: Add a brief module docstring like `/-! # Inference System Typeclass -/` or similar.

---

## 3. Naming Conventions

### 3.1 Variable Name Inconsistency in S5.lean

Most theorems in the PR use Greek letters `φ ψ χ` for formula variables (standard Lean convention). However, `S5.lean` switches to `A B` for later theorems:

- Lines 445, 503, 513, 546: `{A B : F}` or `{A : F}`
- Lines 83-413: Consistently use `{φ : F}` or `{φ ψ : F}`

**Recommendation**: Standardize on `φ ψ χ θ` throughout. The switch to `A B` appears to have happened when these theorems were ported from a different source.

### 3.2 `theorem_flip`, `theorem_app1`, `theorem_app2` Naming

In `Combinators.lean`, these three names use the `theorem_` prefix pattern, which is unusual for Lean. Other combinators in the same file use direct names: `imp_trans`, `identity`, `b_combinator`, `pairing`, `dni`.

The `theorem_` prefix reads as if the declaration is named "theorem flip" rather than providing a meaningful mathematical name. Standard combinator names would be:
- `theorem_flip` -> `c_combinator` (the C combinator / flip) - matches `b_combinator`
- `theorem_app1` -> `app1` or `modus_ponens_flip` 
- `theorem_app2` -> `app2` or `vireo_combinator`

**Recommendation**: Consider renaming to `c_combinator` (or `flip`), `app1`, and `app2`. These names would be more consistent with the existing `b_combinator` name. Note: these are referenced from many downstream files, so renaming would require coordinated updates.

### 3.3 LeftMono vs RightMono Variable Order Inconsistency

In `Axioms.lean`:
- `LeftMonoUntilG (φ χ ψ : F)` -- variable order is `φ χ ψ`
- `RightMonoUntil (φ ψ χ : F)` -- variable order is `φ ψ χ`

The different variable orderings between related axioms could lead to confusion when calling them. The wrapped versions in `TemporalDerived.lean` use consistent variable names but the underlying axiom definitions differ.

**Recommendation**: Document or align the variable ordering convention between paired axioms.

### 3.4 G_imp_trans' Trailing Apostrophe

In `TemporalDerived.lean`, `G_imp_trans'` and `H_imp_trans'` use a trailing apostrophe. In Lean/Mathlib convention, trailing `'` typically indicates a variant of an existing declaration. But there is no `G_imp_trans` (without apostrophe) -- the `'` appears to serve no purpose.

**Recommendation**: Remove the trailing `'` from `G_imp_trans'` and `H_imp_trans'`, or rename to `G_imp_trans` and `H_imp_trans`.

### 3.5 Mixed CamelCase in Temporal Operators

`TemporalDerived.lean` defines `someFuture`, `allFuture`, `somePast`, `allPast` using camelCase, while other abbreviations in the codebase use `snake_case` (e.g., `top'`, `neg'`, `conj'`, `disj'`, `diamond'`). And temporal theorems use `F_mono`, `P_mono`, `F_neg_G` with uppercase operator names.

This mix is partly justified (abbreviated operator names like `F`, `G`, `H`, `P` are standard in temporal logic literature), but the `someFuture`/`allFuture` camelCase is unusual for Lean definitions.

**Recommendation**: Minor concern. The camelCase for `someFuture` etc. is acceptable since they serve as readable abbreviations, but `some_future`/`all_future` would be more idiomatic Lean.

---

## 4. Comments and Documentation

### 4.1 Draft Comment Left in Docstring

**Connectives.lean** line 280-282 contains:
```
    i.e., `(¬¬φ → ¬ψ) → ¬(φ → ¬ψ)` -- wait, this does
    not type-check as stated. Let me reconsider.
```

This appears to be a draft note from the proof development process that was left in the final code.

**Recommendation**: Remove the "wait, this does not type-check" comment and replace with the corrected statement. The actual theorem statement that follows is correct.

### 4.2 Empty Module Docstring

**InferenceSystem.lean** line 11: `/-! -/` -- empty module docstring.

**Recommendation**: Add descriptive content or remove.

### 4.3 Documentation Quality - Generally Excellent

All definition files (`InferenceSystem.lean`, `Connectives.lean`, `Axioms.lean`, `ProofSystem.lean`) have thorough module-level and declaration-level docstrings. The proof files have good docstrings explaining proof strategies.

Particular strengths:
- `Connectives.lean` (lines 73-86): The `LukasiewiczDerived` class has an unusually detailed status note explaining why it is intentionally uninstantiated
- `Metalogic/Consistency.lean`: Excellent documentation throughout, with clear explanations of proof strategies
- `Combinators.lean` header: Clear naming convention note about BimodalLogic mapping
- `Axioms.lean`: Clear section organization with `/-! ### ... -/` markers

---

## 5. Proofs

### 5.1 `theorem_app2` (Combinators.lean) -- Excessive Proof Length

The `theorem_app2` proof (lines 139-265, 127 lines) is the longest single proof in the PR. It builds the Vireo combinator from K and S axioms through a deeply nested chain of modus ponens applications.

While the proof is correct and necessarily complex (Vireo requires many intermediate steps in a Hilbert system), the proof is difficult to read due to:
- Intermediate `have` bindings with generic names (`step1`, `step7_b`, `weak_step7`, etc.)
- Very deeply nested type annotations that span 10+ lines each
- No intermediate comments explaining the proof strategy (unlike `double_negation` and `rcp` which have good inline comments)

**Recommendation**: Add section comments within the proof marking major milestones. Consider whether any intermediate steps can be extracted as reusable lemmas.

### 5.2 Proof Style Consistency

The PR uses a mix of proof styles:
- **Tactic proofs** (`by ...`): Used for most complex proofs (good choice)
- **Term proofs**: Used for simple wrappers and compositions (e.g., `pairing`, `dni`, axiom wrappers in `TemporalDerived.lean`)

This is appropriate. The balance is well-chosen.

### 5.3 Heavily Explicit Type Annotations

Many proofs include very explicit `@` calls and type annotations:
```lean
have flip_inst : InferenceSystem.DerivableIn S
    (HasImp.imp ...) :=
  @theorem_flip F _ _ S _ _ φ (HasImp.imp φ HasBot.bot) ψ
```

These explicit annotations are necessary because the Lukasiewicz encoding means Lean's unifier often cannot determine which nested `HasImp.imp` application corresponds to which argument. This is an inherent cost of the `{bot, imp}` primitive basis.

**Observation**: This is not a defect but worth noting -- switching to notation (like the `diamond'`, `neg'`, `conj'` abbreviations) could reduce some visual noise while preserving definitional equality. The S5.lean file defines `diamond'` and `iff'` abbreviations but never uses them (see Section 6.1).

---

## 6. Code Quality

### 6.1 Unused Abbreviations in S5.lean

`S5.lean` defines two abbreviations at lines 71-74:
```lean
abbrev diamond' (φ : F) : F :=
  HasImp.imp (HasBox.box (neg' φ)) HasBot.bot
abbrev iff' (a b : F) : F :=
  conj' (HasImp.imp a b) (HasImp.imp b a)
```

Neither `diamond'` nor `iff'` is used in any theorem body in the file. All theorems spell out the full `HasImp.imp (HasBox.box ...) HasBot.bot` form.

**Recommendation**: Either use these abbreviations in the theorem statements/proofs to improve readability, or remove them. Using them would significantly reduce the visual complexity of theorems like `diamond_disj_iff` and `s5_diamond_conj_diamond`.

### 6.2 Trivial Axioms: FUntilEquiv and PSinceEquiv

In `Axioms.lean` (lines 269-279):
```lean
protected abbrev FUntilEquiv (φ : F) : F :=
  HasImp.imp (HasUntil.untl φ top') (HasUntil.untl φ top')
```

Both `FUntilEquiv` and `PSinceEquiv` reduce to `P → P` (identity). The docstring for `PSinceEquiv` even acknowledges: "Under the Burgess 1982 convention, this is trivially P(φ) → P(φ)."

These are included because the Burgess BX axiom system lists them, and downstream instance files (`Temporal/ProofSystem/Instances.lean`, `Bimodal/ProofSystem/Instances.lean`) provide instances. So they serve a documentation/completeness purpose even if mathematically trivial.

**Recommendation**: No action needed, but consider adding a note to `FUntilEquiv` similar to the one on `PSinceEquiv` explaining the triviality under the Burgess convention.

### 6.3 `LukasiewiczDerived` Class -- Dead Code

`Connectives.lean` (lines 87-96) defines `LukasiewiczDerived` which is:
- Intentionally uninstantiated (documented in the docstring)
- Never referenced from any file in the codebase

While the docstring explains it is "retained as a specification artifact," it adds 10 lines of code that serves no functional purpose.

**Recommendation**: The class is well-documented and harmless. If the project intends to use it for future polymorphic abstractions, keep it. Otherwise, consider removing it to reduce cognitive load.

### 6.4 `open` Declarations -- Potentially Broad

Several files open multiple namespaces:
```lean
open Cslib.Logic
open Cslib.Logic.Axioms
open Cslib.Logic.Theorems.Combinators
open Cslib.Logic.Theorems.Propositional.Core
open Cslib.Logic.Theorems.Propositional.Connectives
open Cslib.Logic.Theorems.Modal.Basic
```

This is acceptable given that:
- Each file is wrapped in a unique namespace (`Cslib.Logic.Theorems.Modal.S5`)
- The opened namespaces are all from the same library
- Name collisions are unlikely

No action needed.

---

## 7. Cross-Cutting Patterns

### 7.1 Systematic Pattern: Explicit `@` for Instance Resolution

Throughout the theorem files, many proofs use explicit `@` notation to help Lean resolve instances:
```lean
@theorem_flip F _ _ S _ _ ...
@double_negation F _ _ S _ _ ...
@lce_imp F _ _ S _ _ ...
```

This is a systematic pattern driven by the polymorphic typeclass design. It could potentially be mitigated by:
- Adding more type aliases (like the existing `diamond'`, `neg'`)
- Using `variable` blocks more aggressively to fix instance parameters

However, changing this would be a significant refactor with risk of breaking things. **No action recommended for this PR.**

### 7.2 Systematic Pattern: F/G/H Symmetry

The temporal theorems follow a systematic F/G (future) and P/H (past) duality pattern. Every future theorem has a past counterpart. This is well-implemented and consistently applied.

### 7.3 Module Keyword and @[expose] public section

All files correctly use the `module` keyword and `@[expose] public section` pattern. This is consistent across the entire PR.

---

## 8. Summary of Actionable Items

### Must Fix (Before PR Merge)

None. All files build, have zero sorries, and are functionally correct.

### Should Fix (Improve Quality)

| # | File | Line | Issue |
|---|------|------|-------|
| 1 | Connectives.lean | 280 | Remove draft comment "wait, this does not type-check" |
| 2 | InferenceSystem.lean | 11 | Replace empty `/-! -/` with actual module docstring |
| 3 | S5.lean | multiple | Remove double blank lines (6 instances) |
| 4 | TemporalDerived.lean | multiple | Remove double blank lines (6 instances) |

### Could Fix (Style/Polish)

| # | File | Line | Issue |
|---|------|------|-------|
| 5 | S5.lean | 445,503,513,546 | Standardize variable names `A B` to `φ ψ` |
| 6 | S5.lean | 71-74 | Use or remove unused `diamond'`/`iff'` abbreviations |
| 7 | Combinators.lean | 89,128,139 | Consider renaming `theorem_flip`/`theorem_app1`/`theorem_app2` |
| 8 | TemporalDerived.lean | 239,258 | Remove trailing `'` from `G_imp_trans'`/`H_imp_trans'` |
| 9 | Various | multiple | Remove `-- section` comments from unnamed `end` |
| 10 | ProofSystem.lean | 9-12 | Trim redundant imports |
| 11 | Modal/Basic.lean | 9 | Trim redundant `ProofSystem` import |
| 12 | Modal/S5.lean | 9-12 | Trim redundant imports |

### Deferred (Post-Merge)

| # | Issue |
|---|-------|
| 13 | Consider moving `Helpers/ListHelpers.lean` to `Foundations/Data/` |
| 14 | Consider using `diamond'`/`neg'`/`conj'` abbreviations more broadly to reduce proof verbosity |
| 15 | Add section comments to `theorem_app2` proof for readability |
| 16 | Add triviality note to `FUntilEquiv` docstring (matching `PSinceEquiv`) |

---

## 9. Overall Assessment

The `Foundations/Logic/` module is well-designed and well-implemented. The typeclass hierarchy (connectives -> axioms -> proof systems -> theorems) is clean and extensible. The polymorphic `abbrev` approach for axioms avoids typeclass diamonds while enabling code reuse across four logic levels. Documentation quality is above average. The only mandatory fixes are cosmetic (empty docstring, draft comment, double blank lines).
