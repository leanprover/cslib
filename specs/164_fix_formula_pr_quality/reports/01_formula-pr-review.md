# PR Quality Review: Formula.lean (Task 159 / Sub-PR 3.1)

**Task**: 164
**Date**: 2026-06-12
**Branch reviewed**: `pr3/temporal-formula` (based on `pr1/foundations-logic`)
**File**: `Cslib/Logics/Temporal/Syntax/Formula.lean` (549 lines)
**Comparison files**: `Cslib/Logics/Propositional/Defs.lean`, `Cslib/Logics/Modal/Basic.lean`, `Cslib/Foundations/Logic/Connectives.lean`

---

## Issue 1: Doc/Code Argument Order Mismatch [HIGH]

**Location**: Lines 24–27 (module doc), lines 48–76 (derived operators), lines 308–334 (complexity), lines 366–370 (next/prev), lines 390–412 (release/trigger/strongRelease/strongTrigger)

**Problem**: The doc comments claim standard temporal logic argument order for `U` and `S`, but the code reverses the arguments. Since `@[inherit_doc] scoped infix:40 " U " => Formula.untl` maps `a U b` to `untl a b`, the following mismatches exist:

| Operator | Doc comment | Code (via notation) | Standard LTL |
|----------|------------|-------------------|-------------|
| `someFuture φ` (line 62) | `F φ := ⊤ U φ` | `.untl φ .top` = `φ U ⊤` | `⊤ U φ` |
| `somePast φ` (line 70) | `P φ := ⊤ S φ` | `.snce φ .top` = `φ S ⊤` | `⊤ S φ` |
| `next φ` (line 366) | `X(φ) = ⊥ U φ` | `.untl φ .bot` = `φ U ⊥` | `⊥ U φ` |
| `prev φ` (line 369) | `Y(φ) = ⊥ S φ` | `.snce φ .bot` = `φ S ⊥` | `⊥ S φ` |
| `release φ ψ` (line 391) | `¬(¬φ U ¬ψ)` | `neg (untl (neg ψ) (neg φ))` = `¬(¬ψ U ¬φ)` | `¬(¬φ U ¬ψ)` |
| `strongRelease φ ψ` (line 407) | `ψ U (ψ ∧ φ)` | `untl (and ψ φ) ψ` = `(ψ ∧ φ) U ψ` | `ψ U (ψ ∧ φ)` |
| `strongTrigger φ ψ` (line 411) | `ψ S (ψ ∧ φ)` | `snce (and ψ φ) ψ` = `(ψ ∧ φ) S ψ` | `ψ S (ψ ∧ φ)` |

**Impact**: The file is purely syntactic (no semantics), so all proofs pass regardless of argument order. However:
1. Any reviewer familiar with LTL will flag the mismatch immediately
2. When semantics are added (future sub-PRs), `φ U ⊤` under standard semantics is trivially true and does NOT mean "eventually φ" — it would be a real bug
3. The complexity function (lines 308–334) pattern-matches on the reversed order, so it's internally consistent but would need updating too

**Fix options**:
- **(A) Swap derived operator arguments to match docs (RECOMMENDED)**: Change `someFuture φ` to `.untl .top φ`, etc. Update complexity pattern matches. All proofs still pass since they're structural.
- **(B) Rewrite all docs to match code**: Keep the code, but rewrite every doc comment to use the reversed convention and add a prominent note explaining the non-standard argument order.

Option A is recommended because it aligns with standard LTL conventions and the repo's own Connectives.lean documentation.

**Affected definitions** (code changes needed for option A):
- `Formula.someFuture` (line 64): `.untl φ .top` → `.untl .top φ`
- `Formula.somePast` (line 72): `.snce φ .top` → `.snce .top φ`
- `Formula.next` (line 366): `.untl φ .bot` → `.untl .bot φ`
- `Formula.prev` (line 370): `.snce φ .bot` → `.snce .bot φ`
- `Formula.release` (line 392): `untl (neg ψ) (neg φ)` → `untl (neg φ) (neg ψ)`
- `Formula.trigger` (line 396): `snce (neg ψ) (neg φ)` → `snce (neg φ) (neg ψ)`
- `Formula.strongRelease` (line 408): `untl (and ψ φ) ψ` → `untl ψ (and ψ φ)`
- `Formula.strongTrigger` (line 412): `snce (and ψ φ) ψ` → `snce ψ (and ψ φ)`
- Complexity pattern matches (lines 312–334): swap argument positions in all `untl`/`snce` patterns
- swapTemporal theorems (lines 452–494): re-check; may need proof adjustments

---

## Issue 2: Missing `## References` Section [MEDIUM]

**Location**: Module doc (lines 15–28)

**Problem**: Both peer files include a `## References` section citing foundational works:
- `Propositional/Defs.lean` line 39–41: cites Chagrov & Zakharyaschev 1997
- `Modal/Basic.lean` lines 22–26: cites Blackburn, de Rijke & Venema 2001

Formula.lean has no references. Temporal logic has well-established foundational references.

**Fix**: Add a `## References` section after `## Derived Temporal Operators`. Appropriate citations:
- Kamp, H. (1968). *Tense Logic and the Theory of Linear Order*. PhD thesis, UCLA.
- Gabbay, D., Pnueli, A., Shelah, S., and Stavi, J. (1980). On the temporal analysis of fairness.

Use Mathlib BibTeX format: `[Kamp1968]`, `[GabbayPnueliShelahStavi1980]`.

---

## Issue 3: Missing `iff` Derived Connective [LOW-MEDIUM]

**Location**: After line 60 (where `and` is defined)

**Problem**: `Propositional/Defs.lean` (line 76) defines `Proposition.iff`:
```lean
abbrev Proposition.iff (A B : Proposition Atom) : Proposition Atom :=
  (A.imp B).and (B.imp A)
```

The task 159 description explicitly lists `iff` as a derived connective, but it's absent from Formula.lean. The Connectives.lean `LukasiewiczDerived` class also documents `iff` as a standard derived connective pattern.

**Fix**: Add after `Formula.and`:
```lean
/-- Biconditional: φ₁ ↔ φ₂ := (φ₁ → φ₂) ∧ (φ₂ → φ₁) -/
abbrev Formula.iff (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  (φ₁.imp φ₂).and (φ₂.imp φ₁)
```

Add notation:
```lean
@[inherit_doc] scoped infix:30 " ↔ " => Formula.iff
```

---

## Issue 4: Bare-Letter Temporal Notation Risks [MEDIUM]

**Location**: Lines 84–87

**Problem**: The file registers single ASCII letters as scoped notation:
```lean
scoped prefix:40 "F" => Formula.someFuture
scoped prefix:40 "G" => Formula.allFuture
scoped prefix:40 "P" => Formula.somePast
scoped prefix:40 "H" => Formula.allPast
```

When `Cslib.Logic.Temporal` is opened, any identifier `F`, `G`, `P`, or `H` at expression position could be parsed as a temporal operator instead of a variable/function. The comparison files use Unicode for their modalities (`◇`, `□` in Modal/Basic.lean), which avoids conflicts.

**Fix options**:
- **(A)** Use Unicode mathematical bold: `𝐅`, `𝐆`, `𝐏`, `𝐇`
- **(B)** Use Unicode double-struck: `𝔽`, `𝔾`, `ℙ`, `ℍ` (but `ℙ` and `ℍ` conflict with Mathlib)
- **(C)** Keep bare letters but add prominent documentation warning about shadowing

Option A is cleanest. If the author prefers ASCII, option C is acceptable but should include a section comment explaining the tradeoff.

---

## Issue 5: No `Bot`/`Top` Mathlib Instances [LOW]

**Location**: After line 95 (TemporalConnectives instance)

**Problem**: `Propositional/Defs.lean` (lines 79–80) registers Mathlib's `Bot` and `Top`:
```lean
instance : Bot (Proposition Atom) := ⟨.bot⟩
instance : Top (Proposition Atom) := ⟨.top⟩
```

Formula.lean registers `TemporalConnectives` (which extends `HasBot`, `HasImp`, `HasUntil`, `HasSince`) but not Mathlib's `Bot`/`Top`. This means standard `⊥`/`⊤` notation from Mathlib won't resolve for `Formula Atom` outside the scoped notation.

**Fix**: Add before `end Cslib.Logic.Temporal` (line 96):
```lean
instance : Bot (Formula Atom) := ⟨.bot⟩
instance : Top (Formula Atom) := ⟨.top⟩
```

---

## Issue 6: Second Half Outside `@[expose] public section` [LOW]

**Location**: Lines 98–549

**Problem**: Lines 30–96 are inside `@[expose] public section`, but everything after line 96 (countability instances, BEq laws, complexity, temporal depth, derived operators, swapTemporal, atoms) is outside. In `Propositional/Defs.lean`, the entire file is within the public section block.

**Impact**: Definitions in the second half may not be accessible from downstream files that expect public exports. The `Encodable`, `Countable`, `Infinite`, `Denumerable`, `ReflBEq`, `LawfulBEq` instances, plus `complexity`, `temporalDepth`, `swapTemporal`, `atoms`, and all derived operators (`next`, `prev`, `release`, `trigger`, `weakUntil`, `weakSince`, `strongRelease`, `strongTrigger`, `always`, `sometimes`, `weakFuture`, `weakPast`) would not be publicly exported.

**Fix**: Either wrap the second half in its own `@[expose] public section` block, or restructure so the entire file is within one block (matching the Propositional pattern).

---

## Issue 7: Redundant `open` Before `namespace` [COSMETIC]

**Location**: Lines 111–113

**Problem**:
```lean
open Cslib.Logic.Temporal

namespace Cslib.Logic.Temporal
```

The `namespace` declaration already opens the namespace, making the preceding `open` redundant.

**Fix**: Remove line 111 (`open Cslib.Logic.Temporal`).

---

## Summary

| # | Issue | Severity | Effort | Files Changed |
|---|-------|----------|--------|---------------|
| 1 | Argument order mismatch | HIGH | Medium | Formula.lean (15+ defs, complexity, proofs) |
| 2 | Missing references | MEDIUM | Low | Formula.lean (module doc) |
| 3 | Missing `iff` connective | LOW-MEDIUM | Low | Formula.lean (1 abbrev + 1 notation) |
| 4 | Bare-letter notation | MEDIUM | Low | Formula.lean (4 notation lines) |
| 5 | Missing `Bot`/`Top` instances | LOW | Trivial | Formula.lean (2 instances) |
| 6 | Outside `@[expose] public section` | LOW | Low | Formula.lean (section restructure) |
| 7 | Redundant `open` | COSMETIC | Trivial | Formula.lean (delete 1 line) |

All changes are to a single file (`Formula.lean`) on the `pr3/temporal-formula` branch. After fixes, full CI pipeline must pass: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake test`, `lake shake`.
