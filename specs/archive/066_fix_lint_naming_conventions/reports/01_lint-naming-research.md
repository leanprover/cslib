# Research Report: Naming Convention Violations and Rename Strategy

**Task**: 66 - fix_lint_naming_conventions
**Session**: sess_1781063497_2c7653
**Date**: 2026-06-10

## Executive Summary

The codebase has **16 unique snake_case `def`/`abbrev` identifiers** across temporal operator definitions that violate Lean 4 / Mathlib naming conventions. These are defined in 6 source files and referenced across **95 files** with approximately **2,903 total references** (including comments and doc strings). Additionally, there are **~162 theorem/lemma names** that incorporate these snake_case identifiers and will need compound renaming.

**Key finding**: Mathlib convention uses snake_case for theorem/lemma names but lowerCamelCase for `def`/`abbrev` names. The `defsWithUnderscore` linter in `Mathlib.Tactic.Linter.Style` enforces this. Only the 16 def/abbrev names and the theorem names that embed them need renaming.

## 1. Naming Convention Rules

### Lean 4 / Mathlib Standard

| Declaration Type | Convention | Example |
|-----------------|------------|---------|
| `def`, `abbrev` | lowerCamelCase | `someFuture`, `swapTemporal` |
| `theorem`, `lemma` | snake_case (encoding conclusion) | `swap_temporal_involution` |
| `structure`, `class`, `inductive` | UpperCamelCase | `Formula`, `TemporalConnectives` |

### Linter Support

- **`defsWithUnderscore`** (Mathlib env_linter): Checks `def`/`abbrev` names for underscores. Reports: "The definition contains an underscore. This almost surely violates mathlib's naming convention; use lowerCamelCase or UpperCamelCase instead."
- Enabled via `weak.linter.mathlibStandardSet = true` in `lakefile.toml` (already configured)
- **No automated rename tool exists** -- Lean LSP has `lean_references` for finding usages but no rename refactoring; `lean_code_actions` only provides TryThis suggestions

### Theorem Name Convention for Renamed Defs

When a def is renamed from `some_future` to `someFuture`, theorem names that reference it should update the def portion while keeping the snake_case convention for the theorem name structure:

```
swap_temporal_some_future  ->  swapTemporal_someFuture
atoms_swap_temporal        ->  atoms_swapTemporal
neg_bigconj_def            ->  negBigconj_def
```

## 2. Complete Identifier Inventory

### Tier 1: Core Temporal Operators (5 identifiers, ~2,903 references across 95 files)

| Current Name | New Name | Def Sites | Reference Count | Files |
|-------------|----------|-----------|-----------------|-------|
| `some_future` | `someFuture` | 3 (Temporal, Bimodal, ExtFormula) | ~581 | 63 |
| `all_future` | `allFuture` | 3 | ~701 | 78 |
| `some_past` | `somePast` | 3 | ~495 | 56 |
| `all_past` | `allPast` | 3 | ~611 | 70 |
| `swap_temporal` | `swapTemporal` | 3 | ~515 | 33 |

### Tier 2: Derived Temporal Operators (7 identifiers, ~31 references)

| Current Name | New Name | Def Sites | Reference Count | Files |
|-------------|----------|-----------|-----------------|-------|
| `weak_future` | `weakFuture` | 1 (Temporal) | ~3 | 2 |
| `weak_past` | `weakPast` | 1 (Temporal) | ~3 | 2 |
| `weak_until` | `weakUntil` | 1 (Temporal) | ~1 | 1 |
| `weak_since` | `weakSince` | 1 (Temporal) | ~1 | 1 |
| `strong_release` | `strongRelease` | 1 (Temporal) | ~7 | 1 |
| `strong_trigger` | `strongTrigger` | 1 (Temporal) | ~7 | 1 |
| `neg_bigconj` | `negBigconj` | 2 (Temporal, Foundations) | ~9 | 2 |

### Tier 3: Bimodal Derived Defs (4 identifiers, ~4 references)

| Current Name | New Name | Def Sites | Files |
|-------------|----------|-----------|-------|
| `weak_future_left` | `weakFutureLeft` | 1 | 1 |
| `weak_future_right` | `weakFutureRight` | 1 | 1 |
| `weak_past_left` | `weakPastLeft` | 1 | 1 |
| `weak_past_right` | `weakPastRight` | 1 | 1 |

### Theorem Names Requiring Compound Renaming

| Def Name | Theorem Names Affected |
|----------|----------------------|
| `swap_temporal` | ~28 theorem names (e.g., `swap_temporal_involution`, `swap_temporal_neg`, ...) |
| `all_future` | ~41 theorem names (e.g., `all_future_all_future`, `all_future_iff`, ...) |
| `all_past` | ~39 theorem names |
| `some_future` | ~25 theorem names |
| `some_past` | ~25 theorem names |
| `neg_bigconj` | ~2 theorem names |
| `strong_release`, `strong_trigger` | ~1 each |

**Total**: ~162 theorem/lemma names need compound renaming.

## 3. Definition Sites (Complete)

### File 1: `Cslib/Logics/Temporal/Syntax/Formula.lean`

11 snake_case defs:
- Line 63: `abbrev Formula.some_future`
- Line 67: `abbrev Formula.all_future`
- Line 71: `abbrev Formula.some_past`
- Line 75: `abbrev Formula.all_past`
- Line 373: `def weak_future`
- Line 377: `def weak_past`
- Line 399: `def weak_until`
- Line 403: `def weak_since`
- Line 407: `def strong_release`
- Line 411: `def strong_trigger`
- Line 428: `def swap_temporal`

### File 2: `Cslib/Logics/Temporal/Syntax/BigConj.lean`

1 snake_case def:
- Line 38: `def neg_bigconj`

### File 3: `Cslib/Logics/Bimodal/Syntax/Formula.lean`

5 snake_case defs:
- Line 66: `abbrev Formula.some_future`
- Line 70: `abbrev Formula.all_future`
- Line 74: `abbrev Formula.some_past`
- Line 78: `abbrev Formula.all_past`
- Line 127: `def swap_temporal`

### File 4: `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean`

4 snake_case defs:
- Line 348: `def weak_future_left`
- Line 352: `def weak_future_right`
- Line 356: `def weak_past_left`
- Line 360: `def weak_past_right`

### File 5: `Cslib/Foundations/Logic/Theorems/BigConj.lean`

1 snake_case def:
- Line 56: `def neg_bigconj`

### File 6: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean`

5 snake_case defs:
- Line 83: `def some_future` (on ExtFormula)
- Line 86: `def some_past` (on ExtFormula)
- Line 89: `def all_future` (on ExtFormula)
- Line 92: `def all_past` (on ExtFormula)
- Line 101: `def swap_temporal` (on ExtFormula)

## 4. Notation Bindings (Must Update)

These scoped notation declarations reference the snake_case defs and must be updated:

```lean
-- Temporal/Syntax/Formula.lean (lines 84-87):
@[inherit_doc] scoped prefix:40 "F" => Formula.some_future    -- -> Formula.someFuture
@[inherit_doc] scoped prefix:40 "G" => Formula.all_future     -- -> Formula.allFuture
@[inherit_doc] scoped prefix:40 "P" => Formula.some_past      -- -> Formula.somePast
@[inherit_doc] scoped prefix:40 "H" => Formula.all_past       -- -> Formula.allPast

-- Bimodal/Syntax/Formula.lean (lines 89-92):
@[inherit_doc] scoped prefix:40 "F" => Formula.some_future    -- -> Formula.someFuture
@[inherit_doc] scoped prefix:40 "G" => Formula.all_future     -- -> Formula.allFuture
@[inherit_doc] scoped prefix:40 "P" => Formula.some_past      -- -> Formula.somePast
@[inherit_doc] scoped prefix:40 "H" => Formula.all_past       -- -> Formula.allPast
```

## 5. Programmatic Rename Approach

### Recommended: `sed` Batch Replacement

**Why `sed` is safe** for this rename:
1. **No substring false positives**: None of the 16 identifiers appear as substrings of unrelated identifiers (verified by grep)
2. **Consistent word boundaries**: All identifiers are preceded by `.`, space, `(`, or start-of-line, and followed by space, `.`, `)`, newline, or `,`
3. **No scoping issues**: Each identifier name is globally unique within the project (no local variables shadow these names)

**Why not Lean LSP rename**: Lean LSP does not provide rename refactoring. The `lean_references` tool can find usages but cannot perform renames.

**Why not `@[deprecated]`**: Migration aliases add complexity and require maintaining two names. Since this is a private project (not a library consumed by external users), a clean batch rename is preferable.

### sed Command Strategy

The rename must be done in a specific order to avoid partial replacements. For compound names, replace longest matches first:

```bash
# Phase 1: Compound theorem names (longest first to avoid partial matches)
# Example: swap_temporal_some_future must be done BEFORE swap_temporal and some_future
sed -i 's/swap_temporal_some_future/swapTemporal_someFuture/g'
sed -i 's/swap_temporal_some_past/swapTemporal_somePast/g'
sed -i 's/swap_temporal_all_future/swapTemporal_allFuture/g'
sed -i 's/swap_temporal_all_past/swapTemporal_allPast/g'
sed -i 's/swap_temporal_strong_release/swapTemporal_strongRelease/g'
sed -i 's/swap_temporal_strong_trigger/swapTemporal_strongTrigger/g'

# Phase 2: Compound names with remaining identifiers
sed -i 's/some_future_all_future/someFuture_allFuture/g'
# ... etc.

# Phase 3: Simple def names (after all compounds are handled)
sed -i 's/some_future/someFuture/g'
sed -i 's/all_future/allFuture/g'
# ... etc.
```

### Critical Ordering Rules

1. **Longest compound first**: `swap_temporal_some_future` before `swap_temporal` or `some_future`
2. **Definition files first**: Rename in definition files, then downstream
3. **Build verification**: Run `lake build` after each definition file is renamed (the file and its direct dependents)

## 6. Recommended Execution Order

### Phase 1: Tier 2 Identifiers (Low Impact, Low Risk)

Rename the low-reference identifiers first as a test:
1. `weak_until` -> `weakUntil` (1 file, 1 ref)
2. `weak_since` -> `weakSince` (1 file, 1 ref)
3. `strong_release` -> `strongRelease` (1 file, 7 refs)
4. `strong_trigger` -> `strongTrigger` (1 file, 7 refs)
5. `weak_future` -> `weakFuture` (2 files, 3 refs)
6. `weak_past` -> `weakPast` (2 files, 3 refs)
7. Bimodal: `weak_future_left/right`, `weak_past_left/right` (1 file, 4 refs)
8. `neg_bigconj` -> `negBigconj` (2 files, 9 refs)

Verify: `lake build`

### Phase 2: Tier 1 Identifiers (High Impact)

Rename in batch since they are deeply interdependent:
1. Collect ALL compound theorem names containing these identifiers
2. Generate a comprehensive sed script replacing longest matches first
3. Run sed across all 95 affected files simultaneously
4. Run `lake build` to verify

### Implementation Script Template

```bash
#!/bin/bash
# Rename all snake_case temporal identifiers to lowerCamelCase
# Run from project root

FILES=$(find Cslib -name "*.lean" | grep -v '.lake/')

# Phase 1: Compound theorem names (longest first)
# swap_temporal_* compounds
sed -i 's/swap_temporal_strong_release/swapTemporal_strongRelease/g' $FILES
sed -i 's/swap_temporal_strong_trigger/swapTemporal_strongTrigger/g' $FILES
sed -i 's/swap_temporal_some_future/swapTemporal_someFuture/g' $FILES
sed -i 's/swap_temporal_some_past/swapTemporal_somePast/g' $FILES
sed -i 's/swap_temporal_all_future/swapTemporal_allFuture/g' $FILES
sed -i 's/swap_temporal_all_past/swapTemporal_allPast/g' $FILES
# other swap_temporal_* theorems
sed -i 's/swap_temporal_involution/swapTemporal_involution/g' $FILES
sed -i 's/swap_temporal_neg/swapTemporal_neg/g' $FILES
sed -i 's/swap_temporal_diamond/swapTemporal_diamond/g' $FILES
sed -i 's/swap_temporal_next/swapTemporal_next/g' $FILES
sed -i 's/swap_temporal_prev/swapTemporal_prev/g' $FILES
sed -i 's/swap_temporal_int_truth/swapTemporal_int_truth/g' $FILES
sed -i 's/swap_temporal_derives/swapTemporal_derives/g' $FILES
sed -i 's/swap_temporal_dual/swapTemporal_dual/g' $FILES
sed -i 's/swap_temporal_subst/swapTemporal_subst/g' $FILES
sed -i 's/atoms_swap_temporal/atoms_swapTemporal/g' $FILES
sed -i 's/embedFormula_swap_temporal/embedFormula_swapTemporal/g' $FILES
sed -i 's/substFormula_swap_temporal/substFormula_swapTemporal/g' $FILES
sed -i 's/substFreshWith_swap_temporal/substFreshWith_swapTemporal/g' $FILES
sed -i 's/unembed_swap_temporal/unembed_swapTemporal/g' $FILES
sed -i 's/provEquiv_swap_temporal_congr/provEquiv_swapTemporal_congr/g' $FILES

# Compound: *_some_future / *_some_past / *_all_future / *_all_past
# (theorem names that use these as components)
# These are handled by the simple replacements below since they don't
# conflict with each other -- some_future is never a prefix of some_future_X

# Phase 2: Compound def names
sed -i 's/weak_future_left/weakFutureLeft/g' $FILES
sed -i 's/weak_future_right/weakFutureRight/g' $FILES
sed -i 's/weak_past_left/weakPastLeft/g' $FILES
sed -i 's/weak_past_right/weakPastRight/g' $FILES
sed -i 's/strong_release/strongRelease/g' $FILES
sed -i 's/strong_trigger/strongTrigger/g' $FILES
sed -i 's/weak_future/weakFuture/g' $FILES
sed -i 's/weak_past/weakPast/g' $FILES
sed -i 's/weak_until/weakUntil/g' $FILES
sed -i 's/weak_since/weakSince/g' $FILES
sed -i 's/neg_bigconj/negBigconj/g' $FILES

# Phase 3: Core def names (MUST be after all compounds)
sed -i 's/swap_temporal/swapTemporal/g' $FILES
sed -i 's/some_future/someFuture/g' $FILES
sed -i 's/all_future/allFuture/g' $FILES
sed -i 's/some_past/somePast/g' $FILES
sed -i 's/all_past/allPast/g' $FILES

# Phase 4: Verify
lake build
```

## 7. Risk Assessment

### Low Risk
- `weak_until`, `weak_since`, `strong_release`, `strong_trigger`: Very few references, contained to 1-2 files
- `neg_bigconj`: Only 2 definition sites, 9 references

### Medium Risk
- `weak_future`, `weak_past`: Few references but naming is used in Bimodal theorem names
- Bimodal `weak_future_left/right`, `weak_past_left/right`: Contained to one file

### High Risk
- `some_future`, `all_future`, `some_past`, `all_past`, `swap_temporal`: 500-700 references each, 33-78 files each. Batch sed replacement is safe (verified no false positives) but the sheer volume means any mistake would be hard to diagnose.

### Mitigation
1. Create a git branch before starting
2. Run `lake build` after the full rename to catch any missed references
3. The sed approach is all-or-nothing -- partial renames would break the build since notation bindings reference the old names

## 8. Scope Clarification

The task description mentions "19 snake_case identifiers" and "PR-scope files (Temporal/Propositional)". The actual scope is:

- **16 unique snake_case def/abbrev identifiers** (not 19 -- some are defined in multiple formula types)
- **6 definition files** (not just 2)
- **95 files affected** (spanning Temporal, Bimodal, Foundations, and ConservativeExtension)
- **~2,903 textual references** to rename
- **~162 theorem names** containing these identifiers that need compound renaming

The scope extends well beyond "Temporal/Propositional" because:
1. Bimodal logic has its own `Formula` type with identical operator names
2. ExtFormula (ConservativeExtension) defines its own copies
3. Foundations BigConj defines a generic `neg_bigconj`
4. Temporal operator references permeate the entire metalogic (soundness, completeness, separation)

## 9. Additional Snake_Case Defs Outside Task Scope

Beyond the 16 temporal operator identifiers, there are approximately **273 additional snake_case def/abbrev names** across the project (in areas like DeductionTheorem, MCSProperties, RestrictedMCS, Soundness, etc.). These are NOT in scope for this task but represent future lint cleanup work. Examples:

- `deduction_theorem`, `deduction_axiom`, `deduction_mp` (Bimodal/Temporal DeductionTheorem)
- `bimodal_lindenbaum`, `bimodal_negation_complete` (MaximalConsistent)
- `restricted_lindenbaum`, `restricted_mcs_from_formula` (RestrictedMCS)
- `is_valid`, `valid_at_triple`, `truth_at_swap_swap` (Soundness)
- `imp_trans`, `lce_imp`, `rce_imp` (PropositionalHelpers)
- `embed_forward`, `embed_backward`, `discrete_embed` (Chronicle)
- Many more in Chronicle, Frame, Separation, Decidability modules

These would require a separate task with their own dependency analysis.
