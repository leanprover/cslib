# Phase 8 Handoff — DedekindZ Cases.lean Remaining

## Current State
- **Phases 1-7**: COMPLETED and committed
- **Phase 8**: IN PROGRESS — QLemma.lean done, Cases.lean not started
- **Phases 9-15**: NOT STARTED

## Files Completed This Cycle
1. `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean` — Phase 7
2. `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean` — Phase 8 partial

## Immediate Next Action
Port `Cases.lean` (1768 lines source) to `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean`.

## Critical Porting Patterns (discovered this cycle)

### 1. `int_truth_and_iff` / `int_truth_or_iff` / `int_truth_neg_iff` replacements
- Source uses `int_truth_and_iff.mp`, `int_truth_or_iff.mpr`, etc.
- Cslib uses `(int_truth_and M t _ _).mp`, `(int_truth_or M t _ _).mpr`, etc.
- The cslib lemmas take explicit `M t φ ψ` arguments (they are `@[simp]` lemmas)

### 2. `subst` variable elimination
- After `subst hut` where `hut : u = t`, Lean 4 eliminates `t` and replaces it with `u`
- Any subsequent reference to `t` (like `int_truth_or M t _ _`) must use `u` instead
- Fix: replace `M t` with `M u` (or whichever variable survives) after subst
- Alternative: use `rcases hut with rfl` which may behave differently

### 3. `simp only [int_truth_and, int_truth_neg, int_truth_all_past]` ordering
- `int_truth_neg` can fire before `int_truth_and`, breaking the `and` pattern
- In forward proofs: use `rw [int_truth_and, int_truth_neg, int_truth_neg]` then `rw [int_truth_all_past]` OR construct proof terms directly
- In backward proofs: use `have ... := (int_truth_and M t _ _).mp hand` to manually destructure

### 4. Formula abbreviations
- `Formula.and`, `Formula.neg`, `Formula.or` are all `abbrev`s in cslib
- They unfold to `imp`/`bot` patterns automatically
- Don't include them in `simp` calls (triggers "unused simp arg" warnings)
- Use `set_option linter.unusedSimpArgs false` at file level

### 5. Linter options for porting files
```lean
set_option linter.style.emptyLine false
set_option linter.style.longLine false  
set_option linter.unusedSimpArgs false
```

### 6. `push_neg` deprecation warning
- `push_neg` is deprecated in favor of `push Not`
- Both still work but `push_neg` produces a warning

## Remaining Phases

| Phase | File(s) | Source Lines | Status |
|-------|---------|-------------|--------|
| 8 | DedekindZ/Cases.lean | 1768 | IN PROGRESS (QLemma done) |
| 9 | NormalForm.lean | 554 | NOT STARTED |
| 10 | TemporalClosure.lean | 674 | NOT STARTED |
| 11 | Hierarchy/HierarchyDefs.lean | 1051 | NOT STARTED |
| 12 | Hierarchy/HierarchyCaseSep.lean | 655 | NOT STARTED |
| 13 | Hierarchy/HierarchyInduction.lean + HierarchyCompletion.lean | 1437 + 981 | NOT STARTED |
| 14 | SeparationThm.lean + DualEliminations.lean | 354 + 101 | NOT STARTED |
| 15 | Barrel import + final verification | - | NOT STARTED |

## Source Directory
`/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/WeakCanonical/Separation/`
