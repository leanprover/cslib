# Phase 6 Completion Handoff

## Status
- Phases 1-6 COMPLETED (Defs, FormulaOps, IntHelpers, Duality, Distributivity, NegationEquiv)
- Next: Phase 7 (Eliminations.lean, 902 lines source)

## Key Decisions Made

1. **Scoped notation conflict**: `F`, `G`, `H`, `P`, `S`, `U` are all scoped notation in `Cslib.Logic.Bimodal`. This means:
   - Variable names using these letters (e.g., `fun s =>`) get parsed as formula operators
   - Use `w`, `x`, `r`, `m`, `u` etc. as variable names instead
   - For NegationEquiv: used `rw [int_truth_neg, int_truth_or, int_truth_all_future]` to reduce goal to clean propositional form, then worked with `push_neg` and pattern matching
   - Use `Cslib.Logic.Bimodal.Formula.neg` etc. fully qualified when needed in type signatures

2. **Freshness**: Replaced `Atom.mk_fresh_injective` with `Finset.exists_notMem` from Mathlib (`Mathlib.Data.Set.Finite.Basic`)

3. **Int helpers**: Added `Int.exists_least_above'` and `Int.exists_greatest_below'` (non-decidable versions using `Classical.decPred`)

4. **simp only [int_truth]**: Fully unfolds all formula constructors including abbrevs. After this, `or`/`and`/`neg` become raw implications, so `left`/`right`/`rcases` don't work. Instead use `rw` with specific simp lemmas (int_truth_neg, int_truth_or, etc.) to control reduction.

5. **Copyright**: Uses `2026 Benjamin Brastmckie` format

## Next Action
Port Eliminations.lean (Phase 7). Source: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/WeakCanonical/Separation/Eliminations.lean` (902 lines, 8 elimination cases).

## Proof Strategy for NegationEquiv (completed)
- Used `rw [int_truth_neg, int_truth_or, int_truth_all_future]` to get clean `¬ ... ↔ ... ∨ ...` form
- Then `by_cases` on the globally-negated subgoal
- `push_neg` to get existential witnesses
- `Int.exists_least_above'` / `Int.exists_greatest_below'` for well-ordering arguments
- `rw [int_truth_and, int_truth_neg, int_truth_neg]` at specific hypotheses/goals to convert between `int_truth` and `¬`
