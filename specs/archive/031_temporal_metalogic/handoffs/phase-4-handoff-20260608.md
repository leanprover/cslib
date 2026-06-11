# Phase 4 Handoff: Soundness (In Progress)

## Immediate Next Action

Fix remaining compilation errors in `Cslib/Logics/Temporal/Metalogic/Soundness.lean`.

## Current State

- **Phases 1-2**: COMPLETED (DerivationTree.lean, DeductionTheorem.lean compile clean)
- **Phase 3 (MCS)**: NOT STARTED
- **Phase 4 (Soundness)**: IN PROGRESS -- file exists but has ~10 compilation errors
- **Phases 5-6**: NOT STARTED

## Key Decisions Made

1. Named temporal Deriv as `Temporal.Deriv` and `Temporal.ThDerivable` (with `set_option linter.dupNamespace false`) to avoid collision with existing `Temporal.Derivable` in ProofSystem/Derivable.lean.

2. Temporal `DerivationTree.weakening` uses `h : Gamma ⊆ Delta` (List.Subset with implicit first arg) unlike modal which uses `h : ∀ x ∈ Gamma, x ∈ Delta`. All proof terms adapted.

3. Temporal axiom naming: `imp_k` = distribution (modal `implyS`), `imp_s` = weakening (modal `implyK`). Swapped from modal convention.

4. For soundness, `sat_and_iff` and `sat_or_iff` helper theorems convert between raw `Satisfies` and Lean `∧`/`∨` since `Formula.and` / `Formula.or` are encoded as nested `imp`/`bot`.

5. `swap_temporal` duality handled via `dualModel` on `OrderDual D` with `swap_temporal_dual` lemma.

## Remaining Soundness Errors

The `axiom_sound` proof has ~10 remaining type mismatch errors:
- `linear_since` case: Argument order issues in `sat_and_iff` applications (recently fixed but untested)
- `temp_linearity` / `temp_linearity_past` cases: `simp only [sat_and_iff/sat_or_iff]` doesn't work on hypotheses; need explicit `.mp` calls like `linear_until` case
- `until_F` / `since_P` / `F_until_equiv` / `P_since_equiv`: `simp only` with `Satisfies._iff` lemmas fails on abbreviation-expanded formulas
- `swap_temporal_dual`: Failed synthesis of `Nontrivial` or similar instances for `OrderDual`
- All remaining `simp only [Satisfies.xxx_iff] at hypothesis` calls should be replaced with explicit `have := (Satisfies.xxx_iff M t ...).mp hypothesis` pattern

## Pattern for Fixing Remaining Axiom Cases

The working pattern (used in `linear_until`):
```lean
intro hconj
have ⟨h1, h2⟩ := (sat_and_iff M t X Y).mp hconj
obtain ⟨s, hlt, hev, hg⟩ := h1
-- ... work with extracted witnesses
exact Or.inl (Or.inr ⟨...⟩)  -- for disjunctions
```

The FAILING pattern:
```lean
simp only [sat_and_iff] at hconj
simp only [Satisfies.untl_iff] at h1 h2
```

## Files Modified

- `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean` -- Phase 1, CLEAN
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` -- Phase 2, CLEAN
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean` -- Phase 4, HAS ERRORS

## Session

Session: sess_1780982747_80da4d_31
