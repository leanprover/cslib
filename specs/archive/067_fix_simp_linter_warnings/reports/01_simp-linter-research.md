# Task 67: Fix @[simp] Linter Warnings -- Research Report

**Session**: sess_1781063701_dc65b7_67
**Date**: 2026-06-09
**Scope**: 7 `@[simp]` linter warnings across 2 files

## Summary

All 7 warnings stem from the same root cause: derived connectives (`neg`, `some_future`, `some_past`, `all_future`, `all_past`) are defined as `abbrev`, making them transparently unfold during simp. When a simp lemma's LHS references an `abbrev`-defined connective, simp unfolds the `abbrev` first and then applies existing simp lemmas for the primitive constructors. The simpNF linter flags this as "LHS simplifies from" (meaning the LHS can be further simplified before the lemma even matches).

## Warning Analysis

### File 1: `Cslib/Logics/Temporal/Semantics/Satisfies.lean`

#### 1. `neg_iff` (line 112-116)

- **Current LHS**: `Satisfies M t (Formula.neg phi)`
- **Current RHS**: `not (Satisfies M t phi)`
- **Why flagged**: `Formula.neg` is `abbrev` for `.imp phi .bot`. The LHS unfolds to `Satisfies M t (.imp phi .bot)`, which `imp_iff` (an existing `@[simp]` lemma) simplifies to `Satisfies M t phi -> Satisfies M t .bot` = `Satisfies M t phi -> False` = `not (Satisfies M t phi)`. So the LHS "simplifies from" via `imp_iff`.
- **Warning type**: LHS simplifies from
- **Downstream usage**: Zero explicit usages outside definition file.

#### 2. `some_future_iff` (line 127-137)

- **Current LHS**: `Satisfies M t (Formula.some_future phi)`
- **Current RHS**: `exists s, t < s /\ Satisfies M s phi`
- **Why flagged**: `Formula.some_future` is `abbrev` for `.untl phi .top` = `.untl phi (.imp .bot .bot)`. The LHS unfolds to `Satisfies M t (.untl phi (.imp .bot .bot))`, which `untl_iff` simplifies to `exists s, t < s /\ Satisfies M s phi /\ forall r, t < r -> r < s -> Satisfies M r (.imp .bot .bot)`. The guard part `Satisfies M r (.imp .bot .bot)` simplifies to `True` (via `imp_iff`), making the whole guard trivially satisfied. So simp can prove the full equivalence from existing lemmas.
- **Warning type**: LHS simplifies from / simp can prove
- **Downstream usage**: Heavy usage in Soundness.lean (18 references) -- all via `simp only [Satisfies.some_future_iff]` or explicit `.mp`/`.mpr` calls.

#### 3. `some_past_iff` (line 140-150)

- **Current LHS**: `Satisfies M t (Formula.some_past phi)`
- **Current RHS**: `exists s, s < t /\ Satisfies M s phi`
- **Why flagged**: Same pattern as `some_future_iff`. `Formula.some_past` is `abbrev` for `.snce phi .top` = `.snce phi (.imp .bot .bot)`. The LHS unfolds and `snce_iff` + `imp_iff` handle it.
- **Warning type**: LHS simplifies from / simp can prove
- **Downstream usage**: Heavy usage in Soundness.lean (14 references) -- all via `simp only` or explicit `.mp`/`.mpr`.

#### 4. `all_future_iff` (line 153-164)

- **Current LHS**: `Satisfies M t (Formula.all_future phi)`
- **Current RHS**: `forall s, t < s -> Satisfies M s phi`
- **Why flagged**: `Formula.all_future` is `abbrev` for `.neg (.some_future (.neg phi))` = `.imp (.untl (.imp phi .bot) (.imp .bot .bot)) .bot`. The LHS unfolds through multiple layers of abbrevs and existing simp lemmas handle the primitive constructors.
- **Warning type**: LHS simplifies from / simp can prove
- **Downstream usage**: 1 reference in Soundness.lean via `simp only [Satisfies.all_future_iff]`.

#### 5. `all_past_iff` (line 167-177)

- **Current LHS**: `Satisfies M t (Formula.all_past phi)`
- **Current RHS**: `forall s, s < t -> Satisfies M s phi`
- **Why flagged**: Same pattern as `all_future_iff` but with `snce` instead of `untl`.
- **Warning type**: LHS simplifies from / simp can prove
- **Downstream usage**: Zero explicit usages outside definition file (but likely needed in future TruthLemma work).

### File 2: `Cslib/Logics/Propositional/Embedding.lean`

#### 6. `PL.Proposition.toModal_neg` (line 73-75)

- **Current LHS**: `(PL.Proposition.neg phi).toModal`
- **Current RHS**: `Modal.Proposition.neg phi.toModal`
- **Why flagged**: `PL.Proposition.neg` is `abbrev` for `.imp phi .bot`. The LHS unfolds to `(PL.Proposition.imp phi .bot).toModal`, which `toModal_imp` (existing `@[simp]`) simplifies to `Modal.Proposition.imp phi.toModal (.bot).toModal`, and then `toModal_bot` simplifies to `Modal.Proposition.imp phi.toModal Modal.Proposition.bot` = `Modal.Proposition.neg phi.toModal` (by abbrev).
- **Warning type**: LHS simplifies from
- **Downstream usage**: Zero usages outside definition file.

#### 7. `PL.Proposition.toTemporal_neg` (line 88-90)

- **Current LHS**: `(PL.Proposition.neg phi).toTemporal`
- **Current RHS**: `Temporal.Formula.neg phi.toTemporal`
- **Why flagged**: Same pattern as `toModal_neg` but for temporal embedding. `neg` unfolds, then `toTemporal_imp` + `toTemporal_bot` handle it.
- **Warning type**: LHS simplifies from
- **Downstream usage**: Zero usages outside definition file.

## Recommended Fix

### Approach: Remove `@[simp]` attribute from all 7 lemmas

**Rationale**:

1. **The lemmas are redundant in the simp set.** Since all the derived connectives are `abbrev`, simp automatically unfolds them and applies the primitive constructor simp lemmas (`imp_iff`, `untl_iff`, `snce_iff`, `toModal_imp`, `toModal_bot`, etc.). The derived-connective simp lemmas can never fire because the LHS is always simplified away first.

2. **No bare `simp` calls depend on them.** All downstream usages in Soundness.lean are via `simp only [Satisfies.some_future_iff]` or explicit `.mp`/`.mpr` calls. The `simp only` syntax works with any named lemma regardless of `@[simp]` status. The Embedding lemmas have zero downstream usages.

3. **The lemmas remain useful as named rewrite lemmas.** Removing `@[simp]` does not remove the lemma -- it only removes it from the default simp set. Callers can still use `simp only [Satisfies.some_future_iff]`, `rw [Satisfies.some_future_iff]`, or `.mp`/`.mpr` exactly as before.

4. **No alternative fix is viable.** The root cause is that `neg`, `some_future`, etc. are `abbrev`. We cannot change them to `def` (that would break definitional unfolding throughout the codebase). We cannot restructure the simp lemma LHS to avoid the abbrev (the whole point of the lemma is about the derived connective). Using `@[simp, nolint simpNF]` is not appropriate here because the linter is correctly identifying a genuine redundancy.

### Alternative Considered: `@[simp, nolint simpNF]`

This would suppress the warning while keeping the lemmas in the simp set. However, this is not recommended because:
- The lemmas truly are redundant -- simp already handles these cases.
- Adding redundant lemmas to the simp set slows down simp calls.
- `nolint` is reserved for cases where the linter gives a false positive; here the warning is correct.

### Implementation Steps

1. Remove `@[simp]` from all 7 lemmas (simple attribute deletion).
2. Run `lake build` to verify no breakage.
3. The 3 `simp only` calls in Soundness.lean will continue to work unchanged.
4. The 15+ explicit `.mp`/`.mpr` calls in Soundness.lean will continue to work unchanged.

### Risk Assessment

**Risk**: Very low. The fix is purely mechanical (delete 7 `@[simp]` annotations). No proof content changes. All downstream usages are compatible.

**Coordination with Task 66**: Task 66 renames `some_future` -> `someFuture`, etc. The simp fix in task 67 is independent of the renaming. Either can be done first. If task 66 runs first, the lemma names in task 67 will be different (e.g., `someFuture_iff` instead of `some_future_iff`), but the fix (removing `@[simp]`) is the same.

## Dependency Map

```
Satisfies.lean simp dependency chain:
  atom_iff   @[simp] -- primitive, no issue
  imp_iff    @[simp] -- primitive, no issue  
  untl_iff   @[simp] -- primitive, no issue
  snce_iff   @[simp] -- primitive, no issue
  neg_iff    @[simp] -- REMOVE: LHS unfolds to imp_iff target
  some_future_iff @[simp] -- REMOVE: LHS unfolds to untl_iff + imp_iff target
  some_past_iff   @[simp] -- REMOVE: LHS unfolds to snce_iff + imp_iff target
  all_future_iff  @[simp] -- REMOVE: LHS unfolds to imp_iff + untl_iff + imp_iff target
  all_past_iff    @[simp] -- REMOVE: LHS unfolds to imp_iff + snce_iff + imp_iff target

Embedding.lean simp dependency chain:
  toModal_atom    @[simp] -- primitive, no issue
  toModal_bot     @[simp] -- primitive, no issue
  toModal_imp     @[simp] -- primitive, no issue
  toModal_neg     @[simp] -- REMOVE: LHS unfolds to toModal_imp + toModal_bot target
  toTemporal_atom @[simp] -- primitive, no issue
  toTemporal_bot  @[simp] -- primitive, no issue
  toTemporal_imp  @[simp] -- primitive, no issue
  toTemporal_neg  @[simp] -- REMOVE: LHS unfolds to toTemporal_imp + toTemporal_bot target
```

## Verification Checklist

- [ ] Remove `@[simp]` from 5 lemmas in `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
- [ ] Remove `@[simp]` from 2 lemmas in `Cslib/Logics/Propositional/Embedding.lean`
- [ ] Run `lake build` -- expect zero new errors
- [ ] Verify Soundness.lean still builds (uses `simp only` and explicit calls)
- [ ] Run `lake build` on full project for CI compliance
