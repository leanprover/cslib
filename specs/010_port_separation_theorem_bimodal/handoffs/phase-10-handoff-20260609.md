# Phase 10 Handoff - Cycle 3

## Immediate Next Action
Continue with Phase 11: HierarchyDefs.lean (1051 lines source)

## Completed Phases
- Phase 1-7: Complete (cycles 1-2)
- Phase 8: DedekindZ/QLemma.lean + Cases.lean (cycle 3)
- Phase 9: NormalForm.lean (cycle 3)
- Phase 10: TemporalClosure.lean (cycle 3)

## Remaining Phases
- Phase 11: Hierarchy/HierarchyDefs.lean (1051 lines) - has_single_U_type, U/S-formula abstraction
- Phase 12: Hierarchy/HierarchyCaseSep.lean (655 lines) - case-specific separability
- Phase 13: Hierarchy/HierarchyInduction.lean (1437 lines) + HierarchyCompletion.lean (981 lines)
- Phase 14: SeparationThm.lean (354 lines) + DualEliminations.lean (101 lines)
- Phase 15: Barrel import and verification

## Key Porting Insights (Updated)

1. **Scoped notation conflict**: NEVER use F, G, H, P, S, U as variable names in proofs.

2. **int_truth lemma names**: Source uses `int_truth_and_iff.mp h`, cslib uses `(int_truth_and M t _ _).mp h` with explicit M and time variable.

3. **DecidableEq requirement**: Files using `BEq` on Formula need `[DecidableEq Atom]` in the variable block. The source's `==` on Formula translates to `=` with `if p = A /\ q = B` (using decidable equality) rather than `p == A && q == B` (which requires ReflBEq).

4. **subst behavior**: After `subst hwt` where `hwt : w = t`, variable `t` is eliminated and becomes `w`. Always use surviving variable name after subst.

5. **push_neg deprecation**: `push_neg` still works but generates warnings. Consistent with rest of codebase.

6. **Linter options needed**: Most files need some combination of:
   - `set_option linter.style.emptyLine false`
   - `set_option linter.style.longLine false`
   - `set_option linter.unusedSimpArgs false`
   - `set_option linter.unusedSectionVars false`
   - `set_option linter.unusedDecidableInType false`
   - `set_option linter.style.show false`
   - `set_option linter.style.maxHeartbeats false`
   - `set_option linter.flexible false`

7. **Formula.top**: The source defines `abbrev Formula.top : Formula := .imp .bot .bot`. Check if cslib already has this or if it needs to be defined.

8. **`no_U_nested_in_S`**: Defined in TemporalClosure.lean (not Defs.lean). Later phases importing this need to import TemporalClosure.

## Files Created This Cycle
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean` (1657 lines)
- `Cslib/Logics/Bimodal/Metalogic/Separation/NormalForm.lean` (370 lines)
- `Cslib/Logics/Bimodal/Metalogic/Separation/TemporalClosure.lean` (522 lines)
