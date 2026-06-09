# Phase 1 Handoff: SignedFormula Foundation Types

## Completed
- All core types ported: Sign, SignedFormula, Branch, Label, EventualityTracker, TimeOrdering, BlockingState
- Formula extensions added: Hashable instance, complexity, subformulas, subformulaClosure
- Universe-polymorphic: SignedFormula.{u} (Atom : Type u) : Type u
- All proofs: LawfulBEq for Label/Sign, flip_flip, self_mem_subformulas, subformulas_trans
- Build: zero errors, zero warnings, zero sorry

## Key Decisions
1. Formula.complexity uses simplified uniform measure (not the pattern-aware version from source that special-cases derived connectives like all_future, some_past). Sufficient for fuel computation.
2. Formula extensions (hashFormula, complexity, subformulas) placed in Cslib.Logic.Bimodal namespace for dot notation compatibility.
3. AppliedSet deferred to Phase 2 (Tableau.lean) where it is actually defined in the source.
4. Structures use variable-bound instances to avoid deriving mismatch; Eventuality/EventualityTracker use variable (Atom) / variable {Atom} pattern.
5. Replaced native_decide with decide for Sign proofs (mathlib linter compliance).

## Current State
- File: Cslib/Logics/Bimodal/Metalogic/Decidability/SignedFormula.lean
- 845 lines ported (vs ~935 source)
- All pattern-matching on derived connectives (all_future, some_future, etc.) works via abbrev transparency

## Next Action
Phase 2: Port Tableau.lean (28 expansion rules) and TraceCertificate.lean (trace types)
- TraceCertificate is ~303 lines
- Tableau.lean is ~1190 lines with the large applyRule match expression
- Both depend only on SignedFormula (Phase 1)
