# Implementation Summary: Port Frame Semantics to Cslib Bimodal

**Task**: 3 - Port Frame Semantics (PR 2): TaskFrame, WorldHistory, TaskModel, Truth, Validity to Cslib/Logics/Bimodal/Semantics/
**Session**: sess_1780970224_ba1435_3
**Status**: Implemented
**Date**: 2026-06-08

## What Was Done

Ported 5 source files from BimodalLogic/Theories/Bimodal/Semantics/ to Cslib/Logics/Bimodal/Semantics/, plus created a new Context.lean file. Total: 1,649 lines across 6 new files.

### Files Created

| File | Lines | Description |
|------|-------|-------------|
| `Cslib/Logics/Bimodal/Semantics/TaskFrame.lean` | 191 | Task frame structure with 3 axioms, derived theorems, examples, finite frames |
| `Cslib/Logics/Bimodal/Semantics/WorldHistory.lean` | 309 | World history with convex domains, time-shift construction and lemmas |
| `Cslib/Logics/Bimodal/Semantics/TaskModel.lean` | 83 | Model = frame + polymorphic valuation |
| `Cslib/Logics/Bimodal/Semantics/Truth.lean` | 651 | Recursive truth evaluation, shift-closed sets, time-shift preservation |
| `Cslib/Logics/Bimodal/Semantics/Validity.lean` | 275 | Validity, semantic consequence, satisfiability, reduction lemmas |
| `Cslib/Logics/Bimodal/Syntax/Context.lean` | 140 | Context type (List (Formula Atom)) with supporting theorems |

### Key Adaptations from Source

1. **Atom parametrization**: All definitions that reference `Formula` or `Atom` are parameterized by `(Atom : Type*)`, following cslib's polymorphic formula pattern.

2. **Variable naming**: Frame variables use `ℱ` (Unicode U+2131) instead of `F` because `F` is a scoped notation for `Formula.some_future` within the `Cslib.Logic.Bimodal` namespace. Similarly `G`, `H`, `P` are reserved by scoped notations.

3. **Until/Since semantics swap**: The source's `truth_at` put the first `untl` argument as the event (at witness) and the second as the guard (between). Cslib's `Formula.some_future φ = .untl .top φ` follows the standard convention where the first arg is the guard and the second is the event. The truth_at definition was adapted accordingly: for `untl φ ψ`, ψ (second arg) is the event at witness s, and φ (first arg) is the guard between t and s.

4. **Dropped items** (as planned):
   - `from_list` helper (depends on source's concrete `Atom.base`/`Atom.fresh_index`)
   - `strong_release_iff` and `strong_trigger_iff` (cslib lacks these derived connectives)

5. **cslib conventions**: All files have Apache 2.0 copyright header, `module` declaration (where compatible), `@[expose] public section`, namespace `Cslib.Logic.Bimodal`.

## Verification

- Zero sorries in all files
- Zero vacuous definitions
- Zero new axioms
- All 6 modules build successfully with `lake build`
- Full project build passes (pre-existing error in TemporalDerived.lean is unrelated)

## Plan Deviations

- **Task 4.10** (Skip strong_release_iff/strong_trigger_iff): Completed as planned -- these were intentionally dropped since cslib Bimodal Formula lacks the derived connectives.
- **Task 4.3** (truth_at definition): *(deviation: altered -- swapped event/guard positions in untl/snce cases to match cslib's standard convention where first arg is guard, second is event)*
- **Task 3.7** (Remove `open Bimodal.Syntax`): *(deviation: altered -- used `ℱ` variable name for frames instead of `F` to avoid scoped notation conflict with `Formula.some_future`)*
