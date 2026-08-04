import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for Boole's choose operator: `w := ε z: T . pred(z)`
desugars to
  assert ∃ z : T . pred(z);   -- existence obligation (soundness guard)
  havoc w;
  assume pred[z/w];
The existence assertion prevents `assume false` false positives when `pred`
is unsatisfiable.
-/

private def chooseOperatorSeed : StrataDDM.Program :=
#strata
program Boole;

function good(z: int, x: int) : bool;

procedure choose_seed(x: int) returns (w: int)
spec {
  requires ∃ z: int . good(z, x);
  ensures good(w, x);
}
{
  w := ε z: int . good(z, x);
};
#end

/-- info:
Obligation: choose_2_586_exists
Property: assert
Result: ✅ pass

Obligation: choose_seed_ensures_1_560
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseOperatorSeed (options := .quiet)

theorem chooseOperatorSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole chooseOperatorSeed := by
  gen_smt_vcs_boole
  all_goals (first | smt | smt +mono | omega | trivial | grind)

-- Regression: an unsatisfiable predicate must be caught by the existence
-- assertion, not silently turned into `assume false` (which would make every
-- subsequent obligation a false positive). Verification is expected to FAIL
-- here (the existence obligation is unprovable since no `z` satisfies
-- `z != z`); the pinned `#guard_msgs` below documents that expected failure.
private def chooseUnsatSeed : StrataDDM.Program :=
#strata
program Boole;

procedure choose_unsat() returns (w: int)
spec {
  ensures true;
}
{
  w := ε z: int . z != z;
};
#end

/-- info:
Obligation: choose_1_1565_exists
Property: assert
Result: ❌ fail

Obligation: choose_unsat_ensures_0_1545
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseUnsatSeed (options := .quiet)

/-!
## choose-function declarations

`function f(params) : R := ε z . pred(z, params);` declares an uninterpreted
function `f` together with the axiom:
  ∀ params, ∀ z, z = f(params) → pred(z, params)

This lets a specification define a function by its property rather than its
implementation — similar to Verus choose-based spec functions.

Note: unlike `w := ε z . pred(z)` (which guards soundness with an existence
assertion), the function form emits the axiom unconditionally. The user must
ensure `pred` is satisfiable for all inputs (e.g. via a precondition) to avoid
an unsound axiom.
-/

private def chooseFnSeed : StrataDDM.Program :=
#strata
program Boole;

function good(z: int, x: int) : bool;

function best(x: int) : int :=
  ε z : int . good(z, x);

procedure test_choose_fn(x: int) returns (w: int)
spec {
  requires ∃ z: int :: good(z, x);
  ensures good(w, x);
}
{
  w := best(x);
};
#end

/-- info:
Obligation: test_choose_fn_ensures_1_2711
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseFnSeed (options := .quiet)

theorem chooseFnSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole chooseFnSeed := by
  gen_smt_vcs_boole
  all_goals (first | smt | smt +mono | omega | trivial | grind)

-- Without the ∃ precondition the ensures still passes, because the axiom
-- `∀ z, z = best(x) → good(z, x)` unconditionally asserts good(best(x), x).
-- This demonstrates that soundness relies on the caller supplying the witness.
private def chooseFnNoPrecondSeed : StrataDDM.Program :=
#strata
program Boole;

function good(z: int, x: int) : bool;

function best(x: int) : int :=
  ε z : int . good(z, x);

procedure test_no_precond(x: int) returns (w: int)
spec {
  ensures good(w, x);
}
{
  w := best(x);
};
#end

/-- info:
Obligation: test_no_precond_ensures_0_3573
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseFnNoPrecondSeed (options := .quiet)

theorem chooseFnNoPrecondSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole chooseFnNoPrecondSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
