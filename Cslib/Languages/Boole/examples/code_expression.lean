import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example for mutually recursive procedure calls: `RequiresZero`
and `RequiresZeroViaCallee` each require the same precondition and call each
other, exercising call elimination (the caller's `requires` must be
discharged as a proof obligation at the call site) across mutual recursion.
`AssumeThenAssert` additionally shows that an `assume`d fact can be
immediately reused by a subsequent `assert` of the same proposition.
-/

private def code_expression :=
#strata
program Boole;

type T;

const zero : T;

function IsProperIndex(i : int, size : int) : (bool);

procedure RequiresZero(a : (Map int T), n : int) returns ()
spec {
  requires (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero)));
}
{
  call RequiresZeroViaCallee(a, n);
};

procedure RequiresZeroViaCallee(a : (Map int T), n : int) returns ()
spec {
  requires (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero)));
}
{
  call RequiresZero(a, n);
};

procedure AssumeThenAssert(a : (Map int T), n : int) returns ()
{
  assume (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero)));
  assert (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero)));
};

#end

/-- info:
Obligation: callElimAssert_RequiresZeroViaCallee_requires_1_892_2
Property: assert
Result: ✅ pass

Obligation: callElimAssert_RequiresZero_requires_0_703_5
Property: assert
Result: ✅ pass

Obligation: assert_3_1129
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" code_expression (options := .quiet)

theorem code_expression_smtVCsCorrect : Strata.smtVCsCorrectBoole code_expression := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
