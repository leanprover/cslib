import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Verification example illustrating reachability/coverage patterns in Boole
proof obligations: contradictory `requires`/`assume`s make later statements
vacuously verified ("not covered" in the inline annotations below), a
callee's `free`-independent `ensures` clauses are separately discharged at
each call site, and postconditions can go unconstrained when not tied to a
`ensures` clause. The `{:id "..."} covered`/`not covered` comments are
inert documentation, not live Boole syntax.
-/

private def verification_coverage :=
#strata
program Boole;

procedure testRequiresAssign(n: int) returns ()
spec
{
  requires n > 0; // was {:id "r0"} covered
  requires n < 10; // was {:id "r_not_1"} not covered
}
{
    var x: int;
    x := n + 1; // was {:id "a0"} covered
    assert x == n + 1; // was {:id "assert_a0"} covered
    x := 0; // was {:id "a_not_1"} not covered
    assert n > 0; // was {:id "assert_r0"} covered
};

procedure sum(n: int) returns (s: int)
spec
{
  requires n >= 0; // {:id "spre1"} covered
  ensures s == (n * (n + 1)) div 2; // {:id "spost"} covered
}
{
  var foo: int;

  s := 0;
  foo := 27;
  for i: int := 0 to (n - 1)
    invariant (0 <= i && i <= n)
    invariant (s == (i * (i + 1)) div 2)
    invariant (n >= 0)
  {
    s := s + (i + 1);
    foo := foo * 2; // {:id "update_foo"} not covered
  }
};

procedure contradictoryAssume(n: int) returns ()
{
    assume n > 0; // {:id "cont_assume_1"} covered
    assume n < 0; // {:id "cont_assume_2"} covered
    assume n == 5; // {:id "unreach_assume_1"} not covered
    assert n < 10; // {:id "unreach_assert_1"} not covered
};

// NB: an explicit `requires false` leads to _nothing_ being covered
procedure falseRequires(n: int) returns ()
spec
{
  requires n != n; // {:id "false_req"} covered
}
{
    assert false; // {:id "false_assert"} not covered
};

procedure contradictoryRequires(n: int) returns ()
spec
{
  requires n > 0; // {:id "cont_req_1"} covered
  requires n < 0; // {:id "cont_req_2"} covered
}
{
    assume n == 5; // {:id "n_eq_5"} not covered
    assert n > 10; // {:id "n_lt_10"} not covered
};

procedure assumeFalse() returns ()
{
  assume false; // {:id "assumeFalse"} covered
  assert 1 + 1 == 2; // {:id "assertSimple"} not covered
};

procedure testEnsuresCallee(n: int) returns (r: int)
spec
{
  requires n > 0; // {:id "ter0"} covered
  ensures r > n;  // {:id "tee0"} covered
  ensures r > 0;  // {:id "tee1"} covered when proving this procedure
}
{
  r := n + 1;
};

procedure testEnsuresCaller(n: int) returns (r: int)
spec
{
  requires n > 0; // {:id "ter1"} covered
  ensures r > n;  // {:id "tee_not_1"} covered
}
{
  var x: int;
  var y: int;
  call x := testEnsuresCallee(n + 1); // {:id "call1"} requires/ensures covered
  call y := testEnsuresCallee(n + 1); // {:id "call2"} requires/ensures covered
  assert y > 0; // {:id "call2_tee1"} covered
  r := x + y; // {:id "xy_sum"} covered
};

procedure obviouslyUnconstrainedCode(x: int) returns (a: int, b: int)
spec
{
  requires x > 10; // {:id "x_gt_10"} covered
  requires x < 100; // {:id "x_lt_100"} not covered
  ensures a > 10; // {:id "a_gt_10"} covered
}
{
  a := x + 1; // {:id "constrained"} covered
  b := x - 1; // {:id "not_constrained"} not covered: not constrained by ensures clause
};


procedure contradictoryEnsuresClause(x: int) returns (r: int)
spec
{
  requires x > 1; // {:id "xpos_abs"} covered (established by caller)
  ensures r > x; // {:id "cont_ens_abs"} covered (used by caller proof)
}
{
    r := x + 1;
};

// Call function that has contradictory ensures clauses.
procedure callContradictoryFunction(x: int) returns (r: int)
spec
{
  requires x > 1; // {:id "xpos_caller"} covered
  //ensures r < 0; // {:id "caller_ensures"} not covered
}
{
  call r := contradictoryEnsuresClause(x); // {:id "call_cont"} requires/ensures covered
  //r := r - 1; // {:id "unreachable_assignment"} not covered
};

function someInteger(i: int) : int
{
  3
}

axiom (∀ i: int . someInteger(i) == 3); // {:id "someInteger_value_axiom"}

procedure usesSomeInteger() returns (r: bool)
spec
{
  ensures r;
}
{
  r := someInteger(7) == 3;
};

#end

/-- info:
Obligation: assert_2_829
Property: assert
Result: ✅ pass

Obligation: assert_3_932
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: sum_ensures_5_1075
Property: assert
Result: ✅ pass

Obligation: assert_10_1608
Property: assert
Result: ✅ pass

Obligation: assert_12_1842
Property: assert
Result: ✅ pass

Obligation: assert_16_2107
Property: assert
Result: ✅ pass

Obligation: assert_18_2243
Property: assert
Result: ✅ pass

Obligation: testEnsuresCallee_ensures_20_2406
Property: assert
Result: ✅ pass

Obligation: testEnsuresCallee_ensures_21_2448
Property: assert
Result: ✅ pass

Obligation: callElimAssert_testEnsuresCallee_requires_19_2364_7
Property: assert
Result: ✅ pass

Obligation: callElimAssert_testEnsuresCallee_requires_19_2364_2
Property: assert
Result: ✅ pass

Obligation: assert_24_2881
Property: assert
Result: ✅ pass

Obligation: testEnsuresCaller_ensures_23_2642
Property: assert
Result: ✅ pass

Obligation: obviouslyUnconstrainedCode_ensures_27_3146
Property: assert
Result: ✅ pass

Obligation: contradictoryEnsuresClause_ensures_29_3472
Property: assert
Result: ✅ pass

Obligation: callElimAssert_contradictoryEnsuresClause_requires_28_3402_12
Property: assert
Result: ✅ pass

Obligation: usesSomeInteger_ensures_32_4134
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" verification_coverage (options := .quiet)

theorem verification_coverage_smtVCsCorrect : Strata.smtVCsCorrectBoole verification_coverage := by
  gen_smt_vcs_boole
  all_goals
    (intros
     first
     | smt +mono
     | smt
     | omega
     | trivial
     | (have hstep : ∀ x : Int, (x + 1) * (x + 1 - 1) = x * (x - 1) + 2 * x := fun x => by
          have e1 : x + 1 - 1 = x := by omega
          rw [e1, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
          omega
        simp only [hstep] at *
        omega)
     | grind)
