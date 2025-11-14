program Boogie;

// This test provides concrete Boogie programs with loops, invariants, 
// and contradictory or unreachable code

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
  var i: int;
  var foo: int;

  i := 0;
  s := 0;
  foo := 27;
  while (i < n)
    invariant (0 <= i && i <= n) && (s == (i * (i + 1)) div 2) && (n >= 0);
  {
    i := i + 1;
    s := s + i;
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

axiom (forall i: int :: someInteger(i) == 3); // {:id "someInteger_value_axiom"}

procedure usesSomeInteger() returns (r: bool)
spec
{
  ensures r;
}
{
  r := someInteger(7) == 3;
};