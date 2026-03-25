import Strata.MetaVerifier
import Smt

------------------------------------------------------------
namespace Strata

-- CLRS Chapter 10: Stacks (array implementation)
-- Page 223 of 3rd edition
-- STACK-EMPTY(S)
-- 1  if S.top == 0
-- 2      return TRUE
-- 3  else return FALSE
--
-- PUSH(S, x)
-- 1  S.top = S.top + 1
-- 2  S[S.top] = x
--
-- POP(S)
-- 1  if STACK-EMPTY(S)
-- 2      error "underflow"
-- 3  else
-- 4      x = S[S.top]
-- 5      S.top = S.top - 1
-- 6      return x

private def stackArrayPgm :=
#strata
program Boole;

// Represent the stack array as a map from int to int.
// We follow CLRS and treat indices as 1..n, with `top` in [0..n].
type Array := Map int int;

// Global stack storage, capacity, and top pointer
var S   : Array;
var n   : int;   // capacity of S
var top : int;   // index of top element; 0 means "empty"

// Initialize stack with capacity `cap`
procedure StackInit(cap : int) returns ()
spec
{
  requires cap >= 0;
  modifies n;
  modifies top;
  ensures n == cap;
  ensures top == 0;
}
{
  n := cap;
  top := 0;
};

// STACK-EMPTY(S)
procedure StackEmpty() returns (b : bool)
spec
{
  ensures (b ==> top == 0);
  ensures (top == 0 ==> b);
}
{
  if (top == 0) {
    b := true;
  } else {
    b := false;
  }
};

// PUSH(S, x)
procedure Push(x : int) returns ()
spec
{
  // No overflow: must have room for one more element
  requires top < n;
  modifies S;
  modifies top;

  ensures top == old(top) + 1;
  ensures S[top] == x;

  // Older elements are preserved
  ensures (
    ∀ i:int .
      1 <= i && i <= old(top) ==> S[i] == old(S[i])
  );
}
{
  top := top + 1;
  S := S[top := x];
};

// POP(S)
procedure Pop() returns (x : int)
spec
{
  // No underflow: must be non-empty
  requires top > 0;
  modifies top;

  ensures top == old(top) - 1;
  ensures x == old(S[old(top)]);
}
{
  x := S[top];
  top := top - 1;
};

#end

-- will verify once pr in Strata is merged
-- #eval Strata.Boole.verify "cvc5" stackArrayPgm

-- example : Strata.smtVCsCorrect stackArrayPgm := by
--   gen_smt_vcs
--   all_goals (smt +mono)
