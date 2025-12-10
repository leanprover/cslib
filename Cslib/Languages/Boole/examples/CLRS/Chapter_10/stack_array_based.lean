import Strata.MetaVerifier

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
    forall i:int ::
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

#eval verify "cvc5" stackArrayPgm

example : Strata.smtVCsCorrect stackArrayPgm := by
  gen_boogie_vcs
  all_goals grind

-- [FEATURE REQUEST]
-- Support for structures/records and encapsulating methods.
-- For example, we would like to write:

--
-- record Stack :=
--   arr : Array;
--   top : int;
--   cap : int;

-- def Stack.init(cap : int) returns (s : Stack)
-- spec { ensures s.top == 0; ensures s.cap == cap; }
-- {
--   s.top := 0;
--   s.cap := cap;
-- }

-- def Stack.push(s : Stack, x : int) returns (s' : Stack)
-- spec {
--   requires s.top < s.cap;
--   ensures s'.top == s.top + 1;
--   ensures s'.cap == s.cap;
--   ensures s'.arr[s'.top] == x;
-- }
-- {
--   s' := s;
--   s'.top := s.top + 1;
--   s'.arr := s.arr[s'.top := x];
-- }

-- Accessing fields would then be done via:
-- s.top
-- s.cap
-- s.arr[i]
