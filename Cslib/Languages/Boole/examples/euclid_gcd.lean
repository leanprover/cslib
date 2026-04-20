import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- Euclid's algorithm for GCD, with a spec stated via a helper function/predicate.
--
-- We use the subtraction-based variant of Euclid's algorithm to avoid `mod`, which currently
-- tends to produce large verification conditions.
--
-- Divisibility/maximality are stated as axioms about `GCDSpec`.
private def euclidGcdPgm : Strata.Program :=
#strata
program Boole;

function GCDSpec(a : int, b : int) : int;
function Divides(d : int, a : int) : bool;

// Subtraction-based Euclid facts for `GCDSpec`.
axiom (forall x : int :: GCDSpec(x, x) == x);
axiom (forall x : int, y : int :: x > y && y > 0 ==> GCDSpec(x, y) == GCDSpec(x - y, y));
axiom (forall x : int, y : int :: y > x && x > 0 ==> GCDSpec(x, y) == GCDSpec(x, y - x));

// Spec helper: divisibility and maximality properties of the computed `d`.
// The key idea is that callers can assume `free ensures` without having to verify them here.
procedure GCDProperties(a : int, b : int, d : int) returns ()
spec
{
  requires d == GCDSpec(a, b);
  free ensures Divides(d, a) && Divides(d, b);
  free ensures forall e : int :: (e >= 0 && Divides(e, a) && Divides(e, b)) ==> e <= d;
}
{};

procedure EuclidGCD(a : int, b : int) returns (d : int)
spec
{
  requires a > 0;
  requires b > 0;
  ensures d == GCDSpec(a, b);
  ensures Divides(d, a) && Divides(d, b);
  ensures forall e : int :: (e >= 0 && Divides(e, a) && Divides(e, b)) ==> e <= d;
}
{
  var x : int;
  var y : int;

  x := a;
  y := b;

  while (x != y)
    invariant x > 0
    invariant y > 0
    invariant GCDSpec(x, y) == GCDSpec(a, b)
  {
    if (x > y) {
      x := x - y;
    } else {
      y := y - x;
    }
  }

  d := x;

  // Discharge the divisibility/maximality postconditions via the spec helper.
  call GCDProperties(a, b, d);
};
#end

set_option maxHeartbeats 1000000 in
example : Strata.smtVCsCorrect euclidGcdPgm := by
  gen_smt_vcs
  all_goals grind

end Strata
