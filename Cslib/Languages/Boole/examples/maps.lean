import StrataBoole.MetaVerifier
import Smt

namespace Strata

/-
Verification example for derived operations on nested `Map` types
(`Map X (Map Y int)`): a pointwise if-then-else selector, pointwise equality,
and pointwise negation, each axiomatized together with an extensionality
axiom. Exercises reasoning about maps-of-maps via axiomatized higher-order
map functions rather than Boole's native `[...]`/`=~=` operators.
-/

private def mapFunctionsSeed :=
#strata
program Boole;

type X;
type Y;

function mapiteint(c: Map X bool, a: Map X (Map Y int), b: Map X (Map Y int)) : Map X (Map Y int);
function mapeq(f: Map X (Map Y int), g: Map X (Map Y int)) : Map X bool;
function mapnot(f: Map X bool) : Map X bool;

// axioms for basic behavior

axiom (∀ c: Map X bool, a: Map X (Map Y int), b: Map X (Map Y int), x: X .
  mapiteint(c, a, b)[x] == (if c[x] then a[x] else b[x]));

axiom (∀ f: Map X (Map Y int), g: Map X (Map Y int), x: X .
  mapeq(f, g)[x] == (f[x] == g[x]));

axiom (∀ f: Map X bool, x: X .
  mapnot(f)[x] == !(f[x]));

// extensionality axioms
axiom (∀ f: Map X (Map Y int), g: Map X (Map Y int) .
  (∀ x: X . f[x] == g[x]) ==> f == g);

axiom (∀ f: Map X bool, g: Map X bool .
  (∀ x: X . f[x] == g[x]) ==> f == g);


procedure test_map_functions() returns () {
  var a: Map X (Map Y int);
  var b: Map X (Map Y int);
  var c: Map X bool;

  assert (∀ x: X . mapiteint(c, a, b)[x] == mapiteint(mapnot(c), b, a)[x]);
  assert (∀ x: X . mapeq(a, b)[x] == mapeq(b, a)[x]);
};

#end

/-- info:
Obligation: assert_5_1386
Property: assert
Result: ✅ pass

Obligation: assert_6_1465
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" mapFunctionsSeed (options := .quiet)

theorem mapFunctionsSeed_smtVCsCorrect : Strata.smtVCsCorrectBoole mapFunctionsSeed := by
  gen_smt_vcs_boole
  all_goals (try smt +mono)
