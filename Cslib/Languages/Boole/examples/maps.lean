import Strata.MetaVerifier

namespace Strata

private def maps2 :=
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


procedure bar() returns () {
  var a: Map X (Map Y int);
  var b: Map X (Map Y int);
  var c: Map X bool;

  //assert mapiteint(c, a, b) == mapiteint(mapnot(c), b, a);
  // assert mapeq(a, b) == mapeq(b, a);

  assert (∀ x: X . mapiteint(c, a, b)[x] == mapiteint(mapnot(c), b, a)[x]);
  assert (∀ x: X . mapeq(a, b)[x] == mapeq(b, a)[x]);
};

#end

#eval Strata.Boole.verify "cvc5" maps2

example : Strata.smtVCsCorrect maps2 := by
  gen_smt_vcs
  all_goals grind
