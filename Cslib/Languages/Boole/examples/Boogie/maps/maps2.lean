import Strata.Languages.Boogie.Verifier

namespace Strata

private def maps2 :=
#strata
program Boogie;

type X;
type Y;

function mapiteint(c: Map X bool, a: Map X (Map Y int), b: Map X (Map Y int)) : Map X (Map Y int);
function mapeq(f: Map X (Map Y int), g: Map X (Map Y int)) : Map X bool;
function mapnot(f: Map X bool) : Map X bool;

// axioms for basic behavior

axiom (forall c: Map X bool, a: Map X (Map Y int), b: Map X (Map Y int), x: X ::
  mapiteint(c, a, b)[x] == (if c[x] then a[x] else b[x]));

axiom (forall f: Map X (Map Y int), g: Map X (Map Y int), x: X ::
  mapeq(f, g)[x] == (f[x] == g[x]));

axiom (forall f: Map X bool, x: X ::
  mapnot(f)[x] == !(f[x]));

// extensionality axioms
axiom (forall f: Map X (Map Y int), g: Map X (Map Y int) ::
  (forall x: X :: f[x] == g[x]) ==> f == g);

axiom (forall f: Map X bool, g: Map X bool ::
  (forall x: X :: f[x] == g[x]) ==> f == g);


procedure bar() returns () {
  var a: Map X (Map Y int);
  var b: Map X (Map Y int);
  var c: Map X bool;

  //assert mapiteint(c, a, b) == mapiteint(mapnot(c), b, a);
  // assert mapeq(a, b) == mapeq(b, a);

  assert (forall x: X :: mapiteint(c, a, b)[x] == mapiteint(mapnot(c), b, a)[x]);
  assert (forall x: X :: mapeq(a, b)[x] == mapeq(b, a)[x]);
};

#end

#eval verify "cvc5" maps2
