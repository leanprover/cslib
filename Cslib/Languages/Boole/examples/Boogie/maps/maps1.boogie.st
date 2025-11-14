program Boogie;

// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type X;

function mapadd(f: Map X int, g: Map X int) : Map X int;
function mapsub(f: Map X int, g: Map X int) : Map X int;
function mapmul(f: Map X int, g: Map X int) : Map X int;
function mapdiv(f: Map X int, g: Map X int) : Map X int;
function mapmod(f: Map X int, g: Map X int) : Map X int;
function mapconstint(x: int) : Map X int;
function mapconstbool(x: bool) : Map X bool;
function mapand(f: Map X bool, g: Map X bool) : Map X bool;
function mapor(f: Map X bool, g: Map X bool) : Map X bool;
function mapnot(f: Map X bool) : Map X bool;
function mapiteint(f: Map X bool, g: Map X int, h: Map X int) : Map X int;
function mapitebool(f: Map X bool, g: Map X bool, h: Map X bool) : Map X bool;
function maple(f: Map X int, g: Map X int) : Map X bool;
function maplt(f: Map X int, g: Map X int) : Map X bool;
function mapge(f: Map X int, g: Map X int) : Map X bool;
function mapgt(f: Map X int, g: Map X int) : Map X bool;
function mapeq(f: Map X int, g: Map X int) : Map X bool;
function mapiff(f: Map X bool, g: Map X bool) : Map X bool;
function mapimp(f: Map X bool, g: Map X bool) : Map X bool;

const FF: Map X bool;
axiom FF == mapconstbool(false);

const TT: Map X bool;
axiom TT == mapconstbool(true);

const MultisetEmpty: Map X int;
axiom MultisetEmpty == mapconstint(0);

// axioms for basic behavior 

// integer map operations
axiom (forall f: Map X int, g: Map X int, x: X ::
  mapadd(f, g)[x] == f[x] + g[x]);

axiom (forall f: Map X int, g: Map X int, x: X ::
  mapsub(f, g)[x] == f[x] - g[x]);

axiom (forall f: Map X int, g: Map X int, x: X ::
  mapmul(f, g)[x] == f[x] * g[x]);

axiom (forall f: Map X int, g: Map X int, x: X ::
  mapdiv(f, g)[x] == f[x] div g[x]);

axiom (forall f: Map X int, g: Map X int, x: X ::
  mapmod(f, g)[x] == f[x] mod g[x]);

axiom (forall c: int, x: X ::
  mapconstint(c)[x] == c);

// boolean map operations
axiom (forall f: Map X bool, g: Map X bool, x: X ::
  mapand(f, g)[x] == (f[x] && g[x]));

axiom (forall f: Map X bool, g: Map X bool, x: X ::
  mapor(f, g)[x] == (f[x] || g[x]));

axiom (forall f: Map X bool, x: X ::
  mapnot(f)[x] == !(f[x]));

axiom (forall c: bool, x: X ::
  mapconstbool(c)[x] == c);

// conditional map operations
axiom (forall f: Map X bool, g: Map X int, h: Map X int, x: X ::
  mapiteint(f, g, h)[x] == (if f[x] then g[x] else h[x]));

axiom (forall f: Map X bool, g: Map X bool, h: Map X bool, x: X ::
  mapitebool(f, g, h)[x] == (if f[x] then g[x] else h[x]));

// relational map operations
axiom (forall f: Map X int, g: Map X int, x: X ::
  maple(f, g)[x] == (f[x] <= g[x]));

axiom (forall f: Map X int, g: Map X int, x: X ::
  maplt(f, g)[x] == (f[x] < g[x]));

axiom (forall f: Map X int, g: Map X int, x: X ::
  mapge(f, g)[x] == (f[x] >= g[x]));

axiom (forall f: Map X int, g: Map X int, x: X ::
  mapgt(f, g)[x] == (f[x] > g[x]));

axiom (forall f: Map X int, g: Map X int, x: X ::
  mapeq(f, g)[x] == (f[x] == g[x]));

// boolean relations between boolean maps
axiom (forall f: Map X bool, g: Map X bool, x: X ::
  mapiff(f, g)[x] == (f[x] <==> g[x]));

axiom (forall f: Map X bool, g: Map X bool, x: X ::
  mapimp(f, g)[x] == (f[x] ==> g[x]));

// extensionality axioms for maps
axiom (forall f: Map X int, g: Map X int ::
  (forall x: X :: f[x] == g[x]) ==> f == g);

axiom (forall f: Map X bool, g: Map X bool ::
  (forall x: X :: f[x] == g[x]) ==> f == g);

function MultisetSingleton(x: X) : Map X int
{
  MultisetEmpty[x := 1]
}

function MultisetPlus(a: Map X int, b: Map X int) : Map X int
{
  mapadd(a, b)
}

function MultisetMinus(a: Map X int, b: Map X int)  : Map X int
{
  mapiteint(mapgt(a, b), mapsub(a, b), mapconstint(0))
}

procedure foo() returns () {
  var x: X;

  assert (forall y: X :: FF[y] != TT[y]);
  assert (forall y: X :: mapnot(FF)[y] == TT[y]);

  assert MultisetSingleton(x)[x] != MultisetEmpty[x];
  assert (forall y: X :: MultisetPlus(MultisetEmpty, MultisetSingleton(x))[y] == MultisetSingleton(x)[y]);
  assert (forall y: X :: MultisetMinus(MultisetPlus(MultisetEmpty, MultisetSingleton(x)), MultisetSingleton(x))[y] == MultisetEmpty[y]);
  assert (forall y: X :: MultisetMinus(MultisetEmpty, MultisetSingleton(x))[y] == MultisetEmpty[y]);
};