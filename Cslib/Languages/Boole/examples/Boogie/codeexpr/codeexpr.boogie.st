program Boogie;
type StrataHeap;
type StrataRef;
type StrataField (t: Type);

// Type constructors
type T;

// Constants
const zero : T;

// Functions
function IsProperIndex(i : int, size : int) : (bool);

// Uninterpreted procedures
// Implementations
procedure P(a : (Map int T), n : int) returns ()
spec {
  requires (forall i: int :: (IsProperIndex(i, n) ==> (a[i] == zero)));
}
{
  call Q(a, n);
};

procedure Q(a : (Map int T), n : int) returns ()
spec {
  requires (forall i: int :: (IsProperIndex(i, n) ==> (a[i] == zero)));
}
{
  call P(a, n);
};

procedure A(a : (Map int T), n : int) returns ()
{
  assert ((forall i: int :: (IsProperIndex(i, n) ==> (a[i] == zero))) ==> (forall i: int :: (IsProperIndex(i, n) ==> (a[i] == zero))));
};

procedure B(a : (Map int T), n : int) returns ()
{
  assert ((forall i: int :: (IsProperIndex(i, n) ==> (a[i] == zero))) ==> (forall i: int :: (IsProperIndex(i, n) ==> (a[i] == zero))));
};

procedure C(a : (Map int T), n : int) returns ()
{
  assume (forall i: int :: (IsProperIndex(i, n) ==> (a[i] == zero)));
  assert (forall i: int :: (IsProperIndex(i, n) ==> (a[i] == zero)));
};

procedure D(a : (Map int T), n : int) returns ()
{
  assume (forall i: int :: (IsProperIndex(i, n) ==> (a[i] == zero)));
  assert (forall i: int :: (IsProperIndex(i, n) ==> (a[i] == zero)));
};
