program Boogie;

// CLRS Chapter 7: QUICKSORT
// Pseudo-code adapted from CLRS book (2nd edition), page 146
// Pseudo-code:
// QUICKSORT(A, p, r)
// 1  if p < r
// 2    then q <-- PARTITION(A, p, r)
// 3    QUICKSORT(A, p, q - 1)
// 4    QUICKSORT(A, q + 1, r)
// To sort an entire array A, the initial call is QUICKSORT(A, 1 , lenght[A])

// PARTITION(A, p, r)
// 1  x <-- A[r]
// 2  i <-- p - 1
// 3  for j <-- p to r - 1 
// 4    do if A[j] <= x
// 5        then i <-- i + 1
// 6            exchange A[i] <-> A[j]
// 7  exchange A[i + 1] <-> A[r]
// 8  return i + 1 


var A: Map int int;

procedure Quicksort(p: int, r: int) returns ()
spec
{
  requires p >= 1;
  requires r >= p;
  modifies A;
}
{
  if (p < r) {
    var q: int;
    call q := Partition(p, r);
    if (p < q) {
        call Quicksort(p, q - 1);
    }
    if (q < r) {
        call Quicksort(q + 1, r);
    }
  }
};

procedure Partition(p: int, r: int) returns (q: int)
spec
{
  requires p >= 1;
  requires r >= p;
  modifies A;
  ensures q >= p;
  ensures q <= r;
}
{
  var x: int;
  var i: int;
  var j: int;
  var temp: int;
  var temp2: int;

  x := A[r];
  i := p - 1;
  j := p;

  while (j <= r - 1)
    invariant p - 1 <= i && i < j && j <= r;
  {
    if (A[j] <= x) {
      i := i + 1;
      temp := A[i];
      A := A[i := A[j]];
      A := A[j := temp];
    }
    j := j + 1;
  }

  temp2 := A[i + 1];
  A := A[i + 1 := A[r]];
  A := A[r := temp2];

  q := i + 1;
};