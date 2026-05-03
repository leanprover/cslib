import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- Circular-buffer queue.
--
-- The queue is represented by an array `Q`, a capacity `n`, a head pointer, a
-- tail pointer, and a live element count.  Unlike `queue_array_based.lean`,
-- `head` and `tail` wrap back to zero when they reach the capacity.  We model
-- that wraparound with a small `NextIndex` function instead of `mod`, so the
-- verification conditions remain simple arithmetic plus map-update reasoning.
private def circularQueuePgm :=
#strata
program Boole;

type Array := Map int int;

// `NextIndex(i, n)` is `(i + 1) mod n`, axiomatized without using `mod`.
function NextIndex(i : int, n : int) : int;

axiom (∀ i : int, n : int ::
  n > 0 && 0 <= i && i < n ==> 0 <= NextIndex(i, n) && NextIndex(i, n) < n);
axiom (∀ n : int :: n > 0 ==> NextIndex(n - 1, n) == 0);
axiom (∀ i : int, n : int ::
  n > 0 && 0 <= i && i + 1 < n ==> NextIndex(i, n) == i + 1);

var Q     : Array;
var n     : int;
var head  : int;
var tail  : int;
var count : int;

// Initialize an empty circular queue.
procedure CircularQueueInit(cap : int) returns ()
spec
{
  requires cap > 0;
  modifies n;
  modifies head;
  modifies tail;
  modifies count;

  ensures n == cap;
  ensures head == 0;
  ensures tail == 0;
  ensures count == 0;
}
{
  n := cap;
  head := 0;
  tail := 0;
  count := 0;
};

// Return whether the circular queue is empty.
procedure CircularQueueEmpty() returns (b : bool)
spec
{
  ensures (b ==> count == 0);
  ensures (count == 0 ==> b);
}
{
  if (count == 0) {
    b := true;
  } else {
    b := false;
  }
};

// Return whether the circular queue is full.
procedure CircularQueueFull() returns (b : bool)
spec
{
  ensures (b ==> count == n);
  ensures (count == n ==> b);
}
{
  if (count == n) {
    b := true;
  } else {
    b := false;
  }
};

// Add `x` at the current tail position and advance the tail pointer, wrapping
// to zero when the insertion occurs at the last array slot.
procedure CircularEnqueue(x : int) returns ()
spec
{
  requires n > 0;
  requires 0 <= head && head < n;
  requires 0 <= tail && tail < n;
  requires 0 <= count && count < n;
  modifies Q;
  modifies tail;
  modifies count;

  ensures count == old(count) + 1;
  ensures Q[old(tail)] == x;
  ensures 0 <= tail && tail < n;
  ensures (
    ∀ i:int .
      0 <= i && i < n && i != old(tail) ==> Q[i] == old(Q[i])
  );
}
{
  Q := Q[tail := x];
  tail := NextIndex(tail, n);
  count := count + 1;
};

// Remove and return the current head element, then advance the head pointer
// with the same wraparound convention.
procedure CircularDequeue() returns (x : int)
spec
{
  requires n > 0;
  requires 0 <= head && head < n;
  requires 0 <= tail && tail < n;
  requires 0 < count && count <= n;
  modifies head;
  modifies count;

  ensures x == old(Q[old(head)]);
  ensures count == old(count) - 1;
  ensures 0 <= head && head < n;
}
{
  x := Q[head];
  head := NextIndex(head, n);
  count := count - 1;
};

#end

example : Strata.smtVCsCorrect circularQueuePgm := by
  gen_smt_vcs
  all_goals grind

end Strata
