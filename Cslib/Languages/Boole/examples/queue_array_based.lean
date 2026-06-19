import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- CLRS Chapter 10: Queues (array implementation).
--
-- This version models a bounded, non-circular FIFO queue.  The queue contents
-- occupy indices `head .. tail - 1`; `head == tail` means empty.  Unlike a
-- circular-buffer implementation, this example does not wrap `head` or `tail`
-- modulo the capacity.  That keeps the arithmetic simple and focuses the
-- verification on global variables, `modifies` clauses, and `old(...)`
-- postconditions.
private def queueArrayPgm :=
#strata
program Boole;

type Array := Map int int;

// Global queue storage, capacity, and head/tail pointers.
//
// Valid live elements are stored in Q[head], Q[head + 1], ..., Q[tail - 1].
// The next enqueue writes at Q[tail].  The next dequeue reads from Q[head].
var Q    : Array;
var n    : int;
var head : int;
var tail : int;

// Initialize an empty queue with capacity `cap`.
procedure QueueInit(cap : int) returns ()
spec
{
  requires cap >= 0;
  modifies n;
  modifies head;
  modifies tail;
  ensures n == cap;
  ensures head == 0;
  ensures tail == 0;
}
{
  n := cap;
  head := 0;
  tail := 0;
};

// Return whether the queue is empty.
//
// The postconditions state both directions of the Boolean result:
// if `b` is true then the queue is empty, and if the queue is empty then `b`
// is true.  Together these characterize `b` as `(head == tail)`.
procedure QueueEmpty() returns (b : bool)
spec
{
  ensures (b ==> head == tail);
  ensures (head == tail ==> b);
}
{
  if (head == tail) {
    b := true;
  } else {
    b := false;
  }
};

// Add `x` to the back of the queue.
//
// Preconditions require a well-formed, non-full queue segment:
// `0 <= head <= tail < n`.  The `modifies` clause records that this operation
// changes the queue array and the tail pointer, but not the head pointer or
// capacity.  The postconditions use `old(...)` to relate the post-state to the
// pre-state:
// * `tail` advances by one;
// * the old tail slot now stores `x`;
// * all previously live elements are preserved.
procedure Enqueue(x : int) returns ()
spec
{
  requires 0 <= head;
  requires head <= tail;
  requires tail < n;
  modifies Q;
  modifies tail;

  ensures tail == old(tail) + 1;
  ensures Q[old(tail)] == x;
  ensures (
    ∀ i:int .
      old(head) <= i && i < old(tail) ==> Q[i] == old(Q[i])
  );
}
{
  Q := Q[tail := x];
  tail := tail + 1;
};

// Remove and return the front element of the queue.
//
// The non-empty precondition `head < tail` guarantees that `Q[head]` is a live
// element.  Dequeue changes only the head pointer: the array contents and tail
// are not modified.  The returned value is the element that was at the old head,
// and the post-state head advances by one.
procedure Dequeue() returns (x : int)
spec
{
  requires head < tail;
  modifies head;

  ensures head == old(head) + 1;
  ensures x == old(Q[old(head)]);
  ensures head <= tail;
}
{
  x := Q[head];
  head := head + 1;
};

#end

example : Strata.smtVCsCorrect queueArrayPgm := by
  gen_smt_vcs
  all_goals grind

end Strata
