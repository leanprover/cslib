import Strata.MetaVerifier

------------------------------------------------------------
namespace Strata

-- Array-backed double-ended queue.
--
-- A deque supports insertion and removal at both ends.  This example uses a
-- bounded, non-circular array model: live elements occupy indices
-- `front .. back - 1`, with `front == back` meaning empty.  The front can move
-- left and the back can move right, so `PushFront` requires spare space before
-- `front` and `PushBack` requires spare space after `back`.
--
-- The circular-buffer queue example covers wraparound behavior separately.
-- Keeping this deque non-circular makes the specifications direct and lets the
-- example focus on four endpoint operations, `old(...)`, and frame properties.
private def dequeArrayPgm :=
#strata
program Boole;

type Array := Map int int;

var D     : Array;
var n     : int;
var front : int;
var back  : int;

// Initialize an empty deque.  Starting both endpoints at `start` leaves room
// to grow in either direction if `0 < start < cap`.
procedure DequeInit(cap : int, start : int) returns ()
spec
{
  requires cap > 0;
  requires 0 <= start && start <= cap;
  modifies n;
  modifies front;
  modifies back;

  ensures n == cap;
  ensures front == start;
  ensures back == start;
}
{
  n := cap;
  front := start;
  back := start;
};

// Return whether the deque has no live elements.
procedure DequeEmpty() returns (b : bool)
spec
{
  ensures (b ==> front == back);
  ensures (front == back ==> b);
}
{
  if (front == back) {
    b := true;
  } else {
    b := false;
  }
};

// Add `x` to the back of the deque.
procedure PushBack(x : int) returns ()
spec
{
  requires 0 <= front && front <= back;
  requires back < n;
  modifies D;
  modifies back;

  ensures back == old(back) + 1;
  ensures D[old(back)] == x;
  ensures (
    ∀ i:int .
      old(front) <= i && i < old(back) ==> D[i] == old(D[i])
  );
}
{
  D := D[back := x];
  back := back + 1;
};

// Remove and return the last element of the deque.
procedure PopBack() returns (x : int)
spec
{
  requires front < back;
  modifies back;

  ensures back == old(back) - 1;
  ensures x == old(D[old(back) - 1]);
  ensures front <= back;
}
{
  back := back - 1;
  x := D[back];
};

// Add `x` to the front of the deque.
procedure PushFront(x : int) returns ()
spec
{
  requires 0 < front && front <= back;
  requires back <= n;
  modifies D;
  modifies front;

  ensures front == old(front) - 1;
  ensures D[front] == x;
  ensures (
    ∀ i:int .
      old(front) <= i && i < old(back) ==> D[i] == old(D[i])
  );
}
{
  front := front - 1;
  D := D[front := x];
};

// Remove and return the first element of the deque.
procedure PopFront() returns (x : int)
spec
{
  requires front < back;
  modifies front;

  ensures front == old(front) + 1;
  ensures x == old(D[old(front)]);
  ensures front <= back;
}
{
  x := D[front];
  front := front + 1;
};

#end

example : Strata.smtVCsCorrect dequeArrayPgm := by
  gen_smt_vcs
  all_goals grind

end Strata
