import Mathlib.Data.Nat.Basic
import Init.Data.Option.Coe
import Mathlib.Order.Lattice
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.List.Sort


set_option tactic.hygienic false


--set_option autoImplicit false

/-  Typeclass for Ticking  -/

/-- A typeclass for monads that can track time via a 'tick'. -/
class MonadTick (m : Type → Type) where
  tick {α : Type} (a : α) (c : ℕ := 1) : m α

-- Redefine the notation to be generic using the typeclass.
notation "✓" a:arg ", " c:arg => MonadTick.tick a c
notation "✓" a:arg            => MonadTick.tick a

/-- A monad to track accumulated time. -/
structure TimeM (α : Type) where
  val : α
  time : ℕ
  deriving Repr

namespace TimeM

def pure (a : α) : TimeM α :=
  ⟨a, 0⟩

def bind (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.val
  ⟨r.val, m.time + r.time⟩

instance : Monad TimeM where
  pure := pure
  bind := bind

/-- Increments the time counter. -/
@[simp] def tick {α : Type} (a : α) (c : ℕ := 1) : TimeM α :=
  ⟨a, c⟩

/-- Runs the computation to get the final value and total time. -/
def run (m : TimeM α) : α × ℕ :=
  (m.val, m.time)

-- Make TimeM an instance of our new typeclass.
instance : MonadTick TimeM where
  tick a c := ⟨a, c⟩

end TimeM

/-- The state for tracking memory usage. -/
structure SpaceState where
  space : ℤ := 0
  peak_space : ℤ := 0
  min_space : ℤ := 0
  deriving Repr
--TODO: Counting space for the stack frames


-- The initial state for any space computation.
def initialSpaceState : SpaceState := {}

/-- A monad for stateful computations that track space usage. -/
abbrev SpaceM := StateT SpaceState Id

--#check SpaceM
namespace SpaceM

/-- Allocates `amount` space. Updates current, peak, and min space. -/
def alloc (amount : ℤ) : SpaceM Unit := do
  let s ← get
  let newSpace := s.space + amount
  set {
    s with
    space := newSpace,
    peak_space := max s.peak_space newSpace,
    min_space := min s.min_space newSpace
  }

/-- Frees `amount` space. This is just allocating a negative amount. -/
def free (amount : ℤ) : SpaceM Unit :=
  alloc (-amount)

/-- Runs the computation to get the final value and space state. -/
def run (m : SpaceM α) (s0 := initialSpaceState) : α × SpaceState :=
  StateT.run m s0

end SpaceM

/-- A monad combining Space and Time tracking. -/
abbrev ResourceM := StateT SpaceState TimeM

instance : MonadTick ResourceM where
  tick a c := (TimeM.tick a c)

-- This instance allows us to automatically use a TimeM action inside ResourceM.
instance : MonadLift TimeM ResourceM where
  monadLift m := fun s => do
    let a ← m
    return (a, s)

namespace ResourceM


-- We redefine the space operations for the new monad.
-- They don't affect time.

/-- Allocates space within a ResourceM computation. -/
def alloc (amount : ℤ) : ResourceM Unit := do
  let s ← get
  let newSpace := s.space + amount
  set { s with
    space := newSpace,
    peak_space := max s.peak_space newSpace,
    min_space := min s.min_space newSpace
  }

/-- Frees space within a ResourceM computation. -/
def free (amount : ℤ) : ResourceM Unit :=
  alloc (-amount)

-- We "lift" the time operation from TimeM into ResourceM.

/-- Increments time within a ResourceM computation. -/
@[simp] def tick {α : Type} (a : α) (c : ℕ := 1) : ResourceM α := (TimeM.tick a c)

/-- Runs the resource computation. -/
def run (m : ResourceM α) (s0 := initialSpaceState) : (α × SpaceState) × ℕ :=
  -- First, run the StateT transformer, which returns a TimeM computation.
  let timeComputation : TimeM (α × SpaceState) := StateT.run m s0
  -- Then, run the TimeM computation to get the final result.
  timeComputation.run

end ResourceM


-- -- We define `@[simp]` lemmas for the `.time` field, similar to how we did for `.ret`.
-- @[grind, simp] theorem time_of_pure (a : α) : (pure a).time = 0 := rfl
-- @[grind, simp] theorem time_of_bind (m : TimeM α) (f : α → TimeM β) :
--  (TimeM.bind m f).time = m.time + (f m.ret).time := rfl
-- @[grind, simp] theorem time_of_tick {α} (a : α) (c : ℕ) : (tick a c).time = c := rfl
-- @[grind, simp] theorem ret_bind (m : TimeM α) (f : α → TimeM β) :
--   (TimeM.bind m f).ret = (f m.ret).ret := rfl

-- allow us to simplify the chain of compositions
attribute [simp] Bind.bind Pure.pure

--TODO: Counting space for the stack frames
-- Non-tail recursion: memory can be O(n^2) as stack size can be O(n).
def merge (xs ys : List ℕ) : ResourceM (List ℕ) :=
  let rec go : List ℕ → List ℕ → ResourceM (List ℕ)
  | [], ys => do
    .alloc ys.length
    return ys
  | xs, [] => do
    .alloc xs.length
    return xs
  | x::xs', y::ys' => do
    .alloc (xs.length + ys.length)
    let c ← ✓(x ≤ y:Bool)
    if c then
      let rest ← go xs' (y::ys')
      .alloc 1
      .free (xs.length + ys.length)
      return (x :: rest)
    else
      let rest ← go (x::xs') ys'
      .alloc 1
      .free (xs.length + ys.length)
      return (y :: rest)
  go xs ys

-- with Tail recursion
-- memory can be optimized, no stack frame used, free space of
-- the current subroutine before calling the next one.
def mergeTail (as bs acc : List ℕ) : ResourceM (List ℕ) := do
  .alloc (as.length + bs.length + acc.length)
  match as, bs with
  | [], _ => do
     return acc.reverse ++ bs
  | _, [] => do
     return acc.reverse ++ as
  | a::as', b::bs' => do
      let c ← ✓(a ≤ b:Bool)
      if c then
        .free (as.length + bs.length+acc.length)
        mergeTail as' (b::bs') (a::acc)
      else
        .free (as.length + bs.length+acc.length)
        mergeTail (a::as') bs' (b::acc)

def mergeSort (xs : List ℕ) : ResourceM (List ℕ) := do
  .alloc xs.length
  if xs.length < 2 then
    return xs
  else
    let n := xs.length
    let half := n / 2
    let left := xs.take half
    let right := xs.drop half

    let sortedLeft ← mergeSort left
    let sortedRight ← mergeSort right

    let result ← mergeTail sortedLeft sortedRight []

    .free (sortedLeft.length + sortedRight.length+n)
    return result
termination_by xs.length decreasing_by all_goals grind

#check (mergeSort [2,3,1]).run
#eval (mergeSort [1,2,3,4,5,6,7,8]).run.1.2


lemma correctness(xs : List ℕ ): List.Sorted (. ≤ .) (mergeSort xs).run.1.1  := sorry
lemma nlogn_time (xs : List ℕ ): (mergeSort xs).run.2 ≤ 10*xs.length* (Nat.log2 xs.length) := sorry

lemma no_mem_leak(xs : List ℕ ): (mergeSort xs).run.1.2.space = xs.length := sorry
lemma no_neg_mem (xs : List ℕ ): (mergeSort xs).run.1.2.min_space ≥ 0 := sorry
lemma linear_mem (xs : List ℕ ): (mergeSort xs).run.1.2.peak_space ≤ xs.length := sorry
