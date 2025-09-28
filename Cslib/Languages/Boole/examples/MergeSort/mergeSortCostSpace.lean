import Mathlib.Data.Nat.Basic
import Init.Data.Option.Coe
import Mathlib.Order.Lattice
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.List.Sort


set_option tactic.hygienic false


-- The state that will be threaded through our computation.
structure CostSpaceState where
  time : ℕ := 0
  space : ℤ := 0
  peak_space : ℤ := 0
  min_space : ℤ := 0
deriving Repr


-- The monad itself is a function that takes a state and returns a value and a new state.
structure CostSpaceM (α : Type) where
  run : CostSpaceState → (α × CostSpaceState)

namespace CostSpaceM

-- Helper to run a computation with an initial default state.
def eval (m : CostSpaceM α) : α × CostSpaceState :=
  m.run {}

-- Monad Instance
def pure (a : α) : CostSpaceM α :=
  ⟨fun s => (a, s)⟩

def bind (m : CostSpaceM α) (f : α → CostSpaceM β) : CostSpaceM β :=
  ⟨fun s₀ =>
    let (a, s₁) := m.run s₀
    (f a).run s₁⟩

instance : Monad CostSpaceM where
  pure := pure
  bind := bind

/--
### Monadic Operations for Time and Space
-/

-- Tick for time complexity
def tick (c : ℕ := 1) : CostSpaceM Unit :=
  ⟨fun s => ((), { s with time := s.time + c })⟩

-- Allocate `n` units of space
def allocate (n : ℕ) : CostSpaceM Unit :=
  ⟨fun s =>
    let new_space := s.space + n
    let new_peak := max s.peak_space new_space
    ((), { s with space := new_space, peak_space := new_peak})⟩

-- free `n` units of space
def free (n : ℕ) : CostSpaceM Unit :=
  ⟨fun s =>
    let new_space := s.space - n
    let new_debug_space := min s.min_space new_space
    ((), { s with space := new_space, min_space := new_debug_space})⟩



-- The merge function now models memory management.
-- It frees its input lists and allocates space for the output list.
def merge (xs ys : List ℕ) : CostSpaceM (List ℕ) := do
  let rec go (xs' ys' : List ℕ) : CostSpaceM (List ℕ) := do
    match xs', ys' with
    | [], _ => pure ys'
    | _, [] => pure xs'
    | x::xs_tl, y::ys_tl =>
      if x ≤ y then
        do
          tick -- For the comparison
          let rest ← go xs_tl (y::ys_tl)
          pure (x :: rest)
      else
        do
          tick -- For the comparison
          let rest ← go (x::xs_tl) ys_tl
          pure (y :: rest)

  allocate (xs.length + ys.length)
  free  (xs.length + ys.length)
  go xs ys


-- The mergeSort function models the splitting and merging process.
def mergeSort (xs : List ℕ) : CostSpaceM (List ℕ) := do
  if xs.length < 2 then
    tick 1 -- Initial check
    pure xs
  else
    let n := xs.length
    let half := n / 2
    let n' := ((xs.take half).length + (xs.drop half).length)

    allocate n'
    let left := xs.take half
    let right := xs.drop half

    tick (n) -- Cost of splitting the list
    -- Recursively sort the sub-lists
    allocate n'
    let sortedLeft ← mergeSort left
    let sortedRight ← mergeSort right

    free (2*n')
    merge sortedLeft sortedRight

termination_by xs.length

def mergeSort' (xs : List ℕ) : CostSpaceM (List ℕ) := do
  allocate xs.length
  free xs.length
  mergeSort xs


-- Let's run it on an example list
def exampleList := [10,3,5,2]

-- The `eval` helper runs the computation and returns the final result and state.
#eval CostSpaceM.eval (CostSpaceM.mergeSort' exampleList)

def MergeSort (xs : List ℕ):= (CostSpaceM.eval (CostSpaceM.mergeSort' xs)).1
def MergeSort_stat (xs : List ℕ):= (CostSpaceM.eval (CostSpaceM.mergeSort' xs)).2

lemma correctness(xs : List ℕ ): List.Sorted (. ≤ .) (MergeSort xs)  := sorry
lemma nlogn_time (xs : List ℕ ):
  (MergeSort_stat xs).time ≤ 10*xs.length* (Nat.log2 xs.length) := sorry

lemma no_mem_leak(xs : List ℕ ): (MergeSort_stat xs).space = 0 := sorry
lemma no_neg_mem (xs : List ℕ ): (MergeSort_stat xs).min_space ≥ 0 := sorry
lemma linear_mem (xs : List ℕ ): (MergeSort_stat xs).peak_space ≤ xs.length := sorry



end CostSpaceM
