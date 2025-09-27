import Mathlib.Data.Nat.Basic
import Init.Data.Option.Coe
import Mathlib.Order.Lattice

set_option tactic.hygienic false


structure CostM (α : Type) where
  val : α
  cost : ℕ

#check CostM

namespace CostM

def pure (a : α) : CostM α :=
  ⟨a, 0⟩

def bind (m : CostM α) (f : α → CostM β) : CostM β :=
  let r := f m.val
  ⟨r.val, m.cost + r.cost⟩

instance : Monad CostM where
  pure := pure
  bind := bind


-- Increment cost
def tick {α : Type} (a : α) (c : ℕ := 1) : CostM α :=
  ⟨a, c⟩

-- We define `@[simp]` lemmas for the `.cost` field, similar to how we did for `.val`.
@[simp] theorem cost_of_pure (a : α) : (pure a).cost = 0 := rfl
@[simp] theorem cost_of_bind (m : CostM α) (f : α → CostM β) :
  (CostM.bind m f).cost = m.cost + (f m.val).cost := rfl
@[simp] theorem cost_of_tick {α} (a : α) (c : ℕ) : (tick a c).cost = c := rfl
@[simp] theorem val_bind (m : CostM α) (f : α → CostM β) :
  (CostM.bind m f).val = (f m.val).val := rfl

--  Now, we prove the cost of `merge` is linear.

def merge (xs ys : List ℕ) : CostM (List ℕ) :=
  let rec go : List ℕ → List ℕ → CostM (List ℕ)
  | [], ys => tick ys ys.length
  | xs, [] => tick xs xs.length
  | x::xs', y::ys' =>
    if x ≤ y then
      do let rest ← go xs' (y::ys')
         tick (x :: rest)
    else
      do let rest ← go (x::xs') ys'
         tick (y :: rest)
  go xs ys

def mergeSort (xs : List ℕ) : CostM (List ℕ) :=
  if xs.length < 2 then .pure xs
  else
  let n := xs.length
  let half := n / 2
  let left := xs.take half
  let right := xs.drop half
  do
    let sortedLeft ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight
termination_by xs.length decreasing_by (
  · simp only [List.length_take, inf_lt_right, not_le, gt_iff_lt]
    subst n
    simp_all only [not_lt]
    rename_i h
    exact Nat.log2_terminates xs.length h
  · grind
)


#check mergeSort
#eval merge [1,2,3,10] [4,5]
#eval! mergeSort [4,2,3,5]

#check merge.go.induct
#check mergeSort.induct

end CostM
