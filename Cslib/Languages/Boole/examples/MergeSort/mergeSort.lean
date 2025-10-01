import Mathlib.Data.Nat.Basic
import Init.Data.Option.Coe
import Mathlib.Order.Lattice
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Nat.Log

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
#eval! mergeSort [4,2,3,]

#check merge.go.induct
#check mergeSort.induct

open List

@[simp, grind] def IsSorted (l : List ℕ) : Prop := Sorted (· ≤ ·) l
@[simp, grind] def MinOfList (x : ℕ) (l : List ℕ) : Prop := ∀ b ∈ l, x ≤ b

theorem mem_either_merge (xs ys : List ℕ) (z : ℕ)
  (hz : z ∈ (merge xs ys).val) : z ∈ xs ∨ z ∈ ys := by
  rw [merge] at hz
  fun_induction merge.go <;>
  all_goals (try (simp only [not_mem_nil, false_or];assumption))
  all_goals (simp only [Bind.bind, tick, val_bind, mem_cons] at hz;cases hz;all_goals (aesop))


theorem min_all_merge (x : ℕ) (xs ys : List ℕ)
(hxs : MinOfList x xs) (hys : MinOfList x ys) : MinOfList x (merge xs ys).val := by
  simp_all only [MinOfList]
  intro a ha
  apply mem_either_merge at ha
  grind

theorem sorted_merge (l1 l2 : List ℕ) (hxs : IsSorted l1)
  (hys : IsSorted l2) : IsSorted ((merge l1 l2).val) := by
  fun_induction merge.go l1 l2 <;> all_goals (first| simpa [merge,merge.go,tick]|
    simp only [IsSorted, merge, merge.go, h, ↓reduceIte, Bind.bind, tick, val_bind, sorted_cons]
    simp [merge] at ih1
    simp_all only [IsSorted, sorted_cons, implies_true, forall_const, and_true]
    apply min_all_merge <;> all_goals grind
  )

theorem MSMCorrect (xs : List ℕ) : IsSorted (mergeSort xs).val := by
  fun_induction mergeSort xs
  · obtain h | h : x = [] ∨ ∃a, x = [a] := by
      by_cases x.length = 0
      · aesop
      · right
        have: x.length = 1 := by omega
        exact List.length_eq_one_iff.mp this
    · subst h
      simp only [IsSorted]
      exact sorted_nil
    · obtain ⟨a,ha⟩ := h
      rw [ha]
      exact sorted_singleton a
  · simp only [Bind.bind, val_bind]
    apply sorted_merge
    · exact ih2
    · exact ih1

@[simp] theorem merge_cost (xs ys : List ℕ) : (merge xs ys).cost = xs.length + ys.length := by
  simp only [merge]
  fun_induction merge.go <;>
  all_goals(simp_all only [length_cons, Bind.bind, tick, cost_of_bind]; all_goals (grind))

@[simp] theorem merge_val_length_eq_sum (xs ys : List ℕ) :
  (merge xs ys).val.length = xs.length + ys.length := by
  rw [merge]
  fun_induction merge.go <;> all_goals (simp_all only
  [length_cons, Bind.bind, tick, val_bind]; grind [Bind.bind,tick,val_bind])


@[simp] theorem mergeSort_same_length (xs : List ℕ) : (mergeSort xs).val.length = xs.length:= by
  fun_induction mergeSort <;> all_goals (try simp_all only [pure,not_lt, Bind.bind, val_bind])
  grind [merge_val_length_eq_sum]

#check Bind.bind
#check Pure.pure

theorem mergeSort_cost_recurrence (xs : List ℕ) (h : 2 ≤ xs.length) :
  (mergeSort xs).cost = (mergeSort (xs.take (xs.length / 2))).cost +
                        (mergeSort (xs.drop (xs.length / 2))).cost +
                        xs.length := by
  conv =>
    left
    unfold mergeSort
  split_ifs with h1
  · omega
  · dsimp [Bind.bind,cost_of_bind]
    ring_nf
    simp only [merge_cost, Nat.add_left_cancel_iff]
    repeat rw [mergeSort_same_length]
    simp only [length_take, length_drop]
    omega

def MS_REC : ℕ → ℕ
| 0 => 0
| x+1 =>
  if x = 0 then 0
  else
    let n := x+1
    MS_REC (n/2) + MS_REC ((n-1)/2 + 1) + n
termination_by x => x decreasing_by all_goals omega

#eval! mergeSort [4,1,3,4,5,6]
#eval! MS_REC 6


theorem mergeSort_cost_eq_MS_REC (xs : List ℕ) :
  (mergeSort xs).cost = MS_REC xs.length := by
  fun_induction mergeSort
  · simp only [cost_of_pure]
    unfold MS_REC
    simp only [Nat.add_one_sub_one]
    grind
  · simp_all only [not_lt, Bind.bind, cost_of_bind, merge_cost, mergeSort_same_length]
    conv =>
      right
      unfold MS_REC
    simp only [Nat.add_one_sub_one]
    split <;> all_goals (grind)


def MS_REC_SIMP : ℕ → ℕ
| 0 => 0
| x+1 =>
  if x = 0 then 0
  else
    let n := x+1
    2*MS_REC_SIMP (n/2) + n

theorem MS_REC_SIMP_EQ (n : ℕ) :   (MS_REC (2^n))= (MS_REC_SIMP (2^n))  := by
  induction' n  with n ih
  · unfold MS_REC_SIMP MS_REC
    simp only [↓reduceIte]
  · unfold MS_REC_SIMP MS_REC
    split <;> all_goals grind


theorem MS_REC_SIMP_EQ_CLOSED (n : ℕ) : MS_REC_SIMP (2^n) = 2^n * n := by
  induction' n  with n ih
  · unfold MS_REC_SIMP
    aesop
  · unfold MS_REC_SIMP
    grind

-- The cost is written assuming the length of the list is a power of two (for simplicity).
theorem MSCostBound (xs : List ℕ) (h : ∃ k, xs.length = 2 ^ k) :
  (mergeSort xs).cost = xs.length*(Nat.log 2 xs.length)  := by
  rw [mergeSort_cost_eq_MS_REC]
  obtain ⟨k,hk⟩ := h
  rw [hk,MS_REC_SIMP_EQ,MS_REC_SIMP_EQ_CLOSED]
  simp only [Nat.lt_add_one, Nat.log_pow]

end CostM
