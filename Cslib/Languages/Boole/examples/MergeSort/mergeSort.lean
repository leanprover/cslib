import Mathlib.Data.Nat.Basic
import Init.Data.Option.Coe
import Mathlib.Order.Lattice
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Nat.Log

set_option tactic.hygienic false


structure TimeM (α : Type) where
  ret : α
  time : ℕ

namespace TimeM

def pure (a : α) : TimeM α :=
  ⟨a, 0⟩

def bind (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance : Monad TimeM where
  pure := pure
  bind := bind

-- Increment time

@[simp] def tick {α : Type} (a : α) (c : ℕ := 1) : TimeM α :=
  ⟨a, c⟩

notation "✓" a:arg ", " c:arg => tick a c
notation "✓" a:arg => tick a  -- Default case with only one argument

def tickUnit : TimeM Unit :=
  ✓ () -- This uses the default time increment of 1

-- Define custom notation for malloc
--notation "⬆" a:arg ", " size:arg => malloc a size
-- Define custom notation for free
--notation "⬇" a:arg ", " size:arg => free a size


-- We define `@[simp]` lemmas for the `.time` field, similar to how we did for `.ret`.
@[grind, simp] theorem time_of_pure (a : α) : (pure a).time = 0 := rfl
@[grind, simp] theorem time_of_bind (m : TimeM α) (f : α → TimeM β) :
 (TimeM.bind m f).time = m.time + (f m.ret).time := rfl
@[grind, simp] theorem time_of_tick {α} (a : α) (c : ℕ) : (tick a c).time = c := rfl
@[grind, simp] theorem ret_bind (m : TimeM α) (f : α → TimeM β) :
  (TimeM.bind m f).ret = (f m.ret).ret := rfl

-- allow us to simplify the chain of compositions
attribute [simp] Bind.bind Pure.pure TimeM.pure


-- Now, we prove the time of `merge` is linear.
def merge (xs ys : List ℕ) : TimeM (List ℕ) :=
  let rec go : List ℕ → List ℕ → TimeM (List ℕ)
  | [], ys => ✓ ys, ys.length
  | xs, [] => ✓ xs, xs.length
  | x::xs', y::ys' => do
    if x≤ y then
      let rest ← go xs' (y::ys')
      ✓ (x :: rest)
    else
      let rest ← go (x::xs') ys'
      ✓ (y :: rest)
  go xs ys

-- Cosmetic change
def merge' (xs ys : List ℕ) : TimeM (List ℕ) :=
  let rec go : List ℕ → List ℕ → TimeM (List ℕ)
  | [], ys => ✓ ys, ys.length
  | xs, [] => ✓ xs, xs.length
  | x::xs', y::ys' => do
    let c ← ✓ (x ≤ y: Bool)
    if c then
      let rest ← go xs' (y::ys')
      pure (x :: rest)
    else
      let rest ← go (x::xs') ys'
      pure (y :: rest)
  go xs ys


def mergeSort (xs : List ℕ) : TimeM (List ℕ) :=  do
  if xs.length < 2 then return xs
  else
    let n := xs.length
   -- ✓ (), n
    let half := n / 2
    let left :=  xs.take half
    let right := xs.drop half
    let sortedLeft ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight
termination_by xs.length decreasing_by all_goals grind

#check mergeSort
#eval merge [1,2,3,10] [4,5]
#eval mergeSort [4,2,3,]

#check merge.go.induct
#check mergeSort.induct

open List

@[simp, grind] def IsSorted (l : List ℕ) : Prop := Sorted (· ≤ ·) l
@[simp, grind] def MinOfList (x : ℕ) (l : List ℕ) : Prop := ∀ b ∈ l, x ≤ b

theorem mem_either_merge (xs ys : List ℕ) (z : ℕ)
  (hz : z ∈ (merge xs ys).ret) : z ∈ xs ∨ z ∈ ys := by
  rw [merge] at hz
  fun_induction merge.go
  all_goals (try (simp only [not_mem_nil, false_or];assumption))
  all_goals
  simp only [Bind.bind, tick, ret_bind, mem_cons] at hz
  cases hz
  all_goals (aesop)


theorem min_all_merge (x : ℕ) (xs ys : List ℕ)
(hxs : MinOfList x xs) (hys : MinOfList x ys) : MinOfList x (merge xs ys).ret := by
  simp_all only [MinOfList]
  intro a ha
  apply mem_either_merge at ha
  grind

theorem sorted_merge {l1 l2 : List ℕ} (hxs : IsSorted l1)
  (hys : IsSorted l2) : IsSorted ((merge l1 l2).ret) := by
  fun_induction merge.go l1 l2 <;> all_goals (first| simpa [merge,merge.go,tick]|
    simp only [IsSorted, merge, merge.go, h, ↓reduceIte, Bind.bind, tick, ret_bind, sorted_cons]
    simp [merge] at ih1
    simp_all only [IsSorted, sorted_cons, implies_true, forall_const, and_true]
    apply min_all_merge <;> all_goals grind
  )

theorem MSMCorrect (xs : List ℕ) : IsSorted (mergeSort xs).ret := by
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
  · simp only [IsSorted, Bind.bind, ret_bind]
    exact sorted_merge ih2 ih1

@[simp] theorem merge_time (xs ys : List ℕ) :
  (merge xs ys).time = xs.length + ys.length := by
  simp only [merge]
  fun_induction merge.go <;>
  all_goals(simp_all only [length_cons, Bind.bind, tick, time_of_bind]; all_goals (grind))

@[simp] theorem merge_ret_length_eq_sum (xs ys : List ℕ) :
  (merge xs ys).ret.length = xs.length + ys.length := by
  rw [merge]
  fun_induction merge.go
  all_goals
  simp_all only [length_cons, Bind.bind, tick, ret_bind]
  grind

@[simp] theorem mergeSort_same_length (xs : List ℕ) :
  (mergeSort xs).ret.length = xs.length:= by
  fun_induction mergeSort
  · simp only [Pure.pure, pure]
  · simp only [Bind.bind, ret_bind, merge_ret_length_eq_sum]
    grind

theorem mergeSort_time_recurrence (xs : List ℕ) (h : 2 ≤ xs.length) :
  (mergeSort xs).time = (mergeSort (xs.take (xs.length / 2))).time +
                        (mergeSort (xs.drop (xs.length / 2))).time +
                        xs.length := by
  conv =>
    left
    unfold mergeSort
  split_ifs with h1
  · omega
  · simp_all only [not_lt, Bind.bind, time_of_bind, merge_time, mergeSort_same_length, length_take,
    length_drop]
    grind

def MS_REC : ℕ → ℕ
| 0 => 0
| x+1 =>
  if x = 0 then 0
  else
    let n := x+1
    MS_REC (n/2) + MS_REC ((n-1)/2 + 1) + n
termination_by x => x decreasing_by all_goals omega

#eval mergeSort [4,1,3,4,5,6]
#eval MS_REC 6


theorem mergeSort_time_eq_MS_REC (xs : List ℕ) :
  (mergeSort xs).time = MS_REC xs.length := by
  fun_induction mergeSort
  · simp only [Pure.pure, pure]
    --simp only [time_of_pure]
    unfold MS_REC
    simp only [Nat.add_one_sub_one]
    grind
  · simp_all only [not_lt, Bind.bind, time_of_bind, merge_time, mergeSort_same_length]
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

-- The time is written assuming the length of the list is a power of two (for simplicity).
theorem MStimeBound (xs : List ℕ) (h : ∃ k, xs.length = 2 ^ k) :
  (mergeSort xs).time = xs.length*(Nat.log 2 xs.length)  := by
  rw [mergeSort_time_eq_MS_REC]
  obtain ⟨k,hk⟩ := h
  rw [hk,MS_REC_SIMP_EQ,MS_REC_SIMP_EQ_CLOSED]
  simp only [Nat.lt_add_one, Nat.log_pow]

end TimeM
