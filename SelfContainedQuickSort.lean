import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Linarith

set_option autoImplicit false

-- ==========================================
-- PART 1: TimeM Monad (Inlined)
-- ==========================================

structure TimeM (α : Type) where
  ret : α
  time : Nat

namespace TimeM

def pure {α : Type} (a : α) : TimeM α :=
  ⟨a, 0⟩

def bind {α β : Type} (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance : Monad TimeM where
  pure := pure
  bind := bind

def tick {α : Type} (a : α) (c : Nat := 1) : TimeM α := ⟨a, c⟩

end TimeM

export TimeM (tick)

scoped notation "✓" a:arg => tick a 1
scoped notation:max "⟪" tm "⟫" => (TimeM.ret tm)

-- ==========================================
-- PART 2: QuickSort Implementation
-- ==========================================

variable {α : Type} [LinearOrder α]

def partition (p : α → Bool) : List α → TimeM (List α × List α)
  | [] => return ([], [])
  | x :: xs => do
    let (l, r) ← partition p xs
    let c ← ✓ (p x)
    if c then
      return (x :: l, r)
    else
      return (l, x :: r)

theorem partition_ret_length (p : α → Bool) (xs : List α) :
    (⟪partition p xs⟫.1).length + (⟪partition p xs⟫.2).length = xs.length := by
  induction xs with
  | nil => simp [partition, TimeM.pure]
  | cons x xs ih =>
    simp [partition, TimeM.pure, TimeM.bind]
    split <;> simp [ih] <;> omega

theorem partition_length_le (p : α → Bool) (xs : List α) :
    (⟪partition p xs⟫.1).length ≤ xs.length ∧ (⟪partition p xs⟫.2).length ≤ xs.length := by
  have := partition_ret_length p xs
  omega

def quickSort : List α → TimeM (List α)
  | [] => return []
  | x :: xs => do
    let (l, r) ← partition (· ≤ x) xs
    have h1 : l.length < (x :: xs).length := by
      have := partition_length_le (· ≤ x) xs
      simp; omega
    have h2 : r.length < (x :: xs).length := by
      have := partition_length_le (· ≤ x) xs
      simp; omega
    let l_sorted ← quickSort l
    let r_sorted ← quickSort r
    return l_sorted ++ (x :: r_sorted)
  termination_by l => l.length


-- ==========================================
-- PART 3: Verification (Smoke Test)
-- ==========================================

#eval ⟪quickSort [3, 1, 4, 1, 5, 9, 2, 6]⟫
-- Expected: [1, 1, 2, 3, 4, 5, 6, 9]

#eval (quickSort [3, 1, 4, 1, 5, 9, 2, 6]).time
-- Expected: A number representing comparisons (approx n^2 worst case or n log n avg)
