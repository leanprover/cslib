import Cslib.Foundations.Data.HasFresh

namespace CslibTests

open Cslib

variable {Var Term : Type} [DecidableEq Var] [HasFresh Var]

open HasFresh

/-- An example picking free from `Var` and `Finset Var`. -/
example (x : Var) (xs : Finset Var) : ∃ y, x ≠ y ∧ y ∉ xs := by
  let ⟨fresh, _⟩ := fresh_exists <| free_union Var
  exists fresh
  aesop

@[simp]
def fv : Term → Finset ℕ := fun _ ↦ {1, 2, 3}

/-- An example including a specified `free` function. -/
example (_ : Term) (x : ℕ) (xs : Finset ℕ) :
    ∃ y : ℕ, x ≠ y ∧ y ∉ xs ∧ y ∉ ({1, 2, 3} : Finset ℕ) := by
  let ⟨fresh, _⟩ := fresh_exists <| free_union [@fv Term] ℕ
  exists fresh
  aesop

-- check that options work as expected
section

variable (x : ℕ) (xs : Finset ℕ) (var : String)

def f (_ : String) : Finset ℕ := {1, 2, 3}
def g (_ : String) : Finset ℕ := {4, 5, 6}

/-- info: ∅ ∪ {x} ∪ id xs : Finset ℕ -/
#guard_msgs in
#check free_union ℕ

/-- info: ∅ ∪ {x} ∪ id xs ∪ f var ∪ g var : Finset ℕ -/
#guard_msgs in
#check free_union [f, g] ℕ

/-- info: ∅ ∪ id xs : Finset ℕ -/
#guard_msgs in
#check free_union (singleton := false) ℕ

/-- info: ∅ ∪ {x} : Finset ℕ -/
#guard_msgs in
#check free_union (finset := false) ℕ

/-- info: ∅ : Finset ℕ -/
#guard_msgs in
#check free_union (singleton := false) (finset := false) ℕ

end

end CslibTests
