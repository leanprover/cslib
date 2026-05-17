import Cslib.Foundations.Data.Relation

namespace CslibTests

open Cslib

@[reduction_sys "ₙ", grind]
def PredReduction (a b : ℕ) : Prop := a = b + 1

lemma single_step : 5 ⭢ₙ 4 := by
  grind

-- `Trans` instances allow us to switch between single and multistep reductions in a `calc` block
lemma multiple_step : 5 ↠ₙ 1 := by
  -- TODO: can/should this be a `simp` attribute somewhere?
  calc
    5 ⭢ₙ 4 := by grind
    _ ↠ₙ 2 := by
      calc
        4 ↠ₙ 3 := by grind
        _ ⭢ₙ 2 := by grind
    _ ⭢ₙ 1 := by grind

-- ensure that this still works when there are variables
inductive Term (Var : Type)
variable {Var : Type}

@[reduction_sys "β", simp]
def term_rel : Term Var → Term Var → Prop := fun _ _ ↦ True

example (a b : Term Var) : a ⭢β b := by
  simp

-- check that a "cannonical" notation also works
@[reduction_sys, grind]
def PredReduction' (a b : ℕ) : Prop := a = b + 1

example : 5 ⭢ 4 := by
  grind

--check that namespaces are respected

/-- info: CslibTests.PredReduction (a b : ℕ) : Prop -/
#guard_msgs in
#check CslibTests.PredReduction

-- check that delaborators work, including with variables

/-- info: ∀ (a b : ℕ), a ⭢ₙ b : Prop -/
#guard_msgs in
#check ∀ (a b : ℕ), a ⭢ₙ b

/-- info: ∀ (a b : ℕ), a ↠ₙ b : Prop -/
#guard_msgs in
#check ∀ (a b : ℕ), a ↠ₙ b

/-- info: ∀ (a b : Term Var), a ⭢β b : Prop -/
#guard_msgs in
#check ∀ (a b : Term Var), a ⭢β b

/-- info: ∀ (a b : Term Var), a ↠β b : Prop -/
#guard_msgs in
#check ∀ (a b : Term Var), a ↠β b

end CslibTests
