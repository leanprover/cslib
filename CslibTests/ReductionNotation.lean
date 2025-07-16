import Cslib.Syntax.ReductionNotation

@[reduction rs "ₙ", simp]
def PredReduction (a b : ℕ) : Prop := a = b + 1

open Relation.ReflTransGen

lemma single_step : 5 ⭢ₙ 4 := by
  change PredReduction _ _
  simp

lemma multiple_step : 5 ↠ₙ 3 := by
  calc
    5 ↠ₙ 4 := by apply single; change PredReduction _ _; simp
    _ ↠ₙ 3 := by apply single; change PredReduction _ _; simp
