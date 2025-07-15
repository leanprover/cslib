import Cslib.Syntax.ReductionNotation

@[reduction "ₙ", simp]
def PredReduction (a b : ℕ) : Prop := a = b + 1

open Relation.ReflTransGen

lemma single_step : 5 ⇢ₙ 4 := by simp

lemma multiple_step : 5 ↠ₙ 3 := by
  have s1 : 5 ↠ₙ 4 := by
    apply single
    simp
  refine Relation.ReflTransGen.trans s1 ?_
  apply single
  simp
 
lemma equiv_step : 5 ≈ₙ 5 := Relation.EqvGen.refl 5
