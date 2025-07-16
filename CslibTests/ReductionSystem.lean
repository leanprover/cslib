import Cslib.Semantics.ReductionSystem.Basic

@[reduction_sys rs "ₙ", simp]
def PredReduction (a b : ℕ) : Prop := a = b + 1

lemma single_step : 5 ⭢ₙ 4 := by
  change PredReduction _ _
  simp

-- `Trans` instances allow us to switch between single and multistep reductions in a `calc` block
lemma multiple_step : 5 ↠ₙ 1 := by
  -- TODO: can/should this be a `simp` attribute somewhere?
  have h : rs.Red = PredReduction := by rfl
  calc
    5 ⭢ₙ 4 := by simp [h]
    _ ↠ₙ 2 := by
      calc
        4 ⭢ₙ 3 := by simp [h]
        _ ⭢ₙ 2 := by simp [h]
    _ ⭢ₙ 1 := by simp [h]
