import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Reduce
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.Core
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSoundness.Canonical

theorem progress
  (ht : HasType Γ t T) (hem : Ctx.IsEmpty Γ) :
  (∃ t', Reduce t t') ∨ t.IsVal := by
  induction ht
  case var hb =>
    cases hem
    cases hb
  case sub ih => aesop
  case abs => right; constructor
  case tabs => right; constructor
  case app ih1 ih2 =>
    specialize ih1 hem
    cases ih1
    case inl ih1 =>
      have ⟨t1', ih1⟩ := ih1
      left
      constructor
      apply Reduce.red_app_fun
      exact ih1
    case inr ih1 =>
      rename_i hvt _
      have := HasType.value_typing_arrow_inv ih1 hvt
      have ⟨T0, e0, h⟩ := this
      cases h
      left
      constructor
      apply Reduce.red_app
  case tapp ih =>
    specialize ih hem
    cases ih
    case inl ih =>
      have ⟨t1', ih⟩ := ih
      left
      constructor
      apply Reduce.red_tapp_fun
      exact ih
    case inr ih =>
      rename_i hvt
      have := HasType.value_typing_poly_inv ih hvt
      have ⟨T0, e0, h⟩ := this
      cases h
      left
      constructor
      apply Reduce.red_tapp
