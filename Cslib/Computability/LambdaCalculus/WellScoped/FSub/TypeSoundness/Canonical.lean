import Cslib.Computability.LambdaCalculus.WellScoped.FSub.TypeSystem
import Cslib.Computability.LambdaCalculus.WellScoped.FSub.RetypeTheory.TypeSystem

inductive Ctx.IsEmpty : Ctx s -> Prop where
| empty_is_empty : Ctx.IsEmpty .empty

theorem HasType.app_inv
  (ht : HasType Γ (.app e1 e2) T) :
  ∃ T1 T2,
    HasType Γ e1 (.arrow T1 T2)
    ∧ HasType Γ e2 T1
    ∧ Subtyp Γ T2 T := by
  generalize he0 : Exp.app e1 e2 = e at ht
  induction ht <;> cases he0
  case app T1 U1 _ ht1 ht2 _ _ =>
    use T1, U1
    split_ands
    { exact ht1 }
    { exact ht2 }
    { apply Subtyp.refl }
  case sub hsub _ ih =>
    have ⟨T1, T2, ht1, ht2, hs0⟩ := ih rfl
    use T1, T2
    split_ands
    { exact ht1 }
    { exact ht2 }
    { apply Subtyp.trans hs0 hsub }

theorem Subtyp.top_inv
  (hsub : Subtyp Γ .top T) :
  T = .top := by
  generalize he0 : Ty.top = T at hsub
  induction hsub <;> cases he0
  case top => rfl
  case refl => rfl
  case trans => aesop

theorem Subtyp.arrow_inv_left
  (hsub : Subtyp Γ (.arrow T1 U1) T) :
  (∃ T2 U2, T = .arrow T2 U2) ∨ T = .top := by
  generalize he0 : Ty.arrow T1 U1 = T at hsub
  induction hsub <;> cases he0
  case top => right; rfl
  case refl => left; aesop
  case arrow => left; aesop
  case trans ih1 _ ih2 =>
    specialize ih2 rfl
    cases ih2
    case inl ih2 =>
      aesop
    case inr ih2 =>
      cases ih2
      rename_i hsub _
      have heq := Subtyp.top_inv hsub
      aesop

theorem Subtyp.poly_inv_left
  (hsub : Subtyp Γ (.poly T1 T2) T) :
  (∃ T3 T4, T = .poly T3 T4) ∨ T = .top := by
  generalize he0 : Ty.poly T1 T2 = T at hsub
  induction hsub <;> cases he0
  case top => right; rfl
  case refl => left; aesop
  case poly => left; aesop
  case trans ih1 _ ih2 =>
    specialize ih2 rfl
    cases ih2
    case inl ih2 =>
      aesop
    case inr ih2 =>
      cases ih2
      rename_i hsub _
      have heq := Subtyp.top_inv hsub
      aesop

theorem Subtype.tvar_inv_right
  (hsub : Subtyp Γ T (.tvar X)) :
  ∃ X0, T = .tvar X0 := by
  generalize he0 : Ty.tvar X = T0 at hsub
  induction hsub <;> cases he0
  case refl => aesop
  case trans => aesop
  case tvar => aesop

theorem Subtyp.arrow_inv_right
  (hsub : Subtyp Γ T (.arrow T2 U2)) :
  (∃ T1 U1, T = .arrow T1 U1) ∨ (∃ X, T = .tvar X) := by
  generalize he0 : Ty.arrow T2 U2 = T0 at hsub
  induction hsub <;> cases he0
  case refl => aesop
  case tvar => aesop
  case arrow => aesop
  case trans ih1 _ ih2 =>
    specialize ih2 rfl
    cases ih2
    case inl ih2 =>
      have ⟨T2, U2, h⟩ := ih2
      cases h
      specialize ih1 rfl
      aesop
    case inr ih2 =>
      have ⟨X, h⟩ := ih2
      cases h
      rename_i hsub _
      have := Subtype.tvar_inv_right hsub
      aesop

theorem Subtyp.poly_inv_right
  (hsub : Subtyp Γ T (.poly T2 U2)) :
  (∃ T1 U1, T = .poly T1 U1) ∨ (∃ X, T = .tvar X) := by
  generalize he0 : Ty.poly T2 U2 = T0 at hsub
  induction hsub <;> cases he0
  case refl => aesop
  case tvar => aesop
  case poly => aesop
  case trans ih1 _ ih2 =>
    specialize ih2 rfl
    cases ih2
    case inl ih2 =>
      have ⟨T2, U2, h⟩ := ih2
      cases h
      specialize ih1 rfl
      aesop
    case inr ih2 =>
      have ⟨X, h⟩ := ih2
      cases h
      rename_i hsub _
      have := Subtype.tvar_inv_right hsub
      aesop

theorem Subtyp.arrow_inv
  (hsub : Subtyp Γ (.arrow T1 U1) (.arrow T2 U2)) :
  Subtyp Γ T2 T1 ∧ Subtyp Γ U1 U2 := by
  generalize he1 : Ty.arrow T1 U1 = P1 at hsub
  generalize he2 : Ty.arrow T2 U2 = P2 at hsub
  induction hsub <;> cases he1 <;> cases he2
  case refl => constructor <;> apply Subtyp.refl
  case trans hs1 ih1 hs2 ih2 =>
    have := Subtyp.arrow_inv_left hs1
    cases this
    case inr h =>
      cases h
      have := Subtyp.top_inv hs2
      contradiction
    case inl h =>
      have ⟨T3, U3, h⟩ := h
      cases h
      specialize ih1 rfl rfl
      specialize ih2 rfl rfl
      have ⟨ih11, ih12⟩ := ih1
      have ⟨ih21, ih22⟩ := ih2
      constructor
      { apply Subtyp.trans ih21 ih11 }
      { apply Subtyp.trans ih12 ih22 }
  case arrow => aesop

theorem Subtyp.poly_inv
  (hsub : Subtyp Γ (.poly T1 U1) (.poly T2 U2)) :
  Subtyp Γ T2 T1 ∧ Subtyp (Γ,X<:T2) U1 U2 := by
  generalize he1 : Ty.poly T1 U1 = P1 at hsub
  generalize he2 : Ty.poly T2 U2 = P2 at hsub
  induction hsub <;> cases he1 <;> cases he2
  case refl => constructor <;> apply Subtyp.refl
  case poly => aesop
  case trans hs1 ih1 hs2 ih2 =>
    have := Subtyp.poly_inv_left hs1
    cases this
    case inl h =>
      have ⟨T3, T4, h⟩ := h
      cases h
      specialize ih1 rfl rfl
      specialize ih2 rfl rfl
      have ⟨ih11, ih12⟩ := ih1
      have ⟨ih21, ih22⟩ := ih2
      constructor
      { apply Subtyp.trans ih21 ih11 }
      { have ih12' := ih12.retype (Retype.narrow_tvar ih21)
        simp [Ty.subst_id] at ih12'
        apply Subtyp.trans ih12' ih22 }
    case inr h =>
      cases h
      have := Subtyp.top_inv hs2
      contradiction

theorem Subtyp.non_tvar_left_inv
  (hsub : Subtyp Γ T1 T2)
  (hnt : ∀ X, T1 ≠ .tvar X) :
  ∀ X, T2 ≠ .tvar X := by
  induction hsub
  case top => aesop
  case refl => aesop
  case tvar =>
    rename_i X _ _
    specialize hnt X
    contradiction
  case trans ih1 ih2 => aesop
  case arrow => aesop
  case poly => aesop

theorem HasType.value_typing
  (hv : Exp.IsVal v)
  (ht : HasType Γ v T) :
  ∀ X, T ≠ .tvar X := by
  induction ht <;> try (solve | cases hv)
  case sub hsub _ ih =>
    specialize ih hv
    apply Subtyp.non_tvar_left_inv hsub
    exact ih
  case abs => aesop
  case tabs => aesop

theorem HasType.abs_inv {Γ : Ctx s}
  (ht : HasType Γ (.abs T0 e) (.arrow T1 U1)) :
  ∃ U0,
    HasType (Γ,x:T0) e (U0.rename Rename.succVar) ∧
    Subtyp Γ T1 T0 ∧
    Subtyp Γ U0 U1 := by
  generalize he1 : Exp.abs T0 e = t at ht
  generalize he2 : Ty.arrow T1 U1 = P at ht
  induction ht <;> cases he1 <;> cases he2
  case abs T0 t0 U0 ht _ =>
    use U0
    split_ands
    { exact ht }
    { apply Subtyp.refl }
    { apply Subtyp.refl }
  case sub hsub =>
    have := Subtyp.arrow_inv_right hsub
    cases this
    case inl h =>
      have ⟨T1, U1, h⟩ := h
      cases h
      rename_i ih
      specialize ih rfl rfl
      have ⟨U0, ih1, ih2, ih3⟩ := ih
      have ⟨h1, h2⟩ := Subtyp.arrow_inv hsub
      use U0
      split_ands
      { exact ih1 }
      { apply Subtyp.trans h1 ih2 }
      { apply Subtyp.trans ih3 h2 }
    case inr h =>
      have ⟨X, h⟩ := h
      rename_i hv _ _
      have := HasType.value_typing (by constructor) hv
      aesop

theorem HasType.tapp_inv
  (ht : HasType Γ (.tapp e T) U) :
  ∃ T2,
    HasType Γ e (.poly T T2)
    ∧ Subtyp Γ (T2.open_tvar T) U := by
  generalize he1 : Exp.tapp e T = t0 at ht
  induction ht <;> cases he1
  case tapp =>
    rename_i T2 ht _
    use T2
    split_ands
    { exact ht }
    { apply Subtyp.refl }
  case sub hs _ ih =>
    specialize ih rfl
    have ⟨T2, ih1, ih2⟩ := ih
    use T2
    split_ands
    { exact ih1 }
    { apply Subtyp.trans ih2 hs }

theorem HasType.tabs_inv
  (ht : HasType Γ (.tabs T0 e) (.poly T1 U1)) :
  ∃ U0,
    HasType (Γ,X<:T0) e U0
    ∧ Subtyp Γ T1 T0
    ∧ Subtyp (Γ,X<:T1) U0 U1 := by
  generalize he1 : Exp.tabs T0 e = t0 at ht
  generalize he2 : Ty.poly T1 U1 = P at ht
  induction ht <;> cases he1 <;> cases he2
  case tabs T _ U h _ =>
    use U
    split_ands
    { exact h }
    { apply Subtyp.refl }
    { apply Subtyp.refl }
  case sub ht ih hs =>
    have := Subtyp.poly_inv_right hs
    cases this
    case inl h =>
      have ⟨T2, U2, h⟩ := h
      cases h
      rename_i ih
      specialize ih rfl rfl
      have ⟨U0, ih1, ih2, ih3⟩ := ih
      have ⟨h1, h2⟩ := Subtyp.poly_inv hs
      use U0
      split_ands
      { exact ih1 }
      { apply Subtyp.trans h1 ih2 }
      { have ih3' := ih3.retype (Retype.narrow_tvar h1)
        simp [Ty.subst_id] at ih3'
        apply Subtyp.trans ih3' h2 }
    case inr h =>
      have ⟨X, h⟩ := h
      cases h
      rename_i ht _
      have := HasType.value_typing (by constructor) ht
      aesop

theorem HasType.value_typing_arrow_inv
  (hv : Exp.IsVal v)
  (ht : HasType Γ v (.arrow T U)) :
  ∃ T0 e0, v = .abs T0 e0 := by
  generalize he : Ty.arrow T U = P at ht
  induction ht <;> try (solve | cases he | cases hv)
  case sub ih =>
    cases he
    rename_i hs
    have := Subtyp.arrow_inv_right hs
    cases this
    case inl h =>
      have ⟨T1, U1, h⟩ := h
      cases h
      specialize ih hv rfl
      trivial
    case inr h =>
      have ⟨X, h⟩ := h
      rename_i hvt _
      have := HasType.value_typing hv hvt
      aesop
  case abs => aesop

theorem HasType.value_typing_poly_inv
  (hv : Exp.IsVal v)
  (ht : HasType Γ v (.poly T U)) :
  ∃ T0 e0, v = .tabs T0 e0 := by
  generalize he : Ty.poly T U = P at ht
  induction ht <;> try (solve | cases he | cases hv)
  case sub ih =>
    cases he
    rename_i hs
    have := Subtyp.poly_inv_right hs
    cases this
    case inl h =>
      have ⟨T1, U1, h⟩ := h
      cases h
      specialize ih hv rfl
      trivial
    case inr h =>
      have ⟨X, h⟩ := h
      rename_i hvt _
      have := HasType.value_typing hv hvt
      aesop
  case tabs => aesop
