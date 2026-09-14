/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Foundations.Relation.Defs
public import Mathlib.Order.WellFounded

/-! # Basic properties of relations

## TODO:
Many of the results here could be upstreamed to Mathlib. In particular:
- `ReflGen.le_reflGen` and relatives,
- `ReflGen.to_eqvGen` and relatives.
-/

@[expose] public section

variable {α : Type*} {r r₁ r₂ : α → α → Prop}

theorem WellFounded.ofTransGen (trans_wf : WellFounded (Relation.TransGen r)) : WellFounded r := by
  grind [WellFounded.wellFounded_iff_has_min, Relation.TransGen]

@[simp, grind =]
theorem WellFounded.iff_transGen : WellFounded (Relation.TransGen r) ↔ WellFounded r :=
  ⟨ofTransGen, transGen⟩

namespace Relation

open Function

/-- A pair of subrelations lifts to transitivity on the relation. -/
@[implicit_reducible]
def transLeftRight (s s' r : α → α → Prop) [IsTrans α r] (h : s ≤ r) (h' : s' ≤ r) :
    Trans s s' r where
  trans hab hbc := _root_.trans (h _ _ hab) (h' _ _ hbc)

/-- A subrelation lifts to transitivity on the left of the relation. -/
@[implicit_reducible]
def transLeft (s r : α → α → Prop) [IsTrans α r] (h : s ≤ r) : Trans s r r where
  trans hab hbc := _root_.trans (h _ _ hab) hbc

/-- A subrelation lifts to transitivity on the right of the relation. -/
@[implicit_reducible]
def transRight (s r : α → α → Prop) [IsTrans α r] (h : s ≤ r) : Trans r s r where
  trans hab hbc := _root_.trans hab (h _ _ hbc)

@[scoped grind .]
theorem comp_le_comp {s s' r r' : α → α → Prop} (hs : s ≤ s') (hr : r ≤ r') :
    Comp s r ≤ Comp s' r' := fun a c ⟨b, hab, hbc⟩ ↦ ⟨b, hs a b hab, hr b c hbc⟩

theorem comp_self_le (r : α → α → Prop) [IsTrans α r] : Comp r r ≤ r :=
  fun _ _ ⟨_, hab, hbc⟩ ↦ _root_.trans hab hbc

theorem swap_le_iff_le_swap {r₁ r₂ : α → α → Prop} : swap r₁ ≤ r₂ ↔ r₁ ≤ swap r₂ := by
  constructor <;> intro h a b hab <;> exact h b a hab

attribute [scoped grind] ReflGen TransGen ReflTransGen EqvGen

@[scoped grind .]
theorem ReflGen.le_reflGen : r ≤ ReflGen r := fun _ _ => ReflGen.single

theorem ReflGen.to_eqvGen (h : ReflGen r a b) : EqvGen r a b :=
  EqvGen.reflGen_le_eqvGen r _ _ h

@[scoped grind .]
theorem TransGen.le_transGen : r ≤ TransGen r := fun _ _ => TransGen.single

theorem TransGen.to_eqvGen (h : TransGen r a b) : EqvGen r a b :=
  EqvGen.transGen_le_eqvGen r _ _ h

theorem ReflTransGen.to_eqvGen (h : ReflTransGen r a b) : EqvGen r a b :=
  EqvGen.reflTransGen_le_eqvGen r _ _ h

@[scoped grind .]
theorem SymmGen.le_symmGen : r ≤ SymmGen r := fun _ _ => Or.inl

theorem SymmGen.to_eqvGen (h : SymmGen r a b) : EqvGen r a b :=
  EqvGen.symmGen_le_eqvGen r _ _ h

@[simp, scoped grind =] theorem sup_swap_eq_symmGen : r ⊔ Function.swap r = SymmGen r := rfl

@[scoped grind .]
theorem EqvGen.le_eqvGen : r ≤ EqvGen r := EqvGen.rel

theorem _root_.Equivalence.eqvGen_le (h : Equivalence r₂) (hle : r₁ ≤ r₂) : EqvGen r₁ ≤ r₂ :=
  have := h.isEquiv
  EqvGen.eqvGen_le hle

attribute [scoped grind →] ReflGen.to_eqvGen TransGen.to_eqvGen ReflTransGen.to_eqvGen
  SymmGen.to_eqvGen

theorem Join.single [Std.Refl r] (h : r a b) : Join r a b := ⟨b, h, refl b⟩

@[simp, scoped grind =] theorem join₂_eq_join : Join₂ r r = Join r := rfl

theorem join₂_eq_comp_swap : Join₂ r₁ r₂ = Comp r₁ (swap r₂) := rfl

instance [Std.Refl r₁] [Std.Refl r₂] : Std.Refl (Join₂ r₁ r₂) where
  refl a := ⟨a, refl a, refl a⟩

theorem Join₂.single_left [Std.Refl r₂] (h : r₁ a b) : Join₂ r₁ r₂ a b := ⟨b, h, refl b⟩

theorem Join₂.single_right [Std.Refl r₁] (h : r₂ a b) : Join₂ r₁ r₂ b a := ⟨b, refl b, h⟩

theorem Join₂.join₂_le [IsTrans α r] (h₁ : r₁ ≤ r) (h₂ : swap r₂ ≤ r) : Join₂ r₁ r₂ ≤ r :=
  (comp_le_comp h₁ h₂).trans (comp_self_le r)

theorem Join₂.swap_iff {a b : α} : Join₂ r₁ r₂ b a ↔ Join₂ r₂ r₁ a b := by grind [Join₂]

protected theorem Join₂.mono (h₁ : r₁ ≤ r₁') (h₂ : r₂ ≤ r₂') : Join₂ r₁ r₂ ≤ Join₂ r₁' r₂' :=
  fun x y ⟨z, hxz, hyz⟩ => ⟨z, h₁ x z hxz, h₂ y z hyz⟩

@[deprecated _root_.refl +typeChanged (since := "2026-09-07")]
theorem MJoin.refl (a : α) : MJoin r a a := _root_.refl a

@[deprecated Join.single +typeChanged (since := "2026-09-07")]
theorem MJoin.single (h : ReflTransGen r a b) : MJoin r a b := Join.single h

theorem _root_.Equivalence.join_reflTransGen_le (h : Equivalence r₂) (hle : r₁ ≤ r₂) :
    Join (ReflTransGen r₁) ≤ r₂ :=
  have := h.isEquiv
  join_le_of_equivalence_of_le h <| reflTransGen_le_of_le hle

theorem join_reflTransGen_le_eqvGen : Join (ReflTransGen r) ≤ EqvGen r :=
    (EqvGen.is_equivalence r).join_reflTransGen_le EqvGen.le_eqvGen

theorem join₂_reflTransGen_le [Std.Refl r] [IsTrans α r] (h₁ : r₁ ≤ r) (h₂ : swap r₂ ≤ r) :
    Join₂ (ReflTransGen r₁) (ReflTransGen r₂) ≤ r := by
  refine Join₂.join₂_le ?_ (ReflTransGen.swap.trans ?_)
    <;> apply reflTransGen_le_of_le <;> assumption

theorem join₂_reflTransGen_le_of_isEquiv [IsEquiv α r] (h₁ : r₁ ≤ r) (h₂ : r₂ ≤ r) :
    Join₂ (ReflTransGen r₁) (ReflTransGen r₂) ≤ r :=
  join₂_reflTransGen_le h₁ (by rwa [swap_le_iff_le_swap, Std.Symm.swap_eq])

theorem _root_.Equivalence.join₂_reflTransGen_le (h : Equivalence r) (h₁ : r₁ ≤ r) (h₂ : r₂ ≤ r) :
    Join₂ (ReflTransGen r₁) (ReflTransGen r₂) ≤ r :=
  have := h.isEquiv
  join₂_reflTransGen_le_of_isEquiv h₁ h₂

theorem left_le_join₂_reflTransGen : r₁ ≤ Join₂ (ReflTransGen r₁) (ReflTransGen r₂) :=
  fun _ _ h => Join₂.single_left (.single h)

theorem swap_right_le_join₂_reflTransGen : swap r₂ ≤ Join₂ (ReflTransGen r₁) (ReflTransGen r₂) :=
    fun _ _ h => Join₂.single_right (.single h)

/-- If a relation is squeezed by a relation and its multi-step closure, they are multi-step equal -/
theorem reflTransGen_mono_closed (h₁ : r₁ ≤ r₂) (h₂ : r₂ ≤ ReflTransGen r₁) :
    ReflTransGen r₁ = ReflTransGen r₂ := by
  ext a b
  exact ⟨ReflTransGen.mono h₁ a b, reflTransGen_closed h₂ a b⟩

@[deprecated Relation.ReflGen.stdSymm +typeChanged (since := "2026-09-03")]
lemma ReflGen.symmGen_symm : ReflGen (SymmGen r) a b → ReflGen (SymmGen r) b a :=
  Std.Symm.symm a b

@[simp, scoped grind =]
theorem reflTransGen_symmGen : ReflTransGen (SymmGen r) = EqvGen r := EqvGen.reflTransGen_symmGen r

@[scoped grind <=]
theorem join_inl (r₁_ab : r₁ a b) : (r₁ ⊔ r₂) a b :=
  Or.inl r₁_ab

@[scoped grind <=]
theorem join_inr (r₂_ab : r₂ a b) : (r₁ ⊔ r₂) a b :=
  Or.inr r₂_ab

@[scoped grind <=]
theorem join_inl_reflTransGen (r₁_ab : ReflTransGen r₁ a b) : ReflTransGen (r₁ ⊔ r₂) a b :=
  ReflTransGen.mono le_sup_left _ _ r₁_ab

@[scoped grind <=]
theorem join_inr_reflTransGen (r₂_ab : ReflTransGen r₂ a b) : ReflTransGen (r₁ ⊔ r₂) a b :=
  ReflTransGen.mono le_sup_right _ _ r₂_ab

end Relation
