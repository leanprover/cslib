/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Foundations.Relation.Defs
public import Mathlib.Order.WellFounded

/-! # Basic properties of relations -/

@[expose] public section

variable {α : Type*} {r r₁ r₂ : α → α → Prop}

theorem WellFounded.ofTransGen (trans_wf : WellFounded (Relation.TransGen r)) : WellFounded r := by
  grind [WellFounded.wellFounded_iff_has_min, Relation.TransGen]

@[simp, grind =]
theorem WellFounded.iff_transGen : WellFounded (Relation.TransGen r) ↔ WellFounded r :=
  ⟨ofTransGen, transGen⟩

namespace Relation

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

attribute [scoped grind] ReflGen TransGen ReflTransGen EqvGen

theorem ReflGen.to_eqvGen (h : ReflGen r a b) : EqvGen r a b :=
  EqvGen.reflGen_le_eqvGen r _ _ h

theorem TransGen.to_eqvGen (h : TransGen r a b) : EqvGen r a b :=
  EqvGen.transGen_le_eqvGen r _ _ h

theorem ReflTransGen.to_eqvGen (h : ReflTransGen r a b) : EqvGen r a b :=
  EqvGen.reflTransGen_le_eqvGen r _ _ h

theorem SymmGen.to_eqvGen (h : SymmGen r a b) : EqvGen r a b :=
  EqvGen.symmGen_le_eqvGen r _ _ h

attribute [scoped grind →] ReflGen.to_eqvGen TransGen.to_eqvGen ReflTransGen.to_eqvGen
  SymmGen.to_eqvGen

@[deprecated _root_.refl +typeChanged (since := "2026-09-07")]
theorem MJoin.refl (a : α) : MJoin r a a := _root_.refl a

theorem MJoin.single (h : ReflTransGen r a b) : MJoin r a b := by
  use b

/-- If a relation is squeezed by a relation and its multi-step closure, they are multi-step equal -/
theorem reflTransGen_mono_closed (h₁ : r₁ ≤ r₂) (h₂ : r₂ ≤ ReflTransGen r₁) :
    ReflTransGen r₁ = ReflTransGen r₂ := by
  ext a b
  exact ⟨ReflTransGen.mono h₁ a b, reflTransGen_closed h₂ a b⟩

@[deprecated Relation.ReflGen.stdSymm +typeChanged (since := "2026-09-03")]
lemma ReflGen.symmGen_symm : ReflGen (SymmGen r) a b → ReflGen (SymmGen r) b a :=
  Std.Symm.symm a b

@[simp, grind =]
theorem reflTransGen_symmGen : ReflTransGen (SymmGen r) = EqvGen r := EqvGen.reflTransGen_symmGen r

end Relation
