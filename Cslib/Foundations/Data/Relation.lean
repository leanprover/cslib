/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Init
public import Mathlib.Logic.Relation
public import Mathlib.Data.List.TFAE
public import Mathlib.Order.Comparable
public import Mathlib.Order.WellFounded
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Util.Notation3

@[expose] public section

variable {α : Type*} {r : α → α → Prop}

theorem WellFounded.ofTransGen (trans_wf : WellFounded (Relation.TransGen r)) : WellFounded r := by
  grind [WellFounded.wellFounded_iff_has_min, Relation.TransGen]

@[simp, grind =]
theorem WellFounded.iff_transGen : WellFounded (Relation.TransGen r) ↔ WellFounded r :=
  ⟨ofTransGen, transGen⟩

/-! # Relations

## References

* [*Term Rewriting and All That*][Baader1998]

-/

namespace Relation

attribute [scoped grind] ReflGen TransGen ReflTransGen EqvGen CompRel

theorem ReflGen.to_eqvGen (h : ReflGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem TransGen.to_eqvGen (h : TransGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem ReflTransGen.to_eqvGen (h : ReflTransGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem SymmGen.to_eqvGen (h : SymmGen r a b) : EqvGen r a b := by
  induction h <;> grind

attribute [scoped grind →] ReflGen.to_eqvGen TransGen.to_eqvGen ReflTransGen.to_eqvGen
  SymmGen.to_eqvGen

/-- The join of the reflexive transitive closure. This is not named in Mathlib, but see
  `#loogle Relation.Join (Relation.ReflTransGen ?r)` -/
abbrev MJoin (r : α → α → Prop) := Join (ReflTransGen r)

theorem MJoin.refl (a : α) : MJoin r a a := by
  use a

theorem MJoin.symm : Symmetric (MJoin r) := Relation.symmetric_join

theorem MJoin.single (h : ReflTransGen r a b) : MJoin r a b := by
  use b

/-- The relation `r` 'up to' the relation `s`. -/
def UpTo (r s : α → α → Prop) : α → α → Prop := Comp s (Comp r s)

/-- A relation has the diamond property when all reductions with a common origin are joinable -/
abbrev Diamond (r : α → α → Prop) := ∀ {a b c : α}, r a b → r a c → Join r b c

/-- A relation is confluent when its reflexive transitive closure has the diamond property. -/
abbrev Confluent (r : α → α → Prop) := Diamond (ReflTransGen r)

/-- A relation is semi-confluent when single and multiple steps with common origin
  are multi-joinable. -/
abbrev SemiConfluent (r : α → α → Prop) :=
  ∀ {x y₁ y₂}, ReflTransGen r x y₂ → r x y₁ → Join (ReflTransGen r) y₁ y₂

/-- A relation has the Church Rosser property when equivalence implies multi-joinability. -/
abbrev ChurchRosser (r : α → α → Prop) := ∀ {x y}, EqvGen r x y → Join (ReflTransGen r) x y

/-- Extending a multistep reduction by a single step preserves multi-joinability. -/
lemma Diamond.extend (h : Diamond r) :
    ReflTransGen r a b → r a c → Join (ReflTransGen r) b c := by
  intros ab ac
  induction ab using ReflTransGen.head_induction_on generalizing c
  case refl => exists c, .single ac
  case head a'_c' _ ih =>
    obtain ⟨d, cd, c'_d⟩ := h ac a'_c'
    obtain ⟨d', b_d', d_d'⟩ := ih c'_d
    exact ⟨d', b_d', .head cd d_d'⟩

/-- The diamond property implies confluence. -/
theorem Diamond.toConfluent (h : Diamond r) : Confluent r := by
  intros a b c ab bc
  induction ab using ReflTransGen.head_induction_on generalizing c
  case refl => exists c
  case head _ _ a'_c' _ ih =>
    obtain ⟨d, cd, c'_d⟩ := h.extend bc a'_c'
    obtain ⟨d', b_d', d_d'⟩ := ih c'_d
    exact ⟨d', b_d', .trans cd d_d'⟩

theorem Confluent.toChurchRosser (h : Confluent r) : ChurchRosser r := by
  intro x y h_eqv
  induction h_eqv with
  | rel _ b => exists b; grind [ReflTransGen.single]
  | refl a => exists a
  | symm a b _ ih => exact symmetric_join ih
  | trans _ _ _ _ _ ih1 ih2 =>
      obtain ⟨u, _, hbu⟩ := ih1
      obtain ⟨v, hbv, _⟩ := ih2
      obtain ⟨w, _, _⟩ := h hbu hbv
      exists w
      grind [ReflTransGen.trans]

theorem SemiConfluent.toConfluent (h : SemiConfluent r) : Confluent r := by
  intro x y1 y2 h_xy1 h_xy2
  induction h_xy1 with
  | refl => use y2
  | tail h_xz h_zy1 ih =>
      obtain ⟨u, h_zu, _⟩ := ih
      obtain ⟨v, _, _⟩ := h h_zu h_zy1
      exists v
      grind [ReflTransGen.trans]

attribute [scoped grind →] Confluent.toChurchRosser SemiConfluent.toConfluent

private theorem confluent_equivalents : [ChurchRosser r, SemiConfluent r, Confluent r].TFAE := by
  grind [List.tfae_cons_cons, List.tfae_singleton]

theorem SemiConfluent_iff_ChurchRosser : SemiConfluent r ↔ ChurchRosser r :=
  List.TFAE.out confluent_equivalents 1 0

theorem Confluent_iff_ChurchRosser : Confluent r ↔ ChurchRosser r :=
  List.TFAE.out confluent_equivalents 2 0

theorem Confluent_iff_SemiConfluent : Confluent r ↔ SemiConfluent r :=
  List.TFAE.out confluent_equivalents 2 1

theorem Confluent_of_unique_end {x : α} (h : ∀ y : α, ReflTransGen r y x) : Confluent r := by
  intro a b c hab hac
  exact ⟨x, h b, h c⟩

/-- An element is reducible with respect to a relation if there is a value it is related to. -/
abbrev Reducible (r : α → α → Prop) (x : α) : Prop := ∃ y, r x y

/-- An element is normal if it is not reducible. -/
abbrev Normal (r : α → α → Prop) (x : α) : Prop := ¬ Reducible r x

theorem Normal_iff (r : α → α → Prop) (x : α) : Normal r x ↔ ∀ y, ¬ r x y := by
  rw [Normal, not_exists]

/-- An element is normalizable if it is related to a normal element. -/
abbrev Normalizable (r : α → α → Prop) (x : α) : Prop :=
  ∃ n, ReflTransGen r x n ∧ Normal r n

/-- A relation is normalizing when every element is normalizable. -/
abbrev Normalizing (r : α → α → Prop) : Prop :=
  ∀ x, Normalizable r x

/-- A multi-step from a normal form must be reflexive. -/
@[grind =>]
theorem Normal.reflTransGen_eq (h : Normal r x) (xy : ReflTransGen r x y) : x = y := by
  induction xy <;> grind

/-- For a Church-Rosser relation, elements in an equivalence class must be multi-step related. -/
theorem ChurchRosser.normal_eqvGen_reflTransGen (cr : ChurchRosser r) (norm : Normal r x)
    (xy : EqvGen r y x) : ReflTransGen r y x := by
  have ⟨_, _, _⟩ := cr xy
  grind

/-- For a Church-Rosser relation there is one normal form in each equivalence class. -/
theorem ChurchRosser.normal_eq (cr : ChurchRosser r) (nx : Normal r x) (ny : Normal r y)
    (xy : EqvGen r x y) : x = y := by
  have ⟨_, _, _⟩ := cr xy
  grind

/-- A pair of subrelations lifts to transitivity on the relation. -/
def trans_of_subrelation (s s' r : α → α → Prop) (hr : Transitive r)
    (h : Subrelation s r) (h' : Subrelation s' r) : Trans s s' r where
  trans hab hbc := hr (h hab) (h' hbc)

/-- A subrelation lifts to transitivity on the left of the relation. -/
def trans_of_subrelation_left (s r : α → α → Prop) (hr : Transitive r)
    (h : Subrelation s r) : Trans s r r where
  trans hab hbc := hr (h hab) hbc

/-- A subrelation lifts to transitivity on the right of the relation. -/
def trans_of_subrelation_right (s r : α → α → Prop) (hr : Transitive r)
    (h : Subrelation s r) : Trans r s r where
  trans hab hbc := hr hab (h hbc)

/-- Confluence implies that multi-step joinability is an equivalence. -/
theorem Confluent.equivalence_join_reflTransGen (h : Confluent r) :
    Equivalence (Join (ReflTransGen r)) := by
  grind [equivalence_join, reflexive_reflTransGen, transitive_reflTransGen]

/-- A relation is terminating when the inverse of its transitive closure is well-founded.
  Note that this is also called Noetherian or strongly normalizing in the literature. -/
abbrev Terminating (r : α → α → Prop) := WellFounded (fun a b => r b a)

theorem Terminating.toTransGen (ht : Terminating r) : Terminating (TransGen r) := by
  suffices _ : (fun a b => TransGen r b a) = TransGen (Function.swap r) by grind
  grind [transGen_swap]

theorem Terminating.ofTransGen : Terminating (TransGen r) → Terminating r := by
  suffices _ : (fun a b => TransGen r b a) = TransGen (Function.swap r) by grind
  grind [transGen_swap]

theorem Terminating.iff_transGen : Terminating (TransGen r) ↔ Terminating r :=
  ⟨ofTransGen, toTransGen⟩

theorem Terminating.subrelation {r' : α → α → Prop} (hr : Terminating r) (h : Subrelation r' r) :
    Terminating r' := by
  rw [Terminating, wellFounded_iff_isEmpty_descending_chain] at hr ⊢
  rw [isEmpty_subtype]
  intro f hf
  exact hr.elim ⟨f, fun n ↦ by exact h (hf n)⟩

theorem Terminating.isNormalizing (h : Terminating r) : Normalizing r := by
  unfold Terminating at h
  intro t
  apply WellFounded.induction h t
  intro a ih
  by_cases ha : Reducible r a
  · obtain ⟨b, hab⟩ := ha
    obtain ⟨n, hbn, hn⟩ := ih b hab
    exact ⟨n, ReflTransGen.head hab hbn, hn⟩
  · use a

theorem Terminating.isConfluent_iff_all_unique_Normal (ht : Terminating r) :
    Confluent r ↔ ∀ a : α, ∃! n : α, ReflTransGen r a n ∧ Normal r n := by
  have hn : Normalizing r := ht.isNormalizing
  constructor
  · intro hc a
    apply existsUnique_of_exists_of_unique (hn a)
    rintro n₁ n₂ ⟨hr₁, hn₁⟩ ⟨hr₂, hn₂⟩
    have hj : Join (ReflTransGen r) n₁ n₂ := hc hr₁ hr₂
    obtain ⟨m, h₁, h₂⟩ := hj
    rw [Normal.reflTransGen_eq hn₁ h₁, Normal.reflTransGen_eq hn₂ h₂]
  · intro h a b c hab hac
    obtain ⟨na, ⟨han, hnnor⟩, H⟩ := h a
    use na
    obtain ⟨nb, hbnb, hnb⟩ := hn b
    obtain ⟨nc, hcnc, hnc⟩ := hn c
    have hanb : (ReflTransGen r) a nb := ReflTransGen.trans hab hbnb
    have hanc : (ReflTransGen r) a nc := ReflTransGen.trans hac hcnc
    have hnanb : nb = na := H nb ⟨hanb, hnb⟩
    have hnanc : nc = na := H nc ⟨hanc, hnc⟩
    rw [hnanb] at hbnb
    rw [hnanc] at hcnc
    exact ⟨hbnb, hcnc⟩

/-- A relation is convergent when it is both confluent and terminating. -/
abbrev Convergent (r : α → α → Prop) := Confluent r ∧ Terminating r

theorem Convergent.isTerminating (h : Convergent r) : Terminating r := h.right

theorem Convergent.isConfluent (h : Convergent r) : Confluent r := h.left

theorem Convergent.isNormalizing (h : Convergent r) : Normalizing r := h.isTerminating.isNormalizing

theorem Convergent.unique_Normal (h : Convergent r) :
    ∀ a : α, ∃! n : α, ReflTransGen r a n ∧ Normal r n :=
  h.isTerminating.isConfluent_iff_all_unique_Normal.mp h.isConfluent

/-- A relation is locally confluent when all reductions with a common origin are multi-joinable -/
abbrev LocallyConfluent (r : α → α → Prop) :=
  ∀ {a b c : α}, r a b → r a c → Join (ReflTransGen r) b c

theorem Confluent.toLocallyConfluent (h : Confluent r) : LocallyConfluent r := by
  intro _ _ _ ab ac
  exact h (.single ab) (.single ac)

/-- Newman's lemma: a terminating, locally confluent relation is confluent. -/
theorem LocallyConfluent.Terminating_toConfluent (hlc : LocallyConfluent r) (ht : Terminating r) :
    Confluent r := by
  intro x
  induction x using ht.induction with
  | h x ih =>
    intro y z xy xz
    cases xy.cases_head with
    | inl => exists z; grind
    | inr h =>
      obtain ⟨y₁, x_y₁, y₁_y⟩ := h
      cases xz.cases_head with
      | inl => exists y; grind
      | inr h =>
        obtain ⟨z₁, x_z₁, z₁_z⟩ := h
        have ⟨u, z₁_u, y₁_u⟩ := hlc x_z₁ x_y₁
        have ⟨v, uv, yv⟩ : Join (ReflTransGen r) u y := by grind
        have ⟨w, vw, zw⟩ : Join (ReflTransGen r) v z := by grind [ReflTransGen.trans]
        exact ⟨w, .trans yv vw, zw⟩

/-- A relation is strongly confluent when single steps are reflexive- and multi-joinable. -/
abbrev StronglyConfluent (r : α → α → Prop) :=
  ∀ {x y₁ y₂}, r x y₁ → r x y₂ → ∃ z, ReflGen r y₁ z ∧ ReflTransGen r y₂ z

/-- Generalization of `Confluent` to two relations. -/
def Commute (r₁ r₂ : α → α → Prop) := ∀ {x y₁ y₂},
  ReflTransGen r₁ x y₁ → ReflTransGen r₂ x y₂ → ∃ z, ReflTransGen r₂ y₁ z ∧ ReflTransGen r₁ y₂ z

theorem Commute.symmetric : Symmetric (@Commute α) := by
  intro r₁ r₂ h x y₁ y₂ x_y₁ x_y₂
  obtain ⟨_, _, _⟩ := h x_y₂ x_y₁
  grind

theorem Commute.toConfluent : Commute r r = Confluent r := rfl

/-- Generalization of `StronglyConfluent` to two relations. -/
def StronglyCommute (r₁ r₂ : α → α → Prop) :=
  ∀ {x y₁ y₂}, r₁ x y₁ → r₂ x y₂ → ∃ z, ReflGen r₂ y₁ z ∧ ReflTransGen r₁ y₂ z

theorem StronglyCommute.toStronglyConfluent : StronglyCommute r r = StronglyConfluent r := rfl

/-- Generalization of `Diamond` to two relations. -/
def DiamondCommute (r₁ r₂ : α → α → Prop) :=
  ∀ {x y₁ y₂}, r₁ x y₁ → r₂ x y₂ → ∃ z, r₂ y₁ z ∧ r₁ y₂ z

theorem DiamondCommute.toDiamond : DiamondCommute r r = Diamond r := by rfl

theorem StronglyCommute.extend (h : StronglyCommute r₁ r₂) (xy : ReflTransGen r₁ x y)
    (xz : r₂ x z) : ∃ w, ReflGen r₂ y w ∧ ReflTransGen r₁ z w := by
  induction xy with
  | refl => exact ⟨z, .single xz, .refl⟩
  | @tail b c _ bc ih =>
    obtain ⟨w, bw, zw⟩ := ih
    cases bw with
    | refl => exact ⟨c, .refl, zw.trans (.single bc)⟩
    | single bw => cases h bc bw; grind [ReflTransGen.trans]

theorem StronglyCommute.toCommute (h : StronglyCommute r₁ r₂) : Commute r₁ r₂ := by
  intro x y₁ y₂ x_y₁ x_y₂
  induction x_y₂ with
  | refl => exists y₁
  | @tail a b xa ab ih =>
    obtain ⟨z, y₁_z, y₂_z⟩ := ih
    obtain ⟨w, zw, bw⟩ := h.extend y₂_z ab
    exact ⟨w, y₁_z.trans zw.to_reflTransGen, bw⟩

theorem StronglyConfluent.toConfluent (h : StronglyConfluent r) : Confluent r :=
  StronglyCommute.toCommute h

variable {r₁ r₂ : α → α → Prop}

@[scoped grind <=]
theorem join_inl (r₁_ab : r₁ a b) : (r₁ ⊔ r₂) a b :=
  Or.inl r₁_ab

@[scoped grind <=]
theorem join_inr (r₂_ab : r₂ a b) : (r₁ ⊔ r₂) a b :=
  Or.inr r₂_ab

@[scoped grind <=]
theorem join_inl_reflTransGen (r₁_ab : ReflTransGen r₁ a b) : ReflTransGen (r₁ ⊔ r₂) a b := by
  induction r₁_ab <;> grind

@[scoped grind <=]
theorem join_inr_reflTransGen (r₂_ab : ReflTransGen r₂ a b) : ReflTransGen (r₁ ⊔ r₂) a b := by
  induction r₂_ab <;> grind

lemma Commute.join_left (c₁ : Commute r₁ r₃) (c₂ : Commute r₂ r₃) : Commute (r₁ ⊔ r₂) r₃ := by
  intro x y z xy xz
  induction xy with
  | refl => grind
  | @tail b c _ bc ih =>
    have ⟨w, bw, _⟩ := ih
    cases bc with
    | inl bc =>
      obtain ⟨_, _, _⟩ := c₁ (.single bc) bw
      grind [ReflTransGen.trans]
    | inr bc =>
      obtain ⟨_, _, _⟩ := c₂ (.single bc) bw
      grind [ReflTransGen.trans]

theorem Commute.join_confluent (c₁ : Confluent r₁) (c₂ : Confluent r₂) (comm : Commute r₁ r₂) :
    Confluent (r₁ ⊔ r₂) := by
  intro a b c ab ac
  induction ab generalizing c with
  | refl => exists c
  | @tail x y ax xy ih =>
    have h_comm : Commute (r₁ ⊔ r₂) (r₁ ⊔ r₂) := by apply_rules [join_left, symmetric]
    obtain ⟨z, xz, cz⟩ := ih ac
    obtain ⟨w, yw, zw⟩ := h_comm (.single xy) xz
    exact ⟨w, yw, cz.trans zw⟩

/-- If a relation is squeezed by a relation and its multi-step closure, they are multi-step equal -/
theorem reflTransGen_mono_closed (h₁ : Subrelation r₁ r₂) (h₂ : Subrelation r₂ (ReflTransGen r₁)) :
    ReflTransGen r₁ = ReflTransGen r₂ := by
  ext
  exact ⟨ReflTransGen.mono @h₁, reflTransGen_closed @h₂⟩

lemma ReflGen.compRel_symm : ReflGen (SymmGen r) a b → ReflGen (SymmGen r) b a
| .refl => .refl
| .single (.inl h) => .single (.inr h)
| .single (.inr h) => .single (.inl h)

@[simp, grind =]
theorem reflTransGen_compRel : ReflTransGen (SymmGen r) = EqvGen r := by
  ext a b
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | tail hab hbc ih =>
      cases hbc with
      | inl h => exact ih.trans _ _ _ (.rel _ _ h)
      | inr h => exact ih.trans _ _ _ (.symm _ _ (.rel _ _ h))
  · intro h
    induction h with
    | rel _ _ ih => exact .single (.inl ih)
    | refl x => exact .refl
    | symm x y eq ih =>
      rw [symmGen_swap]
      exact reflTransGen_swap.mp ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `Relator.RightUnique` corresponds to deterministic reductions, which are confluent, as all
multi-reductions with a common origin start the same (this fact is
`Relation.ReflTransGen.total_of_right_unique`.) -/
theorem RightUnique.toConfluent (hr : Relator.RightUnique r) : Confluent r := by
  intro a b c ab ac
  obtain (h | h) := ReflTransGen.total_of_right_unique hr ab ac
  · use c
  · use b

public meta section

open Lean Elab Meta Command Term

/--
  This command adds notations for relations. This should not usually be called directly, but from
  the `reduction_sys` attribute.

  As an example `reduction_notation foo "β"` will add the notations "⭢β" and "↠β".

  Note that the string used will afterwards be registered as a notation. This means that if you have
  also used this as a constructor name, you will need quotes to access corresponding cases, e.g. «β»
  in the above example.
-/
syntax attrKind "reduction_notation" ident (str)? : command
macro_rules
  | `($kind:attrKind reduction_notation $rel $sym) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ⭢" $sym:str t':39 => $rel t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ↠" $sym:str t':39 => Relation.ReflTransGen $rel t t'
     )
  | `($kind:attrKind reduction_notation $rel) =>
    `(
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ⭢ " t':39 => $rel t t'
      @[nolint docBlame]
      $kind:attrKind notation3 t:39 " ↠ " t':39 => Relation.ReflTransGen $rel t t'
     )


/--
  This attribute calls the `reduction_notation` command for the annotated declaration, such as in:

  ```
  @[reduction_sys "ₙ", simp]
  def PredReduction (a b : ℕ) : Prop := a = b + 1
  ```
-/
syntax (name := reduction_sys) "reduction_sys" (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `reduction_sys
  descr := "Register notation for a relation and its closures."
  add := fun decl stx _ => MetaM.run' do
    match stx with
    | `(attr | reduction_sys $sym) =>
        let mut sym := sym
        unless sym.getString.endsWith " " do
          sym := Syntax.mkStrLit (sym.getString ++ " ")
        liftCommandElabM <| do
          modifyScope ({ · with currNamespace := decl.getPrefix })
          elabCommand (← `(scoped reduction_notation $(mkIdent decl) $sym))
    | `(attr | reduction_sys) =>
        liftCommandElabM <| do
          modifyScope ({ · with currNamespace := decl.getPrefix })
          elabCommand (← `(scoped reduction_notation $(mkIdent decl)))
    | _ => throwError "invalid syntax for 'reduction_sys' attribute"
}

end

end Relation
