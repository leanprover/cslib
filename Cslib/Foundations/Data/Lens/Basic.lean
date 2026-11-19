/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/

module

public import Cslib.Init
public import Mathlib.Logic.Equiv.Defs

/-!
# Lawful Lenses for Verified State Access

This module defines polymorphic lenses (`Lens`) and well-behaved lenses (`LawfulLens`) for
compositional state access and update, together with lens independence (`Lens.Independent`) for
reasoning about orthogonal state components.

## Main definitions

* `Cslib.Lens`: A pair of `get : S → A` and `set : S → A → S` operations focusing on a view `A`
  within a state `S`.
* `Cslib.Lens.over`: Modify the focused view in a state by applying an endofunction `A → A`.
* `Cslib.Lens.id`, `Cslib.Lens.comp`: Identity lens and sequential lens composition.
* `Cslib.Lens.Independent`: Orthogonality predicate for two lenses focusing on disjoint parts of
  the same state.
* `Cslib.LawfulLens`: A `Lens` satisfying the three put-get (`get_set`), get-put (`set_get`), and
  put-put (`set_set`) laws.
* `Cslib.LawfulLens.fst`, `Cslib.LawfulLens.snd`, `Cslib.LawfulLens.ofEquiv`,
  `Cslib.LawfulLens.prod`: Standard lawful lenses for products, equivalences, and independent
  lens pairing.
-/

@[expose] public section

namespace Cslib

universe u v w x

/-- A `Lens S A` focuses on a component of type `A` inside a state of type `S` via total `get` and
`set` operations. -/
structure Lens (S : Type u) (A : Type v) where
  /-- Extract the focused component of type `A` from a state of type `S`. -/
  get : S → A
  /-- Replace the focused component of type `A` in a state of type `S`. -/
  set : S → A → S

namespace Lens

variable {S : Type u} {A : Type v} {B : Type w} {C : Type x}

/-- Two lenses are equal if they have the same getter and setter on all inputs. -/
@[ext]
theorem ext {l₁ l₂ : Lens S A} (hget : ∀ s, l₁.get s = l₂.get s)
    (hset : ∀ s a, l₁.set s a = l₂.set s a) : l₁ = l₂ := by
  cases l₁
  cases l₂
  simp only [mk.injEq]
  exact ⟨funext hget, funext₂ hset⟩

@[simp]
theorem get_mk (g : S → A) (st : S → A → S) (s : S) : (Lens.mk g st).get s = g s := rfl

@[simp]
theorem set_mk (g : S → A) (st : S → A → S) (s : S) (a : A) :
    (Lens.mk g st).set s a = st s a := rfl

/-- Modify the focused part of `s` by applying `f` to its current value. -/
def over (l : Lens S A) (f : A → A) (s : S) : S :=
  l.set s (f (l.get s))

/-- Alias for `Lens.over`. -/
abbrev modify (l : Lens S A) (f : A → A) (s : S) : S :=
  l.over f s

theorem over_def (l : Lens S A) (f : A → A) (s : S) : l.over f s = l.set s (f (l.get s)) := rfl

@[simp, scoped grind =]
theorem over_const (l : Lens S A) (a : A) (s : S) :
    l.over (Function.const A a) s = l.set s a := rfl

/-- The identity lens focusing on the entire state `S`. -/
protected def id : Lens S S where
  get s := s
  set _ a := a

@[simp, scoped grind =]
theorem id_get (s : S) : (Lens.id : Lens S S).get s = s := rfl

@[simp, scoped grind =]
theorem id_set (s a : S) : (Lens.id : Lens S S).set s a = a := rfl

@[simp, scoped grind =]
theorem id_over (f : S → S) (s : S) : (Lens.id : Lens S S).over f s = f s := rfl

/-- Compose `l₁ : Lens S A` and `l₂ : Lens A B` to focus on `B` inside `S`. -/
def comp (l₁ : Lens S A) (l₂ : Lens A B) : Lens S B where
  get s := l₂.get (l₁.get s)
  set s b := l₁.set s (l₂.set (l₁.get s) b)

@[simp, scoped grind =]
theorem comp_get (l₁ : Lens S A) (l₂ : Lens A B) (s : S) :
    (l₁.comp l₂).get s = l₂.get (l₁.get s) := rfl

@[simp, scoped grind =]
theorem comp_set (l₁ : Lens S A) (l₂ : Lens A B) (s : S) (b : B) :
    (l₁.comp l₂).set s b = l₁.set s (l₂.set (l₁.get s) b) := rfl

/-- Modifying through a composite lens equals nested modification. -/
theorem comp_over (l₁ : Lens S A) (l₂ : Lens A B) (f : B → B) (s : S) :
    (l₁.comp l₂).over f s = l₁.over (l₂.over f) s := rfl

/-- Right identity law for lens composition. -/
@[simp, scoped grind =]
theorem comp_id (l : Lens S A) : l.comp Lens.id = l := rfl

/-- Left identity law for lens composition. -/
@[simp, scoped grind =]
theorem id_comp (l : Lens S A) : Lens.id.comp l = l := rfl

/-- Associativity of lens composition. -/
theorem comp_assoc (l₁ : Lens S A) (l₂ : Lens A B) (l₃ : Lens B C) :
    (l₁.comp l₂).comp l₃ = l₁.comp (l₂.comp l₃) := rfl

/-- Lens focusing on the first projection of a product `A × B`. -/
def fst : Lens (A × B) A where
  get p := p.1
  set p a := (a, p.2)

@[simp, scoped grind =]
theorem fst_get (p : A × B) : (Lens.fst : Lens (A × B) A).get p = p.1 := rfl

@[simp, scoped grind =]
theorem fst_set (p : A × B) (a : A) : (Lens.fst : Lens (A × B) A).set p a = (a, p.2) := rfl

/-- Lens focusing on the second projection of a product `A × B`. -/
def snd : Lens (A × B) B where
  get p := p.2
  set p b := (p.1, b)

@[simp, scoped grind =]
theorem snd_get (p : A × B) : (Lens.snd : Lens (A × B) B).get p = p.2 := rfl

@[simp, scoped grind =]
theorem snd_set (p : A × B) (b : B) : (Lens.snd : Lens (A × B) B).set p b = (p.1, b) := rfl

/-- Construct a lens from an equivalence `S ≃ A`. -/
def ofEquiv (e : S ≃ A) : Lens S A where
  get := e
  set _ a := e.symm a

@[simp, scoped grind =]
theorem ofEquiv_get (e : S ≃ A) (s : S) : (Lens.ofEquiv e).get s = e s := rfl

@[simp, scoped grind =]
theorem ofEquiv_set (e : S ≃ A) (s : S) (a : A) : (Lens.ofEquiv e).set s a = e.symm a := rfl

/-- Two lenses on the same state `S` are *independent* (orthogonal) if setting either one preserves
the view of the other and updates through the two lenses commute. -/
structure Independent (l₁ : Lens S A) (l₂ : Lens S B) : Prop where
  /-- Setting `l₂` does not alter `l₁.get`. -/
  get_set_right : ∀ (s : S) (b : B), l₁.get (l₂.set s b) = l₁.get s
  /-- Setting `l₁` does not alter `l₂.get`. -/
  get_set_left : ∀ (s : S) (a : A), l₂.get (l₁.set s a) = l₂.get s
  /-- Setting `l₁` and `l₂` commutes. -/
  set_comm : ∀ (s : S) (a : A) (b : B), l₁.set (l₂.set s b) a = l₂.set (l₁.set s a) b

namespace Independent

variable {D : Type*} {l₁ : Lens S A} {l₂ : Lens S B}

/-- Lens independence is symmetric. -/
@[symm]
theorem symm (h : Independent l₁ l₂) : Independent l₂ l₁ where
  get_set_right := h.get_set_left
  get_set_left := h.get_set_right
  set_comm s b a := (h.set_comm s a b).symm

/-- Modifying through `l₂` preserves `l₁.get` when `l₁` and `l₂` are independent. -/
theorem get_over_right (h : Independent l₁ l₂) (g : B → B) (s : S) :
    l₁.get (l₂.over g s) = l₁.get s :=
  h.get_set_right s (g (l₂.get s))

/-- Modifying through `l₁` preserves `l₂.get` when `l₁` and `l₂` are independent. -/
theorem get_over_left (h : Independent l₁ l₂) (f : A → A) (s : S) :
    l₂.get (l₁.over f s) = l₂.get s :=
  h.get_set_left s (f (l₁.get s))

/-- Modifying `l₁` commutes with setting `l₂` when `l₁` and `l₂` are independent. -/
theorem over_set_comm (h : Independent l₁ l₂) (f : A → A) (b : B) (s : S) :
    l₁.over f (l₂.set s b) = l₂.set (l₁.over f s) b := by
  simp only [over, h.get_set_right, h.set_comm]

/-- Setting `l₁` commutes with modifying `l₂` when `l₁` and `l₂` are independent. -/
theorem set_over_comm (h : Independent l₁ l₂) (a : A) (g : B → B) (s : S) :
    l₁.set (l₂.over g s) a = l₂.over g (l₁.set s a) := by
  simp only [over, h.get_set_left, h.set_comm]

/-- Modifications through independent lenses commute. -/
theorem over_comm (h : Independent l₁ l₂) (f : A → A) (g : B → B) (s : S) :
    l₁.over f (l₂.over g s) = l₂.over g (l₁.over f s) := by
  simp only [over, h.get_set_right, h.get_set_left, h.set_comm]

/-- Post-composing independent lenses with arbitrary sub-lenses preserves independence. -/
theorem comp_right (h : Independent l₁ l₂) (l₃ : Lens A C) (l₄ : Lens B D) :
    Independent (l₁.comp l₃) (l₂.comp l₄) where
  get_set_right s d := by simp only [comp_get, comp_set, h.get_set_right]
  get_set_left s c := by simp only [comp_get, comp_set, h.get_set_left]
  set_comm s c d := by simp only [comp_set, h.get_set_right, h.get_set_left, h.set_comm]

end Independent

theorem independent_comm {l₁ : Lens S A} {l₂ : Lens S B} :
    Independent l₁ l₂ ↔ Independent l₂ l₁ :=
  ⟨Independent.symm, Independent.symm⟩

/-- Modifying `l₂` preserves `l₁.get` for independent lenses. -/
theorem get_over_of_independent {l₁ : Lens S A} {l₂ : Lens S B} (h : Independent l₁ l₂)
    (g : B → B) (s : S) : l₁.get (l₂.over g s) = l₁.get s :=
  h.get_over_right g s

/-- Modifications through independent lenses commute. -/
theorem over_comm_of_independent {l₁ : Lens S A} {l₂ : Lens S B} (h : Independent l₁ l₂)
    (f : A → A) (g : B → B) (s : S) : l₁.over f (l₂.over g s) = l₂.over g (l₁.over f s) :=
  h.over_comm f g s

/-- The first and second projection lenses on `A × B` are independent. -/
theorem fst_snd_independent : Independent (Lens.fst : Lens (A × B) A) (Lens.snd : Lens (A × B) B)
    where
  get_set_right _ _ := rfl
  get_set_left _ _ := rfl
  set_comm _ _ _ := rfl

end Lens

/-- A `LawfulLens S A` is a `Lens S A` satisfying the three classical lens laws:
* `get_set` (PutGet): getting after setting returns the value that was set;
* `set_get` (GetPut): setting the current value leaves the state unchanged;
* `set_set` (PutPut): setting twice is equivalent to keeping only the second update. -/
structure LawfulLens (S : Type u) (A : Type v) extends Lens S A where
  /-- Getting the view immediately after setting `a` yields `a`. -/
  get_set : ∀ (s : S) (a : A), get (set s a) = a
  /-- Setting the focused component back to its current value leaves the state unchanged. -/
  set_get : ∀ (s : S), set s (get s) = s
  /-- Setting twice overwrites the first update with the second. -/
  set_set : ∀ (s : S) (a b : A), set (set s a) b = set s b

attribute [simp, scoped grind =] LawfulLens.get_set LawfulLens.set_get LawfulLens.set_set
attribute [coe] LawfulLens.toLens

namespace LawfulLens

variable {S : Type u} {A : Type v} {B : Type w} {C : Type x}

instance : Coe (LawfulLens S A) (Lens S A) := ⟨LawfulLens.toLens⟩

/-- Forgetting the proof fields from `LawfulLens` to `Lens` is injective. -/
theorem toLens_injective : Function.Injective (LawfulLens.toLens (S := S) (A := A)) := by
  rintro ⟨l₁, _, _, _⟩ ⟨l₂, _, _, _⟩ h
  cases h
  rfl

@[simp]
theorem toLens_inj {l₁ l₂ : LawfulLens S A} : l₁.toLens = l₂.toLens ↔ l₁ = l₂ :=
  toLens_injective.eq_iff

/-- Two lawful lenses are equal if they have the same getter and setter on all inputs. -/
@[ext]
theorem ext {l₁ l₂ : LawfulLens S A} (hget : ∀ s, l₁.get s = l₂.get s)
    (hset : ∀ s a, l₁.set s a = l₂.set s a) : l₁ = l₂ :=
  toLens_injective (Lens.ext hget hset)

/-- For lawful lenses, equality of setters alone already implies equality of lenses. -/
theorem ext_set {l₁ l₂ : LawfulLens S A} (hset : ∀ s a, l₁.set s a = l₂.set s a) : l₁ = l₂ := by
  ext s a
  · calc
      l₁.get s = l₁.get (l₂.set s (l₂.get s)) := by rw [l₂.set_get]
      _ = l₁.get (l₁.set s (l₂.get s)) := by rw [hset]
      _ = l₂.get s := l₁.get_set s (l₂.get s)
  · exact hset s a

/-- Modify the focused part of `s` by applying `f` to its current value. -/
abbrev over (l : LawfulLens S A) (f : A → A) (s : S) : S :=
  l.toLens.over f s

/-- Alias for `LawfulLens.over`. -/
abbrev modify (l : LawfulLens S A) (f : A → A) (s : S) : S :=
  l.toLens.over f s

theorem over_def (l : LawfulLens S A) (f : A → A) (s : S) :
    l.over f s = l.set s (f (l.get s)) := rfl

/-- Modifying by the identity function leaves the state unchanged. -/
@[simp, scoped grind =]
theorem over_id (l : LawfulLens S A) (s : S) : l.over _root_.id s = s := by
  simp [Lens.over]

/-- Modifying by `fun a => a` leaves the state unchanged. -/
theorem over_id' (l : LawfulLens S A) (s : S) : l.over (fun a => a) s = s := by
  simp [Lens.over]

/-- Getting the view after `over f` applies `f` to the previous view. -/
@[simp, scoped grind =]
theorem get_over (l : LawfulLens S A) (f : A → A) (s : S) :
    l.get (l.over f s) = f (l.get s) := by
  simp [Lens.over]

/-- Setting after `over f` overwrites the modification. -/
@[simp, scoped grind =]
theorem set_over (l : LawfulLens S A) (f : A → A) (s : S) (a : A) :
    l.set (l.over f s) a = l.set s a := by
  simp [Lens.over]

/-- Modifying after setting `a` is equivalent to setting `f a`. -/
@[simp, scoped grind =]
theorem over_set (l : LawfulLens S A) (f : A → A) (s : S) (a : A) :
    l.over f (l.set s a) = l.set s (f a) := by
  simp [Lens.over]

/-- Sequential modifications through the same lawful lens fuse via function composition. -/
@[simp]
theorem over_over (l : LawfulLens S A) (g f : A → A) (s : S) :
    l.over g (l.over f s) = l.over (g ∘ f) s := by
  simp [Lens.over]

/-- The identity lawful lens on `S`. -/
protected def id : LawfulLens S S where
  toLens := Lens.id
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

@[simp, scoped grind =]
theorem id_toLens : (LawfulLens.id : LawfulLens S S).toLens = Lens.id := rfl

@[simp, scoped grind =]
theorem id_get (s : S) : (LawfulLens.id : LawfulLens S S).get s = s := rfl

@[simp, scoped grind =]
theorem id_set (s a : S) : (LawfulLens.id : LawfulLens S S).set s a = a := rfl

@[simp, scoped grind =]
theorem id_over (f : S → S) (s : S) : (LawfulLens.id : LawfulLens S S).over f s = f s := rfl

/-- Compose two lawful lenses `l₁ : LawfulLens S A` and `l₂ : LawfulLens A B`. -/
def comp (l₁ : LawfulLens S A) (l₂ : LawfulLens A B) : LawfulLens S B where
  toLens := l₁.toLens.comp l₂.toLens
  get_set s b := by simp
  set_get s := by simp
  set_set s a b := by simp

@[simp, scoped grind =]
theorem comp_toLens (l₁ : LawfulLens S A) (l₂ : LawfulLens A B) :
    (l₁.comp l₂).toLens = l₁.toLens.comp l₂.toLens := rfl

@[simp, scoped grind =]
theorem comp_get (l₁ : LawfulLens S A) (l₂ : LawfulLens A B) (s : S) :
    (l₁.comp l₂).get s = l₂.get (l₁.get s) := rfl

@[simp, scoped grind =]
theorem comp_set (l₁ : LawfulLens S A) (l₂ : LawfulLens A B) (s : S) (b : B) :
    (l₁.comp l₂).set s b = l₁.set s (l₂.set (l₁.get s) b) := rfl

/-- Modifying through a composite lawful lens equals nested modification. -/
theorem comp_over (l₁ : LawfulLens S A) (l₂ : LawfulLens A B) (f : B → B) (s : S) :
    (l₁.comp l₂).over f s = l₁.over (l₂.over f) s := rfl

/-- Right identity law for lawful lens composition. -/
@[simp, scoped grind =]
theorem comp_id (l : LawfulLens S A) : l.comp LawfulLens.id = l :=
  toLens_injective (Lens.comp_id l.toLens)

/-- Left identity law for lawful lens composition. -/
@[simp, scoped grind =]
theorem id_comp (l : LawfulLens S A) : LawfulLens.id.comp l = l :=
  toLens_injective (Lens.id_comp l.toLens)

/-- Associativity of lawful lens composition. -/
theorem comp_assoc (l₁ : LawfulLens S A) (l₂ : LawfulLens A B) (l₃ : LawfulLens B C) :
    (l₁.comp l₂).comp l₃ = l₁.comp (l₂.comp l₃) :=
  toLens_injective (Lens.comp_assoc l₁.toLens l₂.toLens l₃.toLens)

/-- Lawful lens focusing on the first component of a product `A × B`. -/
def fst : LawfulLens (A × B) A where
  toLens := Lens.fst
  get_set _ _ := rfl
  set_get p := Prod.eta p
  set_set _ _ _ := rfl

@[simp, scoped grind =]
theorem fst_toLens : (LawfulLens.fst : LawfulLens (A × B) A).toLens = Lens.fst := rfl

@[simp, scoped grind =]
theorem fst_get (p : A × B) : (LawfulLens.fst : LawfulLens (A × B) A).get p = p.1 := rfl

@[simp, scoped grind =]
theorem fst_set (p : A × B) (a : A) :
    (LawfulLens.fst : LawfulLens (A × B) A).set p a = (a, p.2) := rfl

/-- Lawful lens focusing on the second component of a product `A × B`. -/
def snd : LawfulLens (A × B) B where
  toLens := Lens.snd
  get_set _ _ := rfl
  set_get p := Prod.eta p
  set_set _ _ _ := rfl

@[simp, scoped grind =]
theorem snd_toLens : (LawfulLens.snd : LawfulLens (A × B) B).toLens = Lens.snd := rfl

@[simp, scoped grind =]
theorem snd_get (p : A × B) : (LawfulLens.snd : LawfulLens (A × B) B).get p = p.2 := rfl

@[simp, scoped grind =]
theorem snd_set (p : A × B) (b : B) :
    (LawfulLens.snd : LawfulLens (A × B) B).set p b = (p.1, b) := rfl

/-- Construct a lawful lens from an equivalence `S ≃ A`. -/
def ofEquiv (e : S ≃ A) : LawfulLens S A where
  toLens := Lens.ofEquiv e
  get_set _ a := e.apply_symm_apply a
  set_get s := e.symm_apply_apply s
  set_set _ _ _ := rfl

@[simp, scoped grind =]
theorem ofEquiv_toLens (e : S ≃ A) : (LawfulLens.ofEquiv e).toLens = Lens.ofEquiv e := rfl

@[simp, scoped grind =]
theorem ofEquiv_get (e : S ≃ A) (s : S) : (LawfulLens.ofEquiv e).get s = e s := rfl

@[simp, scoped grind =]
theorem ofEquiv_set (e : S ≃ A) (s : S) (a : A) :
    (LawfulLens.ofEquiv e).set s a = e.symm a := rfl

/-- Two lawful lenses are independent if their underlying raw lenses are independent. -/
abbrev Independent (l₁ : LawfulLens S A) (l₂ : LawfulLens S B) : Prop :=
  Lens.Independent l₁.toLens l₂.toLens

/-- The first and second projection lawful lenses on `A × B` are independent. -/
theorem fst_snd_independent :
    Lens.Independent (LawfulLens.fst (A := A) (B := B)).toLens
      (LawfulLens.snd (A := A) (B := B)).toLens :=
  Lens.fst_snd_independent

/-- Modifying `l₂` preserves `l₁.get` for independent lawful lenses. -/
theorem get_over_of_independent {l₁ : LawfulLens S A} {l₂ : LawfulLens S B}
    (h : Independent l₁ l₂) (g : B → B) (s : S) :
    l₁.get (l₂.over g s) = l₁.get s :=
  h.get_over_right g s

/-- Modifications through independent lawful lenses commute. -/
theorem over_comm_of_independent {l₁ : LawfulLens S A} {l₂ : LawfulLens S B}
    (h : Independent l₁ l₂) (f : A → A) (g : B → B) (s : S) :
    l₁.over f (l₂.over g s) = l₂.over g (l₁.over f s) :=
  h.over_comm f g s

/-- Pre-composing two independent lenses on `A` with a lawful lens `LawfulLens S A` preserves
independence. -/
theorem Independent.comp_left (l : LawfulLens S A) {l₁ : Lens A B} {l₂ : Lens A C}
    (h : Lens.Independent l₁ l₂) :
    Lens.Independent (l.toLens.comp l₁) (l.toLens.comp l₂) where
  get_set_right s c := by simp [h.get_set_right]
  get_set_left s b := by simp [h.get_set_left]
  set_comm s b c := by simp [h.set_comm]

/-- Pair two independent lawful lenses `l₁ : LawfulLens S A` and `l₂ : LawfulLens S B` into a
lawful lens focusing on `A × B`. -/
def prod (l₁ : LawfulLens S A) (l₂ : LawfulLens S B) (h : Independent l₁ l₂) :
    LawfulLens S (A × B) where
  get s := (l₁.get s, l₂.get s)
  set s p := l₂.set (l₁.set s p.1) p.2
  get_set s p := by simp [h.get_set_right]
  set_get s := by simp
  set_set s p q := by
    simp only [h.set_comm (l₁.set s p.1) q.1 p.2, l₂.set_set, l₁.set_set]

@[simp, scoped grind =]
theorem prod_get (l₁ : LawfulLens S A) (l₂ : LawfulLens S B) (h : Independent l₁ l₂) (s : S) :
    (l₁.prod l₂ h).get s = (l₁.get s, l₂.get s) := rfl

@[simp, scoped grind =]
theorem prod_set (l₁ : LawfulLens S A) (l₂ : LawfulLens S B) (h : Independent l₁ l₂)
    (s : S) (p : A × B) :
    (l₁.prod l₂ h).set s p = l₂.set (l₁.set s p.1) p.2 := rfl

/-- Projecting the first component of a paired lens `l₁.prod l₂ h` recovers `l₁`. -/
@[simp]
theorem prod_comp_fst (l₁ : LawfulLens S A) (l₂ : LawfulLens S B) (h : Independent l₁ l₂) :
    (l₁.prod l₂ h).comp LawfulLens.fst = l₁ := by
  ext s a
  · rfl
  · simp only [comp_set, fst_set, prod_get, prod_set]
    rw [← h.get_set_left s a, l₂.set_get]

/-- Projecting the second component of a paired lens `l₁.prod l₂ h` recovers `l₂`. -/
@[simp]
theorem prod_comp_snd (l₁ : LawfulLens S A) (l₂ : LawfulLens S B) (h : Independent l₁ l₂) :
    (l₁.prod l₂ h).comp LawfulLens.snd = l₂ := by
  ext s b
  · rfl
  · simp

/-- If `l₁` and `l₂` are independent of `l₃` (and of each other), their product pairing
`l₁.prod l₂ h₁₂` is also independent of `l₃`. -/
theorem prod_independent {l₁ : LawfulLens S A} {l₂ : LawfulLens S B} {l₃ : LawfulLens S C}
    (h₁₂ : Independent l₁ l₂) (h₁₃ : Independent l₁ l₃) (h₂₃ : Independent l₂ l₃) :
    Independent (l₁.prod l₂ h₁₂) l₃ where
  get_set_right s c := by simp [h₁₃.get_set_right, h₂₃.get_set_right]
  get_set_left s p := by simp [h₂₃.get_set_left, h₁₃.get_set_left]
  set_comm s p c := by simp [h₁₃.set_comm, h₂₃.set_comm]

end LawfulLens

end Cslib
