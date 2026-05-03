/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Eric Wieser
-/

module

public import Cslib.Init

/-!
# Free Monad

This file defines a general `FreeM` monad construction for representing effectful programs
as pure syntax trees, separate from their interpretation.

The `FreeM` monad generates a free monad from any type constructor `f : Type → Type`, without
requiring `f` to be a `Functor`. This implementation uses the "freer monad" approach as the
traditional free monad is not safely definable in Lean due to termination checking.

In this construction, **effectful programs are represented as trees of effects**.
Each node (`FreeM.liftBind`) represents a request to perform an effect, accompanied by a
continuation specifying how the computation proceeds after the effect.
The leaves (`FreeM.pure`) represent completed computations with final results.

This separation of syntax from semantics enables multiple interpretations of the same program:
execution, static analysis, optimization, pretty-printing, verification, and more.

A key insight is that `FreeM F` satisfies the **universal property of free monads**: for any monad
`M` and effect handler `f : F → M`, there exists a unique way to interpret `FreeM F` computations
in `M` that respects the effect semantics given by `f`.
This unique interpreter is `FreeM.liftM f`


## Main Definitions

- `FreeM`: The free monad construction
- `FreeM.liftM`: The canonical interpreter satisfying the universal property
- `FreeM.liftM_unique`: Proof of the universal property

For elimination and interpretation theory, see `Free/Fold.lean`.

See the Haskell [freer-simple](https://hackage.haskell.org/package/freer-simple) library for the
Haskell implementation that inspired this approach.

## Implementation Notes

The `FreeM` monad is defined using an inductive type with constructors `.pure` and `.liftBind`.
We implement `Functor` and `Monad` instances, and prove the corresponding `LawfulFunctor`
and `LawfulMonad` instances.


The file `Free/Effects.lean` demonstrates practical applications by implementing State, Writer, and
Continuations monads using `FreeM` with appropriate effect signatures.

The file `Free/Fold.lean` provides the theory of the fold operation for free monads.

## References

* [Oleg Kiselyov, Hiromi Ishii. *Freer Monads, More Extensible Effects*][Kiselyov2015]
* [Bartosz Milewski. *The Dao of Functional Programming*][MilewskiDao]

## Tags

Free monad, state monad
-/

@[expose] public section

namespace Cslib

-- Disable generation of unneeded lemmas which the simpNF linter would complain about.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The Free monad over a type constructor `F`.

A `FreeM F a` is a tree of operations from the type constructor `F`, with leaves of type `a`.
It has two constructors: `pure` for wrapping a value of type `a`, and `liftBind` for
representing an operation from `F` followed by a continuation.

This construction provides a free monad for any type constructor `F`, allowing for composable
effect descriptions that can be interpreted later. Unlike the traditional free monad,
this does not require `F` to be a functor. -/
inductive FreeM.{u, v, w} (F : Type u → Type v) (α : Type w) where
  /-- The action that does nothing and returns `a`. -/
  | protected pure (a : α) : FreeM F α
  /-- Invoke the operation `op` with contuation `cont`.

  Note that Lean's inductive types prevent us splitting this into separate bind and lift
  constructors. -/
  | liftBind {ι : Type u} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

universe u v w w' w''

namespace FreeM
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''}

section notations

instance : Pure (FreeM F) where pure := .pure

@[simp]
theorem pure_eq_pure : FreeM.pure = (pure : α → FreeM F α) := rfl

/-- Bind operation for the `FreeM` monad.

The builtin `>>=` notation should be preferred when `α` and `β` are in the same universe. -/
protected def bind (x : FreeM F α) (f : α → FreeM F β) : FreeM F β :=
  match x with
  | .pure a => f a
  | .liftBind op cont => .liftBind op fun z => FreeM.bind (cont z) f

instance : Bind (FreeM F) where bind := .bind

/-- Note that this lemma does not always apply, as it is universe-constrained by `Bind.bind`. -/
@[simp]
theorem bind_eq_bind {α β : Type w} : (FreeM.bind : FreeM F α → _ → FreeM F β) = Bind.bind := rfl

/-- Map a function over a `FreeM` monad.

The builtin `<$>` notation should be preferred when `α` and `β` are in the same universe. -/
def map (f : α → β) : FreeM F α → FreeM F β
  | .pure a => .pure (f a)
  | .liftBind op cont => .liftBind op fun z => FreeM.map f (cont z)

instance : Functor (FreeM F) where
  map := .map

/-- Note that this lemma does not always apply, as it is universe-constrained by `Functor.map`. -/
@[simp]
theorem map_eq_map {α β : Type w} : FreeM.map (F := F) (α := α) (β := β) = Functor.map := rfl

/-- Lift an operation from the effect signature `F` into the `FreeM F` monad. -/
def lift (op : F ι) : FreeM F ι :=
  .liftBind op pure

@[simp]
lemma liftBind_eq (op : F ι) :
    liftBind op cont = (lift op : FreeM F ι).bind cont :=
  rfl

set_option linter.unusedVariables false in
/-- An override for the default induction principle that is in simp-normal form.

Note that when `α` and `ι` are in the same universe, this simplifies slightly further. -/
@[induction_eliminator]
protected theorem induction {motive : FreeM F α → Prop}
    (pure : ∀ a, motive (pure a))
    (lift_bind : ∀ {ι} (op : F ι) (cont : ι → FreeM F α) (ih : ∀ i, motive (cont i)),
      motive ((lift op).bind cont)) : ∀ x, motive x
  | .pure a => pure a
  | liftBind _ _ => lift_bind _ _ fun _ => FreeM.induction pure lift_bind _

end notations

protected theorem bind_assoc (x : FreeM F α) (f : α → FreeM F β) (g : β → FreeM F γ) :
    (x.bind f).bind g = x.bind (fun x => (f x).bind g) := by
  induction x with
  | pure a => rfl
  | lift_bind op cont ih => simp [← liftBind_eq, FreeM.bind, ih] at *

/-- `.pure a` followed by `bind` collapses immediately. -/
@[simp]
lemma pure_bind (a : α) (f : α → FreeM F β) : (pure a : FreeM F α).bind f = f a := rfl

@[simp]
lemma bind_pure : ∀ x : FreeM F α, x.bind pure = x
  | .pure a => rfl
  | liftBind op k => by simp [FreeM.bind, bind_pure, -bind_eq_bind]

@[simp]
lemma bind_pure_comp (f : α → β) : ∀ x : FreeM F α, x.bind (pure ∘ f) = map f x
  | .pure a => rfl
  | liftBind op k => by simp only [FreeM.bind, map, bind_pure_comp]

@[simp]
theorem map_pure (f : α → β) (x : α) : map f (pure x : FreeM F α) = pure (f x) := rfl

@[simp]
theorem map_bind (f : β → γ) (x : FreeM F α) (c : α → FreeM F β) :
    map f (x.bind c) = x.bind fun a => (c a).map f := by
  simp_rw [← bind_pure_comp, FreeM.bind_assoc]

@[simp]
theorem id_map : ∀ x : FreeM F α, map id x = x
  | .pure a => rfl
  | .liftBind op cont => by simp_all [map, id_map]

theorem comp_map (h : β → γ) (g : α → β) : ∀ x : FreeM F α, map (h ∘ g) x = map h (map g x)
  | .pure a => rfl
  | .liftBind op cont => by simp_all [map, comp_map]

instance : LawfulFunctor (FreeM F) where
  map_const := rfl
  id_map := id_map
  comp_map _ _ := comp_map _ _

instance : Monad (FreeM F) where

instance : LawfulMonad (FreeM F) := LawfulMonad.mk'
  (bind_pure_comp := bind_pure_comp)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := FreeM.bind_assoc)

section liftM
variable {m : Type u → Type w} [Monad m] {α β : Type u}

/--
Interpret a `FreeM F` computation into any monad `m` by providing an interpretation
function for the effect signature `F`.

This function defines the *canonical interpreter* from the free monad `FreeM F` into the target
monad `m`. It is the unique monad morphism that extends the effect handler
`interp : ∀ {β}, F β → m β` via the universal property of `FreeM`.
-/
protected def liftM (interp : {ι : Type u} → F ι → m ι) : FreeM F α → m α
  | .pure a => pure a
  | .liftBind op cont => interp op >>= fun result => (cont result).liftM interp

@[simp]
lemma liftM_pure (interp : {ι : Type u} → F ι → m ι) (a : α) :
    (pure a : FreeM F α).liftM interp = pure a := rfl

@[simp]
lemma liftM_lift_bind (interp : {ι : Type u} → F ι → m ι) (op : F β) (cont : β → FreeM F α) :
    ((lift op) >>= cont).liftM interp = (do let b ← interp op; (cont b).liftM interp) := by
  rfl

@[simp]
lemma liftM_lift [LawfulMonad m] (interp : {ι : Type u} → F ι → m ι) (op : F β) :
    (lift op).liftM interp = interp op := by
  simp_rw [lift, FreeM.liftM, _root_.bind_pure]

@[simp]
lemma liftM_bind [LawfulMonad m]
    (interp : {ι : Type u} → F ι → m ι) (x : FreeM F α) (f : α → FreeM F β) :
    (x >>= f).liftM interp = (do let a ← x.liftM interp; (f a).liftM interp) := by
  induction x generalizing f with
  | pure a => simp only [liftM_pure, LawfulMonad.pure_bind]
  | lift_bind op cont ih => simp [← ih]

@[simp]
lemma liftM_map [LawfulMonad m]
    (interp : {ι : Type u} → F ι → m ι) (f : α → β) (x : FreeM F α) :
    (f <$> x).liftM interp = f <$> x.liftM interp := by
  simp_rw [← LawfulMonad.bind_pure_comp, liftM_bind, liftM_pure]

@[simp]
lemma liftM_seq [LawfulMonad m]
    (interp : {ι : Type u} → F ι → m ι) (x : FreeM F (α → β)) (y : FreeM F α) :
    (x <*> y).liftM interp = x.liftM interp <*> y.liftM interp := by
  simp [seq_eq_bind_map]

@[simp]
lemma liftM_seqLeft [LawfulMonad m]
    (interp : {ι : Type u} → F ι → m ι) (x : FreeM F α) (y : FreeM F β) :
    (x <* y).liftM interp = x.liftM interp <* y.liftM interp := by
  simp [seqLeft_eq_bind]

@[simp]
lemma liftM_seqRight [LawfulMonad m]
    (interp : {ι : Type u} → F ι → m ι) (x : FreeM F α) (y : FreeM F β) :
    (x *> y).liftM interp = x.liftM interp *> y.liftM interp := by
  simp [seqRight_eq_bind]

/--
A predicate stating that `interp : FreeM F α → m α` is an interpreter for the effect
handler `handler : ∀ {α}, F α → m α`.

This means that `interp` is a monad morphism from the free monad `FreeM F` to the
monad `m`, and that it extends the interpretation of individual operations
given by `f`.

Formally, `interp` satisfies the two equations:
- `interp (pure a) = pure a`
- `interp (liftBind op k) = handler op >>= fun x => interp (k x)`
-/
structure Interprets (handler : {ι : Type u} → F ι → m ι) (interp : FreeM F α → m α) : Prop where
  apply_pure (a : α) : interp (.pure a) = pure a
  apply_lift_bind {ι : Type u} (op : F ι) (cont : ι → FreeM F α) :
    interp (lift op >>= cont) = handler op >>= fun x => interp (cont x)

theorem Interprets.eq {handler : {ι : Type u} → F ι → m ι} {interp : FreeM F α → m α}
    (h : Interprets handler interp) :
    interp = (·.liftM @handler) := by
  ext x
  induction x with
  | pure a => exact h.apply_pure a
  | lift_bind op cont ih =>
    simp [h.apply_lift_bind, ih]

theorem Interprets.liftM (handler : {ι : Type u} → F ι → m ι) :
    Interprets handler (·.liftM handler : FreeM F α → _) where
  apply_pure _ := rfl
  apply_lift_bind _ _ := rfl

/--
The universal property of the free monad `FreeM`.

That is, `liftM handler` is the unique interpreter that extends the effect handler `handler` to
interpret `FreeM F` computations in a monad `m`.
-/
theorem Interprets.iff (handler : {ι : Type u} → F ι → m ι) (interp : FreeM F α → m α) :
    Interprets handler interp ↔ interp = (·.liftM handler) :=
  ⟨(·.eq), fun h => h ▸ Interprets.liftM _⟩

end liftM

end FreeM

end Cslib
