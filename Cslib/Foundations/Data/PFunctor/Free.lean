/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Cslib.Foundations.Data.PFunctor.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Free Monad of a Polynomial Functor

We define the free monad on a **polynomial functor** (`PFunctor`), and prove some basic properties.

The free monad `PFunctor.FreeM P` definitionally extends the W-type construction with
an extra `pure` constructor (represented by adding a `PFunctor.linear` term over the return type),
yielding a monad that is free over the polynomial functor `P`.

## Comparison with `Cslib.FreeM`

`Cslib.FreeM F` (in `Cslib/Foundations/Control/Monad/Free.lean`) builds a free monad over an
arbitrary type constructor `F : Type u → Type v`, which need not be functorial.
Its `liftBind` constructor abstracts over the intermediate type `ι`:
```
| liftBind {ι : Type u} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
```

`PFunctor.FreeM P` instead takes a polynomial functor `P : PFunctor`, where the shapes
`P.A` and positions `P.B a` are given explicitly.
Its `liftBind` constructor uses the shape and continuation directly:
```
| liftBind (a : P.A) (cont : P.B a → P.FreeM α) : P.FreeM α
```

When the effect signature is naturally polynomial (a fixed set of operations, each with a
known return type), `PFunctor.FreeM` avoids the universe bump that the abstract `ι` in
`Cslib.FreeM` introduces.
Concretely, `PFunctor.FreeM P` is a genuine endofunctor on a single universe: for a ground
`P`, `P.FreeM α : Type` whenever `α : Type`, whereas `Cslib.FreeM F α : Type 1` for
`F : Type → Type`, since `liftBind` stores the intermediate type `ι : Type`.

This matters when a program must itself be a first-class value of the same kind, i.e. for
higher-order effects whose operations consume or return computations of the same monad
(schedulers, exception handlers, staged interpreters, higher-order oracles).
Such an effect's response type can be another `P.FreeM` computation, staying in one universe:
```
def coin : PFunctor.{0,0} := ⟨Bool, fun b => if b then Bool else Nat⟩
-- a `coin`-program is itself `Type 0`, so it can be another effect's response type:
def scheduler : PFunctor.{0,0} := ⟨Unit, fun _ => coin.FreeM Bool⟩  -- `Type 0`
```
With the abstract `ι`, the analogous program lives in `Type 1`, so an effect `Type → Type`
cannot return it; bumping the effect to `Type 1 → Type 1` pushes its programs to `Type 2`,
and so on without bound.

This construction is ported from the [VCV-io](https://github.com/dtumad/VCV-io) library.

## Main Definitions

- `PFunctor.FreeM`: The free monad on a polynomial functor.
- `PFunctor.FreeM.lift`: Lift a shape of the base polynomial functor into the free monad.
- `PFunctor.FreeM.liftObj`: Lift an object of the base polynomial functor into the free monad.
- `PFunctor.FreeM.liftM`: Interpret `FreeM P` into any other monad.

## Implementation Notes

`FreeM P α` is a `def`, not an `inductive`: it is the W-type of the polynomial functor
`P.add (C α)`, whose `C α`-shaped nodes are leaves carrying pure values. The raw W-type
representation is confined to the constructors `FreeM.pure` and `FreeM.liftBind`, the
recursor `FreeM.rec`, and a few (dis)equality lemmas; every other definition and proof
factors through this interface.
-/

@[expose] public section

universe u v uA uB

namespace PFunctor

/-- The free monad on a polynomial functor: the W-type of the polynomial functor obtained by\
adjoining a constant shape for each pure value to `P`. -/
def FreeM (P : PFunctor.{uA, uB}) (α : Type v) : Type (max uA uB v) :=
  PFunctor.W (P.add (.const α))

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α β γ : Type*}

/-- A leaf node wrapping a pure value. -/
protected def pure (a : α) : P.FreeM α := ⟨.inr a, PEmpty.elim⟩

/-- Invoke the operation `a : P.A` with continuation `cont : P.B a → P.FreeM α`. -/
@[match_pattern]
def liftBind (a : P.A) (cont : P.B a → P.FreeM α) : P.FreeM α := ⟨.inl a, cont⟩

/-- Lift a shape of the base polynomial functor into the free monad. -/
def lift (a : P.A) : P.FreeM (P.B a) := ⟨.inl a, PFunctor.FreeM.pure⟩

instance [Inhabited α] : Inhabited (P.FreeM α) := ⟨.pure default⟩

instance : Pure (P.FreeM) where pure := .pure

/-- All continuations stored at a pure W-node are equal because their domain is empty. -/
lemma pure_eq_mk_inl (a : α) (cont : PEmpty → P.FreeM α) :
    FreeM.pure a = (⟨.inr a, cont⟩ : P.FreeM α) :=
  congr_arg (WType.mk (Sum.inr a)) (funext PEmpty.rec)

/-- Recursor for `FreeM`, stated in terms of its pure and effect-node interface.
This is the only place the W-type representation is consumed; all other definitions factor
through it. Definitions made with it compute definitionally on both node shapes, see
`FreeM.rec_pure` and `FreeM.rec_lift_bind`. -/
protected def rec {motive : P.FreeM α → Sort u} (pure : ∀ a, motive (pure a))
    (liftBind : ∀ (a : P.A) (cont : P.B a → P.FreeM α) (_ih : ∀ i, motive (cont i)),
      motive (FreeM.liftBind a cont)) : ∀ x, motive x
  | ⟨.inr a, cont⟩ => pure_eq_mk_inl a cont ▸ pure a
  | ⟨.inl a, cont⟩ => liftBind a cont fun u => FreeM.rec pure liftBind (cont u)

@[simp]
theorem pure_eq_pure : (FreeM.pure : α → P.FreeM α) = pure := rfl

@[simp] lemma lift_ne_pure (a : P.A) (y : P.B a) :
    (lift a : P.FreeM (P.B a)) ≠ pure y := fun h => by cases congrArg PFunctor.W.head h

@[simp] lemma pure_ne_lift (a : P.A) (y : P.B a) :
    pure y ≠ (lift a : P.FreeM (P.B a)) := (lift_ne_pure a y).symm

/-- Bind operation for the `FreeM` monad, defined via `FreeM.rec`.

The builtin `>>=` notation should be preferred when `α` and `β` are in the same universe. -/
protected def bind (x : P.FreeM α) (f : α → P.FreeM β) : P.FreeM β :=
  FreeM.rec (motive := fun _ => P.FreeM β) f (fun a _ cont => .liftBind a cont) x

instance : Bind (P.FreeM) where bind := .bind

/-- Note that this lemma does not always apply, as it is universe-constrained by `Bind.bind`. -/
@[simp]
theorem bind_eq_bind {α β : Type v} :
    (FreeM.bind : P.FreeM α → _ → P.FreeM β) = Bind.bind := rfl

/-- Map a function over a `FreeM` computation, defined in terms of `FreeM.bind`.

The builtin `<$>` notation should be preferred when `α` and `β` are in the same universe. -/
def map (f : α → β) (x : P.FreeM α) : P.FreeM β := x.bind (FreeM.pure ∘ f)

instance : Functor (P.FreeM) where
  map := .map

/-- Note that this lemma does not always apply, as it is universe-constrained by `Functor.map`. -/
@[simp]
theorem map_eq_map {α β : Type v} :
    FreeM.map (P := P) (α := α) (β := β) = Functor.map := rfl

@[simp]
lemma liftBind_eq (a : P.A) (cont : P.B a → P.FreeM α) :
    FreeM.liftBind a cont = (FreeM.lift a).bind cont := rfl

@[simp]
lemma rec_pure {motive : P.FreeM α → Sort u} (hp : ∀ a, motive (pure a))
    (hlb : ∀ (a : P.A) (cont : P.B a → P.FreeM α) (_ih : ∀ i, motive (cont i)),
      motive (FreeM.liftBind a cont)) (a : α) :
    FreeM.rec hp hlb (pure a) = hp a := rfl

/-- `FreeM.rec` computes definitionally on effect nodes.
Stated for the simp-normal form `(FreeM.lift a).bind cont` of `FreeM.liftBind a cont`. -/
@[simp]
lemma rec_lift_bind {motive : P.FreeM α → Sort u} (hp : ∀ a, motive (pure a))
    (hlb : ∀ (a : P.A) (cont : P.B a → P.FreeM α) (_ih : ∀ i, motive (cont i)),
      motive (FreeM.liftBind a cont)) (a : P.A) (cont : P.B a → P.FreeM α) :
    FreeM.rec hp hlb ((FreeM.lift a).bind cont) =
      hlb a cont fun i => FreeM.rec hp hlb (cont i) := rfl

/-- Lift an object of the base polynomial functor into the free monad.

This lifts the shape `x.1` with `lift` and relabels the responses with `x.2`. We use the
universe-polymorphic `FreeM.map` rather than `<$>`, since the response type `P.B x.1` and the
target `α` need not lie in the same universe. -/
abbrev liftObj (x : P.Obj α) : P.FreeM α := (lift x.1).map x.2

instance : MonadLift P (P.FreeM) where
  monadLift x := FreeM.liftObj x

lemma monadLift_eq_liftObj (x : P.Obj α) : (x : P.FreeM α) = FreeM.liftObj x := rfl

/-- Case analysis for `FreeM`, stated in terms of its pure and effect-node interface and in
the same simp-normal form as `FreeM.induction`. -/
@[cases_eliminator]
protected def cases {motive : P.FreeM α → Sort u}
    (pure : ∀ a, motive (pure a))
    (lift_bind : ∀ (a : P.A) (cont : P.B a → P.FreeM α), motive ((FreeM.lift a).bind cont)) :
    ∀ x, motive x :=
  FreeM.rec pure fun a cont _ => lift_bind a cont

set_option linter.unusedVariables false in
/-- An override for the default induction principle that is in simp-normal form.

Note that when `α` and `P.B a` are in the same universe, this simplifies slightly further. -/
@[induction_eliminator]
protected theorem induction {motive : P.FreeM α → Prop}
    (pure : ∀ a, motive (pure a))
    (lift_bind : ∀ (a : P.A) (cont : P.B a → P.FreeM α) (ih : ∀ i, motive (cont i)),
      motive ((FreeM.lift a).bind cont)) : ∀ x, motive x :=
  FreeM.rec pure lift_bind

/-- `.pure a` followed by `bind` collapses immediately. -/
@[simp]
lemma pure_bind (a : α) (f : α → P.FreeM β) :
    (pure a : P.FreeM α).bind f = f a := rfl

@[simp]
lemma liftBind_bind (a : P.A) (cont : P.B a → P.FreeM β) (f : β → P.FreeM γ) :
    ((FreeM.lift a).bind cont).bind f = (FreeM.lift a).bind (fun u ↦ (cont u).bind f) := rfl

protected theorem bind_assoc (x : P.FreeM α) (f : α → P.FreeM β) (g : β → P.FreeM γ) :
    (x.bind f).bind g = x.bind (fun a => (f a).bind g) := by
  induction x with
  | pure a => rfl
  | lift_bind a cont ih => simp [ih]

@[simp]
lemma bind_pure (x : P.FreeM α) : x.bind pure = x := by
  induction x with
  | pure a => rfl
  | lift_bind a cont ih => simp [ih]

@[simp]
lemma bind_pure_comp (f : α → β) (x : P.FreeM α) : x.bind (pure ∘ f) = map f x := rfl

@[simp]
lemma map_pure (f : α → β) (a : α) :
    (pure a : P.FreeM α).map f = pure (f a) := rfl

@[simp]
lemma map_lift_bind (f : α → β) (a : P.A) (cont : P.B a → P.FreeM α) :
    ((FreeM.lift a).bind cont).map f = (FreeM.lift a).bind (fun u ↦ (cont u).map f) := rfl

@[simp]
lemma liftObj_bind (x : P.Obj α) (f : α → P.FreeM β) :
    (FreeM.liftObj x).bind f = FreeM.liftBind x.1 (fun a ↦ f (x.2 a)) := rfl

@[simp] lemma bind_eq_pure_iff (x : P.FreeM α) (f : α → P.FreeM β) (b : β) :
    x.bind f = pure b ↔ ∃ a, x = pure a ∧ f a = pure b := by
  cases x with
  | pure a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, hf⟩ => by cases h; exact hf⟩
  | lift_bind a cont =>
    constructor
    · intro h
      cases h
    · rintro ⟨_, h, _⟩
      cases h

@[simp] lemma pure_eq_bind_iff (x : P.FreeM α) (f : α → P.FreeM β) (b : β) :
    pure b = x.bind f ↔ ∃ a, x = pure a ∧ pure b = f a := by
  cases x with
  | pure a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, hf⟩ => by cases h; exact hf⟩
  | lift_bind a cont =>
    constructor
    · intro h
      cases h
    · rintro ⟨_, h, _⟩
      cases h

lemma lift_bind_ne_pure (a : P.A) (cont : P.B a → P.FreeM α) (y : α) :
    (FreeM.lift a).bind cont ≠ pure y := by simp

lemma pure_ne_lift_bind (a : P.A) (cont : P.B a → P.FreeM α) (y : α) :
    pure y ≠ (FreeM.lift a).bind cont := by simp

@[simp] lemma liftObj_ne_pure (x : P.Obj α) (y : α) :
    (liftObj x : P.FreeM α) ≠ pure y := lift_bind_ne_pure _ _ _

@[simp] lemma pure_ne_liftObj (x : P.Obj α) (y : α) :
    pure y ≠ (liftObj x : P.FreeM α) := pure_ne_lift_bind _ _ _

instance : Monad (P.FreeM) where

@[simp]
theorem id_map (x : P.FreeM α) : map id x = x := bind_pure x

theorem comp_map (h : β → γ) (g : α → β) (x : P.FreeM α) :
    map (h ∘ g) x = map h (map g x) :=
  (FreeM.bind_assoc x (FreeM.pure ∘ g) (FreeM.pure ∘ h)).symm

instance : LawfulMonad (P.FreeM) := LawfulMonad.mk'
  (bind_pure_comp := bind_pure_comp)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := FreeM.bind_assoc)

@[simp]
lemma pure_inj (a b : α) : (pure a : P.FreeM α) = pure b ↔ a = b := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl; rfl

lemma liftBind_inj (a a' : P.A)
    (cont : P.B a → P.FreeM α) (cont' : P.B a' → P.FreeM α) :
    FreeM.liftBind a cont = FreeM.liftBind a' cont' ↔ ∃ h : a = a', h ▸ cont = cont' := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

section liftM

variable {m : Type uB → Type v} {α : Type uB}

/-- Interpret a `FreeM P` computation into any monad `m` by providing an interpretation
`interp : (a : P.A) → m (P.B a)` for each operation. -/
protected def liftM [Pure m] [Bind m] (interp : (a : P.A) → m (P.B a)) : P.FreeM α → m α :=
  FreeM.rec (motive := fun _ => m α) (fun a => pure a) (fun a _ ih => interp a >>= ih)

variable [Monad m] (interp : (a : P.A) → m (P.B a))

@[simp]
lemma liftM_pure (a : α) : (Pure.pure a : P.FreeM α).liftM interp = Pure.pure a := rfl

@[simp]
lemma liftM_lift_bind (a : P.A) (cont : P.B a → P.FreeM α) :
    FreeM.liftM interp (FreeM.lift a >>= cont) =
      (do let u ← interp a; (cont u).liftM interp) := rfl

/--
A predicate stating that `eval : P.FreeM α → m α` is an interpreter for the polynomial
effect handler `handler : (a : P.A) → m (P.B a)`.

This means that `eval` is a monad morphism from the free monad `P.FreeM` to the
monad `m`, and that it extends the interpretation of individual operations given by
`handler`.
-/
structure Interprets (handler : (a : P.A) → m (P.B a)) (eval : P.FreeM α → m α) : Prop where
  apply_pure (a : α) : eval (.pure a) = pure a
  apply_lift_bind (a : P.A) (cont : P.B a → P.FreeM α) :
    eval ((FreeM.lift a).bind cont) = handler a >>= fun x => eval (cont x)

theorem Interprets.eq {handler : (a : P.A) → m (P.B a)} {eval : P.FreeM α → m α}
    (h : Interprets handler eval) :
    eval = (·.liftM handler) := by
  ext x
  induction x with
  | pure a => exact h.apply_pure a
  | lift_bind a cont ih =>
    rw [h.apply_lift_bind]
    conv_rhs => simp only [bind_eq_bind, liftM_lift_bind]
    simp only [ih]

theorem Interprets.liftM (handler : (a : P.A) → m (P.B a)) :
    Interprets handler (·.liftM handler : P.FreeM α → _) where
  apply_pure _ := rfl
  apply_lift_bind _ _ := rfl

/--
The universal property of the free monad `P.FreeM`.

That is, `liftM handler` is the unique interpreter that extends the effect handler `handler` to
interpret `P.FreeM` computations in a monad `m`.
-/
theorem Interprets.iff (handler : (a : P.A) → m (P.B a)) (eval : P.FreeM α → m α) :
    Interprets handler eval ↔ eval = (·.liftM handler) :=
  ⟨(·.eq), fun h => h ▸ Interprets.liftM _⟩

variable [LawfulMonad m]

@[simp]
lemma liftM_bind {α β : Type uB} (x : P.FreeM α) (f : α → P.FreeM β) :
    (x >>= f).liftM interp = (do let u ← x.liftM interp; (f u).liftM interp) := by
  induction x with
  | pure _ => simp only [liftM_pure, LawfulMonad.pure_bind]
  | lift_bind a cont h =>
    simp_rw [bind_eq_bind]
    rw [LawfulMonad.bind_assoc, liftM_lift_bind]
    simp_rw [liftM_lift_bind, LawfulMonad.bind_assoc]
    congr 1
    funext u
    exact h u

@[simp]
lemma liftM_map {α β : Type uB} (f : α → β) (x : P.FreeM α) :
    (f <$> x).liftM interp = f <$> x.liftM interp := by
  simp_rw [← LawfulMonad.bind_pure_comp, liftM_bind, liftM_pure]

@[simp]
lemma liftM_seq {α β : Type uB}
    (interp : (a : P.A) → m (P.B a)) (x : P.FreeM (α → β)) (y : P.FreeM α) :
    (x <*> y).liftM interp = x.liftM interp <*> y.liftM interp := by
  simp [seq_eq_bind_map]

@[simp]
lemma liftM_seqLeft {α β : Type uB}
    (interp : (a : P.A) → m (P.B a)) (x : P.FreeM α) (y : P.FreeM β) :
    (x <* y).liftM interp = x.liftM interp <* y.liftM interp := by
  simp [seqLeft_eq_bind]

@[simp]
lemma liftM_seqRight {α β : Type uB}
    (interp : (a : P.A) → m (P.B a)) (x : P.FreeM α) (y : P.FreeM β) :
    (x *> y).liftM interp = x.liftM interp *> y.liftM interp := by
  simp [seqRight_eq_bind]

@[simp]
lemma liftM_lift (interp : (a : P.A) → m (P.B a)) (a : P.A) :
    (FreeM.lift a).liftM interp = interp a := by
  simpa [bind_pure] using
    (liftM_lift_bind (interp := interp) (a := a) (cont := pure))

@[simp]
lemma liftM_liftObj (interp : (a : P.A) → m (P.B a)) (x : P.Obj α) :
    (FreeM.liftObj x).liftM interp = x.2 <$> interp x.1 := by
  simp [liftObj]

end liftM

end FreeM

end PFunctor
