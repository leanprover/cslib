/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Edward Ayers, Shreyas Srinivas
-/
module

public import Mathlib
public import Cslib.Init

/-!
# Additive Writer monads

This file is a port of Mathlib's WriterT monad which incorrectly uses multiplicative logs.
-/

@[expose] public section

namespace Cslib

universe u v

/-- Adds a writable output of type `ω` to a monad.

The instances on this type assume `[AddMonoid ω]`.

Use `AddWriterT.run` to obtain the final value of this output. -/
def AddWriterT (ω : Type u) (M : Type u → Type v) (α : Type u) : Type v :=
  M (α × ω)

/-- `AddWriter` is simply `AddWriterT` applied to the `Id` monad -/
abbrev AddWriter ω := AddWriterT ω Id

/-- Standard MonadWriter API for AddWriter -/
class MonadAddWriter (ω : outParam (Type u)) (M : Type u → Type v) where
  /-- Emit an output `w`. -/
  tell (w : ω) : M PUnit
  /-- Capture the output produced by `f`, without intercepting. -/
  listen {α} (f : M α) : M (α × ω)
  /-- Buffer the output produced by `f` as `w`, then emit `(← f).2 w` in its place. -/
  pass {α} (f : M (α × (ω → ω))) : M α

export MonadWriter (tell listen pass)

variable {M : Type u → Type v} {α ω ρ σ : Type u}

instance [MonadWriter ω M] : MonadWriter ω (ReaderT ρ M) where
  tell w := (tell w : M _)
  listen x r := listen <| x r
  pass x r := pass <| x r

instance [Monad M] [MonadWriter ω M] : MonadWriter ω (StateT σ M) where
  tell w := (tell w : M _)
  listen x s := (fun ((a, w), s) ↦ ((a, s), w)) <$> listen (x s)
  pass x s := pass <| (fun ((a, f), s) ↦ ((a, s), f)) <$> (x s)

namespace AddWriterT

/-- Standard conversion from `M (α × ω)` to `AddWriterT ω M α` -/
@[inline]
protected def mk {ω : Type u} (cmd : M (α × ω)) : AddWriterT ω M α := cmd

/-- Run a writer monad `AddWriterT ω M α` -/
@[inline]
protected def run {ω : Type u} (cmd : AddWriterT ω M α) : M (α × ω) := cmd

/-- Run a writer monad `AddWriterT ω M α` -/
@[inline]
protected def runThe (ω : Type u) (cmd : AddWriterT ω M α) : M (α × ω) := cmd

/-- Extensional equality of AddWriterT Monad -/
@[ext]
protected theorem ext {ω : Type u} (x x' : AddWriterT ω M α) (h : x.run = x'.run) : x = x' := h

variable [Monad M]

/-- Creates an instance of `Monad`, with explicitly given `empty` and `append` operations.

Previously, this would have used an instance of `[AddMonoid ω]` as input.
In practice, however, `AddWriterT` is used for logging and creating lists so restricting to
monoids with `Mul` and `One` can make `AddWriterT` cumbersome to use.

This is used to derive instances for both `[AddMonoid ω]`.
-/
@[reducible, inline]
def monad (empty : ω) (append : ω → ω → ω) : Monad (AddWriterT ω M) where
  map := fun f (cmd : M _) ↦ AddWriterT.mk <| (fun (a, w) ↦ (f a, w)) <$> cmd
  pure := fun a ↦ pure (f := M) (a, empty)
  bind := fun (cmd : M _) f ↦
    AddWriterT.mk <| cmd >>= fun (a, w₁) ↦
      (fun (b, w₂) ↦ (b, append w₁ w₂)) <$> (f a)

/-- Lift an `M` to a `AddWriterT ω M`, using the given `empty` as the add monoid unit. -/
@[inline]
protected def liftTell (empty : ω) : MonadLift M (AddWriterT ω M) where
  monadLift := fun cmd ↦ AddWriterT.mk <| (fun a ↦ (a, empty)) <$> cmd

instance [EmptyCollection ω] [Append ω] : Monad (AddWriterT ω M) := monad ∅ (· ++ ·)
instance [EmptyCollection ω] : MonadLift M (AddWriterT ω M) := AddWriterT.liftTell ∅
instance [AddMonoid ω] : Monad (AddWriterT ω M) := monad 0 (· + ·)
instance [AddMonoid ω] : MonadLift M (AddWriterT ω M) := AddWriterT.liftTell 0

instance [AddMonoid ω] [LawfulMonad M] : LawfulMonad (AddWriterT ω M) := LawfulMonad.mk'
  (bind_pure_comp := by
    simp [Bind.bind, Functor.map, Pure.pure, AddWriterT.mk, bind_pure_comp])
  (id_map := by simp [Functor.map, AddWriterT.mk])
  (pure_bind := by simp [Bind.bind, Pure.pure, AddWriterT.mk])
  (bind_assoc := by simp [Bind.bind, add_assoc, AddWriterT.mk, ← bind_pure_comp])

instance : MonadWriter ω (AddWriterT ω M) where
  tell := fun w ↦ AddWriterT.mk <| pure (⟨⟩, w)
  listen := fun cmd ↦ AddWriterT.mk <| (fun (a, w) ↦ ((a, w), w)) <$> cmd
  pass := fun cmd ↦ AddWriterT.mk <| (fun ((a, f), w) ↦ (a, f w)) <$> cmd

instance {ε : Type*} [MonadExcept ε M] : MonadExcept ε (AddWriterT ω M) where
  throw := fun e ↦ AddWriterT.mk <| throw e
  tryCatch := fun cmd c ↦ AddWriterT.mk <| tryCatch cmd fun e ↦ (c e).run

instance [MonadLiftT M (AddWriterT ω M)] : MonadControl M (AddWriterT ω M) where
  stM := fun α ↦ α × ω
  liftWith f := liftM <| f fun x ↦ x.run
  restoreM := AddWriterT.mk

instance : MonadFunctor M (AddWriterT ω M) where
  monadMap := fun k (w : M _) ↦ AddWriterT.mk <| k w

/--
Adapt functorially maps `f` to the writer log of an `AddWriterT` to produce another
with the modified log.
-/
@[inline] protected def adapt {ω' : Type u} {α : Type u} (f : ω → ω') :
    AddWriterT ω M α → AddWriterT ω' M α :=
  fun cmd ↦ AddWriterT.mk <| Prod.map id f <$> cmd

end AddWriterT

/-- Adapt a monad stack, changing the type of its top-most environment.

This class is comparable to [Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify),
but does not use lenses (why would it), and is derived automatically for any transformer
implementing `MonadFunctor`.
-/
class MonadAddWriterAdapter (ω : outParam (Type u)) (m : Type u → Type v) where
  /-- The addaptWriter function -/
  adaptAddWriter {α : Type u} : (ω → ω) → m α → m α

export MonadWriterAdapter (adaptWriter)

variable {m : Type u → Type*}
/-- Transitivity.

see Note [lower instance priority] -/
instance (priority := 100) monadWriterAdapterTrans {n : Type u → Type v}
    [MonadWriterAdapter ω m] [MonadFunctor m n] : MonadWriterAdapter ω n where
  adaptWriter f := monadMap (fun {α} ↦ (adaptWriter f : m α → m α))

instance [Monad m] : MonadWriterAdapter ω (AddWriterT ω m) where
  adaptWriter := AddWriterT.adapt

universe u₀ u₁ v₀ v₁ in
/-- reduce the equivalence between two writer monads to the equivalence between
their underlying monad -/
def AddWriterT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
    {α₁ ω₁ : Type u₀} {α₂ ω₂ : Type u₁} (F : (m₁ (α₁ × ω₁)) ≃ (m₂ (α₂ × ω₂))) :
    AddWriterT ω₁ m₁ α₁ ≃ AddWriterT ω₂ m₂ α₂ where
  toFun (f : m₁ _) := AddWriterT.mk <| F f
  invFun (f : m₂ _) := AddWriterT.mk <| F.symm f
  left_inv (f : m₁ _) := congr_arg AddWriterT.mk <| F.left_inv f
  right_inv (f : m₂ _) := congr_arg AddWriterT.mk <| F.right_inv f

end Cslib
