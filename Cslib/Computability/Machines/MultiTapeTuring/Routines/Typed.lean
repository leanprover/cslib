/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.TapeView
public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines

namespace Turing
namespace Routines

/-- Turing machine `tm` computes a function on data from tape `i` and updates tape `j`. -/
-- TODO move this somewhere else
@[expose]
public def computes_function_read_update' {k : ℕ}
  (tm : MultiTapeTM k Char) (f : Data → TapeView → TapeView)
  (i j : Fin k) (_h_neq : i ≠ j) :=
  ∀ views, tm.eval_struct views = some (Function.update views j (f (views i).current (views j)))

@[expose]
public def computes_function_read_update {k : ℕ}
  {α : Type} [StrEnc α]
  (tm : MultiTapeTM k Char) (f : α → TapeView → TapeView)
  (i j : Fin k) (_h_neq : i ≠ j) :=
  ∀ (x : α) (views : Fin k → TapeView),
    ((views i).current = StrEnc.toData x) →
    tm.eval_struct views = some (Function.update views j (f x (views j)))

@[expose]
public def computes_function_read_read_update {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char) (f : α → β → TapeView → TapeView)
  (i j r : Fin k) (_h_neq : [i, j, r].get.Injective) :=
  ∀ (x : α) (y: β) (views : Fin k → TapeView),
    ((views i).current = StrEnc.toData x) →
    ((views j).current = StrEnc.toData y) →
    tm.eval_struct views = some (Function.update views r (f x y (views r)))

/-- Turing machine `tm` computes a function on data from tape `i` and pushes data to the
list on tape `j`. -/
@[expose]
public def computes_function_read_push {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char)
  (f : α → β)
  (i j : Fin k) (h_neq : i ≠ j) :=
  computes_function_read_update tm (fun d tv => tv.pushList (StrEnc.toData (f d))) i j h_neq

@[expose]
public def computes_function_read_read_push {k : ℕ}
  {α β γ : Type} [StrEnc α] [StrEnc β] [StrEnc γ]
  (tm : MultiTapeTM k Char)
  (f : α → β → γ)
  (i j s : Fin k) (h_neq : [i, j, s].get.Injective) :=
  computes_function_read_read_update tm
    (fun x y tv => tv.pushList (StrEnc.toData (f x y))) i j s h_neq

/-- Turing machine `tm` updates the head of tape `i`. -/
public def computes_function_head_update {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char) (f : α → β)
  (i : Fin k) :=
  ∀ views, tm.eval_struct views =
    some (Function.update views i ((views i).updateListHeadTyped f))

@[simp, grind =>]
public theorem computes_function_seq₁ {k : ℕ}
  {α β γ : Type} [StrEnc α] [StrEnc β] [StrEnc γ]
  {tm₁ tm₂ : MultiTapeTM k Char} {f₁ : α → β} {f₂ : β → γ}
  {i j : Fin k} (h_neq : i ≠ j)
  (h_comp₁ : computes_function_read_push tm₁ f₁ i j h_neq)
  (h_comp₂ : computes_function_head_update tm₂ f₂ j) :
  computes_function_read_push (tm₁ ;ₜ tm₂) (fun x => f₂ (f₁ x)) i j h_neq := by sorry

@[simp, grind =>]
public theorem computes_function_seq₂ {k : ℕ}
  {α β γ δ : Type} [StrEnc α] [StrEnc β] [StrEnc γ] [StrEnc δ]
  {tm₁ tm₂ : MultiTapeTM k Char} {f₁ : α → β → γ} {f₂ : γ → δ}
  {i j r : Fin k} (h_neq : [i, j, r].get.Injective)
  (h_comp₁ : computes_function_read_read_push tm₁ f₁ i j r h_neq)
  (h_comp₂ : computes_function_head_update tm₂ f₂ r) :
  computes_function_read_read_push (tm₁ ;ₜ tm₂) (fun x y => f₂ (f₁ x y)) i j r h_neq := by sorry

@[grind =>]
public theorem computes_function_read_read_push_swap {k : ℕ}
  {α β γ : Type} [StrEnc α] [StrEnc β] [StrEnc γ]
  {tm : MultiTapeTM k Char} {f : α → β → γ}
  {i j r : Fin k} {h_neq : [i, j, r].get.Injective}
  (h : computes_function_read_read_push tm f i j r h_neq) :
  computes_function_read_read_push tm (fun x y => f y x) j i r
    (by sorry) := by sorry

inductive TapeEffects where
  | read
  | consume
  | put
  | modify

-- and all indices different
def FunArgs (k : ℕ) := List ((Fin k) × TapeEffects)

def ReturnType {k : ℕ} (args : FunArgs k) : Type := match args with
 | [] => Unit
 | (_, .read) :: rest => ReturnType rest
 | (_, .consume) :: rest => ReturnType rest
 | (_, .put) :: rest => Data × ReturnType rest
 | (_, .modify) :: rest => Data × ReturnType rest

def InputTypes {k : ℕ} (args : FunArgs k) : Type := match args with
 | [] => Unit
 | (_, .read) :: rest => Data → (InputTypes rest)
 | (_, .consume) :: rest => Data → (InputTypes rest)
 | (_, .put) :: rest => InputTypes rest
 | (_, .modify) :: rest => Data → (InputTypes rest)

def TypeOfFunArgs {k : ℕ} (args : FunArgs k) : Type := (InputTypes args) → (ReturnType args)

-- def EvaluateFun {k : ℕ} (args : FunArgs k) (views : Fin k → TapeView)
--   (f : TypeOfFunArgs args) : Option (ReturnType args) := match args with
--   | [] => some ()
--   | (i, .read) :: rest => (views i).current.bind (fun d => EvaluateFun rest views (f d))
--   | (_, .consume) :: rest => Data → (InputTypes rest)
--   | (_, .put) :: rest => InputTypes rest
--   | (_, .modify) :: rest => Data → (InputTypes rest)

--   --(i, TapeEffects.read) :: rest =>
--     let current := (views i).current
--     current.bind (fun d => EvaluateFun rest views (f d))

-- public def computes_function_general {k : ℕ}
--   (tm : MultiTapeTM k Char) (f : TapeView → Data → TapeView)
--   (i j : Fin k) (_h_neq : i ≠ j)
--   (views : Fin k → TapeView) :=
--   tm.eval_struct views = some (Function.update views j
--     (((views i).current.map (f (views j))).getD (views j)))



end Routines
end Turing
