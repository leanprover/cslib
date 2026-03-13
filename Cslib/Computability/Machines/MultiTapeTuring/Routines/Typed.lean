/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Encoding
public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines

namespace Turing
namespace Routines

/-- Turing machine `tm` computes a function on data from tape `i` and updates tape `j`. -/
-- TODO move this somewhere else
public def computes_function_read_update {k : ℕ}
  (tm : MultiTapeTM k Char) (f : Data → TapeView → TapeView)
  (i j : Fin k) (_h_neq : i ≠ j) :=
  ∀ views, tm.eval_struct views = some (Function.update views j
    (((views i).current.map (f · (views j))).getD (views j)))

-- TODO could generalize this to `f` having a preimage β.
/-- Turing machine `tm` computes a function on data from tape `i` and pushes data to the
list on tape `j`. -/
public def computes_function_read_push {k : ℕ}
  {α : Type} [StrEnc α]
  (tm : MultiTapeTM k Char)
  (f : Data → α)
  (i j : Fin k) (h_neq : i ≠ j) :=
  computes_function_read_update tm (fun d tv => tv.pushList (StrEnc.toData (f d))) i j h_neq

-- TODO maybe we don't need this any more if we generalize the input type, so if the
-- input does not decode to a list, we do nothing.
/-- Turing machine `tm` computes a function on a list from tape `i` and pushes data to the
lsit on tape `j`. -/
public def computes_function_readList_push {k : ℕ}
  {α : Type} [StrEnc α]
  (tm : MultiTapeTM k Char)
  (f : List Data → α)
  (i j : Fin k) (h_neq : i ≠ j) :=
  computes_function_read_update tm (fun d tv => match d with
   | Data.list ls => tv.pushList (StrEnc.toData (f ls))
   | Data.num _ => tv) i j h_neq


/-- Turing machine `tm` updates the head of tape `i`. -/
public def computes_function_head_update {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char) (f : α → β)
  (i : Fin k) :=
  ∀ views, tm.eval_struct views =
    some (Function.update views i ((views i).updateListHeadTyped f))

@[simp]
public theorem computes_function_seq₁ {k : ℕ}
  {β γ : Type} [StrEnc β] [StrEnc γ]
  (tm₁ tm₂ : MultiTapeTM k Char) (f₁ : Data → β) (f₂ : β → γ)
  (i j : Fin k) (h_neq : i ≠ j)
  (h_comp₁ : computes_function_read_push tm₁ f₁ i j h_neq)
  (h_comp₂ : computes_function_head_update tm₂ f₂ i) :
  computes_function_read_push (tm₁ ;ₜ tm₂) (f₂ ∘ f₁) i j h_neq := by sorry

@[simp]
public theorem computes_function_seq₂ {k : ℕ}
  {β γ : Type} [StrEnc β] [StrEnc γ]
  {tm₁ tm₂ : MultiTapeTM k Char} {f₁ : List Data → β} {f₂ : β → γ}
  {i j : Fin k} (h_neq : i ≠ j)
  (h_comp₁ : computes_function_readList_push tm₁ f₁ i j h_neq)
  (h_comp₂ : computes_function_head_update tm₂ f₂ i) :
  computes_function_readList_push (tm₁ ;ₜ tm₂) (f₂ ∘ f₁) i j h_neq := by sorry

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
