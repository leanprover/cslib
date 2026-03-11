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
public def computes_function {k : ℕ}
  (tm : MultiTapeTM k Char) (f : TapeView → Data → TapeView)
  (i j : Fin k) (_h_neq : i ≠ j)
  (views : Fin k → TapeView) :=
  tm.eval_struct views = some (Function.update views j
    (((views i).current.map (f (views j))).getD (views j)))

-- TODO could generalize this to `f` having a preimage β.
public def computes_function_push {k : ℕ}
  {α : Type} [StrEnc α]
  (tm : MultiTapeTM k Char) (f : Data → α)
  (i j : Fin k) (_h_neq : i ≠ j) :=
  computes_function tm (fun tv d => tv.pushList (StrEnc.toData (f d))) i j _h_neq

/-- Turing machine `tm` computes a function of the current item at tape `i` seen as type
-- `α` and pushes the result (type `β`) to tape `j`. -/
-- public def computes_function_push' {k : ℕ}
--   {α β : Type} [StrEnc α] [StrEnc β]
--   (tm : MultiTapeTM k Char) (f : α → β)
--   (i j : Fin k) (_h_neq : i ≠ j) :=
--   computes_function tm (fun tv d => tv.pushList (StrEnc.toData (f d))) i j _h_neq

public def computes_function_push_bool {k : ℕ}
  (tm : MultiTapeTM k Char) (f : Data → Bool)
  (i j : Fin k) (h_neq : i ≠ j) :=
  computes_function_push (α := Bool) tm f i j h_neq

/-- Turing machine `tm` updates the head of tape `i`. -/
public def computes_function_update {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char) (f : α → β)
  (i : Fin k)
  (views : Fin k → TapeView) :=
  tm.eval_struct views = some (Function.update views i ((views i).updateListHeadTyped f))


end Routines
end Turing
