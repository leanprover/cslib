/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines

namespace Turing
namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- Put characters and Data values
-- ═══════════════════════════════════════════════════════════════════════════

/-- Write a list of characters to tape `i` by repeatedly moving left and writing,
    effectively prepending the characters to the tape content. -/
public def putChars : List Char → Fin k → MultiTapeTM k Char
  | [], _ => noop
  | c :: rest, i => putChars rest i ;ₜ left i ;ₜ write c i

/-- Prepend the encoding of a `Data` value to tape `i`. -/
public def put {k : ℕ} (d : Data) (i : Fin k) : MultiTapeTM k Char :=
  putChars (Data.enc d) i

/-- Prepend the encoding of a value of type `α` (via its `StrEnc` instance) to tape `i`. -/
public def putEnc {k : ℕ} {α : Type*} [StrEnc α] (x : α) (i : Fin k) :
    MultiTapeTM k Char :=
  put (StrEnc.toData x) i

/-- `put d i` writes a `Data` value to tape `i` if the tape is empty.
    If the tape already has data, `put` is a no-op.
    Resets the path to `[]`. -/
@[simp]
public lemma put_eval_struct_empty {k : ℕ} {d : Data} {i : Fin k}
    {views : Fin k → TapeView}
    (h_empty : (views i).data = Data.list []) :
    (put d i).eval_struct views = some
      (Function.update views i ⟨d, []⟩) := by sorry

@[simp]
public lemma put_eval_struct_nonempty {k : ℕ} {d : Data} {i : Fin k}
    {views : Fin k → TapeView}
    (h_nonempty : (views i).data ≠ Data.list []) :
    (put d i).eval_struct views = some views := by sorry

end Routines
end Turing
