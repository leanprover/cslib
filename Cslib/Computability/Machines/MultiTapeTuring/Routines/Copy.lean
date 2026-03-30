/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Put
public import Cslib.Computability.Machines.MultiTapeTuring.Routines.Typed

namespace Turing
namespace Routines

/-- Copy a Data-encoded value from tape `i` to tape `j`
    (prepending the encoding to tape `j`). -/
public def copyEnc {k : ℕ} (i j : Fin k) (h_eq : i ≠ j) : MultiTapeTM k Char := sorry

/-- `copyEnc i j` copies the `Data` element at the current path position
    of tape `i` and writes it to tape `j` (overwrites everything).
    Tape `i` is not modified. -/
@[simp]
public lemma copyEnc_eval_struct {k : ℕ} {i j : Fin k}
    {views : Fin k → TapeView}
    {h_ne : i ≠ j} :
    (copyEnc i j h_ne).eval_struct views = some (Function.update views j
      (.ofData (views i).current)) := by sorry

end Routines
end Turing
