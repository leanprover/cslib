/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines
public import Cslib.Computability.Machines.MultiTapeTuring.TapeView

namespace Turing
namespace Routines

/-- Repeatedly run a sub routine as long as the current item on tape `i` is equal to a given
encoding.
-/
public def doWhileEq {k : ℕ} (d : Data) (i : Fin k) (tm : MultiTapeTM k Char) :
    MultiTapeTM k Char := sorry

-- TODO
-- public theorem doWhileEq.eval_struct {k : ℕ} {d : Data} {i : Fin k} {tm : MultiTapeTM k Char}
--   {h_halts : ∀ views, tm.HaltsOn (TapeView.toBiTape ∘ views)}
--   {views : Fin k → TapeView}
--   (n : ℕ)
--   (h_exists : ((tm.eval_struct · sorry)^[n] views i).current = d)
--   (h_min : ∀ n' < n, ((tm.eval_struct sorry)^[n'] views i).current ≠ d) :
--     (doWhileEq d i tm).eval_struct views = .some ((tm.eval_struct sorry)^[n] views) := by
--   sorry


end Routines
end Turing
