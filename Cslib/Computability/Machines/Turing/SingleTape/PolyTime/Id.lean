/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Pim Spelier, Daan van Gent
-/

module

public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-!
# The identity machine

The Turing machine `idComputer` computing the identity function, together with the witnesses that
the identity is `TimeComputable` (in constant time) and `PolyTimeComputable`.
-/

@[expose] public section

open Relation

namespace Cslib.Turing

open BiTape StackTape
open _root_.Turing

namespace SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A Turing machine computing the identity. -/
def idComputer : SingleTapeTM Symbol where
  State := PUnit
  q₀ := PUnit.unit
  tr _ b := ⟨⟨b, none⟩, none⟩

/-- The identity map on Symbol is computable in constant time. -/
def TimeComputable.id : TimeComputable (Symbol := Symbol) id where
  tm := idComputer
  timeBound _ := 1
  outputsFunInTime _ := ⟨1, le_rfl, RelatesInSteps.single rfl⟩

/-- A proof that the identity map on Symbol is computable in polytime. -/
noncomputable def PolyTimeComputable.id : PolyTimeComputable (Symbol := Symbol) id where
  toTimeComputable := TimeComputable.id
  poly := 1
  bounds _ := by simp [TimeComputable.id]

end SingleTapeTM

end Cslib.Turing
