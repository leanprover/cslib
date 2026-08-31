import Cslib.Computability.URM.Defs
import Cslib.Foundations.Data.Lens.Basic

namespace CslibTests.Lens

open Cslib
open Cslib.URM

/-- A lawful lens for the program counter of CSLib's existing URM state. -/
def pcLens : LawfulLens State Nat where
  get := State.pc
  set := fun s pc => { s with pc := pc }
  get_set := by
    intro s pc
    rfl
  set_get := by
    intro s
    cases s
    rfl
  set_set := by
    intro s pc₁ pc₂
    cases s
    rfl

/-- Increment the program counter through the lens API. -/
def bumpPC (s : State) : State :=
  Cslib.Lens.over pcLens (· + 1) s

@[simp]
theorem bumpPC_pc (s : State) : (bumpPC s).pc = s.pc + 1 := by
  cases s
  rfl

@[simp]
theorem bumpPC_regs (s : State) : (bumpPC s).regs = s.regs := by
  cases s
  rfl

end CslibTests.Lens
