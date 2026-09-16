/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

namespace CslibTests.MultiTapeComplexity

open Turing.MultiTapeTM

private def finish (move : SignType) (symbol : Bool) : Turing.MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨move, Fin.elim0, some symbol, none⟩

private def bit : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; simpa using h⟩

-- Bounds can differ for inputs of the same encoded length.
private lemma constant_computable :
    ComputableInTimeAndSpace (fun _ : Bool => true) bit bit
      (fun b => if b then 1 else 2) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, (finish 0 true).toMultiTapeNTM, (finish 0 true).deterministic,
    fun b => ⟨1, ?_, 0, le_rfl, ?_⟩⟩
  · cases b <;> decide
  · let p : (finish 0 true).ComputationPath (bit b) :=
      { cfgs := [(finish 0 true).initCfg (bit b),
          (finish 0 true).step ((finish 0 true).initCfg (bit b))]
        last := (finish 0 true).step ((finish 0 true).initCfg (bit b))
        isChainFromTo := by simp }
    refine ⟨p, ?_, ?_, rfl, p.space_zero_tapes rfl⟩ <;>
      dsimp only [p] <;>
      simp [step_of_state, finish, bit, Turing.Cfg.Halted]
    rfl

end CslibTests.MultiTapeComplexity
