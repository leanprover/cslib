/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes

namespace CslibTests.MultiTapePlumbing

open Turing.MultiTapeTM

private def finish (move : SignType) (symbol : Bool) : Turing.MultiTapeTM 0 Bool Unit where
  q₀ := ()
  tr _ _ _ := ⟨move, Fin.elim0, some symbol, none⟩

-- Sequential execution retains the output accumulated by the first machine.
example : (((finish 0 true).seq (finish 0 false)).runFrom
    (((finish 0 true).seq (finish 0 false)).initCfg []) 2).output = [true, false] := by rfl

private def sparse : Fin 1 ↪ Fin 3 := ⟨fun _ => 2, fun _ _ _ => Subsingleton.elim _ _⟩

private def writer : Turing.MultiTapeTM 1 Bool Unit where
  q₀ := ()
  tr _ _ _ := ⟨0, fun _ => (some (some true), 1), none, none⟩

-- The injection is not an initial-segment inclusion; unused tape data and heads are retained.
example : ((writer.extendTapes sparse).runFrom
    (ExtendTapes.embed sparse (writer.initCfg [])
      (fun _ _ => some false) (fun _ => 7)) 1).workTapes 0 0 = some false := by rfl

example : ((writer.extendTapes sparse).runFrom
    (ExtendTapes.embed sparse (writer.initCfg [])
      (fun _ _ => some false) (fun _ => 7)) 1).workTapePos 0 = 7 := by rfl

example : ((writer.extendTapes sparse).runFrom
    (ExtendTapes.embed sparse (writer.initCfg [])
      (fun _ _ => some false) (fun _ => 7)) 1).workTapes 2 0 = some true := by rfl

-- Exact halting time includes an already halted starting configuration.
example (cfg : Cfg 0 Bool Unit []) (h : cfg.state = none) :
    (finish 0 true).HaltsAt cfg 0 :=
  ⟨h, fun _ hs => (Nat.not_lt_zero _ hs).elim⟩

-- An initialized machine must take a step before halting; later padded times are not first halts.
example : ¬ (finish 0 true).haltsAtStep [] 0 := by
  intro h
  simpa [runFrom, initCfg] using h.halted

example : (finish 0 true).haltsAtStep [] 1 := by
  refine ⟨rfl, ?_⟩
  intro s hs
  have : s = 0 := by omega
  subst s
  simp [runFrom, initCfg]

example : ¬ (finish 0 true).haltsAtStep [] 2 := by
  intro h
  exact h.active 1 (by decide) rfl

-- A zero-time first phase hands off without charging an additional step.
example (cfg : Cfg 0 Bool Unit []) (h : cfg.state = none) :
    ((finish 0 true).seq (finish 0 false)).runFrom
        (Sequential.left (finish 0 false) cfg) 1 =
      Sequential.right ((finish 0 false).step (cfg.withState (some ()))) :=
  runFrom_seq _ _ cfg 0 1 ⟨h, fun _ hs => (Nat.not_lt_zero _ hs).elim⟩

end CslibTests.MultiTapePlumbing
