/-
Copyright (c) 2026 William (Liam) Schilling. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William (Liam) Schilling
-/

module

public import Cslib.Computability.Automata.DT.ToBimachine
public import Cslib.Computability.Transductions.Transduction

@[expose] public section

/-! # Rational Transductions

A transduction `IsRational` if it is recognized by a deterministic printer
with finite-state look-left and look-right (a `Bimachine`).
Equivalently, a rational transduction is recognized by
a nondeterministic finite-state left-to-right reader-printer.
A transduction `IsSubsequential` if it is recognized by
a deterministic finite-state left-to-right reader-printer (a `DetTransducer`).
All subsequential transductions are rational transductions.
-/

namespace Cslib.Transduction

open Automata.DT
open Automata.Transducer

variable {Symbol Weight : Type*} [Monoid Weight]

/-- A sequential transduction is recognized by a deterministic transducer without final weights. -/
def IsSequential (f : Transduction Symbol Weight) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ dt : DetTransducer σ Symbol Weight, dt.IsFinalEmpty ∧
    transduceLeft dt = f

/-- A subsequential transduction is recognized by a deterministic transducer. -/
def IsSubsequential (f : Transduction Symbol Weight) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ dt : DetTransducer σ Symbol Weight,
    transduceLeft dt = f

/-- A rational transduction is recognized by a bimachine. -/
def IsRational (f : Transduction Symbol Weight) : Prop :=
  ∃ σl σr : Type, ∃ _ : Fintype σl, ∃ _ : Fintype σr, ∃ bm : Bimachine σl σr Symbol Weight,
    transduceLeft bm = f

namespace IsSubsequential

/-- All sequential transductions are subsequential. -/
theorem of_sequential (f : Transduction Symbol Weight) : IsSequential f → IsSubsequential f := by
  intro ⟨σ, h_fin, dt, _, h⟩
  exact ⟨σ, h_fin, dt, h⟩

end IsSubsequential

namespace IsRational

/-- All subsequential transductions are rational. -/
theorem of_subsequential (f : Transduction Symbol Weight) : IsSubsequential f → IsRational f := by
  intro ⟨σ, h_fin, dt, h⟩
  refine ⟨σ, Unit, h_fin, Unit.fintype, dt.toBimachine, ?_⟩
  ext
  simp [←h]

end IsRational

end Cslib.Transduction
