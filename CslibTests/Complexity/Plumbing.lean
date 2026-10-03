/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTapeFlagged
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTapeRewound

namespace CslibTests

open Cslib Turing MultiTapeTM

/-- **The two adapters stack.** A normalized computation, fed its input from a work tape and
writing what it would have emitted onto another work tape, is a tape transformation — which is
what a combinator needs in order to use it as a component. -/
example {k : ℕ} {Symbol State : Type*} {input output : List Symbol} {t s : ℕ}
    {tm : MultiTapeTM k Symbol State} (mark : Symbol)
    (h : tm.ComputesNormalizedInTimeAndSpace input output t s) :
    ∃ P Q, TransformsTapes ((tm.inputFromTapeFlagged mark).outputToTapeRewound) P Q
      (t + 4 + output.length + 2)
      (s + 2 * input.length + 2 * k + 10 + 2 * output.length + (k + 2) + 3) :=
  ⟨_, _, transformsTapes_outputToTapeRewound
    (transformsTapes_inputFromTapeFlagged h.transformsTapes mark
      (by rintro inp ws ⟨rfl, -⟩; exact le_refl _))
    (by rintro inp ws ws' e - ⟨i, w, w', -, -, -, rfl⟩; exact le_refl _)⟩

/-- A tape transformation can be sequenced with itself, the emitted words concatenating. -/
example {k : ℕ} {Symbol State : Type*} {t s : ℕ} {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop}
    (h : TransformsTapes tm P Q t s) (hmid : ∀ input ws ws' e, P input ws → Q input ws ws' e →
      P input ws') :
    ∃ Q', TransformsTapes (tm.seq tm) P Q' (t + t) (s + s) :=
  ⟨_, transformsTapes_seq h h hmid⟩

end CslibTests
