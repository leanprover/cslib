/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTapeFlagged
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTapeRewound

namespace CslibTests

open Cslib Turing MultiTapeTM

/-- **The two adapters stack, and a computation feeds them directly.** A machine computing `f` and
leaving its tapes clean, fed its input from a work tape and writing what it would have emitted
onto another work tape, is a tape transformation — which is what a combinator needs in order to
use it as a component. No bridge appears: `h a` is already a specification. -/
example {k : ℕ} {Symbol State α β : Type*} {tm : MultiTapeTM k Symbol State}
    {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol} {f : α → β} {t s : α → ℕ}
    (mark : Symbol) (h : ComputesFunNormalizedInTimeAndSpace tm encIn encOut f t s) (a : α) :
    ∃ P Q, TransformsTapes ((tm.inputFromTapeFlagged mark).outputToTapeRewound) P Q
      (t a + 4 + (encOut (f a)).length + 2)
      (s a + 2 * (encIn a).length + 2 * k + 10 + 2 * (encOut (f a)).length + (k + 2) + 3) :=
  ⟨_, _, transformsTapes_outputToTapeRewound
    (transformsTapes_inputFromTapeFlagged (h a) mark
      (by rintro inp ws ⟨rfl, -⟩; exact le_refl _))
    (by rintro inp ws ws' e - ⟨i, w, w', -, -, -, rfl⟩; exact le_refl _)⟩

/-- A concrete machine enters the interface through `transformsTapes_of_runFrom`, which is the
only place the ambient output has to be dealt with. -/
example {k : ℕ} {Symbol State α β : Type*} {tm : MultiTapeTM k Symbol State}
    {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol} {f : α → β} {t s : α → ℕ}
    (hrun : ∀ a, tm.runFrom (wordsCfg (encIn a) (some tm.q₀) (fun _ => []) []) (t a) =
      wordsCfg (encIn a) none (fun _ => []) (encOut (f a)))
    (hspace : ∀ a, tm.spaceUsed (wordsCfg (encIn a) (some tm.q₀) (fun _ => []) []) (t a) ≤ s a) :
    ComputesFunNormalizedInTimeAndSpace tm encIn encOut f t s :=
  fun a => transformsTapes_of_runFrom (hrun a) (hspace a)

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
