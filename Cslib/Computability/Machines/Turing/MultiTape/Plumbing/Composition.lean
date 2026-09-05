/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Composition.Rewind

/-!
# Correctness of multi-tape composition

`comp_haltsWithOutput` proves that the composite machine returns the second machine's output
on the first machine's result. The first phase takes one step per native step; the second takes
two, following a rewind of the intermediate output and one initial classification step.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Composition

variable {k₀ k₁ : ℕ}
variable {Symbol State₀ State₁ : Type*}

variable (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁)

/-- Composition returns the second machine's output on the first machine's result.
The first halting time must be minimal; the second may be padded. -/
theorem comp_haltsWithOutput
    {input out₀ out₁ : List Symbol} {u v : ℕ}
    (hhalt₀ : (tm₀.runFrom (tm₀.initCfg input) u).state = none)
    (hactive₀ : ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none)
    (hout₀ : (tm₀.runFrom (tm₀.initCfg input) u).output = out₀)
    (hhalt₁ : (tm₁.runFrom (tm₁.initCfg out₀) v).state = none)
    (hout₁ : (tm₁.runFrom (tm₁.initCfg out₀) v).output = out₁) :
    ((comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input)
        (u + (out₀.length + 3) + 2 * v)).state = none ∧
      ((comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input)
          (u + (out₀.length + 3) + 2 * v)).output = out₁ := by
  subst out₀
  subst out₁
  have hfinal := runFrom_secondPhase tm₀ tm₁
    (tm₀.runFrom (tm₀.initCfg input) u)
    (tm₁.initCfg (tm₀.runFrom (tm₀.initCfg input) u).output) v
  rw [← runFrom_to_secondInit tm₀ tm₁ input u hhalt₀ hactive₀, ← runFrom_add] at hfinal
  rw [hfinal]
  simp only [embedSecond, hhalt₁, and_self]

end Turing.MultiTapeTM
