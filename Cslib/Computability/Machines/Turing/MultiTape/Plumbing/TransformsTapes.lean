/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Machines as transformers of tape words

A tape transformation has a run path between configurations holding words, with the heads reset
and the output unchanged. The same path witnesses the postcondition and both resource bounds.
The time bound allows earlier halting.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- A machine has a path from tapes satisfying `P` to tapes satisfying `Q`, within `t` steps and
`s` cells. Both endpoints have their heads reset and the same output. -/
def TransformsTapes (tm : MultiTapeNTM k Symbol State)
    (P : (input : List Symbol) → (Fin k → List Symbol) → Prop)
    (Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop)
    (t s : ℕ) : Prop :=
  ∀ (input : List Symbol) (ws : Fin k → List Symbol) (out : List Symbol), P input ws →
    ∃ ws', ∃ p : tm.RunPath input,
      p.head = wordsCfg input (some tm.q₀) ws out ∧
      p.last = wordsCfg input none ws' out ∧ Q input ws ws' ∧ p.length ≤ t ∧ p.space ≤ s

/-- Strengthen the precondition, weaken the postcondition, and enlarge the resource bounds. -/
theorem TransformsTapes.imp {tm : MultiTapeNTM k Symbol State}
    {P P' : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q Q' : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop}
    {t s t' s' : ℕ} (h : TransformsTapes tm P Q t s)
    (hP : ∀ input ws, P' input ws → P input ws)
    (hQ : ∀ input ws ws', P' input ws → Q input ws ws' → Q' input ws ws')
    (ht : t ≤ t') (hs : s ≤ s') : TransformsTapes tm P' Q' t' s' := by
  intro input ws out hP'
  obtain ⟨ws', p, hp, hlast, hQ', htime, hspace⟩ := h input ws out (hP input ws hP')
  exact ⟨ws', p, hp, hlast, hQ input ws ws' hP' hQ', htime.trans ht, hspace.trans hs⟩

/-- The machine that halts on its first step without changing its tapes or output. -/
def nop (k : ℕ) (Symbol : Type*) : MultiTapeNTM k Symbol Unit where
  q₀ := ()
  Tr _ _ _ a :=
    a = { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none }

/-- The machine that does nothing is deterministic. -/
lemma nop_isDeterministic : (nop k Symbol).IsDeterministic := by
  intro _ _ _
  simp [nop]

/-- A single step of `nop` halts and leaves the words alone. -/
lemma step_nop (ws : Fin k → List Symbol) (out : List Symbol) :
    (nop k Symbol).Step (wordsCfg input (some ()) ws out) (wordsCfg input none ws out) := by
  apply (step_of_state rfl).mpr
  refine ⟨_, rfl, ?_⟩
  simp [Action.apply, wordsCfg, SignType.cast]

/-- The machine that does nothing leaves every word as it was in one step and one cell per tape. -/
theorem transformsTapes_nop (k : ℕ) (Symbol : Type*) :
    TransformsTapes (nop k Symbol) (fun _ _ ↦ True) (fun _ ws ws' ↦ ws' = ws) 1 k := by
  intro input ws out _
  let p : (nop k Symbol).RunPath input :=
    (RelSeries.singleton _ (wordsCfg input (some ()) ws out)).snoc
      (wordsCfg input none ws out) (step_nop ws out)
  refine ⟨ws, p, by simp [p, nop], RelSeries.last_snoc .., rfl, le_rfl, ?_⟩
  apply RunPath.space_le_of_workTapePos_const
  intro c hc
  rcases RelSeries.mem_snoc.mp hc with ⟨n, rfl⟩ | rfl <;> rfl

end Turing.MultiTapeNTM
