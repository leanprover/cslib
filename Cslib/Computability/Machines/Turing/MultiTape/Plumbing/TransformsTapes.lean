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

The interface through which combinators use machines: a machine reads words from its work tapes
and leaves words on them. A combinator composing such machines talks about words only, never about
individual cells, head positions or the set of tapes a machine has touched.

Configurations are described by *equalities*: `wordsCfg input q ws out` is the configuration whose
work tape `i` holds exactly the word `ws i` (contents `tapeOfList (ws i)`, head at the start), with
the input head at the start of the input and output `out`. A specification
`TransformsTapes tm P Q t s` says: started on word-holding tapes satisfying `P`, the machine has
a path of at most `t` steps to the halted *normal form* `wordsCfg input none ws' out` (every head
reset to its initial position, tapes blank outside their words, output untouched), with the new
words related to the old ones by `Q` and using at most `s` work-tape cells. The same path witnesses
the postcondition and both bounds; other paths of a nondeterministic machine are unrestricted.
Requiring this normal form is what lets specifications compose by rewriting: the halting
configuration of one machine is already a valid start for the next, so which words survived a step
is read off the equation, not re-established cell by cell.

## Main definitions

* `Turing.MultiTapeNTM.TransformsTapes`: the specification format described above.
* `Turing.MultiTapeNTM.nop`: the machine that does nothing.

## Main results

* `Turing.MultiTapeNTM.TransformsTapes.imp`: strengthen the precondition, weaken the postcondition
  and raise the bounds.
* `Turing.MultiTapeNTM.transformsTapes_nop`: `nop` leaves every word as it was, the first machine of
  the interface and the check that the format is inhabited as intended.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `TransformsTapes tm P Q t s`: started in its initial state on tapes holding words `ws` that
satisfy the precondition `P`, the machine has a path of at most `t` steps to the halted
configuration whose tapes hold words `ws'` with `Q input ws ws'`, having used at most `s` work-tape
cells along that path. Every head is reset and the output is unchanged.

The bounds are numbers; a specification whose bounds depend on the data is a *family*
`∀ j, TransformsTapes tm (P j) (Q j) (t j) (s j)` over one fixed machine. -/
def TransformsTapes (tm : MultiTapeNTM k Symbol State)
    (P : (input : List Symbol) → (Fin k → List Symbol) → Prop)
    (Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop)
    (t s : ℕ) : Prop :=
  ∀ (input : List Symbol) (ws : Fin k → List Symbol) (out : List Symbol), P input ws →
    ∃ ws', ∃ p : tm.RunPath input,
      p.head = wordsCfg input (some tm.q₀) ws out ∧
      p.last = wordsCfg input none ws' out ∧ Q input ws ws' ∧ p.length ≤ t ∧ p.space ≤ s

/-- A `TransformsTapes` statement can be read with a stronger precondition, a weaker postcondition
and larger bounds. -/
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

/-- A `TransformsTapes` statement can be read with larger bounds. -/
theorem TransformsTapes.mono {tm : MultiTapeNTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop}
    {t s t' s' : ℕ} (h : TransformsTapes tm P Q t s) (ht : t ≤ t') (hs : s ≤ s') :
    TransformsTapes tm P Q t' s' :=
  h.imp (fun _ _ => id) (fun _ _ _ _ => id) ht hs

/-- The machine that does nothing: it halts on its first step, leaving the tapes and their heads
unchanged. -/
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

/-- **The machine that does nothing** halts in one step, leaving every word as it was. Its heads
never move, so it visits one cell per tape. This is the first machine of the interface: it checks
that the specification format is inhabited exactly as intended. -/
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
