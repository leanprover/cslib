/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Machines as transformers of tape words

The interface through which combinators use machines: a machine reads words from its work tapes
and leaves words on them. A combinator composing such machines talks about words only, never about
individual cells, head positions or the set of tapes a machine has touched.

Configurations are described by *equalities*: `wordsCfg input q ws out` is the configuration whose
work tape `i` holds exactly the word `ws i` (contents `tapeOfList (ws i)`, head at the start), with
the input head at the start of the input and output `out`. A specification
`TransformsTapes tm P Q t s` says: started on word-holding tapes satisfying `P`, after exactly `t`
steps a chosen path ends in the halted *normal form* `wordsCfg input none ws' out` (every head reset
to its initial position, tapes blank outside their words, output untouched), with the new words
related to the old ones by `Q` and using at most `s` work-tape cells. The machine may halt earlier
than `t`; since a halted machine stays put and stops visiting new cells, running on to `t` costs
nothing, so a fixed step count loses no generality and allows a uniform specification of bounds.
Requiring this normal form is what lets specifications compose by rewriting: the halting
configuration of one machine is already a valid start for the next, so which words survived a step
is read off the equation, not re-established cell by cell.

## Main definitions

* `Turing.tapeOfList`: the tape holding exactly a given word.
* `Turing.wordsCfg`: the configuration whose tapes hold given words.
* `Turing.MultiTapeNTM.TransformsTapes`: the specification format described above.
* `Turing.MultiTapeTM.nop`: the machine that does nothing.

## Main results

* `Turing.MultiTapeNTM.TransformsTapes.imp`: strengthen the precondition, weaken the postcondition
  and raise the bounds.
* `Turing.MultiTapeTM.transformsTapes_nop`: `nop` leaves every word as it was, the first machine of
  the interface and the check that the format is inhabited as intended.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The initial configuration is the word configuration with blank tapes and no output. -/
lemma initCfg_eq_wordsCfg (tm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    tm.initCfg input = wordsCfg input (some tm.q₀) (fun _ => []) [] := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i
  simp [Cfg.init, wordsCfg]

/-- `TransformsTapes tm P Q t s`: started in its initial state on tapes holding words `ws` that
satisfy the precondition `P`, the machine is halted after exactly `t` steps in the configuration
whose tapes hold words `ws'` with `Q input ws ws'`, having used at most `s` work-tape cells. The
machine is free to halt before step `t`, because it then stays in that configuration.

The bounds are numbers; a specification whose bounds depend on the data is a *family*
`∀ j, TransformsTapes tm (P j) (Q j) (t j) (s j)` over one fixed machine. -/
def TransformsTapes (tm : MultiTapeNTM k Symbol State)
    (P : (input : List Symbol) → (Fin k → List Symbol) → Prop)
    (Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop)
    (t s : ℕ) : Prop :=
  ∀ (input : List Symbol) (ws : Fin k → List Symbol) (out : List Symbol), P input ws →
    ∃ ws', ∃ p : tm.RunPath (wordsCfg input (some tm.q₀) ws out),
      p.time = t ∧ p.last = wordsCfg input none ws' out ∧ Q input ws ws' ∧ p.space ≤ s

/-- A `TransformsTapes` statement can be read with a stronger precondition, a weaker postcondition
and larger bounds. -/
theorem TransformsTapes.imp {tm : MultiTapeNTM k Symbol State}
    {P P' : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q Q' : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop}
    {t s t' s' : ℕ} (h : TransformsTapes tm P Q t s)
    (hP : ∀ input ws, P' input ws → P input ws)
    (hQ : ∀ input ws ws', P' input ws → Q input ws ws' → Q' input ws ws')
    (ht : t ≤ t') (hs : s ≤ s') :
    TransformsTapes tm P' Q' t' s' := by
  intro input ws out hP'
  obtain ⟨ws', p, rfl, hrun, hQ'', hspace⟩ := h input ws out (hP input ws hP')
  have hhalt : p.last.Halted := by simp [Cfg.Halted, hrun]
  exact ⟨ws', p.pad (t' - p.time) hhalt, by simp; omega,
    hrun, hQ input ws ws' hP' hQ'', by simpa using hspace.trans hs⟩

end Turing.MultiTapeNTM

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} {input : List Symbol}

section Nop

/-- The machine that does nothing: it halts on its first step, leaving the configuration
unchanged. -/
def nop (k : ℕ) (Symbol : Type*) : MultiTapeTM k Symbol Unit :=
  ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }

/-- A single step of `nop` halts and leaves the words alone. -/
@[simp]
lemma step_nop (ws : Fin k → List Symbol) (out : List Symbol) :
    (nop k Symbol).step (wordsCfg input (some ()) ws out) = wordsCfg input none ws out := by
  simp [step_of_state, nop, Action.apply, wordsCfg, SignType.cast]

/-- `nop` reaches its halting configuration after exactly one step. -/
@[simp]
lemma runFrom_nop_one (ws : Fin k → List Symbol) (out : List Symbol) :
    (nop k Symbol).runFrom (wordsCfg input (some ()) ws out) 1 = wordsCfg input none ws out := by
  simpa only [runFrom, Function.iterate_one] using step_nop ws out

/-- **The machine that does nothing** halts in one step, leaving every word as it was. Its heads
never move, so it visits one cell per tape. This is the first machine of the interface: it checks
that the specification format is inhabited exactly as intended. -/
theorem transformsTapes_nop (k : ℕ) (Symbol : Type*) :
    (nop k Symbol).TransformsTapes (fun _ _ => True) (fun _ ws ws' => ws' = ws) 1 k := by
  intro input ws out _
  let p : (nop k Symbol).RunPath (wordsCfg input (some ()) ws out) :=
    { cfgs := [wordsCfg input (some ()) ws out, wordsCfg input none ws out]
      last := wordsCfg input none ws out
      isChainFromTo := by simp }
  refine ⟨ws, p, rfl, rfl, rfl, ?_⟩
  simp [p, MultiTapeNTM.RunPath.space, spaceUsedOfCfgs, visitedOfCfgs, wordsCfg]

end Nop

end Turing.MultiTapeTM
