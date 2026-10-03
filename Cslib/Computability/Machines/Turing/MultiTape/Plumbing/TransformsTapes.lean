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
`TransformsTapes tm P Q t s` says: started on word-holding tapes satisfying `P`, after exactly `t`
steps the machine sits in the halted *normal form* `wordsCfg input none ws' (out ++ emitted)`
(every head reset to its initial position, tapes blank outside their words, the ambient output
extended by whatever the machine emitted), with the new words and the emitted word related to the
old words by `Q` and using at most `s` work-tape cells. The machine may halt earlier
than `t`; since a halted machine stays put and stops visiting new cells, running on to `t` costs
nothing, so a fixed step count loses no generality and spares every composition an existential.
Requiring this normal form is what lets specifications compose by rewriting: the halting
configuration of one machine is already a valid start for the next, so which words survived a step
is read off the equation, not re-established cell by cell.

A whole computation is described in the same vocabulary by
`ComputesNormalizedInTimeAndSpace`: a machine that starts on blank tapes and halts in the same
normal form, having emitted its output. This is `ComputesInTimeAndSpace` strengthened by the
requirement that the machine clean up after itself. It is not a separate notion: it is exactly the
transformation that turns blank tapes into blank tapes and emits the output, on one fixed input,
and `ComputesNormalizedInTimeAndSpace.transformsTapes` says so. That is what makes a computation
usable as a *component* — every combinator of the plumbing layer consumes a `TransformsTapes` and
produces one, so computations and plumbing stack without a change of vocabulary.

## Main definitions

* `Turing.MultiTapeTM.TransformsTapes`: the specification format described above.
* `Turing.MultiTapeTM.ComputesNormalizedInTimeAndSpace`: a computation that leaves its tapes in
  the normal form.
* `Turing.MultiTapeTM.nop`: the machine that does nothing.

## Main results

* `Turing.MultiTapeTM.TransformsTapes.imp`: strengthen the precondition, weaken the postcondition
  and raise the bounds.
* `Turing.MultiTapeTM.TransformsTapes.exists`: a family of specifications over a parameter is a
  single specification with an existential precondition.
* `Turing.MultiTapeTM.ComputesNormalizedInTimeAndSpace.computesInTimeAndSpace`: a normalized
  computation is in particular a computation.
* `Turing.MultiTapeTM.ComputesNormalizedInTimeAndSpace.transformsTapes`: a normalized computation
  is in particular a tape transformation, and can therefore be plumbed.
* `Turing.MultiTapeTM.transformsTapes_nop`: `nop` leaves every word as it was, the first machine of
  the interface and the check that the format is inhabited as intended.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `TransformsTapes tm P Q t s`: started in its initial state on tapes holding words `ws` that
satisfy the precondition `P`, the machine is halted after exactly `t` steps in the configuration
whose tapes hold words `ws'` and which has appended `emitted` to the output, with
`Q input ws ws' emitted`, having used at most `s` work-tape cells. The machine is free to halt
before step `t`, because it then stays in that configuration.

The output is described as a *suffix* appended to whatever was already there, never as an absolute
value, so that the specification is insensitive to the ambient output — which is what lets
specifications compose: in a sequence the emitted words concatenate.

The bounds are numbers; a specification whose bounds depend on the data is a *family*
`∀ j, TransformsTapes tm (P j) (Q j) (t j) (s j)` over one fixed machine. -/
def TransformsTapes (tm : MultiTapeTM k Symbol State)
    (P : (input : List Symbol) → (Fin k → List Symbol) → Prop)
    (Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop)
    (t s : ℕ) : Prop :=
  ∀ (input : List Symbol) (ws : Fin k → List Symbol) (out : List Symbol), P input ws →
    ∃ ws' emitted,
      tm.runFrom (wordsCfg input (some tm.q₀) ws out) t =
        wordsCfg input none ws' (out ++ emitted) ∧
      Q input ws ws' emitted ∧
      tm.spaceUsed (wordsCfg input (some tm.q₀) ws out) t ≤ s

/-- A `TransformsTapes` statement can be read with a stronger precondition, a weaker postcondition
and larger bounds. -/
theorem TransformsTapes.imp {tm : MultiTapeTM k Symbol State}
    {P P' : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q Q' : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {t s t' s' : ℕ} (h : TransformsTapes tm P Q t s)
    (hP : ∀ input ws, P' input ws → P input ws)
    (hQ : ∀ input ws ws' e, P' input ws → Q input ws ws' e → Q' input ws ws' e)
    (ht : t ≤ t') (hs : s ≤ s') :
    TransformsTapes tm P' Q' t' s' := by
  intro input ws out hP'
  obtain ⟨ws', e, hrun, hQ'', hspace⟩ := h input ws out (hP input ws hP')
  -- the machine is halted at step `t`, so running on to `t'` changes neither tapes nor space
  have hhalt : (tm.runFrom (wordsCfg input (some tm.q₀) ws out) t).state = none := by
    rw [hrun]
    rfl
  refine ⟨ws', e, ?_, hQ input ws ws' e hP' hQ'', ?_⟩
  · rw [runFrom_eq_of_halt tm _ ht hhalt, hrun]
  · rw [spaceUsed_eq_of_halt _ ht hhalt]
    exact hspace.trans hs

/-- A family of specifications over a parameter is a single specification whose precondition is
the existential over the family. The parameter is recovered in the postcondition, so nothing is
lost; this is how a family with *uniform* bounds is turned back into a single statement. -/
theorem TransformsTapes.exists {ι : Sort*} {tm : MultiTapeTM k Symbol State}
    {P : ι → (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : ι → (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {t s : ℕ} (h : ∀ j, TransformsTapes tm (P j) (Q j) t s) :
    TransformsTapes tm (fun input ws => ∃ j, P j input ws)
      (fun input ws ws' e => ∃ j, P j input ws ∧ Q j input ws ws' e) t s := by
  rintro input ws out ⟨j, hj⟩
  obtain ⟨ws', e, hrun, hQ, hspace⟩ := h j input ws out hj
  exact ⟨ws', e, hrun, ⟨j, hj, hQ⟩, hspace⟩

/-! ### Normalized computations -/

section Normalized

/-- `ComputesNormalizedInTimeAndSpace tm input output t s`: started on blank work tapes, the
machine is after `t` steps halted *in the normal form* — every work tape blank again, every work
head back at cell `0` and the input head back at the start of the input — having emitted `output`
and used at most `s` work-tape cells. As everywhere in this file the time bound is an upper bound:
the machine may halt earlier and then simply stay put.

This is `Turing.MultiTapeTM.ComputesInTimeAndSpace` plus the requirement that the machine clean up
after itself, and it is what makes a computation usable as a component: because the final
configuration is again a `Turing.wordsCfg`, the run can be composed with the plumbing machines
that move words between the tapes and the input and output streams. -/
def ComputesNormalizedInTimeAndSpace (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ) : Prop :=
  tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
      wordsCfg input none (fun _ => []) output ∧
  tm.spaceUsed (wordsCfg input (some tm.q₀) (fun _ => []) []) t ≤ s

namespace ComputesNormalizedInTimeAndSpace

variable {tm : MultiTapeTM k Symbol State} {input output : List Symbol} {t s : ℕ}

/-- The run of a normalized computation, started from the initial configuration. -/
lemma runFrom_initCfg (h : tm.ComputesNormalizedInTimeAndSpace input output t s) :
    tm.runFrom (tm.initCfg input) t = wordsCfg input none (fun _ => []) output := by
  rw [initCfg, Cfg.init_eq_wordsCfg]
  exact h.1

/-- The space of a normalized computation, started from the initial configuration. -/
lemma spaceUsed_initCfg (h : tm.ComputesNormalizedInTimeAndSpace input output t s) :
    tm.spaceUsed (tm.initCfg input) t ≤ s := by
  rw [initCfg, Cfg.init_eq_wordsCfg]
  exact h.2

/-- **A normalized computation is a computation.** The space bound of
`Turing.MultiTapeTM.ComputesInTimeAndSpace` is exact, so it is met by the space actually used,
which is at most `s`. -/
theorem computesInTimeAndSpace (h : tm.ComputesNormalizedInTimeAndSpace input output t s) :
    ∃ s' ≤ s, tm.ComputesInTimeAndSpace input output t s' :=
  ⟨_, h.spaceUsed_initCfg, by rw [h.runFrom_initCfg]; rfl, by rw [h.runFrom_initCfg]; rfl, rfl⟩

/-- Both bounds can be weakened: the machine has halted at step `t`, so it neither moves nor
visits new cells afterwards. -/
theorem mono (h : tm.ComputesNormalizedInTimeAndSpace input output t s) {t' s' : ℕ}
    (ht : t ≤ t') (hs : s ≤ s') :
    tm.ComputesNormalizedInTimeAndSpace input output t' s' := by
  have hhalt : (tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t).state = none := by
    rw [h.1]; rfl
  exact ⟨by rw [runFrom_eq_of_halt _ _ ht hhalt, h.1],
    by rw [spaceUsed_eq_of_halt _ ht hhalt]; exact h.2.trans hs⟩

/-- Spelling a run on blank tapes and no output as a run on blank tapes over an arbitrary ambient
output, which the machine never reads. -/
private lemma wordsCfg_eq_prependOutput (q : Option State) (out : List Symbol) :
    wordsCfg (k := k) input q (fun _ => []) out =
      (wordsCfg input q (fun _ => ([] : List Symbol)) []).prependOutput out := by
  simp

/-- **A normalized computation is a tape transformation.** It is the one that turns blank tapes
into blank tapes and emits `output`, on the single input it is about. The ambient output plays no
role, because a machine never reads what it has already written.

This is the bridge that lets a whole computation be fed to the combinators of the plumbing layer,
which all speak `Turing.MultiTapeTM.TransformsTapes`. -/
theorem transformsTapes (h : tm.ComputesNormalizedInTimeAndSpace input output t s) :
    TransformsTapes tm (fun inp ws => inp = input ∧ ws = fun _ => [])
      (fun _ _ ws' e => ws' = (fun _ => []) ∧ e = output) t s := by
  rintro inp ws out ⟨rfl, rfl⟩
  refine ⟨fun _ => [], output, ?_, ⟨rfl, rfl⟩, ?_⟩
  · rw [wordsCfg_eq_prependOutput, runFrom_prependOutput, h.1]
    simp
  · rw [wordsCfg_eq_prependOutput, spaceUsed_prependOutput]
    exact h.2

end ComputesNormalizedInTimeAndSpace

end Normalized

section Nop

/-- The machine that does nothing: it halts on its first step, leaving the configuration
unchanged. -/
def nop (k : ℕ) (Symbol : Type*) : MultiTapeTM k Symbol Unit where
  q₀ := ()
  tr _ _ _ := { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }

/-- A single step of `nop` halts and leaves the words alone. -/
@[simp]
lemma step_nop (ws : Fin k → List Symbol) (out : List Symbol) :
    (nop k Symbol).step (wordsCfg input (some ()) ws out) = wordsCfg input none ws out := by
  refine Cfg.ext rfl ?_ ?_ ?_ ?_ <;>
    simp [step, nop, Action.apply, wordsCfg, SignType.cast]

/-- `nop` reaches its halting configuration after exactly one step. -/
@[simp]
lemma runFrom_nop_one (ws : Fin k → List Symbol) (out : List Symbol) :
    (nop k Symbol).runFrom (wordsCfg input (some ()) ws out) 1 = wordsCfg input none ws out := by
  simpa only [runFrom, Function.iterate_one] using step_nop ws out

/-- **The machine that does nothing** halts in one step, leaving every word as it was. Its heads
never move, so it visits one cell per tape. This is the first machine of the interface: it checks
that the specification format is inhabited exactly as intended. -/
theorem transformsTapes_nop (k : ℕ) (Symbol : Type*) :
    TransformsTapes (nop k Symbol) (fun _ _ => True) (fun _ ws ws' e => ws' = ws ∧ e = []) 1 k := by
  intro input ws out _
  -- the heads never move, so each tape touches only the single cell `0`
  refine ⟨ws, [], by rw [List.append_nil]; exact runFrom_nop_one ws out, ⟨rfl, rfl⟩,
    spaceUsed_le_of_workTapePos_const _ 1 fun m hm => ?_⟩
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
  · rfl
  · rw [runFrom_nop_one]; funext i; simp only [wordsCfg_workTapePos]

end Nop

end Turing.MultiTapeTM
