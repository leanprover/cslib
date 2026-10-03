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

A whole computation needs no separate vocabulary. A machine that starts on blank tapes and halts
in the same normal form, having emitted its output, *is* the tape transformation whose
precondition pins the input and whose postcondition pins the emitted word; so
`ComputesNormalizedInTimeAndSpace` is an abbreviation for that transformation rather than a notion
of its own, and `ComputesFunNormalizedInTimeAndSpace` — `ComputesFunInTimeAndSpace` strengthened
by the requirement that the machine clean up after itself — is the family of them. That is what
makes a computation usable as a *component*: every combinator of the plumbing layer consumes a
`TransformsTapes` and produces one, so computations and plumbing stack with nothing in between.

## Main definitions

* `Turing.MultiTapeTM.TransformsTapes`: the specification format described above.
* `Turing.MultiTapeTM.ComputesNormalizedInTimeAndSpace`: a computation that leaves its tapes in
  the normal form, as a specification.
* `Turing.MultiTapeTM.ComputesFunNormalizedInTimeAndSpace`: a machine computing a function and
  leaving its tapes in the normal form, as a family of specifications.
* `Turing.MultiTapeTM.nop`: the machine that does nothing.

## Main results

* `Turing.MultiTapeTM.TransformsTapes.imp`: strengthen the precondition, weaken the postcondition
  and raise the bounds.
* `Turing.MultiTapeTM.TransformsTapes.exists`: a family of specifications over a parameter is a
  single specification with an existential precondition.
* `Turing.MultiTapeTM.transformsTapes_iff_nil_output`: a specification holds over every ambient
  output as soon as it holds over none; this is how a concrete machine enters the interface.
* `Turing.MultiTapeTM.computesNormalized_iff`: a normalized computation, as an equation.
* `Turing.MultiTapeTM.TransformsTapes.computesInTimeAndSpace`: and how it leaves it again.
* `Turing.MultiTapeTM.ComputesFunNormalizedInTimeAndSpace.computesFunInTimeAndSpace`: a normalized
  computation is in particular a computation.
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

/-! ### Whole computations as tape transformations -/

section Computations

variable {tm : MultiTapeTM k Symbol State}
  {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
  {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
    List Symbol → Prop}
  {t s : ℕ}

/-- Spelling a run over an arbitrary ambient output as a run with no prior output, which the
machine never reads. -/
private lemma wordsCfg_eq_prependOutput (q : Option State) (ws : Fin k → List Symbol)
    (out : List Symbol) :
    wordsCfg input q ws out = (wordsCfg input q ws []).prependOutput out := by
  simp

/-- **The ambient output is a concern of sequencing, not of machines.** A specification holds for
every prior output as soon as it holds for none, because a machine never reads what it has already
written. This is where that is discharged, once, rather than by every caller: a concrete machine
enters the interface by proving the right-hand side.

The only consumer of the generality is `Turing.MultiTapeTM.transformsTapes_seq`, which runs the
second machine after the first has emitted. -/
theorem transformsTapes_iff_nil_output :
    TransformsTapes tm P Q t s ↔ ∀ input ws, P input ws → ∃ ws' e,
      tm.runFrom (wordsCfg input (some tm.q₀) ws []) t = wordsCfg input none ws' e ∧
      Q input ws ws' e ∧ tm.spaceUsed (wordsCfg input (some tm.q₀) ws []) t ≤ s := by
  constructor
  · intro h input ws hP
    simpa using h input ws [] hP
  · rintro h input ws out hP
    obtain ⟨ws', e, hrun, hQ, hspace⟩ := h input ws hP
    refine ⟨ws', e, ?_, hQ, ?_⟩
    · rw [wordsCfg_eq_prependOutput, runFrom_prependOutput, hrun]
      simp
    · rw [wordsCfg_eq_prependOutput, spaceUsed_prependOutput]
      exact hspace

/-- `ComputesNormalizedInTimeAndSpace tm input output t s`: started on blank tapes, the machine
halts *in the normal form* — every work tape blank again, every work head back at cell `0` and the
input head back at the start of the input — having emitted `output`, within `t` steps and `s`
work-tape cells.

This is not a notion of its own: it is literally the tape transformation that turns blank tapes
into blank tapes and emits `output`, on the one input it is about. Saying so in the definition is
what lets every combinator of the plumbing layer consume a computation directly, with no change of
vocabulary. `Turing.MultiTapeTM.computesNormalized_iff` is the equation form. -/
abbrev ComputesNormalizedInTimeAndSpace (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ) : Prop :=
  TransformsTapes tm (fun inp ws => inp = input ∧ ws = fun _ => [])
    (fun _ _ ws' e => ws' = (fun _ => []) ∧ e = output) t s

/-- **A normalized computation is `ComputesInTimeAndSpace` plus cleanup.** Unfolding the
specification leaves exactly the run equation of
`Turing.MultiTapeTM.ComputesInTimeAndSpace`, strengthened to demand the normal form again at the
end, together with the space bound. -/
theorem computesNormalized_iff {input output : List Symbol} :
    tm.ComputesNormalizedInTimeAndSpace input output t s ↔
      tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
          wordsCfg input none (fun _ => []) output ∧
        tm.spaceUsed (wordsCfg input (some tm.q₀) (fun _ => []) []) t ≤ s := by
  constructor
  · intro h
    obtain ⟨ws', e, hrun, ⟨rfl, rfl⟩, hspace⟩ :=
      transformsTapes_iff_nil_output.mp h input (fun _ => []) ⟨rfl, rfl⟩
    exact ⟨hrun, hspace⟩
  · rintro ⟨hrun, hspace⟩
    refine transformsTapes_iff_nil_output.mpr ?_
    rintro inp ws ⟨rfl, rfl⟩
    exact ⟨fun _ => [], output, hrun, ⟨rfl, rfl⟩, hspace⟩

/-- **A single normalized run is a tape transformation.** This is how a concrete machine enters
the interface. -/
theorem transformsTapes_of_runFrom {input output : List Symbol}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
      wordsCfg input none (fun _ => []) output)
    (hspace : tm.spaceUsed (wordsCfg input (some tm.q₀) (fun _ => []) []) t ≤ s) :
    tm.ComputesNormalizedInTimeAndSpace input output t s :=
  computesNormalized_iff.mpr ⟨hrun, hspace⟩

/-- A specification read from the *initial* configuration, which is the word configuration with
blank tapes and no output. This is the step from the vocabulary of the plumbing layer back to the
vocabulary of whole computations. -/
theorem TransformsTapes.runFrom_initCfg (h : TransformsTapes tm P Q t s) {input : List Symbol}
    (hP : P input fun _ => []) :
    ∃ ws' e, tm.runFrom (tm.initCfg input) t = wordsCfg input none ws' e ∧
      Q input (fun _ => []) ws' e ∧ tm.spaceUsed (tm.initCfg input) t ≤ s := by
  obtain ⟨ws', e, hrun, hQ, hspace⟩ := h input (fun _ => []) [] hP
  rw [List.nil_append] at hrun
  rw [initCfg, Cfg.init_eq_wordsCfg]
  exact ⟨ws', e, hrun, hQ, hspace⟩

/-- **A tape transformation that accepts blank tapes is a computation.** The space bound of
`Turing.MultiTapeTM.ComputesInTimeAndSpace` is exact, so it is met by the space actually used,
which is at most `s`. -/
theorem TransformsTapes.computesInTimeAndSpace (h : TransformsTapes tm P Q t s)
    {input output : List Symbol} (hP : P input fun _ => [])
    (hQ : ∀ ws' e, Q input (fun _ => []) ws' e → e = output) :
    ∃ s' ≤ s, tm.ComputesInTimeAndSpace input output t s' := by
  obtain ⟨ws', e, hrun, hq, hspace⟩ := h.runFrom_initCfg hP
  obtain rfl := hQ ws' e hq
  exact ⟨_, hspace, by rw [hrun]; rfl, by rw [hrun]; rfl, rfl⟩

/-- `ComputesFunNormalizedInTimeAndSpace tm encIn encOut f t s`: for every `a`, the machine is the
tape transformation which, started on blank tapes with `encIn a` on the input tape, halts *in the
normal form* — every work tape blank again, every work head back at cell `0` and the input head
back at the start of the input — having emitted `encOut (f a)`, within `t a` steps and `s a`
work-tape cells.

This is `Turing.MultiTapeTM.ComputesFunInTimeAndSpace` plus the requirement that the machine clean
up after itself, and it is a *family of specifications* in the sense of
`Turing.MultiTapeTM.TransformsTapes`, exactly as the bounds of the plumbing layer are families
whenever they depend on the data. -/
def ComputesFunNormalizedInTimeAndSpace {α β : Type*} (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol) (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, tm.ComputesNormalizedInTimeAndSpace (encIn a) (encOut (f a)) (t a) (s a)

namespace ComputesFunNormalizedInTimeAndSpace

variable {α β : Type*} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol} {f : α → β}
  {t s : α → ℕ}

/-- Resource bounds can be weakened independently on every input. -/
theorem mono (h : ComputesFunNormalizedInTimeAndSpace tm encIn encOut f t s) {t' s' : α → ℕ}
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputesFunNormalizedInTimeAndSpace tm encIn encOut f t' s' :=
  fun a => (h a).imp (fun _ _ h => h) (fun _ _ _ _ _ h => h) (ht a) (hs a)

/-- **A normalized computation is a computation.** -/
theorem computesFunInTimeAndSpace
    (h : ComputesFunNormalizedInTimeAndSpace tm encIn encOut f t s) :
    ComputesFunInTimeAndSpace tm encIn encOut f t s := fun a =>
  let ⟨s', hs', hc⟩ := (h a).computesInTimeAndSpace ⟨rfl, rfl⟩ fun _ _ h => h.2
  ⟨t a, le_refl _, s', hs', hc⟩

end ComputesFunNormalizedInTimeAndSpace

end Computations

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
