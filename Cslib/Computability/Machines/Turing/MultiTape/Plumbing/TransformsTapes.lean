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
(every head reset to its initial position, tapes blank outside their words, the word `emitted`
appended to the output it was handed), with the new words related to the old ones by `Q`, and
every run from the start visits at most `s` work-tape cells. The machine may halt earlier than `t`;
since a halted machine stays put, running on to `t` costs nothing, so a fixed step count loses no
generality and spares every composition an existential.
Requiring this normal form is what lets specifications compose by rewriting: the halting
configuration of one machine is already a valid start for the next, so which words survived a step
is read off the equation, not re-established cell by cell.

The output is described as the word the machine *appends*, never as an absolute value, so that a
specification is insensitive to the output it is handed — which is what lets specifications
compose: along a sequence the emitted words concatenate.

## Main definitions

* `Turing.MultiTapeTM.TransformsTapes`: the specification format described above.
* `Turing.MultiTapeTM.nop`: the machine that does nothing.

## Main results

* `Turing.MultiTapeTM.TransformsTapes.imp`: strengthen the precondition, weaken the postcondition
  and raise the bounds.
* `Turing.MultiTapeTM.transformsTapes_iff_nil_output`: the generality in the ambient output is
  free, so a concrete machine need only be run with no prior output.
* `Turing.MultiTapeTM.transformsTapes_nop`: `nop` leaves every word as it was, the first machine of
  the interface and the check that the format is inhabited as intended.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `TransformsTapes tm P Q t s`: started in its initial state on tapes holding words `ws` that
satisfy the precondition `P`, the machine is halted after exactly `t` steps in the configuration
whose tapes hold words `ws'` and which has appended `emitted` to the output it was handed, with
`Q input ws ws' emitted`, and every run from the start visits at most `s` work-tape cells. The
machine is free to halt before step `t`, because it then stays in that configuration.

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
      ∀ p : tm.RunPath input, p.head = wordsCfg input (some tm.q₀) ws out → p.space ≤ s

/-- A `TransformsTapes` statement can be read with a stronger precondition, a weaker postcondition
and larger bounds. -/
theorem TransformsTapes.imp {tm : MultiTapeTM k Symbol State}
    {P P' : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q Q' : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {t s t' s' : ℕ} (h : TransformsTapes tm P Q t s)
    (hP : ∀ input ws, P' input ws → P input ws)
    (hQ : ∀ input ws ws' emitted, P' input ws → Q input ws ws' emitted → Q' input ws ws' emitted)
    (ht : t ≤ t') (hs : s ≤ s') :
    TransformsTapes tm P' Q' t' s' := by
  intro input ws out hP'
  obtain ⟨ws', emitted, hrun, hQ'', hspace⟩ := h input ws out (hP input ws hP')
  -- the machine is halted at step `t`, so running on to `t'` does not change the tapes
  have hhalt : (tm.runFrom (wordsCfg input (some tm.q₀) ws out) t).state = none := by
    rw [hrun]
    rfl
  refine ⟨ws', emitted, ?_, hQ input ws ws' emitted hP' hQ'', fun p hp => (hspace p hp).trans hs⟩
  rw [runFrom_eq_of_halt tm _ ht hhalt, hrun]

/-- A `TransformsTapes` statement can be read with larger bounds. -/
theorem TransformsTapes.mono {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {t s t' s' : ℕ} (h : TransformsTapes tm P Q t s) (ht : t ≤ t') (hs : s ≤ s') :
    TransformsTapes tm P Q t' s' :=
  h.imp (fun _ _ => id) (fun _ _ _ _ _ => id) ht hs

/-- **The ambient output is a concern of sequencing, not of machines.** A specification holds for
every prior output as soon as it holds for none, because a machine never reads what it has already
written. This is where that generality is discharged, once, rather than by every caller: a concrete
machine enters the interface by proving the right-hand side.

The only consumer of the generality is `Turing.MultiTapeTM.transformsTapes_seq`, which runs the
second machine after the first has emitted. -/
theorem transformsTapes_iff_nil_output {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ} :
    TransformsTapes tm P Q t s ↔ ∀ input ws, P input ws → ∃ ws' emitted,
      tm.runFrom (wordsCfg input (some tm.q₀) ws []) t = wordsCfg input none ws' emitted ∧
      Q input ws ws' emitted ∧
      ∀ p : tm.RunPath input, p.head = wordsCfg input (some tm.q₀) ws [] → p.space ≤ s := by
  constructor
  · intro h input ws hP
    simpa using h input ws [] hP
  · rintro h input ws out hP
    obtain ⟨ws', emitted, hrun, hQ, hspace⟩ := h input ws hP
    -- the run with output `out` is the run without it, mapped by prepending `out`
    have hcfg : wordsCfg input (some tm.q₀) ws out =
        tm.prependOutputHom out (wordsCfg input (some tm.q₀) ws []) := by simp
    refine ⟨ws', emitted, ?_, hQ, fun p hp => ?_⟩
    · rw [hcfg, runFrom_map, hrun]
      simp
    · rw [MultiTapeNTM.RunPath.eq_map_ofDeterministic _ p (hp.trans hcfg),
        MultiTapeNTM.RunPath.space_map_eq _ _ fun _ _ => rfl]
      exact hspace _ rfl

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
  rw [step_of_state (by rfl)]
  simp [nop, Action.apply, wordsCfg, SignType.cast]

/-- `nop` reaches its halting configuration after exactly one step. -/
@[simp]
lemma runFrom_nop_one (ws : Fin k → List Symbol) (out : List Symbol) :
    (nop k Symbol).runFrom (wordsCfg input (some ()) ws out) 1 = wordsCfg input none ws out := by
  simpa only [runFrom, Function.iterate_one] using step_nop ws out

/-- **The machine that does nothing** halts in one step, leaving every word as it was and emitting
nothing. Its heads never move, so it visits one cell per tape. This is the first machine of the
interface: it checks that the specification format is inhabited exactly as intended. -/
theorem transformsTapes_nop (k : ℕ) (Symbol : Type*) :
    TransformsTapes (nop k Symbol) (fun _ _ => True)
      (fun _ ws ws' emitted => ws' = ws ∧ emitted = []) 1 k := by
  intro input ws out _
  refine ⟨ws, [], by rw [List.append_nil]; exact runFrom_nop_one ws out, ⟨rfl, rfl⟩,
    fun p hp => ?_⟩
  -- the heads never move, so each head visits only the single cell `0`
  refine (p.space_le_sum_card (S := fun _ => {0}) ?_).trans_eq (by simp)
  rintro _ ⟨m, rfl⟩ i
  rw [runPath_apply_eq_runFrom, hp]
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h, runFrom]
  · rw [runFrom_eq_of_halt _ _ h (by rw [runFrom_nop_one]; rfl), runFrom_nop_one]
    simp

end Nop

end Turing.MultiTapeTM
