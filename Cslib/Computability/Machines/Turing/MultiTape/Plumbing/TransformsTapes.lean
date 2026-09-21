/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

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
steps the machine sits in the halted *normal form* `wordsCfg input none ws' out` (every head reset
to its initial position, tapes blank outside their words, output untouched), with the new words
related to the old ones by `Q` and using at most `s` work-tape cells. The machine may halt earlier
than `t`; since a halted machine stays put and stops visiting new cells, running on to `t` costs
nothing, so a fixed step count loses no generality and spares every composition an existential.
Requiring this normal form is what lets specifications compose by rewriting: the halting
configuration of one machine is already a valid start for the next, so which words survived a step
is read off the equation, not re-established cell by cell.

## Main definitions

* `Turing.MultiTapeTM.tapeOfList`: the tape holding exactly a given word.
* `Turing.MultiTapeTM.wordsCfg`: the configuration whose tapes hold given words.
* `Turing.MultiTapeTM.TransformsTapes`: the specification format described above.
* `Turing.MultiTapeTM.nop`: the machine that does nothing.

## Main results

* `Turing.MultiTapeTM.TransformsTapes.imp`: strengthen the precondition, weaken the postcondition
  and raise the bounds.
* `Turing.MultiTapeTM.transformsTapes_nop`: `nop` leaves every word as it was, the first machine of
  the interface and the check that the format is inhabited as intended.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- A tape containing exactly the symbols of `xs` at positions `0, ..., xs.length - 1`. -/
def tapeOfList (xs : List Symbol) : ℤ → Option Symbol
  | .ofNat n => xs[n]?
  | .negSucc _ => none

@[simp]
lemma tapeOfList_ofNat (xs : List Symbol) (n : ℕ) : tapeOfList xs n = xs[n]? := rfl

@[simp]
lemma tapeOfList_negSucc (xs : List Symbol) (n : ℕ) :
    tapeOfList xs (.negSucc n) = none := rfl

/-- Appending one symbol writes precisely the cell after the existing word. -/
lemma tapeOfList_append_single (xs : List Symbol) (x : Symbol) :
    tapeOfList (xs ++ [x]) = Function.update (tapeOfList xs) (xs.length : ℤ) (some x) := by
  funext z
  cases z with
  | negSucc n => simp [tapeOfList]
  | ofNat n => grind [tapeOfList]

/-- The blank tape holds the empty word. -/
@[simp]
lemma tapeOfList_nil : tapeOfList ([] : List Symbol) = fun _ => none := by
  funext z
  cases z <;> simp

/-- The cell at position `0` holds the first symbol of the word. -/
lemma tapeOfList_zero (xs : List Symbol) : tapeOfList xs 0 = xs.head? := by
  have h : (0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
  rw [h, tapeOfList_ofNat]
  cases xs <;> rfl

/-- The configuration whose work tape `i` holds exactly the word `ws i` with its head at the
start, whose input head is at the start of the input, in state `q` with output `out`. -/
@[simps]
def wordsCfg (input : List Symbol) (q : Option State)
    (ws : Fin k → List Symbol) (out : List Symbol) : Cfg k Symbol State input :=
  ⟨q, 1, fun i => tapeOfList (ws i), fun _ => 0, out⟩

/-- Remapping the state of a `wordsCfg` remaps its state and leaves the words alone. -/
@[simp]
lemma mapState_wordsCfg {State' : Type*} (φ : Option State → Option State')
    (input : List Symbol) (q : Option State) (ws : Fin k → List Symbol) (out : List Symbol) :
    (wordsCfg input q ws out).mapState φ = wordsCfg input (φ q) ws out := rfl

/-- The initial configuration is the word configuration with blank tapes and no output. -/
lemma initCfg_eq_wordsCfg (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
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
def TransformsTapes (tm : MultiTapeTM k Symbol State)
    (P : (input : List Symbol) → (Fin k → List Symbol) → Prop)
    (Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop)
    (t s : ℕ) : Prop :=
  ∀ (input : List Symbol) (ws : Fin k → List Symbol) (out : List Symbol), P input ws →
    ∃ ws',
      tm.runFrom (wordsCfg input (some tm.q₀) ws out) t = wordsCfg input none ws' out ∧
      Q input ws ws' ∧
      tm.spaceUsed (wordsCfg input (some tm.q₀) ws out) t ≤ s

/-- A `TransformsTapes` statement can be read with a stronger precondition, a weaker postcondition
and larger bounds. -/
theorem TransformsTapes.imp {tm : MultiTapeTM k Symbol State}
    {P P' : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q Q' : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) → Prop}
    {t s t' s' : ℕ} (h : TransformsTapes tm P Q t s)
    (hP : ∀ input ws, P' input ws → P input ws)
    (hQ : ∀ input ws ws', P' input ws → Q input ws ws' → Q' input ws ws')
    (ht : t ≤ t') (hs : s ≤ s') :
    TransformsTapes tm P' Q' t' s' := by
  intro input ws out hP'
  obtain ⟨ws', hrun, hQ'', hspace⟩ := h input ws out (hP input ws hP')
  -- the machine is halted at step `t`, so running on to `t'` changes neither tapes nor space
  have hhalt : (tm.runFrom (wordsCfg input (some tm.q₀) ws out) t).state = none := by
    rw [hrun]
    rfl
  refine ⟨ws', ?_, hQ input ws ws' hP' hQ'', ?_⟩
  · rw [runFrom_eq_of_halt tm _ ht hhalt, hrun]
  · rw [spaceUsed_eq_of_halt _ ht hhalt]
    exact hspace.trans hs

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
  rw [runFrom_succ_eq_step', runFrom_zero, step_nop]

/-- **The machine that does nothing** halts in one step, leaving every word as it was. Its heads
never move, so it visits one cell per tape. This is the first machine of the interface: it checks
that the specification format is inhabited exactly as intended. -/
theorem transformsTapes_nop (k : ℕ) (Symbol : Type*) :
    TransformsTapes (nop k Symbol) (fun _ _ => True) (fun _ ws ws' => ws' = ws) 1 k := by
  intro input ws out _
  -- the heads never move, so each tape touches only the single cell `0`
  refine ⟨ws, runFrom_nop_one ws out, rfl,
    spaceUsed_le_of_workTapePos_const _ 1 fun m hm => ?_⟩
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
  · rw [runFrom_zero]
  · rw [runFrom_nop_one]; funext i; simp only [wordsCfg_workTapePos]

end Nop

end Turing.MultiTapeTM
