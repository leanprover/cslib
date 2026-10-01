/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes
public import Mathlib.Data.Fintype.Option
public import Mathlib.Basic.Finite.Sum

/-!
# Branching combinators

`branch i x tm₁ tm₂` first reads one symbol — the one under the head of work tape `i` — then,
depending on whether it equals `some x`, behaves like `tm₁` or like `tm₂`, each started in its
initial state on the tapes as they were.

It is a control combinator analogous to sequential composition (`Plumbing/Sequential.lean`): the
state space adds a fresh dispatch state on top of `State₁ ⊕ State₂`, the dispatch is one step that
writes nothing and moves no head, and afterwards the machine mirrors the chosen sub-machine through
a left/right embedding just as `seq` mirrors its second machine. It is an instance of a single
machine `armed d` parameterised by the dispatch decision `d`, and the arm-mirroring semiconjugation
is proved once, for all `d`.

Because at a starting `wordsCfg` the head of every work tape sits at the start of its word, tape
`i`'s symbol there is exactly `(ws i).head?`, so the dispatch reads precisely the predicate its
specification branches on.

## Main results

* `Turing.MultiTapeTM.exists_transformsTapes_branch`: from two transformations sharing a
  postcondition, a single machine that runs one or the other according to the symbol under tape
  `i`, with the time bound `max t₁ t₂ + 1` and the space bound `max s₁ s₂ + k`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {S₁ S₂ : Type*} {input : List Bool}

namespace Branch

/-- The shared branching machine, parameterised by a dispatch decision `d`. State `none` is a fresh
dispatch state: it reads the input symbol and the work-tape symbols and, in one step that writes
nothing and moves no head, jumps to the sub-machine's initial state chosen by `d`. Thereafter it
mirrors the chosen machine, its states carried by `Sum.inl`/`Sum.inr`. -/
private def armed (d : Option Bool → (Fin k → Option Bool) → S₁ ⊕ S₂)
    (tm₁ : MultiTapeTM k Bool S₁) (tm₂ : MultiTapeTM k Bool S₂) :
    MultiTapeTM k Bool (Option (S₁ ⊕ S₂)) where
  q₀ := none
  tr q inp work :=
    match q with
    | none =>
      { inputTape := 0
        workTapes := fun _ => (none, 0)
        output := none
        state := some (some (d inp work)) }
    | some (Sum.inl q₁) =>
      let a := tm₁.tr q₁ inp work
      { a with state := a.state.map (fun s => (some (Sum.inl s) : Option (S₁ ⊕ S₂))) }
    | some (Sum.inr q₂) =>
      let a := tm₂.tr q₂ inp work
      { a with state := a.state.map (fun s => (some (Sum.inr s) : Option (S₁ ⊕ S₂))) }

variable {d : Option Bool → (Fin k → Option Bool) → S₁ ⊕ S₂}
  {tm₁ : MultiTapeTM k Bool S₁} {tm₂ : MultiTapeTM k Bool S₂}

/-- A configuration of `tm₁`, embedded into the branching machine: a halted state stays halted, a
live state is carried by `Sum.inl`. -/
private def leftCfg (cfg : Cfg k Bool S₁ input) : Cfg k Bool (Option (S₁ ⊕ S₂)) input :=
  cfg.mapState (Option.map (fun s => (some (Sum.inl s) : Option (S₁ ⊕ S₂))))

/-- A configuration of `tm₂`, embedded into the branching machine. -/
private def rightCfg (cfg : Cfg k Bool S₂ input) : Cfg k Bool (Option (S₁ ⊕ S₂)) input :=
  cfg.mapState (Option.map (fun s => (some (Sum.inr s) : Option (S₁ ⊕ S₂))))

@[simp]
private lemma workTapePos_leftCfg (cfg : Cfg k Bool S₁ input) :
    (leftCfg (S₂ := S₂) cfg).workTapePos = cfg.workTapePos := rfl

@[simp]
private lemma workTapePos_rightCfg (cfg : Cfg k Bool S₂ input) :
    (rightCfg (S₁ := S₁) cfg).workTapePos = cfg.workTapePos := rfl

@[simp]
private lemma leftCfg_wordsCfg (q : Option S₁) (ws : Fin k → List Bool) (out : List Bool) :
    leftCfg (S₂ := S₂) (wordsCfg input q ws out) =
      wordsCfg input (q.map (fun s => (some (Sum.inl s) : Option (S₁ ⊕ S₂)))) ws out := rfl

@[simp]
private lemma rightCfg_wordsCfg (q : Option S₂) (ws : Fin k → List Bool) (out : List Bool) :
    rightCfg (S₁ := S₁) (wordsCfg input q ws out) =
      wordsCfg input (q.map (fun s => (some (Sum.inr s) : Option (S₁ ⊕ S₂)))) ws out := rfl

/-- On `tm₁`'s configurations, the branching machine mirrors `tm₁` step for step. This holds for
every dispatch `d`, since it only touches the live `Sum.inl` states, whose transition is
independent of `d`. -/
private lemma step_leftCfg (cfg : Cfg k Bool S₁ input) :
    (armed d tm₁ tm₂).step (leftCfg cfg) = leftCfg (tm₁.step cfg) := by
  rcases cfg with ⟨_ | q, inputPos, workTapes, workTapePos, output⟩ <;> rfl

/-- On `tm₂`'s configurations, the branching machine mirrors `tm₂` step for step. -/
private lemma step_rightCfg (cfg : Cfg k Bool S₂ input) :
    (armed d tm₁ tm₂).step (rightCfg cfg) = rightCfg (tm₂.step cfg) := by
  rcases cfg with ⟨_ | q, inputPos, workTapes, workTapePos, output⟩ <;> rfl

private lemma runFrom_leftCfg (cfg : Cfg k Bool S₁ input) (n : ℕ) :
    (armed d tm₁ tm₂).runFrom (leftCfg cfg) n = leftCfg (tm₁.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (step_leftCfg c).symm) n cfg).symm

private lemma runFrom_rightCfg (cfg : Cfg k Bool S₂ input) (n : ℕ) :
    (armed d tm₁ tm₂).runFrom (rightCfg cfg) n = rightCfg (tm₂.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (step_rightCfg c).symm) n cfg).symm

/-! ### The work-tape branch -/

/-- The branching machine. State `none` is a fresh dispatch state: it reads the symbol under tape
`i`'s head and, in one step that writes nothing and moves no head, jumps to `tm₁`'s initial state
(if the symbol is `some x`) or `tm₂`'s (otherwise). Thereafter it mirrors the chosen machine, its
states carried by `Sum.inl`/`Sum.inr`. -/
private abbrev branch (i : Fin k) (x : Bool) (tm₁ : MultiTapeTM k Bool S₁)
    (tm₂ : MultiTapeTM k Bool S₂) : MultiTapeTM k Bool (Option (S₁ ⊕ S₂)) :=
  armed (fun _inp work => if work i = some x then Sum.inl tm₁.q₀ else Sum.inr tm₂.q₀) tm₁ tm₂

variable {i : Fin k} {x : Bool}

/-- The dispatch step when the symbol under tape `i` is `some x`: it lands on `tm₁`'s initial
configuration, embedded on the left. -/
private lemma step_start_left (ws : Fin k → List Bool) (out : List Bool)
    (h : (ws i).head? = some x) :
    (branch i x tm₁ tm₂).step (wordsCfg input (some none) ws out) =
      leftCfg (S₂ := S₂) (wordsCfg input (some tm₁.q₀) ws out) := by
  rw [step_apply_of_state rfl]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [branch, armed, Cfg.workTapeSymbols, tapeOfList_zero, h, leftCfg, Cfg.mapState, wordsCfg,
      Action.apply, SignType.cast]

/-- The dispatch step when the symbol under tape `i` is not `some x`: it lands on `tm₂`'s initial
configuration, embedded on the right. -/
private lemma step_start_right (ws : Fin k → List Bool) (out : List Bool)
    (h : ¬ (ws i).head? = some x) :
    (branch i x tm₁ tm₂).step (wordsCfg input (some none) ws out) =
      rightCfg (S₁ := S₁) (wordsCfg input (some tm₂.q₀) ws out) := by
  rw [step_apply_of_state rfl]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [branch, armed, Cfg.workTapeSymbols, tapeOfList_zero, h, rightCfg, Cfg.mapState, wordsCfg,
      Action.apply, SignType.cast]

end Branch

open Branch in
/-- **Branching on a tape symbol.** Given two transformations that share a postcondition `Q`, a
single machine reads the symbol under the head of work tape `i`: if it is `some x` it performs the
first transformation, otherwise the second. The dispatch costs one step and, moving no head, at
most `k` cells, so the time bound is `max t₁ t₂ + 1` and the space bound `max s₁ s₂ + k`. -/
public theorem exists_transformsTapes_branch {J : Type*} {k : ℕ} (i : Fin k) (x : Bool)
    {State₁ State₂ : Type} [Finite State₁] [Finite State₂]
    {tm₁ : MultiTapeTM k Bool State₁} {tm₂ : MultiTapeTM k Bool State₂}
    {P₁ P₂ : J → (input : List Bool) → (Fin k → List Bool) → Prop}
    {Q : J → (input : List Bool) → (Fin k → List Bool) → (Fin k → List Bool) → Prop}
    {t₁ s₁ t₂ s₂ : J → ℕ}
    (h₁ : ∀ j, TransformsTapes tm₁ (P₁ j) (Q j) (t₁ j) (s₁ j))
    (h₂ : ∀ j, TransformsTapes tm₂ (P₂ j) (Q j) (t₂ j) (s₂ j)) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State), ∀ j : J,
      TransformsTapes tm
        (fun input ws => if (ws i).head? = some x then P₁ j input ws else P₂ j input ws)
        (Q j) (max (t₁ j) (t₂ j) + 1) (max (s₁ j) (s₂ j) + k) := by
  refine ⟨Option (State₁ ⊕ State₂), inferInstance, branch i x tm₁ tm₂, fun j input ws out hP => ?_⟩
  let start := wordsCfg (State := Option (State₁ ⊕ State₂)) input (some none) ws out
  -- Raise both arms to the same bounds before accounting for the dispatch.
  have hafter : ∃ ws',
      (branch i x tm₁ tm₂).runFrom ((branch i x tm₁ tm₂).step start) (max (t₁ j) (t₂ j)) =
        wordsCfg input none ws' out ∧ Q j input ws ws' ∧
      (branch i x tm₁ tm₂).spaceUsed ((branch i x tm₁ tm₂).step start)
        (max (t₁ j) (t₂ j)) ≤ max (s₁ j) (s₂ j) := by
    dsimp only [start]
    by_cases h : (ws i).head? = some x
    · obtain ⟨ws', hrun, hQ, hsp⟩ := (h₁ j).imp (fun _ _ => id) (fun _ _ _ _ => id)
        (Nat.le_max_left (t₁ j) (t₂ j)) (Nat.le_max_left (s₁ j) (s₂ j))
          input ws out (by simpa [h] using hP)
      rw [step_start_left ws out h]
      refine ⟨ws', ?_, hQ, ?_⟩
      · rw [runFrom_leftCfg, hrun]; rfl
      · exact (spaceUsed_eq_of_workTapePos _ _ _ fun m _ => by
          rw [runFrom_leftCfg, workTapePos_leftCfg]).le.trans hsp
    · obtain ⟨ws', hrun, hQ, hsp⟩ := (h₂ j).imp (fun _ _ => id) (fun _ _ _ _ => id)
        (Nat.le_max_right (t₁ j) (t₂ j)) (Nat.le_max_right (s₁ j) (s₂ j))
          input ws out (by simpa [h] using hP)
      rw [step_start_right ws out h]
      refine ⟨ws', ?_, hQ, ?_⟩
      · rw [runFrom_rightCfg, hrun]; rfl
      · exact (spaceUsed_eq_of_workTapePos _ _ _ fun m _ => by
          rw [runFrom_rightCfg, workTapePos_rightCfg]).le.trans hsp
  have hdispatch : (branch i x tm₁ tm₂).spaceUsed start 1 ≤ k := by
    refine spaceUsed_le_of_workTapePos_const start 1 fun m hm => ?_
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · rfl
    · change ((branch i x tm₁ tm₂).step start).workTapePos = start.workTapePos
      dsimp only [start]
      by_cases h : (ws i).head? = some x
      · rw [step_start_left ws out h]; rfl
      · rw [step_start_right ws out h]; rfl
  obtain ⟨ws', hrun, hQ, hsp⟩ := hafter
  refine ⟨ws', ?_, hQ, ?_⟩
  · change (branch i x tm₁ tm₂).runFrom start (max (t₁ j) (t₂ j) + 1) = _
    simpa only [runFrom, Function.iterate_succ_apply] using hrun
  · change (branch i x tm₁ tm₂).spaceUsed start (max (t₁ j) (t₂ j) + 1) ≤ _
    rw [Nat.add_comm]
    exact (spaceUsed_add_le start 1 _).trans
      (by simpa only [runFrom, Function.iterate_one, Nat.add_comm] using
        Nat.add_le_add hdispatch hsp)

end Turing.MultiTapeTM
