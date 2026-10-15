/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

namespace CslibTests.MultiTapeComplexity

open Turing.MultiTapeTM

private def finish (move : SignType) (symbol : Bool) : Turing.MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨move, Fin.elim0, some symbol, none⟩

private def bit : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; simpa using h⟩

-- Bounds can differ for inputs of the same encoded length.
private lemma constant_computable (symbol : Bool) :
    ComputableInTimeAndSpace (fun _ : Bool => symbol) bit bit
      (fun b => if b then 1 else 2) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, finish 0 symbol, fun b ↦ ?_⟩
  have h : ((finish 0 symbol).runFrom ((finish 0 symbol).initCfg (bit b)) 1).Halted ∧
      ((finish 0 symbol).runFrom ((finish 0 symbol).initCfg (bit b)) 1).output = bit symbol := by
    rw [runFrom, Function.iterate_one, step_of_state rfl]
    simp [finish, Turing.Cfg.Halted]; rfl
  exact ⟨⟨1, h⟩, (runsInTime_of_halted h.1).mono (by cases b <;> decide), by simp⟩

-- A theorem about nondeterministic steps applies directly to a deterministic machine.
example {tm : Turing.MultiTapeTM k Symbol State} {input : List Symbol}
    {c c' : Turing.Cfg k Symbol State input} (h : c.Halted) :
    tm.Step c c' ↔ c' = c :=
  Turing.MultiTapeNTM.step_of_halt h

-- Deterministic function bounds can be weakened for the witnessing machine.
example {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {t s t' s' : α → ℕ} (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' :=
  h.mono ht hs

-- Deterministic function computation satisfies the shared resource bounds.
example {α β : Type*} {tm : Turing.MultiTapeTM k Symbol State}
    {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s : α → ℕ}
    (h : tm.ComputesFunInTimeAndSpace encIn encOut f t s) (a : α) :
    tm.RunsInTime (encIn a) (t a) ∧ tm.RunsInSpace (encIn a) (s a) :=
  (h a).2

-- Deciding the full and empty languages requires returning true and false, respectively.
example : DecidableInTimeAndSpace (Set.univ : Set Bool) bit
    (fun b ↦ if b then 1 else 2) (fun _ ↦ 0) := by
  unfold DecidableInTimeAndSpace indicator
  simpa [bit] using constant_computable true

example : DecidableInTimeAndSpace (∅ : Set Bool) bit
    (fun b ↦ if b then 1 else 2) (fun _ ↦ 0) := by
  unfold DecidableInTimeAndSpace indicator
  simpa [bit] using constant_computable false

open Turing Turing.MultiTapeNTM

private def stop (b : Bool) : Action 0 Bool Unit := ⟨0, Fin.elim0, some b, none⟩

private def chooseBit : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := ∃ b, action = stop b

private lemma chooseBit_time (input : List Bool) : chooseBit.RunsInTime input 1 := by
  intro p hp
  let i : Fin p.length := ⟨0, hp⟩
  have hstep := p.step i
  change chooseBit.Step p.head (p.toRunPath i.succ) at hstep
  rw [p.head_eq] at hstep
  obtain ⟨action, ⟨b, rfl⟩, hc⟩ := hstep
  have hh : (p.toRunPath i.succ).Halted := by rw [hc]; rfl
  rw [RunPath.last_eq_of_halted p.toRunPath i.succ hh]
  exact hh

-- Halting padding does not violate the time bound.
example : chooseBit.RunsInTime [] 100 := (chooseBit_time []).mono (by decide)

-- The transition into a halting configuration still costs one step.
example : ¬chooseBit.RunsInTime [] 0 := by
  intro h
  let p : chooseBit.ComputationPath [] := ⟨RelSeries.singleton _ (chooseBit.initCfg []), rfl⟩
  have hh := h p le_rfl
  cases hh

private def blocked : MultiTapeNTM 0 Bool Unit := ⟨(), fun _ _ _ _ ↦ False⟩

-- A stuck initial configuration fails the zero-step bound, despite having no successor.
example : ¬blocked.RunsInTime [] 0 := by
  intro h
  let p : blocked.ComputationPath [] := ⟨RelSeries.singleton _ (blocked.initCfg []), rfl⟩
  have hh := h p le_rfl
  cases hh

-- All stuck paths have zero steps, so the one-step bound holds.
example (input : List Bool) : blocked.RunsInTime input 1 := by
  intro p hp
  have hstep := p.step ⟨0, hp⟩
  change blocked.Step p.head _ at hstep
  rw [p.head_eq] at hstep
  obtain ⟨_, hf, _⟩ := hstep
  exact hf.elim

private def mayLoop : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := action = stop true ∨ action = ⟨0, Fin.elim0, none, some ()⟩

-- One short halting branch does not bound a second branch that can keep running.
example : (∃ p : mayLoop.ComputationPath [], p.time = 1 ∧ p.last.Halted) ∧
    ¬mayLoop.RunsInTime [] 1 := by
  constructor
  · let p : mayLoop.ComputationPath [] :=
      ⟨(RelSeries.singleton _ (mayLoop.initCfg [])).snoc
        ((stop true).apply (mayLoop.initCfg [])) ⟨stop true, Or.inl rfl, rfl⟩, by simp⟩
    exact ⟨p, rfl, rfl⟩
  · intro h
    let action : Action 0 Bool Unit := ⟨0, Fin.elim0, none, some ()⟩
    let p : mayLoop.ComputationPath [] :=
      ⟨(RelSeries.singleton _ (mayLoop.initCfg [])).snoc
        (action.apply (mayLoop.initCfg [])) ⟨action, Or.inr rfl, rfl⟩, by simp⟩
    have hh := h p le_rfl
    cases hh

private def visit (b : Bool) : Action 1 Bool Unit :=
  ⟨0, fun _ ↦ (none, if b then 0 else 1), some b, none⟩

private def mayUseSpace : MultiTapeNTM 1 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := ∃ b, action = visit b

private def visitPath (b : Bool) : mayUseSpace.ComputationPath [] where
  toRunPath := (RelSeries.singleton _ (mayUseSpace.initCfg [])).snoc
    ((visit b).apply (mayUseSpace.initCfg [])) ⟨visit b, ⟨b, rfl⟩, rfl⟩
  head_eq := by simp

-- A space bound on one path does not bound another.
example : (visitPath true).space = 1 ∧ ¬mayUseSpace.RunsInSpace [] 1 := by
  refine ⟨by decide, fun hs ↦ ?_⟩
  have hspace : (visitPath false).space = 2 := by decide
  have := hs (visitPath false)
  omega

end CslibTests.MultiTapeComplexity
