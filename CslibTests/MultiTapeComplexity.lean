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
private lemma constant_computable :
    ComputableInTimeAndSpace (fun _ : Bool => true) bit bit
      (fun b => if b then 1 else 2) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, finish 0 true, ?_⟩
  intro b
  refine ⟨1, ?_, ?_, ?_, by simp⟩
  · cases b <;> decide
  · rw [runFrom, Function.iterate_one, step_of_state rfl]
    simp [finish, Turing.Cfg.Halted]
  · rw [runFrom, Function.iterate_one, step_of_state rfl]
    simp [finish]; rfl

-- A theorem about nondeterministic steps applies directly to a deterministic machine.
example {tm : Turing.MultiTapeTM k Symbol State} {input : List Symbol}
    {c c' : Turing.Cfg k Symbol State input} (h : c.Halted) :
    tm.Step c c' ↔ c' = c :=
  Turing.MultiTapeNTM.step_of_halt h

-- Deterministic function bounds can be weakened for the witnessing machine.
example {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {t s t' s' : α → ℕ} (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

-- A deterministic decider is already a nondeterministic decider.
example {α : Type*} {L : Set α} {enc : α ↪ List Bool} {t s : α → ℕ}
    (h : DecidableInTimeAndSpace L enc t s) :
    Turing.MultiTapeNTM.DecidableInTimeAndSpace L enc t s := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm.toMultiTapeNTM, htm⟩

-- Deterministic decision agrees with computing the Boolean indicator.
example {α : Type*} {L : Set α} {enc : α ↪ List Bool} {t s : α → ℕ}
    {tm : Turing.MultiTapeTM k Bool State}
    (h : tm.ComputesFunInTimeAndSpace enc bit (indicator L) t s) :
    tm.DecidesInTimeAndSpace L enc t s :=
  decidesInTimeAndSpace_iff.mpr h

open Turing Turing.MultiTapeNTM

private def stop (b : Bool) : Action 0 Bool Unit := ⟨0, Fin.elim0, some b, none⟩

private def chooseBit : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := ∃ b, action = stop b

private def outputPath (input : List Bool) (b : Bool) : chooseBit.ComputationPath input where
  toRunPath := (RelSeries.singleton _ (chooseBit.initCfg input)).snoc
    ((stop b).apply (chooseBit.initCfg input)) ⟨stop b, ⟨b, rfl⟩, rfl⟩
  head_eq := by simp

private lemma chooseBit_path {input : List Bool} (p : chooseBit.ComputationPath input)
    (hp : 0 < p.length) :
    p.last.Halted ∧ (p.last.output = [true] ∨ p.last.output = [false]) := by
  let i : Fin p.length := ⟨0, hp⟩
  have hstep := p.step i
  change chooseBit.Step p.head (p.toRunPath i.succ) at hstep
  rw [p.head_eq] at hstep
  obtain ⟨action, ⟨b, rfl⟩, hc⟩ := hstep
  have hh : (p.toRunPath i.succ).Halted := by rw [hc]; rfl
  rw [RunPath.last_eq_of_halted p.toRunPath i.succ hh, hc]
  cases b <;> simp [stop, Action.apply, Cfg.Halted]

private lemma chooseBit_time (input : List Bool) : chooseBit.RunsInTime input 1 := by
  intro p hp _ _
  exact (chooseBit_path p hp).1

-- The same machine decides the full language: rejecting branches on a member are allowed.
example : chooseBit.DecidesInTimeAndSpace Set.univ bit (fun _ ↦ 1) (fun _ ↦ 0) := by
  intro a
  refine ⟨⟨fun _ ↦ Set.mem_univ _, fun _ ↦ ⟨outputPath _ true, rfl, rfl⟩⟩,
    chooseBit_time _, ?_, fun p hp ↦ ?_⟩
  · intro p
    simp [ComputationPath.space, RunPath.space]
  · by_cases hlen : 0 < p.length
    · exact (chooseBit_path p hlen).2
    · have heq : Fin.last p.length = 0 := Fin.ext (by simp; omega)
      have hlast : p.last = p.head := congrArg p.toFun heq
      rw [hlast, p.head_eq] at hp
      cases hp

-- Halting padding does not violate the time bound.
example : chooseBit.RunsInTime [] 100 := (chooseBit_time []).mono (by decide)

-- The transition into a halting configuration still costs one step.
example : ¬chooseBit.RunsInTime [] 0 := by
  intro h
  let p : chooseBit.ComputationPath [] := ⟨RelSeries.singleton _ (chooseBit.initCfg []), rfl⟩
  have hh := h p le_rfl ((stop true).apply p.last) ⟨stop true, ⟨true, rfl⟩, rfl⟩
  cases hh

private def blocked : MultiTapeNTM 0 Bool Unit := ⟨(), fun _ _ _ _ ↦ False⟩

private lemma blocked_path {input : List Bool} (p : blocked.ComputationPath input) :
    p.last = blocked.initCfg input := by
  by_cases hp : 0 < p.length
  · have hstep := p.step ⟨0, hp⟩
    change blocked.Step p.head _ at hstep
    rw [p.head_eq] at hstep
    obtain ⟨_, hf, _⟩ := hstep
    exact hf.elim
  · have heq : Fin.last p.length = 0 := Fin.ext (by simp; omega)
    exact (congrArg p.toFun heq).trans p.head_eq

-- A branch with no transition rejects immediately, without requiring a successor.
example : blocked.DecidesInTimeAndSpace ∅ bit (fun _ ↦ 0) (fun _ ↦ 0) := by
  intro a
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨p, hp, _⟩
      rw [blocked_path p] at hp
      cases hp
    · simp
  · intro p _ c hc
    rw [blocked_path p] at hc
    obtain ⟨_, hf, _⟩ := hc
    exact hf.elim
  · intro p
    simp [ComputationPath.space, RunPath.space]
  · intro p hp
    rw [blocked_path p] at hp
    cases hp

private def mayLoop : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := action = stop true ∨ action = ⟨0, Fin.elim0, none, some ()⟩

-- One short accepting branch does not bound a second branch that can keep running.
example : mayLoop.Accepts [] ∧ ¬mayLoop.RunsInTime [] 1 := by
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
    have hh := h p le_rfl (action.apply p.last) ⟨action, Or.inr rfl, rfl⟩
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

-- A short accepting path does not excuse extra space used on a rejecting branch.
example : mayUseSpace.Accepts [] ∧ ¬mayUseSpace.UsesSpace [] 1 := by
  refine ⟨⟨visitPath true, rfl, rfl⟩, fun hs ↦ ?_⟩
  have hspace : (visitPath false).space = 2 := by decide
  have := hs (visitPath false)
  omega

end CslibTests.MultiTapeComplexity
