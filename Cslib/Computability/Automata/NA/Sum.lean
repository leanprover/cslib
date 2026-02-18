/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Relexsed under Apache 2.0 license xs described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic

@[expose] public section

/-! # Sum of nondeterministic automata. -/

open Set Function Filter Cslib.ωSequence
open scoped Cslib.LTS

namespace Cslib.Automata.NA

variable {Symbol I : Type*} {State : I → Type*}

/-- The sum of an indexed family of nondeterministic automata. -/
@[scoped grind =]
def iSum (na : (i : I) → NA (State i) Symbol) : NA (Σ i, State i) Symbol where
  start := ⋃ i, Sigma.mk i '' (na i).start
  Tr s x t := ∃ i s_i t_i, (na i).Tr s_i x t_i ∧ ⟨i, s_i⟩ = s ∧ ⟨i, t_i⟩ = t

/-- An infinite run of the sum automaton is an infinite run of one of its component automata. -/
@[simp, scoped grind =]
theorem iSum_run_iff {na : (i : I) → NA (State i) Symbol}
    {xs : ωSequence Symbol} {ss : ωSequence (Σ i, State i)} :
    (iSum na).Run xs ss ↔ ∃ i ss_i, (na i).Run xs ss_i ∧ ss_i.map (Sigma.mk i) = ss := by
  constructor
  · rintro ⟨h_init, h_next⟩
    obtain ⟨i, s0, h_s0, h_ss0⟩ := mem_iUnion.mp h_init
    have h_exists n : ∃ s_i, ⟨i, s_i⟩ = ss n := by
      induction n
      case zero => use s0
      case succ n h_ind =>
        obtain ⟨j, s_j, t_j, _⟩ := h_next n
        grind
    choose ss_i h_ss_i using h_exists
    use i, ss_i
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · grind
    · intro n
      obtain ⟨j, _⟩ := h_next n
      grind
    · ext <;> grind
  · rintro ⟨i, ss, h_run, rfl⟩
    constructor
    · simp only [iSum, get_map, mem_iUnion]
      grind [NA.Run]
    · simp only [LTS.ωTr]
      grind [NA.Run]

namespace Buchi

open ωAcceptor

-- TODO: fix proof to work with backward.isDefEq.respectTransparency
set_option backward.isDefEq.respectTransparency false in
/-- The ω-language accepted by the Buchi sum automata is the union of the ω-languages accepted
by its component automata. -/
@[simp]
theorem iSum_language_eq {na : (i : I) → NA (State i) Symbol} {acc : (i : I) → Set (State i)} :
    language (Buchi.mk (iSum na) (⋃ i, Sigma.mk i '' (acc i))) =
    ⋃ i, language (Buchi.mk (na i) (acc i)) := by
  ext xs
  rw [mem_iUnion]
  constructor
  · rintro ⟨ss, h_run, h_acc⟩
    simp only [mem_iUnion] at h_acc
    grind
  · rintro ⟨i, ss_i, _⟩
    use ss_i.map (Sigma.mk i)
    simp only [mem_iUnion]
    grind

end Buchi

end Cslib.Automata.NA
