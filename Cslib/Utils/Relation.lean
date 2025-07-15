/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Chris Henson
-/
import Mathlib.Logic.Relation

universe u

variable {α : Type u} {R R' : α → α → Prop}

/-- A relation has the diamond property when all reductions with a common origin are joinable -/
abbrev Diamond (R : α → α → Prop) := ∀ {A B C : α}, R A B → R A C → (∃ D, R B D ∧ R C D)

/-- A relation is confluent when its reflexive transitive closure has the diamond property. -/
abbrev Confluence (R : α → α → Prop) := Diamond (Relation.ReflTransGen R)

/-- Extending a multistep reduction by a single step preserves multi-joinability. -/
lemma Relation.ReflTransGen.diamond_extend (h : Diamond R) : 
  Relation.ReflTransGen R A B → 
  R A C → 
  ∃ D, Relation.ReflTransGen R B D ∧ Relation.ReflTransGen R C D := by
  intros AB _
  revert C
  induction AB using Relation.ReflTransGen.head_induction_on <;> intros C AC
  case refl => exact ⟨C, ⟨single AC, by rfl⟩⟩
  case head A'_C' _ ih =>
    obtain ⟨D, ⟨CD, C'_D⟩⟩ := h AC A'_C'
    obtain ⟨D', ⟨B_D', D_D'⟩⟩ := ih C'_D
    exact ⟨D', ⟨B_D', head CD D_D'⟩⟩

/-- The dismond property implies confluence. -/
theorem Relation.ReflTransGen.diamond (h : Diamond R) : Confluence R := by
  intros A B C AB BC
  revert C
  induction AB using Relation.ReflTransGen.head_induction_on <;> intros C BC
  case refl => exists C
  case head _ _ A'_C' _ ih =>
    obtain ⟨D, ⟨CD, C'_D⟩⟩ := diamond_extend h BC A'_C'
    obtain ⟨D', ⟨B_D', D_D'⟩⟩ := ih C'_D
    exact ⟨D', ⟨B_D', trans CD D_D'⟩⟩

/-- Equivalence of relations preserves the diamond property. -/
theorem diamond_bisim (sim : ∀ {M N : α}, R M N ↔ R' M N) (h : Diamond R) : Diamond R' := by
  intros L M₁ M₂ L_M₁ L_M₂
  have ⟨N, ⟨M₁_chain_N, M₂_chain_N⟩⟩ := h (sim.mpr L_M₁) (sim.mpr L_M₂)
  exact ⟨N, ⟨sim.mp M₁_chain_N, sim.mp M₂_chain_N⟩⟩
