/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau
import Mathlib.Data.List.ReduceOption

/-! # Nondeterministic automata with ε-transitions. -/

@[expose] public section

namespace Cslib.Automata

/-- A nondeterministic finite automaton with ε-transitions (`εNA`) is an `NA` with an `Option`
symbol type. The special symbol ε is represented by the `Option.none` case.

Internally, ε (`Option.none`) is treated as the `τ` label of the underlying transition system,
allowing for reusing the definitions and results on saturated transitions of `LTS` to deal with
ε-closure. -/
structure εNA (State Symbol : Type*) extends NA State (Option Symbol)

variable {State Symbol : Type*}

@[local grind =]
instance : HasTau (Option α) := ⟨.none⟩

/-- The `ε`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `ε`-transitions. We use `LTS.τClosure` since `ε` (`Option.none`) is an instance
of `HasTau.τ`. -/
abbrev εNA.εClosure (a : εNA State Symbol) (S : Set State) := a.τClosure S

namespace εNA

/-- A saturated `ε`-transition is a run along a list of `ε`s. -/
theorem τSTr_iff_exists_mTr_replicate {a : εNA State Symbol} {s t : State} :
    a.τSTr s t ↔ ∃ n, a.MTr s (List.replicate n none) t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, .refl⟩
    | tail _ htr ih =>
      obtain ⟨n, hmtr⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [List.replicate_succ']
      exact hmtr.stepR _ htr
  · rintro ⟨n, hmtr⟩
    induction n generalizing s with
    | zero =>
      obtain rfl := hmtr.nil_eq _
      exact .refl
    | succ n ih =>
      obtain ⟨s', htr, hmtr'⟩ := LTS.MTr.cons_iff.mp hmtr
      exact .head htr (ih hmtr')

/-- A saturated run of an `εNA` along `xs.map some` is a run along a list of optional symbols
which becomes `xs` once its `ε`s are dropped. -/
theorem sMTr_map_some_iff {a : εNA State Symbol} {s t : State} {xs : List Symbol} :
    a.SMTr s (xs.map some) t ↔
      ∃ μs : List (Option Symbol), μs.reduceOption = xs ∧ a.MTr s μs t := by
  constructor
  · intro h
    induction xs generalizing s with
    | nil =>
      cases h with
      | τ hstr =>
        obtain ⟨n, hmtr⟩ := τSTr_iff_exists_mTr_replicate.mp ((LTS.sTr_τSTr_iff _).mp hstr)
        exact ⟨_, List.reduceOption_replicate_none, hmtr⟩
    | cons x xs ih =>
      cases h with
      | stepL hstr hrest =>
        obtain ⟨μs, hμs, hmtr⟩ := ih hrest
        cases hstr with
        | tr h₁ htr h₂ =>
          obtain ⟨n₁, hmtr₁⟩ := τSTr_iff_exists_mTr_replicate.mp h₁
          obtain ⟨n₂, hmtr₂⟩ := τSTr_iff_exists_mTr_replicate.mp h₂
          refine ⟨List.replicate n₁ none ++ some x :: (List.replicate n₂ none ++ μs), ?_, ?_⟩
          · simp [List.reduceOption_append, hμs]
          · exact hmtr₁.comp _ (.stepL htr (hmtr₂.comp _ hmtr))
  · rintro ⟨μs, rfl, hmtr⟩
    induction hmtr with
    | refl => exact LTS.SMTr.refl _ _
    | @stepL _ μ _ _ _ htr _ ih =>
      cases μ with
      | none => exact LTS.SMTr.comp (.τ (.single htr)) ih
      | some x => exact .stepL (.single htr) ih

/-- The finite-word acceptance condition of an `εNA` is a set of accepting states. -/
structure FinAcc (State Symbol : Type*) extends εNA State Symbol where
  /-- The set of accepting states. -/
  accept : Set State

namespace FinAcc

/-- An `εNA.FinAcc` accepts a string if there is a saturated multistep accepting derivative with
that trace from the start state. -/
@[scoped grind =]
instance : Acceptor (FinAcc State Symbol) Symbol where
  Accepts a xs := ∃ s ∈ a.start, ∃ s' ∈ a.accept, a.SMTr s (xs.map some) s'

open Acceptor in
/-- A word is accepted if and only if a plain run from an initial to an accepting state reads it
once its `ε`s are dropped. -/
theorem mem_language_iff {a : FinAcc State Symbol} {xs : List Symbol} :
    xs ∈ language a ↔ ∃ s ∈ a.start, ∃ t ∈ a.accept,
      ∃ μs : List (Option Symbol), μs.reduceOption = xs ∧ a.MTr s μs t := by
  rw [mem_language]
  exact exists_congr fun _ => and_congr_right fun _ => exists_congr fun _ =>
    and_congr_right fun _ => sMTr_map_some_iff

end FinAcc

end εNA

end Cslib.Automata
