/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Semantics.LTS.HasTau
public import Mathlib.Data.List.ReduceOption

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

instance : DecidableEqTau (Option α) := fun a => Option.decidableEqNone a

/-- The `ε`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `ε`-transitions. We use `LTS.τClosure` since `ε` (`Option.none`) is an instance
of `HasTau.τ`. -/
abbrev εNA.εClosure (a : εNA State Symbol) (S : Set State) := a.τClosure S

namespace εNA

theorem filter_ne_τ_eq_map_some {μs : List (Option Symbol)} :
    μs.filter (· ≠ HasTau.τ) = μs.reduceOption.map some := by
  induction μs with
  | nil => rfl
  | cons μ μs ih => cases μ <;> simp_all [HasTau.τ, List.reduceOption]

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
  have hvis : ∀ μ ∈ xs.map some, μ ≠ (HasTau.τ : Option Symbol) := by
    intro μ hμ
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hμ
    exact Option.some_ne_none x
  rw [mem_language]
  exact exists_congr fun _ => and_congr_right fun _ => exists_congr fun _ =>
    and_congr_right fun _ => (LTS.sMTr_iff_exists_mTr_filter hvis).trans
      (exists_congr fun _ => and_congr_left' <| by
        rw [filter_ne_τ_eq_map_some, List.map_inj_right (fun _ _ => Option.some_inj.mp)])

end FinAcc

end εNA

end Cslib.Automata
