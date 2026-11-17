/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Foundations.Semantics.LTS.Basic

/-! # Multistack Pushdown Automata

A multistack pushdown automaton (MPDA) with `n` stacks is a finite control equipped with `n`
stacks over a common stack alphabet. Every transition carries an input symbol and performs at most
one stack operation: it either leaves all stacks untouched (`nop`), pushes a symbol onto one stack,
or pops a given symbol from the top of one stack.

Following the conventions of `NA`, an `MPDA` extends an `LTS` over its control states, whose labels
pair an input symbol with a stack operation. We do not impose any finiteness assumption. The
configuration semantics is itself an `LTS` (`MPDA.configLTS`), so that the generic `LTS` API for
multistep transitions applies directly to runs of the automaton.

A word is accepted when some run starts in an initial state with all stacks empty and ends in an
accepting state with all stacks empty, as in [AkshayGastinKrishnaRoychowdhury2020].

Silent moves are not built in. They can be obtained by instantiating `Symbol` with `Option Σ`.

## Main definitions

- `MPDA.Op`: the stack operations of an MPDA.
- `MPDA`: multistack pushdown automata.
- `MPDA.Config`: configurations, consisting of a control state and the contents of all stacks.
- `MPDA.configLTS`: the transition system on configurations.
- An `Acceptor` instance for acceptance by final state and empty stacks.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

@[expose] public section

namespace Cslib.Automata

/-- The stack operations of a multistack pushdown automaton with `n` stacks over the stack
alphabet `Γ`. -/
inductive MPDA.Op (n : ℕ) (Γ : Type*) where
  /-- Leave all stacks unchanged. -/
  | nop
  /-- Push `γ` onto stack `i`. -/
  | push (i : Fin n) (γ : Γ)
  /-- Pop `γ` from the top of stack `i`. -/
  | pop (i : Fin n) (γ : Γ)
  deriving DecidableEq

/-- A multistack pushdown automaton with `n` stacks, control states `State`, input alphabet `Symbol`
and stack alphabet `Γ`. Its transition relation is an `LTS` over control states, whose labels pair
an input symbol with a stack operation. -/
structure MPDA (n : ℕ) (State Symbol Γ : Type*) extends LTS State (Symbol × MPDA.Op n Γ) where
  /-- The set of initial states. -/
  start : Set State
  /-- The set of accepting states. -/
  accept : Set State

namespace MPDA

variable {n : ℕ} {State Symbol Γ : Type*}

/-- The contents of `n` stacks. The head of each list is the top of the stack. -/
abbrev Stacks (n : ℕ) (Γ : Type*) := Fin n → List Γ

/-- All stacks are empty. -/
def Stacks.empty : Stacks n Γ := fun _ => []

/-- `op.Apply σ σ'` holds when performing `op` on the stacks `σ` yields `σ'`. A pop of `γ` from
stack `i` is enabled only when `γ` is on top of stack `i`. -/
def Op.Apply : Op n Γ → Stacks n Γ → Stacks n Γ → Prop
  | .nop, σ, σ' => σ' = σ
  | .push i γ, σ, σ' => σ' = Function.update σ i (γ :: σ i)
  | .pop i γ, σ, σ' => σ = Function.update σ' i (γ :: σ' i)

@[simp]
theorem Op.apply_nop {σ σ' : Stacks n Γ} : (Op.nop : Op n Γ).Apply σ σ' ↔ σ' = σ := Iff.rfl

@[simp]
theorem Op.apply_push {i : Fin n} {γ : Γ} {σ σ' : Stacks n Γ} :
    (Op.push i γ).Apply σ σ' ↔ σ' = Function.update σ i (γ :: σ i) := Iff.rfl

@[simp]
theorem Op.apply_pop {i : Fin n} {γ : Γ} {σ σ' : Stacks n Γ} :
    (Op.pop i γ).Apply σ σ' ↔ σ = Function.update σ' i (γ :: σ' i) := Iff.rfl

/-- Popping `γ` from stack `i` undoes pushing `γ` onto stack `i`. -/
theorem Op.apply_pop_iff_apply_push {i : Fin n} {γ : Γ} {σ σ' : Stacks n Γ} :
    (Op.pop i γ).Apply σ σ' ↔ (Op.push i γ).Apply σ' σ := Iff.rfl

/-- Stack operations are deterministic. -/
theorem Op.Apply.eq {op : Op n Γ} {σ σ₁ σ₂ : Stacks n Γ}
    (h₁ : op.Apply σ σ₁) (h₂ : op.Apply σ σ₂) : σ₁ = σ₂ := by
  cases op with
  | nop => exact h₁.trans h₂.symm
  | push i γ => exact h₁.trans h₂.symm
  | pop i γ =>
    funext j
    by_cases hj : j = i
    · subst hj
      have := congrFun (h₁.symm.trans h₂) j
      simp only [Function.update_self, List.cons.injEq, true_and] at this
      exact this
    · have := congrFun (h₁.symm.trans h₂) j
      simp only [ne_eq, hj, not_false_eq_true, Function.update_of_ne] at this
      exact this

/-- A configuration of an MPDA: a control state and the contents of all stacks. -/
@[ext]
structure Config (n : ℕ) (State Γ : Type*) where
  /-- The control state. -/
  state : State
  /-- The contents of the stacks. -/
  contents : Stacks n Γ

/-- The transition system on configurations of an MPDA. A configuration `c` moves to `c'` with
label `μ` when the control moves along `μ` and the stack operation of `μ` turns the stacks of `c`
into those of `c'`. -/
def configLTS (M : MPDA n State Symbol Γ) : LTS (Config n State Γ) (Symbol × Op n Γ) where
  Tr c μ c' := M.Tr c.state μ c'.state ∧ μ.2.Apply c.contents c'.contents

@[simp]
theorem configLTS_tr {M : MPDA n State Symbol Γ} {c c' : Config n State Γ}
    {μ : Symbol × Op n Γ} :
    M.configLTS.Tr c μ c' ↔ M.Tr c.state μ c'.state ∧ μ.2.Apply c.contents c'.contents := Iff.rfl

/-- Every run on configurations projects to a run of the control. -/
theorem configLTS_mTr_state {M : MPDA n State Symbol Γ} {c c' : Config n State Γ}
    {μs : List (Symbol × Op n Γ)} (h : M.configLTS.MTr c μs c') : M.MTr c.state μs c'.state := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih => exact .stepL htr.1 ih

/-- An MPDA accepts a word if it has a run labelled by that word that starts in an initial state
with all stacks empty and ends in an accepting state with all stacks empty. -/
@[simp, scoped grind =]
instance : Acceptor (MPDA n State Symbol Γ) Symbol where
  Accepts M xs := ∃ s ∈ M.start, ∃ s' ∈ M.accept, ∃ μs : List (Symbol × Op n Γ),
    μs.map Prod.fst = xs ∧ M.configLTS.MTr ⟨s, Stacks.empty⟩ μs ⟨s', Stacks.empty⟩

end MPDA

end Cslib.Automata
