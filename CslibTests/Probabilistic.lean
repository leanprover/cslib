/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Crypto.Game
import Cslib.Languages.Probabilistic.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn

/-! Examples of typed, adaptive, and stateful probabilistic programs, and Boolean games. -/

namespace CslibTests.Probabilistic

open Cslib Cslib.Crypto

universe u

private def adaptive (input : ℕ) : OracleComp ℕ (fun _ => ℕ) ℕ := do
  let answer ← OracleComp.query input
  OracleComp.query answer

example (f : ℕ → ℕ) (input : ℕ) :
    OracleComp.eval (fun query => PMF.pure (f query)) (adaptive input) =
      PMF.pure (f (f input)) := by
  simp [adaptive]

private abbrev Reply : Bool → Type
  | false => Bool
  | true => ℕ

private def typed : OracleComp Bool Reply ℕ := do
  let flag ← OracleComp.query false
  if flag then OracleComp.query true else pure 0

private noncomputable def typedOracle : (flag : Bool) → PMF (Reply flag)
  | false => PMF.pure true
  | true => PMF.pure 7

example : OracleComp.eval typedOracle typed = PMF.pure 7 := by
  simp [typed, typedOracle]

private noncomputable def counter (_ : Unit) : StateT ℕ PMF ℕ :=
  fun state => PMF.pure (state, state + 1)

private def twice : OracleComp Unit (fun _ => ℕ) (ℕ × ℕ) := do
  let first ← OracleComp.query ()
  let second ← OracleComp.query ()
  return (first, second)

-- The two calls share private state; the result retains their order.
example : OracleComp.runState counter twice 10 = PMF.pure ((10, 11), 12) := by
  simp [twice, counter, PMF.pure_map]

private def doubleQuery (query : Unit) : OracleComp Unit (fun _ => ℕ) ℕ := do
  let _ ← OracleComp.query query
  OracleComp.query query

-- Discarding a reply still changes state, including inside a substituted handler.
example : OracleComp.runState counter (OracleComp.simulate doubleQuery twice) 10 =
    PMF.pure ((11, 13), 14) := by
  simp [twice, doubleQuery, counter, PMF.pure_map]

private noncomputable def remember {α : Type u} (value : α) : StateT (Option α) PMF α
  | none => PMF.pure (value, some value)
  | some previous => PMF.pure (previous, some previous)

private def sampleAndRecall {α : Type u} (p : PMF α) : OracleComp α (fun _ => α) (α × α) := do
  let first ← OracleComp.sample p
  let a ← OracleComp.query first
  let second ← OracleComp.sample p
  let b ← OracleComp.query second
  return (a, b)

-- Sampling between calls preserves the stored value and the correlation between replies.
-- The example also exercises evaluation at an arbitrary universe.
example {α : Type u} (p : PMF α) :
    OracleComp.runState remember (sampleAndRecall p) none =
      p.map (fun a => ((a, a), some a)) := by
  simp [sampleAndRecall, remember, PMF.map, Function.comp_def]

example : Game.winProbability
    (ProbComp.eval (OracleComp.uniform Bool : ProbComp Bool)) = 1 / 2 := by
  simp [OracleComp.uniform, Game.winProbability, Probability.PMF.uniformOfFintype_apply]

private abbrev Word := List Bool

-- A prospective inversion game needs only the frontend and finite uniform sampling.
private noncomputable def inversionGame (f : Word → Word)
    (adversary : ℕ → Word → ProbComp Word) (n : ℕ) : ProbComp Bool := do
  let bits ← OracleComp.uniform (Fin n → Bool)
  let input := List.ofFn bits
  let candidate ← adversary n (f input)
  return f candidate == f input

-- Inversion accepts any preimage, including one with a different length.
example (n : ℕ) : Game.winProbability
    (ProbComp.eval (inversionGame (fun _ => [true]) (fun _ _ => pure []) n)) = 1 := by
  simp [inversionGame, Game.winProbability, PMF.map, Function.comp_def]

end CslibTests.Probabilistic
