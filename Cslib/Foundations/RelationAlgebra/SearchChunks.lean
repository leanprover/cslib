/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.SearchProblem

/-!
# Independently checked count-certificate chunks

A large certificate can be split into declarations with a bounded amount of computation in each
proof. A reference carries an already proved count and checks exact equality of the search state
before reusing it. Earlier proofs are used as theorems rather than reducing their certificates
again. Neither the choice of chunk boundaries nor the reference table is trusted.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Counting

variable {State : Type*}

/-- Numeric reference data, independent of any proof of its count. -/
structure CountData (State : Type*) where
  /-- The state whose count is stored. -/
  state : State
  /-- The stored number of models. -/
  result : ℕ

/-- Transport a known count through equality of numeric reference entries without unfolding it. -/
theorem CountData.count_eq_of_some_eq {count : State → ℕ}
    (state : State) (result : ℕ) (hcount : count state = result) {data : CountData State}
    (h : some (⟨state, result⟩ : CountData State) = some data) :
    count data.state = data.result := by
  have he := Option.some.inj h
  cases he
  exact hcount

/-- Every stored numeric reference agrees with the specified model count. -/
def ReferencesValid (count : State → ℕ) (references : ℕ → Option (CountData State)) : Prop :=
  ∀ index data, references index = some data → count data.state = data.result

/-- Reference lookup using only numeric data and exact comparison of the search state. -/
def withReferencesData (rules : Rules State) (sameState : State → State → Bool)
    (references : ℕ → Option (CountData State)) : Rules State :=
  { rules with
    lookup := fun state index => match references index with
      | none => none
      | some data => if sameState state data.state then some data.result else none }

/-- Independently proved reference counts suffice for the purely numeric lookup checker. -/
theorem withReferencesData_sound {rules : Rules State} {count : State → ℕ}
    (sound : Sound rules count) (sameState : State → State → Bool)
    (sameState_sound : ∀ state other, sameState state other = true → state = other)
    (references : ℕ → Option (CountData State)) (hvalid : ReferencesValid count references) :
    Sound (withReferencesData rules sameState references) count where
  reject := sound.reject
  accept := sound.accept
  split := sound.split
  simplify := sound.simplify
  lookup state index result h := by
    change (match references index with
      | none => none
      | some data => if sameState state data.state then some data.result else none) =
      some result at h
    cases hr : references index with
    | none => simp [hr] at h
    | some data =>
      simp only [hr] at h
      split at h
      · rename_i hs
        have he := sameState_sound state data.state hs
        injection h with hc
        rw [he, ← hc]
        exact hvalid index data hr
      · contradiction

/-- A search state with its exact count already proved. -/
structure CertifiedCount (count : State → ℕ) where
  /-- The state whose count is certified. -/
  state : State
  /-- The certified number of models. -/
  result : ℕ
  /-- The mathematical justification of the stored number. -/
  proof : count state = result

/-- Enable references, checking equality of the current and previously certified states. -/
def withReferences {count : State → ℕ} (rules : Rules State) (sameState : State → State → Bool)
    (references : ℕ → Option (CertifiedCount count)) : Rules State :=
  { rules with
    lookup := fun state index => match references index with
      | none => none
      | some certified =>
        if sameState state certified.state then some certified.result else none }

/-- Reusing a proved count for an equal state preserves checker soundness. -/
theorem withReferences_sound {rules : Rules State} {count : State → ℕ}
    (sound : Sound rules count) (sameState : State → State → Bool)
    (sameState_sound : ∀ state other, sameState state other = true → state = other)
    (references : ℕ → Option (CertifiedCount count)) :
    Sound (withReferences rules sameState references) count where
  reject := sound.reject
  accept := sound.accept
  split := sound.split
  simplify := sound.simplify
  lookup state index result h := by
    change (match references index with
      | none => none
      | some certified =>
        if sameState state certified.state then some certified.result else none) = some result at h
    cases hr : references index with
    | none => simp [hr] at h
    | some certified =>
      simp only [hr] at h
      split at h
      · rename_i hs
        have he := sameState_sound state certified.state hs
        injection h with hc
        rw [he, ← hc]
        exact certified.proof
      · contradiction

end Cslib.RelationAlgebra.Counting

namespace Cslib.RelationAlgebra.Search

open Counting

/-- A certified count for one state of this numeric relation-algebra problem. -/
abbrev Problem.CertifiedCount (problem : Problem) :=
  Counting.CertifiedCount (ActiveSearch.modelCount problem.variables problem.constraints)

/-- Check one certificate chunk, using earlier certified states as references. -/
def Problem.checkChunk (problem : Problem) (references : ℕ → Option problem.CertifiedCount)
    (state : ActiveSearch.State) (certificate : Certificate) : Option ℕ :=
  Counting.check
    (withReferences (ActiveSearch.rules problem.variables problem.constraints)
      ActiveSearch.State.beq references) state certificate

/-- A successfully checked chunk proves the exact count at its starting state. -/
theorem Problem.checkChunk_sound (problem : Problem) (hp : problem.PermutationsBounded)
    (references : ℕ → Option problem.CertifiedCount) (state : ActiveSearch.State)
    (certificate : Certificate) (result : ℕ)
    (hcheck : problem.checkChunk references state certificate = some result) :
    ActiveSearch.modelCount problem.variables problem.constraints state = result :=
  Counting.check_sound
    (withReferences_sound (ActiveSearch.rules_sound (problem.constraints_sound hp))
      ActiveSearch.State.beq (fun state other => (ActiveSearch.State.beq_eq_true state other).mp)
      references) certificate state result hcheck

/-- Package a checked chunk for use by later chunks without rechecking its computation. -/
def Problem.certify (problem : Problem) (hp : problem.PermutationsBounded)
    (references : ℕ → Option problem.CertifiedCount) (state : ActiveSearch.State)
    (certificate : Certificate) (result : ℕ)
    (hcheck : problem.checkChunk references state certificate = some result) :
    problem.CertifiedCount :=
  ⟨state, result, problem.checkChunk_sound hp references state certificate result hcheck⟩

end Cslib.RelationAlgebra.Search
