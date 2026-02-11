/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.Bisimulation
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity


namespace CslibTests

open Cslib

-- A simple LTS on natural numbers

inductive NatTr : ℕ → ℕ → ℕ → Prop where
| one : NatTr 1 2 2
| one' : NatTr 1 1 1
| two : NatTr 2 1 1
| two' : NatTr 2 2 2

theorem NatTr.dom : NatTr n μ m → (n = 1 ∨ n = 2) ∧ (m = 1 ∨ m = 2) := by
  intro h
  cases h <;> simp

def natLTS : LTS ℕ ℕ := ⟨NatTr⟩

inductive NatBisim : ℕ → ℕ → Prop where
| one_one : NatBisim 1 1
| one_two : NatBisim 1 2
| two_one : NatBisim 2 1
| two_two : NatBisim 2 2

example : 1 ~[natLTS] 2 := by
  exists NatBisim
  constructor
  · constructor
  · intro s1 s2 hr μ
    constructor
    · intro s1' htr
      cases htr <;> (cases hr <;> repeat constructor)
    · intro s2' htr
      cases htr <;> (cases hr <;> repeat constructor)

inductive TLabel : Type where
| τ

instance : HasTau TLabel := {
  τ := TLabel.τ
}

inductive NatDivergentTr : ℕ → TLabel → ℕ → Prop where
| step : NatDivergentTr n τ n.succ

def natDivLTS : LTS ℕ TLabel := ⟨NatDivergentTr⟩

def natInfiniteExecution : ωSequence ℕ := ⟨fun n => n⟩
def τSequence : ωSequence TLabel := ⟨fun _ => .τ⟩

theorem τSequence_divergentTrace : LTS.DivergentTrace τSequence := by
  simp [LTS.DivergentTrace]

example : natDivLTS.Divergent 0 := by
  use natInfiniteExecution, τSequence
  refine ⟨?_, rfl, τSequence_divergentTrace⟩
  intro i
  constructor

example : natDivLTS.Divergent 3 := by
  use natInfiniteExecution.drop 3, τSequence
  refine ⟨?_, rfl, τSequence_divergentTrace⟩
  intro i
  constructor

example : natDivLTS.Divergent n := by
  use natInfiniteExecution.drop n, τSequence.drop n
  refine ⟨?_, ?_, τSequence_divergentTrace⟩
  · intro i
    simp only [ωSequence.get_drop]
    constructor
  · simp [natInfiniteExecution]

-- Examples on decidable LTSs
def natTrF (n : ℕ) (μ : ℕ) (m : ℕ) : Bool :=
  match n, μ, m with
  | 1, 2, 2 => true
  | 1, 1, 1 => true
  | 2, 1, 1 => true
  | 2, 2, 2 => true
  | _, _, _ => false

def natLTSF : LTS ℕ ℕ := ⟨fun n μ m => natTrF n μ m⟩

example : natLTSF.MTr 1 [1, 2] 2 := by
  calc
    LTS.Tr.toRelation natLTSF 1 1 1 := by constructor
    LTS.Tr.toRelation natLTSF 2 1 2 := by constructor

-- check that notation works
variable {Term : Type} {Label : Type}
@[lts lts "β", simp]
def labelled_transition : Term → Label → Term → Prop := fun _ _ _ ↦ True

example (a b : Term) (μ : Label) : a [μ]⭢β b := by
  change labelled_transition a μ b
  simp

-- check that a "cannonical" notation works
attribute [lts cannonical_lts] labelled_transition

example (a b : Term) (μ : Label) : a [μ]⭢ b := by
  change labelled_transition a μ b
  simp

--check that namespaces are respected

/-- info: CslibTests.labelled_transition {Term Label : Type} : Term → Label → Term → Prop -/
#guard_msgs in
#check CslibTests.labelled_transition

/-- info: CslibTests.cannonical_lts {Term Label : Type} : LTS Term Label -/
#guard_msgs in
#check CslibTests.cannonical_lts

-- check that delaborators work, including with variables

/-- info: ∀ (a b : Term) (μ : Label), a[μ]⭢β b : Prop -/
#guard_msgs in
#check ∀ (a b : Term) (μ : Label), a [μ]⭢β b

/-- info: ∀ (a b : Term) (μ : Label), a[[μ]]↠β b : Prop -/
#guard_msgs in
#check ∀ (a b : Term) (μ : Label), a [[μ]]↠β b

end CslibTests
