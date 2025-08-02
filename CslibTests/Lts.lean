/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Semantics.Lts.Basic
import Cslib.Semantics.Lts.Bisimulation
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity

-- A simple LTS on natural numbers

inductive NatTr : ℕ → ℕ → ℕ → Prop where
| one : NatTr 1 2 2
| one' : NatTr 1 1 1
| two : NatTr 2 1 1
| two' : NatTr 2 2 2

theorem NatTr.dom : NatTr n μ m → (n = 1 ∨ n = 2) ∧ (m = 1 ∨ m = 2) := by
  intro h
  cases h <;> simp

def natLts : Lts ℕ ℕ := ⟨NatTr⟩

inductive NatBisim : ℕ → ℕ → Prop where
| one_one : NatBisim 1 1
| one_two : NatBisim 1 2
| two_one : NatBisim 2 1
| two_two : NatBisim 2 2

example : 1 ~[natLts] 2 := by
  exists NatBisim
  constructor
  . constructor
  . simp [Bisimulation]
    intro s1 s2 hr μ
    constructor
    . intro s1' htr
      cases htr <;> (cases hr <;> repeat constructor)
    . intro s2' htr
      cases htr <;> (cases hr <;> repeat constructor)

inductive TLabel : Type where
| τ

instance : HasTau TLabel := {
  τ := TLabel.τ
}

inductive NatDivergentTr : ℕ → TLabel → ℕ → Prop where
| step : NatDivergentTr n τ n.succ

def natDivLts : Lts ℕ TLabel := ⟨NatDivergentTr⟩

def natInfiniteExecution : Stream' ℕ := fun n => n

theorem natInfiniteExecution.infiniteExecution : natDivLts.DivergentExecution natInfiniteExecution := by
  simp [Lts.DivergentExecution]
  intro n
  constructor

example : natDivLts.Divergent 0 := by
  simp [Lts.Divergent]
  exists natInfiniteExecution
  constructor; constructor
  exact natInfiniteExecution.infiniteExecution

example : natDivLts.Divergent 3 := by
  simp [Lts.Divergent]
  exists natInfiniteExecution.drop 3
  simp [Stream'.drop]
  constructor
  · constructor
  · simp [Lts.DivergentExecution]
    simp [Stream'.drop]
    intro n
    constructor

example : natDivLts.Divergent n := by
  simp [Lts.Divergent]
  exists natInfiniteExecution.drop n
  simp [Stream'.drop]
  constructor
  · constructor
  · apply Lts.divergent_drop
    exact natInfiniteExecution.infiniteExecution

-- check that notation works
variable {Term : Type} {Label : Type}
@[lts lts "β", simp]
def labelled_transition : Term → Label → Term → Prop := λ _ _ _ ↦ True

example (a b : Term) (μ : Label) : a [μ]⭢β b := by
  change labelled_transition a μ b
  simp

-- check that a "cannonical" notation works
attribute [lts cannonical_lts] labelled_transition

example (a b : Term) (μ : Label) : a [μ]⭢ b := by
  change labelled_transition a μ b
  simp

--check that namespaces are respected
namespace foo
@[lts namespaced_lts]
def bar (_ _ _ : ℕ) : Prop := True
end foo

/-- info: foo.bar : ℕ → ℕ → ℕ → Prop -/
#guard_msgs in
#check foo.bar

/-- info: foo.namespaced_lts : Lts ℕ ℕ -/
#guard_msgs in
#check foo.namespaced_lts

-- check that delaborators work, including with variables

/-- info: ∀ (a b : Term) (μ : Label), a[μ]⭢β b : Prop -/
#guard_msgs in
#check ∀ (a b : Term) (μ : Label), a [μ]⭢β b

/-- info: ∀ (a b : Term) (μ : Label), a[[μ]]↠β b : Prop -/
#guard_msgs in
#check ∀ (a b : Term) (μ : Label), a [[μ]]↠β b
