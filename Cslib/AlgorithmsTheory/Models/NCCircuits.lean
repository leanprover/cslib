/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric WIeser
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

namespace Cslib

namespace Algorithms

namespace Prog
inductive Circuit (α : Type u) : Type u → Type u where
  | const (id : ℕ) (x : α) : Circuit α α
  | add (id : ℕ) (c₁ c₂ : Circuit α α) : Circuit α α
  | mul (id : ℕ) (c₁ c₂ : Circuit α α) : Circuit α α
  | neg (id : ℕ) (c : Circuit α α) : Circuit α α

structure CircuitCosts where
  depth : ℕ
  size : ℕ
deriving BEq, DecidableEq

instance : Zero CircuitCosts where
  zero := ⟨0,0⟩

instance : Add CircuitCosts where
  add x y := ⟨x.1 + y.1, x.2 + y.2⟩

instance : AddZero CircuitCosts where

def circEval {α : Type u} [Ring α] (c : Circuit α ι) : ι :=
  match c with
  | .const _ x => x
  | .add _ c₁ c₂ => circEval c₁ + circEval c₂
  | .mul _ c₁ c₂ => circEval c₁ * circEval c₂
  | .neg _ c => - circEval c

def depthOf (q : Circuit α β) :=
  match q with
  | .const _ c => 0
  | .add _ c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .mul _ c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .neg _ c => 1 + depthOf c

def uniqueIDs (q : Circuit α β) (countedIDs : Finset ℕ) : Finset ℕ :=
  match q with
  | .const id _ =>
      insert id countedIDs
  | .add id x y =>
      let s₁ := uniqueIDs x countedIDs
      let s₂ := uniqueIDs y s₁
      insert id s₂
  | .mul id x y =>
      let s₁ := uniqueIDs x countedIDs
      let s₂ := uniqueIDs y s₁
      insert id s₂
  | .neg id x =>
      let s := uniqueIDs x countedIDs
      insert id s


def sizeOf (q : Circuit α β) := (uniqueIDs q {}).card

def circModel [Ring α] : Model (Circuit α) CircuitCosts where
  evalQuery q := circEval q
  cost q := ⟨depthOf q, sizeOf q⟩

end Prog

end Algorithms

end Cslib
