/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Alex Meiburg
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

namespace Cslib

namespace Algorithms

namespace Prog
inductive Circuit (α : Type u) : Type u → Type u where
  | const (x : α) : Circuit α α
  | add (c₁ c₂ : Circuit α α) : Circuit α α
  | mul (c₁ c₂ : Circuit α α) : Circuit α α
  | neg (c : Circuit α α) : Circuit α α
deriving DecidableEq

structure CircuitCosts where
  depth : ℕ
  size : ℕ
deriving BEq, DecidableEq

instance : Zero CircuitCosts where
  zero := ⟨0,0⟩

instance : Add CircuitCosts where
  add x y := ⟨x.1 + y.1, x.2 + y.2⟩

instance : AddZero CircuitCosts where

def circEval {α : Type u} [Add α] [Mul α] [Neg α] (c : Circuit α ι) : ι :=
  match c with
  | .const x => x
  | .add c₁ c₂ => circEval c₁ + circEval c₂
  | .mul c₁ c₂ => circEval c₁ * circEval c₂
  | .neg c => - circEval c

def depthOf (q : Circuit α β) :=
  match q with
  | .const c => 0
  | .add c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .mul c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .neg c => 1 + depthOf c

-- def uniqueIDs (q : Circuit α β) (countedIDs : Finset ℕ) : Finset ℕ :=
--   match q with
--   | .const id _ =>
--       insert id countedIDs
--   | .add id x y =>
--       let s₁ := uniqueIDs x countedIDs
--       let s₂ := uniqueIDs y s₁
--       insert id s₂
--   | .mul id x y =>
--       let s₁ := uniqueIDs x countedIDs
--       let s₂ := uniqueIDs y s₁
--       insert id s₂
--   | .neg id x =>
--       let s := uniqueIDs x countedIDs
--       insert id s

def Circuit.subcircuits {α} [DecidableEq α] (c : Circuit α α) : Finset (Circuit α α) :=
  insert c (
    match c with
    | .const _ => {}
    | .add c₁ c₂ => c₁.subcircuits ∪ c₂.subcircuits
    | .mul c₁ c₂ => c₁.subcircuits ∪ c₂.subcircuits
    | .neg c' => c'.subcircuits
)

def Circuit.sizeOf [DecidableEq α] (c : Circuit α β) :=
  match c with
  | .const x => (subcircuits (.const x)).card
  | .add c₁ c₂ => (subcircuits (.add c₁ c₂)).card
  | .mul c₁ c₂ => (subcircuits (.mul c₁ c₂)).card
  | .neg c' => (subcircuits c').card


def circModel [Add α] [Mul α] [Neg α] [DecidableEq α] : Model (Circuit α) CircuitCosts where
  evalQuery q := circEval q
  cost q := ⟨depthOf q, q.sizeOf⟩

end Prog

end Algorithms

end Cslib
