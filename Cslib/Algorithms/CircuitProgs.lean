/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.Algorithms.QueryModel

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
  nodeIDList : List ℕ

instance : PureCosts CircuitCosts where
  pureCost := ⟨0,0, []⟩

instance : Zero CircuitCosts where
  zero := ⟨0,0, []⟩

instance : Add CircuitCosts where
  add x y := ⟨x.1 + y.1, x.2 + y.2, x.3 ++ y.3⟩

def circEval (α : Type u) [Add α] [Mul α] [Neg α] (c : Circuit α ι) : ι :=
  match c with
  | .const _ x => x
  | .add _ c₁ c₂ => circEval α c₁ + circEval α c₂
  | .mul _ c₁ c₂ => circEval α c₁ * circEval α c₂
  | .neg _ c => - circEval α c

def depthOf (q : Circuit α β) :=
  match q with
  | .const _ c => 0
  | .add _ c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .mul _ c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .neg _ c => 1 + depthOf c

def uniqueIDs (q : Circuit α β) (countedIDs : List ℕ) : List ℕ :=
  match q with
  | .const id _ =>
      if id ∉ countedIDs then id :: countedIDs else countedIDs
  | .add id x y =>
      let s₁ := uniqueIDs x countedIDs
      let s₂ := uniqueIDs y s₁
      if id ∉ s₂
      then
        id :: s₂
      else
        s₂
  | .mul id x y =>
      let s₁ := uniqueIDs x countedIDs
      let s₂ := uniqueIDs y s₁
      if id ∉ s₂
      then id :: s₂
      else s₂
  | .neg id x =>
      let s := uniqueIDs x countedIDs
      if id ∉ s
      then id :: s
      else s


def sizeOf (q : Circuit α β) := (uniqueIDs q []).length

def circModel (α : Type u) [Add α] [Mul α] [Neg α] : Model (Circuit α) CircuitCosts where
  evalQuery q := circEval α q
  cost q := ⟨depthOf q, sizeOf q, uniqueIDs q []⟩

open Circuit in
def exCircuit1 : Prog (Circuit Bool) Bool := do
  let x := const 0 true
  let y := const 1 true
  let z := add 2 x y
  let w := mul 3 x y
  add 4 z w

#eval exCircuit1.eval (circModel Bool)
#eval exCircuit1.time (circModel Bool)

open Circuit in
def exCircuit2 : Prog (Circuit ℚ) ℚ := do
  let x := const 0 (1 : ℚ)
  let y := const 1 (2 : ℚ)
  let z := add 2 x y
  mul 4 z z

#eval exCircuit2.eval (circModel ℚ)
#eval exCircuit2.time (circModel ℚ)

open Circuit in
def exCircuit3 (x y : Circuit ℚ ℚ) : Prog (Circuit ℚ) ℚ := do
  let z := add 2 x y
  let w := mul 3 x y
  mul 4 z w

#eval (exCircuit3 (.const 0 (1 : ℚ)) (.const 1 (21 : ℚ))).eval (circModel ℚ)
#eval (exCircuit3 (.const 0 (1 : ℚ)) (.const 1 (21 : ℚ))).time (circModel ℚ)


open Circuit in
def CircAnd (n : ℕ) (x : Fin n → Circuit Bool Bool) : Circuit Bool Bool :=
  match n with
  | 0 => const n true
  | m + 1 =>
      let x_head := x 0
      let x_cons := CircAnd m (Fin.tail x)
      mul (n + m + 1) x_head x_cons

def execCircAnd (x : Fin n → Circuit Bool Bool) : Prog (Circuit Bool) Bool := do
  CircAnd n x

#eval (execCircAnd ![.const 0 true, .const 1 true, .const 2 true]).eval (circModel Bool)
#eval (execCircAnd ![.const 0 true, .const 1 true, .const 2 true]).time (circModel Bool)

end Prog

end Algorithms

end Cslib
