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
inductive Circuit (n : ℕ) (α : Type u) : Type u → Type u where
  | const  (x : α) : Circuit n α α
  | add (c₁ c₂ : Fin n) : Circuit n α α
  | mul (c₁ c₂ : Fin n) : Circuit n α α
  | neg (c : Fin n) : Circuit n α α

structure CircuitLines (n : ℕ) (α ι : Type u) : Type u where
  circuits : (i : Fin n) → Circuit i ι ι

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

variable (α : Type u) [Add α] [Mul α] [Neg α]

def circEval {n : ℕ} (c : CircuitLines n α α) (id : Fin n) : α :=
  match (c.circuits id) with
  | .const x => x
  | .add id₁ id₂ => circEval c ⟨id₁, by grind⟩ + circEval c ⟨id₂, by grind⟩
  | .mul id₁ id₂ => circEval c ⟨id₁, by grind⟩ * circEval c ⟨id₂, by grind⟩
  | .neg id => - circEval c ⟨id, by grind⟩
termination_by id


def depthOf (c : CircuitLines n α α) (id : Fin n) :=
  match (c.circuits id) with
  | .const c => 0
  | .add id₁ id₂ => 1 + max (depthOf c ⟨id₁, by grind⟩) (depthOf c ⟨id₂, by grind⟩)
  | .mul id₁ id₂ => 1 + max (depthOf c ⟨id₁, by grind⟩) (depthOf c ⟨id₂, by grind⟩)
  | .neg id => 1 + depthOf c ⟨id, by grind⟩

def uniqueIDs (q : CircuitLines n α α) (countedIDs : List ℕ) (id : Fin n) : List ℕ :=
  match (q.circuits id) with
  | .const _ =>
      countedIDs.insert id
  | .add id₁ id₂ =>
      let s₁ := uniqueIDs q countedIDs ⟨id₁, by grind⟩
      let s₂ := uniqueIDs q s₁ ⟨id₂, by clear s₁; grind⟩
      s₂.insert id
  | .mul id₁ id₂ =>
      let s₁ := uniqueIDs q countedIDs ⟨id₁, by grind⟩
      let s₂ := uniqueIDs q s₁ ⟨id₂, by clear s₁; grind⟩
      s₂.insert id
  | .neg c =>
      let s := uniqueIDs q countedIDs ⟨c, by grind⟩
      s.insert id

def sizeOf (q : CircuitLines n α α) (id : Fin n) := (uniqueIDs α q [] id).length

def circModel  [Add ι] [Mul ι] [Neg ι] : Model (CircuitLines (n + 1) ι) CircuitCosts where
  evalQuery {ι} q := @circEval ι q ⟨n, by grind⟩
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
