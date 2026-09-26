/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Circuit.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Composing circuits

A program can be continued by a second program whose inputs are read from wires of the first.
Reading them from the outputs of a circuit gives sequential composition, `Circuit.comp`, which
evaluates to the composite of the two functions. Reading them from the original inputs gives
parallel composition on shared inputs, `Circuit.append`, whose outputs are those of the first
circuit followed by those of the second. In both cases the gate counts add.
-/

@[expose] public section

namespace Fin

variable {α : Type*} {m n : ℕ}

@[simp] theorem append_comp_castAdd (u : Fin m → α) (v : Fin n → α) :
    append u v ∘ castAdd n = u :=
  funext (append_left u v)

@[simp] theorem append_comp_natAdd (u : Fin m → α) (v : Fin n → α) :
    append u v ∘ natAdd m = v :=
  funext (append_right u v)

end Fin

namespace Cslib.Circuits

universe v u

variable {σ : Signature.{v}} {U : Type u} {n m p k g₁ g₂ : ℕ}

namespace Program

/-- The wire of `p.append feed q` that carries a wire of `q`: an input of `q` is the wire of `p`
feeding it, and a gate of `q` comes after all the gates of `p`. -/
def appendWire (feed : Fin k → Wire n g₁) : Wire k g₂ → Wire n (g₁ + g₂)
  | .input i => (feed i).castAdd g₂
  | .gate j => .gate (Fin.natAdd g₁ j)

@[simp] theorem appendWire_input (feed : Fin k → Wire n g₁) (i : Fin k) :
    appendWire (g₂ := g₂) feed (Wire.input i) = (feed i).castAdd g₂ := rfl

@[simp] theorem appendWire_gate (feed : Fin k → Wire n g₁) (j : Fin g₂) :
    appendWire feed (Wire.gate j) = Wire.gate (Fin.natAdd g₁ j) := rfl

theorem appendWire_castSucc (feed : Fin k → Wire n g₁) (w : Wire k g₂) :
    appendWire (g₂ := g₂ + 1) feed w.castSucc = (appendWire feed w).castSucc := by
  cases w with
  | input i =>
    change (feed i).castAdd (g₂ + 1) = ((feed i).castAdd g₂).castSucc
    cases feed i <;> rfl
  | gate j => rfl

theorem appendWire_last (feed : Fin k → Wire n g₁) :
    appendWire (g₂ := g₂ + 1) feed (Wire.gate (Fin.last g₂)) =
      Wire.gate (Fin.last (g₁ + g₂)) :=
  rfl

/-- Continue `p` by `q`, reading the inputs of `q` from the wires `feed` of `p`. -/
def append (p : Program σ n g₁) (feed : Fin k → Wire n g₁) :
    {g₂ : ℕ} → Program σ k g₂ → Program σ n (g₁ + g₂)
  | _, .empty => p
  | _, .gate q line => .gate (p.append feed q) (line.mapWires (appendWire feed))

variable (p : Program σ n g₁) (feed : Fin k → Wire n g₁) (I : Interpretation σ U)
  (x : Fin n → U)

/-- The wires of `p` keep their values after `p` is continued. -/
theorem trace_append_castAdd (q : Program σ k g₂) (w : Wire n g₁) :
    (p.append feed q).trace I x (w.castAdd g₂) = p.trace I x w := by
  induction q with
  | empty => cases w <;> rfl
  | @gate g₂ q line ih =>
    have hw : w.castAdd (g₂ + 1) = (w.castAdd g₂).castSucc := by cases w <;> rfl
    rw [hw]
    exact (Program.trace_gate_castSucc _ _ I x _).trans ih

/-- A wire of `q` carries, in the continued program, the value it has when `q` runs on the
values of the wires feeding it. -/
theorem trace_append_appendWire (q : Program σ k g₂) (w : Wire k g₂) :
    (p.append feed q).trace I x (appendWire feed w) =
      q.trace I (fun i => p.trace I x (feed i)) w := by
  induction q with
  | empty =>
    cases w with
    | input i => exact trace_append_castAdd p feed I x .empty (feed i)
    | gate j => exact j.elim0
  | @gate g₂ q line ih =>
    refine Wire.lastCases ?_ (fun w => ?_) w
    · rw [appendWire_last]
      refine (Program.eval_gate_last _ _ I x).trans ?_
      refine Eq.trans ?_ (Program.eval_gate_last q line I _).symm
      exact Line.eval_mapWires line (appendWire feed) I _ x _ _ ih
    · rw [appendWire_castSucc]
      refine (Program.trace_gate_castSucc _ _ I x _).trans ?_
      exact (ih w).trans (Program.trace_gate_castSucc q line I _ w).symm

end Program

namespace Circuit

variable {I : Interpretation σ U}

/-- Feed the outputs of `c` to the inputs of `d`. -/
def comp (d : Circuit σ m p) (c : Circuit σ n m) : Circuit σ n p :=
  ⟨c.program.append c.outputs d.program, fun o => Program.appendWire c.outputs (d.outputs o)⟩

@[simp] theorem size_comp (d : Circuit σ m p) (c : Circuit σ n m) :
    (d.comp c).size = c.size + d.size := rfl

@[simp] theorem eval_comp (d : Circuit σ m p) (c : Circuit σ n m) (x : Fin n → U) :
    (d.comp c).eval I x = d.eval I (c.eval I x) := by
  funext o
  exact Program.trace_append_appendWire c.program c.outputs I x d.program (d.outputs o)

/-- Run `c` and `d` on the same inputs, listing the outputs of `c` before those of `d`. -/
def append (c : Circuit σ n m) (d : Circuit σ n p) : Circuit σ n (m + p) :=
  ⟨c.program.append Wire.input d.program,
    Fin.append (fun o => (c.outputs o).castAdd d.size)
      fun o => Program.appendWire Wire.input (d.outputs o)⟩

@[simp] theorem size_append (c : Circuit σ n m) (d : Circuit σ n p) :
    (c.append d).size = c.size + d.size := rfl

@[simp] theorem eval_append (c : Circuit σ n m) (d : Circuit σ n p) (x : Fin n → U) :
    (c.append d).eval I x = Fin.append (c.eval I x) (d.eval I x) := by
  funext o
  induction o using Fin.addCases with
  | left o =>
    simp only [eval, append, Function.comp_apply, Fin.append_left]
    exact Program.trace_append_castAdd c.program Wire.input I x d.program (c.outputs o)
  | right o =>
    simp only [eval, append, Function.comp_apply, Fin.append_right]
    exact Program.trace_append_appendWire c.program Wire.input I x d.program _

/-- Feeding a circuit computing `f` into one computing `g` computes `g ∘ f`. -/
theorem Computes.comp {c : Circuit σ n m} {d : Circuit σ m p}
    {f : (Fin n → U) → Fin m → U} {g : (Fin m → U) → Fin p → U}
    (hc : c.Computes I f) (hd : d.Computes I g) : (d.comp c).Computes I (g ∘ f) := fun x => by
  rw [eval_comp, hc x, hd]
  rfl

/-- Circuits computing `f` and `g`, run side by side, compute their outputs together. -/
theorem Computes.append {c : Circuit σ n m} {d : Circuit σ n p}
    {f : (Fin n → U) → Fin m → U} {g : (Fin n → U) → Fin p → U}
    (hc : c.Computes I f) (hd : d.Computes I g) :
    (c.append d).Computes I (fun x => Fin.append (f x) (g x)) := fun x => by
  rw [eval_append, hc x, hd x]

/-- Feeding a circuit computing `f` on `S` into one computing `g` on the image of `S` computes
`g ∘ f` on `S`. -/
theorem ComputesOn.comp {c : Circuit σ n m} {d : Circuit σ m p} {S : Set (Fin n → U)}
    {f : (Fin n → U) → Fin m → U} {g : (Fin m → U) → Fin p → U}
    (hc : c.ComputesOn I S f) (hd : d.ComputesOn I (f '' S) g) :
    (d.comp c).ComputesOn I S (g ∘ f) := fun x hx => by
  rw [eval_comp, hc hx]
  exact hd ⟨x, hx, rfl⟩

/-- Circuits computing `f` and `g` on `S`, run side by side, compute their outputs together. -/
theorem ComputesOn.append {c : Circuit σ n m} {d : Circuit σ n p} {S : Set (Fin n → U)}
    {f : (Fin n → U) → Fin m → U} {g : (Fin n → U) → Fin p → U}
    (hc : c.ComputesOn I S f) (hd : d.ComputesOn I S g) :
    (c.append d).ComputesOn I S (fun x => Fin.append (f x) (g x)) := fun x hx => by
  rw [eval_append, hc hx, hd hx]

end Circuit

end Cslib.Circuits
