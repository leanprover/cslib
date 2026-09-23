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

variable {σ : Signature.{v}} {U : Type u} {n m p k g h : ℕ}

namespace Program

/-- The wire of `p.append feed q` that carries a wire of `q`: an input of `q` is the wire of `p`
feeding it, and a gate of `q` comes after all the gates of `p`. -/
def appendWire (feed : Fin k → Wire n g) : Wire k h → Wire n (g + h) :=
  Fin.addCases (fun i => Fin.castLE (Nat.add_le_add_left (Nat.le_add_right g h) n) (feed i))
    fun j => Wire.gate (Fin.natAdd g j)

@[simp] theorem appendWire_input (feed : Fin k → Wire n g) (i : Fin k) :
    appendWire (h := h) feed (Wire.input i) =
      Fin.castLE (Nat.add_le_add_left (Nat.le_add_right g h) n) (feed i) := by
  simp [appendWire]

@[simp] theorem appendWire_gate (feed : Fin k → Wire n g) (j : Fin h) :
    appendWire feed (Wire.gate j) = Wire.gate (Fin.natAdd g j) := by
  simp [appendWire]

theorem appendWire_castSucc (feed : Fin k → Wire n g) (w : Wire k h) :
    appendWire (h := h + 1) feed w.castSucc = (appendWire feed w).castSucc := by
  induction w using Fin.addCases with
  | left i => exact Fin.ext (by simp [Fin.castSucc_castAdd])
  | right j => exact Fin.ext (by simp)

theorem appendWire_last (feed : Fin k → Wire n g) :
    appendWire (h := h + 1) feed (Fin.last (k + h)) = Fin.last (n + (g + h)) := by
  rw [← Fin.natAdd_last, appendWire_gate]
  exact Fin.ext (by simp)

/-- Continue `p` by `q`, reading the inputs of `q` from the wires `feed` of `p`. -/
def append (p : Program σ n g) (feed : Fin k → Wire n g) :
    {h : ℕ} → Program σ k h → Program σ n (g + h)
  | _, .empty => p
  | _, .gate q line => .gate (p.append feed q) (line.mapWires (appendWire feed))

variable (p : Program σ n g) (feed : Fin k → Wire n g) (I : Interpretation σ U)
  (x : Fin n → U)

/-- The wires of `p` keep their values after `p` is continued. -/
theorem trace_append_castLE (q : Program σ k h) (w : Wire n g) :
    (p.append feed q).trace I x
        (Fin.castLE (Nat.add_le_add_left (Nat.le_add_right g h) n) w) =
      p.trace I x w := by
  induction q with
  | empty => rfl
  | @gate h q line ih =>
    have hw : (Fin.castLE (Nat.add_le_add_left (Nat.le_add_right g (h + 1)) n) w :
          Wire n (g + (h + 1))) =
        (Fin.castLE (Nat.add_le_add_left (Nat.le_add_right g h) n) w).castSucc :=
      Fin.ext rfl
    rw [hw]
    exact (Program.trace_gate_castSucc _ _ I x _).trans ih

/-- A wire of `q` carries, in the continued program, the value it has when `q` runs on the
values of the wires feeding it. -/
theorem trace_append_appendWire (q : Program σ k h) (w : Wire k h) :
    (p.append feed q).trace I x (appendWire feed w) =
      q.trace I (fun i => p.trace I x (feed i)) w := by
  induction q with
  | empty =>
    induction w using Fin.addCases with
    | left i =>
      rw [appendWire_input]
      exact (trace_append_castLE p feed I x .empty (feed i)).trans
        (Program.trace_input .empty I (fun i => p.trace I x (feed i)) i).symm
    | right j => exact j.elim0
  | @gate h q line ih =>
    refine Fin.lastCases (n := k + h) ?_ (fun w => ?_) w
    · rw [appendWire_last]
      refine (Program.trace_gate_last _ _ I x).trans ?_
      refine Eq.trans ?_ (Program.trace_gate_last q line I _).symm
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
    Fin.append
      (fun o => Fin.castLE (Nat.add_le_add_left (Nat.le_add_right _ _) n) (c.outputs o))
      fun o => Program.appendWire Wire.input (d.outputs o)⟩

@[simp] theorem size_append (c : Circuit σ n m) (d : Circuit σ n p) :
    (c.append d).size = c.size + d.size := rfl

@[simp] theorem eval_append (c : Circuit σ n m) (d : Circuit σ n p) (x : Fin n → U) :
    (c.append d).eval I x = Fin.append (c.eval I x) (d.eval I x) := by
  funext o
  induction o using Fin.addCases with
  | left o =>
    simp only [eval, append, Function.comp_apply, Fin.append_left]
    exact Program.trace_append_castLE c.program Wire.input I x d.program (c.outputs o)
  | right o =>
    simp only [eval, append, Function.comp_apply, Fin.append_right]
    refine (Program.trace_append_appendWire c.program Wire.input I x d.program _).trans ?_
    simp

/-- Feeding a circuit computing `F` into one computing `H` computes `H ∘ F`. -/
theorem Computes.comp {c : Circuit σ n m} {d : Circuit σ m p}
    {F : (Fin n → U) → Fin m → U} {H : (Fin m → U) → Fin p → U}
    (hc : c.Computes I F) (hd : d.Computes I H) : (d.comp c).Computes I (H ∘ F) := fun x => by
  rw [eval_comp, hc x, hd]
  rfl

/-- Circuits computing `F` and `G`, run side by side, compute their outputs together. -/
theorem Computes.append {c : Circuit σ n m} {d : Circuit σ n p}
    {F : (Fin n → U) → Fin m → U} {G : (Fin n → U) → Fin p → U}
    (hc : c.Computes I F) (hd : d.Computes I G) :
    (c.append d).Computes I (fun x => Fin.append (F x) (G x)) := fun x => by
  rw [eval_append, hc x, hd x]

/-- Feeding a circuit computing `F` on `S` into one computing `H` on the image of `S` computes
`H ∘ F` on `S`. -/
theorem ComputesOn.comp {c : Circuit σ n m} {d : Circuit σ m p} {S : Set (Fin n → U)}
    {F : (Fin n → U) → Fin m → U} {H : (Fin m → U) → Fin p → U}
    (hc : c.ComputesOn I S F) (hd : d.ComputesOn I (F '' S) H) :
    (d.comp c).ComputesOn I S (H ∘ F) := fun x hx => by
  rw [eval_comp, hc x hx]
  exact hd _ ⟨x, hx, rfl⟩

/-- Circuits computing `F` and `G` on `S`, run side by side, compute their outputs together. -/
theorem ComputesOn.append {c : Circuit σ n m} {d : Circuit σ n p} {S : Set (Fin n → U)}
    {F : (Fin n → U) → Fin m → U} {G : (Fin n → U) → Fin p → U}
    (hc : c.ComputesOn I S F) (hd : d.ComputesOn I S G) :
    (c.append d).ComputesOn I S (fun x => Fin.append (F x) (G x)) := fun x hx => by
  rw [eval_append, hc x hx, hd x hx]

end Circuit

end Cslib.Circuits
