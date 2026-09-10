/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.ToAdditive
import Cslib.Computability.Circuit.Normalization
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Counting Boolean circuits

We bound the size of `computableFunctions n s`, the Boolean functions computable with
at most `s` De Morgan gates. This estimate is used in Shannon's lower bound.

The proof first merges gates that compute the same function on every input, preserving
the circuit's outputs without increasing its size. A resulting circuit with `g` gates
has `g!` distinct labeled presentations, one for each permutation of its gates. This
lets us divide the presentation count by `g!` before summing over gate counts `g ≤ s`.
-/

public section

namespace Cslib.Circuits.Boolean

open scoped BigOperators

variable {n g s : ℕ}

/-- Boolean functions computable with at most `s` De Morgan gates. -/
noncomputable def computableFunctions (n s : ℕ) : Finset (BooleanFunction n) := by
  classical
  exact Finset.univ.filter fun f => ∃ g ≤ s, ∃ c : Circuit signature n g 1, c.Computes f

@[simp] theorem mem_computableFunctions {f : BooleanFunction n} :
    f ∈ computableFunctions n s ↔ ∃ g ≤ s, ∃ c : Circuit signature n g 1, c.Computes f := by
  classical
  simp [computableFunctions]

private noncomputable def irredundantFunctions (n g : ℕ) : Finset (BooleanFunction n) := by
  classical
  exact Finset.univ.filter fun f => ∃ c : Circuit signature n g 1,
    c.Computes f ∧ Function.Injective (c.program.gateFunction interpretation)

private theorem mem_irredundantFunctions {f : BooleanFunction n} :
    f ∈ irredundantFunctions n g ↔ ∃ c : Circuit signature n g 1,
      c.Computes f ∧ Function.Injective (c.program.gateFunction interpretation) := by
  classical
  simp [irredundantFunctions]

private instance opFintype : Fintype Op where
  elems := {.const false, .const true, .not, .and, .or}
  complete := by intro op; cases op <;> simp

private def lineEquiv (n g : ℕ) :
    Line signature n g ≃ Σ op : Op, Fin (signature.Arity op) → Wire n g where
  toFun l := ⟨l.op, l.wires⟩
  invFun l := ⟨l.1, l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable instance : Fintype (Line signature n g) :=
  Fintype.ofEquiv _ (lineEquiv n g).symm

private theorem card_line_le (n g : ℕ) :
    Fintype.card (Line signature n g) ≤ 5 * (n + g + 1) ^ 2 := by
  rw [Fintype.card_congr (lineEquiv n g), Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin]
  calc
    ∑ op : Op, (n + g) ^ signature.Arity op ≤ ∑ _op : Op, (n + g + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro op _
      exact (Nat.pow_le_pow_left (by omega : n + g ≤ n + g + 1) _).trans
        (Nat.pow_le_pow_right (by omega) (by cases op <;> simp))
    _ = 5 * (n + g + 1) ^ 2 := by simp [show Fintype.card Op = 5 from rfl]

-- Gate equations and an output wire, without a topological ordering.
private abbrev Presentation (n g : ℕ) := (Fin g → Line signature n g) × Wire n g

private def relabel (c : Circuit signature n g 1) (π : Equiv.Perm (Fin g)) :
    Presentation n g :=
  (fun a => (c.program.lines (π.symm a)).mapWires (Wire.Renaming.ofPermutation π),
    Wire.Renaming.ofPermutation π (c.outputs 0))

private theorem relabel_line_eval (c : Circuit signature n g 1) (π : Equiv.Perm (Fin g))
    (x : Fin n → Bool) (v : Fin g → Bool) (a : Fin g) :
    ((relabel c π).1 a).eval interpretation x v =
      (c.program.lines (π.symm a)).eval interpretation x (v ∘ π) := by
  apply Line.eval_mapRenaming
  intro gate
  simp [Wire.Renaming.ofPermutation]

private theorem relabel_unique (c : Circuit signature n g 1) (π : Equiv.Perm (Fin g))
    (x : Fin n → Bool) (v : Fin g → Bool)
    (h : ∀ a, ((relabel c π).1 a).eval interpretation x v = v a) :
    v = c.program.eval interpretation x ∘ π.symm := by
  have hv : v ∘ π = c.program.eval interpretation x :=
    c.program.eq_eval_of_forall_lines_eval interpretation x _ (fun a => by
      simpa [relabel_line_eval] using h (π a))
  funext a
  simpa using congrFun hv (π.symm a)

private theorem relabel_output (c : Circuit signature n g 1) (π : Equiv.Perm (Fin g))
    (x : Fin n → Bool) :
    Fin.addCases x (c.program.eval interpretation x ∘ π.symm) (relabel c π).2 =
      c.eval interpretation x 0 := by
  apply Wire.Renaming.value_apply
  intro gate
  simp [Wire.Renaming.ofPermutation, Function.comp_def]

private noncomputable def representative (f : ↥(irredundantFunctions n g)) :
    Circuit signature n g 1 :=
  (mem_irredundantFunctions.mp f.property).choose

private theorem representative_spec (f : ↥(irredundantFunctions n g)) :
    (representative f).Computes f ∧
      Function.Injective ((representative f).program.gateFunction interpretation) :=
  (mem_irredundantFunctions.mp f.property).choose_spec

-- Equal presentations determine the function; distinct gate functions determine the labels.
private theorem relabel_injective : Function.Injective
    (fun p : ↥(irredundantFunctions n g) × Equiv.Perm (Fin g) =>
      relabel (representative p.1) p.2) := by
  rintro ⟨f, π⟩ ⟨f', τ⟩ heq
  dsimp only at heq
  have hvalues (x : Fin n → Bool) :
      (representative f).program.eval interpretation x ∘ π.symm =
        (representative f').program.eval interpretation x ∘ τ.symm := by
    apply relabel_unique
    intro a
    rw [← heq, relabel_line_eval]
    simpa [Function.comp_def] using
      (representative f).program.lines_eval interpretation x (π.symm a)
  have hfunction : f = f' := by
    apply Subtype.ext
    funext x
    rw [← (representative_spec f).1 x, ← (representative_spec f').1 x,
      ← relabel_output _ π, ← relabel_output _ τ, heq, hvalues]
  subst f'
  have hpermutation : π.symm = τ.symm := by
    apply Equiv.ext
    intro a
    apply (representative_spec f).2
    funext x
    exact congrFun (hvalues x) a
  exact Prod.ext rfl (by simpa using congrArg Equiv.symm hpermutation)

private theorem card_irredundantFunctions_mul_factorial_le (n g : ℕ) :
    (irredundantFunctions n g).card * g.factorial ≤
      (5 * (n + g + 1) ^ 2) ^ g * (n + g) := by
  classical
  have h := Fintype.card_le_of_injective _ (relabel_injective (n := n) (g := g))
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_fun] at h
  exact h.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (card_line_le n g) g))

private theorem card_computableFunctions_le_sum (n s : ℕ) :
    (computableFunctions n s).card ≤
      ∑ g ∈ Finset.range (s + 1), (irredundantFunctions n g).card := by
  classical
  apply le_trans (Finset.card_le_card (t :=
    (Finset.range (s + 1)).biUnion (irredundantFunctions n)) ?_) Finset.card_biUnion_le
  intro f hf
  obtain ⟨g, hg, c, hc⟩ := mem_computableFunctions.mp hf
  obtain ⟨k, hk, d, hd, hinj⟩ := c.exists_injective_gateFunction interpretation
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_range.mpr (by omega), mem_irredundantFunctions.mpr ⟨d, ?_, hinj⟩⟩
  simpa only [Circuit.Computes, hd] using hc

/-- An upper bound on the number of computable functions, accounting for gate relabelings. -/
theorem card_computableFunctions_mul_factorial_le (n s : ℕ) :
    (computableFunctions n s).card * s.factorial ≤
      (s + 1) * (5 * (n + s + 1) ^ 2) ^ s * (n + s) := by
  let B := 5 * (n + s + 1) ^ 2
  have hB : s ≤ B := by
    dsimp [B]
    nlinarith [Nat.le_mul_self (n + s + 1)]
  have hterm (g : ℕ) (hg : g ≤ s) :
      (irredundantFunctions n g).card * s.factorial ≤ B ^ s * (n + s) := by
    calc
      (irredundantFunctions n g).card * s.factorial =
          ((irredundantFunctions n g).card * g.factorial) * (g + 1).ascFactorial (s - g) := by
        rw [mul_assoc, Nat.factorial_mul_ascFactorial, Nat.add_sub_of_le hg]
      _ ≤ ((5 * (n + g + 1) ^ 2) ^ g * (n + g)) * s ^ (s - g) :=
        Nat.mul_le_mul (card_irredundantFunctions_mul_factorial_le n g)
          (by simpa [Nat.add_sub_of_le hg] using Nat.ascFactorial_le_pow_add g (s - g))
      _ ≤ (B ^ g * (n + s)) * B ^ (s - g) := by dsimp [B]; gcongr
      _ = B ^ s * (n + s) := by rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hg]
  calc
    (computableFunctions n s).card * s.factorial ≤
        (∑ g ∈ Finset.range (s + 1), (irredundantFunctions n g).card) * s.factorial :=
      Nat.mul_le_mul_right _ (card_computableFunctions_le_sum n s)
    _ ≤ ∑ _g ∈ Finset.range (s + 1), B ^ s * (n + s) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun g hg => hterm g (Nat.le_of_lt_succ (Finset.mem_range.mp hg))
    _ = (s + 1) * B ^ s * (n + s) := by simp [mul_assoc]

end Cslib.Circuits.Boolean
