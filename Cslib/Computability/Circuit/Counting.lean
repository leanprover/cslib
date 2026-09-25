/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Finite
public import Cslib.Computability.Circuit.Normalization
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.ToAdditive

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# Counting functions computed by finite circuits

For a finite signature, only finitely many functions can be computed with a fixed gate budget,
even when the carrier is infinite. We enumerate circuit syntax and collect its scalar functions.
Semantic equality and normalization use classical reasoning; the syntax enumeration is computable.

After merging gates that compute the same function, a circuit with `g` gates has `g!` distinct
labeled presentations. This factorial correction sharpens the count used in Shannon's lower bound.
The main bound accepts any uniform bound on the number of lines;
`card_computableFunctions_mul_factorial_le_of_arity_le` specializes it to operation arities.
-/

@[expose] public section

namespace Cslib.Circuits

open scoped BigOperators

universe v u
variable {σ : Signature.{v}} [Fintype σ.Op] {U : Type u}
variable {I : Interpretation σ U} {n g s : ℕ}

/-- Scalar functions computable with at most `s` gates. Enumerating circuit syntax makes
this family finite without requiring a finite carrier. -/
noncomputable def computableFunctions (I : Interpretation σ U) (n s : ℕ) :
    Finset ((Fin n → U) → U) :=
  open scoped Classical in
  (Finset.range (s + 1)).biUnion fun g =>
    Finset.univ.image fun c : Circuit σ n g 1 => fun x => c.eval I x 0

@[simp] theorem mem_computableFunctions {f : (Fin n → U) → U} :
    f ∈ computableFunctions I n s ↔
      ∃ g ≤ s, ∃ c : Circuit σ n g 1, c.Computes I (fun x _ => f x) := by
  classical
  simp [computableFunctions, Circuit.Computes, funext_iff, Nat.lt_succ_iff]

/-- Functions computed by circuits with exactly `g` pairwise semantically distinct gates.
Each such function has `g!` distinct presentations obtained by relabeling its chosen circuit. -/
noncomputable def irredundantFunctions (I : Interpretation σ U) (n g : ℕ) :
    Finset ((Fin n → U) → U) :=
  open scoped Classical in
  (Finset.univ.filter fun c : Circuit σ n g 1 => c.Irredundant I).image
    fun c => fun x => c.eval I x 0

@[simp] theorem mem_irredundantFunctions {f : (Fin n → U) → U} :
    f ∈ irredundantFunctions I n g ↔ ∃ c : Circuit σ n g 1,
      c.Computes I (fun x _ => f x) ∧ c.Irredundant I := by
  classical
  simp [irredundantFunctions, Circuit.Computes, funext_iff, and_comm]

section Relabeling

omit [Fintype σ.Op]

-- Gate equations and an output wire, without a topological ordering.
private abbrev Presentation (n g : ℕ) := (Fin g → Line σ n g) × Wire n g

private def relabel (c : Circuit σ n g 1) (π : Equiv.Perm (Fin g)) :
    Presentation (σ := σ) n g :=
  (fun a => (c.program.lines (π.symm a)).mapWires (Wire.Renaming.ofPermutation π),
    Wire.Renaming.ofPermutation π (c.outputs 0))

private theorem relabel_line_eval (c : Circuit σ n g 1) (π : Equiv.Perm (Fin g))
    (x : Fin n → U) (v : Fin g → U) (a : Fin g) :
    ((relabel c π).1 a).eval I x v =
      (c.program.lines (π.symm a)).eval I x (v ∘ π) := by
  apply Line.eval_mapRenaming
  intro gate
  simp [Wire.Renaming.ofPermutation]

private theorem relabel_unique (c : Circuit σ n g 1) (π : Equiv.Perm (Fin g))
    (x : Fin n → U) (v : Fin g → U)
    (h : ∀ a, ((relabel c π).1 a).eval I x v = v a) :
    v = c.program.eval I x ∘ π.symm := by
  have hv : v ∘ π = c.program.eval I x :=
    c.program.eq_eval_of_forall_lines_eval I x _ (fun a => by
      simpa [relabel_line_eval] using h (π a))
  funext a
  simpa using congrFun hv (π.symm a)

private theorem relabel_output (c : Circuit σ n g 1) (π : Equiv.Perm (Fin g))
    (x : Fin n → U) :
    Fin.addCases x (c.program.eval I x ∘ π.symm) (relabel c π).2 =
      c.eval I x 0 := by
  apply Wire.Renaming.value_apply
  intro gate
  simp [Wire.Renaming.ofPermutation, Function.comp_def]

end Relabeling

private noncomputable def representative (f : irredundantFunctions I n g) :
    Circuit σ n g 1 :=
  (mem_irredundantFunctions.mp f.property).choose

private theorem representative_spec (f : irredundantFunctions I n g) :
    (representative f).Computes I (fun x _ => f.1 x) ∧
      (representative f).Irredundant I :=
  (mem_irredundantFunctions.mp f.property).choose_spec

-- Equal presentations determine the function; distinct gate functions determine the labels.
private theorem relabel_injective : Function.Injective
    (fun p : irredundantFunctions I n g × Equiv.Perm (Fin g) =>
      relabel (representative p.1) p.2) := by
  rintro ⟨f, π⟩ ⟨f', τ⟩ heq
  dsimp only at heq
  have hvalues (x : Fin n → U) :
      (representative f).program.eval I x ∘ π.symm =
        (representative f').program.eval I x ∘ τ.symm := by
    apply relabel_unique
    intro a
    rw [← heq, relabel_line_eval]
    simpa [Function.comp_def] using
      (representative f).program.lines_eval I x (π.symm a)
  have hfunction : f = f' := by
    apply Subtype.ext
    funext x
    have hf : (representative f).eval I x 0 = f.1 x :=
      congrFun ((representative_spec f).1 x) 0
    have hf' : (representative f').eval I x 0 = f'.1 x :=
      congrFun ((representative_spec f').1 x) 0
    rw [← hf, ← hf',
      ← relabel_output _ π, ← relabel_output _ τ, heq, hvalues]
  subst f'
  have hpermutation : π.symm = τ.symm := by
    apply Equiv.ext
    intro a
    apply (representative_spec f).2
    funext x
    exact congrFun (hvalues x) a
  exact Prod.ext rfl (by simpa using congrArg Equiv.symm hpermutation)

/-- Distinct functions and permutations of their irredundant gates give distinct presentations. -/
theorem card_irredundantFunctions_mul_factorial_le (I : Interpretation σ U) (n g : ℕ) :
    (irredundantFunctions I n g).card * g.factorial ≤
      Fintype.card (Line σ n g) ^ g * (n + g) := by
  classical
  have h := Fintype.card_le_of_injective _ (relabel_injective (I := I) (n := n) (g := g))
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_fun] using h

/-- Normalizing a circuit places its function in one of the irredundant families. -/
theorem card_computableFunctions_le_sum (I : Interpretation σ U) (n s : ℕ) :
    (computableFunctions I n s).card ≤
      ∑ g ∈ Finset.range (s + 1), (irredundantFunctions I n g).card := by
  classical
  apply le_trans (Finset.card_le_card (t :=
    (Finset.range (s + 1)).biUnion (irredundantFunctions I n)) ?_) Finset.card_biUnion_le
  intro f hf
  obtain ⟨g, hg, c, hc⟩ := mem_computableFunctions.mp hf
  obtain ⟨k, hk, d, hd, hinj⟩ := c.exists_irredundant I
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_range.mpr (by omega), mem_irredundantFunctions.mpr ⟨d, ?_, hinj⟩⟩
  simpa only [Circuit.Computes, hd] using hc

/-- Bound the number of computable functions using a uniform line count `B`. The condition
`s ≤ B` absorbs the extra factorial factors from circuits with fewer than `s` gates. -/
theorem card_computableFunctions_mul_factorial_le (I : Interpretation σ U) (n s B : ℕ)
    (hB : s ≤ B) (hlines : ∀ g ≤ s, Fintype.card (Line σ n g) ≤ B) :
    (computableFunctions I n s).card * s.factorial ≤
      (s + 1) * B ^ s * (n + s) := by
  have hterm (g : ℕ) (hg : g ≤ s) :
      (irredundantFunctions I n g).card * s.factorial ≤ B ^ s * (n + s) := by
    calc
      (irredundantFunctions I n g).card * s.factorial =
          ((irredundantFunctions I n g).card * g.factorial) *
            (g + 1).ascFactorial (s - g) := by
        rw [mul_assoc, Nat.factorial_mul_ascFactorial, Nat.add_sub_of_le hg]
      _ ≤ (Fintype.card (Line σ n g) ^ g * (n + g)) * s ^ (s - g) :=
        Nat.mul_le_mul (card_irredundantFunctions_mul_factorial_le I n g)
          (by simpa [Nat.add_sub_of_le hg] using Nat.ascFactorial_le_pow_add g (s - g))
      _ ≤ (B ^ g * (n + s)) * B ^ (s - g) := by gcongr; exact hlines g hg
      _ = B ^ s * (n + s) := by rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hg]
  calc
    (computableFunctions I n s).card * s.factorial ≤
        (∑ g ∈ Finset.range (s + 1), (irredundantFunctions I n g).card) * s.factorial :=
      Nat.mul_le_mul_right _ (card_computableFunctions_le_sum I n s)
    _ ≤ ∑ _g ∈ Finset.range (s + 1), B ^ s * (n + s) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun g hg => hterm g (Nat.le_of_lt_succ (Finset.mem_range.mp hg))
    _ = (s + 1) * B ^ s * (n + s) := by simp [mul_assoc]

/-- A cardinality bound for any finite signature with bounded arities. The maximum also
covers empty signatures and signatures containing only nullary operations. -/
theorem card_computableFunctions_mul_factorial_le_of_arity_le
    (I : Interpretation σ U) (n s r : ℕ) (arity_le : ∀ op, σ.Arity op ≤ r) :
    (computableFunctions I n s).card * s.factorial ≤
      (s + 1) * (max s (Fintype.card σ.Op * (n + s + 1) ^ r)) ^ s * (n + s) := by
  apply card_computableFunctions_mul_factorial_le I n s _ (Nat.le_max_left _ _)
  intro g hg
  exact (Line.card_le n g r arity_le).trans
    ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : n + g + 1 ≤ n + s + 1) r)).trans
      (Nat.le_max_right _ _))

end Cslib.Circuits
