/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Complexity
public import Cslib.Computability.Circuit.Finite
public import Cslib.Computability.Circuit.Normalization
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.ToAdditive

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# Counting functions computed by finite circuits

For a finite signature, only finitely many functions can be computed with a fixed gate budget,
even when the carrier is infinite. The set `computableFunctions I n s` of scalar functions whose
`ecomplexity` is at most `s` is covered by the outputs of the finitely many programs of each
size, so it is finite and its cardinality is `Set.ncard`. Semantic equality and normalization
use classical reasoning.

After merging gates that compute the same function, a circuit with `g` gates has `g!` distinct
labeled presentations. This factorial correction sharpens the count used in Shannon's lower bound.
The main bound accepts any uniform bound on the number of lines;
`card_computableFunctions_mul_factorial_le_of_arity_le` specializes it to operation arities.
`card_computableFunctions_full_mul_factorial_le` uses the exact full-basis line count,
keeping the number of operation tables explicit when the arity varies.
-/

@[expose] public section

namespace Cslib.Circuits

open scoped BigOperators

universe v u
variable {σ : Signature.{v}} {U : Type u}
variable {I : Interpretation σ U} {n g s : ℕ}

/-- Scalar functions computable with at most `s` gates. -/
def computableFunctions (I : Interpretation σ U) (n s : ℕ) : Set ((Fin n → U) → U) :=
  {f | ∃ c : Circuit σ n 1, c.Computes I (single f) ∧ c.size ≤ s}

@[simp] theorem mem_computableFunctions {f : (Fin n → U) → U} :
    f ∈ computableFunctions I n s ↔
      ∃ c : Circuit σ n 1, c.Computes I (single f) ∧ c.size ≤ s :=
  Iff.rfl

/-- The functions computable with at most `s` gates are those of complexity at most `s`. -/
theorem mem_computableFunctions_iff_ecomplexity_le {f : (Fin n → U) → U} :
    f ∈ computableFunctions I n s ↔ ecomplexity I (single f) ≤ s := by
  rw [mem_computableFunctions, ecomplexity_le_iff]

/-- Every function computable within a gate budget over a finite signature is the output of one
of the finitely many programs of some size within the budget, so there are finitely many of them
even when the carrier is infinite. -/
instance [Finite σ.Op] : Finite (computableFunctions I n s) := by
  refine Set.Finite.to_subtype ((Set.finite_iUnion fun g : Fin (s + 1) =>
    Set.finite_range fun p : Program σ n g × Wire n g => p.1.wireFunction I p.2).subset ?_)
  rintro f ⟨c, hc, hs⟩
  exact Set.mem_iUnion.mpr ⟨⟨c.size, Nat.lt_succ_of_le hs⟩, (c.program, c.outputs 0),
    funext fun x => congrFun (hc x) 0⟩

/-- Functions computed by a circuit whose `g` gates compute pairwise distinct functions.
Permuting the gates of such a circuit, ignoring their order, gives `g!` distinct gate lists;
this is the factorial saving in the counting bound. -/
def irredundantFunctions (I : Interpretation σ U) (n g : ℕ) : Set ((Fin n → U) → U) :=
  {f | ∃ c : Circuit σ n 1, c.Computes I (single f) ∧ c.Irredundant I ∧ c.size = g}

@[simp] theorem mem_irredundantFunctions {f : (Fin n → U) → U} :
    f ∈ irredundantFunctions I n g ↔
      ∃ c : Circuit σ n 1, c.Computes I (single f) ∧ c.Irredundant I ∧ c.size = g :=
  Iff.rfl

instance [Finite σ.Op] : Finite (irredundantFunctions I n g) :=
  Set.Finite.to_subtype <| (computableFunctions I n g).toFinite.subset
    fun _ ⟨c, hc, _, hg⟩ => ⟨c, hc, hg.le⟩

private theorem mem_irredundantFunctions_iff {f : (Fin n → U) → U} :
    f ∈ irredundantFunctions I n g ↔ ∃ p : Program σ n g × Wire n g,
      (∀ x, p.1.trace I x p.2 = f x) ∧ p.1.Irredundant I := by
  constructor
  · rintro ⟨c, hf, hi, rfl⟩
    exact ⟨(c.program, c.outputs 0), fun x => congrFun (hf x) 0, hi⟩
  · rintro ⟨⟨p, w⟩, hf, hi⟩
    exact ⟨⟨p, fun _ => w⟩, fun x => funext fun _ => hf x, hi, rfl⟩

section Relabeling

-- Gate equations and an output wire, without a topological ordering.
private abbrev Presentation (n g : ℕ) := (Fin g → Line σ n g) × Wire n g

private def relabel (c : Program σ n g × Wire n g) (π : Equiv.Perm (Fin g)) :
    Presentation (σ := σ) n g :=
  (fun a => (c.1.lines (π.symm a)).mapWires (Wire.Renaming.ofPermutation π),
    Wire.Renaming.ofPermutation π c.2)

private theorem relabel_line_eval (c : Program σ n g × Wire n g) (π : Equiv.Perm (Fin g))
    (x : Fin n → U) (v : Fin g → U) (a : Fin g) :
    ((relabel c π).1 a).eval I x v =
      (c.1.lines (π.symm a)).eval I x (v ∘ π) :=
  Line.eval_mapRenaming _ _ _ _ _ _ fun _ => rfl

private theorem relabel_unique (c : Program σ n g × Wire n g) (π : Equiv.Perm (Fin g))
    (x : Fin n → U) (v : Fin g → U)
    (h : ∀ a, ((relabel c π).1 a).eval I x v = v a) :
    v = c.1.eval I x ∘ π.symm := by
  have hv : v ∘ π = c.1.eval I x :=
    c.1.eq_eval_of_forall_lines_eval I x _ (fun a => by
      simpa [relabel_line_eval] using h (π a))
  funext a
  simpa using congrFun hv (π.symm a)

private theorem relabel_output (c : Program σ n g × Wire n g) (π : Equiv.Perm (Fin g))
    (x : Fin n → U) :
    Wire.elim x (c.1.eval I x ∘ π.symm) (relabel c π).2 = c.1.trace I x c.2 := by
  apply Wire.Renaming.value_apply
  intro gate
  simp [Wire.Renaming.ofPermutation, Function.comp_def]

end Relabeling

private noncomputable def representative (f : irredundantFunctions I n g) :
    Program σ n g × Wire n g :=
  (mem_irredundantFunctions_iff.mp f.property).choose

private theorem representative_spec (f : irredundantFunctions I n g) :
    (∀ x, (representative f).1.trace I x (representative f).2 = f.1 x) ∧
      (representative f).1.Irredundant I :=
  (mem_irredundantFunctions_iff.mp f.property).choose_spec

-- Equal presentations determine the function; distinct gate functions determine the labels.
private theorem relabel_injective : Function.Injective
    (fun p : irredundantFunctions I n g × Equiv.Perm (Fin g) =>
      relabel (representative p.1) p.2) := by
  rintro ⟨f, π⟩ ⟨f', τ⟩ heq
  dsimp only at heq
  have hvalues (x : Fin n → U) :
      (representative f).1.eval I x ∘ π.symm =
        (representative f').1.eval I x ∘ τ.symm := by
    apply relabel_unique
    intro a
    rw [← heq, relabel_line_eval]
    simpa [Function.comp_def] using
      (representative f).1.lines_eval I x (π.symm a)
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

variable [Finite σ.Op]

/-- Distinct functions and permutations of their irredundant gates give distinct presentations. -/
theorem card_irredundantFunctions_mul_factorial_le (I : Interpretation σ U) (n g : ℕ) :
    (irredundantFunctions I n g).ncard * g.factorial ≤
      Nat.card (Line σ n g) ^ g * (n + g) := by
  have h := Nat.card_le_card_of_injective _ (relabel_injective (I := I) (n := n) (g := g))
  simpa only [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fun, Nat.card_fin,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, Wire.card] using h

/-- Normalizing a circuit with at most `s` gates leaves an irredundant circuit with at most `s`
gates computing the same function. -/
theorem card_computableFunctions_le_sum (I : Interpretation σ U) (n s : ℕ) :
    (computableFunctions I n s).ncard ≤
      ∑ g ∈ Finset.range (s + 1), (irredundantFunctions I n g).ncard := by
  induction s with
  | zero =>
    rw [Finset.sum_range_one]
    refine Set.ncard_le_ncard ?_
    rintro f ⟨c, hc, hs⟩
    obtain ⟨d, hd, hinj, hk⟩ := c.exists_irredundant I
    exact ⟨d, fun x => (congrFun hd x).trans (hc x), hinj, by lia⟩
  | succ s ih =>
    rw [Finset.sum_range_succ]
    refine ((Set.ncard_le_ncard (t := computableFunctions I n s ∪
      irredundantFunctions I n (s + 1)) ?_).trans (Set.ncard_union_le _ _)).trans
      (Nat.add_le_add_right ih _)
    rintro f ⟨c, hc, hs⟩
    obtain ⟨d, hd, hinj, hk⟩ := c.exists_irredundant I
    have hdc : d.Computes I (single f) := fun x => (congrFun hd x).trans (hc x)
    rcases Nat.lt_or_ge d.size (s + 1) with hlt | hge
    · exact Or.inl ⟨d, hdc, Nat.le_of_lt_succ hlt⟩
    · exact Or.inr ⟨d, hdc, hinj, le_antisymm (hk.trans hs) hge⟩

/-- Bound the number of computable functions using a uniform line count `B`. The condition
`s ≤ B` absorbs the extra factorial factors from circuits with fewer than `s` gates. -/
theorem card_computableFunctions_mul_factorial_le (I : Interpretation σ U) (n s B : ℕ)
    (hB : s ≤ B) (hlines : ∀ g ≤ s, Nat.card (Line σ n g) ≤ B) :
    (computableFunctions I n s).ncard * s.factorial ≤
      (s + 1) * B ^ s * (n + s) := by
  have hterm (g : ℕ) (hg : g ≤ s) :
      (irredundantFunctions I n g).ncard * s.factorial ≤ B ^ s * (n + s) := by
    calc
      (irredundantFunctions I n g).ncard * s.factorial =
          ((irredundantFunctions I n g).ncard * g.factorial) *
            (g + 1).ascFactorial (s - g) := by
        rw [mul_assoc, Nat.factorial_mul_ascFactorial, Nat.add_sub_of_le hg]
      _ ≤ (Nat.card (Line σ n g) ^ g * (n + g)) * s ^ (s - g) :=
        Nat.mul_le_mul (card_irredundantFunctions_mul_factorial_le I n g)
          (by simpa [Nat.add_sub_of_le hg] using Nat.ascFactorial_le_pow_add g (s - g))
      _ ≤ (B ^ g * (n + s)) * B ^ (s - g) := by gcongr; exact hlines g hg
      _ = B ^ s * (n + s) := by rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hg]
  calc
    (computableFunctions I n s).ncard * s.factorial ≤
        (∑ g ∈ Finset.range (s + 1), (irredundantFunctions I n g).ncard) * s.factorial :=
      Nat.mul_le_mul_right _ (card_computableFunctions_le_sum I n s)
    _ ≤ ∑ _g ∈ Finset.range (s + 1), B ^ s * (n + s) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun g hg => hterm g (Nat.le_of_lt_succ (Finset.mem_range.mp hg))
    _ = (s + 1) * B ^ s * (n + s) := by simp [mul_assoc]

/-- A cardinality bound for any finite signature with bounded arities. The maximum also
covers empty signatures and signatures containing only nullary operations. -/
theorem card_computableFunctions_mul_factorial_le_of_arity_le
    (I : Interpretation σ U) (n s r : ℕ) (arity_le : ∀ op, σ.Arity op ≤ r) :
    (computableFunctions I n s).ncard * s.factorial ≤
      (s + 1) * (max s (Nat.card σ.Op * (n + s + 1) ^ r)) ^ s * (n + s) := by
  apply card_computableFunctions_mul_factorial_le I n s _ (Nat.le_max_left _ _)
  intro g hg
  exact (Line.card_le n g r arity_le).trans
    ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : n + g + 1 ≤ n + s + 1) r)).trans
      (Nat.le_max_right _ _))

/-- The full-basis count keeps the number of operation tables explicit, so the arity may
vary along with the number of inputs and the gate budget. -/
theorem card_computableFunctions_full_mul_factorial_le [Finite U]
    (k n s : ℕ) :
    (computableFunctions (fullInterpretation (k := k) (Carrier := U)) n s).ncard * s.factorial ≤
      (s + 1) * (max s (Nat.card U ^ (Nat.card U ^ k) * (n + s) ^ k +
        Nat.card U)) ^ s * (n + s) := by
  apply card_computableFunctions_mul_factorial_le _ n s _ (Nat.le_max_left _ _)
  intro g hg
  apply le_trans ?_ (Nat.le_max_right _ _)
  rw [Line.card_full]
  gcongr

end Cslib.Circuits
