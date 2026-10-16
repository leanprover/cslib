/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Full
public import Mathlib.Algebra.Order.Floor.Div

/-!
# Aggregation in the full basis

A gate of arity `k > 1` folds up to `k - 1` available values into an accumulator.
Thus a product or sum of `z > 0` available values costs at most
`(z - 1) ⌈/⌉ (k - 1)` gates. The fold construction needs no algebraic laws.
-/

@[expose] public section

namespace Cslib.Circuits.Synthesis

variable {U : Type*} {n k b : ℕ} {s : Set ((Fin n → U) → U)}

/-- Fold at most `b * (k - 1)` available values into an available accumulator
using at most `b` gates. No algebraic laws are required of `op`. -/
theorem full_foldl_of_length_le (hk : 1 < k) (op : U → U → U)
    (fs : List ((Fin n → U) → U)) (seed : (Fin n → U) → U)
    (hseed : seed ∈ s) (hfs : ∀ f ∈ fs, f ∈ s) (hb : fs.length ≤ b * (k - 1)) :
    Synthesis (fullInterpretation (k := k)) s
      {fun x => fs.foldl (fun acc f => op acc (f x)) (seed x)} b := by
  induction b generalizing s seed fs with
  | zero =>
    have he : fs = [] := List.length_eq_zero_iff.mp (by simpa using hb)
    simpa [he] using of_mem hseed
  | succ b ih =>
    let front := fs.take (k - 1)
    let rest := fs.drop (k - 1)
    let next := fun x => front.foldl (fun acc f => op acc (f x)) (seed x)
    have hgate : Synthesis (fullInterpretation (k := k)) s {next} 1 := by
      have h := full_gate (s := s) (show front.length + 1 ≤ k by simp [front]; lia)
        (fun v : Fin (front.length + 1) → U =>
          (List.ofFn fun i : Fin front.length => v i.succ).foldl op (v 0))
        (Fin.cons seed fun i => front[i.val]) (fun i => ?_)
      · simpa [next, List.foldl_map,
          fun x => List.ofFn_getElem_eq_map front (fun f => f x)] using h
      · refine Fin.cases hseed (fun i => ?_) i
        exact hfs _ (List.mem_of_mem_take (List.getElem_mem _))
    have hrest : rest.length ≤ b * (k - 1) := by
      simp only [rest, List.length_drop]
      simp only [Nat.succ_mul] at hb
      lia
    have h := hgate.trans (ih rest next (by simp) (fun f hf =>
      Set.mem_union_left _ (hfs f (List.mem_of_mem_drop hf))) hrest)
    simpa [next, rest, front, ← List.foldl_append, List.take_append_drop,
      Nat.add_comm] using h

/-- Fold available values using ceiling division for the gate budget. -/
theorem full_foldl (hk : 1 < k) (op : U → U → U)
    (fs : List ((Fin n → U) → U)) (seed : (Fin n → U) → U)
    (hseed : seed ∈ s) (hfs : ∀ f ∈ fs, f ∈ s) :
    Synthesis (fullInterpretation (k := k)) s
      {fun x => fs.foldl (fun acc f => op acc (f x)) (seed x)} (fs.length ⌈/⌉ (k - 1)) := by
  apply full_foldl_of_length_le hk op fs seed hseed hfs
  simpa [smul_eq_mul, Nat.mul_comm] using
    (le_smul_ceilDiv (b := fs.length) (show 0 < k - 1 by lia))

/-- Multiply a nonempty list of available values with one gate per `k - 1` additional values. -/
@[to_additive /-- Sum a nonempty list of available values with one gate per `k - 1`
additional values. -/]
theorem full_prod [Monoid U] (hk : 1 < k) (fs : List ((Fin n → U) → U))
    (hne : fs ≠ []) (hfs : ∀ f ∈ fs, f ∈ s) :
    Synthesis (fullInterpretation (k := k)) s
      {fun x => (fs.map (fun f => f x)).prod} ((fs.length - 1) ⌈/⌉ (k - 1)) := by
  cases fs with
  | nil => contradiction
  | cons seed fs =>
    simpa [List.prod_eq_foldl, List.foldl_map] using
      full_foldl hk (· * ·) fs seed (hfs seed (by simp)) (fun f hf => hfs f (by simp [hf]))

end Cslib.Circuits.Synthesis
