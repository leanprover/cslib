/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Full
public import Mathlib.Data.Fintype.BigOperators

/-!
# Shared dictionaries in the full basis

For `t` indicator functions `e i`, index `i` is active at input `x` when
`e i x = marker`. A prescription assigns a value `v i` to each index and returns
the first active index's value, or `default` if none is active. The dictionary
consists of the resulting functions as `v : Fin t → U` varies.

For gate arity at least two, `synthesis_prescriptions` builds the whole dictionary
with at most `q + q^2 + ... + q^t` additional gates, where `q = Fintype.card U`, assuming
the indicators and the default constant are already available. Each stage reuses
the dictionary on the remaining indicators and adds one gate per new assignment.
For disjoint indicators, these dictionaries supply the tables used in Lupanov's
block construction.
-/

@[expose] public section

namespace Cslib.Circuits.Full

variable {U : Type*} [DecidableEq U] {n k : ℕ}

/-- Return `v i` at the first index with `e i x = marker`, or `default` if none exists. -/
def prescription (default marker : U) :
    {t : ℕ} → (Fin t → (Fin n → U) → U) → (Fin t → U) → (Fin n → U) → U
  | 0, _, _, _ => default
  | _ + 1, e, v, x =>
      if e 0 x = marker then v 0 else prescription default marker (Fin.tail e) (Fin.tail v) x

/-- If no indicator equals `marker` at `x`, the prescription returns `default`. -/
theorem prescription_eq_default (default marker : U) {t : ℕ}
    (e : Fin t → (Fin n → U) → U) (v : Fin t → U) (x : Fin n → U)
    (h : ∀ i, e i x ≠ marker) : prescription default marker e v x = default := by
  induction t <;> simp_all [prescription, Fin.tail_def]

/-- If `i` is the only indicator equal to `marker` at `x`, the prescription returns `v i`. -/
theorem prescription_eq (default marker : U) {t : ℕ}
    (e : Fin t → (Fin n → U) → U) (v : Fin t → U) (x : Fin n → U) (i : Fin t)
    (hi : e i x = marker) (h : ∀ j, j ≠ i → e j x ≠ marker) :
    prescription default marker e v x = v i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    cases i using Fin.cases with
    | zero => simp [prescription, hi]
    | succ i =>
      simpa [prescription, Fin.tail_def, h 0 (Fin.succ_ne_zero i).symm] using
        ih _ _ i hi (fun j hj => h j.succ (by simpa using hj))

/-- Once the indicators and the constant `default` are available, compute all functions
`prescription default marker e v` together using at most `q + q^2 + ... + q^t` additional
gates, where `q = Fintype.card U`. The indicators may overlap. The marker and the assigned
values `v i` are encoded in the gate operations. -/
theorem synthesis_prescriptions [Fintype U] (hk : 2 ≤ k) (default marker : U)
    {s : Set ((Fin n → U) → U)} {t : ℕ} (e : Fin t → (Fin n → U) → U)
    (hdefault : (fun _ => default) ∈ s) (he : ∀ i, e i ∈ s) :
    Synthesis (fullInterpretation (k := k)) s (Set.range (prescription default marker e))
      (∑ j ∈ Finset.range t, Fintype.card U ^ (j + 1)) := by
  induction t with
  | zero =>
    simpa [prescription] using Synthesis.of_mem (I := fullInterpretation (k := k)) hdefault
  | succ t ih =>
    have hprev := ih (Fin.tail e) (fun i => he i.succ)
    have hnext (v : Fin (t + 1) → U) :
        Synthesis (fullInterpretation (k := k))
          (s ∪ Set.range (prescription default marker (Fin.tail e)))
          {prescription default marker e v} 1 := by
      refine Synthesis.full_gate hk
        (fun w : Fin 2 → U => if w 0 = marker then v 0 else w 1)
        (fun i => if i = 0 then e 0 else prescription default marker (Fin.tail e) (Fin.tail v)) ?_
      intro i
      split <;> simp [he]
    simpa [Finset.sum_range_succ] using
      hprev.trans (Synthesis.family (prescription default marker e) (fun _ => 1) hnext)

end Cslib.Circuits.Full
