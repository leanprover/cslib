/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Full
public import Mathlib.Data.Fintype.BigOperators

/-!
# Shared decoders in the full basis

A point indicator returns `marker` when the supplied coordinate functions match a
chosen tuple, and `default` otherwise. Coordinates may be arbitrary available
functions of the inputs, including repeated functions.

For gate arity at least two, `synthesis_indicators` builds all tuple indicators
together using at most `q + q^2 + ... + q^t` additional gates, where
`q = Fintype.card U`, assuming the marker constant and the `t` coordinates are
already available. It reuses indicators on the remaining coordinates, adding one
gate per tuple at each stage. These decoders supply the indicators for Lupanov's
shared lookup tables.
-/

@[expose] public section

namespace Cslib.Circuits.Full

variable {U : Type*} [DecidableEq U] {n k : ℕ}

/-- Return `marker` when the coordinates match `a`, and `default` otherwise. -/
def indicator (default marker : U) {t : ℕ}
    (coords : Fin t → (Fin n → U) → U) (a : Fin t → U) : (Fin n → U) → U :=
  fun x => if (fun i => coords i x) = a then marker else default

/-- Build all tuple indicators together, sharing the indicators on the remaining coordinates.
The marker constant must be available; the default value is encoded in each gate operation. -/
theorem synthesis_indicators [Fintype U] (hk : 2 ≤ k) (default marker : U)
    {s : Set ((Fin n → U) → U)} {t : ℕ} (coords : Fin t → (Fin n → U) → U)
    (hmarker : (fun _ => marker) ∈ s) (hcoords : ∀ i, coords i ∈ s) :
    Synthesis (fullInterpretation (k := k)) s (Set.range (indicator default marker coords))
      (∑ j ∈ Finset.range t, Fintype.card U ^ (j + 1)) := by
  induction t with
  | zero =>
    unfold indicator
    simpa [funext_iff] using Synthesis.of_mem (I := fullInterpretation (k := k)) hmarker
  | succ t ih =>
    have hnext (a : Fin (t + 1) → U) :=
      Synthesis.full_gate (s := s ∪ Set.range
        (indicator default marker (Fin.tail coords))) hk
        (fun w : Fin 2 → U => if w 0 = a 0 then w 1 else default)
        (Fin.cons (coords 0) (fun _ => indicator default marker (Fin.tail coords) (Fin.tail a)))
        (by simp [Fin.forall_fin_succ, hcoords])
    unfold indicator at hnext ⊢
    simpa [Fin.tail_def, funext_iff, Fin.forall_fin_succ, ite_and,
      Finset.sum_range_succ] using
      (ih (Fin.tail coords) (fun i => hcoords i.succ)).trans
        (Synthesis.family _ (fun _ => 1) hnext)

end Cslib.Circuits.Full
