/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Semantic circuit normalization

Merging gates that compute the same function preserves wire values and does not
increase circuit size.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n g m : ℕ} {U : Type*}

/-- Distinct gates compute distinct scalar functions. Gates may still duplicate input
functions or be unused by the outputs. -/
def Program.Irredundant (p : Program σ n g) (i : Interpretation σ U) : Prop :=
  Function.Injective (p.gateFunction i)

/-- A circuit is irredundant when its internal gates compute pairwise distinct functions. -/
def Circuit.Irredundant (c : Circuit σ n g m) (i : Interpretation σ U) : Prop :=
  c.program.Irredundant i

/-- A program can be rebuilt with distinct gate functions, preserving every wire's value. -/
theorem Program.exists_irredundant (p : Program σ n g) (i : Interpretation σ U) :
    ∃ k ≤ g, ∃ q : Program σ n k, ∃ ρ : Wire.Renaming n g k,
      (∀ x w, q.trace i x (ρ w) = p.trace i x w) ∧
        q.Irredundant i := by
  classical
  induction p with
  | empty =>
      exact ⟨0, le_rfl, .empty, .id, by simp, fun w => Fin.elim0 w⟩
  | @gate g p line ih =>
      obtain ⟨k, hk, q, ρ, hρ, hq⟩ := ih
      let l := line.mapWires ρ
      have hl (x) : l.eval i x (q.eval i x) = line.eval i x (p.eval i x) :=
        line.eval_mapWires ρ i x x (p.eval i x) (q.eval i x) (hρ x)
      by_cases h : ∃ w, q.gateFunction i w = fun x => l.eval i x (q.eval i x)
      · obtain ⟨w, hw⟩ := h
        refine ⟨k, by omega, q, ρ.skipLast (Wire.gate w), ?_, hq⟩
        intro x v
        refine Wire.lastCases ?_ (fun v => ?_) v
        · simpa using (congrFun hw x).trans (hl x)
        · simpa using hρ x v
      · refine ⟨k + 1, by omega, q.gate l, ρ.appendLast, ?_, ?_⟩
        · intro x v
          refine Wire.lastCases ?_ (fun v => ?_) v
          · simpa using hl x
          · simpa using hρ x v
        · change Function.Injective ((q.gate l).gateFunction i)
          convert Fin.snoc_injective_of_injective hq h using 1
          ext gate x
          refine Fin.lastCases ?_ (fun gate => ?_) gate <;> simp

/-- Every circuit has an equivalent circuit with distinct gate functions and no more gates. -/
theorem Circuit.exists_irredundant (c : Circuit σ n g m) (i : Interpretation σ U) :
    ∃ k ≤ g, ∃ d : Circuit σ n k m,
      d.eval i = c.eval i ∧ d.Irredundant i := by
  obtain ⟨k, hk, q, ρ, hρ, hq⟩ := c.program.exists_irredundant i
  exact ⟨k, hk, ⟨q, ρ ∘ c.outputs⟩, funext fun x => funext fun o => hρ x (c.outputs o), hq⟩

end Cslib.Circuits
