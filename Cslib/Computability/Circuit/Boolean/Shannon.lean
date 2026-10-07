/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Shannon

/-!
# Shannon's lower bound for De Morgan circuits

This is the De Morgan specialization of `Cslib.Circuits.Shannon.exists_hard_function`,
stated for circuits and for circuit complexity. Together with Lupanov's construction, it
gives the asymptotically sharp gate count `2ⁿ/n`.
-/

public section

namespace Cslib.Circuits.Boolean.Shannon

/-- For all sufficiently large `n`, some Boolean function on `n` inputs requires
more than `2ⁿ/n` De Morgan gates, counting constants and negations. -/
theorem exists_hard_function :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : BooleanFunction n,
      ∀ c : Circuit signature n 1,
        c.Computes interpretation (single f) → 2 ^ n / (n : ℝ) < (c.size : ℝ) := by
  simpa [Nat.card_eq_fintype_card] using
    Circuits.Shannon.exists_hard_function interpretation (fun op => by cases op <;> simp)

/-- Shannon's lower bound for circuit complexity: for all sufficiently large `n`, some Boolean
function on `n` inputs has complexity more than `2ⁿ/n`. -/
theorem lt_complexity :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : BooleanFunction n,
      2 ^ n / (n : ℝ) < (complexity interpretation (single f) : ℝ) := by
  obtain ⟨N, hN⟩ := exists_hard_function
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨f, hf⟩ := hN n hn
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single f)
  exact ⟨f, by rw [← hsize]; exact hf c hc⟩

end Cslib.Circuits.Boolean.Shannon
