/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Crypto.Primitives.PRG.Asymptotic

open Cslib.Crypto.PRG Cslib.Probability.PMF Filter
open scoped NNReal Topology

namespace CslibTests.PRG

-- Generators support ordinary function application and extensionality.
example {Seed Output : Type*} (G H : Generator Seed Output)
    (h : ∀ seed, G seed = H seed) : G = H := DFunLike.ext G H h

-- The identity generator is secure with zero error.
example : (Generator.mk (id : Bool → Bool)).Secure (fun _ => True) 0 := by
  apply Generator.secure_zero_of_outputDist_eq
  exact PMF.map_id _

-- Zero-error security implies uniform output.
example {Seed Output : Type*} [Fintype Seed] [Nonempty Seed]
    [Fintype Output] [Nonempty Output] (G : Generator Seed Output)
    (h : G.Secure (fun _ => True) 0) : G.outputDist = uniformOfFintype Output :=
  G.secure_zero_iff_outputDist_eq_uniform.mp h

example (G : Generator Bool (Bool × Bool)) (Admissible : Adversary (Bool × Bool) → Prop)
    {ε δ : ℝ≥0} (hεδ : ε ≤ δ) (h : G.Secure Admissible ε) : G.Secure Admissible δ :=
  Generator.Secure.mono hεδ h

-- Tests that ignore their input have zero advantage.
example (G : Generator Bool (Bool × Bool)) :
    G.Secure (fun adversary => ∃ p : PMF Bool, adversary = fun _ => p) 0 := by
  rintro adversary ⟨p, rfl⟩
  simp

-- Evaluate range membership for a diagonal map and for an empty seed space.
example : (Generator.mk (fun b : Bool => (b, b))).rangeTest (true, true) = true := by decide
example : (Generator.mk (fun b : Bool => (b, b))).rangeTest (false, true) = false := by decide
example : (Generator.mk (Fin.elim0 : Fin 0 → ℕ)).rangeTest 0 = false := by decide

-- Repeating a bit expands, and the range attack has exactly one-half advantage.
example : (Generator.mk (fun b : Bool => (b, b))).advantage
    (Generator.mk (fun b : Bool => (b, b))).rangeAdversary = 1 / 2 := by
  norm_num [Generator.advantage_rangeAdversary, Nat.card_eq_fintype_card]

-- A constant output gives the range test advantage 3/4.
example : (Generator.mk (fun _ : Bool => (false, false))).advantage
    (Generator.mk (fun _ : Bool => (false, false))).rangeAdversary = 3 / 4 := by
  rw [Generator.advantage_rangeAdversary]
  norm_num [Set.range_const]

-- No generator from Bool to Bool × Bool has zero error against all adversaries.
example : ¬ ∃ G : Generator Bool (Bool × Bool), G.Secure (fun _ => True) 0 := by
  rintro ⟨G, hG⟩
  exact G.not_secure_zero_of_isExpanding (by simp [Generator.IsExpanding]) hG

-- The identity family has zero distinguishing advantage.
example : Family.Secure (fun n => Generator.mk (id : (Fin n → Bool) → (Fin n → Bool)))
    (fun _ => True) := by
  have h : Family.SecureWithError
      (fun n => Generator.mk (id : (Fin n → Bool) → (Fin n → Bool)))
      (fun _ => True) (fun _ => 0) := by
    intro adversary_family _ n
    simp [Generator.advantage, Generator.realExperiment, Generator.idealExperiment,
      Generator.outputDist, PMF.map_id]
  exact h.secure (Asymptotics.superpolynomialDecay_zero _ _)

-- The inverse-polynomial gap 1 / (n + 2) rules out asymptotic security.
example (G : Family (fun n => Fin (n + 1)) (fun n => Fin (n + 2))) :
    ¬ G.Secure (fun _ => True) := by
  apply G.not_secure_of_rangeAdversary trivial (δ := fun n => 1 / ((n : ℝ≥0) + 2))
  · intro h
    have hlim : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using h 1
    have hle : (1 / 2 : ℝ) ≤ 0 := ge_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
      linarith)
    norm_num at hle
  · apply Eventually.of_forall
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hgap : (1 : ℝ) / ((n : ℝ) + 2) = 1 - ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
      field_simp
      ring
    calc
      _ ≤ 1 - Fintype.card (Fin (n + 1)) / (Fintype.card (Fin (n + 2)) : ℝ) := by
        simpa using hgap.le
      _ ≤ _ := by simpa only [Generator.advantage_rangeAdversary] using
        (G n).one_sub_card_div_le_advantage_rangeAdversary

-- A stretching bitstring generator is insecure against its range test.
example (G : Family (fun n => Fin n → Bool) (fun n => Fin (n + 1) → Bool)) :
    ¬ G.Secure (fun adversary_family => adversary_family = fun n => (G n).rangeAdversary) :=
  G.not_secure_of_bitstring_stretch rfl (Eventually.of_forall (by omega))

example (G : Family BitVec (fun n => BitVec (n + 1))) :
    ¬ G.Secure (fun adversary_family => adversary_family = fun n => (G n).rangeAdversary) :=
  G.not_secure_of_bitVec_stretch rfl (Eventually.of_forall (by omega))

-- No n-to-(n+1)-bit generator resists arbitrary adversary families.
example : ¬ ∃ G : Family (fun n => Fin n → Bool) (fun n => Fin (n + 1) → Bool),
    G.Secure (fun _ => True) :=
  Family.not_exists_secure_bitstring_stretch (Filter.Eventually.of_forall (by omega))

-- No n-to-(n+1)-bit BitVec family is secure against all adversaries.
example : ¬ ∃ G : Family BitVec (fun n => BitVec (n + 1)), G.Secure (fun _ => True) :=
  Family.not_exists_secure_bitVec_stretch (Filter.Eventually.of_forall (by omega))

end CslibTests.PRG
