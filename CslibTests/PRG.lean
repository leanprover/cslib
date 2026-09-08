/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Crypto.Primitives.PRG.Asymptotic

open Cslib.Crypto.PRG
open scoped NNReal

namespace CslibTests.PRG

-- Generators support ordinary function application and extensionality.
example {Seed Output : Type*} (G H : Generator Seed Output)
    (h : ∀ seed, G seed = H seed) : G = H := DFunLike.ext G H h

-- A nonexpanding generator can be perfectly secure, even against randomized tests.
example : (Generator.mk (id : Bool → Bool)).Secure (fun _ => True) 0 := by
  apply Generator.secure_zero_of_outputDist_eq
  exact PMF.map_id _

-- The game-based definition recovers distribution equality without an error term.
example {Seed Output : Type*} [Fintype Seed] [Nonempty Seed]
    [Fintype Output] [Nonempty Output] (G : Generator Seed Output)
    (h : G.Secure (fun _ => True) 0) : G.outputDist = PMF.uniformOfFintype Output :=
  G.secure_zero_iff_outputDist_eq_uniform.mp h

example (G : Generator Bool (Bool × Bool)) (Admissible : Adversary (Bool × Bool) → Prop)
    {ε δ : ℝ≥0} (hεδ : ε ≤ δ) (h : G.Secure Admissible ε) : G.Secure Admissible δ :=
  Generator.Secure.mono hεδ h

-- Admissibility can express an actual restricted class: tests ignoring their input.
example (G : Generator Bool (Bool × Bool)) :
    G.Secure (fun adversary => ∃ p : PMF Bool, adversary = fun _ => p) 0 := by
  rintro adversary ⟨p, rfl⟩
  simp

-- Repeating a bit expands, and the range attack has exactly one-half advantage.
example : (Generator.mk (fun b : Bool => (b, b))).advantage
    (Generator.mk (fun b : Bool => (b, b))).rangeAdversary = 1 / 2 := by
  norm_num [Generator.advantage_rangeAdversary, Nat.card_eq_fintype_card]

-- Collisions strengthen the attack: the range, not the number of seeds, determines advantage.
example : (Generator.mk (fun _ : Bool => (false, false))).advantage
    (Generator.mk (fun _ : Bool => (false, false))).rangeAdversary = 3 / 4 := by
  rw [Generator.advantage_rangeAdversary]
  norm_num [Set.range_const]

-- The finite impossibility theorem applies without choosing any implementation.
example : ¬ ∃ G : Generator Bool (Bool × Bool), G.Secure (fun _ => True) 0 := by
  rintro ⟨G, hG⟩
  exact G.not_secure_zero_of_isExpanding (by simp [Generator.IsExpanding]) hG

-- The asymptotic definition admits the identity family.
example : Family.Secure (fun n => Generator.mk (id : (Fin n → Bool) → (Fin n → Bool)))
    (fun _ => True) := by
  intro adversary _
  have hzero : ∀ n, (Generator.mk (id : (Fin n → Bool) → (Fin n → Bool))).advantage
      (adversary n) = 0 := by
    intro n
    simp [Generator.advantage, Generator.realExperiment, Generator.idealExperiment,
      Generator.outputDist, PMF.map_id]
  simp only [hzero]
  exact Asymptotics.superpolynomialDecay_zero _ _

-- No n-to-(n+1)-bit generator resists arbitrary adversary families.
example : ¬ ∃ G : Family (fun n => Fin n → Bool) (fun n => Fin (n + 1) → Bool),
    G.Secure (fun _ => True) :=
  Family.not_exists_secure_bitstring_stretch (Filter.Eventually.of_forall (by omega))

-- The same result uses the BitVec representation of the existing one-time pad API.
example : ¬ ∃ G : Family BitVec (fun n => BitVec (n + 1)), G.Secure (fun _ => True) :=
  Family.not_exists_secure_bitVec_stretch (Filter.Eventually.of_forall (by omega))

end CslibTests.PRG
