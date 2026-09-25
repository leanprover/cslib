/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Complexity

/-!
# Relative circuit complexity

The complexity `C(F | G)` of `F` relative to `G` is the least number of gates needed to compute
`F` when the values of `G` come for free: the circuit reads an input `x` followed by the values
`G x`. Such a circuit only ever sees inputs of this form, which make up the graph of `G`, so
computing `F` given `G` is computing `F` of the first part of the input, on the graph of `G`.
Relative complexity is therefore a complexity on a support:
`C(F | G) = C^Γ(F ∘ π)`, where `Γ` is the graph of `G` and `π` forgets the values of `G`.

The rules of relative complexity follow from this identity and the calculus of support
complexity. Knowing `G` never makes `F` harder, and knowing more never makes it harder either.
Computing `G` and then `F` from it gives the chain rule `C(F) ≤ C(G) + C(F | G)`, and its
variant for computing `F` and `G` together. Relative complexity satisfies the triangle
inequality `C(F | H) ≤ C(G | H) + C(F | G)`, and every function is free given itself.
-/

@[expose] public section

namespace Cslib.Circuits

universe v u
variable {σ : Signature.{v}} {U : Type u} {n m k l : ℕ}

/-- The graph of `G`: every input followed by the values of `G` on it. -/
def graph (G : (Fin n → U) → Fin k → U) : Set (Fin (n + k) → U) :=
  Set.range fun x => Fin.append x (G x)

/-- The complexity `C(F | G)` of `F` relative to `G`: the least size of a circuit that, reading
an input followed by the values of `G` on it, outputs the values of `F` on that input; `⊤` if
there is none. -/
noncomputable def ecomplexityGiven (I : Interpretation σ U) (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin k → U) : ℕ∞ :=
  ⨅ c : {c : Circuit σ (n + k) m // ∀ x, c.eval I (Fin.append x (G x)) = F x}, (c.1.size : ℕ∞)

/-- The complexity of `F` relative to `G` as a natural number, which is `0` when no circuit
computes `F` given `G`. -/
noncomputable def complexityGiven (I : Interpretation σ U) (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin k → U) : ℕ :=
  (ecomplexityGiven I F G).toNat

variable {I : Interpretation σ U}

/-- Relative complexity is complexity on the graph: computing `F` given `G` is computing `F` of
the first `n` inputs on the graph of `G`. -/
theorem ecomplexityGiven_eq_ecomplexityOn_graph (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin k → U) :
    ecomplexityGiven I F G = ecomplexityOn I (graph G) (fun z => F (z ∘ Fin.castAdd k)) := by
  have h (c : Circuit σ (n + k) m) :
      (∀ x, c.eval I (Fin.append x (G x)) = F x) ↔
        c.ComputesOn I (graph G) (fun z => F (z ∘ Fin.castAdd k)) := by
    constructor
    · rintro hc _ ⟨x, rfl⟩
      simpa using hc x
    · intro hc x
      simpa using hc _ ⟨x, rfl⟩
  apply le_antisymm
  · exact le_iInf fun c => iInf_le_of_le ⟨c.1, (h c.1).mpr c.2⟩ le_rfl
  · exact le_iInf fun c => iInf_le_of_le ⟨c.1, (h c.1).mp c.2⟩ le_rfl

/-- Keeping the input while computing `G` costs no more than computing `G`. -/
theorem ecomplexity_append_self_le (G : (Fin n → U) → Fin k → U) :
    ecomplexity I (fun x => Fin.append x (G x)) ≤ ecomplexity I G := by
  have h := ecomplexityOn_append_le (I := I) (S := Set.univ) (fun x => x ∘ id) G
  rw [ecomplexityOn_wiring, zero_add] at h
  exact h

/-- Knowing `G` never makes `F` harder: `C(F | G) ≤ C(F)`. -/
theorem ecomplexityGiven_le_ecomplexity (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin k → U) : ecomplexityGiven I F G ≤ ecomplexity I F := by
  rw [ecomplexityGiven_eq_ecomplexityOn_graph]
  exact (ecomplexityOn_comp_wiring_le (Fin.castAdd k) F).trans ecomplexityOn_le_ecomplexity

/-- The chain rule: computing `G` and then `F` from it gives `C(F) ≤ C(G) + C(F | G)`. -/
theorem ecomplexity_le_add_ecomplexityGiven (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin k → U) :
    ecomplexity I F ≤ ecomplexity I G + ecomplexityGiven I F G := by
  have hF : F = (fun z => F (z ∘ Fin.castAdd k)) ∘ fun x => Fin.append x (G x) := by
    funext x
    simp
  calc ecomplexity I F
      = ecomplexityOn I Set.univ
          ((fun z => F (z ∘ Fin.castAdd k)) ∘ fun x => Fin.append x (G x)) :=
        congrArg (ecomplexityOn I Set.univ) hF
    _ ≤ ecomplexity I (fun x => Fin.append x (G x)) +
          ecomplexityOn I (graph G) (fun z => F (z ∘ Fin.castAdd k)) := by
        have h := ecomplexityOn_comp_le (I := I) (S := Set.univ)
          (fun x => Fin.append x (G x)) (fun z => F (z ∘ Fin.castAdd k))
        rw [Set.image_univ] at h
        exact h
    _ ≤ ecomplexity I G + ecomplexityGiven I F G := by
        rw [ecomplexityGiven_eq_ecomplexityOn_graph]
        exact add_le_add (ecomplexity_append_self_le G) le_rfl

/-- Computing `F` and `G` together costs at most computing `F` and then `G` given `F`. -/
theorem ecomplexity_append_le_add_ecomplexityGiven (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin k → U) :
    ecomplexity I (fun x => Fin.append (F x) (G x)) ≤ ecomplexity I F + ecomplexityGiven I G F := by
  have hFG : (fun x => Fin.append (F x) (G x)) =
      (fun z => Fin.append (z ∘ Fin.natAdd n) (G (z ∘ Fin.castAdd m))) ∘
        fun x => Fin.append x (F x) := by
    funext x
    simp
  calc ecomplexity I (fun x => Fin.append (F x) (G x))
      = ecomplexityOn I Set.univ
          ((fun z => Fin.append (z ∘ Fin.natAdd n) (G (z ∘ Fin.castAdd m))) ∘
            fun x => Fin.append x (F x)) :=
        congrArg (ecomplexityOn I Set.univ) hFG
    _ ≤ ecomplexity I (fun x => Fin.append x (F x)) +
          ecomplexityOn I (graph F)
            (fun z => Fin.append (z ∘ Fin.natAdd n) (G (z ∘ Fin.castAdd m))) := by
        have h := ecomplexityOn_comp_le (I := I) (S := Set.univ)
          (fun x => Fin.append x (F x))
          (fun z => Fin.append (z ∘ Fin.natAdd n) (G (z ∘ Fin.castAdd m)))
        rw [Set.image_univ] at h
        exact h
    _ ≤ ecomplexity I F + ecomplexityGiven I G F := by
        refine add_le_add (ecomplexity_append_self_le F) ?_
        rw [ecomplexityGiven_eq_ecomplexityOn_graph]
        have h := ecomplexityOn_append_le (I := I) (S := graph F)
          (fun z => z ∘ Fin.natAdd n) (fun z => G (z ∘ Fin.castAdd m))
        rwa [ecomplexityOn_wiring, zero_add] at h

/-- The triangle inequality: `C(F | H) ≤ C(G | H) + C(F | G)`. Given `H`, compute `G`, and then
`F` from `G`. -/
theorem ecomplexityGiven_le_add (F : (Fin n → U) → Fin m → U) (G : (Fin n → U) → Fin k → U)
    (H : (Fin n → U) → Fin l → U) :
    ecomplexityGiven I F H ≤ ecomplexityGiven I G H + ecomplexityGiven I F G := by
  simp only [ecomplexityGiven_eq_ecomplexityOn_graph]
  let Φ : (Fin (n + l) → U) → Fin (n + k) → U :=
    fun z => Fin.append (z ∘ Fin.castAdd l) (G (z ∘ Fin.castAdd l))
  have hcomp : (fun z => F (z ∘ Fin.castAdd l)) = (fun w => F (w ∘ Fin.castAdd k)) ∘ Φ := by
    funext z
    simp [Φ]
  have himage : Φ '' graph H = graph G := by
    rw [graph, ← Set.range_comp]
    congr 1
    funext x
    simp [Φ]
  calc ecomplexityOn I (graph H) (fun z => F (z ∘ Fin.castAdd l))
      = ecomplexityOn I (graph H) ((fun w => F (w ∘ Fin.castAdd k)) ∘ Φ) := by rw [hcomp]
    _ ≤ ecomplexityOn I (graph H) Φ +
          ecomplexityOn I (Φ '' graph H) (fun w => F (w ∘ Fin.castAdd k)) :=
        ecomplexityOn_comp_le _ _
    _ ≤ ecomplexityOn I (graph H) (fun z => G (z ∘ Fin.castAdd l)) +
          ecomplexityOn I (graph G) (fun w => F (w ∘ Fin.castAdd k)) := by
        rw [himage]
        refine add_le_add ?_ le_rfl
        have h := ecomplexityOn_append_le (I := I) (S := graph H)
          (fun z => z ∘ Fin.castAdd l) (fun z => G (z ∘ Fin.castAdd l))
        rwa [ecomplexityOn_wiring, zero_add] at h

/-- Every function is free given itself: `C(F | F) = 0`. -/
@[simp] theorem ecomplexityGiven_self (F : (Fin n → U) → Fin m → U) :
    ecomplexityGiven I F F = 0 := by
  rw [ecomplexityGiven_eq_ecomplexityOn_graph]
  refine (ecomplexityOn_congr ?_).trans (ecomplexityOn_wiring (Fin.natAdd n))
  rintro _ ⟨x, rfl⟩
  simp

@[simp] theorem complexityGiven_self (F : (Fin n → U) → Fin m → U) :
    complexityGiven I F F = 0 := by
  simp [complexityGiven]

/-- Knowing more never makes `F` harder: `C(F | G, G') ≤ C(F | G)`. -/
theorem ecomplexityGiven_append_le (F : (Fin n → U) → Fin m → U) (G : (Fin n → U) → Fin k → U)
    (G' : (Fin n → U) → Fin l → U) :
    ecomplexityGiven I F (fun x => Fin.append (G x) (G' x)) ≤ ecomplexityGiven I F G := by
  have hG : ecomplexityGiven I G (fun x => Fin.append (G x) (G' x)) = 0 := by
    rw [ecomplexityGiven_eq_ecomplexityOn_graph]
    refine (ecomplexityOn_congr ?_).trans
      (ecomplexityOn_wiring fun j => Fin.natAdd n (Fin.castAdd l j))
    rintro _ ⟨x, rfl⟩
    funext j
    simp
  simpa [hG] using ecomplexityGiven_le_add (I := I) F G (fun x => Fin.append (G x) (G' x))

/-! ### Over a complete basis -/

section Complete

variable [I.IsComplete]

theorem ecomplexityGiven_ne_top (F : (Fin n → U) → Fin m → U) (G : (Fin n → U) → Fin k → U) :
    ecomplexityGiven I F G ≠ ⊤ :=
  ne_top_of_le_ne_top ecomplexity_ne_top (ecomplexityGiven_le_ecomplexity F G)

@[simp] theorem natCast_complexityGiven (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin k → U) : (complexityGiven I F G : ℕ∞) = ecomplexityGiven I F G :=
  ENat.natCast_toNat (ecomplexityGiven_ne_top F G)

theorem complexityGiven_le_complexity (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin k → U) : complexityGiven I F G ≤ complexity I F := by
  have := ecomplexityGiven_le_ecomplexity (I := I) F G
  rw [← natCast_complexityGiven, ← natCast_complexity] at this
  exact_mod_cast this

theorem complexity_le_add_complexityGiven (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin k → U) :
    complexity I F ≤ complexity I G + complexityGiven I F G := by
  have := ecomplexity_le_add_ecomplexityGiven (I := I) F G
  rw [← natCast_complexityGiven, ← natCast_complexity, ← natCast_complexity] at this
  exact_mod_cast this

theorem complexity_append_le_add_complexityGiven (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin k → U) :
    complexity I (fun x => Fin.append (F x) (G x)) ≤ complexity I F + complexityGiven I G F := by
  have := ecomplexity_append_le_add_ecomplexityGiven (I := I) F G
  rw [← natCast_complexityGiven, ← natCast_complexity, ← natCast_complexity] at this
  exact_mod_cast this

theorem complexityGiven_le_add (F : (Fin n → U) → Fin m → U) (G : (Fin n → U) → Fin k → U)
    (H : (Fin n → U) → Fin l → U) :
    complexityGiven I F H ≤ complexityGiven I G H + complexityGiven I F G := by
  have := ecomplexityGiven_le_add (I := I) F G H
  rw [← natCast_complexityGiven, ← natCast_complexityGiven, ← natCast_complexityGiven] at this
  exact_mod_cast this

theorem complexityGiven_append_le (F : (Fin n → U) → Fin m → U)
    (G : (Fin n → U) → Fin k → U) (G' : (Fin n → U) → Fin l → U) :
    complexityGiven I F (fun x => Fin.append (G x) (G' x)) ≤ complexityGiven I F G := by
  have := ecomplexityGiven_append_le (I := I) F G G'
  rw [← natCast_complexityGiven, ← natCast_complexityGiven] at this
  exact_mod_cast this

end Complete

end Cslib.Circuits
