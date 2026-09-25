/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Complexity

/-!
# Relative circuit complexity

The complexity `C(f | g)` of `f` relative to `g` is the least number of gates needed to compute
`f` when the values of `g` come for free: the circuit reads an input `x` followed by the values
`g x`. Such a circuit only ever sees inputs of this form, which make up the graph of `g`, so
computing `f` given `g` is computing `f` of the first part of the input, on the graph of `g`.
Relative complexity is therefore a complexity on a support:
`C(f | g) = C^Γ(f ∘ π)`, where `Γ` is the graph of `g` and `π` forgets the values of `g`.

The rules of relative complexity follow from this identity and the calculus of support
complexity. Knowing `g` never makes `f` harder, and knowing more never makes it harder either.
Computing `g` and then `f` from it gives the chain rule `C(f) ≤ C(g) + C(f | g)`, and its
variant for computing `f` and `g` together. Relative complexity satisfies the triangle
inequality `C(f | h) ≤ C(g | h) + C(f | g)`, and every function is free given itself.
-/

@[expose] public section

namespace Cslib.Circuits

universe v u
variable {σ : Signature.{v}} {U : Type u} {n m k l : ℕ}

/-- The graph of `g`: every input followed by the values of `g` on it. -/
def graph (g : (Fin n → U) → Fin k → U) : Set (Fin (n + k) → U) :=
  Set.range fun x => Fin.append x (g x)

/-- The complexity `C(f | g)` of `f` relative to `g`: the least size of a circuit that, reading
an input followed by the values of `g` on it, outputs the values of `f` on that input; `⊤` if
there is none. -/
noncomputable def ecomplexityGiven (I : Interpretation σ U) (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) : ℕ∞ :=
  ⨅ c : {c : Circuit σ (n + k) m // ∀ x, c.eval I (Fin.append x (g x)) = f x}, (c.1.size : ℕ∞)

variable {I : Interpretation σ U}

/-- Relative complexity is complexity on the graph: computing `f` given `g` is computing `f` of
the first `n` inputs on the graph of `g`. -/
theorem ecomplexityGiven_eq_ecomplexityOn_graph (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) :
    ecomplexityGiven I f g = ecomplexityOn I (graph g) (fun z => f (z ∘ Fin.castAdd k)) := by
  have h (c : Circuit σ (n + k) m) :
      (∀ x, c.eval I (Fin.append x (g x)) = f x) ↔
        c.ComputesOn I (graph g) (fun z => f (z ∘ Fin.castAdd k)) := by
    constructor
    · rintro hc _ ⟨x, rfl⟩
      simpa using hc x
    · intro hc x
      simpa using hc ⟨x, rfl⟩
  apply le_antisymm
  · exact le_iInf fun c => iInf_le_of_le ⟨c.1, (h c.1).mpr c.2⟩ le_rfl
  · exact le_iInf fun c => iInf_le_of_le ⟨c.1, (h c.1).mp c.2⟩ le_rfl

/-- Keeping the input while computing `g` costs no more than computing `g`. -/
theorem ecomplexity_append_self_le (g : (Fin n → U) → Fin k → U) :
    ecomplexity I (fun x => Fin.append x (g x)) ≤ ecomplexity I g := by
  have h := ecomplexityOn_append_le (I := I) (S := Set.univ) (fun x => x ∘ id) g
  rw [ecomplexityOn_wiring, zero_add] at h
  exact h

/-- Knowing `g` never makes `f` harder: `C(f | g) ≤ C(f)`. -/
theorem ecomplexityGiven_le_ecomplexity (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) : ecomplexityGiven I f g ≤ ecomplexity I f := by
  rw [ecomplexityGiven_eq_ecomplexityOn_graph]
  exact (ecomplexityOn_comp_wiring_le (Fin.castAdd k) f).trans ecomplexityOn_le_ecomplexity

/-- The chain rule: computing `g` and then `f` from it gives `C(f) ≤ C(g) + C(f | g)`. -/
theorem ecomplexity_le_add_ecomplexityGiven (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) :
    ecomplexity I f ≤ ecomplexity I g + ecomplexityGiven I f g := by
  have hF : f = (fun z => f (z ∘ Fin.castAdd k)) ∘ fun x => Fin.append x (g x) := by
    funext x
    simp
  calc ecomplexity I f
      = ecomplexityOn I Set.univ
          ((fun z => f (z ∘ Fin.castAdd k)) ∘ fun x => Fin.append x (g x)) :=
        congrArg (ecomplexityOn I Set.univ) hF
    _ ≤ ecomplexity I (fun x => Fin.append x (g x)) +
          ecomplexityOn I (graph g) (fun z => f (z ∘ Fin.castAdd k)) := by
        have h := ecomplexityOn_comp_le (I := I) (S := Set.univ)
          (fun x => Fin.append x (g x)) (fun z => f (z ∘ Fin.castAdd k))
        rw [Set.image_univ] at h
        exact h
    _ ≤ ecomplexity I g + ecomplexityGiven I f g := by
        rw [ecomplexityGiven_eq_ecomplexityOn_graph]
        exact add_le_add (ecomplexity_append_self_le g) le_rfl

/-- Computing `f` and `g` together costs at most computing `f` and then `g` given `f`. -/
theorem ecomplexity_append_le_add_ecomplexityGiven (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) :
    ecomplexity I (fun x => Fin.append (f x) (g x)) ≤ ecomplexity I f + ecomplexityGiven I g f := by
  have hFG : (fun x => Fin.append (f x) (g x)) =
      (fun z => Fin.append (z ∘ Fin.natAdd n) (g (z ∘ Fin.castAdd m))) ∘
        fun x => Fin.append x (f x) := by
    funext x
    simp
  calc ecomplexity I (fun x => Fin.append (f x) (g x))
      = ecomplexityOn I Set.univ
          ((fun z => Fin.append (z ∘ Fin.natAdd n) (g (z ∘ Fin.castAdd m))) ∘
            fun x => Fin.append x (f x)) :=
        congrArg (ecomplexityOn I Set.univ) hFG
    _ ≤ ecomplexity I (fun x => Fin.append x (f x)) +
          ecomplexityOn I (graph f)
            (fun z => Fin.append (z ∘ Fin.natAdd n) (g (z ∘ Fin.castAdd m))) := by
        have h := ecomplexityOn_comp_le (I := I) (S := Set.univ)
          (fun x => Fin.append x (f x))
          (fun z => Fin.append (z ∘ Fin.natAdd n) (g (z ∘ Fin.castAdd m)))
        rw [Set.image_univ] at h
        exact h
    _ ≤ ecomplexity I f + ecomplexityGiven I g f := by
        refine add_le_add (ecomplexity_append_self_le f) ?_
        rw [ecomplexityGiven_eq_ecomplexityOn_graph]
        have h := ecomplexityOn_append_le (I := I) (S := graph f)
          (fun z => z ∘ Fin.natAdd n) (fun z => g (z ∘ Fin.castAdd m))
        rwa [ecomplexityOn_wiring, zero_add] at h

/-- The triangle inequality: `C(f | h) ≤ C(g | h) + C(f | g)`. Given `h`, compute `g`, and then
`f` from `g`. -/
theorem ecomplexityGiven_le_add (f : (Fin n → U) → Fin m → U) (g : (Fin n → U) → Fin k → U)
    (h : (Fin n → U) → Fin l → U) :
    ecomplexityGiven I f h ≤ ecomplexityGiven I g h + ecomplexityGiven I f g := by
  simp only [ecomplexityGiven_eq_ecomplexityOn_graph]
  let Φ : (Fin (n + l) → U) → Fin (n + k) → U :=
    fun z => Fin.append (z ∘ Fin.castAdd l) (g (z ∘ Fin.castAdd l))
  have hcomp : (fun z => f (z ∘ Fin.castAdd l)) = (fun w => f (w ∘ Fin.castAdd k)) ∘ Φ := by
    funext z
    simp [Φ]
  have himage : Φ '' graph h = graph g := by
    rw [graph, ← Set.range_comp]
    congr 1
    funext x
    simp [Φ]
  calc ecomplexityOn I (graph h) (fun z => f (z ∘ Fin.castAdd l))
      = ecomplexityOn I (graph h) ((fun w => f (w ∘ Fin.castAdd k)) ∘ Φ) := by rw [hcomp]
    _ ≤ ecomplexityOn I (graph h) Φ +
          ecomplexityOn I (Φ '' graph h) (fun w => f (w ∘ Fin.castAdd k)) :=
        ecomplexityOn_comp_le _ _
    _ ≤ ecomplexityOn I (graph h) (fun z => g (z ∘ Fin.castAdd l)) +
          ecomplexityOn I (graph g) (fun w => f (w ∘ Fin.castAdd k)) := by
        rw [himage]
        refine add_le_add ?_ le_rfl
        have h := ecomplexityOn_append_le (I := I) (S := graph h)
          (fun z => z ∘ Fin.castAdd l) (fun z => g (z ∘ Fin.castAdd l))
        rwa [ecomplexityOn_wiring, zero_add] at h

/-- Every function is free given itself: `C(f | f) = 0`. -/
@[simp] theorem ecomplexityGiven_self (f : (Fin n → U) → Fin m → U) :
    ecomplexityGiven I f f = 0 := by
  rw [ecomplexityGiven_eq_ecomplexityOn_graph]
  refine (ecomplexityOn_congr ?_).trans (ecomplexityOn_wiring (Fin.natAdd n))
  rintro _ ⟨x, rfl⟩
  simp

/-- Knowing more never makes `f` harder: `C(f | g, g') ≤ C(f | g)`. -/
theorem ecomplexityGiven_append_le (f : (Fin n → U) → Fin m → U) (g : (Fin n → U) → Fin k → U)
    (g' : (Fin n → U) → Fin l → U) :
    ecomplexityGiven I f (fun x => Fin.append (g x) (g' x)) ≤ ecomplexityGiven I f g := by
  have hG : ecomplexityGiven I g (fun x => Fin.append (g x) (g' x)) = 0 := by
    rw [ecomplexityGiven_eq_ecomplexityOn_graph]
    refine (ecomplexityOn_congr ?_).trans
      (ecomplexityOn_wiring fun j => Fin.natAdd n (Fin.castAdd l j))
    rintro _ ⟨x, rfl⟩
    funext j
    simp
  simpa [hG] using ecomplexityGiven_le_add (I := I) f g (fun x => Fin.append (g x) (g' x))

/-! ### Over a complete basis -/

section Complete

theorem ecomplexityGiven_ne_top [I.IsComplete] (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) : ecomplexityGiven I f g ≠ ⊤ :=
  ne_top_of_le_ne_top ecomplexity_ne_top (ecomplexityGiven_le_ecomplexity f g)

/-- The complexity `C(f | g)` of `f` relative to `g` over a complete basis, as a natural
number. -/
noncomputable def complexityGiven (I : Interpretation σ U) [I.IsComplete]
    (f : (Fin n → U) → Fin m → U) (g : (Fin n → U) → Fin k → U) : ℕ :=
  (ecomplexityGiven I f g).untop (ecomplexityGiven_ne_top f g)

variable [I.IsComplete]

@[simp] theorem natCast_complexityGiven (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) : (complexityGiven I f g : ℕ∞) = ecomplexityGiven I f g :=
  WithTop.coe_untop _ _

@[simp] theorem complexityGiven_self (f : (Fin n → U) → Fin m → U) :
    complexityGiven I f f = 0 := by
  have := ecomplexityGiven_self (I := I) f
  rw [← natCast_complexityGiven] at this
  exact_mod_cast this

theorem complexityGiven_le_complexity (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) : complexityGiven I f g ≤ complexity I f := by
  have := ecomplexityGiven_le_ecomplexity (I := I) f g
  rw [← natCast_complexityGiven, ← natCast_complexity] at this
  exact_mod_cast this

theorem complexity_le_add_complexityGiven (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) :
    complexity I f ≤ complexity I g + complexityGiven I f g := by
  have := ecomplexity_le_add_ecomplexityGiven (I := I) f g
  rw [← natCast_complexityGiven, ← natCast_complexity, ← natCast_complexity] at this
  exact_mod_cast this

theorem complexity_append_le_add_complexityGiven (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) :
    complexity I (fun x => Fin.append (f x) (g x)) ≤ complexity I f + complexityGiven I g f := by
  have := ecomplexity_append_le_add_ecomplexityGiven (I := I) f g
  rw [← natCast_complexityGiven, ← natCast_complexity, ← natCast_complexity] at this
  exact_mod_cast this

theorem complexityGiven_le_add (f : (Fin n → U) → Fin m → U) (g : (Fin n → U) → Fin k → U)
    (h : (Fin n → U) → Fin l → U) :
    complexityGiven I f h ≤ complexityGiven I g h + complexityGiven I f g := by
  have := ecomplexityGiven_le_add (I := I) f g h
  rw [← natCast_complexityGiven, ← natCast_complexityGiven, ← natCast_complexityGiven] at this
  exact_mod_cast this

theorem complexityGiven_append_le (f : (Fin n → U) → Fin m → U)
    (g : (Fin n → U) → Fin k → U) (g' : (Fin n → U) → Fin l → U) :
    complexityGiven I f (fun x => Fin.append (g x) (g' x)) ≤ complexityGiven I f g := by
  have := ecomplexityGiven_append_le (I := I) f g g'
  rw [← natCast_complexityGiven, ← natCast_complexityGiven] at this
  exact_mod_cast this

end Complete

end Cslib.Circuits
