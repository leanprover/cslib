/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.Modal.Semantics

namespace Cslib.Logic.Modal

open scoped InferenceSystem Proposition Satisfies

section Grind

variable {τ : PFunctor}
variable {World Atom : Type*}
variable {m : Model World τ Atom}

/-! ## Basic propositional connectives -/

example (h : ⇓Modal[m,w ⊨ ¬φ]) : ¬⇓Modal[m,w ⊨ φ] := by grind only [modal]

example (h : ⇓Modal[m,w ⊨ φ₁ ∧ φ₂]) : ⇓Modal[m,w ⊨ φ₁] := by
  grind only [modal]

example (h₁ : ⇓Modal[m,w ⊨ φ₁]) (h₂ : ⇓Modal[m,w ⊨ φ₂]) : ⇓Modal[m,w ⊨ φ₁ ∧ φ₂] := by
  grind only [modal]

example (h : ⇓Modal[m,w ⊨ φ₁ → φ₂]) (h₁ : ⇓Modal[m,w ⊨ φ₁]) : ⇓Modal[m,w ⊨ φ₂] := by
  grind only [modal]

example (h : ⇓Modal[m,w ⊨ φ₁ ↔ φ₂]) (h₁ : ⇓Modal[m,w ⊨ φ₁]) : ⇓Modal[m,w ⊨ φ₂] := by
  grind only [modal]

/-! ## Triangle -/

example (h : ⇓Modal[m,w ⊨ Δ[op]φs]) : ∃ ws, m.r op w ws ∧ ∀ i, ⇓Modal[m,ws i ⊨ φs i] := by grind

example (hr : m.r op w ws) (hs : ∀ i, ⇓Modal[m,ws i ⊨ φs i]) : ⇓Modal[m,w ⊨ Δ[op]φs] := by grind

/-! ## Nabla -/

example (h : ⇓Modal[m,w ⊨ ∇[op]φs]) (hr : m.r op w ws) : ∃ i, ⇓Modal[m,ws i ⊨ φs i] := by grind

example (h : ∀ ws, m.r op w ws → ∃ i, ⇓Modal[m,ws i ⊨ φs i]) : ⇓Modal[m,w ⊨ ∇[op]φs] := by grind

/-! ## Composition of modal and propositional operators -/

example (h : ⇓Modal[m,w ⊨ Δ[op]φs]) (himp : ∀ ws i, m.r op w ws → ⇓Modal[m,ws i ⊨ φs i → ψs i]) :
    ⇓Modal[m,w ⊨ Δ[op]ψs] := by grind

example (h : ⇓Modal[m,w ⊨ ∇[op]φs]) (himp : ∀ ws i, m.r op w ws → ⇓Modal[m,ws i ⊨ φs i → ψs i]) :
    ⇓Modal[m,w ⊨ ∇[op]ψs] := by grind

/-! ## Derivable modal laws -/

/-- A modal implication should behave as modus ponens. -/
example {φ ψ : Proposition τ Atom} (himp : ⇓Modal[m,w ⊨ φ → ψ]) (hφ : ⇓Modal[m,w ⊨ φ]) :
    ⇓Modal[m,w ⊨ ψ] := by grind only [modal]

/-- `grind` should instantiate quantified modal implications. -/
example {φs ψs : PropositionMap τ op Atom}
    (himp : ∀ i w, ⇓Modal[m,w ⊨ φs i → ψs i])
    (hφ : ⇓Modal[m,w' ⊨ φs i]) :
    ⇓Modal[m,w' ⊨ ψs i] := by
  simp only [Satisfies.imp_iff_imp] at himp
  grind only [modal]

/-- Triangle is monotone in every argument. -/
example {op : τ.A} {φs ψs : PropositionMap τ op Atom} (himp : ∀ i w, ⇓Modal[m,w ⊨ φs i → ψs i])
    (h : ⇓Modal[m,w ⊨ Δ[op]φs]) : ⇓Modal[m,w ⊨ Δ[op]ψs] := by
  simp only [Satisfies.imp_iff_imp] at himp
  grind [modal]

/-- Nabla is monotone in every argument. -/
example {φs ψs : PropositionMap τ op Atom} (himp : ∀ i w, ⇓Modal[m,w ⊨ φs i → ψs i])
    (h : ⇓Modal[m,w ⊨ ∇[op]φs]) : ⇓Modal[m,w ⊨ ∇[op]ψs] := by
  simp only [Satisfies.imp_iff_imp] at himp
  grind [modal]

/-- Triangle preserves pointwise conjunction in the forward direction. -/
example {φs ψs : PropositionMap τ op Atom}
    (h : ⇓Modal[m,w ⊨ Δ[op](φs ∧ ψs)]) : ⇓Modal[m,w ⊨ Δ[op]φs ∧ Δ[op]ψs] := by
  grind [modal]

/-- Either nabla condition entails their pointwise disjunction. -/
example {φs ψs : PropositionMap τ op Atom}
    (h : ⇓Modal[m,w ⊨ ∇[op]φs ∨ ∇[op]ψs]) : ⇓Modal[m,w ⊨ ∇[op](φs ∨ ψs)] := by
  grind [modal]

/-- Nabla is the dual of triangle. -/
example {φs : PropositionMap τ op Atom} : ⇓Modal[m,w ⊨ ∇[op]φs] ↔ ⇓Modal[m,w ⊨ ¬Δ[op](¬φs)] := by
  grind

end Grind

end Cslib.Logic.Modal
