/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.HML.Basic
import Cslib.Logics.Modal.LogicalEquivalence
import Cslib.Languages.CCS.Semantics

namespace CslibTests

open Cslib Logic Modal HML LTS Model Proposition Satisfies
open scoped InferenceSystem

example [∀ p μ, Finite ((CCS.lts (defs := defs)).image p μ)] :
    TheoryEq (Atom := Unit) (ofLTS (CCS.lts (defs := defs)) (fun _ _ => True)) =
      HomBisimilarity (CCS.lts (defs := defs)) :=
  theoryEq_eq_bisimilarity ..

example (v : State → Atom → Prop) (htr : lts.Tr s μ s') (hφ : ⇓Modal[ofLTS lts v,s' ⊨ φ]) :
    ⇓Modal[ofLTS lts v,s ⊨ d⟨μ⟩φ] := by grind only [modal]

example (v : State → Atom → Prop) (hbox : ⇓Modal[Model.ofLTS lts v,s ⊨ d[μ]φ])
    (htr : lts.Tr s μ s') : ⇓Modal[ofLTS lts v,s' ⊨ φ] := by grind only [modal]

section LogicalEquivalence

/-
The next example tests that logical equivalence can lift equivalences.

We prove it twice. Once using our infrastructure for up-to context reasoning directly, and then
with grind. Note that the grind proof works because Satisfies.and_iff_and gives a congruence
principle on the satisfaction relation for the and-connective.
-/

open PFunctor

example {State : Type u} {lts : LTS State Label} {s : State} {μ : Label}
    {φ₁ φ₂ : HML.Proposition Label Atom} (v : State → Atom → Prop)
    (h : ⇓Modal[ofLTS lts v,s ⊨ (d⟨μ⟩φ₁) ∧ φ₂]) : ⇓Modal[ofLTS lts v,s ⊨ (¬d[μ]¬φ₁) ∧ φ₂] := by
  let pc : HasContext.Context (HML.Proposition Label Atom) := Context.andL .hole φ₂
  have dual a (φ : HML.Proposition Label Atom) : d⟨a⟩φ ≡[UEquiv (World := State)] ¬d[a]¬φ := by
    grind only [modal, Satisfies.unary_dual]
  have eqv := LawfulCongruence.covariant.elim pc (dual μ φ₁)
  let jc : HasHContext.Context (Judgement State (mkUnary Label) Atom)
      (HML.Proposition Label Atom) := Judgement.Context.mk (ofLTS lts v) s
  apply LogicalEquivalence.eqvFillValid eqv jc h

example {State : Type u} {lts : LTS State Label} {s : State} {μ : Label}
    {φ₁ φ₂ : HML.Proposition Label Atom} (v : State → Atom → Prop)
    (h : ⇓Modal[ofLTS lts v,s ⊨ (d⟨μ⟩φ₁) ∧ φ₂]) :
    ⇓Modal[ofLTS lts v,s ⊨ (¬d[μ]¬φ₁) ∧ φ₂] := by grind [modal]

end LogicalEquivalence

end CslibTests
