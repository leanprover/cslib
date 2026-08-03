/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.HML.Basic
import Cslib.Logics.HML.LogicalEquivalence
import Cslib.Languages.CCS.Semantics

namespace CslibTests

open Cslib Logic HML LTS

example [∀ p μ, Finite ((CCS.lts (defs := defs)).image p μ)] :
    TheoryEq (CCS.lts (defs := defs)) = HomBisimilarity (CCS.lts (defs := defs)) :=
  theoryEq_eq_bisimilarity ..

section LogicalEquivalence

/-
The next example tests that logical equivalence can lift equivalences.

We prove it twice. Once using our infrastructure for up-to context reasoning directly, and then
with grind. Note that the grind proof works because Satisfies.and_iff_and gives a congruence
principle on the satisfaction relation for the and-connective.
-/

open scoped InferenceSystem
open Proposition

example {State : Type u} {lts : LTS State Label} {s : State} {μ : Label} {φ₁ φ₂ : Proposition Label}
    (h : ⇓HML[lts,s ⊨ (d⟨μ⟩φ₁) ∧ φ₂])
    : ⇓HML[lts,s ⊨ (¬d[μ]¬φ₁) ∧ φ₂] := by
  let pc : HasContext.Context (Proposition Label) := Context.andL .hole φ₂
  have eqv := LawfulCongruence.covariant.elim pc (dual μ φ₁)
  let jc : HasHContext.Context (Judgement State Label) (Proposition Label) :=
    Judgement.Context.mk lts s
  apply LogicalEquivalence.eqvFillValid eqv jc h

example {State : Type u} {lts : LTS State Label} {s : State} {μ : Label} {φ₁ φ₂ : Proposition Label}
    (h : ⇓HML[lts,s ⊨ (d⟨μ⟩φ₁) ∧ φ₂]) : ⇓HML[lts,s ⊨ (¬d[μ]¬φ₁) ∧ φ₂] := by
  grind only [= Satisfies.and_iff_and, => equiv_iff, dual μ φ₁ lts]

end LogicalEquivalence

end CslibTests
