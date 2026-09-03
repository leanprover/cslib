/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.PFunctor.Basic
public import Cslib.Logics.Modal.Basic
public import Cslib.Logics.Modal.Semantics

/-! # Unary Modal Logic -/

@[expose] public section

namespace Cslib.Logic.Modal

open PFunctor
open scoped InferenceSystem Proposition Satisfies Frame

@[scoped grind =]
theorem Satisfies.dynDiamond_iff_exists [Unary τ] {m : Model World τ Atom}
    {φ : Proposition τ Atom} : ⇓Modal[m,w ⊨ d⟨op⟩φ] ↔
      ∃ w', m.toFrame.diagonal op w w' ∧ ⇓Modal[m,w' ⊨ φ] := by
  grind [Satisfies.triangle_iff_exists]

@[scoped grind =]
theorem Satisfies.dynBox_iff_forall [Unary τ] {m : Model World τ Atom} {φ : Proposition τ Atom} :
    ⇓Modal[m,w ⊨ d[op]φ] ↔ ∀ w', m.toFrame.diagonal op w w' → ⇓Modal[m,w' ⊨ φ] := by
  grind [Frame.diagonal]

end Cslib.Logic.Modal
