/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init
public import Cslib.Foundations.Semantics.Frame.Basic
public import Cslib.Foundations.Semantics.LTS.Basic

/-! # Modal Frames and LTS -/

@[expose] public section

namespace Cslib.LTS

open PFunctor

variable (lts : LTS State Label)

/-- Transforms `lts` into a corresponding unary `Frame`. -/
def toFrame : Frame State (mkUnary Label) :=
  Frame.ofRelations (fun μ s s' => lts.Tr s μ s')

instance : Coe (LTS State Label) (Frame State (PFunctor.mkUnary Label)) := ⟨LTS.toFrame⟩

@[simp]
lemma toFrame_r_iff_tr : lts.toFrame.r μ s f ↔ lts.Tr s μ (f default) := by rfl

@[simp, modal =]
lemma toFrame_diagonal_iff_tr : lts.toFrame.diagonal μ s s' ↔ lts.Tr s μ s' := by rfl

end Cslib.LTS
