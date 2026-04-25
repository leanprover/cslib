/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! -/

@[expose] public section

namespace Cslib.Logic

/--
The notation typeclass for inference systems.
This enables the notation `⇓a`, where `a : α` is a derivable value.
-/
class InferenceSystem (α : Type u) where
  /--
  `⇓a` is a derivation of `a`, that is, a witness that `a` is derivable.
  The meaning of this notation is type-dependent.
  -/
  derivation (s : α) : Sort v

namespace InferenceSystem

@[inherit_doc] scoped notation "⇓" a:90 => InferenceSystem.derivation a

/-- Rewrites the conclusion of a proof into an equal one. -/
@[scoped grind =]
def rwConclusion [InferenceSystem α] {Γ Δ : α} (h : Γ = Δ) (p : ⇓Γ) : ⇓Δ := h ▸ p

/-- `a` is derivable if it is the conclusion of some derivation. -/
def Derivable [InferenceSystem α] (a : α) := Nonempty (⇓a)

/-- Shows derivability from a derivation. -/
theorem Derivable.fromDerivation [InferenceSystem α] {a : α} (d : ⇓a) : Derivable a :=
  Nonempty.intro d

instance [InferenceSystem α] {a : α} : Coe (⇓a) (Derivable a) := ⟨Derivable.fromDerivation⟩

/-- Extracts (noncomputably) a derivation from the fact that a conclusion is derivable. -/
noncomputable def Derivable.toDerivation [InferenceSystem α] {a : α} (d : Derivable a) : ⇓a :=
  Classical.choice d

noncomputable instance [InferenceSystem α] {a : α} : Coe (Derivable a) (⇓a) :=
  ⟨Derivable.toDerivation⟩

end InferenceSystem

end Cslib.Logic
