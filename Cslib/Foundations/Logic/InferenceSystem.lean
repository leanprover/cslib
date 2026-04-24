/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

@[expose] public section

namespace Cslib.Logic

/--
The notation typeclass for inference systems.
This enables the notation `S⇓a`, where `S` is a tag for the inference system and `a : α`
is a derivable value.
-/
class InferenceSystem (S : Type) (α : Type*) where
  /--
  `S⇓a` is a derivation of `a`, that is, a witness that `a` is derivable in the system `S`.
  The meaning of this notation is type-dependent.
  -/
  derivation (a : α) : Sort v

inductive InferenceSystem.Default

/-- Class for types (`α`) that have a canonical inference system. -/
abbrev HasInferenceSystem := InferenceSystem InferenceSystem.Default

namespace InferenceSystem

@[inherit_doc] scoped notation S:90 "⇓" a:90 => InferenceSystem.derivation S a

/-- Rewrites the conclusion of a proof into an equal one. -/
@[scoped grind =]
def rwConclusion [InferenceSystem S α] {Γ Δ : α} (h : Γ = Δ) (p : S⇓Γ) : S⇓Δ :=
  h ▸ p

/-- `a` is derivable in `S` if it is the conclusion of some derivation. -/
def DerivableIn S [InferenceSystem S α] (a : α) := Nonempty (S⇓a)

/-- `a : α` is derivable in the default inference system for `α`. -/
abbrev Derivable [InferenceSystem Default α] := DerivableIn Default (α := α)

/-- Shows derivability from a derivation. -/
theorem DerivableIn.fromDerivation [InferenceSystem S α] {a : α} (d : S⇓a) : DerivableIn S a :=
  Nonempty.intro d

instance [InferenceSystem S α] {a : α} : Coe (S⇓a) (DerivableIn S a) := ⟨DerivableIn.fromDerivation⟩

/-- Extracts (noncomputably) a derivation from the fact that a conclusion is derivable. -/
noncomputable def DerivableIn.toDerivation [InferenceSystem S α] {a : α} (d : DerivableIn S a) :
    S⇓a :=
  Classical.choice d

noncomputable instance [InferenceSystem S α] {a : α} : Coe (DerivableIn S a) (S⇓a) :=
  ⟨DerivableIn.toDerivation⟩

-- @[inherit_doc InferenceSystem.derivation]
-- def HasInferenceSystem.derivation (α : Type*) [HasInferenceSystem α] :=
--   (InferenceSystem.derivation Default α) α

@[inherit_doc] scoped notation "⇓" a:90 => InferenceSystem.derivation Default a

end InferenceSystem

end Cslib.Logic
