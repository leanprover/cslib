/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concatenate
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.DelimitOutput
public import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Delimit

/-!
# Complexity of pairs

The components of a pair and the first component of a dependent pair are obtained from the code of
the pair in linear time and zero space, independently of the encodings of the components. A pair
is formed from two machines that compute its components from the same input.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_prod_fst`,
  `Turing.MultiTapeTM.computableInTimeAndSpace_prod_snd`: the components of a pair.
* `Turing.MultiTapeTM.computableInTimeAndSpace_sigma_fst`: the first component of a dependent
  pair.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.prod_mk`: pairing two computable functions.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.Encoding

variable {α β γ : Type*} {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool}

/-- The first projection is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_prod_fst :
    ComputableInTimeAndSpace (Prod.fst : α × β → α) (encProd enc₁ enc₂) enc₁
      (fun p => 2 * (encProd enc₁ enc₂ p).length + 1) (fun _ => 0) :=
  computableInTimeAndSpace_undelimit.of_realizes fun _ => by simp

/-- The second projection is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_prod_snd :
    ComputableInTimeAndSpace (Prod.snd : α × β → β) (encProd enc₁ enc₂) enc₂
      (fun p => 2 * (encProd enc₁ enc₂ p).length + 1) (fun _ => 0) :=
  computableInTimeAndSpace_dropDelimited.of_realizes fun _ => by simp

/-- The first component of a dependent pair is computable in linear time and zero space. -/
theorem computableInTimeAndSpace_sigma_fst {δ : α → Type*} {encδ : ∀ a, δ a ↪ List Bool} :
    ComputableInTimeAndSpace (Sigma.fst : (a : α) × δ a → α) (encSigma enc₁ encδ) enc₁
      (fun x => 2 * (encSigma enc₁ encδ x).length + 1) (fun _ => 0) :=
  computableInTimeAndSpace_undelimit.of_realizes fun _ => by simp

/-- Pairing two computable functions is computable in time `4 * t₁ + t₂ + 4` and space
`3 * (s₁ + s₂)`: the first machine runs with its output delimited, the input is rewound, and the
second machine appends its output. -/
theorem ComputableInTimeAndSpace.prod_mk {f₁ : γ → α} {f₂ : γ → β} {encIn : γ ↪ List Bool}
    {t₁ t₂ s₁ s₂ : γ → ℕ} (h₁ : ComputableInTimeAndSpace f₁ encIn enc₁ t₁ s₁)
    (h₂ : ComputableInTimeAndSpace f₂ encIn enc₂ t₂ s₂) :
    ComputableInTimeAndSpace (fun x => (f₁ x, f₂ x)) encIn (encProd enc₁ enc₂)
      (fun x => 4 * t₁ x + t₂ x + 4) (fun x => 3 * (s₁ x + s₂ x)) :=
  (h₁.delimit.concatenate h₂ fun _ => rfl).mono (fun _ => by lia) fun _ => le_rfl

end Turing.MultiTapeTM
