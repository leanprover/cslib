/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Languages.CombinatoryLogic.Recursion
public import Mathlib.Data.PFun

/-!
# SKI-computable functions

This file defines the notion of SKI-computability for partial functions on natural
numbers, via Church numerals: a term computes `f : ℕ →. ℕ` if it maps Church numeral
inputs to Church numeral outputs wherever `f` is defined.

## Main definitions

- `SKI.Computes`: an SKI term computes a given partial function.
- `SKI.Computable`: a partial function is SKI-computable if some SKI term computes it.

## Implementation notes

Unlike `Cslib.URM.Computes`, which is a two-sided equality of `Part` values, this
predicate is one-sided: it constrains the term's behavior only where the function is
defined, and says nothing about inputs outside the domain.
-/

@[expose] public section

namespace Cslib

namespace SKI

open Red MRed

/-- An SKI term `t` computes a partial function `f : ℕ →. ℕ` if,
for every Church numeral input, `t` applied to the input is a Church numeral
for the output whenever `f` is defined. -/
def Computes (t : SKI) (f : ℕ →. ℕ) : Prop :=
  ∀ n : ℕ, ∀ cn : SKI, IsChurch n cn →
    ∀ m : ℕ, f n = Part.some m →
      IsChurch m (t ⬝ cn)

/-- A partial function `f : ℕ →. ℕ` is SKI-computable if there exists an SKI term that
computes it. -/
def Computable (f : ℕ →. ℕ) : Prop :=
  ∃ t : SKI, Computes t f

/-- To show that a term computes a total function, it suffices to produce a Church
numeral for the output on every input. -/
theorem computes_of_total {t : SKI} {f : ℕ →. ℕ} (g : ℕ → ℕ)
    (heval : ∀ n, f n = Part.some (g n))
    (hcorrect : ∀ n cn, IsChurch n cn → IsChurch (g n) (t ⬝ cn)) :
    Computes t f := by
  intro n cn hcn m hm; rw [heval] at hm; obtain rfl := Part.some_injective hm
  exact hcorrect n cn hcn

/-- Composition of computable functions is computable. -/
theorem comp_computes {f g : ℕ →. ℕ} {tf tg : SKI}
    (hf : Computes tf f) (hg : Computes tg g) :
    Computes (B ⬝ tf ⬝ tg) (fun n => g n >>= f) := by
  intro n cn hcn m hm
  obtain ⟨intermediate, hint_eq, hm_eq⟩ := Part.bind_eq_some_iff.mp hm
  exact isChurch_trans _ (B_def tf tg cn)
    (hf intermediate (tg ⬝ cn) (hg n cn hcn intermediate hint_eq) m hm_eq)

/-- Pairing of computable functions is computable. -/
theorem pair_computes {f g : ℕ →. ℕ} {tf tg : SKI}
    (hf : Computes tf f) (hg : Computes tg g) :
    Computes (S ⬝ (B ⬝ NatPair ⬝ tf) ⬝ tg)
      (fun n => Nat.pair <$> f n <*> g n) := by
  intro n cn hcn m hm
  simp only at hm
  obtain ⟨h, hh_mem, hm_in_h⟩ := Part.mem_bind_iff.mp (hm ▸ Part.mem_some m)
  obtain ⟨a, ha_mem, rfl⟩ := (Part.mem_map_iff _).mp hh_mem
  obtain ⟨b, hb_mem, rfl⟩ := (Part.mem_map_iff _).mp hm_in_h
  have hca := hf n cn hcn a (Part.eq_some_iff.mpr ha_mem)
  have hcb := hg n cn hcn b (Part.eq_some_iff.mpr hb_mem)
  exact isChurch_trans _ ((MRed.S _ _ _).trans (MRed.head _ (B_def _ _ _)))
    (natPair_correct a b _ _ hca hcb)

end SKI

end Cslib
