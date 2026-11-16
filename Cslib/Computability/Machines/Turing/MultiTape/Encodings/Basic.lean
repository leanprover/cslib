/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Encoding.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OneWay

/-!
# Machines on encoded values

Machines see only code words, and the machines for the default encodings of `Cslib.Encoding`
usually do not depend on the encodings of the components of a value. The complexity of a function
on encoded values is therefore obtained in two steps: a machine computes a function on Boolean
words, and this function realizes the function on values in the sense of `Cslib.Encoding.Realizes`.

## Main results

* `Turing.MultiTapeTM.ComputableInTimeAndSpace.of_realizes`: a function realized by a computable
  function on Boolean words is computable within the same bounds.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.congr_out`: the output type and encoding of a
  computable function can be replaced by ones that yield the same code words.
* `Turing.MultiTapeTM.computableInTimeAndSpace_of_oneWayOutput_eq`: a function on Boolean words
  that is the output function of a one-way machine is computable in linear time and zero space.
* `Turing.MultiTapeTM.computableInTimeAndSpace_const`: constant functions are computable in
  constant time and zero space.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.Encoding

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- A function on encoded values that is realized by a computable function `g` on Boolean words is
computable within the bounds of `g`, taken at the code word of the input. -/
theorem ComputableInTimeAndSpace.of_realizes {f : α → β} {g : List Bool → List Bool}
    {t s : List Bool → ℕ} (hg : ComputableInTimeAndSpace g encBits encBits t s)
    (h : Realizes g f encIn encOut) :
    ComputableInTimeAndSpace f encIn encOut (fun a => t (encIn a)) (fun a => s (encIn a)) := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := hg
  exact ⟨k, State, hfinite, tm, fun a => by rw [← h a]; exact htm (encIn a)⟩

/-- If `f` is computable, then so is every `f'` whose values have the same code words, possibly
with another output type and encoding, within the same bounds. -/
theorem ComputableInTimeAndSpace.congr_out {f : α → β} {f' : α → γ} {encOut' : γ ↪ List Bool}
    {t s : α → ℕ} (h : ComputableInTimeAndSpace f encIn encOut t s)
    (henc : ∀ a, encOut' (f' a) = encOut (f a)) :
    ComputableInTimeAndSpace f' encIn encOut' t s := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, fun a => by rw [henc a]; exact htm a⟩

/-- A function on Boolean words that is the output function of a one-way machine is computable in
one step per input and output bit plus one, and in zero space. -/
theorem computableInTimeAndSpace_of_oneWayOutput_eq {State : Type} [Finite State] (q₀ : State)
    (step : State → Bool → List Bool × State) (final : State → List Bool)
    {g : List Bool → List Bool} (hg : ∀ w, oneWayOutput step final q₀ w = g w) :
    ComputableInTimeAndSpace g encBits encBits (fun w => w.length + (g w).length + 1)
      (fun _ => 0) :=
  have ⟨m, hstep, hfinal⟩ := exists_oneWay_length_le step final
  ⟨0, _, inferInstance, oneWay m q₀ step final, fun w => by
    have h := computesInTimeAndSpace_oneWay q₀ hstep hfinal w
    have ht := oneWayTime_le step final q₀ w
    rw [hg] at h ht
    exact ⟨h.1, h.2.1.mono ht, h.2.2⟩⟩

/-- A constant function is computable in the length of the code of its value plus two steps, and
in zero space, relative to every input encoding. -/
theorem computableInTimeAndSpace_const (b : β) :
    ComputableInTimeAndSpace (fun _ : α => b) encIn encOut (fun _ => (encOut b).length + 2)
      (fun _ => 0) :=
  (computableInTimeAndSpace_almostConstTime _ ∅ (encOut b) (by simp)).mono
    (fun _ => by simp only [almostConstTime, Finset.sup_empty, bot_eq_zero]; lia) fun _ => le_rfl

end Turing.MultiTapeTM
