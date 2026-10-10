/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Basic.Finite.Sum
public import Cslib.Foundations.Data.Fin.Tuple
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape

/-!
# Composing tidy computations

`tm₂.comp tm₁ mark` runs `tm₁` with its output written to a work tape, then runs `tm₂` reading its
input from that tape, and finally clears the tape. If both machines compute tidily, so does the
composition. Its time is the sum of the two times plus a term linear in the length of the
intermediate word; so is its space, since the intermediate word is kept on a work tape.

## Main definitions

* `Turing.MultiTapeTM.comp`: the composed machine.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.comp`: tidy computations compose.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp`: tidily computable functions compose.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp'`: the same, with the length of the
  intermediate word bounded by the time of the inner function.
-/

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol S₁ S₂ : Type*}

/-- `tm₂` after `tm₁`, both with their work tapes padded to `max k₁ k₂`: run `tm₁` with its output
written to the work tape `Fin.natAdd (max k₁ k₂) 0`, run `tm₂` reading its input from that tape
(using `mark` on the last work tape to flag the left end of the input), then clear that tape. -/
public noncomputable def comp (tm₂ : MultiTapeTM k₂ Symbol S₂) (tm₁ : MultiTapeTM k₁ Symbol S₁)
    (mark : Symbol) : MultiTapeTM (max k₁ k₂ + 2) Symbol
      ((S₁ ⊕ RewindWorkState) ⊕ (MarkWorkState ⊕ S₂ ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState) :=
  ((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
      Fin.castSuccEmb).seq
    (((tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).seq
      ((clearWork Symbol).extendTapes (tapeEmb (Fin.natAdd (max k₁ k₂) 0))))

/-- If `tm₁` computes `w` from `x` tidily and `tm₂` computes `y` from `w` tidily, then
`tm₂.comp tm₁ mark` computes `y` from `x` tidily. -/
public theorem ComputesTidilyInTimeAndSpace.comp {tm₁ : MultiTapeTM k₁ Symbol S₁}
    {tm₂ : MultiTapeTM k₂ Symbol S₂} {x w y : List Symbol} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : tm₁.ComputesTidilyInTimeAndSpace x w t₁ s₁)
    (h₂ : tm₂.ComputesTidilyInTimeAndSpace w y t₂ s₂) (mark : Symbol) :
    (tm₂.comp tm₁ mark).ComputesTidilyInTimeAndSpace x y (t₁ + t₂ + 4 * w.length + 9)
      (s₁ + s₂ + 5 * w.length + (6 * max k₁ k₂ + 17)) := by
  set K := max k₁ k₂
  -- the work tape holding the intermediate word `w`
  set A : Fin (K + 2) := Fin.natAdd K 0
  have hA : Fin.append (fun _ : Fin K => ([] : List Symbol)) ![w, []] =
      Function.update (fun _ => []) A w := by
    rw [← Fin.append_const (m := K) (n := 2) [], ← Fin.append_update_right]
    congr 1
    simp [funext_iff, Fin.forall_fin_two]
  -- phase 1: `tm₁` writes `w` to `A`
  have hQ₁ (ws' : Fin (K + 1 + 1) → List Symbol)
      (hv : (fun j => ws' (Fin.castSuccEmb j)) = Function.update (fun _ => []) (Fin.last K) w)
      (hx : ∀ l ∉ Set.range Fin.castSuccEmb, ws' l = []) :
      ws' = Function.update (fun _ => []) A w := by
    funext l
    induction l using Fin.lastCases with
    | last =>
      rw [hx _ fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj]
      simp [A, Fin.ext_iff]
    | cast j =>
      rw [show ws' j.castSucc = _ from congrFun hv j]
      simp [A, Function.update_apply, Fin.ext_iff]
  have hp₁ := ((h₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
    Fin.castSuccEmb).imp (P' := fun inp ws => inp = x ∧ ws = fun _ => [])
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) A w ∧ e = [])
    (fun _ _ ⟨hin, hws⟩ => ⟨hin, by simp [hws]⟩)
    (fun _ _ ws' _ ⟨_, hws⟩ ⟨⟨hv, he⟩, hx⟩ => ⟨hQ₁ ws' hv fun l hl => (hx l hl).trans
      (congrFun hws l), he⟩) le_rfl le_rfl
  -- phase 2: `tm₂` reads `w` from `A` and emits `y`
  obtain ⟨hrun₂, hspace₂⟩ :=
    computesTidily_iff.mp (h₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂)))
  have hp₂ := (transformsTapes_inputFromWord_of_runFrom mark hrun₂ hspace₂).imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) A w)
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) A w ∧ e = y)
    (fun _ _ hws => hws.trans hA.symm) (fun _ _ _ _ _ ⟨hws', he⟩ => ⟨hws'.trans hA, he⟩)
    le_rfl le_rfl
  -- phase 3: clear `A`
  have hclear : Function.update (Function.update (fun _ => []) A w) A [] = fun _ => [] := by
    rw [Function.update_idem]
    exact Function.update_eq_self A _
  have hp₃ := (transformsTapes_clearWork_tapeEmb (Symbol := Symbol) A w).imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) A w)
    (Q' := fun _ _ ws' e => ws' = (fun _ => []) ∧ e = [])
    (fun _ _ hws => by rw [hws, Function.update_self])
    (fun _ _ _ _ hws ⟨hws', he⟩ => ⟨by rw [hws', hws, hclear], he⟩) le_rfl le_rfl
  refine (transformsTapes_seq hp₁ (transformsTapes_seq hp₂ hp₃ fun _ _ _ _ _ hQ => hQ.1)
    fun _ _ _ _ _ hQ => hQ.1).imp (fun _ _ h => h) ?_ (by omega) (by omega)
  rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨_, _, _, ⟨-, rfl⟩, ⟨hws, rfl⟩, rfl⟩, rfl⟩
  exact ⟨hws, by simp⟩

/-- If `g` and `f` are tidily computable, so is `f ∘ g`, in the sum of their times and spaces plus
a term linear in the length of the intermediate word `encMid (g a)`. -/
public theorem ComputableTidilyInTimeAndSpace.comp {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => t₁ a + t₂ (g a) + 4 * (encMid (g a)).length + 9)
      (fun a => s₁ a + s₂ (g a) + 5 * (encMid (g a)).length + c) := by
  obtain ⟨k₁, S₁, _, tm₁, h₁⟩ := hg
  obtain ⟨k₂, S₂, _, tm₂, h₂⟩ := hf
  exact ⟨6 * max k₁ k₂ + 17, _, _, inferInstance, tm₂.comp tm₁ true,
    fun a => (h₁ a).comp (h₂ (g a)) true⟩

/-- If `g` and `f` are tidily computable, so is `f ∘ g`: the intermediate word is no longer than
the time of `g`. -/
public theorem ComputableTidilyInTimeAndSpace.comp' {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => 5 * t₁ a + t₂ (g a) + 9) (fun a => s₁ a + s₂ (g a) + 5 * t₁ a + c) := by
  obtain ⟨c, h⟩ := hf.comp hg
  obtain ⟨_, _, _, _, h₁⟩ := hg
  refine ⟨c, h.mono (fun a => ?_) (fun a => ?_)⟩ <;>
  · have := (h₁ a).length_output_le
    omega

end Turing.MultiTapeTM
