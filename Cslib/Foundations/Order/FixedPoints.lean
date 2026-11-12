/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.Order.FixedPoints

/-! # Extensions to Mathlib's fixed point API -/

public section

namespace OrderHom

variable {α : Type u} [CompleteLattice α] (f : α →o α)

theorem nextFixed_bot_coe : ↑(f.nextFixed ⊥ bot_le) = f.lfp :=
  congr(lfp $(bot_sup_eq f))

theorem prevFixed_top_coe : ↑(f.prevFixed ⊤ le_top) = f.gfp :=
  congr(gfp $(top_inf_eq f))

/-- Generalisation of `OrderHom.nextFixed_le` to prefixed points. -/
theorem nextFixed_le_of_map_le {x y : α} (hx : x ≤ f x) (hxy : x ≤ y) (hy : f y ≤ y) :
    ↑(f.nextFixed x hx) ≤ y := by
  apply lfp_le
  simp_all

/-- Generalisation of `OrderHom.le_prevFixed` to postfixed points. -/
theorem le_prevFixed_of_map_ge {x y : α} (hx : f x ≤ x) (hxy : y ≤ x) (hy : y ≤ f y) :
    y ≤ f.prevFixed x hx := by
  apply le_gfp
  simp_all

/-- Analogue of `OrderHom.lfp_induction` for `OrderHom.nextFixed`. -/
theorem nextFixed_induction {x : α} (hx : x ≤ f x) {p : α → Prop} (base : p x)
    (step : ∀ a, p a → x ≤ a → a ≤ f.nextFixed x hx → p (f a))
    (hSup : ∀ s, (∀ a ∈ s, p a) → p (sSup s)) : p (f.nextFixed x hx) := by
  suffices f.nextFixed x hx = sSup {a | x ≤ a ∧ a ≤ f.nextFixed x hx ∧ p a} by grind
  have hx_le : x ≤ sSup {a | x ≤ a ∧ a ≤ f.nextFixed x hx ∧ p a} :=
    le_sSup ⟨le_rfl, f.le_nextFixed hx, base⟩
  have hSup_le : sSup {a | x ≤ a ∧ a ≤ f.nextFixed x hx ∧ p a} ≤ f.nextFixed x hx :=
    sSup_le <| by grind
  refine (f.nextFixed_le_of_map_le hx hx_le <| le_sSup ⟨?_, ?_, ?_⟩).antisymm hSup_le
  · exact hx.trans (f.mono hx_le)
  · exact (f.mono hSup_le).trans (f.nextFixed x hx).prop.le
  · grind

/-- Analogue of `OrderHom.gfp_induction` for `OrderHom.prevFixed`. -/
theorem prevFixed_induction {x : α} (hx : f x ≤ x) {p : α → Prop} (base : p x)
    (step : ∀ a, p a → a ≤ x → f.prevFixed x hx ≤ a → p (f a))
    (hInf : ∀ s, (∀ a ∈ s, p a) → p (sInf s)) : p (f.prevFixed x hx) :=
  f.dual.nextFixed_induction hx base step hInf

end OrderHom
