/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Soundness
public import Cslib.Logics.Temporal.Metalogic.DenseMCS

/-! # Dense Soundness for Temporal Logic

This module proves that the two dense axioms (density and dense_indicator) are
semantically valid on densely ordered serial linear orders, and extends the
base soundness theorem to `FrameClass.Dense`.

## Main Results

- `density_axiom_sound`: G(G(φ)) → G(φ) is valid on DenselyOrdered domains.
- `dense_indicator_sound`: ¬U(⊤, ⊥) is valid on DenselyOrdered domains.
- `axiom_sound_dense`: All 28 axioms are valid on dense serial linear orders.
- `soundness_dense`: Derivation tree soundness at FrameClass.Dense.
- `soundness_thderivable_dense`: ThDerivableFc .Dense implies ValidDense.

## References

- Burgess (1982): BX axiom system for temporal logic
-/

set_option linter.style.setOption false
set_option maxHeartbeats 1600000

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic.Temporal

variable {Atom : Type*}

/-! ## Dense Axiom Soundness -/

/-- The density axiom G(G(φ)) → G(φ) is valid on DenselyOrdered domains.

Proof: Assume G(G(φ)) at t, i.e., for all s > t, G(φ) at s.
We need G(φ) at t, i.e., for all s > t, φ at s.
Take any s > t. By DenselyOrdered, there exists r with t < r < s.
By G(G(φ)) at t, we get G(φ) at r. By G(φ) at r with r < s, we get φ at s. -/
theorem density_axiom_sound {D : Type*} [LinearOrder D] [DenselyOrdered D]
    [NoMaxOrder D] [NoMinOrder D]
    {φ : Formula Atom}
    (M : TemporalModel D Atom) (t : D) :
    Satisfies M t (𝐆𝐆φ → 𝐆φ) := by
  intro h_gg
  rw [Satisfies.allFuture_iff] at h_gg ⊢
  intro s hts
  obtain ⟨r, htr, hrs⟩ := exists_between hts
  have h_g_r := h_gg r htr
  rw [Satisfies.allFuture_iff] at h_g_r
  exact h_g_r s hrs

/-- The dense indicator ¬U(⊤, ⊥) is valid on DenselyOrdered domains.

Proof: Assume U(⊤, ⊥) at t, i.e., exists s > t with ⊤ at s (trivially true)
and ⊥ at all r between t and s. By DenselyOrdered, there exists r with
t < r < s. Then ⊥ at r, contradiction. -/
theorem dense_indicator_sound {D : Type*} [LinearOrder D] [DenselyOrdered D]
    [NoMaxOrder D] [NoMinOrder D]
    (M : TemporalModel D Atom) (t : D) :
    Satisfies M t (Formula.untl Formula.top Formula.bot).neg := by
  rw [Satisfies.neg_iff]
  intro ⟨s, hts, _, h_guard⟩
  obtain ⟨r, htr, hrs⟩ := exists_between hts
  exact h_guard r htr hrs

/-! ## Extended Axiom Soundness at Dense -/

/-- Every axiom in the BX+Dense system is valid over dense serial linear orders.

The 26 Base axioms delegate to `axiom_sound` (since Base ≤ Dense implies
they are valid on all serial linear orders, hence on dense ones).
The 2 Dense axioms use `density_axiom_sound` and `dense_indicator_sound`. -/
theorem axiom_sound_dense {D : Type*} [LinearOrder D] [DenselyOrdered D]
    [NoMaxOrder D] [NoMinOrder D]
    {φ : Formula Atom} (h_ax : Axiom φ)
    (_h_fc : h_ax.minFrameClass ≤ FrameClass.Dense)
    (M : TemporalModel D Atom) (t : D) : Satisfies M t φ := by
  cases h_ax with
  | density φ => exact density_axiom_sound M t
  | dense_indicator => exact dense_indicator_sound M t
  | imp_k => exact axiom_sound (.imp_k _ _ _) (FrameClass.base_le _) M t
  | imp_s => exact axiom_sound (.imp_s _ _) (FrameClass.base_le _) M t
  | efq => exact axiom_sound (.efq _) (FrameClass.base_le _) M t
  | peirce => exact axiom_sound (.peirce _ _) (FrameClass.base_le _) M t
  | serial_future => exact axiom_sound .serial_future (FrameClass.base_le _) M t
  | serial_past => exact axiom_sound .serial_past (FrameClass.base_le _) M t
  | left_mono_until_G => exact axiom_sound (.left_mono_until_G _ _ _) (FrameClass.base_le _) M t
  | left_mono_since_H => exact axiom_sound (.left_mono_since_H _ _ _) (FrameClass.base_le _) M t
  | right_mono_until => exact axiom_sound (.right_mono_until _ _ _) (FrameClass.base_le _) M t
  | right_mono_since => exact axiom_sound (.right_mono_since _ _ _) (FrameClass.base_le _) M t
  | connect_future => exact axiom_sound (.connect_future _) (FrameClass.base_le _) M t
  | connect_past => exact axiom_sound (.connect_past _) (FrameClass.base_le _) M t
  | enrichment_until => exact axiom_sound (.enrichment_until _ _ _) (FrameClass.base_le _) M t
  | enrichment_since => exact axiom_sound (.enrichment_since _ _ _) (FrameClass.base_le _) M t
  | self_accum_until => exact axiom_sound (.self_accum_until _ _) (FrameClass.base_le _) M t
  | self_accum_since => exact axiom_sound (.self_accum_since _ _) (FrameClass.base_le _) M t
  | absorb_until => exact axiom_sound (.absorb_until _ _) (FrameClass.base_le _) M t
  | absorb_since => exact axiom_sound (.absorb_since _ _) (FrameClass.base_le _) M t
  | linear_until => exact axiom_sound (.linear_until _ _ _ _) (FrameClass.base_le _) M t
  | linear_since => exact axiom_sound (.linear_since _ _ _ _) (FrameClass.base_le _) M t
  | until_F => exact axiom_sound (.until_F _ _) (FrameClass.base_le _) M t
  | since_P => exact axiom_sound (.since_P _ _) (FrameClass.base_le _) M t
  | temp_linearity => exact axiom_sound (.temp_linearity _ _) (FrameClass.base_le _) M t
  | temp_linearity_past => exact axiom_sound (.temp_linearity_past _ _) (FrameClass.base_le _) M t
  | F_until_equiv => exact axiom_sound (.F_until_equiv _) (FrameClass.base_le _) M t
  | P_since_equiv => exact axiom_sound (.P_since_equiv _) (FrameClass.base_le _) M t

end Cslib.Logic.Temporal

universe u_dom_dense

namespace Cslib.Logic.Temporal

open Cslib.Logic.Temporal

variable {Atom : Type*}

/-! ## Dense Swap Valid -/

/-- Dense version of `swap_valid_of_valid`: if φ is satisfied everywhere in all
dense serial linear order models, then `swapTemporal φ` is also satisfied.
Proved by transferring to the dual model (which is also DenselyOrdered). -/
theorem swap_valid_of_valid_dense
    {φ : Formula Atom}
    (h_valid : ∀ (D : Type u_dom_dense) [LinearOrder D] [DenselyOrdered D]
      [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D), Satisfies M t φ)
    (D : Type u_dom_dense) [LinearOrder D] [DenselyOrdered D]
    [NoMaxOrder D] [NoMinOrder D]
    (M : TemporalModel D Atom) (t : D) :
    Satisfies M t (Formula.swapTemporal φ) := by
  rw [swapTemporal_dual]
  exact h_valid (OrderDual D) (dualModel M) (OrderDual.toDual t)

/-! ## Dense Soundness Theorem -/

/-- **Soundness at Dense**: If `Γ ⊢[Dense] φ`, then for any dense serial
linear order model and any time where all of `Γ` is satisfied, `φ` is also
satisfied. -/
theorem soundness_dense {D : Type*} [LinearOrder D] [DenselyOrdered D]
    [NoMaxOrder D] [NoMinOrder D]
    {Γ : Context Atom} {φ : Formula Atom}
    (d : DerivationTree FrameClass.Dense Γ φ)
    (M : TemporalModel D Atom) (t : D)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies M t ψ) : Satisfies M t φ := by
  match d with
  | .axiom _ ψ h_ax h_fc =>
    exact axiom_sound_dense h_ax h_fc M t
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact soundness_dense d₁ M t h_ctx (soundness_dense d₂ M t h_ctx)
  | .temporal_necessitation ψ d' =>
    simp only [Satisfies.allFuture_iff]
    intro s hlt
    exact soundness_dense d' M s (fun _ h => nomatch h)
  | .temporal_duality ψ d' =>
    exact swap_valid_of_valid_dense
      (fun D' _ _ _ _ M' t' => soundness_dense d' M' t' (fun _ h => nomatch h)) D M t
  | .weakening Γ' Δ ψ d' h_sub =>
    exact soundness_dense d' M t (fun x hx => h_ctx x (h_sub hx))

/-- **Soundness for Dense-derivable formulas**: If `ThDerivableFc .Dense φ`,
then `φ` is valid over all dense serial linear orders. -/
theorem soundness_thderivable_dense {D : Type*} [LinearOrder D] [DenselyOrdered D]
    [NoMaxOrder D] [NoMinOrder D]
    {φ : Formula Atom} (h : Temporal.ThDerivableFc FrameClass.Dense φ)
    (M : TemporalModel D Atom) (t : D) : Satisfies M t φ := by
  obtain ⟨d⟩ := h
  exact soundness_dense d M t (fun _ h => nomatch h)

end Cslib.Logic.Temporal
