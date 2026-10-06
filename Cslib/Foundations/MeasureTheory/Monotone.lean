/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Increasing sequences of measures

The supremum of an increasing sequence of measures is computed pointwise on measurable sets
(`Measure.iSup_apply_of_monotone`), and the Giry bind is monotone in its continuation and commutes
with increasing limits of continuations (`Measure.bind_iSup_of_monotone`). These are the facts
needed to interpret a possibly non-terminating computation by the limit of its finite
approximations.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The Giry bind is monotone in an almost everywhere measurable continuation. -/
theorem bind_mono_right {μ : Measure α} {f g : α → Measure β} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (hfg : ∀ᵐ a ∂μ, f a ≤ g a) : μ.bind f ≤ μ.bind g :=
  le_iff.2 fun s hs => by
    simpa [bind_apply hs hf, bind_apply hs hg] using lintegral_mono_ae (hfg.mono fun _ h => h s)

/-- The Giry bind is monotone in its continuation when every map out of the source is measurable. -/
theorem bind_mono_right_of_discrete [DiscreteMeasurableSpace α] {μ : Measure α}
    {f g : α → Measure β} (hfg : ∀ a, f a ≤ g a) : μ.bind f ≤ μ.bind g :=
  bind_mono_right Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable
    (.of_forall hfg)

private theorem iSup_tsum_of_monotone (f : ℕ → ℕ → ℝ≥0∞) (hf : ∀ i, Monotone (f · i)) :
    ⨆ n, ∑' i, f n i = ∑' i, ⨆ n, f n i := by
  simp_rw [ENNReal.tsum_eq_iSup_sum,
    ENNReal.finsetSum_iSup_of_monotone (f := fun i n => f n i) hf]
  exact iSup_comm

/-- The measure whose value on a measurable set is the supremum along an increasing sequence. -/
private noncomputable def monotoneLimit (μ : ℕ → Measure α) (hμ : Monotone μ) : Measure α :=
  ofMeasurable (fun s _ => ⨆ n, μ n s) (by simp) fun s hs hd => by
    simpa [measure_iUnion hd hs] using
      iSup_tsum_of_monotone (fun n i => μ n (s i)) fun i _ _ h => hμ h (s i)

/-- The supremum of an increasing sequence of measures is computed pointwise on measurable sets. -/
theorem iSup_apply_of_monotone {μ : ℕ → Measure α} (hμ : Monotone μ) {s : Set α}
    (hs : MeasurableSet s) : (⨆ n, μ n) s = ⨆ n, μ n s := by
  have : ⨆ n, μ n = monotoneLimit μ hμ :=
    le_antisymm (iSup_le fun n => le_iff.2 fun t ht => by
        simpa [monotoneLimit, ofMeasurable_apply _ ht] using le_iSup (μ · t) n)
      (le_iff.2 fun t ht => by
        simpa [monotoneLimit, ofMeasurable_apply _ ht] using fun n => le_iSup μ n t)
  simp [this, monotoneLimit, ofMeasurable_apply _ hs]

/-- The Giry bind commutes with an increasing sequence of measurable continuations. -/
theorem bind_iSup_of_monotone {μ : Measure α} {f : ℕ → α → Measure β}
    (hf : ∀ n, Measurable (f n)) (hlim : Measurable fun a => ⨆ n, f n a)
    (hmono : ∀ a, Monotone (f · a)) : μ.bind (fun a => ⨆ n, f n a) = ⨆ n, μ.bind (f n) := by
  have hbind : Monotone fun n => μ.bind (f n) := fun i j h =>
    bind_mono_right (hf i).aemeasurable (hf j).aemeasurable (.of_forall fun a => hmono a h)
  ext s hs
  rw [bind_apply hs hlim.aemeasurable, iSup_apply_of_monotone hbind hs]
  simp_rw [iSup_apply_of_monotone (hmono _) hs, bind_apply hs (hf _).aemeasurable]
  exact lintegral_iSup (fun n => (measurable_coe hs).comp (hf n)) fun i j h a => hmono a h s

/-- Lower integration against an increasing sequence of measures commutes with its supremum. -/
theorem lintegral_iSup_of_monotone {μ : ℕ → Measure α} (hμ : Monotone μ) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂(⨆ n, μ n) = ⨆ n, ∫⁻ a, f a ∂μ n := by
  have (g : SimpleFunc α ℝ≥0∞) : g.lintegral (⨆ n, μ n) = ⨆ n, g.lintegral (μ n) := by
    simp only [SimpleFunc.lintegral, iSup_apply_of_monotone hμ (g.measurableSet_preimage _),
      ENNReal.mul_iSup]
    exact ENNReal.finsetSum_iSup_of_monotone fun _ _ _ h => mul_le_mul' le_rfl (hμ h _)
  simp only [lintegral_def, this, iSup_comm (ι := ℕ)]

/-- The Giry bind commutes with an increasing sequence of source measures. -/
theorem iSup_bind_of_monotone {μ : ℕ → Measure α} (hμ : Monotone μ) {f : α → Measure β}
    (hf : Measurable f) : (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f := by
  have hbind : Monotone fun n => (μ n).bind f := fun _ _ h => le_iff.2 fun s hs => by
    simpa [bind_apply hs hf.aemeasurable] using lintegral_mono' (hμ h) le_rfl
  ext s hs
  simp [bind_apply hs hf.aemeasurable, iSup_apply_of_monotone hbind hs,
    lintegral_iSup_of_monotone hμ]

end MeasureTheory.Measure
