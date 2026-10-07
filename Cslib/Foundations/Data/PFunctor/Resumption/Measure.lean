/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Cslib.Foundations.Data.PFunctor.Free.Measure
public import Cslib.Foundations.Data.PFunctor.Resumption
public import Cslib.Foundations.MeasureTheory.Monotone

/-!
# Output measures of resumptions

Given a measure `μ a` on the responses of each operation `a`, the output measure
`r.toMeasure μ` of a resumption is the supremum of the measures `approxMeasure μ n r` of the values
it returns within `n` operations. This is the least-fixed-point reading of a possibly
non-terminating program: runs that never return contribute no mass, so `r.toMeasure μ` may have
total mass below `1` even when each `μ a` is a probability measure.

With discrete response spaces, `toMeasure` unfolds like `PFunctor.FreeM.toMeasure`, and the two
agree along `PFunctor.FreeM.toResumption` (`PFunctor.FreeM.toMeasure_toResumption`).
-/

@[expose] public section

open MeasureTheory

universe uA uB u v

namespace PFunctor.Resumption

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)] {α : Type u} {β : Type v}
  [MeasurableSpace α] [MeasurableSpace β] (μ : (a : P.A) → Measure (P.B a))

/-- The output measure of the values a resumption returns within `n` operations, each operation
`a` answered according to `μ a`. -/
noncomputable def approxMeasure : ℕ → Resumption P α → Measure α
  | 0, r => (dest r).elim .dirac fun _ => 0
  | n + 1, r => (dest r).elim .dirac fun x => (μ x.fst).bind fun b => approxMeasure n (x.snd b)

@[simp]
theorem approxMeasure_pure (n : ℕ) (a : α) : approxMeasure μ n (pure a) = .dirac a := by
  cases n <;> simp [approxMeasure]

@[simp]
theorem approxMeasure_zero_lift_bind (a : P.A) (k : P.B a → Resumption P α) :
    approxMeasure μ 0 ((lift a).bind (α := no_index (P.B a)) k) = 0 := by
  simp [approxMeasure]

@[simp]
theorem approxMeasure_succ_lift_bind (n : ℕ) (a : P.A) (k : P.B a → Resumption P α) :
    approxMeasure μ (n + 1) ((lift a).bind (α := no_index (P.B a)) k) =
      (μ a).bind fun b => approxMeasure μ n (k b) := by
  simp [approxMeasure]

/-- The output measure of `r` when each operation `a` is answered according to `μ a`: the
supremum of the output measures within finitely many operations. -/
noncomputable def toMeasure (r : Resumption P α) (μ : (a : P.A) → Measure (P.B a)) : Measure α :=
  ⨆ n, approxMeasure μ n r

theorem approxMeasure_le_toMeasure (n : ℕ) (r : Resumption P α) :
    approxMeasure μ n r ≤ r.toMeasure μ :=
  le_iSup (approxMeasure μ · r) n

@[simp]
theorem toMeasure_pure (a : α) : (pure a : Resumption P α).toMeasure μ = .dirac a := by
  simp [toMeasure]

section Discrete

variable [∀ a, DiscreteMeasurableSpace (P.B a)]

theorem monotone_approxMeasure (r : Resumption P α) : Monotone (approxMeasure μ · r) := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n generalizing r with
  | zero => cases r <;> simp [Measure.zero_le]
  | succ n ih =>
    cases r with
    | pure a => simp
    | lift_bind a k =>
      simpa using Measure.bind_mono_right_of_discrete fun b => ih (k b)

theorem toMeasure_lift_bind (a : P.A) (k : P.B a → Resumption P α) :
    ((lift a).bind (α := no_index (P.B a)) k).toMeasure μ =
      (μ a).bind fun b => (k b).toMeasure μ := by
  rw [toMeasure, ← (monotone_approxMeasure μ _).iSup_nat_add 1]
  simp_rw [approxMeasure_succ_lift_bind]
  exact (Measure.bind_iSup_of_monotone (fun _ => .of_discrete) .of_discrete
    fun b => monotone_approxMeasure μ (k b)).symm

@[simp]
theorem toMeasure_lift (a : P.A) :
    toMeasure (α := no_index (P.B a)) (lift a) μ = μ a := by
  simpa using toMeasure_lift_bind μ a pure

theorem toMeasure_bind (r : Resumption P α) {k : α → Resumption P β}
    (hk : Measurable fun a => (k a).toMeasure μ) :
    (r.bind k).toMeasure μ = (r.toMeasure μ).bind fun a => (k a).toMeasure μ := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    induction n generalizing r with
    | zero => cases r <;> simp [Measure.dirac_bind hk, approxMeasure_le_toMeasure, Measure.zero_le]
    | succ n ih => cases r with
      | pure a => simpa [Measure.dirac_bind hk] using approxMeasure_le_toMeasure μ _ (k a)
      | lift_bind a f =>
        simpa [toMeasure_lift_bind, Measure.bind_bind Measurable.of_discrete.aemeasurable
          hk.aemeasurable] using Measure.bind_mono_right_of_discrete fun b => ih (f b)
  · change (⨆ n, approxMeasure μ n r).bind _ ≤ _
    rw [Measure.iSup_bind_of_monotone (monotone_approxMeasure μ r) hk]
    refine iSup_le fun n => ?_
    induction n generalizing r with
    | zero => cases r <;> simp [Measure.dirac_bind hk, Measure.zero_le]
    | succ n ih => cases r with
      | pure a => simp [Measure.dirac_bind hk]
      | lift_bind a f =>
        simpa [toMeasure_lift_bind, Measure.bind_bind Measurable.of_discrete.aemeasurable
          hk.aemeasurable] using Measure.bind_mono_right_of_discrete fun b => ih (f b)

theorem toMeasure_map (r : Resumption P α) {f : α → β} (hf : Measurable f) :
    (r.map f).toMeasure μ = (r.toMeasure μ).map f := by
  rw [← bind_pure_comp, toMeasure_bind μ r (k := pure ∘ f)
    (by simpa [Function.comp_def] using Measure.measurable_dirac.comp hf)]
  simpa [Function.comp_def] using Measure.bind_dirac_eq_map _ hf

@[simp]
theorem toMeasure_bind_of_discrete [DiscreteMeasurableSpace α] (r : Resumption P α)
    (k : α → Resumption P β) :
    (r.bind k).toMeasure μ = (r.toMeasure μ).bind fun a => (k a).toMeasure μ :=
  toMeasure_bind μ r .of_discrete

@[simp]
theorem toMeasure_bind_of_discrete' {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] (r : Resumption P α) (k : α → Resumption P β) :
    (r >>= k).toMeasure μ = (r.toMeasure μ).bind fun a => (k a).toMeasure μ :=
  toMeasure_bind_of_discrete μ r k

@[simp]
theorem toMeasure_map_of_discrete [DiscreteMeasurableSpace α] (r : Resumption P α)
    (f : α → β) : (r.map f).toMeasure μ = (r.toMeasure μ).map f :=
  toMeasure_map μ r .of_discrete

@[simp]
theorem toMeasure_map_of_discrete' {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] (r : Resumption P α) (f : α → β) :
    (f <$> r).toMeasure μ = (r.toMeasure μ).map f :=
  toMeasure_map_of_discrete μ r f

/-- With probability measures on responses, the output measure has total mass at most one; the
missing mass is the probability of running forever. -/
theorem toMeasure_univ_le_one [∀ a, IsProbabilityMeasure (μ a)] (r : Resumption P α) :
    r.toMeasure μ Set.univ ≤ 1 := by
  rw [toMeasure, Measure.iSup_apply_of_monotone (monotone_approxMeasure μ r) MeasurableSet.univ]
  refine iSup_le fun n => ?_
  induction n generalizing r with
  | zero => cases r <;> simp
  | succ n ih => cases r with
    | pure a => simp
    | lift_bind a k =>
      simpa [Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable] using
        lintegral_mono (fun b => ih (k b)) |>.trans_eq (by simp)

instance [∀ a, IsProbabilityMeasure (μ a)] (r : Resumption P α) :
    IsFiniteMeasure (r.toMeasure μ) :=
  ⟨(toMeasure_univ_le_one μ r).trans_lt ENNReal.one_lt_top⟩

end Discrete

end PFunctor.Resumption

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)]
  [∀ a, DiscreteMeasurableSpace (P.B a)] {α : Type u} [MeasurableSpace α]
  (μ : (a : P.A) → Measure (P.B a))

/-- Embedding a free program as a resumption preserves its output measure. -/
@[simp]
theorem toMeasure_toResumption (x : P.FreeM α) : x.toResumption.toMeasure μ = x.toMeasure μ := by
  induction x <;> simp [*]

end PFunctor.FreeM

namespace PFunctor.M

variable {P : PFunctor.{uA, uB}} [∀ a, MeasurableSpace (P.B a)] {α : Type u} [MeasurableSpace α]
  (μ : (a : P.A) → Measure (P.B a))

/-- A resumption that never returns has no output: all of its mass is lost to divergence. -/
@[simp]
theorem toMeasure_toResumption (t : P.M) :
    (t.toResumption : Resumption P α).toMeasure μ = 0 := by
  have (n : ℕ) (t : P.M) : Resumption.approxMeasure μ n (t.toResumption : Resumption P α) = 0 := by
    induction n generalizing t with
    | zero => induction t using M.cases with | f x => cases x; simp
    | succ n ih => induction t using M.cases with | f x => cases x; simp [ih]
  simp [Resumption.toMeasure, this]

end PFunctor.M
