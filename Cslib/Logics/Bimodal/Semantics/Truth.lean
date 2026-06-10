/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Semantics.TaskModel
public import Cslib.Logics.Bimodal.Semantics.WorldHistory
public import Cslib.Logics.Bimodal.Syntax.Formula

/-!
# Truth - Truth Evaluation in Task Semantics

This module defines truth evaluation for TM formulas in task models.

## Main Definitions

- `truth_at`: Truth of a formula at a model-history-time triple

## Main Results

- Basic truth lemmas (bot_false, imp_iff, atom_iff_of_domain, etc.)
- ShiftClosed definition and Set.univ_shift_closed
- Time-shift preservation theorems

## Note on Variable Naming

Frame variables use `ℱ` rather than `F` because `F` is a scoped
notation for `Formula.some_future` within `Cslib.Logic.Bimodal`.
Similarly, `G`, `H`, `P` are scoped notations. Gamma uses `Γ`.
-/

@[expose] public section

namespace Cslib.Logic.Bimodal

variable {Atom : Type*}
  {D : Type*} [AddCommGroup D] [LinearOrder D]
  [IsOrderedAddMonoid D] {ℱ : TaskFrame D}

/--
Truth of a formula at a model-history-time triple.

The evaluation is defined recursively on formula structure:
- Atoms: true iff t is in domain AND valuation says so
- Bot (⊥): always false
- Implication: standard material conditional
- Box (□): true iff φ true at all world histories in Ω at time t
- Until U(φ,ψ): ∃ s > t, φ(s) ∧ ∀ r ∈ (t,s), ψ(r)
- Since S(φ,ψ): ∃ s < t, φ(s) ∧ ∀ r ∈ (s,t), ψ(r)
-/
def truth_at (M : TaskModel Atom ℱ) (Omega : Set (WorldHistory ℱ))
    (τ : WorldHistory ℱ) (t : D) : Formula Atom → Prop
  | Formula.atom p =>
    ∃ (ht : τ.domain t), M.valuation (τ.states t ht) p
  | Formula.bot => False
  | Formula.imp φ ψ =>
    truth_at M Omega τ t φ → truth_at M Omega τ t ψ
  | Formula.box φ =>
    ∀ (σ : WorldHistory ℱ), σ ∈ Omega →
      truth_at M Omega σ t φ
  | Formula.untl φ ψ =>
    ∃ s : D, t < s ∧ truth_at M Omega τ s φ ∧
      ∀ r : D, t < r → r < s → truth_at M Omega τ r ψ
  | Formula.snce φ ψ =>
    ∃ s : D, s < t ∧ truth_at M Omega τ s φ ∧
      ∀ r : D, s < r → r < t → truth_at M Omega τ r ψ

namespace Truth

/--
Bot (⊥) is false everywhere.
-/
theorem bot_false
    {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D]
    {ℱ : TaskFrame D} {M : TaskModel Atom ℱ}
    {τ : WorldHistory ℱ}
    {t : D}
    (Omega : Set (WorldHistory ℱ)) :
    ¬(truth_at M Omega τ t Formula.bot) := by
  intro h
  exact h

/--
Truth of implication is material conditional.
-/
theorem imp_iff
    {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D]
    {ℱ : TaskFrame D} {M : TaskModel Atom ℱ}
    {τ : WorldHistory ℱ}
    {t : D}
    (Omega : Set (WorldHistory ℱ))
    (φ ψ : Formula Atom) :
    (truth_at M Omega τ t (φ.imp ψ)) ↔
      ((truth_at M Omega τ t φ) →
        (truth_at M Omega τ t ψ)) := by
  rfl

/--
Truth of atom at a time in the domain.
-/
theorem atom_iff_of_domain
    {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D]
    {ℱ : TaskFrame D} {M : TaskModel Atom ℱ}
    {τ : WorldHistory ℱ}
    {t : D} (ht : τ.domain t)
    (Omega : Set (WorldHistory ℱ))
    (p : Atom) :
    (truth_at M Omega τ t (Formula.atom p)) ↔
      M.valuation (τ.states t ht) p := by
  simp only [truth_at]
  constructor
  · intro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨ht, h⟩

/--
Truth of atom at a time outside the domain is false.
-/
theorem atom_false_of_not_domain
    {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D]
    {ℱ : TaskFrame D} {M : TaskModel Atom ℱ}
    {τ : WorldHistory ℱ}
    {t : D} (ht : ¬τ.domain t)
    (Omega : Set (WorldHistory ℱ))
    (p : Atom) :
    ¬(truth_at M Omega τ t (Formula.atom p)) := by
  simp only [truth_at]
  intro ⟨ht', _⟩
  exact ht ht'

/--
Truth of box: formula true at all histories in Omega.
-/
theorem box_iff
    {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D]
    {ℱ : TaskFrame D} {M : TaskModel Atom ℱ}
    {τ : WorldHistory ℱ}
    {t : D}
    (Omega : Set (WorldHistory ℱ))
    (φ : Formula Atom) :
    (truth_at M Omega τ t φ.box) ↔
      ∀ (σ : WorldHistory ℱ), σ ∈ Omega →
        (truth_at M Omega σ t φ) := by
  rfl

/--
Truth of some_future: existential future operator.
-/
@[simp] theorem some_future_iff
    {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D]
    {ℱ : TaskFrame D} {M : TaskModel Atom ℱ}
    {τ : WorldHistory ℱ}
    {t : D}
    (Omega : Set (WorldHistory ℱ))
    (φ : Formula Atom) :
    truth_at M Omega τ t (Formula.some_future φ) ↔
      ∃ s, t < s ∧ truth_at M Omega τ s φ := by
  simp only [truth_at]
  constructor
  · rintro ⟨s, hlt, hevent, _⟩
    exact ⟨s, hlt, hevent⟩
  · rintro ⟨s, hlt, hs⟩
    exact ⟨s, hlt, hs, fun _ _ _ h => h⟩

/--
Truth of some_past: existential past operator.
-/
@[simp] theorem some_past_iff
    {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D]
    {ℱ : TaskFrame D} {M : TaskModel Atom ℱ}
    {τ : WorldHistory ℱ}
    {t : D}
    (Omega : Set (WorldHistory ℱ))
    (φ : Formula Atom) :
    truth_at M Omega τ t (Formula.some_past φ) ↔
      ∃ s, s < t ∧ truth_at M Omega τ s φ := by
  simp only [truth_at]
  constructor
  · rintro ⟨s, hlt, hevent, _⟩
    exact ⟨s, hlt, hevent⟩
  · rintro ⟨s, hlt, hs⟩
    exact ⟨s, hlt, hs, fun _ _ _ h => h⟩

/--
Truth of all_future: universal future operator.
-/
@[simp] theorem future_iff
    {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D]
    {ℱ : TaskFrame D} {M : TaskModel Atom ℱ}
    {τ : WorldHistory ℱ}
    {t : D}
    (Omega : Set (WorldHistory ℱ))
    (φ : Formula Atom) :
    truth_at M Omega τ t φ.all_future ↔
      ∀ (s : D), t < s →
        truth_at M Omega τ s φ := by
  simp only [truth_at]
  constructor
  · intro h s hlt
    by_contra hns
    exact h ⟨s, hlt, hns,
      fun _ _ _ h => h⟩
  · intro h ⟨s, hlt, hevent, _⟩
    exact hevent (h s hlt)

/--
Truth of all_past: universal past operator.
-/
@[simp] theorem past_iff
    {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D]
    {ℱ : TaskFrame D} {M : TaskModel Atom ℱ}
    {τ : WorldHistory ℱ}
    {t : D}
    (Omega : Set (WorldHistory ℱ))
    (φ : Formula Atom) :
    truth_at M Omega τ t φ.all_past ↔
      ∀ (s : D), s < t →
        truth_at M Omega τ s φ := by
  simp only [truth_at]
  constructor
  · intro h s hlt
    by_contra hns
    exact h ⟨s, hlt, hns,
      fun _ _ _ h => h⟩
  · intro h ⟨s, hlt, hevent, _⟩
    exact hevent (h s hlt)

end Truth

/--
A set of world histories is shift-closed if shifting any history by
any amount keeps it in the set.
-/
def ShiftClosed (Omega : Set (WorldHistory ℱ)) : Prop :=
  ∀ σ ∈ Omega, ∀ (Δ : D),
    WorldHistory.time_shift σ Δ ∈ Omega

/--
The universal set of world histories is trivially shift-closed.
-/
theorem Set.univ_shift_closed :
    ShiftClosed (Set.univ : Set (WorldHistory ℱ)) := by
  intro σ _ Δ
  exact Set.mem_univ _

/-! ## Time-Shift Preservation -/

namespace TimeShift

/--
Truth transport across equal histories.
-/
theorem truth_history_eq (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ))
    (τ₁ τ₂ : WorldHistory ℱ) (t : D)
    (h_eq : τ₁ = τ₂) (φ : Formula Atom) :
    truth_at M Omega τ₁ t φ ↔
      truth_at M Omega τ₂ t φ := by
  cases h_eq
  rfl

/--
Truth at double time-shift with opposite amounts equals truth at
original history.
-/
theorem truth_double_shift_cancel (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ))
    (σ : WorldHistory ℱ) (Δ : D) (t : D)
    (φ : Formula Atom) :
    truth_at M Omega
      (WorldHistory.time_shift
        (WorldHistory.time_shift σ Δ) (-Δ)) t φ ↔
    truth_at M Omega σ t φ := by
  induction φ generalizing t with
  | atom p =>
    simp only [truth_at]
    constructor
    · intro ⟨ht', h⟩
      have ht : σ.domain t :=
        (WorldHistory.time_shift_time_shift_neg_domain_iff
          σ Δ t).mp ht'
      have h_eq :=
        WorldHistory.time_shift_time_shift_neg_states
          σ Δ t ht ht'
      exact ⟨ht, by rw [← h_eq]; exact h⟩
    · intro ⟨ht, h⟩
      have ht' :
        (WorldHistory.time_shift
          (WorldHistory.time_shift σ Δ) (-Δ)).domain t :=
        (WorldHistory.time_shift_time_shift_neg_domain_iff
          σ Δ t).mpr ht
      have h_eq :=
        WorldHistory.time_shift_time_shift_neg_states
          σ Δ t ht ht'
      exact ⟨ht', by rw [h_eq]; exact h⟩
  | bot =>
    simp only [truth_at]
  | imp ψ χ ih_ψ ih_χ =>
    simp only [truth_at]
    constructor
    · intro h h_ψ
      have h_ψ' := (ih_ψ t).mpr h_ψ
      exact (ih_χ t).mp (h h_ψ')
    · intro h h_ψ'
      have h_ψ := (ih_ψ t).mp h_ψ'
      exact (ih_χ t).mpr (h h_ψ)
  | box ψ ih =>
    simp only [truth_at]
  | untl φ ψ ih_φ ih_ψ =>
    simp only [truth_at]
    constructor
    · intro ⟨s, h_le, h_event, h_guard⟩
      exact ⟨s, h_le, (ih_φ s).mp h_event,
        fun r hr1 hr2 => (ih_ψ r).mp (h_guard r hr1 hr2)⟩
    · intro ⟨s, h_le, h_event, h_guard⟩
      exact ⟨s, h_le, (ih_φ s).mpr h_event,
        fun r hr1 hr2 => (ih_ψ r).mpr (h_guard r hr1 hr2)⟩
  | snce φ ψ ih_φ ih_ψ =>
    simp only [truth_at]
    constructor
    · intro ⟨s, h_le, h_event, h_guard⟩
      exact ⟨s, h_le, (ih_φ s).mp h_event,
        fun r hr1 hr2 => (ih_ψ r).mp (h_guard r hr1 hr2)⟩
    · intro ⟨s, h_le, h_event, h_guard⟩
      exact ⟨s, h_le, (ih_φ s).mpr h_event,
        fun r hr1 hr2 => (ih_ψ r).mpr (h_guard r hr1 hr2)⟩

/--
Time-shift preserves truth of formulas.

If σ is a history and Δ = y - x, then truth at (σ, y) equals truth
at (time_shift σ Δ, x).
-/
theorem time_shift_preserves_truth (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ))
    (h_sc : ShiftClosed Omega) (σ : WorldHistory ℱ)
    (x y : D) (φ : Formula Atom) :
    truth_at M Omega
      (WorldHistory.time_shift σ (y - x)) x φ ↔
      truth_at M Omega σ y φ := by
  induction φ generalizing x y σ with
  | atom p =>
    simp only [truth_at, WorldHistory.time_shift]
    have h_eq : x + (y - x) = y := by
      rw [add_sub, add_sub_cancel_left]
    constructor
    · intro ⟨hx, h⟩
      have hy : σ.domain y := by rw [← h_eq]; exact hx
      have h_states :=
        WorldHistory.states_eq_of_time_eq σ
          (x + (y - x)) y h_eq hx hy
      exact ⟨hy, by rw [← h_states]; exact h⟩
    · intro ⟨hy, h⟩
      have hx : σ.domain (x + (y - x)) := by
        rw [h_eq]; exact hy
      have h_states :=
        WorldHistory.states_eq_of_time_eq σ
          (x + (y - x)) y h_eq hx hy
      exact ⟨hx, by rw [h_states]; exact h⟩
  | bot =>
    simp only [truth_at]
  | imp ψ χ ih_ψ ih_χ =>
    simp only [truth_at]
    constructor
    · intro h h_psi
      have h_psi' := (ih_ψ σ x y).mpr h_psi
      exact (ih_χ σ x y).mp (h h_psi')
    · intro h h_psi'
      have h_psi := (ih_ψ σ x y).mp h_psi'
      exact (ih_χ σ x y).mpr (h h_psi)
  | box ψ ih =>
    simp only [truth_at]
    constructor
    · intro h_box_x ρ h_rho_mem
      have h_shifted_mem :
        WorldHistory.time_shift ρ (y - x) ∈ Omega :=
        h_sc ρ h_rho_mem (y - x)
      have h1 := h_box_x
        (WorldHistory.time_shift ρ (y - x)) h_shifted_mem
      exact (ih ρ x y).mp h1
    · intro h_box_y ρ h_rho_mem
      have h_shifted_mem :
        WorldHistory.time_shift ρ (x - y) ∈ Omega :=
        h_sc ρ h_rho_mem (x - y)
      have h1 := h_box_y
        (WorldHistory.time_shift ρ (x - y)) h_shifted_mem
      have h2 :=
        (ih (WorldHistory.time_shift ρ (x - y)) x y).mpr h1
      have h_cancel : y - x = -(x - y) :=
        (neg_sub x y).symm
      have h_hist_eq :
        WorldHistory.time_shift
          (WorldHistory.time_shift ρ (x - y)) (y - x) =
        WorldHistory.time_shift
          (WorldHistory.time_shift ρ (x - y))
          (-(x - y)) := by
        exact WorldHistory.time_shift_congr
          (WorldHistory.time_shift ρ (x - y))
          (y - x) (-(x - y)) h_cancel
      have h2' :=
        (truth_history_eq M Omega _ _ x h_hist_eq ψ).mp h2
      exact (truth_double_shift_cancel M Omega ρ
        (x - y) x ψ).mp h2'
  | untl φ ψ ih_φ ih_ψ =>
    -- φ is event (at witness s), ψ is guard (between)
    simp only [truth_at]
    constructor
    · -- (→) shifted at x → original at y
      intro ⟨s, h_x_lt_s, h_event_s, h_guard⟩
      refine ⟨s + (y - x), ?_, ?_, ?_⟩
      · -- y < s + (y - x)
        have h := add_lt_add_right h_x_lt_s (y - x)
        have h_eq : x + (y - x) = y := by
          rw [add_sub, add_sub_cancel_left]
        calc y = x + (y - x) := h_eq.symm
          _ = (y - x) + x := add_comm x (y - x)
          _ < (y - x) + s := h
          _ = s + (y - x) := add_comm (y - x) s
      · -- φ (event) at (σ, s + (y - x))
        have h_shift_eq2 : (s + (y - x)) - s = y - x :=
          add_sub_cancel_left s (y - x)
        have h_hist_eq :
          WorldHistory.time_shift σ
            ((s + (y - x)) - s) =
          WorldHistory.time_shift σ (y - x) := by
          exact WorldHistory.time_shift_congr σ
            ((s + (y - x)) - s) (y - x) h_shift_eq2
        have h_conv :=
          (truth_history_eq M Omega _ _ s
            h_hist_eq.symm φ).mp h_event_s
        exact (ih_φ σ s (s + (y - x))).mp h_conv
      · -- ψ (guard) between
        intro r h_y_lt_r h_r_lt_s'
        have h_x_lt_r' : x < r - (y - x) := by
          have h :=
            sub_lt_sub_right h_y_lt_r (y - x)
          simp only [sub_sub_cancel] at h
          exact h
        have h_r'_lt_s : r - (y - x) < s := by
          have h :=
            sub_lt_sub_right h_r_lt_s' (y - x)
          simp only [add_sub_cancel_right] at h
          exact h
        have h_grd :=
          h_guard (r - (y - x)) h_x_lt_r' h_r'_lt_s
        have h_shift_eq : r - (r - (y - x)) = y - x :=
          sub_sub_cancel r (y - x)
        have h_hist_eq :
          WorldHistory.time_shift σ
            (r - (r - (y - x))) =
          WorldHistory.time_shift σ (y - x) := by
          exact WorldHistory.time_shift_congr σ
            (r - (r - (y - x))) (y - x) h_shift_eq
        have h_conv :=
          (truth_history_eq M Omega _ _
            (r - (y - x)) h_hist_eq.symm ψ).mp h_grd
        exact (ih_ψ σ (r - (y - x)) r).mp h_conv
    · -- (←) original at y → shifted at x
      intro ⟨s, h_y_lt_s, h_event_s, h_guard⟩
      refine ⟨s - (y - x), ?_, ?_, ?_⟩
      · -- x < s - (y - x)
        have h :=
          sub_lt_sub_right h_y_lt_s (y - x)
        simp only [sub_sub_cancel] at h
        exact h
      · -- φ (event) at (shifted σ, s - (y - x))
        have h_shift_eq :
          s - (s - (y - x)) = y - x :=
          sub_sub_cancel s (y - x)
        have h_hist_eq :
          WorldHistory.time_shift σ
            (s - (s - (y - x))) =
          WorldHistory.time_shift σ (y - x) := by
          exact WorldHistory.time_shift_congr σ
            (s - (s - (y - x))) (y - x) h_shift_eq
        have h_conv :=
          (ih_φ σ (s - (y - x)) s).mpr h_event_s
        exact (truth_history_eq M Omega _ _
          (s - (y - x)) h_hist_eq φ).mp h_conv
      · -- ψ (guard) between
        intro r' h_x_lt_r' h_r'_lt_s'
        have h_y_lt_r : y < r' + (y - x) := by
          have h :=
            add_lt_add_right h_x_lt_r' (y - x)
          have h_eq : x + (y - x) = y := by
            rw [add_sub, add_sub_cancel_left]
          calc y = x + (y - x) := h_eq.symm
            _ = (y - x) + x := add_comm x (y - x)
            _ < (y - x) + r' := h
            _ = r' + (y - x) := add_comm (y - x) r'
        have h_r_lt_s : r' + (y - x) < s := by
          have h_eq : s - (y - x) + (y - x) = s :=
            sub_add_cancel s (y - x)
          calc r' + (y - x)
            < s - (y - x) + (y - x) :=
              add_lt_add_left h_r'_lt_s' (y - x)
            _ = s := h_eq
        have h_grd :=
          h_guard (r' + (y - x)) h_y_lt_r h_r_lt_s
        have h_shift_eq :
          (r' + (y - x)) - r' = y - x :=
          add_sub_cancel_left r' (y - x)
        have h_hist_eq :
          WorldHistory.time_shift σ
            ((r' + (y - x)) - r') =
          WorldHistory.time_shift σ (y - x) := by
          exact WorldHistory.time_shift_congr σ
            ((r' + (y - x)) - r') (y - x) h_shift_eq
        have h_conv :=
          (ih_ψ σ r' (r' + (y - x))).mpr h_grd
        exact (truth_history_eq M Omega _ _ r'
          h_hist_eq ψ).mp h_conv
  | snce φ ψ ih_φ ih_ψ =>
    -- φ is event (at witness s), ψ is guard (between)
    simp only [truth_at]
    constructor
    · -- (→) shifted at x → original at y
      intro ⟨s, h_s_lt_x, h_event_s, h_guard⟩
      refine ⟨s + (y - x), ?_, ?_, ?_⟩
      · -- s + (y - x) < y
        have h :=
          add_lt_add_right h_s_lt_x (y - x)
        calc s + (y - x)
          = (y - x) + s := add_comm s (y - x)
          _ < (y - x) + x := h
          _ = x + (y - x) := add_comm (y - x) x
          _ = y := by rw [add_sub, add_sub_cancel_left]
      · -- φ (event) at (σ, s + (y - x))
        have h_shift_eq :
          (s + (y - x)) - s = y - x :=
          add_sub_cancel_left s (y - x)
        have h_hist_eq :
          WorldHistory.time_shift σ
            ((s + (y - x)) - s) =
          WorldHistory.time_shift σ (y - x) := by
          exact WorldHistory.time_shift_congr σ
            ((s + (y - x)) - s) (y - x) h_shift_eq
        have h_conv :=
          (truth_history_eq M Omega _ _ s
            h_hist_eq.symm φ).mp h_event_s
        exact (ih_φ σ s (s + (y - x))).mp h_conv
      · -- ψ (guard) between
        intro r h_s'_lt_r h_r_lt_y
        have h_s_lt_r' : s < r - (y - x) := by
          have h :=
            sub_lt_sub_right h_s'_lt_r (y - x)
          simp only [add_sub_cancel_right] at h
          exact h
        have h_r'_lt_x : r - (y - x) < x := by
          have h :=
            sub_lt_sub_right h_r_lt_y (y - x)
          simp only [sub_sub_cancel] at h
          exact h
        have h_grd :=
          h_guard (r - (y - x)) h_s_lt_r' h_r'_lt_x
        have h_shift_eq :
          r - (r - (y - x)) = y - x :=
          sub_sub_cancel r (y - x)
        have h_hist_eq :
          WorldHistory.time_shift σ
            (r - (r - (y - x))) =
          WorldHistory.time_shift σ (y - x) := by
          exact WorldHistory.time_shift_congr σ
            (r - (r - (y - x))) (y - x) h_shift_eq
        have h_conv :=
          (truth_history_eq M Omega _ _
            (r - (y - x)) h_hist_eq.symm ψ).mp h_grd
        exact (ih_ψ σ (r - (y - x)) r).mp h_conv
    · -- (←) original at y → shifted at x
      intro ⟨s, h_s_lt_y, h_event_s, h_guard⟩
      refine ⟨s - (y - x), ?_, ?_, ?_⟩
      · -- s - (y - x) < x
        have h :=
          sub_lt_sub_right h_s_lt_y (y - x)
        simp only [sub_sub_cancel] at h
        exact h
      · -- φ (event) at (shifted σ, s - (y - x))
        have h_shift_eq :
          s - (s - (y - x)) = y - x :=
          sub_sub_cancel s (y - x)
        have h_hist_eq :
          WorldHistory.time_shift σ
            (s - (s - (y - x))) =
          WorldHistory.time_shift σ (y - x) := by
          exact WorldHistory.time_shift_congr σ
            (s - (s - (y - x))) (y - x) h_shift_eq
        have h_conv :=
          (ih_φ σ (s - (y - x)) s).mpr h_event_s
        exact (truth_history_eq M Omega _ _
          (s - (y - x)) h_hist_eq φ).mp h_conv
      · -- ψ (guard) between
        intro r' h_s'_lt_r' h_r'_lt_x
        have h_s_lt_r : s < r' + (y - x) := by
          calc s
            = s - (y - x) + (y - x) :=
              (sub_add_cancel s (y - x)).symm
            _ < r' + (y - x) :=
              add_lt_add_left h_s'_lt_r' (y - x)
        have h_r_lt_y : r' + (y - x) < y := by
          have h_eq : x + (y - x) = y := by
            rw [add_sub, add_sub_cancel_left]
          calc r' + (y - x)
            < x + (y - x) :=
              add_lt_add_left h_r'_lt_x (y - x)
            _ = y := h_eq
        have h_grd :=
          h_guard (r' + (y - x)) h_s_lt_r h_r_lt_y
        have h_shift_eq :
          (r' + (y - x)) - r' = y - x :=
          add_sub_cancel_left r' (y - x)
        have h_hist_eq :
          WorldHistory.time_shift σ
            ((r' + (y - x)) - r') =
          WorldHistory.time_shift σ (y - x) := by
          exact WorldHistory.time_shift_congr σ
            ((r' + (y - x)) - r') (y - x) h_shift_eq
        have h_conv :=
          (ih_ψ σ r' (r' + (y - x))).mpr h_grd
        exact (truth_history_eq M Omega _ _ r'
          h_hist_eq ψ).mp h_conv

/--
Corollary: For any history σ at time y, there exists a history at
time x where the same formulas are true.
-/
theorem exists_shifted_history (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ))
    (h_sc : ShiftClosed Omega) (σ : WorldHistory ℱ)
    (x y : D) (φ : Formula Atom) :
    truth_at M Omega σ y φ ↔
    truth_at M Omega
      (WorldHistory.time_shift σ (y - x)) x φ := by
  exact (time_shift_preserves_truth M Omega h_sc σ
    x y φ).symm

end TimeShift

end Cslib.Logic.Bimodal
