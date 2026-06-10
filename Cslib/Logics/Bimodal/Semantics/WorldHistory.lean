/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Semantics.TaskFrame

/-!
# WorldHistory - World Histories for Task Semantics

This module defines world histories, which are functions from time domains
to world states.

## Main Definitions

- `WorldHistory F`: World history structure with convex domain and
  task constraint
- `WorldHistory.time_shift`: Time-shifted history construction

## Main Results

- Example world histories (universal, trivial)
- Time-shift lemmas (domain, states, cancellation)
- Order reversal lemmas for temporal duality
-/

@[expose] public section

namespace Cslib.Logic.Bimodal

/--
World history for a task frame.

A world history assigns a world state to each time in its domain,
such that the history respects the task relation of the frame.
-/
structure WorldHistory {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] (F : TaskFrame D) where
  /-- Domain predicate (which times are in the history) -/
  domain : D → Prop
  /-- Convexity constraint: domain has no temporal gaps. -/
  convex : ∀ (x z : D), domain x → domain z →
    ∀ (y : D), x ≤ y → y ≤ z → domain y
  /-- State assignment function. -/
  states : (t : D) → domain t → F.WorldState
  /-- Task relation respect constraint. -/
  respects_task : ∀ (s t : D) (hs : domain s) (ht : domain t),
    s ≤ t → F.task_rel (states s hs) (t - s) (states t ht)

namespace WorldHistory

variable {D : Type*} [AddCommGroup D] [LinearOrder D]
  [IsOrderedAddMonoid D] {F : TaskFrame D}

/--
Universal world history over all time (requires explicit reflexivity
proof).
-/
def universal (F : TaskFrame D) (w : F.WorldState)
    (h_refl : ∀ d : D, F.task_rel w d w) : WorldHistory F where
  domain := fun _ => True
  convex := by
    intros x z hx hz y hxy hyz
    exact True.intro
  states := fun _ _ => w
  respects_task := by
    intros s t hs ht hst
    exact h_refl (t - s)

/--
Trivial world history for the trivial frame.
-/
def trivial {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] :
    WorldHistory (TaskFrame.trivial_frame (D := D)) where
  domain := fun _ => True
  convex := by
    intros x z hx hz y hxy hyz
    exact True.intro
  states := fun _ _ => ()
  respects_task := by
    intros s t hs ht hst
    exact True.intro

/--
Universal world history for trivial frame with a specific constant
state.
-/
def universal_trivialFrame {D : Type*} [AddCommGroup D]
    [LinearOrder D] [IsOrderedAddMonoid D]
    (w : (TaskFrame.trivial_frame (D := D)).WorldState) :
    WorldHistory (TaskFrame.trivial_frame (D := D)) where
  domain := fun _ => True
  convex := by
    intros x z hx hz y hxy hyz
    exact True.intro
  states := fun _ _ => w
  respects_task := by
    intros s t hs ht hst
    exact True.intro

/--
Universal world history for nat frame with a specific constant Nat
state.
-/
def universal_natFrame {D : Type*} [AddCommGroup D]
    [LinearOrder D] [IsOrderedAddMonoid D] (n : Nat) :
    WorldHistory (TaskFrame.nat_frame (D := D)) where
  domain := fun _ => True
  convex := by
    intros x z hx hz y hxy hyz
    exact True.intro
  states := fun _ _ => n
  respects_task := by
    intros s t hs ht hst
    right
    rfl

/--
Get the state at a time (helper function that bundles membership
proof).
-/
def state_at (τ : WorldHistory F) (t : D) (h : τ.domain t) :
    F.WorldState :=
  τ.states t h

/-! ## Time-Shift Construction -/

/--
Time-shifted history construction.

Given history `σ` and shift offset `Δ`, construct history `τ` where:
- `τ.domain z ↔ σ.domain (z + Δ)`
- `τ.states z = σ.states (z + Δ)`
-/
def time_shift (σ : WorldHistory F) (Δ : D) : WorldHistory F where
  domain := fun z => σ.domain (z + Δ)
  convex := by
    intros x z hx hz y hxy hyz
    have hxy' : x + Δ ≤ y + Δ := by
      rw [add_comm x, add_comm y]
      exact add_le_add_right hxy Δ
    have hyz' : y + Δ ≤ z + Δ := by
      rw [add_comm y, add_comm z]
      exact add_le_add_right hyz Δ
    exact σ.convex (x + Δ) (z + Δ) hx hz (y + Δ) hxy' hyz'
  states := fun z hz => σ.states (z + Δ) hz
  respects_task := by
    intros s t hs ht hst
    have h_shifted : s + Δ ≤ t + Δ := by
      rw [add_comm s, add_comm t]
      exact add_le_add_right hst Δ
    have h_duration : (t + Δ) - (s + Δ) = t - s := by
      rw [add_sub_add_right_eq_sub]
    rw [← h_duration]
    exact σ.respects_task (s + Δ) (t + Δ) hs ht h_shifted

/--
Time-shift preserves domain membership (forward direction).
-/
theorem time_shift_domain_iff (σ : WorldHistory F) (Δ z : D) :
    (time_shift σ Δ).domain z ↔ σ.domain (z + Δ) := by
  rfl

/--
Inverse time-shift: shifting by -Δ undoes shifting by Δ on the
domain.
-/
theorem time_shift_inverse_domain (σ : WorldHistory F) (Δ : D)
    (z : D) :
    (time_shift (time_shift σ Δ) (-Δ)).domain z ↔
      σ.domain z := by
  simp only [time_shift]
  constructor
  · intro h
    have : z + -Δ + Δ = z := by
      rw [add_assoc, neg_add_cancel, add_zero]
    rw [this] at h
    exact h
  · intro h
    have : z + -Δ + Δ = z := by
      rw [add_assoc, neg_add_cancel, add_zero]
    rw [this]
    exact h

/--
States are equal when times are provably equal (proof irrelevance).
-/
theorem states_eq_of_time_eq (σ : WorldHistory F) (t₁ t₂ : D)
    (h : t₁ = t₂) (ht₁ : σ.domain t₁) (ht₂ : σ.domain t₂) :
    σ.states t₁ ht₁ = σ.states t₂ ht₂ := by
  subst h
  rfl

/--
Double time-shift cancels: states at
(time_shift (time_shift σ Δ) (-Δ)) equal states at σ.
-/
theorem time_shift_time_shift_states (σ : WorldHistory F) (Δ : D)
    (t : D) (ht : σ.domain t)
    (ht' : (time_shift (time_shift σ Δ) (-Δ)).domain t) :
    (time_shift (time_shift σ Δ) (-Δ)).states t ht' =
      σ.states t ht := by
  simp only [time_shift]
  have h_eq : t + -Δ + Δ = t := by
    rw [add_assoc, neg_add_cancel, add_zero]
  exact states_eq_of_time_eq σ (t + -Δ + Δ) t h_eq _ ht

/--
Extensionality lemma for time_shift: shifting by equal amounts
gives equal histories.
-/
theorem time_shift_congr (σ : WorldHistory F) (Δ₁ Δ₂ : D)
    (h : Δ₁ = Δ₂) :
    time_shift σ Δ₁ = time_shift σ Δ₂ := by
  subst h
  rfl

/--
Domain membership for time_shift by zero is equivalent to original
domain.
-/
theorem time_shift_zero_domain_iff (σ : WorldHistory F) (z : D) :
    (time_shift σ 0).domain z ↔ σ.domain z := by
  simp only [time_shift, add_zero]

/--
Domain membership for double time-shift with opposite amounts
equals original.
-/
theorem time_shift_time_shift_neg_domain_iff (σ : WorldHistory F)
    (Δ : D) (z : D) :
    (time_shift (time_shift σ Δ) (-Δ)).domain z ↔
      σ.domain z := by
  simp only [time_shift]
  have h : z + -Δ + Δ = z := by
    rw [add_assoc, neg_add_cancel, add_zero]
  constructor
  · intro hd; rw [h] at hd; exact hd
  · intro hd; rw [h]; exact hd

/--
States at double time-shift with opposite amounts equals original
states.
-/
theorem time_shift_time_shift_neg_states (σ : WorldHistory F)
    (Δ : D) (t : D) (ht : σ.domain t)
    (ht' : (time_shift (time_shift σ Δ) (-Δ)).domain t) :
    (time_shift (time_shift σ Δ) (-Δ)).states t ht' =
      σ.states t ht := by
  simp only [time_shift]
  have h_eq : t + -Δ + Δ = t := by
    rw [add_assoc, neg_add_cancel, add_zero]
  exact states_eq_of_time_eq σ (t + -Δ + Δ) t h_eq _ ht

/-! ## Order Reversal Lemmas -/

/--
Group inverse reverses strict order: s < t ↔ -t < -s
-/
theorem neg_lt_neg_iff (s t : D) : s < t ↔ -t < -s := by
  constructor
  · intro h
    exact neg_lt_neg h
  · intro h
    have hs : s = -(-s) := by simp
    have ht : t = -(-t) := by simp
    rw [hs, ht]
    exact neg_lt_neg h

/--
Group inverse reverses non-strict order: s ≤ t ↔ -t ≤ -s
-/
theorem neg_le_neg_iff (s t : D) : s ≤ t ↔ -t ≤ -s := by
  constructor
  · intro h
    exact neg_le_neg h
  · intro h
    have hs : s = -(-s) := by simp
    have ht : t = -(-t) := by simp
    rw [hs, ht]
    exact neg_le_neg h

omit [LinearOrder D] [IsOrderedAddMonoid D] in
/--
Double negation is identity: -(-t) = t
-/
theorem neg_neg_eq (t : D) : -(-t) = t := by
  simp

omit [LinearOrder D] [IsOrderedAddMonoid D] in
/--
Group inverse is injective: -s = -t ↔ s = t
-/
theorem neg_injective (s t : D) : -s = -t ↔ s = t := by
  constructor
  · intro h
    have : -(-s) = -(-t) := by rw [h]
    simp only [neg_neg] at this
    exact this
  · intro h
    rw [h]

end WorldHistory

end Cslib.Logic.Bimodal
