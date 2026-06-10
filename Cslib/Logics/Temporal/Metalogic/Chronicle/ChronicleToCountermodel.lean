/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Temporal.Metalogic.Chronicle.ChronicleConstruction
import Cslib.Logics.Temporal.Semantics.Satisfies

/-!
# Chronicle-to-Countermodel Extraction

This module extracts a `TemporalModel` from the chronicle limit construction.
Given an MCS `A`, the chronicle construction produces a limit domain `limit_dom`
and a point function `limit_f`. We define:

- `ChronicleSubtype`: the subtype `{x : Rat // x ∈ limit_dom A h_mcs}`
- Order instances: `LinearOrder`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`
- `chronicle_model`: the `TemporalModel` with valuation `V(p)(t) := atom p ∈ limit_f(t.val)`

## Main Results

- `chronicle_linear_order`: LinearOrder on ChronicleSubtype (inherited from Rat)
- `chronicle_nontrivial`: At least two distinct points in limit_dom
- `chronicle_no_max_order`: No maximum element
- `chronicle_no_min_order`: No minimum element
- `chronicle_model`: The TemporalModel on ChronicleSubtype

## References

- Burgess 1982: Section 2, Claim 2.11
-/

set_option linter.style.setOption false
set_option linter.flexible false
set_option maxHeartbeats 1600000

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}
variable [Denumerable (Formula Atom)]

/-- The subtype of rationals in the limit domain. -/
abbrev ChronicleSubtype (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A) :=
  {x : Rat // x ∈ limit_dom A h_mcs}

/-- The canonical zero point in the limit domain. -/
noncomputable def chronicle_zero
    (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A) :
    ChronicleSubtype A h_mcs :=
  ⟨0, zero_mem_limit_dom A h_mcs⟩

/-- Nontrivial: the limit domain has at least two points.

Proof: 0 ∈ limit_dom. Since limit_f(0) = A is an MCS, F(⊤) ∈ A by seriality.
By limit_F_resolution, there exists y > 0 in limit_dom. So 0 ≠ y. -/
instance chronicle_nontrivial (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A) :
    Nontrivial (ChronicleSubtype A h_mcs) := by
  have h0 := zero_mem_limit_dom A h_mcs
  have h_mcs_0 := limit_c0 A h_mcs 0 h0
  have h_f_zero : limit_f A h_mcs 0 = A := limit_f_zero A h_mcs
  have h_f_top : Formula.some_future Formula.top ∈ limit_f A h_mcs 0 := by
    rw [h_f_zero]
    have h_top : Formula.top ∈ A := by
      apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
      unfold temporalDerivationSystem Temporal.Deriv
      exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
    exact temporal_implication_property h_mcs
      (temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
        (by unfold temporalDerivationSystem Temporal.Deriv
            exact ⟨.axiom [] _ (.serial_future) trivial⟩))
      h_top
  obtain ⟨y, hy, hlt, _⟩ := limit_F_resolution A h_mcs 0 h0 Formula.top h_f_top
  exact ⟨⟨⟨0, h0⟩, ⟨y, hy⟩, by simp; exact ne_of_lt hlt⟩⟩

/-- NoMaxOrder: for any point t in the limit domain, there exists a strictly
larger point.

Proof: limit_f(t) is an MCS by limit_c0, so F(⊤) ∈ limit_f(t) by seriality.
By limit_F_resolution, there exists y > t in limit_dom. -/
instance chronicle_no_max_order (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A) :
    NoMaxOrder (ChronicleSubtype A h_mcs) := by
  constructor
  intro ⟨t, ht⟩
  have h_mcs_t := limit_c0 A h_mcs t ht
  have h_f_top : Formula.some_future Formula.top ∈ limit_f A h_mcs t := by
    have h_top : Formula.top ∈ limit_f A h_mcs t := by
      apply temporal_closed_under_derivation h_mcs_t (L := []) (fun _ h => nomatch h)
      unfold temporalDerivationSystem Temporal.Deriv
      exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
    exact temporal_implication_property h_mcs_t
      (temporal_closed_under_derivation h_mcs_t (L := []) (fun _ h => nomatch h)
        (by unfold temporalDerivationSystem Temporal.Deriv
            exact ⟨.axiom [] _ (.serial_future) trivial⟩))
      h_top
  obtain ⟨y, hy, hlt, _⟩ := limit_F_resolution A h_mcs t ht Formula.top h_f_top
  exact ⟨⟨y, hy⟩, hlt⟩

/-- NoMinOrder: for any point t in the limit domain, there exists a strictly
smaller point.

Proof: limit_f(t) is an MCS, so P(⊤) ∈ limit_f(t) by seriality.
By limit_P_resolution, there exists y < t in limit_dom. -/
instance chronicle_no_min_order (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A) :
    NoMinOrder (ChronicleSubtype A h_mcs) := by
  constructor
  intro ⟨t, ht⟩
  have h_mcs_t := limit_c0 A h_mcs t ht
  have h_p_top : Formula.some_past Formula.top ∈ limit_f A h_mcs t := by
    have h_top : Formula.top ∈ limit_f A h_mcs t := by
      apply temporal_closed_under_derivation h_mcs_t (L := []) (fun _ h => nomatch h)
      unfold temporalDerivationSystem Temporal.Deriv
      exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
    exact temporal_implication_property h_mcs_t
      (temporal_closed_under_derivation h_mcs_t (L := []) (fun _ h => nomatch h)
        (by unfold temporalDerivationSystem Temporal.Deriv
            exact ⟨.axiom [] _ (.serial_past) trivial⟩))
      h_top
  obtain ⟨y, hy, hlt, _⟩ := limit_P_resolution A h_mcs t ht Formula.top h_p_top
  exact ⟨⟨y, hy⟩, hlt⟩

/-- The chronicle temporal model: valuation maps atoms to their membership in
the limit point function. -/
noncomputable def chronicle_model
    (A : Set (Formula Atom)) (h_mcs : Temporal.SetMaximalConsistent A) :
    TemporalModel (ChronicleSubtype A h_mcs) Atom where
  valuation := fun t p => Formula.atom p ∈ limit_f A h_mcs t.val

end Cslib.Logic.Temporal.Metalogic.Chronicle
