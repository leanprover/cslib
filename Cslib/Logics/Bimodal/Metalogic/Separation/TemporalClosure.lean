/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Separation.Defs
import Cslib.Logics.Bimodal.Metalogic.Separation.Duality

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false

/-!
# Temporal Closure Infrastructure

Infrastructure for proving the temporal closure properties (that temporal
operators preserve separability) without axioms.

## Key Results

- `replace_box_with_top`: Normalize formula by replacing degenerate `box` with `top`
- `replace_box_equiv`: Box-normalization preserves `int_equiv`
- `replace_box_preserves_separated`: Box-normalization preserves syntactic separation
- `replace_box_separated_no_S_nested`: Box-free separated formulas satisfy `no_S_nested_in_U`
- `no_U_nested_in_S`: Dual of `no_S_nested_in_U`
- `swap_no_U_nested_gives_no_S_nested`: Duality converts between the two predicates
-/

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Box Normalization -/

/-- Replace all `box` nodes in a formula with `top` (imp bot bot). -/
def replace_box_with_top : Formula Atom -> Formula Atom
  | .atom a => .atom a
  | .bot => .bot
  | .imp phi psi => .imp (replace_box_with_top phi) (replace_box_with_top psi)
  | .box _ => .imp .bot .bot  -- top
  | .untl phi psi => .untl (replace_box_with_top phi) (replace_box_with_top psi)
  | .snce phi psi => .snce (replace_box_with_top phi) (replace_box_with_top psi)

/-- Box-normalization preserves semantic equivalence over integer time. -/
theorem replace_box_equiv (phi : Formula Atom) : int_equiv phi (replace_box_with_top phi) := by
  intro M t
  induction phi generalizing t with
  | atom _ => simp [replace_box_with_top, int_truth]
  | bot => simp [replace_box_with_top, int_truth]
  | imp a b ih1 ih2 =>
    simp [replace_box_with_top, int_truth]
    exact ⟨fun h hp => (ih2 t).mp (h ((ih1 t).mpr hp)),
           fun h hp => (ih2 t).mpr (h ((ih1 t).mp hp))⟩
  | box _ => simp [replace_box_with_top, int_truth]
  | untl a b ih1 ih2 =>
    simp [replace_box_with_top, int_truth]
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨s, hs, (ih1 s).mp h1, fun r hr1 hr2 => (ih2 r).mp (h2 r hr1 hr2)⟩
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨s, hs, (ih1 s).mpr h1, fun r hr1 hr2 => (ih2 r).mpr (h2 r hr1 hr2)⟩
  | snce a b ih1 ih2 =>
    simp [replace_box_with_top, int_truth]
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨s, hs, (ih1 s).mp h1, fun r hr1 hr2 => (ih2 r).mp (h2 r hr1 hr2)⟩
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨s, hs, (ih1 s).mpr h1, fun r hr1 hr2 => (ih2 r).mpr (h2 r hr1 hr2)⟩

/-- Box-normalization preserves is_U_free. -/
theorem replace_box_preserves_U_free (phi : Formula Atom) (h : is_U_free phi = true) :
    is_U_free (replace_box_with_top phi) = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 => simp [is_U_free] at h; simp [replace_box_with_top, is_U_free, ih1 h.1, ih2 h.2]
  | box _ => simp [replace_box_with_top, is_U_free]
  | untl _ _ => simp [is_U_free] at h
  | snce a b ih1 ih2 => simp [is_U_free] at h; simp [replace_box_with_top, is_U_free, ih1 h.1, ih2 h.2]

/-- Box-normalization preserves is_S_free. -/
theorem replace_box_preserves_S_free (phi : Formula Atom) (h : is_S_free phi = true) :
    is_S_free (replace_box_with_top phi) = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 => simp [is_S_free] at h; simp [replace_box_with_top, is_S_free, ih1 h.1, ih2 h.2]
  | box _ => simp [replace_box_with_top, is_S_free]
  | untl a b ih1 ih2 => simp [is_S_free] at h; simp [replace_box_with_top, is_S_free, ih1 h.1, ih2 h.2]
  | snce _ _ => simp [is_S_free] at h

/-- Box-normalization preserves syntactic separation. -/
theorem replace_box_preserves_separated (phi : Formula Atom)
    (h : is_syntactically_separated phi = true) :
    is_syntactically_separated (replace_box_with_top phi) = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [is_syntactically_separated] at h
    simp [replace_box_with_top, is_syntactically_separated, ih1 h.1, ih2 h.2]
  | box _ => simp [replace_box_with_top, is_syntactically_separated]
  | untl a b _ih1 _ih2 =>
    simp [is_syntactically_separated] at h
    simp [replace_box_with_top, is_syntactically_separated,
          replace_box_preserves_S_free a h.1, replace_box_preserves_S_free b h.2]
  | snce a b _ih1 _ih2 =>
    simp [is_syntactically_separated] at h
    simp [replace_box_with_top, is_syntactically_separated,
          replace_box_preserves_U_free a h.1, replace_box_preserves_U_free b h.2]

/-! ## no_S_nested_in_U for Box-Free Separated Formulas -/

/-- U-free formulas satisfy no_S_nested_in_U (vacuously: no untl nodes). -/
theorem u_free_no_S_nested (phi : Formula Atom) (h : is_U_free phi = true) :
    no_S_nested_in_U phi := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 => simp [is_U_free] at h; exact ⟨ih1 h.1, ih2 h.2⟩
  | box a ih => simp [is_U_free] at h; exact ih h
  | untl _ _ => simp [is_U_free] at h
  | snce a b ih1 ih2 => simp [is_U_free] at h; exact ⟨ih1 h.1, ih2 h.2⟩

/-- S-free formulas satisfy no_S_nested_in_U (untl args inherit S-freeness). -/
theorem s_free_no_S_nested (phi : Formula Atom) (h : is_S_free phi = true) :
    no_S_nested_in_U phi := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 => simp [is_S_free] at h; exact ⟨ih1 h.1, ih2 h.2⟩
  | box a ih => simp [is_S_free] at h; exact ih h
  | untl a b _ih1 _ih2 => simp [is_S_free] at h; exact h
  | snce _ _ => simp [is_S_free] at h

/-- A box-normalized separated formula satisfies no_S_nested_in_U. -/
theorem replace_box_separated_no_S_nested (phi : Formula Atom)
    (h : is_syntactically_separated phi = true) :
    no_S_nested_in_U (replace_box_with_top phi) := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 =>
    simp [is_syntactically_separated] at h
    simp [replace_box_with_top, no_S_nested_in_U]
    exact ⟨ih1 h.1, ih2 h.2⟩
  | box _ =>
    simp [replace_box_with_top, no_S_nested_in_U]
  | untl a b _ih1 _ih2 =>
    simp [is_syntactically_separated] at h
    simp [replace_box_with_top, no_S_nested_in_U]
    exact ⟨replace_box_preserves_S_free a h.1, replace_box_preserves_S_free b h.2⟩
  | snce a b _ih1 _ih2 =>
    simp [is_syntactically_separated] at h
    simp [replace_box_with_top, no_S_nested_in_U]
    exact ⟨u_free_no_S_nested (replace_box_with_top a) (replace_box_preserves_U_free a h.1),
           u_free_no_S_nested (replace_box_with_top b) (replace_box_preserves_U_free b h.2)⟩

/-! ## Dual Predicate: no_U_nested_in_S -/

/-- The formula has no U (untl) nested within any S (snce) argument. -/
def no_U_nested_in_S : Formula Atom -> Prop
  | .atom _ => True
  | .bot => True
  | .imp phi psi => no_U_nested_in_S phi ∧ no_U_nested_in_S psi
  | .box phi => no_U_nested_in_S phi
  | .untl phi psi => no_U_nested_in_S phi ∧ no_U_nested_in_S psi
  | .snce phi psi => is_U_free phi = true ∧ is_U_free psi = true

/-- swapTemporal converts no_U_nested_in_S to no_S_nested_in_U. -/
theorem swap_no_U_nested_gives_no_S_nested (phi : Formula Atom)
    (h : no_U_nested_in_S phi) : no_S_nested_in_U phi.swapTemporal := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | box a ih => exact ih h
  | untl a b ih1 ih2 =>
    exact ⟨ih1 h.1, ih2 h.2⟩
  | snce a b _ih1 _ih2 =>
    obtain ⟨ha, hb⟩ := h
    constructor
    · rw [dual_S_free_iff_U_free]; exact ha
    · rw [dual_S_free_iff_U_free]; exact hb

/-- swapTemporal converts no_S_nested_in_U to no_U_nested_in_S. -/
theorem swap_no_S_nested_gives_no_U_nested (phi : Formula Atom)
    (h : no_S_nested_in_U phi) : no_U_nested_in_S phi.swapTemporal := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | box a ih => exact ih h
  | untl a b _ih1 _ih2 =>
    obtain ⟨ha, hb⟩ := h
    constructor
    · rw [dual_U_free_iff_S_free]; exact ha
    · rw [dual_U_free_iff_S_free]; exact hb
  | snce a b ih1 ih2 =>
    exact ⟨ih1 h.1, ih2 h.2⟩

/-- A box-normalized separated formula also satisfies no_U_nested_in_S. -/
theorem replace_box_separated_no_U_nested (phi : Formula Atom)
    (h : is_syntactically_separated phi = true) :
    no_U_nested_in_S (replace_box_with_top phi) := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 =>
    simp [is_syntactically_separated] at h
    simp [replace_box_with_top, no_U_nested_in_S]
    exact ⟨ih1 h.1, ih2 h.2⟩
  | box _ =>
    simp [replace_box_with_top, no_U_nested_in_S]
  | untl a b _ih1 _ih2 =>
    simp [is_syntactically_separated] at h
    simp [replace_box_with_top, no_U_nested_in_S]
    exact ⟨s_free_no_U_nested (replace_box_with_top a) (replace_box_preserves_S_free a h.1),
           s_free_no_U_nested (replace_box_with_top b) (replace_box_preserves_S_free b h.2)⟩
  | snce a b _ih1 _ih2 =>
    simp [is_syntactically_separated] at h
    simp [replace_box_with_top, no_U_nested_in_S]
    exact ⟨replace_box_preserves_U_free a h.1, replace_box_preserves_U_free b h.2⟩
where
  u_free_no_U_nested (phi : Formula Atom) (h : is_U_free phi = true) : no_U_nested_in_S phi := by
    induction phi with
    | atom _ => trivial
    | bot => trivial
    | imp a b ih1 ih2 => simp [is_U_free] at h; exact ⟨ih1 h.1, ih2 h.2⟩
    | box a ih => simp [is_U_free] at h; exact ih h
    | untl _ _ => simp [is_U_free] at h
    | snce a b _ih1 _ih2 => simp [is_U_free] at h; exact h
  s_free_no_U_nested (phi : Formula Atom) (h : is_S_free phi = true) : no_U_nested_in_S phi := by
    induction phi with
    | atom _ => trivial
    | bot => trivial
    | imp a b ih1 ih2 => simp [is_S_free] at h; exact ⟨ih1 h.1, ih2 h.2⟩
    | box a ih => simp [is_S_free] at h; exact ih h
    | untl a b ih1 ih2 => simp [is_S_free] at h; exact ⟨ih1 h.1, ih2 h.2⟩
    | snce _ _ => simp [is_S_free] at h

/-! ## Key Structural Properties for Temporal Closure -/

/-- snce of box-normalized separated formulas satisfies no_S_nested_in_U. -/
theorem snce_of_boxfree_sep_no_S_nested (phi psi : Formula Atom)
    (h1 : is_syntactically_separated phi = true)
    (h2 : is_syntactically_separated psi = true) :
    no_S_nested_in_U (.snce (replace_box_with_top phi) (replace_box_with_top psi)) := by
  simp [no_S_nested_in_U]
  exact ⟨replace_box_separated_no_S_nested phi h1,
         replace_box_separated_no_S_nested psi h2⟩

/-- allPast of box-normalized separated formula satisfies no_S_nested_in_U. -/
theorem allPast_of_boxfree_sep_no_S_nested (phi : Formula Atom)
    (h : is_syntactically_separated phi = true) :
    no_S_nested_in_U (.allPast (replace_box_with_top phi)) := by
  simp only [no_S_nested_in_U_allPast]
  exact replace_box_separated_no_S_nested phi h

/-- untl of box-normalized separated formulas satisfies no_U_nested_in_S. -/
theorem untl_of_boxfree_sep_no_U_nested (phi psi : Formula Atom)
    (h1 : is_syntactically_separated phi = true)
    (h2 : is_syntactically_separated psi = true) :
    no_U_nested_in_S (.untl (replace_box_with_top phi) (replace_box_with_top psi)) := by
  simp [no_U_nested_in_S]
  exact ⟨replace_box_separated_no_U_nested phi h1,
         replace_box_separated_no_U_nested psi h2⟩

/-- allFuture of box-normalized separated formula satisfies no_U_nested_in_S. -/
theorem allFuture_of_boxfree_sep_no_U_nested (phi : Formula Atom)
    (h : is_syntactically_separated phi = true) :
    no_U_nested_in_S (.allFuture (replace_box_with_top phi)) := by
  simp only [Formula.allFuture, Formula.neg, Formula.someFuture, Formula.top,
    no_U_nested_in_S, and_true]
  exact replace_box_separated_no_U_nested phi h

/-! ## Congruence Lemmas for Box Normalization -/

/-- snce preserves int_equiv under box normalization of arguments. -/
theorem snce_replace_box_equiv (phi psi : Formula Atom) :
    int_equiv (.snce phi psi)
      (.snce (replace_box_with_top phi) (replace_box_with_top psi)) := by
  intro M t; constructor
  · rintro ⟨s, hst, h1, h2⟩
    exact ⟨s, hst, (replace_box_equiv phi M s).mp h1,
           fun r hr1 hr2 => (replace_box_equiv psi M r).mp (h2 r hr1 hr2)⟩
  · rintro ⟨s, hst, h1, h2⟩
    exact ⟨s, hst, (replace_box_equiv phi M s).mpr h1,
           fun r hr1 hr2 => (replace_box_equiv psi M r).mpr (h2 r hr1 hr2)⟩

/-- allPast preserves int_equiv under box normalization. -/
theorem allPast_replace_box_equiv (phi : Formula Atom) :
    int_equiv (.allPast phi) (.allPast (replace_box_with_top phi)) := by
  intro M t; simp only [int_truth_allPast]; constructor
  · intro h s hs; exact (replace_box_equiv phi M s).mp (h s hs)
  · intro h s hs; exact (replace_box_equiv phi M s).mpr (h s hs)

/-- untl preserves int_equiv under box normalization of arguments. -/
theorem untl_replace_box_equiv (phi psi : Formula Atom) :
    int_equiv (.untl phi psi)
      (.untl (replace_box_with_top phi) (replace_box_with_top psi)) := by
  intro M t; constructor
  · rintro ⟨s, hts, h1, h2⟩
    exact ⟨s, hts, (replace_box_equiv phi M s).mp h1,
           fun r hr1 hr2 => (replace_box_equiv psi M r).mp (h2 r hr1 hr2)⟩
  · rintro ⟨s, hts, h1, h2⟩
    exact ⟨s, hts, (replace_box_equiv phi M s).mpr h1,
           fun r hr1 hr2 => (replace_box_equiv psi M r).mpr (h2 r hr1 hr2)⟩

/-- allFuture preserves int_equiv under box normalization. -/
theorem allFuture_replace_box_equiv (phi : Formula Atom) :
    int_equiv (.allFuture phi) (.allFuture (replace_box_with_top phi)) := by
  intro M t; simp only [int_truth_allFuture]; constructor
  · intro h s hs; exact (replace_box_equiv phi M s).mp (h s hs)
  · intro h s hs; exact (replace_box_equiv phi M s).mpr (h s hs)

/-! ## Junction-Depth Helpers -/

/-- junction_depth_S = 0 implies U-free. -/
theorem junction_depth_S_zero_imp_U_free (phi : Formula Atom) (h : junction_depth_S phi = 0) :
    is_U_free phi = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [junction_depth_S] at h; simp [is_U_free, ih1 (by omega), ih2 (by omega)]
  | box a ih => simp [junction_depth_S] at h; simp [is_U_free, ih h]
  | untl _ _ => simp [junction_depth_S] at h
  | snce a b ih1 ih2 =>
    simp [junction_depth_S] at h; simp [is_U_free, ih1 (by omega), ih2 (by omega)]

/-- junction_depth_U = 0 implies S-free. -/
theorem junction_depth_U_zero_imp_S_free (phi : Formula Atom) (h : junction_depth_U phi = 0) :
    is_S_free phi = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [junction_depth_U] at h; simp [is_S_free, ih1 (by omega), ih2 (by omega)]
  | box a ih => simp [junction_depth_U] at h; simp [is_S_free, ih h]
  | untl a b ih1 ih2 =>
    simp [junction_depth_U] at h; simp [is_S_free, ih1 (by omega), ih2 (by omega)]
  | snce _ _ => simp [junction_depth_U] at h

/-- S-free formulas have junction_depth = 0. -/
theorem s_free_junction_depth_zero (phi : Formula Atom) (h : is_S_free phi = true) :
    junction_depth phi = 0 := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [is_S_free] at h; simp [junction_depth, ih1 h.1, ih2 h.2]
  | box a ih => simp [is_S_free] at h; simp [junction_depth, ih h]
  | untl a b ih1 ih2 =>
    simp [is_S_free] at h
    simp [junction_depth, junction_depth_U]
    have : junction_depth_U a = 0 := s_free_junction_depth_U_zero a h.1
    have : junction_depth_U b = 0 := s_free_junction_depth_U_zero b h.2
    omega
  | snce _ _ => simp [is_S_free] at h
where
  s_free_junction_depth_U_zero (phi : Formula Atom) (h : is_S_free phi = true) :
      junction_depth_U phi = 0 := by
    induction phi with
    | atom _ => rfl
    | bot => rfl
    | imp a b ih1 ih2 =>
      simp [is_S_free] at h; simp [junction_depth_U, ih1 h.1, ih2 h.2]
    | box a ih => simp [is_S_free] at h; simp [junction_depth_U, ih h]
    | untl a b ih1 ih2 =>
      simp [is_S_free] at h; simp [junction_depth_U, ih1 h.1, ih2 h.2]
    | snce _ _ => simp [is_S_free] at h

/-- U-free formulas have junction_depth = 0. -/
theorem u_free_junction_depth_zero (phi : Formula Atom) (h : is_U_free phi = true) :
    junction_depth phi = 0 := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [is_U_free] at h; simp [junction_depth, ih1 h.1, ih2 h.2]
  | box a ih => simp [is_U_free] at h; simp [junction_depth, ih h]
  | untl _ _ => simp [is_U_free] at h
  | snce a b ih1 ih2 =>
    simp [is_U_free] at h
    simp [junction_depth, junction_depth_S]
    have : junction_depth_S a = 0 := u_free_junction_depth_S_zero a h.1
    have : junction_depth_S b = 0 := u_free_junction_depth_S_zero b h.2
    omega
where
  u_free_junction_depth_S_zero (phi : Formula Atom) (h : is_U_free phi = true) :
      junction_depth_S phi = 0 := by
    induction phi with
    | atom _ => rfl
    | bot => rfl
    | imp a b ih1 ih2 =>
      simp [is_U_free] at h; simp [junction_depth_S, ih1 h.1, ih2 h.2]
    | box a ih => simp [is_U_free] at h; simp [junction_depth_S, ih h]
    | untl _ _ => simp [is_U_free] at h
    | snce a b ih1 ih2 =>
      simp [is_U_free] at h; simp [junction_depth_S, ih1 h.1, ih2 h.2]

/-- The snce of two box-normalized separated formulas has junction_depth ≤ 1. -/
theorem snce_of_boxfree_sep_jd_le_one (phi psi : Formula Atom)
    (h1 : is_syntactically_separated phi = true)
    (h2 : is_syntactically_separated psi = true) :
    junction_depth (.snce (replace_box_with_top phi) (replace_box_with_top psi)) ≤ 1 := by
  simp [junction_depth]
  constructor
  · exact replace_box_jdS_le_one phi h1
  · exact replace_box_jdS_le_one psi h2
where
  replace_box_jdS_le_one (phi : Formula Atom) (h : is_syntactically_separated phi = true) :
      junction_depth_S (replace_box_with_top phi) ≤ 1 := by
    induction phi with
    | atom _ => simp [replace_box_with_top, junction_depth_S]
    | bot => simp [replace_box_with_top, junction_depth_S]
    | imp a b ih1 ih2 =>
      simp [is_syntactically_separated] at h
      simp [replace_box_with_top, junction_depth_S]
      exact ⟨ih1 h.1, ih2 h.2⟩
    | box _ =>
      simp [replace_box_with_top, junction_depth_S]
    | untl a b _ih1 _ih2 =>
      simp [is_syntactically_separated] at h
      simp [replace_box_with_top, junction_depth_S]
      have ha := s_free_junction_depth_zero (replace_box_with_top a) (replace_box_preserves_S_free a h.1)
      have hb := s_free_junction_depth_zero (replace_box_with_top b) (replace_box_preserves_S_free b h.2)
      omega
    | snce a b _ih1 _ih2 =>
      simp [is_syntactically_separated] at h
      simp [replace_box_with_top, junction_depth_S]
      have ha := u_free_junction_depth_zero.u_free_junction_depth_S_zero
        (replace_box_with_top a) (replace_box_preserves_U_free a h.1)
      have hb := u_free_junction_depth_zero.u_free_junction_depth_S_zero
        (replace_box_with_top b) (replace_box_preserves_U_free b h.2)
      omega

/-! ## Expand Temporal -/

/-- Replace all `allPast` and `allFuture` with their definitions.
    With 6-constructor Formula, this is the identity function. -/
def expand_temporal : Formula Atom → Formula Atom
  | .atom a => .atom a
  | .bot => .bot
  | .imp φ ψ => .imp (expand_temporal φ) (expand_temporal ψ)
  | .box φ => .box φ
  | .untl φ ψ => .untl (expand_temporal φ) (expand_temporal ψ)
  | .snce φ ψ => .snce (expand_temporal φ) (expand_temporal ψ)

/-- With 6-constructor Formula, expand_temporal is the identity function. -/
@[simp] theorem expand_temporal_id (φ : Formula Atom) : expand_temporal φ = φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 => simp only [expand_temporal, ih1, ih2]
  | box _ => simp only [expand_temporal]
  | untl a b ih1 ih2 => simp only [expand_temporal, ih1, ih2]
  | snce a b ih1 ih2 => simp only [expand_temporal, ih1, ih2]

/-- expand_temporal preserves semantic equivalence. -/
theorem expand_temporal_equiv (φ : Formula Atom) : int_equiv φ (expand_temporal φ) := by
  rw [expand_temporal_id]; exact int_equiv_refl _

/-- Predicate: formula contains no `allPast` or `allFuture` constructors. -/
def has_no_allpast_allfuture : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ => has_no_allpast_allfuture φ && has_no_allpast_allfuture ψ
  | .box _ => true
  | .untl φ ψ => has_no_allpast_allfuture φ && has_no_allpast_allfuture ψ
  | .snce φ ψ => has_no_allpast_allfuture φ && has_no_allpast_allfuture ψ

/-- With 6-constructor Formula, has_no_allpast_allfuture is trivially true. -/
@[simp] theorem has_no_allpast_allfuture_true (φ : Formula Atom) :
    has_no_allpast_allfuture φ = true := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 => simp only [has_no_allpast_allfuture, ih1, ih2, Bool.and_self]
  | box _ => rfl
  | untl a b ih1 ih2 => simp only [has_no_allpast_allfuture, ih1, ih2, Bool.and_self]
  | snce a b ih1 ih2 => simp only [has_no_allpast_allfuture, ih1, ih2, Bool.and_self]

/-- In the restricted fragment, JD=0 implies syntactically separated. -/
theorem expanded_jd_zero_imp_separated (φ : Formula Atom)
    (hexp : has_no_allpast_allfuture φ = true)
    (hjd : junction_depth φ = 0) :
    is_syntactically_separated φ = true := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b iha ihb =>
    simp only [junction_depth] at hjd
    simp only [is_syntactically_separated,
      iha (has_no_allpast_allfuture_true a) (by omega),
      ihb (has_no_allpast_allfuture_true b) (by omega), Bool.and_self]
  | box _ => rfl
  | untl a b _iha _ihb =>
    simp [junction_depth] at hjd
    have ha := junction_depth_U_zero_imp_S_free a (by omega)
    have hb := junction_depth_U_zero_imp_S_free b (by omega)
    simp [is_syntactically_separated, ha, hb]
  | snce a b _iha _ihb =>
    simp [junction_depth] at hjd
    have ha := junction_depth_S_zero_imp_U_free a (by omega)
    have hb := junction_depth_S_zero_imp_U_free b (by omega)
    simp [is_syntactically_separated, ha, hb]

/-- In the restricted fragment, a U-free formula is syntactically separated. -/
theorem restricted_u_free_separated (phi : Formula Atom)
    (hrestr : has_no_allpast_allfuture phi = true)
    (huf : is_U_free phi = true) :
    is_syntactically_separated phi = true :=
  expanded_jd_zero_imp_separated phi hrestr (u_free_junction_depth_zero phi huf)

end Cslib.Logic.Bimodal.Metalogic.Separation
