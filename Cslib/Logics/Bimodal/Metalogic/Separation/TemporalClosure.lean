/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.Defs
public import Cslib.Logics.Bimodal.Metalogic.Separation.Duality

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false

/-!
# Temporal Closure Infrastructure

Infrastructure for proving the temporal closure properties (that temporal
operators preserve separability) without axioms.

## Key Results

- `replaceBoxWithTop`: Normalize formula by replacing degenerate `box` with `top`
- `replace_box_equiv`: Box-normalization preserves `intEquiv`
- `replace_box_preserves_separated`: Box-normalization preserves syntactic separation
- `replace_box_separated_no_S_nested`: Box-free separated formulas satisfy `noSNestedInU`
- `noUNestedInS`: Dual of `noSNestedInU`
- `swap_no_U_nested_gives_no_S_nested`: Duality converts between the two predicates
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Box Normalization -/

/-- Replace all `box` nodes in a formula with `top` (imp bot bot). -/
def replaceBoxWithTop : Formula Atom -> Formula Atom
  | .atom a => .atom a
  | .bot => .bot
  | .imp phi psi => .imp (replaceBoxWithTop phi) (replaceBoxWithTop psi)
  | .box _ => .imp .bot .bot  -- top
  | .untl phi psi => .untl (replaceBoxWithTop phi) (replaceBoxWithTop psi)
  | .snce phi psi => .snce (replaceBoxWithTop phi) (replaceBoxWithTop psi)

/-- Box-normalization preserves semantic equivalence over integer time. -/
theorem replace_box_equiv (phi : Formula Atom) : intEquiv phi (replaceBoxWithTop phi) := by
  intro M t
  induction phi generalizing t with
  | atom _ => simp [replaceBoxWithTop, intTruth]
  | bot => simp [replaceBoxWithTop, intTruth]
  | imp a b ih1 ih2 =>
    simp [replaceBoxWithTop, intTruth]
    exact ⟨fun h hp => (ih2 t).mp (h ((ih1 t).mpr hp)),
           fun h hp => (ih2 t).mpr (h ((ih1 t).mp hp))⟩
  | box _ => simp [replaceBoxWithTop, intTruth]
  | untl a b ih1 ih2 =>
    simp [replaceBoxWithTop, intTruth]
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨s, hs, (ih1 s).mp h1, fun r hr1 hr2 => (ih2 r).mp (h2 r hr1 hr2)⟩
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨s, hs, (ih1 s).mpr h1, fun r hr1 hr2 => (ih2 r).mpr (h2 r hr1 hr2)⟩
  | snce a b ih1 ih2 =>
    simp [replaceBoxWithTop, intTruth]
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨s, hs, (ih1 s).mp h1, fun r hr1 hr2 => (ih2 r).mp (h2 r hr1 hr2)⟩
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨s, hs, (ih1 s).mpr h1, fun r hr1 hr2 => (ih2 r).mpr (h2 r hr1 hr2)⟩

/-- Box-normalization preserves isUFree. -/
theorem replace_box_preserves_U_free (phi : Formula Atom) (h : isUFree phi = true) :
    isUFree (replaceBoxWithTop phi) = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 => simp [isUFree] at h; simp [replaceBoxWithTop, isUFree, ih1 h.1, ih2 h.2]
  | box _ => simp [replaceBoxWithTop, isUFree]
  | untl _ _ => simp [isUFree] at h
  | snce a b ih1 ih2 => simp [isUFree] at h; simp [replaceBoxWithTop, isUFree, ih1 h.1, ih2 h.2]

/-- Box-normalization preserves isSFree. -/
theorem replace_box_preserves_S_free (phi : Formula Atom) (h : isSFree phi = true) :
    isSFree (replaceBoxWithTop phi) = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 => simp [isSFree] at h; simp [replaceBoxWithTop, isSFree, ih1 h.1, ih2 h.2]
  | box _ => simp [replaceBoxWithTop, isSFree]
  | untl a b ih1 ih2 => simp [isSFree] at h; simp [replaceBoxWithTop, isSFree, ih1 h.1, ih2 h.2]
  | snce _ _ => simp [isSFree] at h

/-- Box-normalization preserves syntactic separation. -/
theorem replace_box_preserves_separated (phi : Formula Atom)
    (h : isSyntacticallySeparated phi = true) :
    isSyntacticallySeparated (replaceBoxWithTop phi) = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [isSyntacticallySeparated] at h
    simp [replaceBoxWithTop, isSyntacticallySeparated, ih1 h.1, ih2 h.2]
  | box _ => simp [replaceBoxWithTop, isSyntacticallySeparated]
  | untl a b _ih1 _ih2 =>
    simp [isSyntacticallySeparated] at h
    simp [replaceBoxWithTop, isSyntacticallySeparated,
          replace_box_preserves_S_free a h.1, replace_box_preserves_S_free b h.2]
  | snce a b _ih1 _ih2 =>
    simp [isSyntacticallySeparated] at h
    simp [replaceBoxWithTop, isSyntacticallySeparated,
          replace_box_preserves_U_free a h.1, replace_box_preserves_U_free b h.2]

/-! ## noSNestedInU for Box-Free Separated Formulas -/

/-- U-free formulas satisfy noSNestedInU (vacuously: no untl nodes). -/
theorem u_free_no_S_nested (phi : Formula Atom) (h : isUFree phi = true) :
    noSNestedInU phi := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 => simp [isUFree] at h; exact ⟨ih1 h.1, ih2 h.2⟩
  | box a ih => simp [isUFree] at h; exact ih h
  | untl _ _ => simp [isUFree] at h
  | snce a b ih1 ih2 => simp [isUFree] at h; exact ⟨ih1 h.1, ih2 h.2⟩

/-- S-free formulas satisfy noSNestedInU (untl args inherit S-freeness). -/
theorem s_free_no_S_nested (phi : Formula Atom) (h : isSFree phi = true) :
    noSNestedInU phi := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 => simp [isSFree] at h; exact ⟨ih1 h.1, ih2 h.2⟩
  | box a ih => simp [isSFree] at h; exact ih h
  | untl a b _ih1 _ih2 => simp [isSFree] at h; exact h
  | snce _ _ => simp [isSFree] at h

/-- A box-normalized separated formula satisfies noSNestedInU. -/
theorem replace_box_separated_no_S_nested (phi : Formula Atom)
    (h : isSyntacticallySeparated phi = true) :
    noSNestedInU (replaceBoxWithTop phi) := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 =>
    simp [isSyntacticallySeparated] at h
    simp [replaceBoxWithTop, noSNestedInU]
    exact ⟨ih1 h.1, ih2 h.2⟩
  | box _ =>
    simp [replaceBoxWithTop, noSNestedInU]
  | untl a b _ih1 _ih2 =>
    simp [isSyntacticallySeparated] at h
    simp [replaceBoxWithTop, noSNestedInU]
    exact ⟨replace_box_preserves_S_free a h.1, replace_box_preserves_S_free b h.2⟩
  | snce a b _ih1 _ih2 =>
    simp [isSyntacticallySeparated] at h
    simp [replaceBoxWithTop, noSNestedInU]
    exact ⟨u_free_no_S_nested (replaceBoxWithTop a) (replace_box_preserves_U_free a h.1),
           u_free_no_S_nested (replaceBoxWithTop b) (replace_box_preserves_U_free b h.2)⟩

/-! ## Dual Predicate: noUNestedInS -/

/-- The formula has no U (untl) nested within any S (snce) argument. -/
def noUNestedInS : Formula Atom -> Prop
  | .atom _ => True
  | .bot => True
  | .imp phi psi => noUNestedInS phi ∧ noUNestedInS psi
  | .box phi => noUNestedInS phi
  | .untl phi psi => noUNestedInS phi ∧ noUNestedInS psi
  | .snce phi psi => isUFree phi = true ∧ isUFree psi = true

/-- swapTemporal converts noUNestedInS to noSNestedInU. -/
theorem swap_no_U_nested_gives_no_S_nested (phi : Formula Atom)
    (h : noUNestedInS phi) : noSNestedInU phi.swapTemporal := by
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

/-- swapTemporal converts noSNestedInU to noUNestedInS. -/
theorem swap_no_S_nested_gives_no_U_nested (phi : Formula Atom)
    (h : noSNestedInU phi) : noUNestedInS phi.swapTemporal := by
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

/-- A box-normalized separated formula also satisfies noUNestedInS. -/
theorem replace_box_separated_no_U_nested (phi : Formula Atom)
    (h : isSyntacticallySeparated phi = true) :
    noUNestedInS (replaceBoxWithTop phi) := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 =>
    simp [isSyntacticallySeparated] at h
    simp [replaceBoxWithTop, noUNestedInS]
    exact ⟨ih1 h.1, ih2 h.2⟩
  | box _ =>
    simp [replaceBoxWithTop, noUNestedInS]
  | untl a b _ih1 _ih2 =>
    simp [isSyntacticallySeparated] at h
    simp [replaceBoxWithTop, noUNestedInS]
    exact ⟨s_free_no_U_nested (replaceBoxWithTop a) (replace_box_preserves_S_free a h.1),
           s_free_no_U_nested (replaceBoxWithTop b) (replace_box_preserves_S_free b h.2)⟩
  | snce a b _ih1 _ih2 =>
    simp [isSyntacticallySeparated] at h
    simp [replaceBoxWithTop, noUNestedInS]
    exact ⟨replace_box_preserves_U_free a h.1, replace_box_preserves_U_free b h.2⟩
where
  u_free_no_U_nested (phi : Formula Atom) (h : isUFree phi = true) : noUNestedInS phi := by
    induction phi with
    | atom _ => trivial
    | bot => trivial
    | imp a b ih1 ih2 => simp [isUFree] at h; exact ⟨ih1 h.1, ih2 h.2⟩
    | box a ih => simp [isUFree] at h; exact ih h
    | untl _ _ => simp [isUFree] at h
    | snce a b _ih1 _ih2 => simp [isUFree] at h; exact h
  s_free_no_U_nested (phi : Formula Atom) (h : isSFree phi = true) : noUNestedInS phi := by
    induction phi with
    | atom _ => trivial
    | bot => trivial
    | imp a b ih1 ih2 => simp [isSFree] at h; exact ⟨ih1 h.1, ih2 h.2⟩
    | box a ih => simp [isSFree] at h; exact ih h
    | untl a b ih1 ih2 => simp [isSFree] at h; exact ⟨ih1 h.1, ih2 h.2⟩
    | snce _ _ => simp [isSFree] at h

/-! ## Key Structural Properties for Temporal Closure -/

/-- snce of box-normalized separated formulas satisfies noSNestedInU. -/
theorem snce_of_boxfree_sep_no_S_nested (phi psi : Formula Atom)
    (h1 : isSyntacticallySeparated phi = true)
    (h2 : isSyntacticallySeparated psi = true) :
    noSNestedInU (.snce (replaceBoxWithTop phi) (replaceBoxWithTop psi)) := by
  simp [noSNestedInU]
  exact ⟨replace_box_separated_no_S_nested phi h1,
         replace_box_separated_no_S_nested psi h2⟩

/-- allPast of box-normalized separated formula satisfies noSNestedInU. -/
theorem allPast_of_boxfree_sep_no_S_nested (phi : Formula Atom)
    (h : isSyntacticallySeparated phi = true) :
    noSNestedInU (.allPast (replaceBoxWithTop phi)) := by
  simp only [no_S_nested_in_U_allPast]
  exact replace_box_separated_no_S_nested phi h

/-- untl of box-normalized separated formulas satisfies noUNestedInS. -/
theorem untl_of_boxfree_sep_no_U_nested (phi psi : Formula Atom)
    (h1 : isSyntacticallySeparated phi = true)
    (h2 : isSyntacticallySeparated psi = true) :
    noUNestedInS (.untl (replaceBoxWithTop phi) (replaceBoxWithTop psi)) := by
  simp [noUNestedInS]
  exact ⟨replace_box_separated_no_U_nested phi h1,
         replace_box_separated_no_U_nested psi h2⟩

/-- allFuture of box-normalized separated formula satisfies noUNestedInS. -/
theorem allFuture_of_boxfree_sep_no_U_nested (phi : Formula Atom)
    (h : isSyntacticallySeparated phi = true) :
    noUNestedInS (.allFuture (replaceBoxWithTop phi)) := by
  simp only [Formula.allFuture, Formula.neg, Formula.someFuture, Formula.top,
    noUNestedInS, and_true]
  exact replace_box_separated_no_U_nested phi h

/-! ## Congruence Lemmas for Box Normalization -/

/-- snce preserves intEquiv under box normalization of arguments. -/
theorem snce_replace_box_equiv (phi psi : Formula Atom) :
    intEquiv (.snce phi psi)
      (.snce (replaceBoxWithTop phi) (replaceBoxWithTop psi)) := by
  intro M t; constructor
  · rintro ⟨s, hst, h1, h2⟩
    exact ⟨s, hst, (replace_box_equiv phi M s).mp h1,
           fun r hr1 hr2 => (replace_box_equiv psi M r).mp (h2 r hr1 hr2)⟩
  · rintro ⟨s, hst, h1, h2⟩
    exact ⟨s, hst, (replace_box_equiv phi M s).mpr h1,
           fun r hr1 hr2 => (replace_box_equiv psi M r).mpr (h2 r hr1 hr2)⟩

/-- allPast preserves intEquiv under box normalization. -/
theorem allPast_replace_box_equiv (phi : Formula Atom) :
    intEquiv (.allPast phi) (.allPast (replaceBoxWithTop phi)) := by
  intro M t; simp only [int_truth_allPast]; constructor
  · intro h s hs; exact (replace_box_equiv phi M s).mp (h s hs)
  · intro h s hs; exact (replace_box_equiv phi M s).mpr (h s hs)

/-- untl preserves intEquiv under box normalization of arguments. -/
theorem untl_replace_box_equiv (phi psi : Formula Atom) :
    intEquiv (.untl phi psi)
      (.untl (replaceBoxWithTop phi) (replaceBoxWithTop psi)) := by
  intro M t; constructor
  · rintro ⟨s, hts, h1, h2⟩
    exact ⟨s, hts, (replace_box_equiv phi M s).mp h1,
           fun r hr1 hr2 => (replace_box_equiv psi M r).mp (h2 r hr1 hr2)⟩
  · rintro ⟨s, hts, h1, h2⟩
    exact ⟨s, hts, (replace_box_equiv phi M s).mpr h1,
           fun r hr1 hr2 => (replace_box_equiv psi M r).mpr (h2 r hr1 hr2)⟩

/-- allFuture preserves intEquiv under box normalization. -/
theorem allFuture_replace_box_equiv (phi : Formula Atom) :
    intEquiv (.allFuture phi) (.allFuture (replaceBoxWithTop phi)) := by
  intro M t; simp only [int_truth_allFuture]; constructor
  · intro h s hs; exact (replace_box_equiv phi M s).mp (h s hs)
  · intro h s hs; exact (replace_box_equiv phi M s).mpr (h s hs)

/-! ## Junction-Depth Helpers -/

/-- junctionDepthS = 0 implies U-free. -/
theorem junction_depth_S_zero_imp_U_free (phi : Formula Atom) (h : junctionDepthS phi = 0) :
    isUFree phi = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [junctionDepthS] at h; simp [isUFree, ih1 (by omega), ih2 (by omega)]
  | box a ih => simp [junctionDepthS] at h; simp [isUFree, ih h]
  | untl _ _ => simp [junctionDepthS] at h
  | snce a b ih1 ih2 =>
    simp [junctionDepthS] at h; simp [isUFree, ih1 (by omega), ih2 (by omega)]

/-- junctionDepthU = 0 implies S-free. -/
theorem junction_depth_U_zero_imp_S_free (phi : Formula Atom) (h : junctionDepthU phi = 0) :
    isSFree phi = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [junctionDepthU] at h; simp [isSFree, ih1 (by omega), ih2 (by omega)]
  | box a ih => simp [junctionDepthU] at h; simp [isSFree, ih h]
  | untl a b ih1 ih2 =>
    simp [junctionDepthU] at h; simp [isSFree, ih1 (by omega), ih2 (by omega)]
  | snce _ _ => simp [junctionDepthU] at h

/-- S-free formulas have junctionDepth = 0. -/
theorem s_free_junction_depth_zero (phi : Formula Atom) (h : isSFree phi = true) :
    junctionDepth phi = 0 := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [isSFree] at h; simp [junctionDepth, ih1 h.1, ih2 h.2]
  | box a ih => simp [isSFree] at h; simp [junctionDepth, ih h]
  | untl a b ih1 ih2 =>
    simp [isSFree] at h
    simp [junctionDepth, junctionDepthU]
    have : junctionDepthU a = 0 := s_free_junction_depth_U_zero a h.1
    have : junctionDepthU b = 0 := s_free_junction_depth_U_zero b h.2
    omega
  | snce _ _ => simp [isSFree] at h
where
  s_free_junction_depth_U_zero (phi : Formula Atom) (h : isSFree phi = true) :
      junctionDepthU phi = 0 := by
    induction phi with
    | atom _ => rfl
    | bot => rfl
    | imp a b ih1 ih2 =>
      simp [isSFree] at h; simp [junctionDepthU, ih1 h.1, ih2 h.2]
    | box a ih => simp [isSFree] at h; simp [junctionDepthU, ih h]
    | untl a b ih1 ih2 =>
      simp [isSFree] at h; simp [junctionDepthU, ih1 h.1, ih2 h.2]
    | snce _ _ => simp [isSFree] at h

/-- U-free formulas have junctionDepth = 0. -/
theorem u_free_junction_depth_zero (phi : Formula Atom) (h : isUFree phi = true) :
    junctionDepth phi = 0 := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [isUFree] at h; simp [junctionDepth, ih1 h.1, ih2 h.2]
  | box a ih => simp [isUFree] at h; simp [junctionDepth, ih h]
  | untl _ _ => simp [isUFree] at h
  | snce a b ih1 ih2 =>
    simp [isUFree] at h
    simp [junctionDepth, junctionDepthS]
    have : junctionDepthS a = 0 := u_free_junction_depth_S_zero a h.1
    have : junctionDepthS b = 0 := u_free_junction_depth_S_zero b h.2
    omega
where
  u_free_junction_depth_S_zero (phi : Formula Atom) (h : isUFree phi = true) :
      junctionDepthS phi = 0 := by
    induction phi with
    | atom _ => rfl
    | bot => rfl
    | imp a b ih1 ih2 =>
      simp [isUFree] at h; simp [junctionDepthS, ih1 h.1, ih2 h.2]
    | box a ih => simp [isUFree] at h; simp [junctionDepthS, ih h]
    | untl _ _ => simp [isUFree] at h
    | snce a b ih1 ih2 =>
      simp [isUFree] at h; simp [junctionDepthS, ih1 h.1, ih2 h.2]

/-- The snce of two box-normalized separated formulas has junctionDepth ≤ 1. -/
theorem snce_of_boxfree_sep_jd_le_one (phi psi : Formula Atom)
    (h1 : isSyntacticallySeparated phi = true)
    (h2 : isSyntacticallySeparated psi = true) :
    junctionDepth (.snce (replaceBoxWithTop phi) (replaceBoxWithTop psi)) ≤ 1 := by
  simp [junctionDepth]
  constructor
  · exact replace_box_jdS_le_one phi h1
  · exact replace_box_jdS_le_one psi h2
where
  replace_box_jdS_le_one (phi : Formula Atom) (h : isSyntacticallySeparated phi = true) :
      junctionDepthS (replaceBoxWithTop phi) ≤ 1 := by
    induction phi with
    | atom _ => simp [replaceBoxWithTop, junctionDepthS]
    | bot => simp [replaceBoxWithTop, junctionDepthS]
    | imp a b ih1 ih2 =>
      simp [isSyntacticallySeparated] at h
      simp [replaceBoxWithTop, junctionDepthS]
      exact ⟨ih1 h.1, ih2 h.2⟩
    | box _ =>
      simp [replaceBoxWithTop, junctionDepthS]
    | untl a b _ih1 _ih2 =>
      simp [isSyntacticallySeparated] at h
      simp [replaceBoxWithTop, junctionDepthS]
      have ha := s_free_junction_depth_zero (replaceBoxWithTop a) (replace_box_preserves_S_free a h.1)
      have hb := s_free_junction_depth_zero (replaceBoxWithTop b) (replace_box_preserves_S_free b h.2)
      omega
    | snce a b _ih1 _ih2 =>
      simp [isSyntacticallySeparated] at h
      simp [replaceBoxWithTop, junctionDepthS]
      have ha := u_free_junction_depth_zero.u_free_junction_depth_S_zero
        (replaceBoxWithTop a) (replace_box_preserves_U_free a h.1)
      have hb := u_free_junction_depth_zero.u_free_junction_depth_S_zero
        (replaceBoxWithTop b) (replace_box_preserves_U_free b h.2)
      omega

/-! ## Expand Temporal -/

/-- Replace all `allPast` and `allFuture` with their definitions.
    With 6-constructor Formula, this is the identity function. -/
def expandTemporal : Formula Atom → Formula Atom
  | .atom a => .atom a
  | .bot => .bot
  | .imp φ ψ => .imp (expandTemporal φ) (expandTemporal ψ)
  | .box φ => .box φ
  | .untl φ ψ => .untl (expandTemporal φ) (expandTemporal ψ)
  | .snce φ ψ => .snce (expandTemporal φ) (expandTemporal ψ)

/-- With 6-constructor Formula, expandTemporal is the identity function. -/
@[simp] theorem expand_temporal_id (φ : Formula Atom) : expandTemporal φ = φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 => simp only [expandTemporal, ih1, ih2]
  | box _ => simp only [expandTemporal]
  | untl a b ih1 ih2 => simp only [expandTemporal, ih1, ih2]
  | snce a b ih1 ih2 => simp only [expandTemporal, ih1, ih2]

/-- expandTemporal preserves semantic equivalence. -/
theorem expand_temporal_equiv (φ : Formula Atom) : intEquiv φ (expandTemporal φ) := by
  rw [expand_temporal_id]; exact int_equiv_refl _

/-- Predicate: formula contains no `allPast` or `allFuture` constructors. -/
def hasNoAllpastAllfuture : Formula Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp φ ψ => hasNoAllpastAllfuture φ && hasNoAllpastAllfuture ψ
  | .box _ => true
  | .untl φ ψ => hasNoAllpastAllfuture φ && hasNoAllpastAllfuture ψ
  | .snce φ ψ => hasNoAllpastAllfuture φ && hasNoAllpastAllfuture ψ

/-- With 6-constructor Formula, hasNoAllpastAllfuture is trivially true. -/
@[simp] theorem has_no_allpast_allfuture_true (φ : Formula Atom) :
    hasNoAllpastAllfuture φ = true := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 => simp only [hasNoAllpastAllfuture, ih1, ih2, Bool.and_self]
  | box _ => rfl
  | untl a b ih1 ih2 => simp only [hasNoAllpastAllfuture, ih1, ih2, Bool.and_self]
  | snce a b ih1 ih2 => simp only [hasNoAllpastAllfuture, ih1, ih2, Bool.and_self]

/-- In the restricted fragment, JD=0 implies syntactically separated. -/
theorem expanded_jd_zero_imp_separated (φ : Formula Atom)
    (hexp : hasNoAllpastAllfuture φ = true)
    (hjd : junctionDepth φ = 0) :
    isSyntacticallySeparated φ = true := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b iha ihb =>
    simp only [junctionDepth] at hjd
    simp only [isSyntacticallySeparated,
      iha (has_no_allpast_allfuture_true a) (by omega),
      ihb (has_no_allpast_allfuture_true b) (by omega), Bool.and_self]
  | box _ => rfl
  | untl a b _iha _ihb =>
    simp [junctionDepth] at hjd
    have ha := junction_depth_U_zero_imp_S_free a (by omega)
    have hb := junction_depth_U_zero_imp_S_free b (by omega)
    simp [isSyntacticallySeparated, ha, hb]
  | snce a b _iha _ihb =>
    simp [junctionDepth] at hjd
    have ha := junction_depth_S_zero_imp_U_free a (by omega)
    have hb := junction_depth_S_zero_imp_U_free b (by omega)
    simp [isSyntacticallySeparated, ha, hb]

/-- In the restricted fragment, a U-free formula is syntactically separated. -/
theorem restricted_u_free_separated (phi : Formula Atom)
    (hrestr : hasNoAllpastAllfuture phi = true)
    (huf : isUFree phi = true) :
    isSyntacticallySeparated phi = true :=
  expanded_jd_zero_imp_separated phi hrestr (u_free_junction_depth_zero phi huf)

end Cslib.Logic.Bimodal.Metalogic.Separation
