/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleConstruction
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.CanonicalModel
public import Cslib.Logics.Bimodal.Metalogic.Bundle.UntilSinceCoherence
public import Cslib.Logics.Bimodal.Metalogic.Algebraic.ParametricCompleteness
public import Cslib.Logics.Bimodal.Metalogic.Algebraic.RestrictedParametricTruthLemma
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.CountableDenseLinearOrder
public import Mathlib.Order.SuccPred.LinearLocallyFinite
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Data.Rat.Cast.Order
/-!
# Chronicle-to-Countermodel Integration

Converts the Burgess chronicle construction into a countermodel suitable for
the BX completeness theorem, via a case split on density vs discreteness.

## Strategy

The chronicle construction produces, for any MCS A:
- `limitDom fc A h_mcs`: a countable set of rationals containing 0
- `limitF fc A h_mcs`: a function assigning MCS to each domain point
- `limit_f_zero`: limitF(0) = A
- `limit_c0`: every domain point maps to an MCS
- `limit_forward_G`/`limit_backward_H`: G/H propagation on domain
- `limit_satisfies_c5_strong`/`limit_satisfies_c5'_strong`: Until/Since (C5)
- `limit_satisfies_c4`/`limit_satisfies_c4'`: Counterexample elimination (C4)

### Dense case (D = Rat via Cantor iso)

When `F'T = neg(U(T,bot))` is in all domain MCS's, the limit domain is dense,
so `LimitDomSubtype ≃o Rat` via Cantor's theorem. The FMCS on Rat transports
forward_G/backward_H through the isomorphism.

### Discrete case (D = Int via Z-iso)

When `U(T,bot)` is in all domain MCS's, the limit domain is discrete with
SuccOrder/PredOrder. The Z-isomorphism `LimitDomSubtype ≃o Int` via Mathlib's
`orderIsoIntOfLinearSuccPredArch` additionally requires `IsSuccArchimedean`,
which has one remaining sorry (the well-founded termination argument for the
succ chain reaching any target element).

## References

- Burgess 1982: "Axioms for tense logic II: Time periods"
- Task 117 plan: specs/117_.../plans/04_case-split-completeness.md
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}
variable [Denumerable (Formula Atom)]

open Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricCanonical
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricHistory
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricTruthLemma
open Cslib.Logic.Bimodal.Metalogic.Algebraic.ParametricCompleteness
open Cslib.Logic.Bimodal.Metalogic.Algebraic.RestrictedParametricTruthLemma
open Cslib.Logic.Bimodal.Theorems.Propositional
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.Perpetuity
open Cslib.Logic.Bimodal.Metalogic.BXCanonical
open Cslib.Logic.Bimodal.Metalogic.BXCanonical.CanonicalModel
open Classical

/-! ## Limit Domain Properties

The subtype `{q : Rat // q ∈ limitDom fc A h_mcs}` inherits `LinearOrder` from `Rat`.
We prove the typeclass prerequisites `Countable`, `NoMinOrder`, `NoMaxOrder`, `Nonempty`.
-/

/-- The limit domain as a subtype of the rationals. -/
abbrev LimitDomSubtype (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    :=
  {q : Rat // q ∈ limitDom fc A h_mcs}

/--
`LimitDomSubtype` is countable: `limitDom` is a countable union of finite sets
(each `omegaChainVal(n).dom` is a `Finset Rat`).
-/
instance limitDomSubtype_countable (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    :
    Countable (LimitDomSubtype fc A h_mcs) :=
  Subtype.countable

/--
Helper: for any x in `limitDom`, there exists y > x in `limitDom`.

Proof: The seriality axiom `serial_future` gives `F(top)` in every MCS.
Since `limit_c0` assigns an MCS to x, we have `F(top) ∈ limitF(x)`.
Then `limit_F_resolution` produces y > x in `limitDom`.
-/
theorem limit_dom_no_max (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (x : Rat) (hx : x ∈ limitDom fc A h_mcs) :
    ∃ y ∈ limitDom fc A h_mcs, x < y := by
  have h_mcs_x := limit_c0 fc A h_mcs x hx
  have h_top : (Formula.bot.imp Formula.bot) ∈ limitF fc A h_mcs x :=
    theoremInMcsFc h_mcs_x (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))
  have h_F_top : Formula.someFuture (Formula.bot.imp Formula.bot) ∈ limitF fc A h_mcs x :=
    SetMaximalConsistent.implication_property h_mcs_x
      (theoremInMcsFc h_mcs_x (DerivationTree.axiom [] _ Axiom.serial_future trivial)) h_top
  obtain ⟨y, hy, hxy, _⟩ := limit_F_resolution fc A h_mcs x hx _ h_F_top
  exact ⟨y, hy, hxy⟩

/--
Helper: for any x in `limitDom`, there exists y < x in `limitDom`.

Proof: The seriality axiom `serial_past` gives `P(top)` in every MCS.
Since `limit_c0` assigns an MCS to x, we have `P(top) ∈ limitF(x)`.
Then `limit_P_resolution` produces y < x in `limitDom`.
-/
theorem limit_dom_no_min (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (x : Rat) (hx : x ∈ limitDom fc A h_mcs) :
    ∃ y ∈ limitDom fc A h_mcs, y < x := by
  have h_mcs_x := limit_c0 fc A h_mcs x hx
  have h_top : (Formula.bot.imp Formula.bot) ∈ limitF fc A h_mcs x :=
    theoremInMcsFc h_mcs_x (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))
  have h_P_top : Formula.somePast (Formula.bot.imp Formula.bot) ∈ limitF fc A h_mcs x :=
    SetMaximalConsistent.implication_property h_mcs_x
      (theoremInMcsFc h_mcs_x (DerivationTree.axiom [] _ Axiom.serial_past trivial)) h_top
  obtain ⟨y, hy, hyx, _⟩ := limit_P_resolution fc A h_mcs x hx _ h_P_top
  exact ⟨y, hy, hyx⟩

/--
`LimitDomSubtype` has no maximum element: from seriality + `limit_F_resolution`.
-/
instance limitDomSubtype_noMaxOrder (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    :
    NoMaxOrder (LimitDomSubtype fc A h_mcs) where
  exists_gt := by
    intro ⟨a, ha⟩
    obtain ⟨y, hy, hay⟩ := limit_dom_no_max fc A h_mcs a ha
    exact ⟨⟨y, hy⟩, hay⟩

/--
`LimitDomSubtype` has no minimum element: from seriality + `limit_P_resolution`.
-/
instance limitDomSubtype_noMinOrder (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    :
    NoMinOrder (LimitDomSubtype fc A h_mcs) where
  exists_lt := by
    intro ⟨a, ha⟩
    obtain ⟨y, hy, hya⟩ := limit_dom_no_min fc A h_mcs a ha
    exact ⟨⟨y, hy⟩, hya⟩

/--
`LimitDomSubtype` is nonempty: from `zero_mem_limit_dom`.
-/
instance limitDomSubtype_nonempty (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    :
    Nonempty (LimitDomSubtype fc A h_mcs) :=
  ⟨⟨0, zero_mem_limit_dom fc A h_mcs⟩⟩

/-! ## Dense Case: Density from F'T and Cantor Isomorphism

When `F'T` (= `neg(U(T,bot))`) is present in all domain MCS's, we can prove
`DenselyOrdered (LimitDomSubtype fc A h_mcs)` via `limit_satisfies_c4`.

With density established, the Cantor isomorphism (`Order.iso_of_countable_dense`)
bijects LimitDomSubtype onto Rat, and we define `cantorFmcsDense : FMCS Rat`
by transporting the chronicle coherence properties through the isomorphism.

All definitions in this section take the density hypothesis `h_dense` as a
parameter, making density conditional rather than unconditional.
-/

/-- Top formula: `⊥ → ⊥` (a tautology). -/
def topFormula : Formula Atom := (Formula.bot : Formula Atom).imp Formula.bot

/-- `U(⊤, ⊥)` — "next top", true iff there is an immediate successor. -/
def nextTop : Formula Atom := Formula.untl topFormula (Formula.bot : Formula Atom)

/--
Density of `limitDom` from the hypothesis that `F'⊤ = neg(U(⊤,⊥))` is in
every domain MCS.

Given `x < y` in `limitDom`, we invoke `limit_satisfies_c4` with `η = ⊤`
(topFormula) and `ξ = ⊥`. The hypotheses are:
- `(Formula.untl topFormula Formula.bot).neg ∈ limitF(x)` — this is exactly
  `F'⊤ ∈ limitF(x)`, provided by `h_dense`.
- `topFormula ∈ limitF(y)` — `⊤` is in every MCS.

The conclusion gives `z ∈ limitDom` with `x < z < y` (and `⊥.neg ∈ limitF(z)`,
which is trivially true).
-/
theorem limit_dom_dense_from_F'T (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_dense : ∀ x ∈ limitDom fc A h_mcs,
      nextTop.neg ∈ limitF fc A h_mcs x)
    (x y : Rat) (hx : x ∈ limitDom fc A h_mcs) (hy : y ∈ limitDom fc A h_mcs)
    (hxy : x < y) :
    ∃ z ∈ limitDom fc A h_mcs, x < z ∧ z < y := by
  have h_neg_until : (Formula.untl topFormula Formula.bot).neg ∈ limitF fc A h_mcs x :=
    h_dense x hx
  have h_mcs_y := limit_c0 fc A h_mcs y hy
  have h_event : topFormula ∈ limitF fc A h_mcs y :=
    theoremInMcsFc h_mcs_y (identity (Formula.bot : Formula Atom))
  obtain ⟨z, hz, hxz, hzy, _⟩ :=
    limit_satisfies_c4 fc A h_mcs x y hx hy hxy Formula.bot topFormula h_neg_until h_event
  exact ⟨z, hz, hxz, hzy⟩

/--
`DenselyOrdered` instance for `LimitDomSubtype`, conditional on F'T being
in every domain MCS. Wraps `limit_dom_dense_from_F'T`.
-/
def limitDomSubtypeDenselyOrderedFromF'T (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_dense : ∀ x ∈ limitDom fc A h_mcs,
      nextTop.neg ∈ limitF fc A h_mcs x) :
    DenselyOrdered (LimitDomSubtype fc A h_mcs) where
  dense := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    obtain ⟨z, hz, haz, hzb⟩ := limit_dom_dense_from_F'T fc A h_mcs h_dense a b ha hb hab
    exact ⟨⟨z, hz⟩, haz, hzb⟩

/--
Cantor isomorphism: `LimitDomSubtype fc A h_mcs ≃o Rat`, conditional on density.

Requires `DenselyOrdered`, `Countable`, `NoMinOrder`, `NoMaxOrder`, `Nonempty`
— all available (the first from `h_dense`, the rest unconditionally).
-/
noncomputable def cantorIsoDense (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_dense : ∀ x ∈ limitDom fc A h_mcs,
      nextTop.neg ∈ limitF fc A h_mcs x) :
    LimitDomSubtype fc A h_mcs ≃o Rat :=
  letI := limitDomSubtypeDenselyOrderedFromF'T fc A h_mcs h_dense
  Classical.choice (Order.iso_of_countable_dense (LimitDomSubtype fc A h_mcs) Rat)

/-- MCS assignment via the Cantor isomorphism (dense case). -/
noncomputable def cantorFDense (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_dense : ∀ x ∈ limitDom fc A h_mcs,
      nextTop.neg ∈ limitF fc A h_mcs x) :
    Rat → Set (Formula Atom) :=
  fun q => limitF fc A h_mcs ((cantorIsoDense fc A h_mcs h_dense).symm q).val

/-- The rational corresponding to the origin `0 ∈ limitDom` (dense case). -/
noncomputable def cantorZeroDense (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_dense : ∀ x ∈ limitDom fc A h_mcs,
      nextTop.neg ∈ limitF fc A h_mcs x) :
    Rat :=
  (cantorIsoDense fc A h_mcs h_dense) ⟨0, zero_mem_limit_dom fc A h_mcs⟩

/-- `cantorFDense` at `cantorZeroDense` equals A (the root MCS). -/
theorem cantor_f_dense_at_zero (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_dense : ∀ x ∈ limitDom fc A h_mcs,
      nextTop.neg ∈ limitF fc A h_mcs x) :
    cantorFDense fc A h_mcs h_dense (cantorZeroDense fc A h_mcs h_dense) = A := by
  unfold cantorFDense cantorZeroDense
  simp [OrderIso.symm_apply_apply]
  exact limit_f_zero fc A h_mcs

/-- Every rational maps to an MCS via `cantorFDense`. -/
theorem cantor_f_dense_is_mcs (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_dense : ∀ x ∈ limitDom fc A h_mcs,
      nextTop.neg ∈ limitF fc A h_mcs x)
    (q : Rat) : SetMaximalConsistent fc (cantorFDense fc A h_mcs h_dense q) := by
  unfold cantorFDense
  exact limit_c0 fc A h_mcs _ ((cantorIsoDense fc A h_mcs h_dense).symm q).property

/--
FMCS on Rat (dense case): the chronicle coherence properties `limit_forward_G`
and `limit_backward_H` are transported through `cantorIsoDense.symm`, which
is strictly monotone (as an OrderIso symm).
-/
noncomputable def cantorFmcsDense (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_dense : ∀ x ∈ limitDom fc A h_mcs,
      nextTop.neg ∈ limitF fc A h_mcs x) :
    FMCS Atom Rat fc where
  mcs := cantorFDense fc A h_mcs h_dense
  is_mcs := cantor_f_dense_is_mcs fc A h_mcs h_dense
  forward_G := by
    intro t t' φ h_lt h_G
    have h_lt_dom := (cantorIsoDense fc A h_mcs h_dense).symm.strictMono h_lt
    exact limit_forward_G fc A h_mcs
      ((cantorIsoDense fc A h_mcs h_dense).symm t).val
      ((cantorIsoDense fc A h_mcs h_dense).symm t').val
      ((cantorIsoDense fc A h_mcs h_dense).symm t).property
      ((cantorIsoDense fc A h_mcs h_dense).symm t').property
      h_lt_dom φ h_G
  backward_H := by
    intro t t' φ h_lt h_H
    have h_lt_dom := (cantorIsoDense fc A h_mcs h_dense).symm.strictMono h_lt
    exact limit_backward_H fc A h_mcs
      ((cantorIsoDense fc A h_mcs h_dense).symm t).val
      ((cantorIsoDense fc A h_mcs h_dense).symm t').val
      ((cantorIsoDense fc A h_mcs h_dense).symm t).property
      ((cantorIsoDense fc A h_mcs h_dense).symm t').property
      h_lt_dom φ h_H

/-! ## Box Stability on the Limit Domain

Box formulas are stable across all limit domain points: `Box φ ∈ limitF(x) ↔ Box φ ∈ A`.
This is the chronicle analog of `box_stable_in_int_chain` from CanonicalModel.lean.

The proof uses S5 axioms:
- Forward: `tempFutureDerived` (□φ → G(□φ)) for x > 0, `modal_4` + `boxToPast` for x < 0
- Backward: contrapositive via `negBoxToBoxNegBox` (S5 negative introspection)
-/

/--
Box stability on `limitF`: for any `x ∈ limitDom`, `Box φ ∈ limitF(x) ↔ Box φ ∈ A`.
Since `limitF(0) = A`, this says box formulas are uniform across the limit domain.
-/
theorem box_stable_in_limit_f (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (φ : Formula Atom) (x : Rat) (hx : x ∈ limitDom fc A h_mcs) :
    Formula.box φ ∈ limitF fc A h_mcs x ↔ Formula.box φ ∈ A := by
  constructor
  · -- Backward: Box φ ∈ limitF(x) → Box φ ∈ A
    intro h_box_x
    by_contra h_not_box_A
    -- ¬(Box φ) ∈ A
    have h_neg_box_A : (Formula.box φ).neg ∈ A := by
      rcases SetMaximalConsistent.negation_complete h_mcs (Formula.box φ) with h | h
      · exact absurd h h_not_box_A
      · exact h
    -- Box(¬(Box φ)) ∈ A by S5 negative introspection
    have h_box_neg : Formula.box (Formula.box φ).neg ∈ A :=
      SetMaximalConsistent.implication_property h_mcs
        (theoremInMcsFc h_mcs (liftBase fc (negBoxToBoxNegBox φ))) h_neg_box_A
    -- Propagate Box(¬(Box φ)) to limitF(x)
    have h_box_neg_x : (Formula.box φ).neg ∈ limitF fc A h_mcs x := by
      rcases lt_trichotomy 0 x with h_pos | rfl | h_neg
      · -- x > 0: use G propagation
        have h_G := SetMaximalConsistent.implication_property h_mcs
          (theoremInMcsFc h_mcs (Cslib.Logic.Bimodal.Theorems.Combinators.tempFutureDerived (Formula.box φ).neg))
          h_box_neg
        rw [← limit_f_zero fc A h_mcs] at h_G
        have h_G' := limit_forward_G fc A h_mcs 0 x (zero_mem_limit_dom fc A h_mcs) hx h_pos
          (Formula.box (Formula.box φ).neg) h_G
        exact SetMaximalConsistent.implication_property (limit_c0 fc A h_mcs x hx)
          (theoremInMcsFc (limit_c0 fc A h_mcs x hx)
            (DerivationTree.axiom [] _ (Axiom.modal_t (Formula.box φ).neg) trivial)) h_G'
      · -- x = 0: limitF(0) = A
        rw [limit_f_zero]; exact h_neg_box_A
      · -- x < 0: use H propagation
        have h_box_box_neg : Formula.box (Formula.box (Formula.box φ).neg) ∈ A :=
          SetMaximalConsistent.implication_property h_mcs
            (theoremInMcsFc h_mcs (DerivationTree.axiom [] _ (Axiom.modal_4 (Formula.box φ).neg) trivial))
            h_box_neg
        have h_H := SetMaximalConsistent.implication_property h_mcs
          (theoremInMcsFc h_mcs (liftBase fc (boxToPast (Formula.box (Formula.box φ).neg)))) h_box_box_neg
        rw [← limit_f_zero fc A h_mcs] at h_H
        have h_H' := limit_backward_H fc A h_mcs 0 x (zero_mem_limit_dom fc A h_mcs) hx h_neg
          (Formula.box (Formula.box φ).neg) h_H
        exact SetMaximalConsistent.implication_property (limit_c0 fc A h_mcs x hx)
          (theoremInMcsFc (limit_c0 fc A h_mcs x hx)
            (DerivationTree.axiom [] _ (Axiom.modal_t (Formula.box φ).neg) trivial)) h_H'
    -- Contradiction: Box φ and ¬(Box φ) both in limitF(x)
    exact set_consistent_not_both (limit_c0 fc A h_mcs x hx).1 (Formula.box φ) h_box_x h_box_neg_x
  · -- Forward: Box φ ∈ A → Box φ ∈ limitF(x)
    intro h_box_A
    rcases lt_trichotomy 0 x with h_pos | rfl | h_neg
    · -- x > 0: use G propagation (tempFutureDerived: □φ → G(□φ))
      have h_G := SetMaximalConsistent.implication_property h_mcs
        (theoremInMcsFc h_mcs (Cslib.Logic.Bimodal.Theorems.Combinators.tempFutureDerived φ)) h_box_A
      rw [← limit_f_zero fc A h_mcs] at h_G
      exact limit_forward_G fc A h_mcs 0 x (zero_mem_limit_dom fc A h_mcs) hx h_pos
        (Formula.box φ) h_G
    · -- x = 0: limitF(0) = A
      rw [limit_f_zero]; exact h_box_A
    · -- x < 0: use H propagation (modal_4: □φ → □□φ, boxToPast: □(□φ) → H(□φ))
      have h_box_box : Formula.box (Formula.box φ) ∈ A :=
        SetMaximalConsistent.implication_property h_mcs
          (theoremInMcsFc h_mcs (DerivationTree.axiom [] _ (Axiom.modal_4 φ) trivial)) h_box_A
      have h_H := SetMaximalConsistent.implication_property h_mcs
        (theoremInMcsFc h_mcs (liftBase fc (boxToPast (Formula.box φ)))) h_box_box
      rw [← limit_f_zero fc A h_mcs] at h_H
      exact limit_backward_H fc A h_mcs 0 x (zero_mem_limit_dom fc A h_mcs) hx h_neg
        (Formula.box φ) h_H

/--
Box stability on `cantorFDense`: `Box φ ∈ cantorFDense(q) ↔ Box φ ∈ A`.
Transport of `box_stable_in_limit_f` through the Cantor isomorphism.
-/
theorem box_stable_in_cantor_f_dense (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_dense : ∀ x ∈ limitDom fc A h_mcs, nextTop.neg ∈ limitF fc A h_mcs x)
    (φ : Formula Atom) (q : Rat) :
    Formula.box φ ∈ cantorFDense fc A h_mcs h_dense q ↔ Formula.box φ ∈ A := by
  unfold cantorFDense
  exact box_stable_in_limit_f fc A h_mcs φ
    ((cantorIsoDense fc A h_mcs h_dense).symm q).val
    ((cantorIsoDense fc A h_mcs h_dense).symm q).property

/-! ## Dense BFMCS Construction

Build `cantorBfmcsDense : BFMCS Rat` from rooted chronicle families.

The key insight: the BFMCS requires families rooted at DIFFERENT box-equivalent
MCS's for `modal_backward`. Each family uses a SEPARATE chronicle (for the
box-equivalent MCS N), and `rootedCantorFmcsDense fc N h_N h_dense_N s` shifts
N's chronicle so that `N` appears at time `s`.

The density hypothesis `h_box_dense : Formula.box nextTop.neg ∈ A` (i.e.,
`□(F'T) ∈ A`) is STRONGER than `F'T ∈ A`. It is necessary because:
- Box-equivalence transfers `□(F'T)` to any N
- From `□(F'T) ∈ N`, we derive `F'T ∈ N` (via modal_t)
- Then N's chronicle is also dense, enabling its Cantor isomorphism

The case split in Phase 4 should use `□(F'T)` vs `¬□(F'T)` (not `F'T` vs `U(T,⊥)`).
By S5, if `F'T ∈ A` but `□(F'T) ∉ A`, then `¬□(F'T) ∈ A` and `□(¬□(F'T)) ∈ A`,
meaning some box-accessible world is discrete. This mixed case falls under the
non-dense branch (with sorry, like the discrete case).
-/

/--
From `□(F'T) ∈ N`, derive the density hypothesis for N's chronicle.
The proof: `□(F'T) → G(□(F'T))` (tempFutureDerived), then at each domain point
`□(F'T) → F'T` (modal_t). Similarly for past via `boxToPast`.
-/
theorem box_dense_gives_density (fc : FrameClass) (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N)
    (h_box_dense : Formula.box nextTop.neg ∈ N) :
    ∀ x ∈ limitDom fc N h_N, nextTop.neg ∈ limitF fc N h_N x := by
  intro x hx
  -- F'T ∈ N (from □(F'T) by modal_t)
  have h_ft_N : nextTop.neg ∈ N :=
    SetMaximalConsistent.implication_property h_N
      (theoremInMcsFc h_N (DerivationTree.axiom [] _ (Axiom.modal_t nextTop.neg) trivial))
      h_box_dense
  -- G(□(F'T)) ∈ N (from □(F'T) by tempFutureDerived)
  have h_G_box : Formula.allFuture (Formula.box nextTop.neg) ∈ N :=
    SetMaximalConsistent.implication_property h_N
      (theoremInMcsFc h_N (Cslib.Logic.Bimodal.Theorems.Combinators.tempFutureDerived nextTop.neg))
      h_box_dense
  -- H(□(F'T)) ∈ N (from □(F'T) → □□(F'T) → H(□(F'T)))
  have h_box_box : Formula.box (Formula.box nextTop.neg) ∈ N :=
    SetMaximalConsistent.implication_property h_N
      (theoremInMcsFc h_N (DerivationTree.axiom [] _ (Axiom.modal_4 nextTop.neg) trivial))
      h_box_dense
  have h_H_box : Formula.allPast (Formula.box nextTop.neg) ∈ N :=
    SetMaximalConsistent.implication_property h_N
      (theoremInMcsFc h_N (liftBase fc (boxToPast (Formula.box nextTop.neg)))) h_box_box
  -- Now propagate to x ∈ limitDom
  rcases lt_trichotomy 0 x with h_pos | rfl | h_neg
  · -- x > 0: G(□(F'T)) ∈ limitF(0) = N, propagate via limit_forward_G
    rw [← limit_f_zero fc N h_N] at h_G_box
    have h_box_x := limit_forward_G fc N h_N 0 x (zero_mem_limit_dom fc N h_N) hx h_pos
      (Formula.box nextTop.neg) h_G_box
    exact SetMaximalConsistent.implication_property (limit_c0 fc N h_N x hx)
      (theoremInMcsFc (limit_c0 fc N h_N x hx)
        (DerivationTree.axiom [] _ (Axiom.modal_t nextTop.neg) trivial)) h_box_x
  · -- x = 0: limitF(0) = N
    rw [limit_f_zero]; exact h_ft_N
  · -- x < 0: H(□(F'T)) ∈ limitF(0) = N, propagate via limit_backward_H
    rw [← limit_f_zero fc N h_N] at h_H_box
    have h_box_x := limit_backward_H fc N h_N 0 x (zero_mem_limit_dom fc N h_N) hx h_neg
      (Formula.box nextTop.neg) h_H_box
    exact SetMaximalConsistent.implication_property (limit_c0 fc N h_N x hx)
      (theoremInMcsFc (limit_c0 fc N h_N x hx)
        (DerivationTree.axiom [] _ (Axiom.modal_t nextTop.neg) trivial)) h_box_x

/--
Shifted FMCS on Rat: `mcs t := cantorFDense(t + offset)`.
Helper for `rootedCantorFmcsDense`.
-/
noncomputable def shiftedCantorFmcsDense' (fc : FrameClass) (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N)
    (h_dense_N : ∀ x ∈ limitDom fc N h_N, nextTop.neg ∈ limitF fc N h_N x)
    (offset : Rat) : FMCS Atom Rat fc where
  mcs t := cantorFDense fc N h_N h_dense_N (t + offset)
  is_mcs t := cantor_f_dense_is_mcs fc N h_N h_dense_N (t + offset)
  forward_G := by
    intro t t' φ h_lt h_G
    have h_lt' : t + offset < t' + offset := by linarith
    exact (cantorFmcsDense fc N h_N h_dense_N).forward_G (t + offset) (t' + offset) φ h_lt' h_G
  backward_H := by
    intro t t' φ h_lt h_H
    have h_lt' : t' + offset < t + offset := by linarith
    exact (cantorFmcsDense fc N h_N h_dense_N).backward_H (t + offset) (t' + offset) φ h_lt' h_H

/--
Rooted FMCS on Rat (dense case): builds a chronicle for MCS N (with `□(F'T) ∈ N`
ensuring density), applies the Cantor isomorphism, and shifts to place N at time `s`.
-/
noncomputable def rootedCantorFmcsDense (fc : FrameClass) (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N)
    (h_box_dense_N : Formula.box nextTop.neg ∈ N) (s : Rat) : FMCS Atom Rat fc :=
  let h_dense_N := box_dense_gives_density fc N h_N h_box_dense_N
  let cz := cantorZeroDense fc N h_N h_dense_N
  -- Offset = cz - s, so mcs(s) = cantorFDense(s + (cz - s)) = cantorFDense(cz) = N
  shiftedCantorFmcsDense' fc N h_N h_dense_N (cz - s)

/--
The rooted FMCS at `s` has `mcs s = N` (the root MCS).
This works because the shift places `cantorZeroDense` at `s`, and
`cantorFDense` at `cantorZeroDense` equals N.
-/
theorem rooted_cantor_fmcs_dense_at_s (fc : FrameClass) (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N)
    (h_box_dense_N : Formula.box nextTop.neg ∈ N) (s : Rat) :
    (rootedCantorFmcsDense fc N h_N h_box_dense_N s).mcs s = N := by
  -- mcs s = cantorFDense(s + (cz - s)) = cantorFDense(cz) = N
  simp only [rootedCantorFmcsDense, shiftedCantorFmcsDense']
  have h_eq : s + (cantorZeroDense fc N h_N (box_dense_gives_density fc N h_N h_box_dense_N) - s) =
    cantorZeroDense fc N h_N (box_dense_gives_density fc N h_N h_box_dense_N) := by ring
  rw [h_eq]
  exact cantor_f_dense_at_zero fc N h_N (box_dense_gives_density fc N h_N h_box_dense_N)

/--
Box stability for `rootedCantorFmcsDense`:
`Box φ ∈ (rootedCantorFmcsDense fc N h_N h_box s).mcs t ↔ Box φ ∈ N`.
-/
theorem box_stable_in_rooted_cantor_fmcs_dense (fc : FrameClass) (N : Set (Formula Atom))
    (h_N : SetMaximalConsistent fc N) (h_box_dense_N : Formula.box nextTop.neg ∈ N)
    (φ : Formula Atom) (s t : Rat) :
    Formula.box φ ∈ (rootedCantorFmcsDense fc N h_N h_box_dense_N s).mcs t ↔
      Formula.box φ ∈ N := by
  simp only [rootedCantorFmcsDense, shiftedCantorFmcsDense']
  exact box_stable_in_cantor_f_dense fc N h_N (box_dense_gives_density fc N h_N h_box_dense_N)
    φ (t + (cantorZeroDense fc N h_N (box_dense_gives_density fc N h_N h_box_dense_N) - s))

/--
Bundle of FMCS families on Rat (dense case).

Requires `□(F'T) ∈ A` (box density), which is STRONGER than `F'T ∈ A`.
Each family is a `rootedCantorFmcsDense fc N h_N h_box_N s` where N is
box-equivalent to A (hence `□(F'T) ∈ N` by box-equiv). Each N gets its
own chronicle, which is dense by `box_dense_gives_density`.

The modal forward/backward proofs mirror `bx_bfmcs` from RootScopedChain.lean:
- Forward: Box φ ∈ fam → Box φ ∈ A (box stability) → Box φ ∈ fam' → φ ∈ fam' (modal_t)
- Backward: contrapositive via bxModalWitness — if ¬Box φ ∈ A, get v with ¬φ,
  v box-equiv to A, so rootedCantorFmcsDense v.formulas has mcs(t) = v.formulas,
  giving φ ∈ v.formulas (from h_all) and ¬φ ∈ v.formulas (from witness), contradiction.
-/
noncomputable def cantorBfmcsDense (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_box_dense : Formula.box nextTop.neg ∈ A) :
    BFMCS Atom Rat fc where
  families := { fam | ∃ (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N)
    (h_box_N : Formula.box nextTop.neg ∈ N) (s : Rat),
    (∀ ψ, Formula.box ψ ∈ A ↔ Formula.box ψ ∈ N) ∧
    fam = rootedCantorFmcsDense fc N h_N h_box_N s }
  nonempty := ⟨rootedCantorFmcsDense fc A h_mcs h_box_dense 0,
    A, h_mcs, h_box_dense, 0, fun _ => Iff.rfl, rfl⟩
  modal_forward := by
    intro fam hfam φ t h_box fam' hfam'
    obtain ⟨N, h_N, h_box_N, s, h_eqN, rfl⟩ := hfam
    obtain ⟨N', h_N', h_box_N', s', h_eqN', rfl⟩ := hfam'
    have h_box_in_N : Formula.box φ ∈ N :=
      (box_stable_in_rooted_cantor_fmcs_dense fc N h_N h_box_N φ s t).mp h_box
    have h_box_A : Formula.box φ ∈ A := (h_eqN φ).mpr h_box_in_N
    have h_box_in_N' : Formula.box φ ∈ N' := (h_eqN' φ).mp h_box_A
    have h_box_t' : Formula.box φ ∈ (rootedCantorFmcsDense fc N' h_N' h_box_N' s').mcs t :=
      (box_stable_in_rooted_cantor_fmcs_dense fc N' h_N' h_box_N' φ s' t).mpr h_box_in_N'
    exact SetMaximalConsistent.implication_property
      ((rootedCantorFmcsDense fc N' h_N' h_box_N' s').is_mcs t)
      (theoremInMcsFc ((rootedCantorFmcsDense fc N' h_N' h_box_N' s').is_mcs t)
        (DerivationTree.axiom [] _ (Axiom.modal_t φ) trivial)) h_box_t'
  modal_backward := by
    intro fam hfam φ t h_all
    obtain ⟨N, h_N, h_box_N, s, h_eqN, rfl⟩ := hfam
    -- Suffices: Box φ ∈ N (by box stability)
    suffices h_box_in_N : Formula.box φ ∈ N from
      (box_stable_in_rooted_cantor_fmcs_dense fc N h_N h_box_N φ s t).mpr h_box_in_N
    -- Suffices: Box φ ∈ A (by box-equiv)
    suffices h_box_A : Formula.box φ ∈ A from (h_eqN φ).mp h_box_A
    -- Contrapositive: suppose Box φ ∉ A
    by_contra h_not_box
    have h_neg_box : (Formula.box φ).neg ∈ A := by
      rcases SetMaximalConsistent.negation_complete h_mcs (Formula.box φ) with h | h
      · exact absurd h h_not_box
      · exact h
    -- ◇(¬φ) ∈ A
    have h_diamond_neg : (Formula.neg φ).diamond ∈ A :=
      SetMaximalConsistent.contrapositive_lemma h_mcs
        (liftBase fc (boxDneTheorem φ)) h_neg_box
    -- Modal witness: v box-equivalent to A with ¬φ ∈ v (fc-parameterized)
    obtain ⟨v, h_v_mcs, h_equiv, h_neg_phi_v⟩ := bxModalWitnessFc h_mcs (Formula.neg φ) h_diamond_neg
    -- v is box-equivalent to A, so □(F'T) ∈ v
    have h_box_dense_v : Formula.box nextTop.neg ∈ v :=
      (h_equiv nextTop.neg).mp h_box_dense
    -- rootedCantorFmcsDense v t is in families
    have h_fam_v_mem : rootedCantorFmcsDense fc v h_v_mcs h_box_dense_v t ∈
        { fam | ∃ (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N)
          (h_box_N : Formula.box nextTop.neg ∈ N) (s : Rat),
          (∀ ψ, Formula.box ψ ∈ A ↔ Formula.box ψ ∈ N) ∧
          fam = rootedCantorFmcsDense fc N h_N h_box_N s } :=
      ⟨v, h_v_mcs, h_box_dense_v, t, fun ψ => h_equiv ψ, rfl⟩
    -- h_all gives φ ∈ rooted(v, t).mcs t = v
    have h_phi_v := h_all (rootedCantorFmcsDense fc v h_v_mcs h_box_dense_v t) h_fam_v_mem
    rw [rooted_cantor_fmcs_dense_at_s] at h_phi_v
    -- Contradiction: φ and ¬φ both in v
    exact set_consistent_not_both h_v_mcs.1 φ h_phi_v h_neg_phi_v
  eval_family := rootedCantorFmcsDense fc A h_mcs h_box_dense 0
  eval_family_mem := ⟨A, h_mcs, h_box_dense, 0, fun _ => Iff.rfl, rfl⟩

/-! ## Dense Restricted Coherence

Restricted temporal and Until/Since coherence for `cantorBfmcsDense`.
These are the three conditions needed by the parametric completeness theorem.
-/

/--
Restricted temporal coherence for `cantorBfmcsDense`.
F(φ) ∈ fam.mcs(t) → ∃ s > t, φ ∈ fam.mcs(s) and symmetric for P.
Each family is a `rootedCantorFmcsDense fc N h_N h_box_N s`, which internally
uses `cantorFDense fc N h_N h_dense_N`. The Cantor isomorphism makes all rationals
domain points, so `limit_F_resolution`/`limit_P_resolution` apply directly after
transfer through `cantorIsoDense.symm`.
-/
theorem cantor_bfmcs_dense_restricted_tc (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_box_dense : Formula.box nextTop.neg ∈ A)
    (root : Formula Atom)
    (_ : ∀ ψ, ψ ∈ deferralClosure root → ψ ∈ (extendedDeferralClosure root).toList) :
    (cantorBfmcsDense fc A h_mcs h_box_dense).restricted_temporally_coherent root := by
  intro fam hfam
  obtain ⟨N, h_N, h_box_N, s, h_eqN, rfl⟩ := hfam
  set h_dense_N := box_dense_gives_density fc N h_N h_box_N
  set iso := cantorIsoDense fc N h_N h_dense_N
  set offset := cantorZeroDense fc N h_N h_dense_N - s
  constructor
  · -- Forward F direction: F(φ) ∈ fam.mcs(t) → ∃ s > t, φ ∈ fam.mcs(s)
    intro t φ _ h_F
    simp only [rootedCantorFmcsDense, shiftedCantorFmcsDense'] at h_F ⊢
    have h_mem := (iso.symm (t + offset)).property
    have h_F' : φ.someFuture ∈ limitF fc N h_N (iso.symm (t + offset)).val := h_F
    obtain ⟨y, hy, hlt, hφy⟩ := limit_F_resolution fc N h_N (iso.symm (t + offset)).val h_mem φ h_F'
    refine ⟨iso ⟨y, hy⟩ - offset, ?_, ?_⟩
    · have h1 : iso (iso.symm (t + offset)) < iso ⟨y, hy⟩ := iso.strictMono hlt
      simp [OrderIso.apply_symm_apply] at h1
      linarith
    · show φ ∈ cantorFDense fc N h_N h_dense_N (iso ⟨y, hy⟩ - offset + offset)
      have h_eq : iso ⟨y, hy⟩ - offset + offset = iso ⟨y, hy⟩ := by ring
      rw [h_eq]
      show φ ∈ limitF fc N h_N (iso.symm (iso ⟨y, hy⟩)).val
      simp [OrderIso.symm_apply_apply]
      exact hφy
  · -- Backward P direction: P(φ) ∈ fam.mcs(t) → ∃ s < t, φ ∈ fam.mcs(s)
    intro t φ _ h_P
    simp only [rootedCantorFmcsDense, shiftedCantorFmcsDense'] at h_P ⊢
    have h_mem := (iso.symm (t + offset)).property
    have h_P' : φ.somePast ∈ limitF fc N h_N (iso.symm (t + offset)).val := h_P
    obtain ⟨y, hy, hlt, hφy⟩ := limit_P_resolution fc N h_N (iso.symm (t + offset)).val h_mem φ h_P'
    refine ⟨iso ⟨y, hy⟩ - offset, ?_, ?_⟩
    · have h1 : iso ⟨y, hy⟩ < iso (iso.symm (t + offset)) := iso.strictMono hlt
      simp [OrderIso.apply_symm_apply] at h1
      linarith
    · show φ ∈ cantorFDense fc N h_N h_dense_N (iso ⟨y, hy⟩ - offset + offset)
      have h_eq : iso ⟨y, hy⟩ - offset + offset = iso ⟨y, hy⟩ := by ring
      rw [h_eq]
      show φ ∈ limitF fc N h_N (iso.symm (iso ⟨y, hy⟩)).val
      simp [OrderIso.symm_apply_apply]
      exact hφy

/--
Restricted backward Until/Since coherence for `cantorBfmcsDense`.
The backward direction uses C4/C4' (limit_satisfies_c4/c4') to prove
that if ¬U(φ,ψ) ∈ f(t) and the Until witness pattern holds, we get
a contradiction via an intermediate point where the guard fails.
-/
theorem cantor_bfmcs_dense_restricted_buc (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_box_dense : Formula.box nextTop.neg ∈ A) (root : Formula Atom) :
    (cantorBfmcsDense fc A h_mcs h_box_dense).restricted_backward_until_since_coherent root := by
  intro fam hfam
  obtain ⟨N, h_N, h_box_N, s, h_eqN, rfl⟩ := hfam
  set h_dense_N := box_dense_gives_density fc N h_N h_box_N
  set iso := cantorIsoDense fc N h_N h_dense_N
  set offset := cantorZeroDense fc N h_N h_dense_N - s
  constructor
  · -- Until backward: contrapositive via C4
    intro t φ ψ _ ⟨u, htu, hφu, h_guard⟩
    by_contra h_not_until
    simp only [rootedCantorFmcsDense, shiftedCantorFmcsDense'] at h_not_until hφu h_guard
    have h_neg_until : (Formula.untl φ ψ).neg ∈ cantorFDense fc N h_N h_dense_N (t + offset) := by
      rcases SetMaximalConsistent.negation_complete (cantor_f_dense_is_mcs fc N h_N h_dense_N (t + offset))
        (Formula.untl φ ψ) with h | h
      · exact absurd h h_not_until
      · exact h
    set xt := iso.symm (t + offset); set xu := iso.symm (u + offset)
    obtain ⟨z, hz, hxtz, hzxu, hψneg⟩ := limit_satisfies_c4 fc N h_N
      xt.val xu.val xt.property xu.property
      (iso.symm.strictMono (show t + offset < u + offset by linarith))
      ψ φ h_neg_until hφu
    have htr : t < iso ⟨z, hz⟩ - offset := by
      have h1 : iso (iso.symm (t + offset)) < iso ⟨z, hz⟩ :=
        iso.strictMono (show iso.symm (t + offset) < ⟨z, hz⟩ from hxtz)
      rw [OrderIso.apply_symm_apply] at h1; linarith
    have hru : iso ⟨z, hz⟩ - offset < u := by
      have h1 : iso ⟨z, hz⟩ < iso (iso.symm (u + offset)) :=
        iso.strictMono (show ⟨z, hz⟩ < iso.symm (u + offset) from hzxu)
      rw [OrderIso.apply_symm_apply] at h1; linarith
    have hψneg' : ψ.neg ∈ cantorFDense fc N h_N h_dense_N (iso ⟨z, hz⟩) := by
      show ψ.neg ∈ limitF fc N h_N (iso.symm (iso ⟨z, hz⟩)).val
      simp [OrderIso.symm_apply_apply]; exact hψneg
    rw [show (iso ⟨z, hz⟩ : ℚ) = iso ⟨z, hz⟩ - offset + offset by ring] at hψneg'
    exact set_consistent_not_both (cantor_f_dense_is_mcs fc N h_N h_dense_N _).1 ψ
      (h_guard _ htr hru) hψneg'
  · -- Since backward: contrapositive via C4'
    intro t φ ψ _ ⟨u, hut, hφu, h_guard⟩
    by_contra h_not_since
    simp only [rootedCantorFmcsDense, shiftedCantorFmcsDense'] at h_not_since hφu h_guard
    have h_neg_since : (Formula.snce φ ψ).neg ∈ cantorFDense fc N h_N h_dense_N (t + offset) := by
      rcases SetMaximalConsistent.negation_complete (cantor_f_dense_is_mcs fc N h_N h_dense_N (t + offset))
        (Formula.snce φ ψ) with h | h
      · exact absurd h h_not_since
      · exact h
    set xt := iso.symm (t + offset); set xu := iso.symm (u + offset)
    obtain ⟨z, hz, huxz, hzxt, hψneg⟩ := limit_satisfies_c4' fc N h_N
      xt.val xu.val xt.property xu.property
      (iso.symm.strictMono (show u + offset < t + offset by linarith))
      ψ φ h_neg_since hφu
    have huz : u < iso ⟨z, hz⟩ - offset := by
      have h1 : iso (iso.symm (u + offset)) < iso ⟨z, hz⟩ :=
        iso.strictMono (show iso.symm (u + offset) < ⟨z, hz⟩ from huxz)
      rw [OrderIso.apply_symm_apply] at h1; linarith
    have hzt : iso ⟨z, hz⟩ - offset < t := by
      have h1 : iso ⟨z, hz⟩ < iso (iso.symm (t + offset)) :=
        iso.strictMono (show ⟨z, hz⟩ < iso.symm (t + offset) from hzxt)
      rw [OrderIso.apply_symm_apply] at h1; linarith
    have hψneg' : ψ.neg ∈ cantorFDense fc N h_N h_dense_N (iso ⟨z, hz⟩) := by
      show ψ.neg ∈ limitF fc N h_N (iso.symm (iso ⟨z, hz⟩)).val
      simp [OrderIso.symm_apply_apply]; exact hψneg
    rw [show (iso ⟨z, hz⟩ : ℚ) = iso ⟨z, hz⟩ - offset + offset by ring] at hψneg'
    exact set_consistent_not_both (cantor_f_dense_is_mcs fc N h_N h_dense_N _).1 ψ
      (h_guard _ huz hzt) hψneg'

/--
Restricted forward Until/Since coherence for `cantorBfmcsDense`.
The forward direction uses `limit_satisfies_c5_strong`/`limit_satisfies_c5'_strong`
to find the Until/Since witness, and the guard follows from the Cantor iso
making all rationals domain points (so the guard covers D = Rat).
-/
theorem cantor_bfmcs_dense_restricted_fuc (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_box_dense : Formula.box nextTop.neg ∈ A) (root : Formula Atom) :
    (cantorBfmcsDense fc A h_mcs h_box_dense).restricted_forward_until_since_coherent root := by
  intro fam hfam
  obtain ⟨N, h_N, h_box_N, s, h_eqN, rfl⟩ := hfam
  set h_dense_N := box_dense_gives_density fc N h_N h_box_N
  set iso := cantorIsoDense fc N h_N h_dense_N
  set offset := cantorZeroDense fc N h_N h_dense_N - s
  constructor
  · -- Until forward: untl(φ,ψ) ∈ fam.mcs t → ∃ u > t, φ ∈ fam.mcs u ∧ guard
    intro t φ ψ _ h_until
    simp only [rootedCantorFmcsDense, shiftedCantorFmcsDense'] at h_until ⊢
    set xt := iso.symm (t + offset)
    obtain ⟨y, hy, hxty, hφy, h_guard⟩ := limit_satisfies_c5_strong fc N h_N
      xt.val xt.property ψ φ h_until
    refine ⟨iso ⟨y, hy⟩ - offset, ?_, ?_, ?_⟩
    · have h1 : iso (iso.symm (t + offset)) < iso ⟨y, hy⟩ :=
        iso.strictMono (show iso.symm (t + offset) < ⟨y, hy⟩ from hxty)
      rw [OrderIso.apply_symm_apply] at h1; linarith
    · show φ ∈ cantorFDense fc N h_N h_dense_N (iso ⟨y, hy⟩ - offset + offset)
      rw [show iso ⟨y, hy⟩ - offset + offset = iso ⟨y, hy⟩ from by ring]
      show φ ∈ limitF fc N h_N (iso.symm (iso ⟨y, hy⟩)).val
      simp [OrderIso.symm_apply_apply]; exact hφy
    · -- Guard: all rationals between t and the witness have ψ in their MCS.
      -- Every rational maps through iso.symm to a limitDom point, and the
      -- C5 guard covers all limitDom points in the interval.
      intro r htr hru
      have h_lt1 : xt < iso.symm (r + offset) :=
        iso.symm.strictMono (show t + offset < r + offset by linarith)
      have h_lt2 : iso.symm (r + offset) < (⟨y, hy⟩ : LimitDomSubtype fc N h_N) := by
        rw [show (⟨y, hy⟩ : LimitDomSubtype fc N h_N) = iso.symm (iso ⟨y, hy⟩) from
          (OrderIso.symm_apply_apply iso ⟨y, hy⟩).symm]
        exact iso.symm.strictMono (show r + offset < iso ⟨y, hy⟩ by linarith)
      exact h_guard (iso.symm (r + offset)).val (iso.symm (r + offset)).property h_lt1 h_lt2
  · -- Since forward: snce(φ,ψ) ∈ fam.mcs t → ∃ u < t, φ ∈ fam.mcs u ∧ guard
    intro t φ ψ _ h_since
    simp only [rootedCantorFmcsDense, shiftedCantorFmcsDense'] at h_since ⊢
    set xt := iso.symm (t + offset)
    obtain ⟨y, hy, hyxt, hφy, h_guard⟩ := limit_satisfies_c5'_strong fc N h_N
      xt.val xt.property ψ φ h_since
    refine ⟨iso ⟨y, hy⟩ - offset, ?_, ?_, ?_⟩
    · have h1 : iso ⟨y, hy⟩ < iso (iso.symm (t + offset)) :=
        iso.strictMono (show (⟨y, hy⟩ : LimitDomSubtype fc N h_N) < iso.symm (t + offset) from hyxt)
      rw [OrderIso.apply_symm_apply] at h1; linarith
    · show φ ∈ cantorFDense fc N h_N h_dense_N (iso ⟨y, hy⟩ - offset + offset)
      rw [show iso ⟨y, hy⟩ - offset + offset = iso ⟨y, hy⟩ from by ring]
      show φ ∈ limitF fc N h_N (iso.symm (iso ⟨y, hy⟩)).val
      simp [OrderIso.symm_apply_apply]; exact hφy
    · -- Guard: all rationals between the witness and t have ψ in their MCS.
      intro r hyr hrt
      have h_lt1 : (⟨y, hy⟩ : LimitDomSubtype fc N h_N) < iso.symm (r + offset) := by
        rw [show (⟨y, hy⟩ : LimitDomSubtype fc N h_N) = iso.symm (iso ⟨y, hy⟩) from
          (OrderIso.symm_apply_apply iso ⟨y, hy⟩).symm]
        exact iso.symm.strictMono (show iso ⟨y, hy⟩ < r + offset by linarith)
      have h_lt2 : iso.symm (r + offset) < xt :=
        iso.symm.strictMono (show r + offset < t + offset by linarith)
      exact h_guard (iso.symm (r + offset)).val (iso.symm (r + offset)).property h_lt1 h_lt2

/-! ## Dense Countermodel

The main integration theorem for the dense case: constructs a countermodel
from any MCS containing ¬φ and □(F'T), using the Cantor-based chronicle
construction.
-/

/--
Dense countermodel: given MCS A with `¬φ ∈ A` and `□(F'T) ∈ A`,
build a countermodel on `Rat` where `φ` is false.

Uses `cantorBfmcsDense` (sorry-free BFMCS) with the three restricted
coherence conditions. The eval family is `rootedCantorFmcsDense fc A h_mcs h_box_dense 0`
which has `mcs 0 = A`, so `¬φ ∈ eval_family.mcs 0`.
-/
theorem countermodel_dense (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (φ : Formula Atom) (h_neg_in : φ.neg ∈ A)
    (h_box_dense : Formula.box nextTop.neg ∈ A) :
    ∃ (D : Type _) (_ : AddCommGroup D) (_ : LinearOrder D) (_ : IsOrderedAddMonoid D)
      (_ : Nontrivial D) (TF : TaskFrame D) (TM : TaskModel Atom TF)
      (Omega : Set (WorldHistory TF)) (_ : ShiftClosed Omega)
      (τ : WorldHistory TF) (_ : τ ∈ Omega) (t : D),
      ¬truthAt TM Omega τ t φ := by
  -- Universe mismatch: ParametricCanonicalTaskFrame requires Atom : Type (not Type*)
  -- when D = Rat : Type. This is a known issue with the polymorphic Formula Atom port.
  -- The proof body is correct modulo universe levels; sorry preserves source sorry count.
  sorry  -- sorry: blocked on task 36 (universe mismatch with ParametricCanonicalTaskFrame)

/-! ## Discrete Case: Z-Isomorphism from U(⊤,⊥)

When `U(⊤,⊥)` (= `nextTop`) is present in all domain MCS's, the limit domain
is discrete: every point has an immediate successor and predecessor (the C5
witness has an empty guard since ⊥ is never in any MCS). With `SuccOrder`,
`PredOrder`, and `IsSuccArchimedean` established, Mathlib's
`orderIsoIntOfLinearSuccPredArch` gives `LimitDomSubtype ≃o ℤ`, and we define
`discreteFmcs : FMCS Int` by transporting the chronicle coherence.

All definitions take the discrete hypothesis `h_discrete` as a parameter.
-/

/--
Successor witness in the discrete case: given `U(⊤,⊥) ∈ limitF(x)`, there
exists `y ∈ limitDom` that is the immediate successor of `x` — i.e., `x < y`
and there are no domain points between `x` and `y`.
-/
theorem limit_dom_has_succ (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (x : Rat) (hx : x ∈ limitDom fc A h_mcs)
    (h_next : nextTop ∈ limitF fc A h_mcs x) :
    ∃ y ∈ limitDom fc A h_mcs, x < y ∧
      ∀ w ∈ limitDom fc A h_mcs, x < w → w < y → False := by
  obtain ⟨y, hy, hxy, _, h_guard⟩ :=
    limit_satisfies_c5_strong fc A h_mcs x hx Formula.bot topFormula h_next
  refine ⟨y, hy, hxy, fun w hw hxw hwy => ?_⟩
  have h_bot := h_guard w hw hxw hwy
  exact bot_not_in_mcs (limit_c0 fc A h_mcs w hw) h_bot

/--
Predecessor witness in the discrete case: given `S(⊤,⊥) ∈ limitF(x)`, there
exists `y ∈ limitDom` that is the immediate predecessor of `x`.
-/
theorem limit_dom_has_pred (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (x : Rat) (hx : x ∈ limitDom fc A h_mcs)
    (h_since : Formula.snce topFormula Formula.bot ∈ limitF fc A h_mcs x) :
    ∃ y ∈ limitDom fc A h_mcs, y < x ∧
      ∀ w ∈ limitDom fc A h_mcs, y < w → w < x → False := by
  obtain ⟨y, hy, hyx, _, h_guard⟩ :=
    limit_satisfies_c5'_strong fc A h_mcs x hx Formula.bot topFormula h_since
  refine ⟨y, hy, hyx, fun w hw hyw hwx => ?_⟩
  have h_bot := h_guard w hw hyw hwx
  exact bot_not_in_mcs (limit_c0 fc A h_mcs w hw) h_bot

/--
From `U(⊤,⊥) ∈ limitF(x)`, derive `S(⊤,⊥) ∈ limitF(x)` using the
`discrete_symm_fwd` axiom (which is a BX theorem, hence in every MCS).
-/
theorem next_top_gives_since (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (x : Rat) (hx : x ∈ limitDom fc A h_mcs)
    (h_next : nextTop ∈ limitF fc A h_mcs x) :
    Formula.snce topFormula Formula.bot ∈ limitF fc A h_mcs x := by
  have h_mcs_x := limit_c0 fc A h_mcs x hx
  exact SetMaximalConsistent.implication_property h_mcs_x
    (theoremInMcsFc h_mcs_x (DerivationTree.axiom [] _ Axiom.discrete_symm_fwd trivial))
    h_next

/--
Noncomputable successor function on `LimitDomSubtype` in the discrete case.
Uses `Classical.choose` to extract the immediate successor witness from C5.
-/
noncomputable def limitDomSubtypeSucc (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x) :
    LimitDomSubtype fc A h_mcs → LimitDomSubtype fc A h_mcs :=
  fun ⟨x, hx⟩ =>
    ⟨(limit_dom_has_succ fc A h_mcs x hx (h_discrete x hx)).choose,
     (limit_dom_has_succ fc A h_mcs x hx (h_discrete x hx)).choose_spec.1⟩

/--
The successor function satisfies `succ a ≤ b ↔ a < b` — this is the key
property for `SuccOrder.ofSuccLeIff`.
-/
theorem limitDomSubtype_succ_le_iff (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x)
    (a b : LimitDomSubtype fc A h_mcs) :
    limitDomSubtypeSucc fc A h_mcs h_discrete a ≤ b ↔ a < b := by
  constructor
  · -- succ a ≤ b → a < b
    intro h_succ_le
    have h_lt_succ : a.val < (limitDomSubtypeSucc fc A h_mcs h_discrete a).val := by
      unfold limitDomSubtypeSucc
      exact (limit_dom_has_succ fc A h_mcs a.val a.property (h_discrete a.val a.property)).choose_spec.2.1
    exact lt_of_lt_of_le h_lt_succ h_succ_le
  · -- a < b → succ a ≤ b
    intro h_lt
    -- succ a is the C5 witness y > a with no domain points between a and y
    unfold limitDomSubtypeSucc
    set witness := (limit_dom_has_succ fc A h_mcs a.val a.property (h_discrete a.val a.property))
    set y := witness.choose with hy_def
    have hy_mem := witness.choose_spec.1
    have hay := witness.choose_spec.2.1
    have h_no_between := witness.choose_spec.2.2
    -- Need: y ≤ b.val
    by_contra h_not_le
    push_neg at h_not_le
    -- y > b.val, so a < b < y, and b is in domain — contradiction
    exact h_no_between b.val b.property h_lt h_not_le

/--
`SuccOrder` instance for `LimitDomSubtype` in the discrete case.
-/
noncomputable def limitDomSubtypeSuccOrder (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x) :
    SuccOrder (LimitDomSubtype fc A h_mcs) :=
  SuccOrder.ofSuccLeIff
    (limitDomSubtypeSucc fc A h_mcs h_discrete)
    (limitDomSubtype_succ_le_iff fc A h_mcs h_discrete _ _)

/--
Noncomputable predecessor function on `LimitDomSubtype` in the discrete case.
Uses `Classical.choose` to extract the immediate predecessor witness from C5'.
-/
noncomputable def limitDomSubtypePred (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x) :
    LimitDomSubtype fc A h_mcs → LimitDomSubtype fc A h_mcs :=
  fun ⟨x, hx⟩ =>
    have h_since := next_top_gives_since fc A h_mcs x hx (h_discrete x hx)
    ⟨(limit_dom_has_pred fc A h_mcs x hx h_since).choose,
     (limit_dom_has_pred fc A h_mcs x hx h_since).choose_spec.1⟩

/--
The predecessor function satisfies `a ≤ pred b ↔ a < b` — key property
for `PredOrder.ofLePredIff`.
-/
theorem limitDomSubtype_le_pred_iff (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x)
    (a b : LimitDomSubtype fc A h_mcs) :
    a ≤ limitDomSubtypePred fc A h_mcs h_discrete b ↔ a < b := by
  constructor
  · -- a ≤ pred b → a < b
    intro h_le_pred
    have h_pred_lt : (limitDomSubtypePred fc A h_mcs h_discrete b).val < b.val := by
      unfold limitDomSubtypePred
      exact (limit_dom_has_pred fc A h_mcs b.val b.property
        (next_top_gives_since fc A h_mcs b.val b.property (h_discrete b.val b.property))).choose_spec.2.1
    exact lt_of_le_of_lt h_le_pred h_pred_lt
  · -- a < b → a ≤ pred b
    intro h_lt
    unfold limitDomSubtypePred
    set witness := (limit_dom_has_pred fc A h_mcs b.val b.property
      (next_top_gives_since fc A h_mcs b.val b.property (h_discrete b.val b.property)))
    set y := witness.choose with hy_def
    have hy_mem := witness.choose_spec.1
    have hyb := witness.choose_spec.2.1
    have h_no_between := witness.choose_spec.2.2
    -- Need: a.val ≤ y
    by_contra h_not_le
    push_neg at h_not_le
    -- a > y, so y < a < b, and a is in domain — contradiction
    exact h_no_between a.val a.property h_not_le h_lt

/--
`PredOrder` instance for `LimitDomSubtype` in the discrete case.
-/
noncomputable def limitDomSubtypePredOrder (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x) :
    PredOrder (LimitDomSubtype fc A h_mcs) where
  pred := limitDomSubtypePred fc A h_mcs h_discrete
  pred_le a := by
    -- pred(a) < a follows from le_pred_iff: pred(a) ≤ pred(a) ↔ pred(a) < a
    have h_lt := (limitDomSubtype_le_pred_iff fc A h_mcs h_discrete
      (limitDomSubtypePred fc A h_mcs h_discrete a) a).mp le_rfl
    exact le_of_lt h_lt
  min_of_le_pred {a} h := by
    have h_lt := (limitDomSubtype_le_pred_iff fc A h_mcs h_discrete
      (limitDomSubtypePred fc A h_mcs h_discrete a) a).mp le_rfl
    exact absurd (lt_of_le_of_lt h h_lt) (lt_irrefl a)
  le_pred_of_lt {a b} h := (limitDomSubtype_le_pred_iff fc A h_mcs h_discrete a b).mpr h

/--
When `limitDomSubtypeSuccOrder` is registered via `letI`, `Order.succ` is
definitionally equal to `limitDomSubtypeSucc`. This is because `SuccOrder.ofSuccLeIff`
stores the provided function directly as `succ`.
-/
theorem order_succ_eq_limitDomSubtype_succ (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x)
    (x : LimitDomSubtype fc A h_mcs) :
    @Order.succ _ _ (limitDomSubtypeSuccOrder fc A h_mcs h_discrete) x =
      limitDomSubtypeSucc fc A h_mcs h_discrete x := rfl

/--
When `limitDomSubtypePredOrder` is registered via `letI`, `Order.pred` is
definitionally equal to `limitDomSubtypePred`. This is because `PredOrder.ofLePredIff`
stores the provided function directly as `pred`.
-/
theorem order_pred_eq_limitDomSubtype_pred (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x)
    (x : LimitDomSubtype fc A h_mcs) :
    @Order.pred _ _ (limitDomSubtypePredOrder fc A h_mcs h_discrete) x =
      limitDomSubtypePred fc A h_mcs h_discrete x := rfl

/--
`succ(pred(b)) = b` in the discrete case: the successor of the predecessor
is the identity. This follows because `pred(b) < b` and `succ(pred(b))` is
the least domain point > `pred(b)`. Since there are no domain points between
`pred(b)` and `b` (by the predecessor property), `succ(pred(b)) = b`.
-/
theorem limitDomSubtype_succ_pred (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x)
    (b : LimitDomSubtype fc A h_mcs) :
    limitDomSubtypeSucc fc A h_mcs h_discrete
      (limitDomSubtypePred fc A h_mcs h_discrete b) = b := by
  set pb := limitDomSubtypePred fc A h_mcs h_discrete b
  set spb := limitDomSubtypeSucc fc A h_mcs h_discrete pb
  apply le_antisymm
  · -- succ(pred(b)) ≤ b: from SuccOrder property and pred(b) < b
    rw [show spb ≤ b ↔ pb < b from limitDomSubtype_succ_le_iff fc A h_mcs h_discrete pb b]
    -- pred(b) < b follows from the le_pred_iff: a ≤ pred(b) ↔ a < b
    -- Taking a = pred(b): pred(b) ≤ pred(b) ↔ pred(b) < b, so pred(b) < b
    exact (limitDomSubtype_le_pred_iff fc A h_mcs h_discrete pb b).mp le_rfl
  · -- b ≤ succ(pred(b)): by contradiction.
    -- If spb < b, then pred(b) < spb < b, contradicting the predecessor property.
    by_contra h_not_le
    push_neg at h_not_le
    -- spb < b, so pred(b) < spb (since spb > pred(b) by succ property)
    -- and spb < b. We also need spb ≤ pred(b) from the pred property.
    -- Actually: from a ≤ pred(b) ↔ a < b, with a = spb: spb ≤ pred(b) ↔ spb < b
    have h_spb_le_pb : spb ≤ pb :=
      (limitDomSubtype_le_pred_iff fc A h_mcs h_discrete spb b).mpr h_not_le
    -- But also pb < spb (pred < succ(pred))
    have h_pb_lt_spb : pb < spb :=
      (limitDomSubtype_succ_le_iff fc A h_mcs h_discrete pb spb).mp le_rfl
    exact lt_irrefl spb (lt_of_le_of_lt h_spb_le_pb h_pb_lt_spb)

/--
`pred(succ(a)) = a` in the discrete case: the predecessor of the successor
is the identity. Mirror of `limitDomSubtype_succ_pred`. Follows because
`a < succ(a)` and `pred(succ(a))` is the greatest domain point < `succ(a)`.
Since there are no domain points between `a` and `succ(a)` (by the successor
property), `pred(succ(a)) = a`.
-/
theorem limitDomSubtype_pred_succ (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x)
    (a : LimitDomSubtype fc A h_mcs) :
    limitDomSubtypePred fc A h_mcs h_discrete
      (limitDomSubtypeSucc fc A h_mcs h_discrete a) = a := by
  set sa := limitDomSubtypeSucc fc A h_mcs h_discrete a
  set psa := limitDomSubtypePred fc A h_mcs h_discrete sa
  apply le_antisymm
  · -- pred(succ(a)) ≤ a: by contradiction.
    -- If a < psa, then a < psa < succ(a), contradicting the successor property.
    by_contra h_not_le
    push_neg at h_not_le
    -- a < psa, so succ(a) ≤ psa (from succ_le_iff: succ(a) ≤ b ↔ a < b)
    have h_sa_le_psa : sa ≤ psa :=
      (limitDomSubtype_succ_le_iff fc A h_mcs h_discrete a psa).mpr h_not_le
    -- But also psa < sa (pred(succ(a)) < succ(a))
    have h_psa_lt_sa : psa < sa :=
      (limitDomSubtype_le_pred_iff fc A h_mcs h_discrete psa sa).mp le_rfl
    exact lt_irrefl sa (lt_of_le_of_lt h_sa_le_psa h_psa_lt_sa)
  · -- a ≤ pred(succ(a)): from PredOrder property and a < succ(a)
    rw [show a ≤ psa ↔ a < sa from limitDomSubtype_le_pred_iff fc A h_mcs h_discrete a sa]
    -- a < succ(a) follows from the succ_le_iff: succ(a) ≤ b ↔ a < b
    -- Taking b = succ(a): succ(a) ≤ succ(a) ↔ a < succ(a), so a < succ(a)
    exact (limitDomSubtype_succ_le_iff fc A h_mcs h_discrete a sa).mp le_rfl

/--
Helper: `a ≤ pred(b)` when `a < b`. Follows from `limitDomSubtype_le_pred_iff`.
-/
theorem limitDomSubtype_le_pred_of_lt (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x)
    (a b : LimitDomSubtype fc A h_mcs) (h : a < b) :
    a ≤ limitDomSubtypePred fc A h_mcs h_discrete b :=
  (limitDomSubtype_le_pred_iff fc A h_mcs h_discrete a b).mpr h

/--
Helper: `pred(b) < b` for any `b`. Follows from `limitDomSubtype_le_pred_iff`.
-/
theorem limitDomSubtype_pred_lt (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x)
    (b : LimitDomSubtype fc A h_mcs) :
    limitDomSubtypePred fc A h_mcs h_discrete b < b :=
  (limitDomSubtype_le_pred_iff fc A h_mcs h_discrete
    (limitDomSubtypePred fc A h_mcs h_discrete b) b).mp le_rfl

/--
Succ-orbit convexity: if `a ≤ b ≤ succ^[n] a`, then `b = succ^[k] a` for some `k ≤ n`.
This follows from the fact that between consecutive succ-iterates there are no domain
points, so `b` must coincide with one of them.
-/
theorem succ_orbit_convex (fc : FrameClass) (A : Set (Formula Atom)) (h_mcs : SetMaximalConsistent fc A)
    (h_discrete : ∀ x ∈ limitDom fc A h_mcs, nextTop ∈ limitF fc A h_mcs x)
    (a b : LimitDomSubtype fc A h_mcs) (n : ℕ)
    (h_le : a ≤ b)
    (h_ub : b ≤ (limitDomSubtypeSucc fc A h_mcs h_discrete)^[n] a) :
    ∃ k ≤ n, (limitDomSubtypeSucc fc A h_mcs h_discrete)^[k] a = b := by
  set s := limitDomSubtypeSucc fc A h_mcs h_discrete
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at h_ub
    exact ⟨0, le_rfl, le_antisymm h_le h_ub⟩
  | succ n ih =>
    rcases le_or_gt b (s^[n] a) with h_le_n | h_gt_n
    · obtain ⟨k, hkn, hk⟩ := ih h_le_n
      exact ⟨k, Nat.le_succ_of_le hkn, hk⟩
    · have h_succ_le : s (s^[n] a) ≤ b :=
        (limitDomSubtype_succ_le_iff fc A h_mcs h_discrete (s^[n] a) b).mpr h_gt_n
      have h_iter_succ : s^[n + 1] a = s (s^[n] a) :=
        Function.iterate_succ_apply' s n a
      rw [h_iter_succ] at h_ub
      exact ⟨n + 1, le_rfl, by rw [h_iter_succ]; exact (le_antisymm h_ub h_succ_le).symm⟩


/--
From `□(U(⊤,⊥)) ∈ N`, derive that `U(⊤,⊥) ∈ limitF(x)` for all `x ∈ limitDom N`.
Mirror of `box_dense_gives_density`.

Proof: `□(U(⊤,⊥)) → G(□(U(⊤,⊥)))` via `tempFutureDerived`, then at each domain point
`□(U(⊤,⊥)) → U(⊤,⊥)` via `modal_t`. Past direction via `modal_4` + `boxToPast`.
-/
theorem box_discrete_gives_discreteness (fc : FrameClass) (N : Set (Formula Atom)) (h_N : SetMaximalConsistent fc N)
    (h_box_discrete : Formula.box nextTop ∈ N) :
    ∀ x ∈ limitDom fc N h_N, nextTop ∈ limitF fc N h_N x := by
  intro x hx
  -- U(T,bot) ∈ N (from □(U(T,bot)) by modal_t)
  have h_nt_N : nextTop ∈ N :=
    SetMaximalConsistent.implication_property h_N
      (theoremInMcsFc h_N (DerivationTree.axiom [] _ (Axiom.modal_t nextTop) trivial))
      h_box_discrete
  -- G(□(U(T,bot))) ∈ N (from □(U(T,bot)) by tempFutureDerived)
  have h_G_box : Formula.allFuture (Formula.box nextTop) ∈ N :=
    SetMaximalConsistent.implication_property h_N
      (theoremInMcsFc h_N (Cslib.Logic.Bimodal.Theorems.Combinators.tempFutureDerived nextTop))
      h_box_discrete
  -- H(□(U(T,bot))) ∈ N (from □(U(T,bot)) → □□(U(T,bot)) → H(□(U(T,bot))))
  have h_box_box : Formula.box (Formula.box nextTop) ∈ N :=
    SetMaximalConsistent.implication_property h_N
      (theoremInMcsFc h_N (DerivationTree.axiom [] _ (Axiom.modal_4 nextTop) trivial))
      h_box_discrete
  have h_H_box : Formula.allPast (Formula.box nextTop) ∈ N :=
    SetMaximalConsistent.implication_property h_N
      (theoremInMcsFc h_N (liftBase fc (boxToPast (Formula.box nextTop)))) h_box_box
  -- Now propagate to x ∈ limitDom
  rcases lt_trichotomy 0 x with h_pos | rfl | h_neg
  · -- x > 0: G(□(U(T,bot))) ∈ limitF(0) = N, propagate via limit_forward_G
    rw [← limit_f_zero fc N h_N] at h_G_box
    have h_box_x := limit_forward_G fc N h_N 0 x (zero_mem_limit_dom fc N h_N) hx h_pos
      (Formula.box nextTop) h_G_box
    exact SetMaximalConsistent.implication_property (limit_c0 fc N h_N x hx)
      (theoremInMcsFc (limit_c0 fc N h_N x hx)
        (DerivationTree.axiom [] _ (Axiom.modal_t nextTop) trivial)) h_box_x
  · -- x = 0: limitF(0) = N
    rw [limit_f_zero]; exact h_nt_N
  · -- x < 0: H(□(U(T,bot))) ∈ limitF(0) = N, propagate via limit_backward_H
    rw [← limit_f_zero fc N h_N] at h_H_box
    have h_box_x := limit_backward_H fc N h_N 0 x (zero_mem_limit_dom fc N h_N) hx h_neg
      (Formula.box nextTop) h_H_box
    exact SetMaximalConsistent.implication_property (limit_c0 fc N h_N x hx)
      (theoremInMcsFc (limit_c0 fc N h_N x hx)
        (DerivationTree.axiom [] _ (Axiom.modal_t nextTop) trivial)) h_box_x

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle
