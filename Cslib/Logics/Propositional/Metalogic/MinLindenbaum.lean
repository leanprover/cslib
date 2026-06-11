/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Metalogic.DeductionTheorem
public import Cslib.Logics.Propositional.Metalogic.Soundness

/-! # Deductively Closed Sets for Minimal Propositional Logic

This module defines MinTheory (deductively closed sets without consistency requirement)
for MinPropAxiom and proves the implication witness lemma needed for completeness.

## Main Definitions and Results

- `MinTheory`: A set `S` is a MinTheory if it is closed under derivation from MinPropAxiom.
  Unlike `IntDCCS`, there is no consistency requirement -- `⊥` may belong to `S`.
- `min_theory_imp_property`: Modus ponens closure for MinTheory.
- `min_deriv_from_closure_to_S`: Compilation lemma.
- `min_deriv_imp_of_union`: Cut lemma for union contexts.
- `min_imp_witness`: Implication witness lemma (no EFQ needed).
- `lift_min_to_int`: Lift MinPropAxiom derivations to IntPropAxiom.
- `min_consistent`: MinPropAxiom is consistent (`¬ Derivable MinPropAxiom ⊥`).
- `min_theorems_theory`: The set of MinPropAxiom-theorems is a MinTheory.

## References

* CZ Section 5.1, adapted for minimal logic
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open Cslib.Logic.Helpers

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## MinPropAxiom helper hypotheses -/

private def min_h_implyK :
    ∀ (φ ψ : PL.Proposition Atom), MinPropAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

private def min_h_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    MinPropAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

/-! ## MinTheory Definition -/

/-- A deductively closed set (MinTheory) for MinPropAxiom.

Unlike `IntDCCS`, there is **no consistency requirement**. A MinTheory `S`
may contain `⊥`, representing a world where falsum is "true". This is
essential for minimal logic where `bot_forces w = (⊥ ∈ w.val)` is a
genuine predicate rather than trivially `False`. -/
def MinTheory (S : Set (PL.Proposition Atom)) : Prop :=
  ∀ (L : List (PL.Proposition Atom)) (φ : PL.Proposition Atom),
    (∀ x ∈ L, x ∈ S) → (propDerivationSystem MinPropAxiom).Deriv L φ → φ ∈ S

/-! ## Basic MinTheory Properties -/

/-- Modus ponens closure: if `φ → ψ ∈ S` and `φ ∈ S`, then `ψ ∈ S`. -/
theorem min_theory_imp_property {S : Set (PL.Proposition Atom)}
    (h : MinTheory S) {φ ψ : PL.Proposition Atom}
    (h_imp : φ.imp ψ ∈ S) (h_phi : φ ∈ S) : ψ ∈ S := by
  apply h [φ.imp ψ, φ] ψ
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  · exact (propDerivationSystem MinPropAxiom).mp
      ((propDerivationSystem MinPropAxiom).assumption
        (List.mem_cons.mpr (Or.inl rfl)))
      ((propDerivationSystem MinPropAxiom).assumption
        (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

/-! ## Compiling Derivations from Closure Elements -/

/-- If every element of L is derivable from some list in S,
then any φ derivable from L is also derivable from some list in S.

The proof works by induction on L, using the deduction theorem to
"cut" each element `a` out of the context, replacing it with its
witness derivation from S. -/
theorem min_deriv_from_closure_to_S {S : Set (PL.Proposition Atom)}
    (L : List (PL.Proposition Atom))
    (hL : ∀ x ∈ L, ∃ Lx : List (PL.Proposition Atom),
      (∀ y ∈ Lx, y ∈ S) ∧ (propDerivationSystem MinPropAxiom).Deriv Lx x)
    (φ : PL.Proposition Atom)
    (hd : (propDerivationSystem MinPropAxiom).Deriv L φ) :
    ∃ L' : List (PL.Proposition Atom),
      (∀ y ∈ L', y ∈ S) ∧ (propDerivationSystem MinPropAxiom).Deriv L' φ := by
  induction L generalizing φ with
  | nil => exact ⟨[], fun _ h => (nomatch h), hd⟩
  | cons a L' ih =>
    -- DT: L' ⊢ a → φ
    have hd_dt := prop_has_deduction_theorem min_h_implyK min_h_implyS hd
    -- IH on L' with formula (a → φ): get L_imp ⊆ S with L_imp ⊢ a → φ
    obtain ⟨L_imp, hL_imp_sub, hL_imp_deriv⟩ :=
      ih (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))) (a.imp φ) hd_dt
    -- Witness for a: La ⊆ S with La ⊢ a
    obtain ⟨La, hLa_sub, hLa_deriv⟩ := hL a (List.mem_cons.mpr (Or.inl rfl))
    -- Combine: La ++ L_imp ⊆ S, La ++ L_imp ⊢ φ (by MP)
    exact ⟨La ++ L_imp,
      fun y hy => by
        rw [List.mem_append] at hy
        exact hy.elim (hLa_sub y) (hL_imp_sub y),
      (propDerivationSystem MinPropAxiom).mp
        ((propDerivationSystem MinPropAxiom).weakening hL_imp_deriv
          (fun x hx => List.mem_append.mpr (Or.inr hx)))
        ((propDerivationSystem MinPropAxiom).weakening hLa_deriv
          (fun x hx => List.mem_append.mpr (Or.inl hx)))⟩

/-! ## Cut Lemma for Union Contexts -/

/-- If `L ⊢ ψ` and `L ⊆ S ∪ {φ}`, then `∃ L' ⊆ S, L' ⊢ φ → ψ`.

Uses `deductionWithMem` + `removeAll` to eliminate all occurrences of `φ`
from the derivation context. -/
theorem min_deriv_imp_of_union
    {S : Set (PL.Proposition Atom)}
    {L : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (hL : ∀ x ∈ L, x ∈ S ∪ {φ})
    (hd : (propDerivationSystem MinPropAxiom).Deriv L ψ) :
    ∃ L' : List (PL.Proposition Atom),
      (∀ x ∈ L', x ∈ S) ∧
      (propDerivationSystem MinPropAxiom).Deriv L' (φ.imp ψ) := by
  obtain ⟨d⟩ := hd
  -- Weaken to φ :: L, then DT gives L ⊢ φ → ψ
  have d_ext := DerivationTree.weakening L (φ :: L) ψ d
    (fun x hx => List.mem_cons.mpr (Or.inr hx))
  have d_dt := deductionTheorem min_h_implyK min_h_implyS L φ ψ d_ext
  by_cases hφL : φ ∈ L
  · -- φ ∈ L: use deductionWithMem to remove ALL occurrences of φ
    have d_mem := deductionWithMem min_h_implyK min_h_implyS L φ (φ.imp ψ) d_dt hφL
    -- d_mem : DerivationTree (removeAll L φ) (φ → (φ → ψ))
    -- removeAll L φ ⊆ S
    have h_rem_sub : ∀ x ∈ removeAll L φ, x ∈ S := by
      intro x hx
      simp only [removeAll, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not] at hx
      obtain ⟨hx_in, hx_ne⟩ := hx
      rcases hL x hx_in with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hx_ne
    -- Collapse φ → (φ → ψ) to φ → ψ via S-combinator + identity
    let ctx := removeAll L φ
    have d_is : DerivationTree MinPropAxiom (Atom := Atom) ctx
        ((φ.imp (φ.imp ψ)).imp ((φ.imp φ).imp (φ.imp ψ))) :=
      .weakening [] ctx _ (.ax [] _ (.implyS φ φ ψ)) (fun _ h => nomatch h)
    -- MP: ctx ⊢ (φ → φ) → (φ → ψ)
    have d_step1 := DerivationTree.modus_ponens ctx _ _ d_is d_mem
    -- Build identity ⊢ φ → φ
    have d_k1 : DerivationTree MinPropAxiom (Atom := Atom) [] (φ.imp ((φ.imp φ).imp φ)) :=
      .ax [] _ (.implyK φ (φ.imp φ))
    have d_s1 : DerivationTree MinPropAxiom (Atom := Atom) []
        ((φ.imp ((φ.imp φ).imp φ)).imp ((φ.imp (φ.imp φ)).imp (φ.imp φ))) :=
      .ax [] _ (.implyS φ (φ.imp φ) φ)
    have d_mp1 := DerivationTree.modus_ponens [] _ _ d_s1 d_k1
    have d_k2 : DerivationTree MinPropAxiom (Atom := Atom) [] (φ.imp (φ.imp φ)) :=
      .ax [] _ (.implyK φ φ)
    have d_id := DerivationTree.modus_ponens [] _ _ d_mp1 d_k2
    have d_id_w := DerivationTree.weakening [] ctx _ d_id (fun _ h => nomatch h)
    -- MP: ctx ⊢ φ → ψ
    have d_final := DerivationTree.modus_ponens ctx _ _ d_step1 d_id_w
    exact ⟨ctx, h_rem_sub, ⟨d_final⟩⟩
  · -- φ ∉ L: L ⊆ S already
    have hL_S : ∀ x ∈ L, x ∈ S := by
      intro x hx
      rcases hL x hx with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hx) hφL
    exact ⟨L, hL_S, ⟨d_dt⟩⟩

/-! ## Deductive Closure -/

/-- The deductive closure of a set `S` w.r.t. MinPropAxiom. -/
def minDeductiveClosure (S : Set (PL.Proposition Atom)) :
    Set (PL.Proposition Atom) :=
  {φ | ∃ L : List (PL.Proposition Atom),
    (∀ x ∈ L, x ∈ S) ∧ (propDerivationSystem MinPropAxiom).Deriv L φ}

/-- `S ⊆ minDeductiveClosure S`. -/
theorem min_subset_deductive_closure (S : Set (PL.Proposition Atom)) :
    S ⊆ minDeductiveClosure S :=
  fun φ hφ => ⟨[φ],
    fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ hφ,
    (propDerivationSystem MinPropAxiom).assumption (List.mem_cons.mpr (Or.inl rfl))⟩

/-- The deductive closure is a MinTheory (deductively closed). -/
theorem minDeductiveClosure_is_theory (S : Set (PL.Proposition Atom)) :
    MinTheory (minDeductiveClosure S) :=
  fun L φ hL hd => min_deriv_from_closure_to_S L (fun x hx => hL x hx) φ hd

/-! ## Implication Witness Lemma -/

/-- **Implication Witness Lemma**: If `S` is a MinTheory and `φ → ψ ∉ S`,
then the deductive closure of `S ∪ {φ}` is a MinTheory `T ⊇ S` with
`φ ∈ T` and `ψ ∉ T`.

Unlike the intuitionistic version (`int_imp_witness`), no EFQ or consistency
sub-proof is needed. The deductive closure of `S ∪ {φ}` is always a valid
MinTheory regardless of consistency. -/
theorem min_imp_witness {S : Set (PL.Proposition Atom)}
    (h_theory : MinTheory S) {φ ψ : PL.Proposition Atom}
    (h_not : φ.imp ψ ∉ S) :
    ∃ T : Set (PL.Proposition Atom),
      S ⊆ T ∧ MinTheory T ∧ φ ∈ T ∧ ψ ∉ T := by
  refine ⟨minDeductiveClosure (S ∪ {φ}), ?_, ?_, ?_, ?_⟩
  · -- S ⊆ T
    exact Set.Subset.trans Set.subset_union_left (min_subset_deductive_closure _)
  · -- MinTheory T
    exact minDeductiveClosure_is_theory _
  · -- φ ∈ T
    exact min_subset_deductive_closure _ (Set.mem_union_right S (Set.mem_singleton_iff.mpr rfl))
  · -- ψ ∉ T
    intro ⟨L, hL_sub, hL_deriv⟩
    obtain ⟨L', hL'_sub, hL'_deriv⟩ := min_deriv_imp_of_union hL_sub hL_deriv
    exact h_not (h_theory L' _ hL'_sub hL'_deriv)

/-! ## Consistency of MinPropAxiom -/

/-- Lift a MinPropAxiom derivation tree to a PropositionalAxiom (classical)
derivation tree via `MinPropAxiom.toIntProp.toProp`. -/
noncomputable def liftMinToCl {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree MinPropAxiom Γ φ) :
    DerivationTree PropositionalAxiom Γ φ := by
  match d with
  | .ax Γ ψ h_ax => exact .ax Γ ψ h_ax.toIntProp.toProp
  | .assumption Γ ψ h_mem => exact .assumption Γ ψ h_mem
  | .modus_ponens Γ ψ χ d₁ d₂ =>
    exact .modus_ponens Γ ψ χ (liftMinToCl d₁) (liftMinToCl d₂)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact .weakening Γ' Δ ψ (liftMinToCl d') h_sub

/-- MinPropAxiom is consistent: `[] ⊬ ⊥`.

Proof: lift any MinPropAxiom derivation to classical PropositionalAxiom,
then use `prop_soundness` (classical soundness). -/
theorem min_consistent :
    ¬ Derivable (Atom := Atom) MinPropAxiom Proposition.bot := by
  intro ⟨d⟩
  have d_cl := liftMinToCl d
  exact prop_soundness d_cl (fun _ => True) (fun _ h => nomatch h)

/-! ## Min Theorems Form a MinTheory -/

/-- The set of MinPropAxiom-theorems `{ψ | Derivable MinPropAxiom ψ}` is a MinTheory. -/
theorem min_theorems_theory :
    MinTheory ({ψ : PL.Proposition Atom | Derivable MinPropAxiom ψ}) := by
  intro L φ hL hd
  -- Each element of L is derivable from empty context
  have hL_empty : ∀ x ∈ L, ∃ Lx : List (PL.Proposition Atom),
      (∀ y ∈ Lx, y ∈ (∅ : Set (PL.Proposition Atom))) ∧
      (propDerivationSystem MinPropAxiom).Deriv Lx x := by
    intro x hx
    obtain ⟨dx⟩ := (hL x hx : Derivable MinPropAxiom x)
    exact ⟨[], fun _ h => (nomatch h), ⟨dx⟩⟩
  obtain ⟨L', hL'_sub, hL'_deriv⟩ :=
    min_deriv_from_closure_to_S L hL_empty _ hd
  have hL'_nil : L' = [] := by
    by_contra h
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L' h
    exact (hL'_sub a ha).elim
  rw [hL'_nil] at hL'_deriv
  exact hL'_deriv

end Cslib.Logic.PL
