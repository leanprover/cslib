/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleTypes
public import Cslib.Logics.Bimodal.Metalogic.Bundle.WitnessSeed
public import Cslib.Logics.Bimodal.Theorems.TemporalDerived
public import Cslib.Logics.Bimodal.Theorems.Propositional.Core
public import Mathlib.Order.Zorn

/-!
# r-Relation Lemmas (Burgess 1982, Lemmas 2.2-2.3)

This module proves the foundational lemmas about the r-relation
from Burgess 1982 Section 2, adapted for irreflexive (strict) temporal semantics.

## Main Results

- `rRelation_guard_continues'` (Lemma 2.3 consequence): If r(A, B) and
  gamma U delta in A with delta not in B, then gamma in B and gamma U delta in B.

- `rMaximal_extension_exists`: Existence of R-maximal DCS extensions via Zorn's lemma.

- `deductiveClosure_is_dcs`: The deductive closure of a consistent set is a DCS.

- `until_implies_F_in_mcs` / `since_implies_P_in_mcs`: BX10/BX10' at MCS level.

- `until_self_accum_in_mcs`: BX5 at MCS level.

## Adaptation for Open Guard Semantics (Task 113)

Under open guard semantics (t,s), the evaluation point t is NOT in the guard
interval. Key consequences:
- BX9 (until_elim) is REMOVED: `(phi U psi) -> (phi ∨ psi)` is invalid
- until_guard axiom is REMOVED: `(phi U psi) -> phi` is invalid
- Several lemmas in this file are INVALID and marked with sorry stubs

The r-relation lemmas use:
- BX5 (self_accum_until): `(phi U psi) -> ((phi ∧ (phi U psi)) U psi)`
- BX10 (until_F): `(phi U psi) -> F(psi)` (VALID under open guard)

## References

- Burgess 1982: "Axioms for tense logic II: Time periods", Lemmas 2.2-2.3
- Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Theorems.Combinators

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## Note on Lemma 2.2 (Until Guard Consistency)

Burgess's Lemma 2.2 states: if `gamma U delta in A` for MCS A, then `{gamma}` is
consistent. This is **FALSE** under strict (irreflexive) Until semantics for gamma = bot.

**Concrete counterexample**: Let gamma = bot. Then {bot} is trivially inconsistent
(it derives bot). But bot U delta can be in an MCS A: by BX9 (until_elim),
bot U delta -> bot ∨ delta = delta, so delta ∈ A. The formula bot U delta is
semantically absurd on dense orders (the guard bot can never hold at any point)
but is syntactically consistent with the BX axiom system -- BX9 only gives
bot ∨ delta, not bot, so no contradiction in A.

Under half-closed guard [t,s) the weaker statement `gamma U delta ∈ A -> gamma ∨ delta ∈ A`
WAS provable (via BX9). Under open guard (t,s), even this weaker statement is INVALID:
neither gamma nor delta need hold at the evaluation point t. The `until_disjunction_in_mcs`
lemma has been REMOVED (task 113 Phase 3). The chronicle construction uses the
r-relation machinery and BX10 instead.

Withdrawn in Phase 1 of the revised plan (task 107).
-/

/--
`gamma U delta in A` implies `F(delta) in A` (by BX10).
-/
theorem until_implies_F_in_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {γ δ : Formula Atom}
    (h_until : Formula.untl δ γ ∈ A) :
    Formula.someFuture δ ∈ A := by
  have h_F : DerivationTree fc [] ((Formula.untl δ γ).imp (Formula.someFuture δ)) :=
    DerivationTree.axiom [] _ (Axiom.until_F γ δ) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs_fc h_mcs h_F) h_until

/--
`gamma U delta in A` implies `(gamma ∧ (gamma U delta)) U delta in A` (by BX5).
-/
theorem until_self_accum_in_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {γ δ : Formula Atom}
    (h_until : Formula.untl δ γ ∈ A) :
    Formula.untl δ (Formula.and γ (Formula.untl δ γ)) ∈ A := by
  have h_sa : DerivationTree fc []
      ((Formula.untl δ γ).imp
        (Formula.untl δ (Formula.and γ (Formula.untl δ γ)))) :=
    DerivationTree.axiom [] _ (Axiom.self_accum_until γ δ) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs_fc h_mcs h_sa) h_until

/--
`gamma S delta in A` implies `P(delta) in A` (by BX10').
-/
theorem since_implies_P_in_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {γ δ : Formula Atom}
    (h_since : Formula.snce δ γ ∈ A) :
    Formula.somePast δ ∈ A := by
  have h_P : DerivationTree fc [] ((Formula.snce δ γ).imp (Formula.somePast δ)) :=
    DerivationTree.axiom [] _ (Axiom.since_P γ δ) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs_fc h_mcs h_P) h_since

/-! ## Lemma 2.3: r-Relation Properties -/

/--
**Key property from Lemma 2.3**: If r(A, B) and gamma U delta in A with delta not in B,
then gamma in B and gamma U delta in B.

This is the "guard continues" property of the r-relation.
-/
theorem rRelation_guard_continues' {A B : Set (Formula Atom)}
    (h_r : rRelation A B) {γ δ : Formula Atom}
    (h_until : Formula.untl δ γ ∈ A) (h_not_delta : δ ∉ B) :
    γ ∈ B ∧ Formula.untl δ γ ∈ B := by
  rcases h_r γ δ h_until with h_delta | h_guard
  · exact absurd h_delta h_not_delta
  · exact h_guard

/-! ## Deductive Closure -/

/--
Deductive closure of a set: the set of all formulas derivable from finite subsets of S.
-/
noncomputable def deductiveClosure (fc : FrameClass) (Sig : Set (Formula Atom)) : Set (Formula Atom) :=
  {φ | ∃ L : List (Formula Atom), (∀ ψ ∈ L, ψ ∈ Sig) ∧ Nonempty (DerivationTree fc L φ)}

/-- The deductive closure contains the original set. -/
theorem subset_deductiveClosure (fc : FrameClass) (Sig : Set (Formula Atom)) : Sig ⊆ deductiveClosure fc Sig := by
  intro φ hφ
  exact ⟨[φ], fun ψ hψ => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hψ; exact hψ ▸ hφ,
         ⟨DerivationTree.assumption _ φ (by simp)⟩⟩

/-- The deductive closure is closed under derivation. -/
theorem deductiveClosure_closed (fc : FrameClass) (Sig : Set (Formula Atom)) :
    ∀ (L : List (Formula Atom)) (φ : Formula Atom),
      (∀ ψ ∈ L, ψ ∈ deductiveClosure fc Sig) → DerivationTree fc L φ → φ ∈ deductiveClosure fc Sig := by
  intro L
  induction L with
  | nil =>
    intro φ _ d
    exact ⟨[], fun _ h => absurd h List.not_mem_nil, ⟨d⟩⟩
  | cons ψ L' ih =>
    intro φ hL d
    -- (ψ :: L') ⊢ φ. By deduction theorem: L' ⊢ ψ.imp φ.
    have d_imp : DerivationTree fc L' (ψ.imp φ) := deduction_theorem L' ψ φ d
    -- ψ ∈ deductiveClosure S
    have hψ := hL ψ (List.mem_cons_self)
    -- L' ⊆ deductiveClosure S
    have hL' : ∀ χ ∈ L', χ ∈ deductiveClosure fc Sig :=
      fun χ hχ => hL χ (List.mem_cons_of_mem ψ hχ)
    -- By IH (with ψ.imp φ): ψ.imp φ ∈ deductiveClosure S
    have h_imp := ih (ψ.imp φ) hL' d_imp
    -- Combine: ψ and ψ.imp φ are both in deductiveClosure S
    obtain ⟨M1, hM1_sub, ⟨d1⟩⟩ := h_imp  -- M1 ⊢ ψ → φ, M1 ⊆ Sig
    obtain ⟨M2, hM2_sub, ⟨d2⟩⟩ := hψ      -- M2 ⊢ ψ, M2 ⊆ Sig
    -- Take M = M1 ++ M2, derive M ⊢ φ by modus ponens
    refine ⟨M1 ++ M2, fun χ hχ => ?_, ?_⟩
    · rcases List.mem_append.mp hχ with h | h
      · exact hM1_sub χ h
      · exact hM2_sub χ h
    · have d1' : DerivationTree fc (M1 ++ M2) (ψ.imp φ) :=
        DerivationTree.weakening M1 (M1 ++ M2) (ψ.imp φ) d1
          (List.subset_append_left M1 M2)
      have d2' : DerivationTree fc (M1 ++ M2) ψ :=
        DerivationTree.weakening M2 (M1 ++ M2) ψ d2
          (List.subset_append_right M1 M2)
      exact ⟨DerivationTree.modus_ponens (M1 ++ M2) ψ φ d1' d2'⟩

/-- If S is consistent, then deductiveClosure S is consistent. -/
theorem deductiveClosure_consistent (fc : FrameClass) {Sig : Set (Formula Atom)} (h : SetConsistent fc Sig) :
    SetConsistent fc (deductiveClosure fc Sig) := by
  intro L hL ⟨d⟩
  have h_bot : (Formula.bot : Formula Atom) ∈ deductiveClosure fc Sig :=
    deductiveClosure_closed fc Sig L Formula.bot hL d
  obtain ⟨M, hM_sub, ⟨dM⟩⟩ := h_bot
  exact h M hM_sub ⟨dM⟩

/-- The deductive closure of a consistent set is a DCS. -/
theorem deductiveClosure_is_dcs (fc : FrameClass) {Sig : Set (Formula Atom)} (h : SetConsistent fc Sig) :
    SetDeductivelyClosed fc (deductiveClosure fc Sig) :=
  ⟨deductiveClosure_consistent fc h, deductiveClosure_closed fc Sig⟩

/-- The deductive closure of ANY set is `ClosedUnderDerivation` (regardless of consistency).
This is the key lemma for the strengthened BurgessR3Maximal definition:
when {δ} ∪ B is inconsistent, DC({δ} ∪ B) = Set.univ, which is still ClosedUnderDerivation. -/
theorem deductiveClosure_closed_under_derivation (fc : FrameClass) (Sig : Set (Formula Atom)) :
    ClosedUnderDerivation fc (deductiveClosure fc Sig) :=
  deductiveClosure_closed fc Sig

/-! ## R-Maximal Extension Existence -/

/--
The set of all DCS that extend S, are deductively closed, and satisfy r(A, -).
-/
def rDCSExtensions (fc : FrameClass) (A Sig : Set (Formula Atom)) : Set (Set (Formula Atom)) :=
  {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ rRelation A B}

/--
Given an MCS A and a DCS S with r(A, S), there exists an R-maximal DCS B
with Sig ⊆ B and r(A, B).

Proof: Apply Zorn's lemma to the set of DCS extending S and satisfying r(A, -),
ordered by subset inclusion. Every chain has an upper bound (its union),
which is again a DCS satisfying the r-relation.
-/
theorem rMaximal_extension_exists (fc : FrameClass) {A : Set (Formula Atom)}
    (_h_mcs : SetMaximalConsistent fc A)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc Sig) (h_r : rRelation A Sig) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ rMaximal fc A B := by
  -- Verify S is in the extension set
  have h_S_in : Sig ∈ rDCSExtensions fc A Sig := ⟨Set.Subset.refl _, h_dcs, h_r⟩
  -- Apply Zorn's subset lemma
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset (rDCSExtensions fc A Sig) (by
    intro c hc_sub hc_chain
    by_cases hc_empty : c = ∅
    · exact ⟨Sig, h_S_in, by intro t ht; exact absurd ht (by rw [hc_empty]; exact Set.notMem_empty _)⟩
    · obtain ⟨T₀, hT₀⟩ := Set.nonempty_iff_ne_empty.mpr hc_empty
      refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
      refine ⟨Set.subset_sUnion_of_subset c T₀ (hc_sub hT₀).1 hT₀, ?_, ?_⟩
      · -- ⋃₀ c is a DCS
        constructor
        · -- Consistency: any finite L ⊆ ⋃₀ c is in some element of chain
          intro L hL ⟨d⟩
          obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L
            (fun φ hφ => hL φ hφ)
          exact (hc_sub hTc).2.1.1 L hLT ⟨d⟩
        · -- Closure under derivation: same finite subset argument
          intro L φ hL d
          obtain ⟨T, hTc, hLT⟩ := chain_finite_subset_in_element hc_chain hT₀ L
            (fun ψ hψ => hL ψ hψ)
          exact Set.mem_sUnion.mpr ⟨T, hTc, (hc_sub hTc).2.1.2 L φ hLT d⟩
      · -- r(A, ⋃₀ c): pick any element from chain
        intro γ δ h_until
        rcases (hc_sub hT₀).2.2 γ δ h_until with h_d | ⟨h_g, h_u⟩
        · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
        · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩,
                         Set.mem_sUnion.mpr ⟨T₀, hT₀, h_u⟩⟩)
  -- Extract the R-maximal properties
  obtain ⟨hSB, hB_dcs, hB_r⟩ := hB_in
  refine ⟨B, hSB, hB_dcs, hB_r, ?_⟩
  -- Maximality: no proper DCS extension satisfies r(A, -)
  intro C hC_dcs hBC hC_r
  have hC_in : C ∈ rDCSExtensions fc A Sig :=
    ⟨Set.Subset.trans hSB hBC.1, hC_dcs, hC_r⟩
  -- hB_max gives C ⊆ B, contradicting hBC : B ⊂ C (which has ¬(C ⊆ B))
  exact hBC.2 (hB_max hC_in hBC.1)
where
  /-- Helper: for a chain of sets and a finite list L whose elements are each in
  some element of the chain, all of L is contained in a single chain element. -/
  chain_finite_subset_in_element {c : Set (Set (Formula Atom))} {T₀ : Set (Formula Atom)}
      (hc_chain : IsChain (· ⊆ ·) c) (hT₀ : T₀ ∈ c)
      (L : List (Formula Atom))
      (hL : ∀ φ ∈ L, φ ∈ ⋃₀ c) :
      ∃ T ∈ c, ∀ φ ∈ L, φ ∈ T := by
    induction L with
    | nil => exact ⟨T₀, hT₀, fun _ h => absurd h List.not_mem_nil⟩
    | cons a L ih =>
      obtain ⟨Ta, hTa, ha⟩ := Set.mem_sUnion.mp (hL a (List.mem_cons_self))
      obtain ⟨TL, hTL, hLTL⟩ := ih (fun φ hφ => hL φ (List.mem_cons_of_mem a hφ))
      rcases hc_chain.total hTa hTL with h_le | h_le
      · exact ⟨TL, hTL, fun φ hφ => by
          rcases List.mem_cons.mp hφ with rfl | h
          · exact h_le ha
          · exact hLTL φ h⟩
      · exact ⟨Ta, hTa, fun φ hφ => by
          rcases List.mem_cons.mp hφ with rfl | h
          · exact ha
          · exact h_le (hLTL φ h)⟩

/--
Similarly for Since: R-maximal Since extensions exist.
-/
theorem rMaximalSince_extension_exists (fc : FrameClass) {A : Set (Formula Atom)}
    (_h_mcs : SetMaximalConsistent fc A)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc Sig)
    (h_r : rRelationSince A Sig) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ rMaximalSince fc A B := by
  have h_S_in : Sig ∈ {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ rRelationSince A B} :=
    ⟨Set.Subset.refl _, h_dcs, h_r⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ rRelationSince A B} (by
    intro c hc_sub hc_chain
    by_cases hc_empty : c = ∅
    · exact ⟨Sig, h_S_in, by intro t ht; exact absurd ht (by rw [hc_empty]; exact Set.notMem_empty _)⟩
    · obtain ⟨T₀, hT₀⟩ := Set.nonempty_iff_ne_empty.mpr hc_empty
      refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
      refine ⟨Set.subset_sUnion_of_subset c T₀ (hc_sub hT₀).1 hT₀, ?_, ?_⟩
      · constructor
        · intro L hL ⟨d⟩
          obtain ⟨T, hTc, hLT⟩ := rMaximal_extension_exists.chain_finite_subset_in_element
            hc_chain hT₀ L (fun φ hφ => hL φ hφ)
          exact (hc_sub hTc).2.1.1 L hLT ⟨d⟩
        · intro L φ hL d
          obtain ⟨T, hTc, hLT⟩ := rMaximal_extension_exists.chain_finite_subset_in_element
            hc_chain hT₀ L (fun ψ hψ => hL ψ hψ)
          exact Set.mem_sUnion.mpr ⟨T, hTc, (hc_sub hTc).2.1.2 L φ hLT d⟩
      · intro γ δ h_since
        rcases (hc_sub hT₀).2.2 γ δ h_since with h_d | ⟨h_g, h_s⟩
        · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
        · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩,
                         Set.mem_sUnion.mpr ⟨T₀, hT₀, h_s⟩⟩)
  obtain ⟨hSB, hB_dcs, hB_r⟩ := hB_in
  refine ⟨B, hSB, hB_dcs, hB_r, ?_⟩
  intro C hC_dcs hBC hC_r
  have hC_in : C ∈ {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ rRelationSince A B} :=
    ⟨Set.Subset.trans hSB hBC.1, hC_dcs, hC_r⟩
  exact hBC.2 (hB_max hC_in hBC.1)

/-! ## Three-Argument R-Maximal Extension Existence -/

/--
The set of DCS extending S that satisfy r3Relation A - C.
-/
def r3DCSExtensions (fc : FrameClass) (A Sig C : Set (Formula Atom)) : Set (Set (Formula Atom)) :=
  {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ r3Relation A B C}

/--
Given MCS A and C, and a DCS S with r3Relation A Sig C, there exists an
R3-maximal DCS B with Sig ⊆ B and R3Maximal A B C.

The proof is identical in structure to `rMaximal_extension_exists`:
Zorn's lemma on the set of DCS extending S satisfying r3Relation A - C.
Every chain has an upper bound (its union), which preserves both the
rRelation A - and rRelationSince C - conditions.
-/
theorem r3Maximal_extension_exists (fc : FrameClass) {A C : Set (Formula Atom)}
    (_h_mcs_A : SetMaximalConsistent fc A) (_h_mcs_C : SetMaximalConsistent fc C)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc Sig) (h_r3 : r3Relation A Sig C) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ R3Maximal fc A B C := by
  have h_S_in : Sig ∈ r3DCSExtensions fc A Sig C := ⟨Set.Subset.refl _, h_dcs, h_r3⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset (r3DCSExtensions fc A Sig C) (by
    intro c hc_sub hc_chain
    by_cases hc_empty : c = ∅
    · exact ⟨Sig, h_S_in, by intro t ht; exact absurd ht (by rw [hc_empty]; exact Set.notMem_empty _)⟩
    · obtain ⟨T₀, hT₀⟩ := Set.nonempty_iff_ne_empty.mpr hc_empty
      refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
      refine ⟨Set.subset_sUnion_of_subset c T₀ (hc_sub hT₀).1 hT₀, ?_, ?_⟩
      · -- ⋃₀ c is a DCS (same argument as rMaximal fc case)
        constructor
        · intro L hL ⟨d⟩
          obtain ⟨T, hTc, hLT⟩ := rMaximal_extension_exists.chain_finite_subset_in_element
            hc_chain hT₀ L (fun φ hφ => hL φ hφ)
          exact (hc_sub hTc).2.1.1 L hLT ⟨d⟩
        · intro L φ hL d
          obtain ⟨T, hTc, hLT⟩ := rMaximal_extension_exists.chain_finite_subset_in_element
            hc_chain hT₀ L (fun ψ hψ => hL ψ hψ)
          exact Set.mem_sUnion.mpr ⟨T, hTc, (hc_sub hTc).2.1.2 L φ hLT d⟩
      · -- r3Relation A (⋃₀ c) C: both rRelation A - and rRelationSince C - hold
        constructor
        · -- rRelation A (⋃₀ c)
          intro γ δ h_until
          rcases (hc_sub hT₀).2.2.1 γ δ h_until with h_d | ⟨h_g, h_u⟩
          · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
          · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩,
                           Set.mem_sUnion.mpr ⟨T₀, hT₀, h_u⟩⟩
        · -- rRelationSince C (⋃₀ c)
          intro γ δ h_since
          rcases (hc_sub hT₀).2.2.2 γ δ h_since with h_d | ⟨h_g, h_s⟩
          · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
          · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩,
                           Set.mem_sUnion.mpr ⟨T₀, hT₀, h_s⟩⟩)
  obtain ⟨hSB, hB_dcs, hB_r3⟩ := hB_in
  refine ⟨B, hSB, hB_dcs, hB_r3, ?_⟩
  intro D hD_dcs hBD hD_r3
  have hD_in : D ∈ r3DCSExtensions fc A Sig C :=
    ⟨Set.Subset.trans hSB hBD.1, hD_dcs, hD_r3⟩
  exact hBD.2 (hB_max hD_in hBD.1)

/--
Mirror: R3-maximal Since extensions exist.
-/
theorem r3MaximalSince_extension_exists (fc : FrameClass) {A C : Set (Formula Atom)}
    (_h_mcs_A : SetMaximalConsistent fc A) (_h_mcs_C : SetMaximalConsistent fc C)
    {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc Sig) (h_r3 : r3RelationSince A Sig C) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ R3MaximalSince fc A B C := by
  have h_S_in : Sig ∈ {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ r3RelationSince A B C} :=
    ⟨Set.Subset.refl _, h_dcs, h_r3⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ r3RelationSince A B C} (by
    intro c hc_sub hc_chain
    by_cases hc_empty : c = ∅
    · exact ⟨Sig, h_S_in, by intro t ht; exact absurd ht (by rw [hc_empty]; exact Set.notMem_empty _)⟩
    · obtain ⟨T₀, hT₀⟩ := Set.nonempty_iff_ne_empty.mpr hc_empty
      refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
      refine ⟨Set.subset_sUnion_of_subset c T₀ (hc_sub hT₀).1 hT₀, ?_, ?_⟩
      · constructor
        · intro L hL ⟨d⟩
          obtain ⟨T, hTc, hLT⟩ := rMaximal_extension_exists.chain_finite_subset_in_element
            hc_chain hT₀ L (fun φ hφ => hL φ hφ)
          exact (hc_sub hTc).2.1.1 L hLT ⟨d⟩
        · intro L φ hL d
          obtain ⟨T, hTc, hLT⟩ := rMaximal_extension_exists.chain_finite_subset_in_element
            hc_chain hT₀ L (fun ψ hψ => hL ψ hψ)
          exact Set.mem_sUnion.mpr ⟨T, hTc, (hc_sub hTc).2.1.2 L φ hLT d⟩
      · -- r3RelationSince A (⋃₀ c) C
        constructor
        · -- rRelationSince A (⋃₀ c)
          intro γ δ h_since
          rcases (hc_sub hT₀).2.2.1 γ δ h_since with h_d | ⟨h_g, h_s⟩
          · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
          · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩,
                           Set.mem_sUnion.mpr ⟨T₀, hT₀, h_s⟩⟩
        · -- rRelation C (⋃₀ c)
          intro γ δ h_until
          rcases (hc_sub hT₀).2.2.2 γ δ h_until with h_d | ⟨h_g, h_u⟩
          · exact Or.inl (Set.mem_sUnion.mpr ⟨T₀, hT₀, h_d⟩)
          · exact Or.inr ⟨Set.mem_sUnion.mpr ⟨T₀, hT₀, h_g⟩,
                           Set.mem_sUnion.mpr ⟨T₀, hT₀, h_u⟩⟩)
  obtain ⟨hSB, hB_dcs, hB_r3⟩ := hB_in
  refine ⟨B, hSB, hB_dcs, hB_r3, ?_⟩
  intro D hD_dcs hBD hD_r3
  have hD_in : D ∈ {B | Sig ⊆ B ∧ SetDeductivelyClosed fc B ∧ r3RelationSince A B C} :=
    ⟨Set.Subset.trans hSB hBD.1, hD_dcs, hD_r3⟩
  exact hBD.2 (hB_max hD_in hBD.1)

/--
A deductive closure seed for r3-relation: given rRelation and rRelationSince,
the three-argument version holds automatically.
-/
theorem r3_seed_from_rRelation {A B C : Set (Formula Atom)}
    (h_r : rRelation A B) (h_rS : rRelationSince C B) : r3Relation A B C :=
  ⟨h_r, h_rS⟩

/-! ## Burgess r-Relation Lemmas

The burgessR, burgessRSet, burgessRSince, burgessRSetSince, burgessR3, and
BurgessR3Maximal definitions are in ChronicleTypes.lean (to avoid circular imports).
This section contains the LEMMAS about these relations.
-/

/-! ## Lemma 2.5: Absorption / Intersection Identity

The key lemma for the chronicle construction: if we have r3-maximality for
adjacent pairs and define non-adjacent g values by C3 (three-way intersection),
then the Burgess r-relation holds for the non-adjacent pairs via BX6 absorption.

**The argument**: Given β ∈ g(w,x) ∩ f(x) ∩ B and γ ∈ C:
1. β ∈ B and burgessR(f(x), B, C): (β U γ) ∈ f(x)
2. β ∈ f(x): β ∧ (β U γ) ∈ f(x) (conjunction in MCS)
3. β ∈ g(w,x) and burgessR(f(w), g(w,x), f(x)):
   ((β ∧ (β U γ)) U β) ∈ f(w) -- using β ∧ (β U γ) ∈ f(x) as the "event"
   Wait, that's not right. Let me re-derive.

Actually, burgessR(f(w), β, f(x)) means: for all α ∈ f(x), (β U α) ∈ f(w).
So from β ∧ (β U γ) ∈ f(x): (β U (β ∧ (β U γ))) ∈ f(w).
By BX6 (absorb_until): (β U (β ∧ (β U γ))) → (β U γ).
So (β U γ) ∈ f(w).

This is exactly the Lemma 2.5 argument!
-/

/--
**Lemma 2.5 absorption (single element)**: Given burgessR(A, β, D) where β ∈ D,
burgessR(D, β, C), and D is an MCS, then burgessR(A, β, C).

Uses BX6 (absorb_until): (β U (β ∧ (β U γ))) → (β U γ).

Proof:
1. γ ∈ C and burgessR(D, β, C): (β U γ) ∈ D
2. β ∈ D: β ∧ (β U γ) ∈ D (conjunction in MCS)
3. β ∧ (β U γ) ∈ D and burgessR(A, β, D): (β U (β ∧ (β U γ))) ∈ A
4. BX6: (β U (β ∧ (β U γ))) → (β U γ), so (β U γ) ∈ A.
-/
theorem burgessR_absorption (fc : FrameClass) {A D C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_D : SetMaximalConsistent fc D)
    (β : Formula Atom)
    (h_β_D : β ∈ D)
    (h_rAD : burgessR A β D)
    (h_rDC : burgessR D β C) :
    burgessR A β C := by
  intro γ h_γ_C
  -- Step 1: (β U γ) ∈ D
  have h1 : Formula.untl γ β ∈ D := h_rDC γ h_γ_C
  -- Step 2: β ∧ (β U γ) ∈ D
  have h2 : Formula.and β (Formula.untl γ β) ∈ D :=
    dcs_conj_closed (mcs_is_dcs h_mcs_D) h_β_D h1
  -- Step 3: (β U (β ∧ (β U γ))) ∈ A
  have h3 : Formula.untl (Formula.and β (Formula.untl γ β)) β ∈ A :=
    h_rAD (Formula.and β (Formula.untl γ β)) h2
  -- Step 4: BX6 → (β U γ) ∈ A
  have h_bx6 : DerivationTree fc []
      ((Formula.untl (Formula.and β (Formula.untl γ β)) β).imp (Formula.untl γ β)) :=
    DerivationTree.axiom [] _ (Axiom.absorb_until β γ) trivial
  exact SetMaximalConsistent.implication_property h_mcs_A
    (theorem_in_mcs_fc h_mcs_A h_bx6) h3

/--
**Lemma 2.5 absorption (set version)**: Given burgessRSet(A, B∩D, D) where B∩D ⊆ D,
burgessRSet(D, B∩D, C), and D is MCS, A is MCS, then burgessRSet(A, B∩D, C).

This is the set-level version used for the three-way intersection.
-/
theorem burgessRSet_absorption (fc : FrameClass) {A D C : Set (Formula Atom)} {B : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_D : SetMaximalConsistent fc D)
    (h_sub_D : B ⊆ D)
    (h_rAD : burgessRSet A B D)
    (h_rDC : burgessRSet D B C) :
    burgessRSet A B C := by
  intro β h_β_B
  exact burgessR_absorption fc h_mcs_A h_mcs_D β (h_sub_D h_β_B)
    (h_rAD β h_β_B) (h_rDC β h_β_B)

/-! ## Since-Direction Absorption (Mirror) -/

/--
**Lemma 2.5 absorption for Since (single element)**: Mirror of `burgessR_absorption`
using BX6' (absorb_since): (β S (β ∧ (β S γ))) → (β S γ).
-/
theorem burgessRSince_absorption (fc : FrameClass) {A D C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_D : SetMaximalConsistent fc D)
    (β : Formula Atom)
    (h_β_D : β ∈ D)
    (h_rAD : burgessRSince A β D)
    (h_rDC : burgessRSince D β C) :
    burgessRSince A β C := by
  intro γ h_γ_C
  -- Step 1: (β S γ) ∈ D
  have h1 : Formula.snce γ β ∈ D := h_rDC γ h_γ_C
  -- Step 2: β ∧ (β S γ) ∈ D
  have h2 : Formula.and β (Formula.snce γ β) ∈ D :=
    dcs_conj_closed (mcs_is_dcs h_mcs_D) h_β_D h1
  -- Step 3: (β S (β ∧ (β S γ))) ∈ A
  have h3 : Formula.snce (Formula.and β (Formula.snce γ β)) β ∈ A :=
    h_rAD (Formula.and β (Formula.snce γ β)) h2
  -- Step 4: BX6' → (β S γ) ∈ A
  have h_bx6' : DerivationTree fc []
      ((Formula.snce (Formula.and β (Formula.snce γ β)) β).imp (Formula.snce γ β)) :=
    DerivationTree.axiom [] _ (Axiom.absorb_since β γ) trivial
  exact SetMaximalConsistent.implication_property h_mcs_A
    (theorem_in_mcs_fc h_mcs_A h_bx6') h3

/--
**Lemma 2.5 absorption for Since (set version)**.
-/
theorem burgessRSetSince_absorption (fc : FrameClass) {A D C : Set (Formula Atom)} {B : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_D : SetMaximalConsistent fc D)
    (h_sub_D : B ⊆ D)
    (h_rAD : burgessRSetSince A B D)
    (h_rDC : burgessRSetSince D B C) :
    burgessRSetSince A B C := by
  intro β h_β_B
  exact burgessRSince_absorption fc h_mcs_A h_mcs_D β (h_sub_D h_β_B)
    (h_rAD β h_β_B) (h_rDC β h_β_B)

/-! ## Combined Burgess r3 Absorption

The full Lemma 2.5 for the three-argument case: if g(w,y) = g(w,x) ∩ f(x) ∩ B
where burgessR3(f(w), g(w,x), f(x)) and burgessR3(f(x), B, C), then
burgessR3(f(w), g(w,y), C).
-/

/--
**Lemma 2.5 (full three-argument absorption)**: Given:
- burgessR3(A, B₁, D) (B₁ relates A to intermediate D)
- burgessR3(D, B₂, C) (B₂ relates intermediate D to C)
- B₁₂ ⊆ B₁ ∩ D ∩ B₂ (the three-way intersection)
- A, D, C are MCS

Then burgessR3(A, B₁₂, C).

This is the combined forward + backward absorption that proves the
Burgess r-relation holds for non-adjacent pairs defined by C3.
-/
theorem burgessR3_absorption (fc : FrameClass) {A D C : Set (Formula Atom)} {B₁ B₂ B₁₂ : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_D : SetMaximalConsistent fc D)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_sub_B₁ : B₁₂ ⊆ B₁) (h_sub_D : B₁₂ ⊆ D) (h_sub_B₂ : B₁₂ ⊆ B₂)
    (h_r3_AD : burgessR3 A B₁ D)
    (h_r3_DC : burgessR3 D B₂ C) :
    burgessR3 A B₁₂ C := by
  constructor
  · have h_rAD : burgessRSet A B₁₂ D := fun β hβ => h_r3_AD.1 β (h_sub_B₁ hβ)
    have h_rDC : burgessRSet D B₁₂ C := fun β hβ => h_r3_DC.1 β (h_sub_B₂ hβ)
    exact burgessRSet_absorption fc h_mcs_A h_mcs_D h_sub_D h_rAD h_rDC
  · have h_rCD : burgessRSetSince C B₁₂ D := fun β hβ => h_r3_DC.2 β (h_sub_B₂ hβ)
    have h_rDA : burgessRSetSince D B₁₂ A := fun β hβ => h_r3_AD.2 β (h_sub_B₁ hβ)
    exact burgessRSetSince_absorption fc h_mcs_C h_mcs_D h_sub_D h_rCD h_rDA

/-! ## MCS Contrapositive and C4 Hard Case Derivations -/

/--
Contrapositive in an MCS from membership: if (A -> B) in S and neg(B) in S,
then neg(A) in S. This is the MCS-internal version of the logical contrapositive.
-/
theorem mcs_contrapositive_mem (fc : FrameClass) {Sig : Set (Formula Atom)} (h_mcs : SetMaximalConsistent fc Sig)
    {A B : Formula Atom} (h_impl : A.imp B ∈ Sig) (h_negB : B.neg ∈ Sig) : A.neg ∈ Sig := by
  rcases SetMaximalConsistent.negation_complete h_mcs A with h_A | h_negA
  · have h_B := SetMaximalConsistent.implication_property h_mcs h_impl h_A
    exact absurd (set_consistent_not_both h_mcs.1 B h_B h_negB) id
  · exact h_negA

/--
Key syntactic derivation for the C4 hard case (Burgess Lemma 2.9):
from G(gamma) in A and neg(untl(gamma, delta)) in A, derive G(neg(delta)) in A.

This shows that in the hard case of C4 elimination (where gamma in f(x),
G(gamma) in f(x), and neg(gamma U delta) in f(x)), all future points
must satisfy neg(delta). The derivation uses BX2G (left monotonicity of Until
under G) and BX12 (F(delta) <-> top U delta).

Steps:
1. G(top -> gamma) from G(gamma) by temporal necessitation + distribution
2. BX2G: G(top -> gamma) implies (top U delta -> gamma U delta)
3. Contrapositive with neg(gamma U delta): neg(top U delta) in A
4. BX12 contrapositive: neg(F(delta)) in A, i.e., G(neg(delta)) in A
-/
theorem c4_hard_case_G_neg_delta (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {γ δ : Formula Atom}
    (_h_γ : γ ∈ A)
    (h_Gγ : Formula.allFuture γ ∈ A)
    (h_neg_until : (Formula.untl δ γ).neg ∈ A) :
    Formula.allFuture δ.neg ∈ A := by
  set top := Formula.bot.imp (Formula.bot : Formula Atom) with htop_def
  -- G(top -> gamma) in A by temporal necessitation of prop_s + G distribution
  have h_G_top_gamma : Formula.allFuture (top.imp γ) ∈ A := by
    have h_G_ps := theorem_in_mcs_fc h_mcs
      (DerivationTree.temporal_necessitation _ (DerivationTree.axiom [] _ (Axiom.imp_s γ top) trivial))
    have h_dist := theorem_in_mcs_fc h_mcs
      (liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived (Atom := Atom) γ (top.imp γ)))
    exact SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h_dist h_G_ps) h_Gγ
  -- BX2G: G(top -> gamma) -> (delta U top -> delta U gamma)
  have h_ax := theorem_in_mcs_fc h_mcs
    (DerivationTree.axiom [] _ (Axiom.left_mono_until_G top γ δ) trivial)
  have h_mono : (Formula.untl δ top).imp (Formula.untl δ γ) ∈ A :=
    SetMaximalConsistent.implication_property h_mcs h_ax h_G_top_gamma
  -- Contrapositive: neg(gamma U delta) -> neg(top U delta)
  have h_neg_top_until := mcs_contrapositive_mem fc h_mcs h_mono h_neg_until
  -- BX12 contrapositive: neg(top U delta) -> neg(F(delta))
  have h_bx12 := theorem_in_mcs_fc h_mcs
    (DerivationTree.axiom [] _ (Axiom.F_until_equiv δ) trivial)
  have h_neg_F := mcs_contrapositive_mem fc h_mcs h_bx12 h_neg_top_until
  -- ¬F(δ) → G(¬δ) via duality conversion
  exact neg_someFuture_to_allFuture_neg h_mcs δ h_neg_F

/--
Mirror of `c4_hard_case_G_neg_delta` for the Since direction (C4' hard case):
from H(gamma) in A and neg(snce(gamma, delta)) in A, derive H(neg(delta)) in A.

Uses BX2H (left monotonicity of Since under H) and BX12' (P(delta) <-> top S delta).
-/
theorem c4'_hard_case_H_neg_delta (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {γ δ : Formula Atom}
    (_h_γ : γ ∈ A)
    (h_Hγ : Formula.allPast γ ∈ A)
    (h_neg_since : (Formula.snce δ γ).neg ∈ A) :
    Formula.allPast δ.neg ∈ A := by
  set top := Formula.bot.imp (Formula.bot : Formula Atom) with htop_def
  -- H(top -> gamma) in A by past necessitation of prop_s + H distribution
  have h_H_top_gamma : Formula.allPast (top.imp γ) ∈ A := by
    have h_H_ps := theorem_in_mcs_fc h_mcs
      (Cslib.Logic.Bimodal.Theorems.past_necessitation _
        (DerivationTree.axiom [] _ (Axiom.imp_s γ top) trivial))
    have h_dist := theorem_in_mcs_fc h_mcs
      (Cslib.Logic.Bimodal.Theorems.past_k_dist γ (top.imp γ))
    exact SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h_dist h_H_ps) h_Hγ
  -- BX2H: H(top -> gamma) -> (delta S top -> delta S gamma)
  have h_ax := theorem_in_mcs_fc h_mcs
    (DerivationTree.axiom [] _ (Axiom.left_mono_since_H top γ δ) trivial)
  have h_mono : (Formula.snce δ top).imp (Formula.snce δ γ) ∈ A :=
    SetMaximalConsistent.implication_property h_mcs h_ax h_H_top_gamma
  have h_neg_top_since := mcs_contrapositive_mem fc h_mcs h_mono h_neg_since
  have h_bx12' := theorem_in_mcs_fc h_mcs
    (DerivationTree.axiom [] _ (Axiom.P_since_equiv δ) trivial)
  have h_neg_P := mcs_contrapositive_mem fc h_mcs h_bx12' h_neg_top_since
  -- ¬P(δ) → H(¬δ) via duality conversion
  exact neg_somePast_to_allPast_neg h_mcs δ h_neg_P

/-! ## BurgessR3Maximal Existence and Properties

BurgessR3Maximal (defined in ChronicleTypes.lean) is the CORRECT maximality notion
for the chronicle construction. Key difference from R3Maximal: burgessR3 is
ANTI-monotone in B, so maximality is genuine (not collapsing to MCS via monotonicity).
-/

/--
The set of DCS extending S that satisfy burgessR3(A, -, C).
Used for the Zorn's lemma argument in BurgessR3Maximal existence.
-/
def burgessR3DCSExtensions (fc : FrameClass) (A Sig C : Set (Formula Atom)) : Set (Set (Formula Atom)) :=
  {B | Sig ⊆ B ∧ ClosedUnderDerivation fc B ∧ burgessR3 A B C}

/--
**Helper**: An inconsistent `ClosedUnderDerivation` set equals `Set.univ`.
If D is `ClosedUnderDerivation` and not `SetConsistent`, then D = Set.univ.
Proof: ¬SetConsistent gives ∃ L ⊆ D, DerivationTree L ⊥. By closure, ⊥ ∈ D.
Then for any φ, DerivationTree [⊥] φ (ex falso), so φ ∈ D.
-/
theorem closed_under_derivation_inconsistent_eq_univ (fc : FrameClass)
    {D : Set (Formula Atom)} (h_cud : ClosedUnderDerivation fc D) (h_not_cons : ¬SetConsistent fc D) :
    D = Set.univ := by
  -- ¬SetConsistent fc D means ∃ L ⊆ D with Nonempty (DerivationTree fc L ⊥).
  -- Extract the witness by classical contradiction.
  have h_exists : ∃ L : List (Formula Atom), (∀ φ ∈ L, φ ∈ D) ∧ Nonempty (DerivationTree fc L (Formula.bot : Formula Atom)) := by
    by_contra h_all
    apply h_not_cons
    intro L hL hd
    exact h_all ⟨L, hL, hd⟩
  obtain ⟨L, hL, ⟨d⟩⟩ := h_exists
  -- ⊥ ∈ D by closure under derivation
  have h_bot : (Formula.bot : Formula Atom) ∈ D := h_cud L Formula.bot hL d
  -- For any φ, derive φ from ⊥ (ex falso), so φ ∈ D
  ext φ; simp only [Set.mem_univ, iff_true]
  have d_efq : DerivationTree fc [(Formula.bot : Formula Atom)] φ :=
    DerivationTree.modus_ponens [(Formula.bot : Formula Atom)] Formula.bot φ
      (DerivationTree.weakening [] [(Formula.bot : Formula Atom)] ((Formula.bot : Formula Atom).imp φ)
        (Cslib.Logic.Bimodal.Theorems.Propositional.efq_axiom φ) (List.nil_subset _))
      (DerivationTree.assumption [(Formula.bot : Formula Atom)] Formula.bot (by simp))
  exact h_cud [(Formula.bot : Formula Atom)] φ (fun ψ hψ => by simp at hψ; rw [hψ]; exact h_bot) d_efq

/--
**BurgessR3Maximal existence**: Given MCS A, C and a CUD set S with burgessR3(A, S, C),
there exists a BurgessR3Maximal B with Sig ⊆ B.

Proof: Zorn's lemma on the set of CUD extensions of S satisfying burgessR3.
Chain unions preserve CUD and burgessR3. Zorn gives maximality over
`ClosedUnderDerivation` sets directly, matching Burgess 1982 exactly.
No `NoUnivBurgessR3` hypothesis needed: the Zorn family already uses CUD,
so the maximal element is CUD-maximal by construction.
-/
theorem burgessR3Maximal_extension_exists (fc : FrameClass) {A C : Set (Formula Atom)}
    (_h_mcs_A : SetMaximalConsistent fc A) (_h_mcs_C : SetMaximalConsistent fc C)
    {Sig : Set (Formula Atom)} (h_cud : ClosedUnderDerivation fc Sig) (h_r3 : burgessR3 A Sig C) :
    ∃ B : Set (Formula Atom), Sig ⊆ B ∧ ClosedUnderDerivation fc B ∧ BurgessR3Maximal fc A B C := by
  have h_S_in : Sig ∈ burgessR3DCSExtensions fc A Sig C := ⟨Set.Subset.refl _, h_cud, h_r3⟩
  obtain ⟨B, hB_in, hB_max⟩ := zorn_subset (burgessR3DCSExtensions fc A Sig C) (by
    intro c hc_sub hc_chain
    by_cases hc_empty : c = ∅
    · exact ⟨Sig, h_S_in, by intro t ht; exact absurd ht (by rw [hc_empty]; exact Set.notMem_empty _)⟩
    · obtain ⟨T₀, hT₀⟩ := Set.nonempty_iff_ne_empty.mpr hc_empty
      refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
      refine ⟨Set.subset_sUnion_of_subset c T₀ (hc_sub hT₀).1 hT₀, ?_, ?_⟩
      · -- ⋃₀ c is CUD: closure under derivation is preserved by unions
        intro L φ hL d
        obtain ⟨T, hTc, hLT⟩ := rMaximal_extension_exists.chain_finite_subset_in_element
          hc_chain hT₀ L (fun ψ hψ => hL ψ hψ)
        exact Set.mem_sUnion.mpr ⟨T, hTc, (hc_sub hTc).2.1 L φ hLT d⟩
      · -- burgessR3(A, ⋃₀ c, C)
        constructor
        · -- burgessRSet(A, ⋃₀ c, C): for beta in union, beta in some T_i
          intro β hβ
          obtain ⟨T, hTc, hβT⟩ := Set.mem_sUnion.mp hβ
          exact (hc_sub hTc).2.2.1 β hβT
        · -- burgessRSetSince(C, ⋃₀ c, A): same argument
          intro β hβ
          obtain ⟨T, hTc, hβT⟩ := Set.mem_sUnion.mp hβ
          exact (hc_sub hTc).2.2.2 β hβT)
  obtain ⟨hSB, hB_cud, hB_r3⟩ := hB_in
  exact ⟨B, hSB, hB_cud, hB_cud, hB_r3, fun D hD_cud hBD hD_r3 =>
    hBD.2 (hB_max ⟨Set.Subset.trans hSB hBD.1, hD_cud, hD_r3⟩ hBD.1)⟩

/-! ## BurgessR3Maximal Accessor Lemmas -/

/--
**BurgessR3Maximal implies CUD** (trivial from definition).
-/
theorem BurgessR3Maximal_cud (fc : FrameClass) {A B C : Set (Formula Atom)} (h : BurgessR3Maximal fc A B C) :
    ClosedUnderDerivation fc B := h.1

/--
**BurgessR3Maximal implies burgessR3** (trivial from definition).
-/
theorem BurgessR3Maximal_burgessR3 (fc : FrameClass) {A B C : Set (Formula Atom)} (h : BurgessR3Maximal fc A B C) :
    burgessR3 A B C := h.2.1

/--
**BurgessR3Maximal implies burgessRSet** (forward Until direction).
-/
theorem BurgessR3Maximal_burgessRSet (fc : FrameClass) {A B C : Set (Formula Atom)} (h : BurgessR3Maximal fc A B C) :
    burgessRSet A B C := h.2.1.1

/--
**BurgessR3Maximal implies burgessRSetSince** (backward Since direction).
-/
theorem BurgessR3Maximal_burgessRSetSince (fc : FrameClass) {A B C : Set (Formula Atom)} (h : BurgessR3Maximal fc A B C) :
    burgessRSetSince C B A := h.2.1.2

/-! ## BurgessR3 Bridging Lemmas for C4

These are the KEY lemmas for closing the C4 hard case. They use the content-based
nature of burgessR3 to derive gamma ∉ g(x,y) from neg(untl(gamma, delta)) ∈ f(x)
and delta ∈ f(y).
-/

/--
**BurgessR3 bridging lemma (Until direction)**:
If burgessR3(A, B, C) and gamma ∈ B and delta ∈ C, then untl(gamma, delta) ∈ A.

This is IMMEDIATE from the definition of burgessRSet: for all beta ∈ B,
for all gamma ∈ C, untl(beta, gamma) ∈ A.

Note: In this lemma, the first argument to burgessR3 is A (left endpoint),
B is the interval set, C is the right endpoint.
-/
theorem burgessR3_untl_in {A B C : Set (Formula Atom)}
    (h : burgessR3 A B C) {β : Formula Atom} (hβ : β ∈ B) {γ : Formula Atom} (hγ : γ ∈ C) :
    Formula.untl γ β ∈ A :=
  h.1 β hβ γ hγ

/--
**BurgessR3 bridging lemma (Since direction)**:
If burgessR3(A, B, C) and beta ∈ B and gamma ∈ A, then snce(beta, gamma) ∈ C.
-/
theorem burgessR3_snce_in {A B C : Set (Formula Atom)}
    (h : burgessR3 A B C) {β : Formula Atom} (hβ : β ∈ B) {γ : Formula Atom} (hγ : γ ∈ A) :
    Formula.snce γ β ∈ C :=
  h.2 β hβ γ hγ

/--
**C4 hard case bridging**: If BurgessR3Maximal(A, B, C) and untl(gamma, delta).neg ∈ A
and delta ∈ C, then gamma ∉ B.

Proof: Suppose gamma ∈ B. By burgessR3, untl(gamma, delta) ∈ A. But A is a DCS
(actually an MCS endpoint), so untl(gamma, delta) and untl(gamma, delta).neg cannot
both be in A. Contradiction.

This is THE key lemma for the C4 hard case: it shows gamma ∉ g(x,y), from which
gamma.neg ∈ g(x,y) (by negation completeness of MCS), and then C3 gives
gamma.neg ∈ f(z) for intermediate z.
-/
theorem burgessR3_gamma_not_in_B (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_r3 : burgessR3 A B C)
    {γ δ : Formula Atom}
    (h_neg_until : (Formula.untl δ γ).neg ∈ A)
    (h_delta : δ ∈ C) :
    γ ∉ B := by
  intro h_gamma
  have h_until := h_r3.1 γ h_gamma δ h_delta
  exact set_consistent_not_both h_mcs_A.1 (Formula.untl δ γ) h_until h_neg_until

/--
**C4' hard case bridging (Since direction)**: If BurgessR3Maximal(A, B, C) and
snce(gamma, delta).neg ∈ C and delta ∈ A, then gamma ∉ B.
-/
theorem burgessR3_gamma_not_in_B_since (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3 : burgessR3 A B C)
    {γ δ : Formula Atom}
    (h_neg_since : (Formula.snce δ γ).neg ∈ C)
    (h_delta : δ ∈ A) :
    γ ∉ B := by
  intro h_gamma
  have h_since := h_r3.2 γ h_gamma δ h_delta
  exact set_consistent_not_both h_mcs_C.1 (Formula.snce δ γ) h_since h_neg_since

/-! ## DCS Non-Membership Implies Negation Consistency

Key lemma for the C4 hard case: if gamma ∉ B and B is DCS, then
{gamma.neg} ∪ B is consistent. This allows Lindenbaum extension to an MCS
containing gamma.neg.
-/

/--
If phi ∉ B and B is DCS, then {phi.neg} ∪ B is consistent.

Proof: Suppose not. Then some L ⊆ {phi.neg} ∪ B derives ⊥.
By weakening, (phi.neg :: L') ⊢ ⊥ where L' ⊆ B.
By deduction theorem, L' ⊢ phi.neg → ⊥ = phi.
Since B is DCS and L' ⊆ B, phi ∈ B. Contradiction.
-/
theorem dcs_neg_insert_consistent (fc : FrameClass) {B : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc B)
    {φ : Formula Atom} (h_not_in : φ ∉ B) :
    SetConsistent fc (insert φ.neg B) := by
  intro L hL ⟨d⟩
  -- Strategy: filter L to B-only premises, weaken d, use deduction theorem + DNE.
  haveI : ∀ ψ : Formula Atom, Decidable (ψ ∈ B) := fun ψ => Classical.propDecidable _
  let L_B := L.filter (· ∈ B)
  have h_L_sub : L ⊆ φ.neg :: L_B := by
    intro ψ hψ
    have h := hL ψ hψ
    simp only [Set.mem_insert_iff] at h
    rcases h with rfl | h_B
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hψ, by exact decide_eq_true_eq.mpr h_B⟩)
  -- Weaken d to (φ.neg :: L_B) ⊢ ⊥
  have d_w : DerivationTree fc (φ.neg :: L_B) (Formula.bot : Formula Atom) :=
    DerivationTree.weakening L (φ.neg :: L_B) Formula.bot d h_L_sub
  -- Deduction theorem: L_B ⊢ ¬¬φ
  have d_nn : DerivationTree fc L_B (φ.neg.imp (Formula.bot : Formula Atom)) :=
    deduction_theorem L_B φ.neg Formula.bot d_w
  -- L_B ⊆ B
  have h_LB_sub : ∀ ψ ∈ L_B, ψ ∈ B := by
    intro ψ hψ
    exact decide_eq_true_eq.mp (List.mem_filter.mp hψ).2
  -- ¬¬φ ∈ B by DCS
  have h_nn_B : φ.neg.imp (Formula.bot : Formula Atom) ∈ B := h_dcs.2 L_B _ h_LB_sub d_nn
  -- DNE theorem in B: (¬¬φ → φ) ∈ B
  have h_dne_B : φ.neg.neg.imp φ ∈ B :=
    dcs_contains_theorems h_dcs (Cslib.Logic.Bimodal.Theorems.Propositional.double_negation φ)
  -- Modus ponens in B: φ ∈ B
  have h_phi_B : φ ∈ B := dcs_modus_ponens h_dcs h_dne_B h_nn_B
  exact h_not_in h_phi_B

/-! ## BurgessR3 Guard Algebra

Key algebraic lemmas for the burgessR3 relation, showing that:
1. If untl(β₁, γ) and untl(β₂, γ) are in MCS A, then untl(β₁∧β₂, γ) is in A.
2. If ⊢ β₁ → β₂ and untl(β₁, γ) ∈ A, then untl(β₂, γ) ∈ A.

These are the building blocks for proving that deductive closure preserves burgessR3,
which is needed for the seed construction in BurgessR3Maximal existence.
Uses BX7 (linear_until), BX2G (left_mono_until_G), and BX3 (right_mono_until).
-/

/--
**Guard conjunction for Until**: If untl(β₁, γ) ∈ A and untl(β₂, γ) ∈ A (MCS A),
then untl(β₁∧β₂, γ) ∈ A.

Proof uses BX7 (linear_until) applied to the same event γ:
(β₁ U γ) ∧ (β₂ U γ) → D1 ∨ D2 ∨ D3 where each Dᵢ = (β₁∧β₂) U eᵢ
and each eᵢ → γ is a theorem. Then BX3 (right_mono_until) converts to (β₁∧β₂) U γ.
-/
theorem untl_conj_guard (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (h1 : Formula.untl γ β₁ ∈ A)
    (h2 : Formula.untl γ β₂ ∈ A) :
    Formula.untl γ (Formula.and β₁ β₂) ∈ A := by
  have h_conj : Formula.and (Formula.untl γ β₁) (Formula.untl γ β₂) ∈ A :=
    dcs_conj_closed (mcs_is_dcs h_mcs) h1 h2
  have h_bx7 := theorem_in_mcs_fc h_mcs
    (DerivationTree.axiom [] _ (Axiom.linear_until β₁ γ β₂ γ) trivial)
  have h_disj := SetMaximalConsistent.implication_property h_mcs h_bx7 h_conj
  set guard := Formula.and β₁ β₂
  set D1 := Formula.untl (Formula.and γ γ) guard
  set D2 := Formula.untl (Formula.and γ β₂) guard
  set D3 := Formula.untl (Formula.and β₁ γ) guard
  set target := Formula.untl γ guard
  -- Helper: if ⊢ (e → γ) then ⊢ (guard U e → guard U γ)
  have mk_thm : ∀ e : Formula Atom, DerivationTree fc [] (e.imp γ) →
      DerivationTree fc [] ((Formula.untl e guard).imp target) := by
    intro e h_e_imp
    have h_G := DerivationTree.temporal_necessitation _ h_e_imp
    have h_bx3 := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until e γ guard) trivial
    exact DerivationTree.modus_ponens [] _ _ h_bx3 h_G
  have h_D1_impl := theorem_in_mcs_fc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.lce_imp γ γ))
  have h_D2_impl := theorem_in_mcs_fc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.lce_imp γ β₂))
  have h_D3_impl := theorem_in_mcs_fc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp β₁ γ))
  rcases SetMaximalConsistent.negation_complete h_mcs D3 with h | h
  · exact SetMaximalConsistent.implication_property h_mcs h_D3_impl h
  · have h_D1_or_D2 : Formula.or D1 D2 ∈ A := by
      rcases SetMaximalConsistent.negation_complete h_mcs (Formula.or D1 D2) with h' | h'
      · exact h'
      · have := SetMaximalConsistent.implication_property h_mcs h_disj h'
        exact absurd this (SetMaximalConsistent.neg_excludes h_mcs _ h)
    rcases SetMaximalConsistent.negation_complete h_mcs D1 with h' | h'
    · exact SetMaximalConsistent.implication_property h_mcs h_D1_impl h'
    · have h_D2 := SetMaximalConsistent.implication_property h_mcs h_D1_or_D2 h'
      exact SetMaximalConsistent.implication_property h_mcs h_D2_impl h_D2

/--
**Guard conjunction for Since** (mirror of `untl_conj_guard`):
If snce(β₁, γ) ∈ A and snce(β₂, γ) ∈ A (MCS A), then snce(β₁∧β₂, γ) ∈ A.
Uses BX7' (linear_since), BX3' (right_mono_since).
-/
theorem snce_conj_guard (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (h1 : Formula.snce γ β₁ ∈ A)
    (h2 : Formula.snce γ β₂ ∈ A) :
    Formula.snce γ (Formula.and β₁ β₂) ∈ A := by
  have h_conj : Formula.and (Formula.snce γ β₁) (Formula.snce γ β₂) ∈ A :=
    dcs_conj_closed (mcs_is_dcs h_mcs) h1 h2
  have h_bx7' := theorem_in_mcs_fc h_mcs
    (DerivationTree.axiom [] _ (Axiom.linear_since β₁ γ β₂ γ) trivial)
  have h_disj := SetMaximalConsistent.implication_property h_mcs h_bx7' h_conj
  set guard := Formula.and β₁ β₂
  set D1 := Formula.snce (Formula.and γ γ) guard
  set D2 := Formula.snce (Formula.and γ β₂) guard
  set D3 := Formula.snce (Formula.and β₁ γ) guard
  set target := Formula.snce γ guard
  have mk_thm : ∀ e : Formula Atom, DerivationTree fc [] (e.imp γ) →
      DerivationTree fc [] ((Formula.snce e guard).imp target) := by
    intro e h_e_imp
    have h_H := Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_e_imp
    have h_bx3' := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since e γ guard) trivial
    exact DerivationTree.modus_ponens [] _ _ h_bx3' h_H
  have h_D1_impl := theorem_in_mcs_fc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.lce_imp γ γ))
  have h_D2_impl := theorem_in_mcs_fc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.lce_imp γ β₂))
  have h_D3_impl := theorem_in_mcs_fc h_mcs
    (mk_thm _ (Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp β₁ γ))
  rcases SetMaximalConsistent.negation_complete h_mcs D3 with h | h
  · exact SetMaximalConsistent.implication_property h_mcs h_D3_impl h
  · have h_D1_or_D2 : Formula.or D1 D2 ∈ A := by
      rcases SetMaximalConsistent.negation_complete h_mcs (Formula.or D1 D2) with h' | h'
      · exact h'
      · have := SetMaximalConsistent.implication_property h_mcs h_disj h'
        exact absurd this (SetMaximalConsistent.neg_excludes h_mcs _ h)
    rcases SetMaximalConsistent.negation_complete h_mcs D1 with h' | h'
    · exact SetMaximalConsistent.implication_property h_mcs h_D1_impl h'
    · have h_D2 := SetMaximalConsistent.implication_property h_mcs h_D1_or_D2 h'
      exact SetMaximalConsistent.implication_property h_mcs h_D2_impl h_D2

/--
**Set-level guard conjunction for Until (burgessR)**: If `burgessR(A, α, C)` and
`burgessR(A, β, C)`, then `burgessR(A, α∧β, C)`.

Lifts `untl_conj_guard` pointwise: for every γ ∈ C, `untl(α, γ) ∈ A` and
`untl(β, γ) ∈ A` imply `untl(α∧β, γ) ∈ A`.
-/
theorem burgessR_conj (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {α β : Formula Atom}
    (hα : burgessR A α C) (hβ : burgessR A β C) :
    burgessR A (Formula.and α β) C := by
  intro γ hγ
  exact untl_conj_guard fc h_mcs (hα γ hγ) (hβ γ hγ)

/--
**Set-level guard conjunction for Since (burgessRSince)**: If `burgessRSince(C, α, A)` and
`burgessRSince(C, β, A)`, then `burgessRSince(C, α∧β, A)`.

Lifts `snce_conj_guard` pointwise: for every γ ∈ A, `snce(α, γ) ∈ C` and
`snce(β, γ) ∈ C` imply `snce(α∧β, γ) ∈ C`.
-/
theorem burgessRSince_conj (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc C)
    {α β : Formula Atom}
    (hα : burgessRSince C α A) (hβ : burgessRSince C β A) :
    burgessRSince C (Formula.and α β) A := by
  intro γ hγ
  exact snce_conj_guard fc h_mcs (hα γ hγ) (hβ γ hγ)

/--
**Left monotonicity for Until via G**: If G(β₁ → β₂) ∈ A and untl(β₁, γ) ∈ A,
then untl(β₂, γ) ∈ A. Uses BX2G (left_mono_until_G).
Unlike `untl_left_mono_thm`, does NOT require the pointwise (β₁ → β₂) at A.
-/
theorem untl_left_mono_G (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (h_G_impl : (β₁.imp β₂).allFuture ∈ A)
    (h_untl : Formula.untl γ β₁ ∈ A) :
    Formula.untl γ β₂ ∈ A := by
  have h_ax := theorem_in_mcs_fc h_mcs
    (DerivationTree.axiom [] _ (Axiom.left_mono_until_G β₁ β₂ γ) trivial)
  have h_step := SetMaximalConsistent.implication_property h_mcs h_ax h_G_impl
  exact SetMaximalConsistent.implication_property h_mcs h_step h_untl

/--
**Left monotonicity for Since via H**: If H(β₁ → β₂) ∈ A and snce(β₁, γ) ∈ A,
then snce(β₂, γ) ∈ A. Uses BX2H (left_mono_since_H).
-/
theorem snce_left_mono_H (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (h_H_impl : (β₁.imp β₂).allPast ∈ A)
    (h_snce : Formula.snce γ β₁ ∈ A) :
    Formula.snce γ β₂ ∈ A := by
  have h_ax := theorem_in_mcs_fc h_mcs
    (DerivationTree.axiom [] _ (Axiom.left_mono_since_H β₁ β₂ γ) trivial)
  have h_step := SetMaximalConsistent.implication_property h_mcs h_ax h_H_impl
  exact SetMaximalConsistent.implication_property h_mcs h_step h_snce

/--
**Left monotonicity for Until via theorem**: If ⊢ β₁ → β₂ and untl(β₁, γ) ∈ A,
then untl(β₂, γ) ∈ A. Uses BX2G (left_mono_until_G) via temporal necessitation.
-/
theorem untl_left_mono_thm (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (h_impl : DerivationTree fc [] (β₁.imp β₂))
    (h_untl : Formula.untl γ β₁ ∈ A) :
    Formula.untl γ β₂ ∈ A := by
  have h_G := theorem_in_mcs_fc h_mcs (DerivationTree.temporal_necessitation _ h_impl)
  exact untl_left_mono_G fc h_mcs h_G h_untl

/--
**Left monotonicity for Since via theorem** (mirror): If ⊢ β₁ → β₂ and snce(β₁, γ) ∈ A,
then snce(β₂, γ) ∈ A. Uses BX2H (left_mono_since_H) via past necessitation.
-/
theorem snce_left_mono_thm (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A)
    {β₁ β₂ γ : Formula Atom}
    (h_impl : DerivationTree fc [] (β₁.imp β₂))
    (h_snce : Formula.snce γ β₁ ∈ A) :
    Formula.snce γ β₂ ∈ A := by
  have h_H := theorem_in_mcs_fc h_mcs (Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_impl)
  exact snce_left_mono_H fc h_mcs h_H h_snce

/-! ## Helper: Derivation from Singleton Set Implies Implication Theorem

If φ ∈ deductiveClosure({η}), then ⊢ η → φ. This is the key link between
deductive closure membership and the deduction theorem.
-/

/--
If L consists entirely of copies of η and L ⊢ φ, then [η] ⊢ φ.
By weakening from L to [η] (since every element of L is η).
-/
noncomputable def derivation_from_singleton_list (fc : FrameClass) {η φ : Formula Atom} {L : List (Formula Atom)}
    (hL : ∀ ψ ∈ L, ψ = η) (d : DerivationTree fc L φ) :
    DerivationTree fc [η] φ :=
  DerivationTree.weakening L [η] φ d (fun ψ hψ => by rw [hL ψ hψ]; simp)

/--
If φ ∈ deductiveClosure({η}), then there exists a derivation ⊢ η → φ.
This follows from: φ ∈ DC({η}) means ∃ L ⊆ {η}, L ⊢ φ, hence [η] ⊢ φ
by weakening, hence ⊢ η → φ by the deduction theorem.
-/
theorem deductiveClosure_singleton_imp (fc : FrameClass) {η φ : Formula Atom}
    (hφ : φ ∈ deductiveClosure fc ({η} : Set (Formula Atom))) :
    Nonempty (DerivationTree fc [] (η.imp φ)) := by
  obtain ⟨L, hL_sub, ⟨d⟩⟩ := hφ
  have hL_eq : ∀ ψ ∈ L, ψ = η := fun ψ hψ => Set.mem_singleton_iff.mp (hL_sub ψ hψ)
  exact ⟨deduction_theorem [] η φ (derivation_from_singleton_list fc hL_eq d)⟩

/--
**burgessR propagation through deductive closure**: If burgessR(A, η, C) and
φ ∈ deductiveClosure({η}), then burgessR(A, φ, C).

Proof: φ ∈ DC({η}) gives ⊢ η → φ. By untl_left_mono_thm (BX2), for any
γ ∈ C: untl(η, γ) ∈ A implies untl(φ, γ) ∈ A.
-/
theorem burgessR_of_deductiveClosure_singleton (fc : FrameClass) {A C : Set (Formula Atom)} {η : Formula Atom}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_burgessR : burgessR A η C) (φ : Formula Atom)
    (hφ : φ ∈ deductiveClosure fc ({η} : Set (Formula Atom))) :
    burgessR A φ C := by
  obtain ⟨d⟩ := deductiveClosure_singleton_imp fc hφ
  intro γ hγ
  exact untl_left_mono_thm fc h_mcs_A d (h_burgessR γ hγ)

/--
**burgessRSince propagation through deductive closure**: Mirror of
`burgessR_of_deductiveClosure_singleton` for the Since direction.
-/
theorem burgessRSince_of_deductiveClosure_singleton (fc : FrameClass) {A C : Set (Formula Atom)} {η : Formula Atom}
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_burgessRSince : burgessRSince C η A) (φ : Formula Atom)
    (hφ : φ ∈ deductiveClosure fc ({η} : Set (Formula Atom))) :
    burgessRSince C φ A := by
  obtain ⟨d⟩ := deductiveClosure_singleton_imp fc hφ
  intro γ hγ
  exact snce_left_mono_thm fc h_mcs_C d (h_burgessRSince γ hγ)

/-! ## BurgessR3Maximal Existence from Seed -/

/--
**BurgessR3Maximal existence from seed**: Given an element η satisfying both
burgessR(A, η, C) and burgessRSince(C, η, A), and η ∈ A, there exists B with
BurgessR3Maximal(A, B, C).

This is the CORRECT existence theorem for the chronicle construction. Rather
than constructing a seed from scratch (which fails under strict semantics),
it takes an explicit seed element η that arises from context:
- In C5 elimination: η comes from Lemma 2.4 (the Until guard)
- In C4 splitting: no new seed needed (burgessR3_absorption)

Under open guard semantics, η ∈ A cannot be derived from burgessR(A, η, C)
alone (until_guard axiom removed, task 113). Callers must provide η ∈ A
directly from their proof context.

Proof:
1. η ∈ A (provided by caller)
2. {η} is consistent (subset of A)
3. deductiveClosure({η}) is a DCS
4. deductiveClosure({η}) satisfies burgessR3(A, -, C):
   For any φ ∈ DC({η}), ⊢ η → φ, so by BX2 (untl_left_mono_thm),
   burgessR(A, η, C) gives burgessR(A, φ, C). Similarly for Since.
5. Apply burgessR3Maximal_extension_exists with this seed
-/
theorem burgessR3Maximal_exists_from_seed (fc : FrameClass) (A C : Set (Formula Atom)) (η : Formula Atom)
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_burgessR : burgessR A η C)
    (h_burgessRSince : burgessRSince C η A)
    (_h_η_A : η ∈ A) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal fc A B C := by
  -- deductiveClosure({η}) is CUD (always true, no consistency needed)
  have h_dc_cud : ClosedUnderDerivation fc (deductiveClosure fc ({η} : Set (Formula Atom))) :=
    deductiveClosure_closed_under_derivation fc _
  -- deductiveClosure({η}) satisfies burgessR3(A, -, C)
  have h_dc_r3 : burgessR3 A (deductiveClosure fc ({η} : Set (Formula Atom))) C := by
    constructor
    · intro φ hφ
      exact burgessR_of_deductiveClosure_singleton fc h_mcs_A h_burgessR φ hφ
    · intro φ hφ
      exact burgessRSince_of_deductiveClosure_singleton fc h_mcs_C h_burgessRSince φ hφ
  -- Apply Zorn extension
  obtain ⟨B, _, _, h_B3M⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_mcs_C h_dc_cud h_dc_r3
  exact ⟨B, h_B3M⟩

/-! ## Burgess Lemma 2.3 Equivalence

The element-wise equivalence between burgessR and burgessRSince:
  burgessR(A, β, C) ↔ burgessRSince(C, β, A)

for MCS A, C. This uses BX4/BX4' (connect_future/past) and BX2/BX3
(left/right monotonicity). The equivalence shows that the forward (Until)
and backward (Since) directions of the content-based r-relation are
interchangeable, which is essential for the maximality argument in
Xu's Lemma 3.2.1.
-/

/-! ### Duality helpers for Burgess Lemma 2.3

Since `someFuture`/`somePast` are no longer definitionally `neg(allFuture/allPast(neg _))`,
we need proof-theoretic bridges for the structural identities used in the Burgess lemma. -/

/-- In an MCS, `neg (allPast (neg α)) ∈ M` implies `somePast α ∈ M`.
    Derives `P(α)` from `¬H(¬α)` via BX3' (right_mono_since) + DNE. -/
theorem neg_allPast_neg_to_somePast (fc : FrameClass) {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (α : Formula Atom)
    (h : Formula.neg (Formula.allPast (Formula.neg α)) ∈ M) :
    Formula.somePast α ∈ M := by
  -- ¬H(¬α) = (somePast α.neg.neg).neg.neg (by def of allPast)
  -- DNE: (somePast α.neg.neg).neg.neg → somePast α.neg.neg = P(¬¬α)
  have h_dne_P : Formula.somePast (α.neg.neg) ∈ M := by
    have h_dne : DerivationTree fc [] ((Formula.somePast α.neg.neg).neg.neg.imp (Formula.somePast α.neg.neg)) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.double_negation (Formula.somePast α.neg.neg)
    exact SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs_fc h_mcs h_dne) h
  -- BX3' (right_mono_since): ⊢ H(¬¬α → α) → (P(¬¬α) → P(α))
  -- Build chain at Base level, then lift
  have h_dne_ax : DerivationTree fc [] (α.neg.neg.imp α) := Cslib.Logic.Bimodal.Theorems.Propositional.double_negation α
  have h_H_dne : DerivationTree fc [] ((α.neg.neg.imp α).allPast) :=
    Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_dne_ax
  have h_bx3' : DerivationTree fc [] ((α.neg.neg.imp α).allPast.imp
      ((Formula.snce α.neg.neg Formula.top).imp (Formula.snce α Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_since α.neg.neg α Formula.top) trivial
  have h_P_mono : DerivationTree fc [] ((Formula.somePast α.neg.neg).imp (Formula.somePast α)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3' h_H_dne
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs_fc h_mcs h_P_mono) h_dne_P

/-- In an MCS, `neg (allFuture (neg γ)) ∈ M` implies `someFuture γ ∈ M`.
    Derives `F(γ)` from `¬G(¬γ)` via BX3 (right_mono_until) + DNE. -/
theorem neg_allFuture_neg_to_someFuture (fc : FrameClass) {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (γ : Formula Atom)
    (h : Formula.neg (Formula.allFuture (Formula.neg γ)) ∈ M) :
    Formula.someFuture γ ∈ M := by
  have h_dne_F : Formula.someFuture (γ.neg.neg) ∈ M := by
    have h_dne : DerivationTree fc [] ((Formula.someFuture γ.neg.neg).neg.neg.imp (Formula.someFuture γ.neg.neg)) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.double_negation (Formula.someFuture γ.neg.neg)
    exact SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs_fc h_mcs h_dne) h
  have h_dne_ax : DerivationTree fc [] (γ.neg.neg.imp γ) := Cslib.Logic.Bimodal.Theorems.Propositional.double_negation γ
  have h_G_dne : DerivationTree fc [] ((γ.neg.neg.imp γ).allFuture) :=
    DerivationTree.temporal_necessitation _ h_dne_ax
  have h_bx3 : DerivationTree fc [] ((γ.neg.neg.imp γ).allFuture.imp
      ((Formula.untl γ.neg.neg Formula.top).imp (Formula.untl γ Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_until γ.neg.neg γ Formula.top) trivial
  have h_F_mono : DerivationTree fc [] ((Formula.someFuture γ.neg.neg).imp (Formula.someFuture γ)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dne
  exact SetMaximalConsistent.implication_property h_mcs
    (theorem_in_mcs_fc h_mcs h_F_mono) h_dne_F

/-- F(H(¬α)) ∈ M and G(P(α)) ∈ M are contradictory in an MCS.
    Derives `G(¬H(¬α))` from `G(P(α))` via `⊢ P(α) → ¬H(¬α)`. -/
theorem someFuture_H_neg_G_P_absurd (fc : FrameClass) {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (α : Formula Atom)
    (h_F : Formula.someFuture (Formula.allPast (Formula.neg α)) ∈ M)
    (h_GP : Formula.allFuture (Formula.somePast α) ∈ M) : False := by
  -- ⊢ P(α) → ¬H(¬α): from P(α) → P(¬¬α) and DNI
  have h_dni_ax : DerivationTree fc [] (α.imp α.neg.neg) := dni α
  have h_H_dni : DerivationTree fc [] ((α.imp α.neg.neg).allPast) :=
    Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_dni_ax
  have h_bx3' : DerivationTree fc [] ((α.imp α.neg.neg).allPast.imp
      ((Formula.snce α Formula.top).imp (Formula.snce α.neg.neg Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_since α α.neg.neg Formula.top) trivial
  have h_P_to_Pnn : DerivationTree fc [] ((Formula.somePast α).imp (Formula.somePast α.neg.neg)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3' h_H_dni
  -- P(¬¬α) → P(¬¬α).neg.neg = ¬H(¬α) by DNI
  have h_dni_P : DerivationTree fc [] ((Formula.somePast α.neg.neg).imp (Formula.somePast α.neg.neg).neg.neg) :=
    dni (Formula.somePast α.neg.neg)
  -- Compose: P(α) → ¬H(¬α)
  have h_P_to_neg_H : DerivationTree fc [] ((Formula.somePast α).imp (Formula.neg (Formula.allPast (Formula.neg α)))) :=
    imp_trans h_P_to_Pnn h_dni_P
  -- G(P(α) → ¬H(¬α)) by temporal necessitation
  have h_G_imp : DerivationTree fc [] (Formula.allFuture ((Formula.somePast α).imp (Formula.neg (Formula.allPast (Formula.neg α))))) :=
    DerivationTree.temporal_necessitation _ h_P_to_neg_H
  -- G(P(α)) → G(¬H(¬α)) by temp_k_dist
  have h_kd : DerivationTree fc [] (((Formula.somePast α).imp (Formula.neg (Formula.allPast (Formula.neg α)))).allFuture.imp
      ((Formula.somePast α).allFuture.imp (Formula.neg (Formula.allPast (Formula.neg α))).allFuture)) :=
    liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.temp_k_dist_derived (Atom := Atom) (Formula.somePast α) (Formula.neg (Formula.allPast (Formula.neg α))))
  have h_G_P_imp_G_neg_H : DerivationTree fc [] ((Formula.somePast α).allFuture.imp
      (Formula.neg (Formula.allPast (Formula.neg α))).allFuture) :=
    DerivationTree.modus_ponens [] _ _ h_kd h_G_imp
  have h_G_neg_H : (Formula.neg (Formula.allPast (Formula.neg α))).allFuture ∈ M :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs_fc h_mcs h_G_P_imp_G_neg_H) h_GP
  exact someFuture_allFuture_neg_absurd h_mcs (Formula.allPast (Formula.neg α)) h_F h_G_neg_H

/-- P(G(¬γ)) ∈ M and H(F(γ)) ∈ M are contradictory in an MCS.
    Derives `H(¬G(¬γ))` from `H(F(γ))` via `⊢ F(γ) → ¬G(¬γ)`. -/
theorem somePast_G_neg_H_F_absurd (fc : FrameClass) {M : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc M) (γ : Formula Atom)
    (h_P : Formula.somePast (Formula.allFuture (Formula.neg γ)) ∈ M)
    (h_HF : Formula.allPast (Formula.someFuture γ) ∈ M) : False := by
  -- ⊢ F(γ) → ¬G(¬γ): from F(γ) → F(¬¬γ) and DNI
  have h_dni_ax : DerivationTree fc [] (γ.imp γ.neg.neg) := dni γ
  have h_G_dni : DerivationTree fc [] ((γ.imp γ.neg.neg).allFuture) :=
    DerivationTree.temporal_necessitation _ h_dni_ax
  have h_bx3 : DerivationTree fc [] ((γ.imp γ.neg.neg).allFuture.imp
      ((Formula.untl γ Formula.top).imp (Formula.untl γ.neg.neg Formula.top))) :=
    DerivationTree.axiom [] _ (Axiom.right_mono_until γ γ.neg.neg Formula.top) trivial
  have h_F_to_Fnn : DerivationTree fc [] ((Formula.someFuture γ).imp (Formula.someFuture γ.neg.neg)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dni
  have h_dni_F : DerivationTree fc [] ((Formula.someFuture γ.neg.neg).imp (Formula.someFuture γ.neg.neg).neg.neg) :=
    dni (Formula.someFuture γ.neg.neg)
  have h_F_to_neg_G : DerivationTree fc [] ((Formula.someFuture γ).imp (Formula.neg (Formula.allFuture (Formula.neg γ)))) :=
    imp_trans h_F_to_Fnn h_dni_F
  -- H(F(γ) → ¬G(¬γ)) by past necessitation
  have h_H_imp : DerivationTree fc [] (Formula.allPast ((Formula.someFuture γ).imp (Formula.neg (Formula.allFuture (Formula.neg γ))))) :=
    Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_F_to_neg_G
  -- H(F(γ)) → H(¬G(¬γ)) by past_k_dist
  have h_kd : DerivationTree fc [] (((Formula.someFuture γ).imp (Formula.neg (Formula.allFuture (Formula.neg γ)))).allPast.imp
      ((Formula.someFuture γ).allPast.imp (Formula.neg (Formula.allFuture (Formula.neg γ))).allPast)) :=
    Cslib.Logic.Bimodal.Theorems.past_k_dist (Formula.someFuture γ) (Formula.neg (Formula.allFuture (Formula.neg γ)))
  have h_H_F_imp_H_neg_G : DerivationTree fc [] ((Formula.someFuture γ).allPast.imp
      (Formula.neg (Formula.allFuture (Formula.neg γ))).allPast) :=
    DerivationTree.modus_ponens [] _ _ h_kd h_H_imp
  have h_H_neg_G : (Formula.neg (Formula.allFuture (Formula.neg γ))).allPast ∈ M :=
    SetMaximalConsistent.implication_property h_mcs
      (theorem_in_mcs_fc h_mcs h_H_F_imp_H_neg_G) h_HF
  exact somePast_allPast_neg_absurd h_mcs (Formula.allFuture (Formula.neg γ)) h_P h_H_neg_G

/--
**Burgess Lemma 2.3 (forward)**: burgessR(A, β, C) implies burgessRSince(C, β, A).

If for all γ ∈ C, untl(β, γ) ∈ A, then for all α ∈ A, snce(β, α) ∈ C.
Uses BX4 (connect_future) and BX3' (right_mono_since).
-/
theorem burgessR_implies_burgessRSince (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    {β : Formula Atom} (h_burgessR : burgessR A β C) :
    burgessRSince C β A := by
  intro α hα
  -- Step 1: Show P(α) ∈ C via BX4 + BX10 contradiction
  have h_P : Formula.somePast α ∈ C := by
    rcases SetMaximalConsistent.negation_complete h_mcs_C (α.neg.allPast) with h_H | h_notH
    · -- H(¬α) ∈ C: derive contradiction
      -- burgessR gives untl(β, H(¬α)) ∈ A
      have h_untl : Formula.untl (α.neg.allPast) β ∈ A := h_burgessR _ h_H
      -- BX10: untl(β, H(¬α)) → F(H(¬α)), so F(H(¬α)) ∈ A
      have h_ax10 := DerivationTree.axiom (fc := fc) [] _ (Axiom.until_F β α.neg.allPast) trivial
      have h_F : Formula.someFuture (α.neg.allPast) ∈ A :=
        SetMaximalConsistent.implication_property h_mcs_A (theorem_in_mcs_fc h_mcs_A h_ax10) h_untl
      -- BX4: α → G(P(α)), so G(P(α)) ∈ A
      have h_bx4 := DerivationTree.axiom (fc := fc) [] _ (Axiom.connect_future α) trivial
      have h_GP : Formula.allFuture (Formula.somePast α) ∈ A :=
        SetMaximalConsistent.implication_property h_mcs_A (theorem_in_mcs_fc h_mcs_A h_bx4) hα
      -- F(H(¬α)) and G(P(α)) are contradictory in MCS A
      exact False.elim (someFuture_H_neg_G_P_absurd fc h_mcs_A α h_F h_GP)
    · -- ¬H(¬α) ∈ C: derive P(α) ∈ C via duality bridge
      exact neg_allPast_neg_to_somePast fc h_mcs_C α h_notH
  -- Step 2: From P(α) ∈ C, derive snce(β, α) ∈ C using enrichment_until (A3a)
  -- By contradiction: if snce(β, α) ∉ C, then ¬snce(β, α) ∈ C
  by_contra h_not
  have h_neg : (Formula.snce α β).neg ∈ C := by
    rcases SetMaximalConsistent.negation_complete h_mcs_C (Formula.snce α β) with h | h
    · exact absurd h h_not
    · exact h
  -- burgessR gives untl(β, ¬snce(β, α)) ∈ A
  have h_untl : Formula.untl (Formula.snce α β).neg β ∈ A := h_burgessR _ h_neg
  -- Form conjunction: α ∧ untl(β, ¬snce(β, α)) ∈ A
  have h_conj : Formula.and α (Formula.untl (Formula.snce α β).neg β) ∈ A :=
    dcs_conj_closed (mcs_is_dcs h_mcs_A) hα h_untl
  -- Apply A3a: α ∧ untl(β, ¬snce(β,α)) → untl(β, ¬snce(β,α) ∧ snce(β,α))
  have h_a3a := DerivationTree.axiom (fc := fc) [] _ (Axiom.enrichment_until β (Formula.snce α β).neg α) trivial
  have h_enriched : Formula.untl ((Formula.snce α β).neg.and (Formula.snce α β)) β ∈ A :=
    SetMaximalConsistent.implication_property h_mcs_A (theorem_in_mcs_fc h_mcs_A h_a3a) h_conj
  -- BX10: untl(β, X) → F(X), so F(¬snce(β,α) ∧ snce(β,α)) ∈ A
  have h_F := until_implies_F_in_mcs fc h_mcs_A h_enriched
  -- ¬snce(β,α) ∧ snce(β,α) → ⊥ is derivable (propositional contradiction)
  have h_neg_event : DerivationTree fc [] ((Formula.snce α β).neg.and (Formula.snce α β)).neg :=
    liftBase fc
      (let h1 := Cslib.Logic.Bimodal.Theorems.Propositional.lce_imp (Formula.snce α β).neg (Formula.snce α β)
       let h2 := Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp (Formula.snce α β).neg (Formula.snce α β)
       let h3 := DerivationTree.axiom (fc := .Base) [] _ (Axiom.imp_k ((Formula.snce α β).neg.and (Formula.snce α β)) (Formula.snce α β) (Formula.bot : Formula Atom)) trivial
       mp h2 (mp h1 h3))
  -- G(¬(¬snce(β,α) ∧ snce(β,α))) ∈ A by temporal necessitation
  have h_G_neg := theorem_in_mcs_fc h_mcs_A (DerivationTree.temporal_necessitation _ h_neg_event)
  -- F(X) and G(¬X) are contradictory in MCS A
  exact someFuture_allFuture_neg_absurd h_mcs_A _ h_F h_G_neg

/--
**Burgess Lemma 2.3 (backward)**: burgessRSince(C, β, A) implies burgessR(A, β, C).

If for all α ∈ A, snce(β, α) ∈ C, then for all γ ∈ C, untl(β, γ) ∈ A.
Uses BX4' (connect_past) and BX3 (right_mono_until).
-/
theorem burgessRSince_implies_burgessR (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    {β : Formula Atom} (h_burgessRSince : burgessRSince C β A) :
    burgessR A β C := by
  intro γ hγ
  -- Mirror of forward direction: show F(γ) ∈ A, then strengthen to untl(β, γ) ∈ A
  -- Step 1: Show F(γ) ∈ A via BX4' + BX10' contradiction
  have h_F : Formula.someFuture γ ∈ A := by
    rcases SetMaximalConsistent.negation_complete h_mcs_A (γ.neg.allFuture) with h_G | h_notG
    · -- G(¬γ) ∈ A: derive contradiction
      -- burgessRSince gives snce(β, G(¬γ)) ∈ C (with G(¬γ) ∈ A)
      have h_snce : Formula.snce (γ.neg.allFuture) β ∈ C := h_burgessRSince _ h_G
      -- BX10': snce(β, G(¬γ)) → P(G(¬γ)), so P(G(¬γ)) ∈ C
      have h_ax10' := DerivationTree.axiom (fc := fc) [] _ (Axiom.since_P β γ.neg.allFuture) trivial
      have h_P : Formula.somePast (γ.neg.allFuture) ∈ C :=
        SetMaximalConsistent.implication_property h_mcs_C (theorem_in_mcs_fc h_mcs_C h_ax10') h_snce
      -- BX4': γ → H(F(γ)), so H(F(γ)) ∈ C
      have h_bx4' := DerivationTree.axiom (fc := fc) [] _ (Axiom.connect_past γ) trivial
      have h_HF : Formula.allPast (Formula.someFuture γ) ∈ C :=
        SetMaximalConsistent.implication_property h_mcs_C (theorem_in_mcs_fc h_mcs_C h_bx4') hγ
      -- P(G(¬γ)) and H(F(γ)) are contradictory in MCS C
      exact False.elim (somePast_G_neg_H_F_absurd fc h_mcs_C γ h_P h_HF)
    · -- ¬G(¬γ) ∈ A: derive F(γ) ∈ A via duality bridge
      exact neg_allFuture_neg_to_someFuture fc h_mcs_A γ h_notG
  -- Step 2: From F(γ) ∈ A, derive untl(β, γ) ∈ A using enrichment_since (A3b)
  -- By contradiction: if untl(β, γ) ∉ A, then ¬untl(β, γ) ∈ A
  by_contra h_not
  have h_neg : (Formula.untl γ β).neg ∈ A := by
    rcases SetMaximalConsistent.negation_complete h_mcs_A (Formula.untl γ β) with h | h
    · exact absurd h h_not
    · exact h
  -- burgessRSince gives snce(β, ¬untl(β, γ)) ∈ C
  have h_snce : Formula.snce (Formula.untl γ β).neg β ∈ C := h_burgessRSince _ h_neg
  -- Form conjunction: γ ∧ snce(β, ¬untl(β, γ)) ∈ C
  have h_conj : Formula.and γ (Formula.snce (Formula.untl γ β).neg β) ∈ C :=
    dcs_conj_closed (mcs_is_dcs h_mcs_C) hγ h_snce
  -- Apply A3b: γ ∧ snce(β, ¬untl(β,γ)) → snce(β, ¬untl(β,γ) ∧ untl(β,γ))
  have h_a3b := DerivationTree.axiom (fc := fc) [] _ (Axiom.enrichment_since β (Formula.untl γ β).neg γ) trivial
  have h_enriched : Formula.snce ((Formula.untl γ β).neg.and (Formula.untl γ β)) β ∈ C :=
    SetMaximalConsistent.implication_property h_mcs_C (theorem_in_mcs_fc h_mcs_C h_a3b) h_conj
  -- BX10': snce(β, X) → P(X), so P(¬untl(β,γ) ∧ untl(β,γ)) ∈ C
  have h_P' := since_implies_P_in_mcs fc h_mcs_C h_enriched
  -- ¬untl(β,γ) ∧ untl(β,γ) → ⊥ is derivable (propositional contradiction)
  have h_neg_event : DerivationTree fc [] ((Formula.untl γ β).neg.and (Formula.untl γ β)).neg :=
    liftBase fc
      (let h1 := Cslib.Logic.Bimodal.Theorems.Propositional.lce_imp (Formula.untl γ β).neg (Formula.untl γ β)
       let h2 := Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp (Formula.untl γ β).neg (Formula.untl γ β)
       let h3 := DerivationTree.axiom (fc := .Base) [] _ (Axiom.imp_k ((Formula.untl γ β).neg.and (Formula.untl γ β)) (Formula.untl γ β) (Formula.bot : Formula Atom)) trivial
       mp h2 (mp h1 h3))
  -- H(¬(¬untl(β,γ) ∧ untl(β,γ))) ∈ C by past necessitation
  have h_H_neg := theorem_in_mcs_fc h_mcs_C (Cslib.Logic.Bimodal.Theorems.past_necessitation _ h_neg_event)
  -- P(X) and H(¬X) are contradictory in MCS C
  exact somePast_allPast_neg_absurd h_mcs_C _ h_P' h_H_neg

/--
**Corollary**: burgessRSet and burgessRSetSince are equivalent.
-/
theorem burgessRSet_iff_burgessRSetSince (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C) :
    burgessRSet A B C ↔ burgessRSetSince C B A := by
  constructor
  · intro h_rSet β hβ
    exact burgessR_implies_burgessRSince fc h_mcs_A h_mcs_C (h_rSet β hβ)
  · intro h_rSetSince β hβ
    exact burgessRSince_implies_burgessR fc h_mcs_A h_mcs_C (h_rSetSince β hβ)

/-! ## Xu's Lemma 3.2.1: B Closure Under Until/Since Formation

Xu 1988, Lemma 3.2.1 (p. 192): If BurgessR3Maximal(A, B, C) with A, C MCS,
then B is closed under Until formation with endpoint elements:
- (i) For β ∈ B and γ ∈ C: untl(β, γ) ∈ B
- (ii) For β ∈ B and α ∈ A: snce(β, α) ∈ B

This replaces the irrecoverable B ⊆ A property from the closed-guard era.
The proof uses BX5 (self_accum) + BX2/BX3 (monotonicity) + maximality +
the Burgess 2.3 equivalence (burgessRSet ↔ burgessRSetSince).

Convention note: In Xu's notation U(event, guard), so Xu's "U(γ, β)" = our untl(β, γ).
The theorem statement uses our codebase convention: untl(guard, event).
-/

/--
**Helper**: For any β' ∈ B and δ ∈ C, untl(β' ∧ untl(β, γ), δ) ∈ A.

This is the core BX5 argument used in Xu's Lemma 3.2.1.
Given BurgessR3Maximal(A, B, C) with β ∈ B and γ ∈ C:
  Let β'' = β ∧ β', γ'' = γ ∧ δ.
  burgessRSet gives untl(β'', γ'') ∈ A.
  BX5: untl(β'', γ'') → untl(β'' ∧ untl(β'', γ''), γ'')
  BX2: ... → untl(β' ∧ untl(β, γ), γ'') (weaken guard)
  BX3: ... → untl(β' ∧ untl(β, γ), δ) (weaken event)
-/
theorem burgessR3_untl_conj_in_A (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_dcs_B : SetDeductivelyClosed fc B)
    (h_r3 : burgessR3 A B C)
    {β : Formula Atom} (hβ : β ∈ B) {γ : Formula Atom} (hγ : γ ∈ C)
    (β' : Formula Atom) (hβ' : β' ∈ B) (δ : Formula Atom) (hδ : δ ∈ C) :
    Formula.untl δ (Formula.and β' (Formula.untl γ β)) ∈ A := by
  -- Step 1: Form β'' = β ∧ β' ∈ B and γ'' = γ ∧ δ ∈ C
  have hβ'' : Formula.and β β' ∈ B := dcs_conj_closed h_dcs_B hβ hβ'
  have hγ'' : Formula.and γ δ ∈ C := dcs_conj_closed (mcs_is_dcs h_mcs_C) hγ hδ
  -- Step 2: burgessRSet gives untl(β ∧ β', γ ∧ δ) ∈ A
  have h_untl := h_r3.1 (Formula.and β β') hβ'' (Formula.and γ δ) hγ''
  -- Step 3: BX5 gives untl((β ∧ β') ∧ untl(β ∧ β', γ ∧ δ), γ ∧ δ) ∈ A
  have h_accum := until_self_accum_in_mcs fc h_mcs_A h_untl
  -- Step 4: Weaken guard via BX2
  have h_guard_weak1 : DerivationTree fc [] ((Formula.and β β').imp β) :=
    Cslib.Logic.Bimodal.Theorems.Propositional.lce_imp β β'
  have h_untl_step1 := untl_left_mono_thm fc h_mcs_A h_guard_weak1 h_untl
  -- h_untl_step1 : untl(β, γ ∧ δ) ∈ A
  have h_event_weak1 : DerivationTree fc [] ((Formula.and γ δ).imp γ) :=
    Cslib.Logic.Bimodal.Theorems.Propositional.lce_imp γ δ
  have h_G_event_weak1 := DerivationTree.temporal_necessitation _ h_event_weak1
  have h_bx3 := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until (Formula.and γ δ) γ β) trivial
  have h_untl_beta_gamma := SetMaximalConsistent.implication_property h_mcs_A
    (theorem_in_mcs_fc h_mcs_A (DerivationTree.modus_ponens [] _ _ h_bx3 h_G_event_weak1))
    h_untl_step1
  -- h_untl_beta_gamma : untl(β, γ) ∈ A
  -- Step 4b: Weaken guard of h_accum from
  --   (β ∧ β') ∧ untl(β ∧ β', γ ∧ δ) to β' ∧ untl(β, γ)
  -- First weaken untl(β ∧ β', γ ∧ δ) → untl(β, γ) as a theorem
  have h_untl_inner_weak : DerivationTree fc [] (((γ.and δ).untl (Formula.and β β')).imp (γ.untl β)) := by
    -- BX2G: G(β ∧ β' → β) → (γ ∧ δ) U (β ∧ β') → (γ ∧ δ) U β
    have h_G_gw1 := DerivationTree.temporal_necessitation _ h_guard_weak1
    have h_bx2g := DerivationTree.axiom (fc := fc) [] _ (Axiom.left_mono_until_G (Formula.and β β') β (Formula.and γ δ)) trivial
    have h_step1 : DerivationTree fc [] (((γ.and δ).untl (Formula.and β β')).imp ((γ.and δ).untl β)) :=
      DerivationTree.modus_ponens [] _ _ h_bx2g h_G_gw1
    -- BX3: G(γ ∧ δ → γ) → β U (γ ∧ δ) → β U γ
    have h_step2 : DerivationTree fc [] (((γ.and δ).untl β).imp (γ.untl β)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3 h_G_event_weak1
    -- Chain: untl(β ∧ β', γ ∧ δ) → untl(β, γ ∧ δ) → untl(β, γ)
    exact imp_trans h_step1 h_step2
  -- Now build the full guard implication:
  -- (β ∧ β') ∧ untl(β ∧ β', γ ∧ δ) → β' ∧ untl(β, γ)
  have h_full_guard_weak : DerivationTree fc [] (
    ((Formula.and β β').and ((γ.and δ).untl (Formula.and β β'))).imp
    (β'.and (γ.untl β))) := by
    -- Component 1: (β ∧ β') ∧ X → β ∧ β' → β' (two conj elims)
    have h_comp1 : DerivationTree fc [] (
      ((Formula.and β β').and ((γ.and δ).untl (Formula.and β β'))).imp β') := by
      have h1 : DerivationTree fc [] _ := Cslib.Logic.Bimodal.Theorems.Propositional.lce_imp (Formula.and β β') ((γ.and δ).untl (Formula.and β β'))
      have h2 : DerivationTree fc [] _ := Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp β β'
      exact imp_trans h1 h2
    -- Component 2: (β ∧ β') ∧ untl(β ∧ β', γ ∧ δ) → untl(β ∧ β', γ ∧ δ) → untl(β, γ)
    have h_comp2 : DerivationTree fc [] (
      ((Formula.and β β').and ((γ.and δ).untl (Formula.and β β'))).imp (γ.untl β)) := by
      have h1 : DerivationTree fc [] _ := Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp (Formula.and β β') ((γ.and δ).untl (Formula.and β β'))
      exact imp_trans h1 h_untl_inner_weak
    -- Combine: X → β' and X → untl(β, γ) gives X → β' ∧ untl(β, γ)
    exact combine_imp_conj h_comp1 h_comp2
  -- Step 4c: Apply BX2 to h_accum to weaken guard
  have h_weak_guard := untl_left_mono_thm fc h_mcs_A h_full_guard_weak h_accum
  -- h_weak_guard : (γ.and δ).untl (β'.and (γ.untl β)) ∈ A
  -- Step 5: Weaken event via BX3: γ ∧ δ → δ
  have h_event_weak2 : DerivationTree fc [] ((Formula.and γ δ).imp δ) :=
    Cslib.Logic.Bimodal.Theorems.Propositional.rce_imp γ δ
  have h_G_event_weak2 := DerivationTree.temporal_necessitation _ h_event_weak2
  have h_bx3' := DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until (Formula.and γ δ) δ (β'.and (γ.untl β))) trivial
  exact SetMaximalConsistent.implication_property h_mcs_A
    (theorem_in_mcs_fc h_mcs_A (DerivationTree.modus_ponens [] _ _ h_bx3' h_G_event_weak2))
    h_weak_guard

/-! ## BurgessR3Maximal Existence from g_content Inclusion

When g_content(A) ⊆ C (the canonical temporal ordering A ≤ C), we can
construct BurgessR3Maximal(A, B, C) using ⊤ as a seed:

1. For all γ ∈ C: G(¬γ) ∈ A would give ¬γ ∈ C (by g_content ⊆ C),
   contradicting γ ∈ C. So G(¬γ) ∉ A, hence F(γ) ∈ A (MCS).
   By F_until_equiv: U(⊤, γ) ∈ A. This gives burgessR(A, ⊤, C).

2. For all α ∈ A: BX4 gives G(P(α)) ∈ A, so P(α) ∈ g_content(A) ⊆ C.
   By P_since_equiv: S(⊤, α) ∈ C. This gives burgessRSince(C, ⊤, A).

3. ⊤ ∈ A (theorem in MCS). Apply burgessR3Maximal_exists_from_seed.
-/

/-- F(γ) ∈ A for all γ ∈ C when g_content(A) ⊆ C. -/
theorem F_mem_of_g_content_sub (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_gc : g_content A ⊆ C) (γ : Formula Atom) (h_γ : γ ∈ C) :
    Formula.someFuture γ ∈ A := by
  -- If G(¬γ) ∈ A, then ¬γ ∈ g_content(A) ⊆ C, contradicting γ ∈ C (MCS)
  by_contra h_not_F
  -- ¬F(γ) ∈ A, then G(¬γ) ∈ A via duality bridge
  have h_neg_F : (Formula.someFuture γ).neg ∈ A :=
    (SetMaximalConsistent.negation_complete h_mcs_A _).resolve_left h_not_F
  have h_G_neg : Formula.allFuture γ.neg ∈ A :=
    neg_someFuture_to_allFuture_neg h_mcs_A γ h_neg_F
  -- G(¬γ) ∈ A gives ¬γ ∈ g_content(A) ⊆ C
  have h_neg_C : γ.neg ∈ C := h_gc h_G_neg
  -- γ ∈ C and ¬γ ∈ C contradicts C being MCS (consistent)
  exact SetMaximalConsistent.neg_excludes h_mcs_C γ h_neg_C h_γ

/-- P(α) ∈ C for all α ∈ A when g_content(A) ⊆ C. Uses BX4 (connect_future). -/
theorem P_mem_of_g_content_sub (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_gc : g_content A ⊆ C) (α : Formula Atom) (h_α : α ∈ A) :
    Formula.somePast α ∈ C := by
  -- BX4: α ∈ A → G(P(α)) ∈ A
  have h_GP : Formula.allFuture (Formula.somePast α) ∈ A := by
    have h_ax : DerivationTree fc [] (α.imp (Formula.allFuture (Formula.somePast α))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future α) trivial
    exact SetMaximalConsistent.implication_property h_mcs_A
      (theorem_in_mcs_fc h_mcs_A h_ax) h_α
  -- G(P(α)) ∈ A gives P(α) ∈ g_content(A) ⊆ C
  exact h_gc h_GP

/-- **BurgessR3Maximal existence from g_content inclusion**: Given MCS A, C with
g_content(A) ⊆ C, there exists B with BurgessR3Maximal(A, B, C).

This is the key infrastructure lemma enabling g-value construction in the
chronicle elimination functions. The seed is top (tautology), which satisfies
both burgessR(A, top, C) and burgessRSince(C, top, A) when g_content(A) ⊆ C. -/
theorem burgessR3Maximal_from_g_content_sub (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_gc : g_content A ⊆ C) :
    ∃ B : Set (Formula Atom), BurgessR3Maximal fc A B C := by
  set top := Formula.bot.imp (Formula.bot : Formula Atom) with top_def
  -- top ∈ A (theorem in MCS)
  have h_top_A : top ∈ A :=
    theorem_in_mcs_fc h_mcs_A (identity (Formula.bot : Formula Atom))
  -- burgessR(A, top, C): for all gamma in C, U(top, gamma) in A
  have h_bR : burgessR A top C := by
    intro γ hγ
    have h_F := F_mem_of_g_content_sub fc h_mcs_A h_mcs_C h_gc γ hγ
    -- F(gamma) -> U(top, gamma) by F_until_equiv
    have h_bx12 : DerivationTree fc [] ((Formula.someFuture γ).imp (Formula.untl γ top)) :=
      DerivationTree.axiom [] _ (Axiom.F_until_equiv γ) trivial
    exact SetMaximalConsistent.implication_property h_mcs_A
      (theorem_in_mcs_fc h_mcs_A h_bx12) h_F
  -- burgessRSince(C, top, A): for all alpha in A, S(top, alpha) in C
  have h_bRS : burgessRSince C top A := by
    intro α hα
    have h_P := P_mem_of_g_content_sub fc h_mcs_A h_gc α hα
    -- P(alpha) -> S(top, alpha) by P_since_equiv
    have h_bx12' : DerivationTree fc [] ((Formula.somePast α).imp (Formula.snce α top)) :=
      DerivationTree.axiom [] _ (Axiom.P_since_equiv α) trivial
    exact SetMaximalConsistent.implication_property h_mcs_C
      (theorem_in_mcs_fc h_mcs_C h_bx12') h_P
  -- Apply burgessR3Maximal_exists_from_seed
  exact burgessR3Maximal_exists_from_seed fc A C top h_mcs_A h_mcs_C h_bR h_bRS h_top_A

/-- **BurgessR3Maximal existence with guard membership**: Given MCS A, C with
burgessR(A, η, C) and burgessRSince(C, η, A), there exists B with
η ∈ B and BurgessR3Maximal(A, B, C).

This is the strengthened version of `burgessR3Maximal_exists_from_seed` that
additionally returns the seed element η ∈ B. The proof uses Zorn's lemma on
DC({η}), giving B ⊇ DC({η}) ∋ η.

Note: η ∈ A is NOT required. No consistency of {η} is needed because the
Zorn family consists of CUD sets (which include Set.univ). If η is
inconsistent, DC({η}) = Set.univ, which is CUD. The resulting B may
be Set.univ (a valid CUD g-value). -/
theorem burgessR3Maximal_with_guard (fc : FrameClass) (A C : Set (Formula Atom)) (η : Formula Atom)
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_burgessR : burgessR A η C)
    (h_burgessRSince : burgessRSince C η A) :
    ∃ B : Set (Formula Atom), η ∈ B ∧ BurgessR3Maximal fc A B C := by
  have h_dc_cud : ClosedUnderDerivation fc (deductiveClosure fc ({η} : Set (Formula Atom))) :=
    deductiveClosure_closed_under_derivation fc _
  have h_dc_r3 : burgessR3 A (deductiveClosure fc ({η} : Set (Formula Atom))) C := by
    constructor
    · intro φ hφ
      exact burgessR_of_deductiveClosure_singleton fc h_mcs_A h_burgessR φ hφ
    · intro φ hφ
      exact burgessRSince_of_deductiveClosure_singleton fc h_mcs_C h_burgessRSince φ hφ
  obtain ⟨B, hSB, _, h_B3M⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_mcs_C h_dc_cud h_dc_r3
  have h_η_B : η ∈ B := hSB (subset_deductiveClosure fc ({η} : Set (Formula Atom)) (Set.mem_singleton η))
  exact ⟨B, h_η_B, h_B3M⟩

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle
