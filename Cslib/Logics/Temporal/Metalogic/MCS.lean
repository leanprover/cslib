/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Temporal.Metalogic.DeductionTheorem

/-! # Maximal Consistent Sets for Temporal Logic BX

This module instantiates the generic MCS framework for temporal logic BX and
proves temporal-specific MCS properties needed for the completeness theorem.

## Main Results

- `temporal_lindenbaum`: Every consistent set extends to an MCS.
- `temporal_closed_under_derivation`, `temporal_implication_property`,
  `temporal_negation_complete`: Generic MCS properties.
- `mcs_bot_not_mem`, `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`: Negation lemmas.
- `mcs_g_mp`: G-distribution: `G(φ→ψ) ∈ S` and `G(φ) ∈ S` imply `G(ψ) ∈ S`.
- `mcs_g_witness`: If `G(φ) ∉ S`, exists MCS T with `futureSet Ω ⊆ T` and `φ ∉ T`.
- `mcs_h_witness`: Symmetric for the past (H).

## References

* Cslib/Logics/Modal/Metalogic/MCS.lean — structural template
* Cslib/Foundations/Logic/Metalogic/Consistency.lean — generic MCS framework
-/

set_option linter.style.setOption false
set_option linter.dupNamespace false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Cslib.Logic.Temporal

open Cslib.Logic

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Abbreviations -/

/-- Set consistency for the temporal derivation system. -/
abbrev Temporal.SetConsistent (Ω : Set (Formula Atom)) : Prop :=
  Metalogic.SetConsistent temporalDerivationSystem Ω

/-- Set maximal consistency for the temporal derivation system. -/
abbrev Temporal.SetMaximalConsistent (Ω : Set (Formula Atom)) : Prop :=
  Metalogic.SetMaximalConsistent temporalDerivationSystem Ω

/-! ## Generic MCS Properties -/

theorem temporal_lindenbaum {Ω : Set (Formula Atom)}
    (hS : Temporal.SetConsistent Ω) :
    ∃ M : Set (Formula Atom), Ω ⊆ M ∧ Temporal.SetMaximalConsistent M :=
  Metalogic.set_lindenbaum temporalDerivationSystem hS

theorem temporal_closed_under_derivation
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {L : List (Formula Atom)} (h_sub : ∀ ψ ∈ L, ψ ∈ Ω)
    {φ : Formula Atom} (h_deriv : temporalDerivationSystem.Deriv L φ) : φ ∈ Ω :=
  Metalogic.SetMaximalConsistent.closed_under_derivation
    temporalDerivationSystem temporal_has_deduction_theorem h_mcs h_sub h_deriv

theorem temporal_implication_property
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ ψ : Formula Atom} (h_imp : Formula.imp φ ψ ∈ Ω) (h_phi : φ ∈ Ω) : ψ ∈ Ω :=
  Metalogic.SetMaximalConsistent.implication_property
    temporalDerivationSystem temporal_has_deduction_theorem h_mcs h_imp h_phi

theorem temporal_negation_complete
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    (φ : Formula Atom) : φ ∈ Ω ∨ Formula.neg φ ∈ Ω :=
  Metalogic.SetMaximalConsistent.negation_complete
    temporalDerivationSystem temporal_has_deduction_theorem h_mcs φ

/-! ## Basic MCS Properties -/

private theorem mcs_mp_axiom
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ ψ : Formula Atom} (h_mem : φ ∈ Ω) (h_ax : Axiom (φ.imp ψ)) : ψ ∈ Ω := by
  apply temporal_closed_under_derivation h_mcs (L := [φ]) (fun x hx => by
    simp [List.mem_cons] at hx; exact hx ▸ h_mem)
  unfold temporalDerivationSystem Temporal.Deriv
  exact ⟨.modus_ponens [φ] φ ψ
    (.weakening [] [φ] (φ.imp ψ) (.axiom [] _ h_ax trivial) (fun _ h => nomatch h))
    (.assumption [φ] φ (List.mem_cons.mpr (Or.inl rfl)))⟩

theorem mcs_bot_not_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω) :
    Formula.bot ∉ Ω := by
  intro h_bot
  exact h_mcs.1 [Formula.bot]
    (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h_bot)
    (by simp [temporalDerivationSystem, Temporal.Deriv]
        exact ⟨.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))⟩)

theorem mcs_neg_of_not_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ : Formula Atom} (h_not : φ ∉ Ω) : Formula.neg φ ∈ Ω := by
  rcases temporal_negation_complete h_mcs φ with h | h
  · exact absurd h h_not
  · exact h

theorem mcs_not_mem_of_neg
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ : Formula Atom} (h_neg : Formula.neg φ ∈ Ω) : φ ∉ Ω := by
  intro h_phi
  exact mcs_bot_not_mem h_mcs (temporal_implication_property h_mcs h_neg h_phi)

theorem mcs_mem_iff_neg_not_mem
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ : Formula Atom} : φ ∈ Ω ↔ Formula.neg φ ∉ Ω := by
  constructor
  · intro h hn; exact mcs_bot_not_mem h_mcs (temporal_implication_property h_mcs hn h)
  · intro h; rcases temporal_negation_complete h_mcs φ with h' | h'
    · exact h'
    · exact absurd h' h

/-! ## G-distribution (key lemma) -/

/-- Build a DerivationTree for the contrapositive: `⊢ (A→B)→(¬B→¬A)`. -/
private noncomputable def derive_contrapositive (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) := by
  -- Context: [A→B, ¬B, A] ⊢ ⊥
  -- Then DT three times to get ⊢ (A→B)→¬B→¬A = (A→B)→(B→⊥)→(A→⊥).
  let ctx := [A, Formula.neg B, A.imp B]
  have d_B : DerivationTree FrameClass.Base ctx B :=
    .modus_ponens ctx A B
      (.assumption ctx (A.imp B) (by simp [List.mem_cons, ctx]))
      (.assumption ctx A (by simp [List.mem_cons, ctx]))
  have d_bot : DerivationTree FrameClass.Base ctx Formula.bot :=
    .modus_ponens ctx B Formula.bot
      (.assumption ctx (Formula.neg B) (by simp [List.mem_cons, ctx]))
      d_B
  -- DT on A: [¬B, A→B] ⊢ A→⊥ = ¬A
  have d1 := deduction_theorem [Formula.neg B, A.imp B] A Formula.bot d_bot
  -- DT on ¬B: [A→B] ⊢ ¬B→¬A
  have d2 := deduction_theorem [A.imp B] (Formula.neg B) (Formula.neg A) d1
  -- DT on A→B: [] ⊢ (A→B)→(¬B→¬A)
  exact deduction_theorem [] (A.imp B) (B.neg.imp A.neg) d2

/-- `G(φ→ψ) ∈ S` and `G(φ) ∈ S` imply `G(ψ) ∈ S`.

Proof: By contraposition.
1. `⊢ (φ→ψ) → (¬ψ→¬φ)` (classical contrapositive).
2. Temporal necessitation: `⊢ G((φ→ψ)→(¬ψ→¬φ))`.
3. BX3 (right_mono_until) with EVENT=¬ψ→¬φ applied to `(φ→ψ) U ⊤`:
   `G((φ→ψ)→(¬ψ→¬φ)) → F(φ→ψ) → F(¬ψ→¬φ)`.
   Contrapositive: `G((φ→ψ)→(¬ψ→¬φ)) → G(¬ψ→¬φ) → G(φ→ψ)`.
   Since the G-version is derivable, we get: `G(¬ψ→¬φ) → G(φ→ψ)` in any MCS
   where the G-necessitation holds.
4. BX3 again on `G(¬ψ→¬φ) → F(¬ψ) → F(¬φ)`.
   Contrapositive: `G(¬ψ→¬φ) → G(φ) → G(ψ)`.
5. Chain: `G(φ→ψ) → G(¬ψ→¬φ)` and `G(¬ψ→¬φ) → G(φ) → G(ψ)`.
   So `G(φ→ψ) → G(φ) → G(ψ)`.

But implementing the contrapositive `G(φ→ψ) → G(¬ψ→¬φ)` requires showing that
`¬(φ→ψ) ↔ ¬(¬ψ→¬φ)` and lifting through BX3.

We take a simpler route: `G(φ→ψ) ∈ Ω → G(φ) ∈ Ω → G(ψ) ∈ S`:
Assume `F(¬ψ) ∈ S` (negation of `G(ψ)`).
By BX3: `G(¬ψ→¬φ) → F(¬ψ) → F(¬φ)`.
If we establish `G(¬ψ→¬φ) ∈ S`, then `F(¬φ) ∈ S`, contradicting `G(φ) ∈ S`.
So it suffices to show `G(φ→ψ) ∈ Ω → G(¬ψ→¬φ) ∈ S`. This follows from
`⊢ (φ→ψ)→(¬ψ→¬φ)` + BX2G (guard monotonicity of Until).

Actually, the simplest correct approach uses a chain of MCS membership arguments. -/
theorem mcs_g_mp
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ ψ : Formula Atom}
    (h_g_imp : Formula.all_future (φ.imp ψ) ∈ Ω)
    (h_g_phi : Formula.all_future φ ∈ Ω) : Formula.all_future ψ ∈ Ω := by
  -- Assume G(ψ) ∉ Ω, i.e., F(¬ψ) ∈ Ω. Derive contradiction.
  by_contra h_not_g_psi
  -- G(ψ) = ¬F(¬ψ), so G(ψ) ∉ Ω means ¬F(¬ψ) ∉ Ω, giving F(¬ψ) ∈ Ω.
  have h_f_neg_psi : Formula.some_future (Formula.neg ψ) ∈ Ω :=
    (mcs_mem_iff_neg_not_mem h_mcs).mpr h_not_g_psi
  -- Step 1: Derive ⊢ (φ→ψ) → (¬ψ → ¬φ) (contrapositive)
  have d_contra := derive_contrapositive φ ψ
  -- Step 2: Temporal necessitation: ⊢ G((φ→ψ) → (¬ψ → ¬φ))
  -- G(X) = ¬F(¬X) = ¬(¬X U ⊤). We need ⊢ G(contra).
  -- Actually, temporal_necessitation gives ⊢ G(X) from ⊢ X.
  -- So ⊢ G((φ→ψ) → (¬ψ → ¬φ)).
  have h_g_contra : Formula.all_future ((φ.imp ψ).imp (ψ.neg.imp φ.neg)) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.temporal_necessitation _ d_contra⟩
  -- Step 3: BX3 (right_mono_until):
  -- G(α→β) → (α U χ → β U χ) with α = (φ→ψ), β = (¬ψ→¬φ), χ = ⊤.
  -- This gives: G((φ→ψ)→(¬ψ→¬φ)) → F(φ→ψ) → F(¬ψ→¬φ).
  -- Contrapositive of the inner: G(contra) → ¬F(¬ψ→¬φ) → ¬F(φ→ψ).
  -- i.e., G(contra) → G(¬ψ→¬φ) → G(φ→ψ).
  -- Hmm, this gives us the wrong direction for the chain.
  -- We want: G(φ→ψ) → G(¬ψ→¬φ), not the reverse.
  --
  -- Use BX2G instead: G(guard_old → guard_new) → (event U guard_old → event U guard_new).
  -- BX2G: G(φ→χ) → (ψ U φ → ψ U χ). Here φ=guard_old, χ=guard_new, ψ=event.
  -- We need to change the event of F, not the guard.
  -- F(X) = X U ⊤. EVENT=X, GUARD=⊤.
  -- BX3 changes EVENT, BX2G changes GUARD. For F, guard is ⊤.
  -- BX3: G(α→β) → (α U ⊤ → β U ⊤) = G(α→β) → F(α) → F(β).
  -- So BX3 with α=(φ→ψ), β=(¬ψ→¬φ):
  -- G((φ→ψ)→(¬ψ→¬φ)) → F(φ→ψ) → F(¬ψ→¬φ).
  -- We DON'T have F(φ→ψ). We have G(φ→ψ) = ¬F(¬(φ→ψ)).
  -- So this doesn't help directly.
  --
  -- CORRECT approach using BX3:
  -- BX3: G(α→β) → (α U ⊤ → β U ⊤) = G(α→β) → F(α) → F(β).
  -- With α = ¬ψ, β = ¬φ:
  -- G(¬ψ→¬φ) → F(¬ψ) → F(¬φ).
  -- If we have G(¬ψ→¬φ) ∈ S and F(¬ψ) ∈ S, then F(¬φ) ∈ S.
  -- F(¬φ) ∈ S contradicts G(φ) ∈ S (since G(φ) = ¬F(¬φ)).
  --
  -- So we need G(¬ψ→¬φ) ∈ S. We'll derive this from G(φ→ψ) ∈ S.
  -- The key: ¬(φ→ψ) and ¬(¬ψ→¬φ) are classically equivalent.
  -- More precisely: (φ→ψ) → (¬ψ→¬φ) is our contrapositive.
  -- ⊢ (φ→ψ) → (¬ψ→¬φ) by derive_contrapositive.
  -- Necessitation: ⊢ G((φ→ψ)→(¬ψ→¬φ)) (already have h_g_contra).
  --
  -- Now use BX3 with α=(φ→ψ), β=(¬ψ→¬φ):
  -- G((φ→ψ)→(¬ψ→¬φ)) → F(φ→ψ) → F(¬ψ→¬φ).
  -- Contrapositive: G((φ→ψ)→(¬ψ→¬φ)) → G(¬ψ→¬φ) → G(φ→ψ).
  -- This gives G(¬ψ→¬φ) → G(φ→ψ) (given G(contra) derivable, hence in Ω).
  -- But we HAVE G(φ→ψ) and WANT G(¬ψ→¬φ). WRONG DIRECTION!
  --
  -- Hmm. BX3 only gives us one direction. We also need the converse:
  -- ⊢ (¬ψ→¬φ) → (φ→ψ). This is the converse of contrapositive.
  -- In classical logic: (¬ψ→¬φ) → (φ→ψ) is equivalent to Peirce + DNE.
  -- Specifically: assume ¬ψ→¬φ and φ. Suppose ¬ψ. Then ¬φ. Contradiction.
  -- So ψ by DNE (Peirce). Hence φ→ψ. QED.
  --
  -- So ⊢ (¬ψ→¬φ) → (φ→ψ) is derivable.
  -- Necessitation: ⊢ G((¬ψ→¬φ) → (φ→ψ)).
  -- BX3: G((¬ψ→¬φ)→(φ→ψ)) → F(¬ψ→¬φ) → F(φ→ψ).
  -- Contrapositive: G((¬ψ→¬φ)→(φ→ψ)) → G(φ→ψ) → G(¬ψ→¬φ).
  -- Since G-necessitation derivable: G(φ→ψ) → G(¬ψ→¬φ). YES!
  --
  -- Wait, the contrapositive of `G(X→Y) → F(X) → F(Y)` is:
  -- `G(X→Y) → ¬F(Y) → ¬F(X)`, i.e., `G(X→Y) → G(¬Y) → G(¬X)`.
  -- No wait: `A → B → C` contrapositive is `A → ¬C → ¬B`.
  -- So `G(X→Y) → F(X) → F(Y)` gives `G(X→Y) → ¬F(Y) → ¬F(X)`.
  -- With X = (¬ψ→¬φ), Y = (φ→ψ):
  -- G((¬ψ→¬φ)→(φ→ψ)) → ¬F(φ→ψ) → ¬F(¬ψ→¬φ).
  -- = G((¬ψ→¬φ)→(φ→ψ)) → G(¬(φ→ψ)) → G(¬(¬ψ→¬φ)).
  -- Hmm, that's G(¬(φ→ψ)), not G(φ→ψ).
  --
  -- OK the issue is that `G(X) = ¬F(¬X)`, not `¬F(X)`.
  -- `G(φ→ψ) = ¬F(¬(φ→ψ))`. `G(¬ψ→¬φ) = ¬F(¬(¬ψ→¬φ))`.
  -- These are: ¬F(¬(φ→ψ)) and ¬F(¬(¬ψ→¬φ)).
  -- Since ¬(φ→ψ) and ¬(¬ψ→¬φ) are classically equivalent (both = φ∧¬ψ),
  -- F(¬(φ→ψ)) and F(¬(¬ψ→¬φ)) are equivalent.
  -- So G(φ→ψ) ↔ G(¬ψ→¬φ) in any MCS.
  --
  -- Concretely: ⊢ ¬(φ→ψ) → ¬(¬ψ→¬φ) and ⊢ ¬(¬ψ→¬φ) → ¬(φ→ψ).
  -- BX3 on the first: G(¬(φ→ψ)→¬(¬ψ→¬φ)) → F(¬(φ→ψ)) → F(¬(¬ψ→¬φ)).
  -- Contrapositive: ... → G(¬ψ→¬φ) → G(φ→ψ). (since ¬F(¬X) = G(X))
  -- Wait: ¬F(¬(¬ψ→¬φ)) → ¬F(¬(φ→ψ)), i.e., G(¬ψ→¬φ) → G(φ→ψ).
  -- And the other direction:
  -- G(¬(¬ψ→¬φ)→¬(φ→ψ)) → F(¬(¬ψ→¬φ)) → F(¬(φ→ψ)).
  -- Contrapositive: G(¬(¬ψ→¬φ)→¬(φ→ψ)) → G(φ→ψ) → G(¬ψ→¬φ).
  -- Since ⊢ ¬(¬ψ→¬φ) → ¬(φ→ψ) and necessitation gives the G-version derivable,
  -- we get G(φ→ψ) → G(¬ψ→¬φ) in any MCS.
  --
  -- So the chain is:
  -- (a) G(φ→ψ) → G(¬ψ→¬φ) (from above)
  -- (b) G(¬ψ→¬φ) → F(¬ψ) → F(¬φ) (BX3)
  -- Chain: G(φ→ψ) → F(¬ψ) → F(¬φ).
  -- We have G(φ→ψ) ∈ S and F(¬ψ) ∈ S. So F(¬φ) ∈ S. But G(φ) ∈ S = ¬F(¬φ) ∈ S.
  -- Contradiction! F(¬φ) ∈ S and ¬F(¬φ) ∈ S contradicts consistency of S.
  --
  -- Implementation: build the derivations, use temporal_closed_under_derivation
  -- and temporal_implication_property.

  -- Step A: Derive G(¬ψ→¬φ) ∈ S from G(φ→ψ) ∈ S.
  -- Need: ⊢ ¬(¬ψ→¬φ) → ¬(φ→ψ), then BX3 gives
  -- G(¬(¬ψ→¬φ)→¬(φ→ψ)) → F(¬(¬ψ→¬φ)) → F(¬(φ→ψ)).
  -- Contrapositive: ... → ¬F(¬(φ→ψ)) → ¬F(¬(¬ψ→¬φ)) = G(φ→ψ) → G(¬ψ→¬φ).
  -- Since G(¬(¬ψ→¬φ)→¬(φ→ψ)) is derivable (necessitation of propositional fact),
  -- it's in Ω. Then G(φ→ψ) → G(¬ψ→¬φ) holds in Ω.
  -- But working through the contrapositive of `A → B → C` to get `A → ¬C → ¬B`
  -- requires yet more derivation tree construction.
  --
  -- SIMPLIFICATION: Instead of all this machinery, let me directly prove
  -- the MCS-level result semantically. The core fact is:
  -- For any MCS S with G(φ→ψ) ∈ S, G(φ) ∈ S, and F(¬ψ) ∈ S:
  -- BX3: G(¬ψ→¬φ) → F(¬ψ) → F(¬φ).
  -- We need G(¬ψ→¬φ) ∈ S.
  --
  -- Actually let me try yet another approach. We directly use mcs_mp_axiom
  -- applied to suitable axiom instances.
  --
  -- BX3 axiom: right_mono_until α β χ gives
  --   G(α→β) → (α U χ → β U χ)
  -- Instance with α = Formula.neg ψ, β = Formula.neg φ, χ = Formula.top:
  --   G(¬ψ→¬φ) → (¬ψ U ⊤ → ¬φ U ⊤) = G(¬ψ→¬φ) → F(¬ψ) → F(¬φ)
  --
  -- So if we have G(¬ψ→¬φ) ∈ S, F(¬ψ) ∈ Ω → F(¬φ) ∈ S.
  --
  -- We establish G(¬ψ→¬φ) ∈ S from G(φ→ψ) ∈ S using:
  -- ⊢ ¬(¬ψ→¬φ) → ¬(φ→ψ) (derivable)
  -- BX3 with α = ¬(¬ψ→¬φ), β = ¬(φ→ψ), χ = ⊤:
  -- G(¬(¬ψ→¬φ)→¬(φ→ψ)) → F(¬(¬ψ→¬φ)) → F(¬(φ→ψ))
  -- Derivable G-version in Ω, so:
  -- F(¬(¬ψ→¬φ)) → F(¬(φ→ψ))
  -- Contrapositive: ¬F(¬(φ→ψ)) → ¬F(¬(¬ψ→¬φ))
  -- = G(φ→ψ) → G(¬ψ→¬φ) ✓
  --
  -- But proving the contrapositive at the MCS level requires showing:
  -- if (A→B) ∈ S then (¬B→¬A) ∈ S (where A = F(¬(¬ψ→¬φ)), B = F(¬(φ→ψ))).
  -- This requires: ¬B ∈ Ω → ¬A ∈ S. I.e., G(φ→ψ) ∈ Ω → G(¬ψ→¬φ) ∈ S.
  -- Which is what we're trying to prove!
  --
  -- The issue is that taking contrapositives at the MCS level is non-trivial
  -- because MCS membership is not closed under arbitrary propositional reasoning
  -- without going through derivations.
  --
  -- Let me take the most direct approach possible and just build the derivation
  -- trees we need.

  -- Key derivation: ⊢ ¬(¬ψ→¬φ) → ¬(φ→ψ)
  -- Proof: Assume ¬(¬ψ→¬φ) and (φ→ψ). Then ¬ψ→¬φ by contrapositive(φ→ψ).
  -- Contradiction with ¬(¬ψ→¬φ).
  -- So ¬(¬ψ→¬φ) → ¬(φ→ψ). QED.
  -- In derivation tree: [(¬ψ→¬φ).neg, φ.imp ψ] ⊢ ⊥.
  -- derive_contrapositive gives ⊢ (φ→ψ)→(¬ψ→¬φ).
  -- Weaken to context: [(¬ψ→¬φ).neg, φ.imp ψ] ⊢ (φ→ψ)→(¬ψ→¬φ).
  -- MP with assumption(φ→ψ): [(¬ψ→¬φ).neg, φ.imp ψ] ⊢ ¬ψ→¬φ.
  -- Assumption: (¬ψ→¬φ).neg. MP: ⊥.
  -- DT twice: ⊢ (¬ψ→¬φ).neg → (φ→ψ).neg.
  have d_neg_equiv : DerivationTree FrameClass.Base []
      ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) := by
    let ctx := [φ.imp ψ, (ψ.neg.imp φ.neg).neg]
    have d_contra_w : DerivationTree FrameClass.Base ctx (ψ.neg.imp φ.neg) :=
      .modus_ponens ctx (φ.imp ψ) (ψ.neg.imp φ.neg)
        (.weakening [] ctx _ (derive_contrapositive φ ψ) (fun _ h => nomatch h))
        (.assumption ctx (φ.imp ψ) (by simp [List.mem_cons, ctx]))
    have d_bot : DerivationTree FrameClass.Base ctx Formula.bot :=
      .modus_ponens ctx (ψ.neg.imp φ.neg) Formula.bot
        (.assumption ctx (ψ.neg.imp φ.neg).neg (by simp [List.mem_cons, ctx]))
        d_contra_w
    have d1 := deduction_theorem [(ψ.neg.imp φ.neg).neg] (φ.imp ψ) Formula.bot d_bot
    exact deduction_theorem [] (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg d1
  -- Necessitation: ⊢ G(¬(¬ψ→¬φ) → ¬(φ→ψ))
  have h_g_neg_equiv_S :
      Formula.all_future ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.temporal_necessitation _ d_neg_equiv⟩
  -- BX3 (right_mono_until) with α = ¬(¬ψ→¬φ), β = ¬(φ→ψ), χ = ⊤:
  -- G(¬(¬ψ→¬φ)→¬(φ→ψ)) → (¬(¬ψ→¬φ) U ⊤ → ¬(φ→ψ) U ⊤)
  -- = G(...) → F(¬(¬ψ→¬φ)) → F(¬(φ→ψ))
  -- So G(...) ∈ Ω → (F(¬(¬ψ→¬φ)) → F(¬(φ→ψ))) ∈ S.
  -- BX3 axiom instance:
  -- right_mono_until (¬(¬ψ→¬φ)) (¬(φ→ψ)) ⊤
  -- gives: G(¬(¬ψ→¬φ)→¬(φ→ψ)) → (¬(¬ψ→¬φ) U ⊤ → ¬(φ→ψ) U ⊤)
  have h_bx3_imp : Formula.imp (Formula.some_future (ψ.neg.imp φ.neg).neg)
      (Formula.some_future (φ.imp ψ).neg) ∈ Ω :=
    mcs_mp_axiom h_mcs h_g_neg_equiv_S
      (.right_mono_until (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top)
  -- Now: if F(¬(¬ψ→¬φ)) ∈ S then F(¬(φ→ψ)) ∈ S.
  -- We want the contrapositive: ¬F(¬(φ→ψ)) ∈ Ω → ¬F(¬(¬ψ→¬φ)) ∈ S.
  -- I.e., G(φ→ψ) ∈ Ω → G(¬ψ→¬φ) ∈ S.
  -- This follows from: assume G(φ→ψ) ∈ S, suppose G(¬ψ→¬φ) ∉ S,
  -- then F(¬(¬ψ→¬φ)) ∈ S (by neg complete), then F(¬(φ→ψ)) ∈ S (by h_bx3_imp),
  -- but G(φ→ψ) ∈ S means ¬F(¬(φ→ψ)) ∈ S. Contradiction.
  have h_g_contra_psi_phi : Formula.all_future (ψ.neg.imp φ.neg) ∈ Ω := by
    by_contra h_not
    have h_f := (mcs_mem_iff_neg_not_mem h_mcs).mpr h_not
    -- h_f : F(¬(¬ψ→¬φ)) ∈ Ω
    have h_f2 := temporal_implication_property h_mcs h_bx3_imp h_f
    -- h_f2 : F(¬(φ→ψ)) ∈ Ω
    -- But G(φ→ψ) ∈ S, so ¬F(¬(φ→ψ)) ∈ S. Contradiction.
    exact mcs_not_mem_of_neg h_mcs h_g_imp h_f2
  -- Now: G(¬ψ→¬φ) ∈ S and F(¬ψ) ∈ S.
  -- BX3: G(¬ψ→¬φ) → (¬ψ U ⊤ → ¬φ U ⊤) = G(¬ψ→¬φ) → F(¬ψ) → F(¬φ).
  have h_bx3_2 : Formula.imp (Formula.some_future ψ.neg) (Formula.some_future φ.neg) ∈ Ω :=
    mcs_mp_axiom h_mcs h_g_contra_psi_phi
      (.right_mono_until ψ.neg φ.neg Formula.top)
  -- F(¬ψ) → F(¬φ) ∈ S, and F(¬ψ) ∈ S. So F(¬φ) ∈ S.
  have h_f_neg_phi := temporal_implication_property h_mcs h_bx3_2 h_f_neg_psi
  -- But G(φ) = ¬F(¬φ) ∈ S. Contradiction.
  exact mcs_not_mem_of_neg h_mcs h_g_phi h_f_neg_phi

/-- Symmetric version for H (all_past). -/
theorem mcs_h_mp
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ ψ : Formula Atom}
    (h_h_imp : Formula.all_past (φ.imp ψ) ∈ Ω)
    (h_h_phi : Formula.all_past φ ∈ Ω) : Formula.all_past ψ ∈ Ω := by
  -- Same structure as mcs_g_mp but using BX3' (right_mono_since) and temporal_duality.
  by_contra h_not_h_psi
  have h_p_neg_psi : Formula.some_past (Formula.neg ψ) ∈ Ω :=
    (mcs_mem_iff_neg_not_mem h_mcs).mpr h_not_h_psi
  -- Derive ¬(¬ψ→¬φ) → ¬(φ→ψ) same as before
  have d_neg_equiv : DerivationTree FrameClass.Base []
      ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) := by
    let ctx := [φ.imp ψ, (ψ.neg.imp φ.neg).neg]
    have d_contra_w : DerivationTree FrameClass.Base ctx (ψ.neg.imp φ.neg) :=
      .modus_ponens ctx (φ.imp ψ) (ψ.neg.imp φ.neg)
        (.weakening [] ctx _ (derive_contrapositive φ ψ) (fun _ h => nomatch h))
        (.assumption ctx (φ.imp ψ) (by simp [List.mem_cons, ctx]))
    have d_bot : DerivationTree FrameClass.Base ctx Formula.bot :=
      .modus_ponens ctx (ψ.neg.imp φ.neg) Formula.bot
        (.assumption ctx (ψ.neg.imp φ.neg).neg (by simp [List.mem_cons, ctx]))
        d_contra_w
    have d1 := deduction_theorem [(ψ.neg.imp φ.neg).neg] (φ.imp ψ) Formula.bot d_bot
    exact deduction_theorem [] (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg d1
  -- Use temporal_duality to get the H version
  have h_h_neg_equiv_S :
      Formula.all_past ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) ∈ Ω := by
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    -- Need: ⊢ H(X) where X = (¬(¬ψ→¬φ)) → (¬(φ→ψ)).
    -- H(X) = swap_temporal(G(X)) since H and G are swap-duals.
    -- Actually: ⊢ X by d_neg_equiv. Temporal duality: ⊢ swap_temporal(X).
    -- Temporal necessitation: ⊢ G(X). Then temporal duality of the necessitation?
    -- No: temporal_duality takes ⊢ φ and gives ⊢ swap_temporal(φ).
    -- temporal_necessitation takes ⊢ φ and gives ⊢ G(φ).
    -- We need ⊢ H(X). H(X) = ¬P(¬X) = swap_temporal(¬F(¬X)) = swap_temporal(G(X)).
    -- So: ⊢ G(X) by necessitation. Then ⊢ swap_temporal(G(X)) = H(X) by duality.
    -- Wait: swap_temporal(G(X)) = swap_temporal(¬F(¬X)).
    -- swap_temporal swaps U↔S, so F↔P and G↔H.
    -- swap_temporal(G(X)) = H(swap_temporal(X)).
    -- But we need H(X), not H(swap_temporal(X)).
    -- Hmm. swap_temporal(X) where X is propositional (no temporal operators)
    -- should be X itself (swap only affects untl/snce).
    -- ¬(¬ψ→¬φ) → ¬(φ→ψ) has no temporal operators, so swap_temporal(X) = X.
    -- So swap_temporal(G(X)) = H(X). QED.
    -- Let me verify: G(X) = ¬F(¬X) where F(Y) = Y U ⊤.
    -- swap_temporal(G(X)) = swap_temporal(¬(¬X U ⊤)).
    -- swap on ¬Y = ¬(swap Y). swap on (¬X U ⊤) = swap(¬X) S swap(⊤).
    -- swap(⊤) = ⊤ (⊤ = ⊥→⊥, swap(imp a b) = imp (swap a) (swap b), swap(⊥)=⊥).
    -- swap(¬X) = ¬(swap X) = ¬X (X propositional).
    -- So swap(¬X U ⊤) = ¬X S ⊤ = P(¬X).
    -- swap(G(X)) = swap(¬P(¬X)... wait, no.
    -- G(X) = ¬F(¬X) = (F(¬X) → ⊥) = ((¬X U ⊤) → ⊥).
    -- swap(G(X)) = swap((¬X U ⊤) → ⊥) = (swap(¬X U ⊤) → swap(⊥))
    --            = ((swap(¬X) S swap(⊤)) → ⊥)
    --            = ((¬X S ⊤) → ⊥)   [since X propositional: swap(X)=X]
    --            = (P(¬X) → ⊥)
    --            = ¬P(¬X)
    --            = H(X). ✓
    -- Use double-swap trick: duality on d_neg_equiv gives ⊢ swap(X).
    -- Necessitation: ⊢ G(swap(X)). Duality: ⊢ swap(G(swap(X))) = H(swap(swap(X))) = H(X).
    let X := (ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg
    have d_swap_X := DerivationTree.temporal_duality X d_neg_equiv
    have d_g_swap := DerivationTree.temporal_necessitation _ d_swap_X
    have d_h_swap2 := DerivationTree.temporal_duality _ d_g_swap
    -- d_h_swap2 : ⊢ swap(G(swap(X))) which equals H(swap(swap(X)))
    have h_eq : (Formula.all_future X.swap_temporal).swap_temporal =
        Formula.all_past (X.swap_temporal.swap_temporal) := by
      simp only [Formula.all_future, Formula.all_past, Formula.some_future, Formula.some_past,
        Formula.neg, Formula.top, Formula.swap_temporal]
    rw [Formula.swap_temporal_involution] at h_eq
    exact ⟨h_eq ▸ d_h_swap2⟩
  -- BX3' (right_mono_since): H(α→β) → (α S ⊤ → β S ⊤) = H(α→β) → P(α) → P(β)
  have h_bx3_imp : Formula.imp (Formula.some_past (ψ.neg.imp φ.neg).neg)
      (Formula.some_past (φ.imp ψ).neg) ∈ Ω :=
    mcs_mp_axiom h_mcs h_h_neg_equiv_S
      (.right_mono_since (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top)
  have h_h_contra : Formula.all_past (ψ.neg.imp φ.neg) ∈ Ω := by
    by_contra h_not
    have h_p := (mcs_mem_iff_neg_not_mem h_mcs).mpr h_not
    have h_p2 := temporal_implication_property h_mcs h_bx3_imp h_p
    exact mcs_not_mem_of_neg h_mcs h_h_imp h_p2
  have h_bx3_2 : Formula.imp (Formula.some_past ψ.neg) (Formula.some_past φ.neg) ∈ Ω :=
    mcs_mp_axiom h_mcs h_h_contra
      (.right_mono_since ψ.neg φ.neg Formula.top)
  have h_p_neg_phi := temporal_implication_property h_mcs h_bx3_2 h_p_neg_psi
  exact mcs_not_mem_of_neg h_mcs h_h_phi h_p_neg_phi

/-! ## G-witness and H-witness -/

/-- The "future set" of an MCS: all formulas whose G-closure is in Ω. -/
def futureSet (Ω : Set (Formula Atom)) : Set (Formula Atom) :=
  {φ | Formula.all_future φ ∈ Ω}

/-- The "past set" of an MCS: all formulas whose H-closure is in Ω. -/
def pastSet (Ω : Set (Formula Atom)) : Set (Formula Atom) :=
  {φ | Formula.all_past φ ∈ Ω}

/-- Derive ⊥ from G-context: if all G(lᵢ) ∈ S and L ⊢ ⊥, then S is inconsistent
via iterated G-distribution.

The proof repeatedly applies mcs_g_mp: from G(l₁→l₂→...→⊥) (via necessitation of
the iterated deduction theorem result) and G(l₁) ∈ S, derive G(l₂→...→⊥) ∈ S, etc.
The final step gives G(⊥) ∈ S, i.e., ¬F(⊤) ∈ S. But serial_future gives F(⊤) ∈ S.
Contradiction. -/
private theorem derive_g_contradiction
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {L : List (Formula Atom)} {φ : Formula Atom}
    (hL : ∀ x ∈ L, Formula.all_future x ∈ Ω)
    (d : DerivationTree FrameClass.Base L φ) : Formula.all_future φ ∈ Ω := by
  induction L generalizing φ with
  | nil =>
    -- L = [], d : [] ⊢ φ. Necessitation: ⊢ G(φ). So G(φ) ∈ S.
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    exact ⟨.temporal_necessitation _ d⟩
  | cons a L' ih =>
    -- d : (a :: L') ⊢ φ.
    -- DT: L' ⊢ a → φ.
    have dt := deduction_theorem L' a φ d
    -- IH on L' with (a → φ): G(a → φ) ∈ S.
    have h_g_imp := ih (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))) dt
    -- G(a) ∈ S.
    have h_g_a := hL a (List.mem_cons.mpr (Or.inl rfl))
    -- By mcs_g_mp: G(a → φ) ∈ S and G(a) ∈ Ω → G(φ) ∈ S.
    exact mcs_g_mp h_mcs h_g_imp h_g_a

/-- If `G(φ) ∉ S`, then there exists an MCS `T` with `futureSet Ω ⊆ T` and `φ ∉ T`. -/
theorem mcs_g_witness
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ : Formula Atom} (h_not_g : Formula.all_future φ ∉ Ω) :
    ∃ T : Set (Formula Atom), Temporal.SetMaximalConsistent T ∧
      (∀ ψ, Formula.all_future ψ ∈ Ω → ψ ∈ T) ∧ φ ∉ T := by
  let W := futureSet Ω ∪ {Formula.neg φ}
  have hW : Temporal.SetConsistent W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    -- Separate L into elements with G-versions in Ω and possibly ¬φ.
    let L' := L.filter (· ≠ Formula.neg φ)
    have h_L'_g : ∀ x ∈ L', Formula.all_future x ∈ Ω := by
      intro x hx
      simp only [L', List.mem_filter, decide_eq_true_eq] at hx
      rcases hL x hx.1 with h | h
      · exact h
      · exact absurd h hx.2
    by_cases h_neg_in : Formula.neg φ ∈ L
    · -- ¬φ ∈ L. Weaken to ¬φ :: L', then DT gives L' ⊢ ¬φ → ⊥ = L' ⊢ φ.neg.neg.
      have h_perm : ∀ x, x ∈ L → x ∈ Formula.neg φ :: L' := by
        intro x hx
        by_cases hxn : x = Formula.neg φ
        · exact List.mem_cons.mpr (Or.inl hxn)
        · exact List.mem_cons.mpr (Or.inr (by
            simp only [L', List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
      have d_reord := DerivationTree.weakening L (Formula.neg φ :: L') Formula.bot
        d_bot h_perm
      -- DT: L' ⊢ ¬φ → ⊥
      have d_dne := deduction_theorem L' (Formula.neg φ) Formula.bot d_reord
      -- L' ⊢ ¬φ → ⊥ = L' ⊢ (φ→⊥)→⊥. Derive φ by Peirce + EFQ.
      let neg_phi := Formula.neg φ
      have efq : DerivationTree FrameClass.Base L' (Formula.bot.imp φ) :=
        .weakening [] L' _ (.axiom [] _ (.efq φ) trivial) (fun _ h => nomatch h)
      have ik : DerivationTree FrameClass.Base L'
          ((Formula.bot.imp φ).imp (neg_phi.imp (Formula.bot.imp φ))) :=
        .weakening [] L' _ (.axiom [] _ (.imp_s (Formula.bot.imp φ) neg_phi) trivial)
          (fun _ h => nomatch h)
      have step_k := DerivationTree.modus_ponens L' _ _ ik efq
      have is_ax : DerivationTree FrameClass.Base L'
          ((neg_phi.imp (Formula.bot.imp φ)).imp
           ((neg_phi.imp Formula.bot).imp (neg_phi.imp φ))) :=
        .weakening [] L' _ (.axiom [] _ (.imp_k neg_phi Formula.bot φ) trivial)
          (fun _ h => nomatch h)
      have step_s := DerivationTree.modus_ponens L' _ _ is_ax step_k
      have step3 := DerivationTree.modus_ponens L' _ _ step_s d_dne
      have peirce_ax : DerivationTree FrameClass.Base L'
          (((φ.imp Formula.bot).imp φ).imp φ) :=
        .weakening [] L' _ (.axiom [] _ (.peirce φ Formula.bot) trivial)
          (fun _ h => nomatch h)
      have d_phi := DerivationTree.modus_ponens L' _ _ peirce_ax step3
      -- L' ⊢ φ. By derive_g_contradiction: G(φ) ∈ S. Contradiction.
      exact h_not_g (derive_g_contradiction h_mcs h_L'_g d_phi)
    · -- ¬φ ∉ L. All elements of L have G-versions in Ω.
      have h_all_g : ∀ x ∈ L, Formula.all_future x ∈ Ω := by
        intro x hx
        rcases hL x hx with h | h
        · exact h
        · exact absurd (h ▸ hx) h_neg_in
      -- L ⊢ ⊥. derive_g_contradiction gives G(⊥) ∈ S.
      have h_g_bot := derive_g_contradiction h_mcs h_all_g d_bot
      -- G(⊥) = ¬F(⊤) = ¬F(¬⊥). So ¬F(¬⊥) ∈ S, i.e., ¬(¬⊥ U ⊤) ∈ S.
      -- But F(⊤) ∈ S by serial_future: ⊤ → F(⊤) is axiom, ⊤ ∈ S.
      -- Wait: G(⊥) = ¬F(¬⊥) = ¬F(⊤→⊥→⊥... no.
      -- G(⊥) = all_future ⊥ = neg (some_future (neg ⊥)) = neg (some_future ⊤)
      -- = ¬F(⊤). Hmm, neg ⊥ = ⊥→⊥ = ⊤. So G(⊥) = ¬F(⊤).
      -- serial_future: ⊤ → F(⊤). ⊤ ∈ S (derivable). So F(⊤) ∈ S.
      -- But ¬F(⊤) = G(⊥) ∈ S. Contradiction.
      -- First: ⊤ ∈ S.
      have h_top : Formula.top ∈ Ω := by
        apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
        unfold temporalDerivationSystem Temporal.Deriv
        exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
      -- serial_future: ⊤ → F(⊤).
      have h_f_top : Formula.some_future Formula.top ∈ Ω :=
        mcs_mp_axiom h_mcs h_top .serial_future
      -- G(⊥) = ¬F(⊤). So h_g_bot says ¬F(⊤) ∈ S.
      -- But F(⊤) ∈ S. Contradiction.
      exact mcs_not_mem_of_neg h_mcs h_g_bot h_f_top
  obtain ⟨T, hWT, hT_mcs⟩ := temporal_lindenbaum hW
  refine ⟨T, hT_mcs, ?_, ?_⟩
  · intro ψ h_g; exact hWT (Set.mem_union_left _ h_g)
  · have h_neg : Formula.neg φ ∈ T := hWT (Set.mem_union_right _ (Set.mem_singleton _))
    exact mcs_not_mem_of_neg hT_mcs h_neg

/-- Symmetric version for past: if `H(φ) ∉ S`, exists MCS T with pastSet Ω ⊆ T and φ ∉ T. -/
private theorem derive_h_contradiction
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {L : List (Formula Atom)} {φ : Formula Atom}
    (hL : ∀ x ∈ L, Formula.all_past x ∈ Ω)
    (d : DerivationTree FrameClass.Base L φ) : Formula.all_past φ ∈ Ω := by
  induction L generalizing φ with
  | nil =>
    apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
    unfold temporalDerivationSystem Temporal.Deriv
    have d_g := DerivationTree.temporal_necessitation _ d
    have d_swap := DerivationTree.temporal_duality _ d_g
    have h_eq : (Formula.all_future φ).swap_temporal = Formula.all_past φ.swap_temporal := by
      simp only [Formula.all_future, Formula.all_past, Formula.some_future, Formula.some_past,
        Formula.neg, Formula.top, Formula.swap_temporal]
    -- d_swap : ⊢ swap_temporal(G(φ)) = ⊢ H(swap_temporal(φ))
    -- We need ⊢ H(φ). Since swap is an involution: H(φ) = H(swap(swap(φ))).
    -- Use: derive swap(φ) first, then necessitation, then duality gives H(swap(swap(φ))) = H(φ).
    -- Step 1: duality on d gives ⊢ swap(φ).
    have d_swap_phi := DerivationTree.temporal_duality φ d
    -- Step 2: necessitation on swap(φ) gives ⊢ G(swap(φ)).
    have d_g_swap := DerivationTree.temporal_necessitation _ d_swap_phi
    -- Step 3: duality gives ⊢ swap(G(swap(φ))) = H(swap(swap(φ))) = H(φ) by involution.
    have d_h := DerivationTree.temporal_duality _ d_g_swap
    have h_eq2 : (Formula.all_future φ.swap_temporal).swap_temporal =
        Formula.all_past (φ.swap_temporal.swap_temporal) := by
      simp only [Formula.all_future, Formula.all_past, Formula.some_future, Formula.some_past,
        Formula.neg, Formula.top, Formula.swap_temporal]
    rw [Formula.swap_temporal_involution] at h_eq2
    exact ⟨h_eq2 ▸ d_h⟩
  | cons a L' ih =>
    have dt := deduction_theorem L' a φ d
    have h_h_imp := ih (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))) dt
    have h_h_a := hL a (List.mem_cons.mpr (Or.inl rfl))
    exact mcs_h_mp h_mcs h_h_imp h_h_a

theorem mcs_h_witness
    {Ω : Set (Formula Atom)} (h_mcs : Temporal.SetMaximalConsistent Ω)
    {φ : Formula Atom} (h_not_h : Formula.all_past φ ∉ Ω) :
    ∃ T : Set (Formula Atom), Temporal.SetMaximalConsistent T ∧
      (∀ ψ, Formula.all_past ψ ∈ Ω → ψ ∈ T) ∧ φ ∉ T := by
  let W := pastSet Ω ∪ {Formula.neg φ}
  have hW : Temporal.SetConsistent W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    let L' := L.filter (· ≠ Formula.neg φ)
    have h_L'_h : ∀ x ∈ L', Formula.all_past x ∈ Ω := by
      intro x hx
      simp only [L', List.mem_filter, decide_eq_true_eq] at hx
      rcases hL x hx.1 with h | h
      · exact h
      · exact absurd h hx.2
    by_cases h_neg_in : Formula.neg φ ∈ L
    · have h_perm : ∀ x, x ∈ L → x ∈ Formula.neg φ :: L' := by
        intro x hx
        by_cases hxn : x = Formula.neg φ
        · exact List.mem_cons.mpr (Or.inl hxn)
        · exact List.mem_cons.mpr (Or.inr (by
            simp only [L', List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
      have d_reord := DerivationTree.weakening L (Formula.neg φ :: L') Formula.bot
        d_bot h_perm
      have d_dne := deduction_theorem L' (Formula.neg φ) Formula.bot d_reord
      let neg_phi := Formula.neg φ
      have efq : DerivationTree FrameClass.Base L' (Formula.bot.imp φ) :=
        .weakening [] L' _ (.axiom [] _ (.efq φ) trivial) (fun _ h => nomatch h)
      have ik : DerivationTree FrameClass.Base L'
          ((Formula.bot.imp φ).imp (neg_phi.imp (Formula.bot.imp φ))) :=
        .weakening [] L' _ (.axiom [] _ (.imp_s (Formula.bot.imp φ) neg_phi) trivial)
          (fun _ h => nomatch h)
      have step_k := DerivationTree.modus_ponens L' _ _ ik efq
      have is_ax : DerivationTree FrameClass.Base L'
          ((neg_phi.imp (Formula.bot.imp φ)).imp
           ((neg_phi.imp Formula.bot).imp (neg_phi.imp φ))) :=
        .weakening [] L' _ (.axiom [] _ (.imp_k neg_phi Formula.bot φ) trivial)
          (fun _ h => nomatch h)
      have step_s := DerivationTree.modus_ponens L' _ _ is_ax step_k
      have step3 := DerivationTree.modus_ponens L' _ _ step_s d_dne
      have peirce_ax : DerivationTree FrameClass.Base L'
          (((φ.imp Formula.bot).imp φ).imp φ) :=
        .weakening [] L' _ (.axiom [] _ (.peirce φ Formula.bot) trivial)
          (fun _ h => nomatch h)
      have d_phi := DerivationTree.modus_ponens L' _ _ peirce_ax step3
      exact h_not_h (derive_h_contradiction h_mcs h_L'_h d_phi)
    · have h_all_h : ∀ x ∈ L, Formula.all_past x ∈ Ω := by
        intro x hx
        rcases hL x hx with h | h
        · exact h
        · exact absurd (h ▸ hx) h_neg_in
      have h_h_bot := derive_h_contradiction h_mcs h_all_h d_bot
      have h_top : Formula.top ∈ Ω := by
        apply temporal_closed_under_derivation h_mcs (L := []) (fun _ h => nomatch h)
        unfold temporalDerivationSystem Temporal.Deriv
        exact ⟨.axiom [] _ (.efq Formula.bot) trivial⟩
      have h_p_top : Formula.some_past Formula.top ∈ Ω :=
        mcs_mp_axiom h_mcs h_top .serial_past
      exact mcs_not_mem_of_neg h_mcs h_h_bot h_p_top
  obtain ⟨T, hWT, hT_mcs⟩ := temporal_lindenbaum hW
  refine ⟨T, hT_mcs, ?_, ?_⟩
  · intro ψ h_h; exact hWT (Set.mem_union_left _ h_h)
  · have h_neg : Formula.neg φ ∈ T := hWT (Set.mem_union_right _ (Set.mem_singleton _))
    exact mcs_not_mem_of_neg hT_mcs h_neg

end Cslib.Logic.Temporal
