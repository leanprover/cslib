/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Modal.Metalogic.MCS
import Cslib.Logics.Modal.Metalogic.Soundness

/-! # Completeness Theorem for S5 Modal Logic

This module proves completeness for S5 modal logic via the canonical Kripke model
construction: every formula valid over all S5 frames is derivable.

## Main Results

- `CanonicalWorld`: The type of worlds in the canonical model (MCS).
- `CanonicalModel`: The canonical Kripke model with accessibility and valuation.
- `canonical_refl`, `canonical_trans`, `canonical_eucl`: The canonical model is an S5 frame.
- `truth_lemma`: `Satisfies (CanonicalModel) S φ ↔ φ ∈ S.val` (by structural induction on φ).
- `completeness`: If `φ` is valid over all S5 frames, then `φ` is derivable.

## Design

The canonical model has:
- **Worlds**: Maximally consistent sets (MCS) of the modal derivation system.
- **Accessibility**: `R S T ↔ ∀ ψ, □ψ ∈ S → ψ ∈ T` (the standard canonical relation).
- **Valuation**: `v S p ↔ atom p ∈ S`.

For S5, this relation is reflexive (by axiom T / box_closure), transitive
(by axiom 4 / box_box), and Euclidean (by axiom B + T + 4).

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Canonical Models)
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## Canonical Model Definition -/

/-- A canonical world is a maximally consistent set of the modal derivation system. -/
def CanonicalWorld (Atom : Type*) :=
  { S : Set (Proposition Atom) // Modal.SetMaximalConsistent S }

/-- The canonical model for S5 modal logic.

- Accessibility: `R S T ↔ ∀ ψ, □ψ ∈ S → ψ ∈ T`.
- Valuation: `v S p ↔ atom p ∈ S`. -/
noncomputable def CanonicalModel (Atom : Type*) : Model (CanonicalWorld Atom) Atom where
  r := fun S T => ∀ φ, Proposition.box φ ∈ S.val → φ ∈ T.val
  v := fun S p => Proposition.atom p ∈ S.val

/-! ## Canonical Frame Properties -/

/-- The canonical accessibility relation is reflexive (from axiom T). -/
theorem canonical_refl (S : CanonicalWorld Atom) :
    (CanonicalModel Atom).r S S := by
  intro φ h_box
  exact mcs_box_closure S.property h_box

/-- The canonical accessibility relation is transitive (from axiom 4). -/
theorem canonical_trans (S T U : CanonicalWorld Atom) :
    (CanonicalModel Atom).r S T → (CanonicalModel Atom).r T U →
    (CanonicalModel Atom).r S U := by
  intro hST hTU φ h_box
  -- □φ ∈ S → □□φ ∈ S (by axiom 4)
  have h_box_box := mcs_box_box S.property h_box
  -- □□φ ∈ S → □φ ∈ T (by hST)
  have h_box_T := hST (Proposition.box φ) h_box_box
  -- □φ ∈ T → φ ∈ U (by hTU)
  exact hTU φ h_box_T

/-- The canonical accessibility relation is Euclidean (from axioms B, T, 4).

Euclidean: R S T ∧ R S U → R T U.
Proof: φ ∈ T (given □φ ∈ T). Need φ ∈ U.
Since R S T: □ψ ∈ S → ψ ∈ T for all ψ.
Since R S U: □ψ ∈ S → ψ ∈ U for all ψ.
Given □φ ∈ T, need φ ∈ U.

We use B: φ ∈ T → □◇φ ∈ T.
From R S T and □◇φ ∈ T... wait, R S T goes from S to T, not T to S.

Better approach: Show R T U using the following:
Given □φ ∈ T, need φ ∈ U.
Contrapositive: suppose □φ ∉ U.
Hmm, we need to go through S.

Actually for S5 with R S T and R S U:
□φ ∈ T. Need φ ∈ U.
We know: □φ ∈ T → φ ∈ T (reflexivity of T, from axiom T).
So φ ∈ T. By axiom B: φ ∈ T → □◇φ ∈ T.
So □◇φ ∈ T.
Now need to relate T back to S.

This is getting circular. Let me use a direct argument:
If □φ ∈ T, want φ ∈ U.
Suppose φ ∉ U. Then ¬φ ∈ U (negation complete).
Since R S U: □ψ ∈ S → ψ ∈ U. In particular □(¬φ) ∈ S → ¬φ ∈ U.
We have ¬φ ∈ U. But this doesn't help directly.

Let me try: □φ ∈ T. Want φ ∈ U.
Consider any ψ with □ψ ∈ S. Then ψ ∈ T (by R S T).
So if □φ ∈ S, then φ ∈ T (already know) and φ ∈ U (by R S U). Done for this case.
But □φ might be in T but not in S!

For the general case, we need: φ ∈ T → □φ ∈ S (i.e., the converse of R S T for □-formulas).
This uses axiom B: φ ∈ T → □◇φ ∈ T.
If R S T, then for any ψ, □ψ ∈ S → ψ ∈ T.
Contrapositively: ψ ∉ T → □ψ ∉ S.
But we need the reverse: from T to S.

For S5, the key fact is that the canonical relation is actually an equivalence relation.
Symmetry follows from axiom B + reflexivity:
R S T means ∀ ψ, □ψ ∈ S → ψ ∈ T.
For symmetry: R T S, i.e., ∀ ψ, □ψ ∈ T → ψ ∈ S.
Take □ψ ∈ T. Need ψ ∈ S.
By T: ψ ∈ T. By B: □◇ψ ∈ T. R S T gives ◇ψ ∈ S.
Hmm wait. R S T gives: □χ ∈ S → χ ∈ T. This is S→T direction.
I need to show R T S: □χ ∈ T → χ ∈ S.

Take □χ ∈ T. Suppose χ ∉ S. Then ¬χ ∈ S (neg complete).
By B: ¬χ ∈ S → □◇¬χ ∈ S. So □◇¬χ ∈ S.
Since R S T: ◇¬χ ∈ T. So ¬□χ ∈ T (diamond = ¬□¬, so ◇¬χ = ¬□¬¬χ = ¬□χ... wait.
◇¬χ = ¬□¬(¬χ) = ¬□χ̃ where χ̃ = ¬χ... no.
◇ψ = ¬□¬ψ. So ◇(¬χ) = ¬□¬(¬χ) = ¬□(χ→⊥→⊥)... This is getting complicated with
the syntactic definitions.

Let me use a cleaner approach. -/
theorem canonical_eucl (S T U : CanonicalWorld Atom) :
    (CanonicalModel Atom).r S T → (CanonicalModel Atom).r S U →
    (CanonicalModel Atom).r T U := by
  intro hST hSU φ h_box_T
  -- Need: φ ∈ U.val
  -- Strategy: show □φ ∈ S, then use hSU.
  -- From □φ ∈ T:
  -- Suppose □φ ∉ S. Then ¬□φ ∈ S (by negation completeness).
  -- ¬□φ = □φ → ⊥. If we could show □(□φ) ∈ S, then □φ ∈ T (by hST), then
  -- □φ ∈ S (by reflexivity of canonical model), contradiction.
  -- But we need □(□φ) ∈ S, not just □φ ∈ T.

  -- Better: from □φ ∈ T, derive □φ ∈ S using B + box properties.
  -- □φ ∈ T → φ ∈ T (by T axiom / box_closure).
  have h_phi_T := mcs_box_closure T.property h_box_T
  -- φ ∈ T → □◇φ ∈ T (by B axiom / box_diamond).
  have h_bd_T := mcs_box_diamond T.property h_phi_T
  -- □◇φ ∈ T. We need to get information back to S.
  -- Since R S T: □ψ ∈ S → ψ ∈ T.
  -- We need the reverse direction. But R S T doesn't directly give us T → S.
  -- Key insight: show ◇φ ∈ S, which means ¬□¬φ ∈ S.
  -- If ◇φ ∉ S, then ¬◇φ ∈ S, i.e., □¬φ ∈ S (since ¬◇φ = ¬¬□¬φ = □¬φ by DNE in MCS).
  -- Then by R S T: ¬φ ∈ T. But φ ∈ T, contradiction (T is consistent).
  -- So ◇φ ∈ S.
  -- ◇φ ∈ S means ¬□¬φ ∈ S.
  -- We need □φ ∈ S.
  -- Hmm, ◇φ ∈ S doesn't directly give □φ ∈ S.

  -- Even better approach: use box_box and the canonical relation more carefully.
  -- □φ ∈ T → □□φ ∈ T (by axiom 4).
  have h_bb_T := mcs_box_box T.property h_box_T
  -- □□φ ∈ T.
  -- From □◇φ ∈ T: this means ∀ w', R T w' → ◇φ ∈ w'.
  -- But we need to get □φ ∈ S from □□φ ∈ T.

  -- I think the cleanest proof uses box_witness on S.
  -- Suppose □φ ∉ S. By box_witness: ∃ V (MCS), R S V and φ ∉ V.
  -- But we also have ∀ ψ, □ψ ∈ S → ψ ∈ V (i.e., R S V).
  -- From R S T and R S V, we need R T V (by Euclideanness -- but that's what we're proving!).
  -- Circular.

  -- Direct proof using axiom B more carefully:
  -- We use: if R S T, then R T S (symmetry, provable from axiom B).
  -- Symmetry proof: Take □ψ ∈ T. Need ψ ∈ S.
  -- Suppose ψ ∉ S. Then ¬ψ ∈ S (neg complete).
  -- By axiom B: ¬ψ ∈ S → □◇¬ψ ∈ S.
  -- So □◇¬ψ ∈ S. Since R S T: ◇¬ψ ∈ T.
  -- ◇¬ψ = ¬□¬¬ψ.
  -- In T (MCS): ¬□¬¬ψ ∈ T means □¬¬ψ ∉ T (by mcs_mem_iff_neg_not_mem).
  -- But □ψ ∈ T. We need □¬¬ψ ∉ T to contradict □ψ ∈ T.
  -- The issue: □ψ and □¬¬ψ are syntactically different.
  -- ¬¬ψ = (ψ→⊥)→⊥ which is NOT the same as ψ syntactically.
  -- So □ψ ≠ □((ψ→⊥)→⊥).
  -- We'd need ψ and (ψ→⊥)→⊥ to be inter-derivable, which they are logically
  -- but not syntactically.
  -- This means: from □ψ ∈ T, derive □((ψ→⊥)→⊥) ∈ T.
  -- This requires showing ψ → (ψ→⊥)→⊥ is derivable (easy: Peirce gives this direction).
  -- Then by K + MP: □ψ → □((ψ→⊥)→⊥). So □((ψ→⊥)→⊥) ∈ T. Contradiction.

  -- OK this works but is tedious. Let me implement it.
  -- Actually, let me just show the symmetric relation directly.
  -- Better yet: just prove Euclideanness directly using mcs_box_witness.

  -- Clean direct proof:
  -- Given: R S T, R S U, □φ ∈ T. Want: φ ∈ U.
  -- Suppose φ ∉ U. Then ¬φ ∈ U (neg complete).
  -- By B: ¬φ → □◇¬φ. So □◇¬φ ∈ U.
  -- ◇¬φ = ¬□¬(¬φ) = ¬□((φ→⊥)→⊥).
  -- Since R S U: □ψ ∈ S → ψ ∈ U.
  -- We need something about S.
  -- Hmm, let me try yet another approach.

  -- From the MCS framework, use: ∀ ψ, □ψ ∈ S → ψ ∈ T (R S T).
  -- Contrapositive: ψ ∉ T → □ψ ∉ S.
  -- We want φ ∈ U. Suppose φ ∉ U.
  -- By box_witness on S with φ: if □φ ∉ S, get V with R S V and φ ∉ V.
  -- But that doesn't help directly.

  -- The simplest correct proof I can think of:
  -- □φ ∈ T. By box_box: □□φ ∈ T.
  -- Suppose □φ ∉ S. Then by negation: ¬□φ ∈ S.
  -- ¬□φ = (□φ → ⊥).
  -- By axiom B: ¬□φ → □◇¬□φ. So □◇¬□φ ∈ S.
  -- Since R S T: ◇¬□φ ∈ T.
  -- ◇¬□φ = ¬□¬(¬□φ). In T: □¬(¬□φ) ∉ T.
  -- But we have □□φ ∈ T. If we could show □□φ implies □¬(¬□φ) in T...
  -- □φ → ¬(¬□φ) is: □φ → ((□φ→⊥)→⊥), which is derivable from Peirce.
  -- So by K: □(□φ → ((□φ→⊥)→⊥)) → (□□φ → □((□φ→⊥)→⊥)).
  -- □(□φ → ((□φ→⊥)→⊥)) is derivable (necessitation of Peirce-variant).
  -- So □□φ → □((□φ→⊥)→⊥) in T.
  -- We have □□φ ∈ T, so □((□φ→⊥)→⊥) ∈ T, i.e., □¬(¬□φ) ∈ T. Contradiction.
  -- So □φ ∈ S.
  -- Since R S U: φ ∈ U. Done!

  -- Let me implement this. First I need a helper that derives ψ → ¬¬ψ.
  -- ψ → (ψ→⊥)→⊥ is derivable. This is the double negation introduction.
  -- Proof: Assume ψ. Assume ψ→⊥. Apply to ψ: get ⊥. So ψ → (ψ→⊥)→⊥.

  -- The key step: show □φ ∈ S.
  by_contra h_phi_not_U
  apply h_phi_not_U
  -- φ ∈ U follows from □φ ∈ S and R S U
  apply hSU
  -- Need □φ ∈ S. Suppose not.
  by_contra h_box_not_S
  -- ¬□φ ∈ S
  have h_neg_box := mcs_neg_of_not_mem S.property h_box_not_S
  -- B: ¬□φ → □◇(¬□φ). So □◇(¬□φ) ∈ S.
  have h_bd := mcs_box_diamond S.property h_neg_box
  -- R S T: ◇(¬□φ) ∈ T
  have h_diam_T := hST _ h_bd
  -- ◇(¬□φ) = ¬□¬(¬□φ) ∈ T
  -- So □¬(¬□φ) ∉ T (by mcs_mem_iff_neg_not_mem)
  have h_box_dne_not_T : Proposition.box (Proposition.neg (Proposition.neg (Proposition.box φ))) ∉ T.val := by
    exact mcs_not_mem_of_neg T.property h_diam_T
  -- But we can derive □¬(¬□φ) ∈ T from □□φ ∈ T.
  -- First: derive ψ → ¬¬ψ (double negation intro) is an axiom-derivable fact.
  -- ψ → (ψ→⊥)→⊥: proof: assume ψ and ψ→⊥, then MP gives ⊥.
  -- As a DerivationTree: [ψ, ψ→⊥] ⊢ ⊥.
  -- By deduction theorem (twice): ⊢ ψ → (ψ→⊥) → ⊥ = ⊢ ψ → ¬¬ψ... wait that's ψ → ¬(¬ψ).
  -- But ¬(¬ψ) = (ψ→⊥)→⊥. And ψ → ((ψ→⊥)→⊥). This is just implyK applied differently.
  -- Hmm, actually ψ → ((ψ→⊥)→⊥) is NOT implyK. Let me think.
  -- We need: [ψ, ψ→⊥] ⊢ ⊥. Then DT: [ψ] ⊢ (ψ→⊥)→⊥. Then DT: [] ⊢ ψ→(ψ→⊥)→⊥.
  -- [ψ, ψ→⊥] ⊢ ⊥: MP on assumption(ψ→⊥) and assumption(ψ).

  -- Specifically: □φ → ¬¬□φ = □φ → ((□φ→⊥)→⊥) = □φ → ¬(¬□φ).
  -- We need: if □□φ ∈ T, then □(¬(¬□φ)) ∈ T.
  -- From □φ → ¬¬□φ (derivable), K gives □(□φ) → □(¬¬□φ).
  -- But wait: □φ → ¬¬□φ is derivable (it's ψ → ¬¬ψ with ψ=□φ).
  -- So ⊢ □φ → ¬¬□φ. Necessitation: ⊢ □(□φ → ¬¬□φ).
  -- K: □(□φ → ¬¬□φ) → (□□φ → □¬¬□φ). So □□φ → □¬¬□φ.
  -- We have □□φ ∈ T, so □¬¬□φ ∈ T. But ¬¬□φ = ¬(¬□φ).
  -- So □(¬(¬□φ)) ∈ T. This contradicts h_box_dne_not_T.

  -- Let me implement this derivation and use mcs_mp_axiom / closed_under_derivation.
  -- First, derive ⊢ □φ → ¬¬□φ (= ⊢ □φ → ((□φ→⊥)→⊥)):
  -- [□φ, □φ→⊥] ⊢ ⊥ by MP
  -- DT: [□φ] ⊢ (□φ→⊥)→⊥
  -- DT: [] ⊢ □φ → ((□φ→⊥)→⊥)
  -- This is DNI.

  -- Then: ⊢ □(□φ → ((□φ→⊥)→⊥)) by necessitation
  -- K: □(□φ → ((□φ→⊥)→⊥)) → (□□φ → □((□φ→⊥)→⊥))
  -- So □□φ ∈ T → □((□φ→⊥)→⊥) ∈ T.
  -- I.e., □(¬(¬□φ)) ∈ T.
  -- But h_box_dne_not_T says □(¬(¬□φ)) ∉ T. Contradiction.

  -- Build the derivation of □φ → ¬¬□φ (DNI for □φ)
  let bp := Proposition.box φ
  -- [bp.imp .bot, bp] ⊢ ⊥: MP of assumption(bp.imp .bot) and assumption(bp)
  have d_bot : DerivationTree [bp.imp .bot, bp] Proposition.bot :=
    .modus_ponens [bp.imp .bot, bp] bp .bot
      (.assumption _ (bp.imp .bot) (by simp [List.mem_cons]))
      (.assumption _ bp (by simp [List.mem_cons]))
  -- DT on bp.imp .bot: [bp] ⊢ (bp→⊥)→⊥
  have d_dne := deduction_theorem [bp] (bp.imp .bot) .bot d_bot
  -- DT on bp: [] ⊢ bp → ((bp→⊥)→⊥)
  have d_dni := deduction_theorem [] bp ((bp.imp .bot).imp .bot) d_dne
  -- Necessitation: [] ⊢ □(bp → ((bp→⊥)→⊥))
  have d_nec := DerivationTree.necessitation _ d_dni
  -- □(bp → ¬¬bp) ∈ T via closed_under_derivation
  have h_box_dni_T : Proposition.box (bp.imp ((bp.imp .bot).imp .bot)) ∈ T.val :=
    modal_closed_under_derivation T.property (L := []) (fun _ h => nomatch h) ⟨d_nec⟩
  -- K: □(bp → ¬¬bp) → (□bp → □¬¬bp)
  -- mcs_box_mp gives □¬¬bp ∈ T from □(bp → ¬¬bp) ∈ T and □bp ∈ T.
  -- Wait, mcs_box_mp takes □(φ→ψ) and □φ. Here φ=bp, ψ=¬¬bp=(bp→⊥)→⊥.
  -- We have □(bp → (bp→⊥)→⊥) ∈ T and □bp ∈ T (= □□φ ∈ T = h_bb_T).
  have h_box_dne_T := mcs_box_mp T.property h_box_dni_T h_bb_T
  -- h_box_dne_T : □((bp→⊥)→⊥) ∈ T
  -- = □(¬(¬(□φ))) ∈ T = □(Proposition.neg (Proposition.neg (Proposition.box φ))) ∈ T
  -- This should be the same as Proposition.box (Proposition.neg (Proposition.neg (Proposition.box φ)))
  -- But let me check: bp = Proposition.box φ.
  -- (bp→⊥)→⊥ = ((Proposition.box φ).imp .bot).imp .bot
  -- Proposition.neg (Proposition.neg (Proposition.box φ))
  -- = Proposition.neg ((Proposition.box φ).imp .bot)
  -- = ((Proposition.box φ).imp .bot).imp .bot
  -- Yes! These are definitionally equal since neg is abbrev.
  exact h_box_dne_not_T h_box_dne_T

/-! ## Truth Lemma -/

/-- **Truth Lemma**: For any canonical world `S` and formula `φ`,
`Satisfies (CanonicalModel Atom) S φ ↔ φ ∈ S.val`.

Proved by structural induction on `φ`:
- `atom p`: By definition of canonical valuation.
- `bot`: `False ↔ ⊥ ∈ S.val` (⊥ is never in an MCS).
- `imp φ ψ`: From the implication property and negation completeness.
- `box φ`: Forward from canonical accessibility; reverse from box_witness. -/
theorem truth_lemma (S : CanonicalWorld Atom) :
    (φ : Proposition Atom) → (Satisfies (CanonicalModel Atom) S φ ↔ φ ∈ S.val)
  | .atom p => by
    -- By definition: Satisfies ... S (atom p) = CanonicalModel.v S p = (atom p) ∈ S.val
    constructor
    · intro h; exact h
    · intro h; exact h
  | .bot => by
    constructor
    · intro h; exact absurd h id
    · intro h; exact absurd h (mcs_bot_not_mem S.property)
  | .imp φ ψ => by
    constructor
    · -- Forward: Satisfies m S (φ → ψ) → (φ → ψ) ∈ S
      intro h_sat
      -- h_sat : Satisfies m S φ → Satisfies m S ψ
      -- By negation completeness: either (φ → ψ) ∈ S or ¬(φ → ψ) ∈ S.
      rcases modal_negation_complete S.property (φ.imp ψ) with h | h
      · exact h
      · -- ¬(φ → ψ) ∈ S, i.e., (φ → ψ) → ⊥ ∈ S.
        -- ¬(φ → ψ) means "φ and ¬ψ" classically.
        -- From ¬(φ → ψ) we can derive φ and ¬ψ.
        -- φ derivable from ¬(φ → ψ) via Peirce:
        -- We need φ ∈ S. Use Peirce: ((φ→ψ)→φ)→φ.
        -- Since (φ→ψ)→⊥ ∈ S and ⊥→φ ∈ S (EFQ), we can derive (φ→ψ)→φ.
        -- Actually simpler: from (φ→ψ)→⊥ ∈ S, derive φ ∈ S.
        -- Derivation: Peirce gives ((φ→ψ)→φ)→φ.
        -- We need (φ→ψ)→φ. From (φ→ψ)→⊥ and ⊥→φ:
        -- If φ→ψ, then ⊥ (by our hyp), then φ (by EFQ). So (φ→ψ)→φ.
        -- By Peirce: φ.
        -- Then ψ by h_sat (truth lemma IH for φ).
        -- But also ¬ψ ∈ S (derivable from ¬(φ→ψ)).
        -- Contradiction with ψ ∈ S and ¬ψ ∈ S.

        -- Derive φ ∈ S from ¬(φ→ψ) ∈ S:
        -- We need: ¬(φ→ψ) → φ is derivable.
        -- Proof: Peirce(φ,ψ): ((φ→ψ)→φ)→φ.
        -- And: ¬(φ→ψ) → ((φ→ψ)→φ) via EFQ: ¬(φ→ψ) → ((φ→ψ) → ⊥), then ⊥ → φ.
        -- Compose: from (φ→ψ)→⊥, derive (φ→ψ)→φ: assume (φ→ψ), then ⊥ (by negation), then φ (by EFQ).
        -- Then by Peirce: φ.
        -- So (φ→ψ→⊥) → φ is derivable.

        -- Build: (φ→ψ) → ⊥ ∈ S, need φ ∈ S.
        -- Derive via closed_under_derivation from [(φ.imp ψ).imp .bot]:
        -- 1. Assumption: (φ→ψ)→⊥
        -- 2. Need to build a derivation of φ from [(φ→ψ)→⊥].
        -- [(φ→ψ)→⊥] ⊢ φ:
        -- Peirce: ((φ→ψ)→φ)→φ (axiom, weakened to context)
        -- Need [(φ→ψ)→⊥] ⊢ (φ→ψ)→φ
        -- Assume φ→ψ in context: [(φ→ψ)→⊥, φ→ψ] ⊢ φ
        -- MP: ⊥ from assumption (φ→ψ)→⊥ and assumption (φ→ψ)
        -- EFQ: ⊥ → φ. So ⊥ gives φ.
        -- DT: [(φ→ψ)→⊥] ⊢ (φ→ψ)→φ
        -- Peirce + MP: [(φ→ψ)→⊥] ⊢ φ

        -- This gives φ ∈ S.
        exfalso
        have h_phi_S : φ ∈ S.val := by
          apply modal_closed_under_derivation S.property (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          -- Build [(φ→ψ)→⊥] ⊢ φ
          let ctx := [(φ.imp ψ).imp Proposition.bot]
          -- [(φ→ψ)→⊥, φ→ψ] ⊢ ⊥
          have d_bot : DerivationTree (ctx ++ [φ.imp ψ]) Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons, ctx]))
              (.assumption _ _ (by simp [List.mem_cons, ctx]))
          -- DT: [(φ→ψ)→⊥] ⊢ (φ→ψ)→⊥... wait, that's just the assumption.
          -- Let me redo this more carefully.
          -- ctx = [(φ→ψ)→⊥]
          -- [φ→ψ, (φ→ψ)→⊥] ⊢ ⊥: MP of assumption(φ→ψ→⊥) and assumption(φ→ψ)
          have d_bot' : DerivationTree [φ.imp ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              (.assumption _ _ (by simp [List.mem_cons]))
          -- EFQ: [φ→ψ, (φ→ψ)→⊥] ⊢ φ
          have d_efq : DerivationTree [φ.imp ψ, (φ.imp ψ).imp .bot] φ :=
            .modus_ponens _ .bot φ
              (.weakening [] _ _ (.ax [] _ (.efq φ)) (fun _ h => nomatch h))
              d_bot'
          -- DT: [(φ→ψ)→⊥] ⊢ (φ→ψ) → φ
          have d_dt := deduction_theorem [(φ.imp ψ).imp .bot] (φ.imp ψ) φ d_efq
          -- Peirce: ((φ→ψ)→φ)→φ
          have d_peirce : DerivationTree [(φ.imp ψ).imp .bot] (((φ.imp ψ).imp φ).imp φ) :=
            .weakening [] _ _ (.ax [] _ (.peirce φ ψ)) (fun _ h => nomatch h)
          -- MP: [(φ→ψ)→⊥] ⊢ φ
          exact ⟨.modus_ponens _ _ _ d_peirce d_dt⟩
        -- φ ∈ S, so Satisfies ... S φ by IH
        have h_sat_phi := (truth_lemma S φ).mpr h_phi_S
        -- h_sat applied to h_sat_phi gives Satisfies ... S ψ
        have h_sat_psi := h_sat h_sat_phi
        -- ψ ∈ S by IH
        have h_psi_S := (truth_lemma S ψ).mp h_sat_psi
        -- ¬ψ ∈ S: from ¬(φ→ψ) ∈ S, derive ¬ψ.
        -- Actually, ¬(φ→ψ) → ¬ψ is: (φ→ψ)→⊥ → ψ→⊥.
        -- Proof: assume ψ. Then φ→ψ (by implyK: ψ→(φ→ψ)). Then ⊥. So ψ→⊥.
        have h_neg_psi_S : Proposition.neg ψ ∈ S.val := by
          apply modal_closed_under_derivation S.property (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          -- Build [(φ→ψ)→⊥] ⊢ ψ→⊥
          -- [ψ, (φ→ψ)→⊥] ⊢ ⊥:
          -- implyK: ψ→(φ→ψ), so [ψ] ⊢ φ→ψ (by implyK + MP)
          -- Then MP with (φ→ψ)→⊥: ⊥.
          have d_imp : DerivationTree [ψ, (φ.imp ψ).imp .bot] (φ.imp ψ) :=
            .modus_ponens _ ψ (φ.imp ψ)
              (.weakening [] _ _ (.ax [] _ (.implyK ψ φ)) (fun _ h => nomatch h))
              (.assumption _ _ (by simp [List.mem_cons]))
          have d_bot'' : DerivationTree [ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              d_imp
          -- DT: [(φ→ψ)→⊥] ⊢ ψ→⊥
          exact ⟨deduction_theorem [(φ.imp ψ).imp .bot] ψ .bot d_bot''⟩
        exact mcs_bot_not_mem S.property (modal_implication_property S.property h_neg_psi_S h_psi_S)
    · -- Reverse: (φ → ψ) ∈ S → Satisfies m S (φ → ψ)
      intro h_mem h_sat_phi
      -- h_sat_phi : Satisfies m S φ
      -- φ ∈ S by IH
      have h_phi_S := (truth_lemma S φ).mp h_sat_phi
      -- (φ → ψ) ∈ S and φ ∈ S → ψ ∈ S by implication property
      have h_psi_S := modal_implication_property S.property h_mem h_phi_S
      -- ψ ∈ S → Satisfies m S ψ by IH
      exact (truth_lemma S ψ).mpr h_psi_S
  | .box φ => by
    constructor
    · -- Forward: Satisfies m S (□φ) → □φ ∈ S
      -- Satisfies m S (□φ) means ∀ T, R S T → Satisfies m T φ
      intro h_sat
      -- Suppose □φ ∉ S. By box_witness: ∃ T, R S T and φ ∉ T.
      by_contra h_not_box
      obtain ⟨T, hT_mcs, hST, h_phi_not_T⟩ := mcs_box_witness S.property h_not_box
      -- R S T in canonical model
      have h_R : (CanonicalModel Atom).r S ⟨T, hT_mcs⟩ := hST
      -- Satisfies m ⟨T, hT_mcs⟩ φ by h_sat
      have h_sat_T := h_sat ⟨T, hT_mcs⟩ h_R
      -- φ ∈ T by IH
      have h_phi_T := (truth_lemma ⟨T, hT_mcs⟩ φ).mp h_sat_T
      exact h_phi_not_T h_phi_T
    · -- Reverse: □φ ∈ S → Satisfies m S (□φ)
      -- □φ ∈ S means ∀ T, R S T → φ ∈ T (by definition of canonical R)
      intro h_box T hST
      -- R S T: ∀ ψ, □ψ ∈ S → ψ ∈ T
      have h_phi_T := hST φ h_box
      -- φ ∈ T → Satisfies m T φ by IH
      exact (truth_lemma T φ).mpr h_phi_T

/-! ## Completeness Theorem -/

/-- **Completeness Theorem for S5 Modal Logic**:

If `φ` is valid over all S5 frames (reflexive, transitive, Euclidean), then `φ`
is derivable from the empty context.

**Proof**: By contrapositive. If `φ` is not derivable, then `{¬φ}` is consistent
(otherwise we could derive `φ`). By Lindenbaum's lemma, `{¬φ}` extends to an MCS `M`.
The canonical model is an S5 frame (reflexive, transitive, Euclidean). By the truth
lemma, `M` does not satisfy `φ` (since `¬φ ∈ M`). This contradicts validity. -/
theorem completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable φ := by
  -- Contrapositive: suppose φ is not derivable
  by_contra h_not_deriv
  -- {¬φ} is consistent
  have h_cons : Modal.SetConsistent ({Proposition.neg φ} : Set (Proposition Atom)) := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d⟩
    -- L ⊆ {¬φ} and L ⊢ ⊥
    -- Every element of L is ¬φ.
    -- Case: L = [] or L = [¬φ] or L = [¬φ, ¬φ, ...] (all ¬φ).
    -- If L = []: ⊢ ⊥ means ⊥ is derivable, hence φ is derivable (by EFQ), contradiction.
    -- If ¬φ ∈ L: L ⊢ ⊥, weaken to [¬φ] ⊢ ⊥ (since L ⊆ {¬φ} means all elements are ¬φ).
    -- Then DT: ⊢ ¬φ → ⊥ = ⊢ (φ→⊥)→⊥.
    -- By Peirce + EFQ (same as in box_witness): ⊢ φ. Contradiction with h_not_deriv.
    -- Weaken d to [¬φ]
    have d_weak : DerivationTree [Proposition.neg φ] Proposition.bot :=
      .weakening L [Proposition.neg φ] .bot d (fun x hx => by
        have := hL x hx; simp at this; exact List.mem_cons.mpr (Or.inl this))
    -- DT: ⊢ ¬φ → ⊥ = ⊢ (φ→⊥)→⊥
    have d_dne := deduction_theorem [] (Proposition.neg φ) .bot d_weak
    -- Derive φ from (φ→⊥)→⊥ using Peirce + EFQ (same as box_witness)
    let neg_phi := Proposition.neg φ
    have efq : DerivationTree (Atom := Atom) [] (Proposition.bot.imp φ) :=
      .ax [] _ (.efq φ)
    have ik : DerivationTree (Atom := Atom) [] ((Proposition.bot.imp φ).imp (neg_phi.imp (Proposition.bot.imp φ))) :=
      .ax [] _ (.implyK (Proposition.bot.imp φ) neg_phi)
    have step_k := DerivationTree.modus_ponens [] _ _ ik efq
    have is_ax : DerivationTree (Atom := Atom) []
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .ax [] _ (.implyS neg_phi Proposition.bot φ)
    have step_s := DerivationTree.modus_ponens [] _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens [] _ _ step_s d_dne
    have peirce_ax : DerivationTree (Atom := Atom) [] (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .ax [] _ (.peirce φ Proposition.bot)
    have d_phi := DerivationTree.modus_ponens [] _ _ peirce_ax step3
    exact h_not_deriv ⟨d_phi⟩
  -- Extend {¬φ} to MCS M
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  -- ¬φ ∈ M
  have h_neg_in_M : Proposition.neg φ ∈ M := hM_sup (Set.mem_singleton _)
  -- φ ∉ M
  have h_phi_not_M : φ ∉ M := mcs_not_mem_of_neg hM_mcs h_neg_in_M
  -- The canonical model is an S5 frame
  let w : CanonicalWorld Atom := ⟨M, hM_mcs⟩
  -- Apply validity to canonical model at world w
  have h_sat := h_valid (CanonicalWorld Atom) (CanonicalModel Atom)
    canonical_refl
    canonical_trans
    canonical_eucl
    w
  -- By truth lemma: φ ∈ M
  have h_phi_M := (truth_lemma w φ).mp h_sat
  -- Contradiction
  exact h_phi_not_M h_phi_M

end Cslib.Logic.Modal
