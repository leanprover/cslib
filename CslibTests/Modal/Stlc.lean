/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Safety
import Cslib.Logics.Modal.Lean.Basic
import Cslib.Foundations.Relation.Preserves

/-! # Modal logic for type safety (exemplified on the simply typed λ-calculus)

This file exemplifies how to use modal logic to derive results about programming languages (or
similar models).

In theory of programming languages, type safety is typically established by proving two results:
- **Progress:** a well-typed term is either a value or can take another step.
- **Preservation:** if a well-typed term can take a step, the result is well-typed.

Safety (or soundness) for multistep executions is then derived by combining these two results,
yielding the property that a well-typed term can never get stuck.
This strategy has been popularised with the slogan 'safety = progress + preservation'.

We demonstrate how this strategy can be formalised in CSLib's modal logic for the simply typed
λ-calculus, and how the usual result can be extracted from this development.

We consider a model where worlds are λ-calculus terms and the accessibility relation is single step
full β-reduction. In this model, progress and preservation become:

- **Progress**: `HasType τ → IsValue ∨ ◇IsTerm`;
- **Preservation**: `HasType τ → □HasType τ`.

The proofs of these results are lifted from `Stlc`. Thereon, the development uses reasoning on modal
judgements.
1. From progress and preservation, we derive single step safety: `HasType τ → IsValue ∨ ◇HasType τ`.
2. From preservation for the single step model, we derive the same proposition
   (`HasType τ → □HasType τ`) for the multistep model (where the accessibility relation is multistep
   full β-reduction).
3. We stratify the multistep model on top of the single step model by means of an atomic
   proposition, `IsSingleStepSafe τ t`, defined as
   `⇓Modal[singleStepModel,t ⊨ IsValue ∨ ◇HasType τ]`. (This would not be necessary with multimodal
   logic, as we could use different modalities for single- and multistep reductions.)
4. Using the above and Axiom K, we derive type safety in the multistep model:
   `HasType τ → □IsSingleStepSafe τ`.
5. The standard type safety statement is trivially extracted by unfolding the semantics of step (4).

## References

- * [B. Pierce, *Types and Programming Languages*][Pierce2002]
-/

namespace CslibTests.LambdaCalculus.Stlc.Modal

open Cslib Logic Modal LambdaCalculus LocallyNameless Stlc Untyped Term Relation
open scoped Satisfies Term InferenceSystem

variable {Var : Type*} [HasFresh Var]

/-! ## Modal models of λ-calculus terms -/

/-- Atoms are ordinary predicates on λ-terms. -/
abbrev LAtom Var := Term Var → Prop

/-- Modal propositions over predicates on λ-terms. -/
abbrev LProposition Var := Proposition (LAtom Var)

/-- The single step model of full β-reduction. -/
abbrev singleStepModel : Model (Term Var) (LAtom Var) := Model.ofPredicates (· ⭢βᶠ ·)

/-- The multistep model of full β-reduction. -/
abbrev multiStepModel : Model (Term Var) (LAtom Var) := Model.ofPredicates (· ↠βᶠ ·)

/-! ## Atomic modal propositions on terms -/

/-- A closed term has type `τ`. -/
abbrev HasType (τ : Ty Base) : LProposition Var := (Typing (Var := Var) [] · τ)

/-- A term is a value. -/
abbrev IsValue : LProposition Var := Term.Value (Var := Var)

/-- The proposition satisfied by every term.

Consequently, `◇IsTerm` expresses the existence of an accessible term.
-/
abbrev IsTerm : LProposition Var := fun _ : Term Var => True

/-! ## A generic modal principle -/

/-- The abstract modal core of the standard `safety = progress + preservation` argument.

Suppose that whenever `φ₁` holds:

* every successor satisfies `φ₂` (preservation); and
* either `φ₃` already holds or some successor satisfying `φ₄` exists (progress).

Then either `φ₃` already holds or some successor satisfies `φ₂`.
-/
theorem safety_of_preservation_progress (hpres : ⇓Modal[m,w ⊨ φ₁ → □φ₂])
    (hprog : ⇓Modal[m,w ⊨ φ₁ → φ₃ ∨ ◇φ₄]) : ⇓Modal[m,w ⊨ φ₁ → φ₃ ∨ ◇φ₂] := by
  have : ⇓Modal[m, w ⊨ □φ₂ ∧ ◇φ₄ → ◇φ₂] := by grind only [modal]
  grind only [modal]

/-! ## Modal lifting of progress and preservation -/

/-- Modal view of single step typing preservation. -/
theorem preservation_singleStepModel_modal (τ : Ty Base) (t : Term Var) :
    ⇓Modal[singleStepModel, t ⊨ HasType τ → □HasType τ] := by
  classical
  exact ((Satisfies.ofPredicates_preserves_iff (· ⭢βᶠ ·)).mpr (FullBeta.preservation (τ := τ))) t

omit [HasFresh Var] in
/-- Modal view of single step progress. -/
theorem progress_modal (τ : Ty Base) (t : Term Var) :
    ⇓Modal[singleStepModel, t ⊨ HasType τ → IsValue ∨ ◇IsTerm] := by
  rw [Satisfies.imp_iff_imp]
  intro ht
  rcases FullBeta.progress ht <;> grind only [modal, = Satisfies.diamond_iff_exists]

/-! ## Modal development of type safety

From this point on, the development uses only generic relational and modal principles; no further
STLC-specific reasoning is required.
-/

/-- Modal view of multistep typing preservation. -/
theorem preservation_multiStep_modal (τ : Ty Base) (t : Term Var) :
    ⇓Modal[multiStepModel, t ⊨ HasType τ → □HasType τ] :=
  Satisfies.ofPredicates_preserves_reflTransGen (preservation_singleStepModel_modal τ ·) t

/-- Modal view that preservation and progress give single step safety. -/
theorem type_safety_singleStep_modal (τ : Ty Base) (t : Term Var) :
    ⇓Modal[singleStepModel,t ⊨ HasType τ → IsValue ∨ ◇HasType τ] :=
  safety_of_preservation_progress (preservation_singleStepModel_modal τ t) (progress_modal τ t)

/-- Single step safety, viewed as an atomic property of terms. -/
abbrev IsSingleStepSafe (τ : Ty Base) : LProposition Var :=
  fun t : Term Var => ⇓Modal[singleStepModel,t ⊨ IsValue ∨ ◇HasType τ]

/-- Modal type safety for finite executions.

The outer `□` is interpreted in `multiStepModel`, whereas `IsSingleStepSafe` reifies a
modal judgement in `singleStepModel`.
-/
theorem type_safety_modal (τ : Ty Base) (t : Term Var) :
    ⇓Modal[multiStepModel,t ⊨ HasType τ → □IsSingleStepSafe τ] := by
  have hpres := preservation_multiStep_modal (Var := Var) τ t
  have hsafety : ⇓Modal[multiStepModel,t ⊨ □(HasType τ → IsSingleStepSafe τ)] := by
    rw [Satisfies.box_iff_forall]
    intro t'
    grind only [modal, type_safety_singleStep_modal (Var := Var) τ t']
  -- Axiom K instantiated for single step type safety
  have hk : ⇓Modal[multiStepModel,t ⊨
        □(HasType τ → IsSingleStepSafe τ) → (□HasType τ → □IsSingleStepSafe τ)] :=
    Satisfies.der_of_axiom (Satisfies.k multiStepModel.r _ _)
  grind only [modal]

/-- Type safety: if a term is well-typed, any term it can reach is either a value or can progress.
-/
theorem type_safety {t t' : Term Var} {τ : Ty Base} (ht : [] ⊢ t ∶ τ)
    (hsteps : t ↠βᶠ t') : t'.Value ∨ ∃ t'', t' ⭢βᶠ t'' ∧ [] ⊢ t'' ∶ τ := by
  grind only [modal, type_safety_modal (Var := Var) τ t, Satisfies.box_iff_forall,
    Satisfies.diamond_iff_exists]

end CslibTests.LambdaCalculus.Stlc.Modal
