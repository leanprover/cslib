/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.ProofSystem.Derivation
public import Cslib.Logics.Bimodal.ProofSystem.Instances
public import Cslib.Logics.Bimodal.Syntax.Formula
public import Cslib.Foundations.Logic.Theorems.Combinators
public import Cslib.Logics.Bimodal.Theorems.Perpetuity.Helpers

/-!
# Combinators - Propositional Reasoning Combinators

This module provides fundamental propositional reasoning combinators for the
Bimodal proof system. Most combinators delegate to the generic Foundations
equivalents via the wrap/unwrap bridge pattern, eliminating redundant proofs.

## Main Combinators

### Propositional Reasoning
- `imp_trans`: Transitivity of implication (hypothetical syllogism)
- `mp`: Modus ponens wrapper
- `identity`: Identity combinator (SKK construction)
- `b_combinator`: B combinator (function composition)
- `theorem_flip`: C combinator (argument flip)

### Application Combinators
- `theorem_app1`: Single application lemma
- `theorem_app2`: Double application lemma (Vireo combinator)

### Conjunction Introduction
- `pairing`: Pairing combinator (derived from app2)
- `combine_imp_conj`: Combine two implications into conjunction
- `combine_imp_conj_3`: Combine three implications into nested conjunction

### Double Negation
- `dni`: Double negation introduction (derived from app1)

## Bridge Pattern

The wrap/unwrap bridge delegates to generic Foundations theorems:
- `unwrap`: Extract `DerivationTree .Base [] φ` from `Nonempty`
- `lift`: Promote from `.Base` to any `fc` via `FrameClass.base_le`
- For input-taking theorems: lift the curried generic form and apply modus
  ponens with concrete inputs at `fc` level.

## References

Ported from BimodalLogic/Theories/Bimodal/Theorems/Combinators.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Theorems.Combinators

open Cslib.Logic
open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Perpetuity (unwrap)

-- Use _root_.Cslib.Logic.Theorems.Combinators to avoid name collision
-- with definitions in this namespace (both under Cslib.Logic.*.Theorems.Combinators)

variable {Atom : Type*}

noncomputable section

/--
Transitivity of implication: if `⊢ A → B` and `⊢ B → C` then `⊢ A → C`.
-/
def imp_trans {fc : FrameClass} {A B C : Formula Atom}
    (h1 : DerivationTree fc [] (A.imp B))
    (h2 : DerivationTree fc [] (B.imp C)) : DerivationTree fc [] (A.imp C) :=
  -- b_combinator: ⊢ (B→C) → (A→B) → (A→C) at Base, lifted to fc
  let curried := DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Combinators.b_combinator _ _ _ Bimodal.HilbertTM _ _ A B C))
  DerivationTree.modus_ponens [] _ _
    (DerivationTree.modus_ponens [] _ _ curried h2) h1

/--
From `⊢ A` and `⊢ A → B`, derive `⊢ B` (modus ponens restated).
-/
def mp {fc : FrameClass} {A B : Formula Atom}
    (h1 : DerivationTree fc [] A) (h2 : DerivationTree fc [] (A.imp B)) :
    DerivationTree fc [] B :=
  DerivationTree.modus_ponens [] A B h2 h1

/--
Identity combinator: `⊢ A → A` (SKK construction).
-/
def identity {fc : FrameClass} (A : Formula Atom) :
    DerivationTree fc [] (A.imp A) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Combinators.identity _ _ _ Bimodal.HilbertTM _ _ A))

/--
B combinator (composition): `⊢ (B → C) → (A → B) → (A → C)`.
-/
def b_combinator {fc : FrameClass} {A B C : Formula Atom} :
    DerivationTree fc [] ((B.imp C).imp ((A.imp B).imp (A.imp C))) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Combinators.b_combinator _ _ _ Bimodal.HilbertTM _ _ A B C))

/--
Flip combinator (C): `⊢ (A → B → C) → (B → A → C)`.
-/
def theorem_flip {fc : FrameClass} {A B C : Formula Atom} :
    DerivationTree fc [] ((A.imp (B.imp C)).imp (B.imp (A.imp C))) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Combinators.theorem_flip _ _ _ Bimodal.HilbertTM _ _ A B C))

/--
Single application lemma (app1): `⊢ A → (A → B) → B`.
-/
def theorem_app1 {fc : FrameClass} {A B : Formula Atom} :
    DerivationTree fc [] (A.imp ((A.imp B).imp B)) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Combinators.theorem_app1 _ _ _ Bimodal.HilbertTM _ _ A B))

/--
Double application lemma (app2): `⊢ A → B → (A → B → C) → C`.
-/
def theorem_app2 {fc : FrameClass} {A B C : Formula Atom} :
    DerivationTree fc [] (A.imp (B.imp ((A.imp (B.imp C)).imp C))) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Combinators.theorem_app2 _ _ _ Bimodal.HilbertTM _ _ A B C))

/--
Pairing combinator: `⊢ A → B → A ∧ B`.
-/
def pairing {fc : FrameClass} (A B : Formula Atom) :
    DerivationTree fc [] (A.imp (B.imp (A.and B))) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Combinators.pairing _ _ _ Bimodal.HilbertTM _ _ A B))

/--
Double negation introduction: `⊢ A → ¬¬A`.
-/
def dni {fc : FrameClass} (A : Formula Atom) :
    DerivationTree fc [] (A.imp A.neg.neg) :=
  DerivationTree.lift (FrameClass.base_le fc)
    (unwrap (@_root_.Cslib.Logic.Theorems.Combinators.dni _ _ _ Bimodal.HilbertTM _ _ A))

/--
Combine two implications into a conjunction implication.

Given `⊢ P → A` and `⊢ P → B`, derive `⊢ P → A ∧ B`.
-/
def combine_imp_conj {fc : FrameClass} {R A B : Formula Atom}
    (hA : DerivationTree fc [] (R.imp A))
    (hB : DerivationTree fc [] (R.imp B)) :
    DerivationTree fc [] (R.imp (A.and B)) :=
  -- pairing: ⊢ A → B → (A ∧ B) at fc
  -- imp_trans hA (pairing A B): ⊢ R → B → (A ∧ B)
  -- Then ImplyS to combine with hB
  let h1 := imp_trans hA (pairing A B)
  let s := DerivationTree.axiom (fc := fc) [] _ (Axiom.imp_k R B (A.and B)) (FrameClass.base_le fc)
  let h2 := DerivationTree.modus_ponens [] (R.imp (B.imp (A.and B))) ((R.imp B).imp (R.imp (A.and B))) s h1
  DerivationTree.modus_ponens [] (R.imp B) (R.imp (A.and B)) h2 hB

/--
Combine three implications into a nested conjunction implication.

Given `⊢ P → A`, `⊢ P → B`, and `⊢ P → C`, derive `⊢ P → A ∧ (B ∧ C)`.
-/
def combine_imp_conj_3 {fc : FrameClass} {R A B C : Formula Atom}
    (hA : DerivationTree fc [] (R.imp A))
    (hB : DerivationTree fc [] (R.imp B))
    (hC : DerivationTree fc [] (R.imp C)) :
    DerivationTree fc [] (R.imp (A.and (B.and C))) :=
  combine_imp_conj hA (combine_imp_conj hB hC)

/--
Derived TF theorem: `□φ → G(□φ)`.
-/
def temp_future_derived {fc : FrameClass} (φ : Formula Atom) :
    DerivationTree fc [] ((Formula.box φ).imp (Formula.allFuture (Formula.box φ))) :=
  let mf_box := DerivationTree.axiom [] _ (Axiom.modal_future (Formula.box φ)) (FrameClass.base_le fc)
  let t_G_box := DerivationTree.axiom [] _ (Axiom.modal_t (Formula.allFuture (Formula.box φ))) (FrameClass.base_le fc)
  let chain1 := imp_trans mf_box t_G_box
  let m4 := DerivationTree.axiom [] _ (Axiom.modal_4 φ) (FrameClass.base_le fc)
  imp_trans m4 chain1

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.Combinators
