/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Syntax.Context
public import Cslib.Foundations.Syntax.Congruence
public import Cslib.Foundations.Logic.InferenceSystem

/-! Typeclass and notation for logical equivalence. -/

@[expose] public section

namespace Cslib.Logic

open scoped InferenceSystem

/-- A logical equivalence for a given type of `Judgement`s is a congruence on propositions that
preserves validity of judgements under any judgemental context. -/
class LogicalEquivalence S
    (Proposition : Type u) [HasContext Proposition]
    (Judgement : Type v) [HasHContext Judgement Proposition]
    [InferenceSystem S Judgement] where
  /-- `a ≡[S] b` means that `a` and `b` are logically equivalent in the inference system `S`. -/
  eqv (a b : Proposition) : Prop
  /-- Proof that `eqv` is a congruence. -/
  [congruence : Congruence Proposition eqv]
  /-- Validity is preserved for any judgemental context. -/
  eqvFillValid (heqv : eqv a b) (c : HasHContext.Context Judgement Proposition)
    (h : S⇓(c<[a])) : S⇓(c<[b])

@[inherit_doc]
scoped notation a " ≡[" S "]" b => LogicalEquivalence.eqv S a b

/-- Class for types (`α`) that have a canonical logical equivalence (under a canonical, default
inference system). -/
abbrev HasLogicalEquivalence (Proposition : Type u) [HasContext Proposition]
    (Judgement : Type v) [HasHContext Judgement Proposition]
    [HasInferenceSystem Judgement] :=
  LogicalEquivalence InferenceSystem.Default Proposition Judgement

/-- `a ≡ b` means that `a` and `b` are logically equivalent. -/
scoped infix:29 " ≡ " => LogicalEquivalence.eqv InferenceSystem.Default

end Cslib.Logic
