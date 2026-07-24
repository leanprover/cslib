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

/-- A logical equivalence `eqv` for an inference system `S` is a congruence on propositions (of type
`α`) that preserves validity of judgements under any judgemental context. -/
class LogicalEquivalence S (eqv : α → α → Prop)
    [Congruence eqv] [HasContext α] [HasHContext Judgement α]
    [InferenceSystem S Judgement] where
  /-- Validity is preserved for any judgemental context. -/
  eqvFillValid (heqv : eqv a b) (c : HasHContext.Context Judgement α)
    (h : S⇓(c<[a])) : S⇓(c<[b])

-- @[inherit_doc]
-- scoped notation a " ≡[" S "]" b => LogicalEquivalence.eqv S a b

-- /-- Class for types (`α`) that have a canonical logical equivalence (under a canonical, default
-- inference system). -/
-- abbrev HasLogicalEquivalence Proposition
--     [DefaultCongruence Proposition]
--     [HasContext Proposition] [HasHContext Judgement Proposition]
--     [HasInferenceSystem Judgement] :=
--   LogicalEquivalence InferenceSystem.Default (DefaultCongruence.r) Judgement

end Cslib.Logic
