/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Syntax.Context
public import Cslib.Foundations.Syntax.Congruence

@[expose] public section

namespace Cslib.Logic

/-- A logical equivalence for a given type of `Judgement`s is a congruence on propositions that
preserves validity of judgements. -/
class LogicalEquivalence
    (Proposition : Type u) [HasContext Proposition]
    (Judgement : Type v) [HasHContext Judgement Proposition]
    (Valid : Judgement → Sort w) where
  /-- The logical equivalence relation. -/
  eqv (a b : Proposition) : Prop
  /-- Proof that `eqv` is a congruence. -/
  [congruence : Congruence Proposition eqv]
  /-- Validity is preserved for any judgemental context. -/
  eqv_fill_valid (heqv : eqv a b) (c : HasHContext.Context Judgement Proposition)
    (h : Valid (c<[a])) : Valid (c<[b])

@[inherit_doc]
scoped infix:29 " ≡ " => LogicalEquivalence.eqv

end Cslib.Logic
