/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Syntax.Context

@[expose] public section

namespace Cslib

/-- An equivalence relation preserved by all contexts. -/
class Congruence (α : Sort*) [HasContext α] (r : α → α → Prop) extends IsEquiv α r where
  /-- Equivalence is preserved by contexts. -/
  is_congruence (a b : α) (c : HasContext.Context α) : r a b → r c[a] c[b]

end Cslib
