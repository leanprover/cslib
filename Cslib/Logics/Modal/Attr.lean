/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! # Grind set attribute for modal logic

This module registers the `modal` grind set. To use it, import the `Basic` module of modal logic.

The `modal` grind set is designed to quickly resolve goals that can be derived from modal reasoning
without unfolding the underlying Lean semantics of satisfaction for modalities.
-/

namespace Cslib.Logic.Modal

/-- Attempts to resolve the goal by deriving judgements in modal logic, without unfolding the
underlying Lean semantics of satisfaction for modalities. Use this in combination with modal axioms
for more powerful proof search. -/
register_grind_attr modal

end Cslib.Logic.Modal
