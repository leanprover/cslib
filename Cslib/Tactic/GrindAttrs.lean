/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Lean.Meta.Tactic.Grind.RegisterCommand

/-! # CSLib grind sets

This module registers custom grind sets in CSLib.
-/

@[expose] public section

namespace Cslib.Logic.Modal

/--
The `modal` grind set is designed to quickly resolve goals that can be derived from modal reasoning
without unfolding the underlying Lean semantics of satisfaction for modalities. Use this in
combination with modal axioms for more powerful proof search. -/
register_grind_attr modal

end Cslib.Logic.Modal
