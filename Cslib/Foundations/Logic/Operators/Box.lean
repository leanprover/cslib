/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! # Box modality (□) -/

@[expose] public section

namespace Cslib.Logic

/-- The type `α` has a box modality (`□`). -/
class HasBox (α : Type*) where
  /-- `a` is valid in all immediately reachable states. -/
  box (a : α) : α

@[inherit_doc] scoped prefix:40 "□" => HasBox.box

end Cslib.Logic
