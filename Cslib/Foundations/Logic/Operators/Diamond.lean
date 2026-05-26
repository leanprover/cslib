/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! # Diamond modality (◇) -/

@[expose] public section

namespace Cslib.Logic

/-- The type `α` has a diamond modality (`◇`). -/
class HasDiamond (α : Type*) where
  /-- `a` is valid in a reachable state. -/
  diamond (a : α) : α

@[inherit_doc] scoped prefix:40 "◇" => HasDiamond.diamond

end Cslib.Logic
