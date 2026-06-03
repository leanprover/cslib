/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! -/

@[expose] public section

namespace Cslib

/-- Equality to `Zero` is decidable for all elements of a type (`α`). -/
abbrev DecidableEqZero (α : Type*) [Zero α] := ∀ a : α, Decidable (a = 0)

end Cslib
