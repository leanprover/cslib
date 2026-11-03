/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Syntax.Congruence

namespace CslibTests

open Cslib

def myRel (n m : ℕ) := n = m

instance : DefaultCongruence ℕ myRel := ⟨⟩

example : (2 : ℕ) ≡ (2 : ℕ) := by rfl
example : (2 : ℕ) ≡[myRel] (2 : ℕ) := by rfl

end CslibTests
