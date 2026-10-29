/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Logic.InferenceSystem

namespace CslibTests

open Cslib.Logic

instance : HasInferenceSystem ℕ := ⟨fun _ => True⟩

open scoped InferenceSystem

-- Tests that the delaboration of `InferenceSystem.Default` in the `⇓` notation works.

/-- info: ⇓5 : Prop -/
#guard_msgs in
#check ⇓5

example : ⇓5 := by dsimp [InferenceSystem.derivation]

end CslibTests
