/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Algorithms.CCS.VendingMachine

namespace CslibTests

open Cslib CCS Process Algorithms.CCS.VendingMachine

/-- The deterministic vending machine can perform a coin action. -/
example : ltsD.Tr vm Coin (choice (pre Tea (const .vm)) (pre Coffee (const .vm))) :=
  Tr.const rfl Tr.pre

end CslibTests
