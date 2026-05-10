
/-
Copyright (c) 2026 Simon Cruanes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Cruanes
-/

module

import Cslib.Init

/-!
# Amortized cost analysis

This complements `TimeM` in the cases where amortized costs are necessary.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Amortized

/-- Physicist method: a potential (lower bound on savings) defined on a
    data structure -/
class Potential α where
  /-- non-negative potential. Initial potential should be 0.
      [Okasaki, *Purely Functional Data Structures*, 1996][okasaki1996] -/
  potential : α → Nat

end Cslib.Algorithms.Lean.Amortized

end
