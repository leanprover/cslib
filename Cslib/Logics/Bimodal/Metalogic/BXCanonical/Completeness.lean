/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Completeness.Dense

/-!
# BX Completeness

Barrel file for completeness theorems. Currently contains:

- `completeness_dense`: Dense completeness (via Burgess chronicle on Rat)

Pending (task 36, WeakCanonical):
- `completeness_discrete`: Discrete completeness (via succ-embedding on Int)
- `completeness`: General completeness (three-way case split)
-/

@[expose] public section

