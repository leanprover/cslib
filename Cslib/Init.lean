/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

import Mathlib.Init
import Cslib.Foundations.Lint.Basic

/-!
# CSLib Initialization

This is the root file in CSLib: it is imported by virtually *all* CSLib files.
For this reason, the imports of this file are carefully curated.

Similar to Mathlib.Init, this file imports linters that should be active by default
throughout the CSLib library.
-/
