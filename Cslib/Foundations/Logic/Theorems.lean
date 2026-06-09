/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
import Cslib.Foundations.Logic.Theorems.Combinators
import Cslib.Foundations.Logic.Theorems.Propositional.Core
import Cslib.Foundations.Logic.Theorems.Propositional.Connectives
import Cslib.Foundations.Logic.Theorems.Propositional.Reasoning
import Cslib.Foundations.Logic.Theorems.BigConj

/-! # Propositional Hilbert-Style Theorems

Module aggregator for all propositional theorems derived in the
generic `[PropositionalHilbert S]` framework.

## Submodules

- `Combinators`: I/B/C/S combinators, imp_trans, pairing, dni
- `Propositional.Core`: LEM, DNE, raa, efq_neg, rcp, lce_imp, rce_imp
- `Propositional.Connectives`: classical_merge, iff ops, contraposition,
  De Morgan laws
- `Propositional.Reasoning`: bi_imp
- `BigConj`: bigconj syntax and derivability lemmas
-/
