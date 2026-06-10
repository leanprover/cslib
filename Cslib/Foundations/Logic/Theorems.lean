/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
import Cslib.Foundations.Logic.Theorems.Combinators
import Cslib.Foundations.Logic.Theorems.Propositional.Core
import Cslib.Foundations.Logic.Theorems.Propositional.Connectives
import Cslib.Foundations.Logic.Theorems.BigConj
import Cslib.Foundations.Logic.Theorems.Modal.Basic
import Cslib.Foundations.Logic.Theorems.Modal.S5
import Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived
import Cslib.Foundations.Logic.Theorems.Temporal.FrameConditions

/-! # Hilbert-Style Theorems

Module aggregator for all theorems derived in the generic typeclass framework.

## Submodules

### Propositional (`[PropositionalHilbert S]`)

- `Combinators`: I/B/C/S combinators, imp_trans, pairing, dni
- `Propositional.Core`: LEM, DNE, raa, efq_neg, rcp, lce_imp, rce_imp
- `Propositional.Connectives`: classical_merge, iff ops, contraposition,
  De Morgan laws
- `BigConj`: bigconj syntax and derivability lemmas

### Modal (`[ModalHilbert S]` / `[ModalS5Hilbert S]`)

- `Modal.Basic`: K-level theorems (box_mono, diamond_mono, k_dist_diamond,
  box_contrapose, modal duality, box_iff_intro)
- `Modal.S5`: S5-level theorems (axiom 5 derivation, t_box_to_diamond,
  box_conj_iff, diamond_disj_iff, s5_diamond_box collapse, nested
  modality theorems)
-/
