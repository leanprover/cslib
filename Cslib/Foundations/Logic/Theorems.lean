/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Theorems.Combinators
public import Cslib.Foundations.Logic.Theorems.Propositional.Core
public import Cslib.Foundations.Logic.Theorems.Propositional.Connectives
public import Cslib.Foundations.Logic.Theorems.BigConj
public import Cslib.Foundations.Logic.Theorems.Modal.Basic
public import Cslib.Foundations.Logic.Theorems.Modal.S5
public import Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived
public import Cslib.Foundations.Logic.Theorems.Temporal.FrameConditions

/-! # Hilbert-Style Theorems

Module aggregator for all theorems derived in the generic typeclass framework.

## Submodules

### Minimal (`[MinimalHilbert S]`)

- `Combinators`: I/B/C/S combinators, imp_trans, pairing, dni
- `Propositional.Core` (minimal section): LEM
- `Propositional.Connectives` (minimal section): contrapose_imp,
  contraposition, iff_intro, iff_neg_intro

### Intuitionistic (`[IntuitionisticHilbert S]`)

- `Propositional.Core` (intuitionistic section): efq_axiom, raa, efq_neg

### Classical (`[ClassicalHilbert S]`)

- `Propositional.Core` (classical section): peirce_axiom, DNE, rcp,
  lce_imp, rce_imp
- `Propositional.Connectives` (classical section): classical_merge,
  contrapose_iff, De Morgan laws
- `BigConj`: bigconj syntax and derivability lemmas

### Modal (`[ModalHilbert S]` / `[ModalS5Hilbert S]`)

- `Modal.Basic`: K-level theorems (box_mono, diamond_mono, k_dist_diamond,
  box_contrapose, modal duality, box_iff_intro)
- `Modal.S5`: S5-level theorems (axiom 5 derivation, t_box_to_diamond,
  box_conj_iff, diamond_disj_iff, s5_diamond_box collapse, nested
  modality theorems)

### Temporal (`[TemporalBXHilbert S]`)

- `Temporal.TemporalDerived`: BX-system derived theorems (guard/event monotonicity
  wrappers, future/past operators, enrichment, self-accumulation, absorption,
  linearity)
- `Temporal.FrameConditions`: Frame condition typeclasses (LinearTemporalFrame,
  SerialFrame, DenseTemporalFrame, DiscreteTemporalFrame)
-/
