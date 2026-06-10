/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Temporal.ProofSystem.Axioms
public import Cslib.Logics.Temporal.ProofSystem.Derivation
public import Cslib.Logics.Temporal.ProofSystem.Derivable
public import Cslib.Logics.Temporal.ProofSystem.Instances

/-! # Temporal Proof System

Barrel import for the temporal proof system modules:
- `Axioms`: Concrete axiom inductive with 26 constructors and FrameClass
- `Derivation`: Type-valued DerivationTree with 6 inference rules
- `Derivable`: Prop-valued derivability wrapper
- `Instances`: TemporalBXHilbert instance for Temporal.HilbertBX
-/

@[expose] public section

