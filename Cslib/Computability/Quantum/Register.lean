/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Cslib.Init
public import Mathlib.Data.Fintype.Prod

/-!
# Finite quantum registers

`Register` is the finite-dimensional basis interface shared by states, gates,
operators, measurements, and circuits.  `Qubits n` is the specialization whose
basis labels are the current big-endian `Fin (2^n)` computational basis.
-/

@[expose] public section

namespace Cslib.Quantum

/-- A finite-dimensional quantum register. -/
structure Register where
  /-- Basis labels for the register. -/
  Index : Type
  /-- The basis is finite. -/
  fintype : Fintype Index
  /-- Basis labels have decidable equality. -/
  decEq : DecidableEq Index

attribute [instance] Register.fintype Register.decEq

namespace Register

/-- Product/tensor register. -/
def prod (left right : Register) : Register := by
  letI : Fintype left.Index := left.fintype
  letI : DecidableEq left.Index := left.decEq
  letI : Fintype right.Index := right.fintype
  letI : DecidableEq right.Index := right.decEq
  exact
    { Index := left.Index × right.Index
      fintype := inferInstance
      decEq := inferInstance }

end Register

/-- The `n`-qubit register with big-endian computational basis labels. -/
abbrev Qubits (n : Nat) : Register where
  Index := Fin (2 ^ n)
  fintype := inferInstance
  decEq := inferInstance

end Cslib.Quantum
