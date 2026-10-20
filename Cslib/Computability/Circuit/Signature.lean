/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Init

/-!
# Signatures and interpretations

A `Signature` specifies operation symbols with finite arities. The set of symbols
may be infinite, and their arities need not have a uniform bound.
An `Interpretation` assigns each symbol an operation on a carrier type.
Programs and circuits keep the signature separate from its interpretation.
-/

@[expose] public section

namespace Cslib.Circuits

universe v

/-- A collection of operation symbols, each with a fixed finite arity. -/
structure Signature where
  /-- The operation symbols of the signature. -/
  Op : Type v
  /-- The number of arguments taken by each operation symbol. -/
  Arity : Op → Nat

/-- An interpretation assigns an operation on `Carrier` to every symbol in `σ`. -/
abbrev Interpretation (σ : Signature) (Carrier : Type*) :=
  (op : σ.Op) → (Fin (σ.Arity op) → Carrier) → Carrier

/-- An operation with labels for all constants and operations of arity k. -/
inductive FullOp (k : Nat) Carrier where
  | fn : ((Fin k -> Carrier) -> Carrier) -> FullOp k Carrier
  | con : Carrier → FullOp k Carrier

/-- The signature for FullOp. -/
def fullSignature (k : Nat) (Carrier : Type v) : Signature where
  Op := FullOp k Carrier
  Arity op := match op with
    | .fn _ => k
    | .con _ => 0

/-- The natural interpretation for FullOp, where we evaluate each constant
and function to itself. -/
def fullInterpretation : Interpretation (fullSignature k Carrier) Carrier :=
  fun op tuple ↦ match op with
    | .fn f => f tuple
    | .con c => c

end Cslib.Circuits
