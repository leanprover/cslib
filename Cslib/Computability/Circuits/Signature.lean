/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Init

/-!
# Signatures

A signature is a collection of finitary operation symbols, each with a fixed
arity. Signatures carry no semantics: an `Interpretation` assigns concrete
operations to the symbols, and programs and circuits over a signature are
purely syntactic until they are evaluated in an interpretation.
-/

@[expose] public section

namespace Cslib.Circuits

/-- A collection of finitary operation symbols and their arities. -/
structure Signature where
  /-- The operation symbols of the signature. -/
  Op : Type v
  /-- The number of arguments taken by each operation symbol. -/
  Arity : (op : Op) → Nat

end Cslib.Circuits
