/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Pim Spelier, Daan van Gent
-/

module

public import Mathlib.Computability.Tape

@[expose] public section

namespace Turing

/--
A Turing machine "statement" is just a `Option`al command to move left or right,
and write a symbol (i.e. an `Option Symbol`, where `none` is the blank symbol) on the `BiTape`
-/
structure Stmt (Symbol : Type) where
  /-- The symbol to write at the current head position -/
  symbol : Option Symbol
  /-- The direction to move the tape head -/
  movement : Option Dir
deriving Inhabited

instance inhabitedStmt : Inhabited (Stmt Symbol) := inferInstance

end Turing
