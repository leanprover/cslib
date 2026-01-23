/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.DA.Basic

namespace CslibTests

open Cslib.Automata

/-! A simple elevator. -/

inductive Floor where
| one
| two
deriving DecidableEq

def Floor.fintype : Fintype Floor := {
  elems := {.one, .two}
  complete floor := by grind [Floor]
}

theorem Floor.finite : Finite Floor := Floor.fintype.finite

inductive Direction where
| up
| down
deriving DecidableEq

def Direction.fintype : Fintype Direction := {
  elems := {.up, .down}
  complete dir := by grind [Direction]
}

theorem Direction.finite : Finite Direction := Direction.fintype.finite

def tr (floor : Floor) (dir : Direction) : Floor :=
  match floor, dir with
  | .one, .up => .two
  | .one, .down => .one
  | .two, .up => .two
  | .two, .down => .one

def elevator : DA Floor Direction := {
  tr := tr
  start := .one
}

end CslibTests
