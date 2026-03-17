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
deriving DecidableEq, Fintype

inductive Direction where
| up
| down
deriving DecidableEq, Fintype

def elevator : DA Floor Direction where
  tr
  | .one, .up => .two
  | .one, .down => .one
  | .two, .up => .two
  | .two, .down => .one
  start := .one

end CslibTests
