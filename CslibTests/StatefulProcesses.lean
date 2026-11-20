/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Languages.StatefulProcesses.Basic
import Cslib.Languages.StatefulProcesses.Network

namespace CslibTests

open Cslib.StatefulProcesses Cslib.Mech

-- Notation

example (x : L.Var α) (e : L.Expr α) :
    (`(SPpre|x ≔ e) : Prefix Pid L SelLabel) =
    (Prefix.assign x e) := by
  rfl

example (x : L.Var α) (e : L.Expr α) :
    (`(SP|x ≔ e; 0) : Process Pid L SelLabel ProcName) =
    Process.pre (Prefix.assign x e) 0 := by
  rfl

-- Semantics

open Cslib
open Cslib.StatefulProcesses.Network

section Hello

/-!
A simple example where `p` sends the string `"Hello"` to `q`.
-/

/-- A simple local signature, where variables are named by Lean names and store strings. -/
abbrev helloLocalSig : LocalSig := ⟨Lean.Name, fun _ => String⟩

/-- A simple stringified signature. -/
abbrev helloSig : Sig Lean.Name := fun _ => helloLocalSig

/-- The variable `x`. -/
def helloX : helloLocalSig.Var String := ⟨`x, rfl⟩

/-- A simple stringified process type. -/
abbrev HelloProcess := Process Lean.Name helloLocalSig String String

/-- A simple stringified network type. -/
abbrev HelloNetwork := Network Lean.Name helloSig String String

def helloNet : HelloNetwork := fun p =>
  if p = `p then `(SP|`q ! {"Hello"}; 0)
  else if p = `q then `(SP|`p ? helloX; 0)
  else 0

/-- A simple stringified configuration type. -/
abbrev HelloCfg := Cfg Lean.Name helloSig String String

def helloCfg : HelloCfg where
  net := helloNet
  store := fun _ => fun _ => ""

def helloLts : LTS HelloCfg (Cfg.TrLabel Lean.Name String) := Cfg.lts

-- Example transition.
-- This is begging for more automation.
example : helloLts.Tr helloCfg (.com `p `q "Hello")
    (Cfg.mk 0 (helloCfg.store[⟨`q, helloX⟩ := "Hello"])) := by
  apply Cfg.Tr.com (hstore := rfl)
  · apply Network.Tr.com (by constructor) (by constructor)
    ext p
    simp only [Pi.zero_apply, helloCfg]
    grind [helloNet]
  · exact .call (.val _) rfl

end Hello

end CslibTests
