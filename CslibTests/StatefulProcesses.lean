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

example (x : Var) (e : Expr Var Val FunId) :
    (`(SPpre|x ≔ e) : Prefix Pid Var Val FunId SelLabel) =
    (Prefix.assign x e) := by
  rfl

example (x : Var) (e : Expr Var Val FunId) :
    (`(SP|x ≔ e; 0) : Process Pid Var Val FunId SelLabel ProcName) =
    Process.pre (Prefix.assign x e) 0 := by
  rfl

-- Semantics

open Cslib
open Cslib.StatefulProcesses.Network

section Hello

/-!
A simple example where "p" sends the string `"Hello"` to "q".
-/

/-- A simple stringified process type. -/
abbrev HelloProcess := Process String String String String String String

/-- A simple stringified network type. -/
abbrev HelloNetwork := Network String String String String String String

def helloNet : HelloNetwork := fun p =>
  if p = "p" then `(SP|"q"!"Hello"; 0)
  else if p = "q" then `(SP|"p"?"x"; 0)
  else 0

/-- A simple stringified configuration type. -/
abbrev HelloCfg := Cfg String String String String String String

def helloCfg : HelloCfg where
  net := helloNet
  store := fun _ => fun _ => ""

def stringIsTrue (s : String) := s == "true"

/-- All functions evaluate to "⊥". -/
def HelloEval : FunCallEval String String := fun _ _ v => v = "⊥"

def helloLts : LTS HelloCfg (Cfg.TrLabel String String String) := Cfg.lts stringIsTrue HelloEval

-- Example transition.
-- This is begging for more automation.
example : helloLts.Tr helloCfg (.com "p" "q" "Hello")
    (Cfg.mk 0 (helloCfg.store[("q", "x") := "Hello"])) := by
  apply Cfg.Tr.com (heval := FunCallEval.EvalExpr.val) (hstore := rfl)
  apply Network.Tr.com (by constructor) (by constructor)
  ext p
  simp only [Pi.zero_apply, helloCfg, HasSubstitution.subst]
  grind [helloNet]

end Hello

end CslibTests
