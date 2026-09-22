/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Languages.StatefulProcesses.Basic
public import Cslib.Foundations.Syntax.HasSubstitution

/-! # Networks of stateful processes and their semantics

This module defines networks (maps from process names to process terms), as well as their symbolic
and concrete operational semantics.

## Implementation notes

We leverage the fact that networks are functions to formulate the semantics without requiring a
definition of parallel composition.

## References

* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
-/

@[expose] public section

namespace Cslib.StatefulProcesses

open Cslib.Mech

/-! ## Networks and their symbolic semantics -/

/-- A network maps process names to process terms. -/
abbrev Network (Pid Var Val FunId SelLabel ProcName : Type*) :=
  Pid → Process Pid Var Val FunId SelLabel ProcName

/-- The 0 ('zero') network, mapping all processes to the process term 0. -/
instance : Zero (Network Pid Var Val FunId SelLabel ProcName) := ⟨fun _ => 0⟩

/-- Symbolic transition labels for networks. -/
inductive Network.TrLabel Pid Var Val FunId SelLabel
  | local (p : Pid) (μ : Act Pid Var Val FunId SelLabel)
  | com (p : Pid) (e : Expr Var Val FunId) (q : Pid) (x : Var)
  | sel (p : Pid) (q : Pid) (l : SelLabel)

variable [DecidableEq Pid]

/-- Symbolic transition relation for networks. -/
inductive Network.Tr :
    Network Pid Var Val FunId SelLabel ProcName → TrLabel Pid Var Val FunId SelLabel →
    Network Pid Var Val FunId SelLabel ProcName → Prop
  | local
    (hμ : μ.isInternal) (htr : Process.lts.Tr (n p) μ prP)
    (hn' : n' = n[p := prP]) :
    Tr n (TrLabel.local p μ) n'
  | com
    (hsend : Process.lts.Tr (n p) (.sendValue q e) prP)
    (hrecv : Process.lts.Tr (n q) (.recvValue p x) prQ)
    (hn' : n' = n[p := prP][q := prQ]) :
    Tr n (TrLabel.com p e q x) n'
  | sel
    (hsend : Process.lts.Tr (n p) (.sendLabel q l) prP)
    (hrecv : Process.lts.Tr (n q) (.recvLabel p l) prQ)
    (hn' : n' = n[p := prP][q := prQ]) :
    Tr n (TrLabel.sel p q l) n'

/-- Symbolic LTS of networks. -/
def Network.lts :
    LTS (Network Pid Var Val FunId SelLabel ProcName) (TrLabel Pid Var Val FunId SelLabel) :=
  ⟨Network.Tr⟩

/-! ## Stores, evaluation, and concrete semantics of networks -/

/-- Configurations, consisting of a network and a global store. -/
structure Cfg (Pid Var Val FunId SelLabel ProcName : Type*) where
  /-- The network of the configuration. -/
  net : Network Pid Var Val FunId SelLabel ProcName
  /-- The global store of the configuration. -/
  store : GlobalStore Pid Var Val

/-- Transition labels for network configurations.

These labels model what can be observed from execution, and thus hide internal computational
details.
-/
inductive Cfg.TrLabel Pid Val SelLabel
  | local (p : Pid)
  | com (p : Pid) (q : Pid) (v : Val)
  | sel (p : Pid) (q : Pid) (l : SelLabel)

/-- Transition relation for network configurations. -/
inductive Cfg.Tr [DecidableEq Var] (isTrue : Val → Bool) (Eval : FunCallEval FunId Val) :
    Cfg Pid Var Val FunId SelLabel ProcName → Cfg.TrLabel Pid Val SelLabel →
    Cfg Pid Var Val FunId SelLabel ProcName → Prop where
  -- Internal actions
  | assign
    (htr : Network.lts.Tr cfg.net (.local p (.assign x e)) cfg'.net)
    (heval : Eval.EvalExpr (cfg.store p) e v)
    (hstore : cfg'.store = cfg.store[(p, x) := v]) :
    Tr isTrue Eval cfg (Cfg.TrLabel.local p) cfg'
  | condThen
    (htr : Network.lts.Tr cfg.net (.local p (.condThen e)) cfg'.net)
    (heval : Eval.EvalExpr (cfg.store p) e v)
    (hguard : isTrue v)
    (hstore : cfg'.store = cfg.store) :
    Tr isTrue Eval cfg (Cfg.TrLabel.local p) cfg'
  | condElse
    (htr : Network.lts.Tr cfg.net (.local p (.condElse e)) cfg'.net)
    (heval : Eval.EvalExpr (cfg.store p) e v)
    (hguard : ¬isTrue v)
    (hstore : cfg'.store = cfg.store) :
    Tr isTrue Eval cfg (Cfg.TrLabel.local p) cfg'
  -- Interactions
  | com
    (htr : Network.lts.Tr cfg.net (.com p e q x) cfg'.net)
    (heval : Eval.EvalExpr (cfg.store p) e v)
    (hstore : cfg'.store = cfg.store[(q, x) := v]) :
    Tr isTrue Eval cfg (Cfg.TrLabel.com p q v) cfg'
  | sel
    (htr : Network.lts.Tr cfg.net (.sel p q l) cfg'.net)
    (hstore : cfg'.store = cfg.store) :
    Tr isTrue Eval cfg (Cfg.TrLabel.sel p q l) cfg'

/-- LTS of network configurations. -/
def Cfg.lts [DecidableEq Var] (isTrue : Val → Bool) (Eval : FunCallEval FunId Val) :
    LTS (Cfg Pid Var Val FunId SelLabel ProcName) (Cfg.TrLabel Pid Val SelLabel) :=
  ⟨Cfg.Tr isTrue Eval⟩

end Cslib.StatefulProcesses
