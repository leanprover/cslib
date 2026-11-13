/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Languages.StatefulProcesses.Basic

/-! # Networks of stateful processes and their semantics

This module defines networks (maps from process names to process terms), as well as their symbolic
and concrete operational semantics.

## Implementation notes

We leverage the fact that networks are functions to formulate the semantics without requiring a
definition of parallel composition.

Networks are parametrised over a signature `S : Sig Pid`, which maps process names to local
signatures. Each process with name `p` runs a program (`Process`) over its own local signature
`S p`.

## References

* [F. Montesi, *Introduction to Choreographies*][Montesi2023]
-/

@[expose] public section

namespace Cslib.StatefulProcesses

open Cslib.Mech

universe u v w

/-! ## Networks and their symbolic semantics -/

/-- A network maps each participant to a process over its local signature. -/
abbrev Network (Pid : Type u) (S : Sig.{u, v, w} Pid) (SelLabel ProcName : Type*) :=
  (p : Pid) → Process Pid (S p) SelLabel ProcName

instance : Zero (Network Pid S SelLabel ProcName) := ⟨fun _ => 0⟩

/-- Symbolic transition labels for networks. -/
inductive Network.TrLabel (Pid : Type u) (S : Sig.{u, v, w} Pid) (SelLabel : Type*)
  | local (p : Pid) (μ : Act Pid (S p) SelLabel)
  | com {α : Type w} (p : Pid) (e : S.Expr p α) (q : Pid) (x : S.Var q α)
  | sel (p q : Pid) (l : SelLabel)

variable {Pid : Type u} {S : Sig.{u, v, w} Pid} {SelLabel ProcName : Type*} [DecidableEq Pid]

/-- Symbolic transition relation. Communication connects matching value types. -/
inductive Network.Tr : Network Pid S SelLabel ProcName → TrLabel Pid S SelLabel →
    Network Pid S SelLabel ProcName → Prop
  | local {n n' : Network Pid S SelLabel ProcName} {p : Pid} {μ : Act Pid (S p) SelLabel}
      {prP : Process Pid (S p) SelLabel ProcName}
      (hμ : μ.isInternal) (htr : Process.lts.Tr (n p) μ prP)
      (hn' : n' = Function.update n p prP) : Tr n (.local p μ) n'
  | com {n n' : Network Pid S SelLabel ProcName} {p q : Pid} {α : Type w} {e : S.Expr p α}
      {x : S.Var q α} {prP : Process Pid (S p) SelLabel ProcName}
      {prQ : Process Pid (S q) SelLabel ProcName}
      (hsend : Process.lts.Tr (n p) (.sendValue q e) prP)
      (hrecv : Process.lts.Tr (n q) (.recvValue p x) prQ)
      (hn' : n' = Function.update (Function.update n p prP) q prQ) :
      Tr n (.com p e q x) n'
  | sel {n n' : Network Pid S SelLabel ProcName} {p q : Pid} {l : SelLabel}
      {prP : Process Pid (S p) SelLabel ProcName} {prQ : Process Pid (S q) SelLabel ProcName}
      (hsend : Process.lts.Tr (n p) (.sendLabel q l) prP)
      (hrecv : Process.lts.Tr (n q) (.recvLabel p l) prQ)
      (hn' : n' = Function.update (Function.update n p prP) q prQ) :
      Tr n (.sel p q l) n'

/-- Symbolic LTS of networks. -/
def Network.lts : LTS (Network Pid S SelLabel ProcName) (Network.TrLabel Pid S SelLabel) :=
  ⟨Network.Tr⟩

/-- Configurations consist of a network and a local store for every participant. -/
structure Cfg (Pid : Type u) (S : Sig.{u, v, w} Pid) (SelLabel ProcName : Type*) where
  /-- Network. -/
  net : Network Pid S SelLabel ProcName
  /-- The global store, with a local store for every participant. -/
  store : S.Store

/-- Observable labels, including the type and value of each communicated message. -/
inductive Cfg.TrLabel (Pid SelLabel : Type*)
  | local (p : Pid)
  | com {α : Type w} (p q : Pid) (v : α)
  | sel (p q : Pid) (l : SelLabel)

/-- Concrete transitions evaluate local expressions in the acting participant's store. -/
inductive Cfg.Tr :
    Cfg Pid S SelLabel ProcName → Cfg.TrLabel Pid SelLabel →
    Cfg Pid S SelLabel ProcName → Prop where
  | assign {cfg cfg' : Cfg Pid S SelLabel ProcName} {p : Pid} {α} {x : S.Var p α}
      {e : S.Expr p α} {v : α}
      (htr : Network.lts.Tr cfg.net (.local p (.assign x e)) cfg'.net)
      (heval : e.Eval (cfg.store p) v)
      (hstore : cfg'.store = cfg.store[⟨p, x⟩ := v]) :
      Tr cfg (.local p) cfg'
  | condThen {cfg cfg' : Cfg Pid S SelLabel ProcName} {p : Pid} {α} {_ : HasTrue α}
      {e : S.Expr p α}
      (htr : Network.lts.Tr cfg.net (.local p (.condThen e)) cfg'.net)
      (heval : e.Eval (cfg.store p) HasTrue.true)
      (hstore : cfg'.store = cfg.store) :
      Tr cfg (.local p) cfg'
  | condElse {cfg cfg' : Cfg Pid S SelLabel ProcName} {p : Pid} {α} {_ : HasTrue α}
      {e : S.Expr p α} {v : α}
      (htr : Network.lts.Tr cfg.net (.local p (.condElse e)) cfg'.net)
      (heval : e.Eval (cfg.store p) v) (hne : v ≠ HasTrue.true)
      (hstore : cfg'.store = cfg.store) :
      Tr cfg (.local p) cfg'
  | com {cfg cfg' : Cfg Pid S SelLabel ProcName} {p q : Pid} {α} {e : S.Expr p α}
      {x : S.Var q α} {v : α}
      (htr : Network.lts.Tr cfg.net (.com p e q x) cfg'.net)
      (heval : e.Eval (cfg.store p) v)
      (hstore : cfg'.store = cfg.store[⟨q, x⟩ := v]) :
      Tr cfg (.com p q v) cfg'
  | sel {cfg cfg' : Cfg Pid S SelLabel ProcName} {p q : Pid} {l : SelLabel}
      (htr : Network.lts.Tr cfg.net (.sel p q l) cfg'.net)
      (hstore : cfg'.store = cfg.store) : Tr cfg (.sel p q l) cfg'

/-- Concrete LTS of configurations. -/
def Cfg.lts : LTS (Cfg Pid S SelLabel ProcName) (Cfg.TrLabel.{w} Pid SelLabel) := ⟨Cfg.Tr⟩

end Cslib.StatefulProcesses
