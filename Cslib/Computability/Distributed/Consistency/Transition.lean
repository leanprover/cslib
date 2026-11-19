/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.Consistency.Specification

/-! # Transitions

A transition models an atomic step in a concrete execution and has various attributes
depending on its type.

This file formalizes section 7.1 of [Burckhardt2014].

## References

* [*Principles of Eventual Consistency*][Burckhardt2014]
-/

@[expose] public section

namespace Cslib.DistributedConsistency

variable {State Operation Value Message Process : Type*}

/-- Transtion datatype. -/
inductive Transition (State Operation Value Message Process : Type*)
  /-- Initialization transition. -/
  | init : State → Set Message → Transition State Operation Value Message Process
  /-- Operation call. -/
  | call : Operation → State → State → Set Message →
    Transition State Operation Value Message Process
  /-- Operation call + return transition. -/
  | callret : Operation → State → State → Set Message → Value →
    Transition State Operation Value Message Process
  /-- Message receive transition. -/
  | recv : Message → State → State → Set Message →
    Transition State Operation Value Message Process
  /-- Message receive + return transition. -/
  | recvret : Message → State → State → Set Message → Value →
    Transition State Operation Value Message Process
  /-- Process step transition. -/
  | step : Process → State → State → Set Message →
    Transition State Operation Value Message Process
  /-- Process step + return transition. -/
  | stepret : Process → State → State → Set Message → Value →
    Transition State Operation Value Message Process

namespace Transition

/-! ### Partial functions for accessing the attributes of a transition. -/

/-- The operation of a transition. -/
def op : Transition State Operation Value Message Process → Option Operation
  | call o _ _ _ | callret o _ _ _ _ => some o
  | _ => none

/-- The received message of a transition. -/
def rcv : Transition State Operation Value Message Process → Option Message
  | recv m _ _ _ | recvret m _ _ _ _ => some m
  | _ => none

/-- The process of a transition. -/
def proc : Transition State Operation Value Message Process → Option Process
  | step p _ _ _ | stepret p _ _ _ _ => some p
  | _ => none

/-- The previous state of a transition. -/
def pre : Transition State Operation Value Message Process → Option State
  | call _ s _ _ | callret _ s _ _ _
  | recv _ s _ _ | recvret _ s _ _ _
  | step _ s _ _ | stepret _ s _ _ _ => some s
  | _ => none

/-- The next state of a transition. -/
def post : Transition State Operation Value Message Process → Option State
  | init s' _
  | call _ _ s' _ | callret _ _ s' _ _
  | recv _ _ s' _ | recvret _ _ s' _ _
  | step _ _ s' _ | stepret _ _ s' _ _ => some s'

/-- The set of messages sent by a transition. -/
def snd : Transition State Operation Value Message Process → Set Message
  | init _ ms
  | call _ _ _ ms | callret _ _ _ ms _
  | recv _ _ _ ms | recvret _ _ _ ms _
  | step _ _ _ ms | stepret _ _ _ ms _ => ms

/-- The value returned by a transition. -/
def rval : Transition State Operation Value Message Process → Option Value
  | callret _ _ _ _ v
  | recvret _ _ _ _ v
  | stepret _ _ _ _ v => some v
  | _ => none

end Transition

end Cslib.DistributedConsistency
