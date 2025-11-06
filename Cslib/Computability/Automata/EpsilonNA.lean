/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Automata.NA

/-! # Nondeterministic automata with ε-transitions. -/

namespace Cslib

/-- A nondeterministic finite automaton with ε-transitions (`εNA`) is an `NA` with an `Option`
symbol type. The special symbol ε is represented by the `Option.none` case.

Internally, ε (`Option.none`) is treated as the `τ` label of the underlying transition system,
allowing for reusing the definitions and results on saturated transitions of `LTS` to deal with
ε-closure. -/
structure εNA (State Symbol : Type*) extends NA State (Option Symbol)

structure εNA.FinAcc (State Symbol : Type*) extends εNA State Symbol where
  acc : Set State

variable {State Symbol : Type*}

@[local grind =]
private instance : HasTau (Option α) := ⟨.none⟩

/-- The `ε`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `ε`-transitions. We use `LTS.τClosure` since `ε` (`Option.none`) is an instance
of `HasTau.τ`. -/
abbrev εNA.εClosure (ena : εNA State Symbol) (S : Set State) := ena.τClosure S

namespace εNA

namespace FinAcc

/-- An εNA accepts a string if there is a saturated multistep accepting derivative with that trace
from the start state. -/
@[scoped grind =]
def Accept (enfa : FinAcc State Symbol) (xl : List Symbol) :=
  ∃ s ∈ enfa.acc, ∃ s0 ∈ enfa.toεNA.εClosure enfa.start, enfa.saturate.MTr s0 (xl.map (some ·)) s

@[scoped grind =]
def language (enfa : FinAcc State Symbol) : Language Symbol :=
  { xl : List Symbol | enfa.Accept xl }

@[scoped grind =]
theorem mem_language (enfa : FinAcc State Symbol) (xl : List Symbol) :
    xl ∈ enfa.language ↔
    ∃ s ∈ enfa.acc, ∃ s0 ∈ enfa.toεNA.εClosure enfa.start, enfa.saturate.MTr s0 (xl.map (some ·)) s
    := Iff.rfl

end FinAcc

-- `εNA` will not be used in automata theory on infinite words.

end εNA

end Cslib
