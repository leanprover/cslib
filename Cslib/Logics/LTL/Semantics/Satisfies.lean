/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Syntax.Formula

/-! # LTL Satisfaction over Omega-Words

This module defines a basic satisfaction relation for LTL formulas over omega-words.
An omega-word is represented as a valuation `v : ℕ → (Atom → Prop)`, assigning to
each time point `i : ℕ` the set of atoms that hold at that point.

The semantics follow the standard Kripke/Pnueli definition of LTL over ω-sequences.
Connection to `OmegaExecution` from the LTS library is deferred to future work.

## Main definitions

- `Satisfies v i φ` : formula `φ` holds at time `i` in valuation `v`
- `Valid v φ` : `φ` holds at all time points in `v`
- `Satisfiable φ` : `φ` holds at some time point in some valuation

## References

* [A. Pnueli, *The Temporal Logic of Programs*][Pnueli1977]
* [M. Y. Vardi, P. Wolper,
  *An automata-theoretic approach to automatic program verification*][VardiWolper1986]
-/

@[expose] public section

namespace Cslib.Logic.LTL

variable {Atom : Type*}

/-- Satisfaction relation for LTL over omega-words.

`Satisfies v i φ` means formula `φ` holds at time point `i` in the omega-word `v`,
where `v : ℕ → (Atom → Prop)` assigns a set of true atoms to each time point.

The `untl` case: `φ U ψ` holds at `i` when there exists a future time `j ≥ i`
where ψ holds (the event), and φ holds at all intermediate points `i ≤ k < j`
(the guard). -/
def Satisfies (v : ℕ → (Atom → Prop)) (i : ℕ) : Formula Atom → Prop
  | .atom p => v i p
  | .bot => False
  | .imp φ ψ => Satisfies v i φ → Satisfies v i ψ
  | .next φ => Satisfies v (i + 1) φ
  | .untl φ ψ => ∃ j ≥ i, Satisfies v j ψ ∧ ∀ k, i ≤ k → k < j → Satisfies v k φ

/-- A formula holds at all time points in a given omega-word. -/
def Valid (v : ℕ → (Atom → Prop)) (φ : Formula Atom) : Prop :=
  ∀ i, Satisfies v i φ

/-- A formula is satisfiable: it holds at some time point in some omega-word. -/
def Satisfiable (φ : Formula Atom) : Prop :=
  ∃ (v : ℕ → (Atom → Prop)) (i : ℕ), Satisfies v i φ

end Cslib.Logic.LTL

end
