/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Languages.Congruences.RightCongruence

@[expose] public section

/-! # Deterministic automaton corresponding to a right congruence. -/

namespace Cslib

open scoped FLTS RightCongruence

variable {Symbol : Type*}

/-- Every right congruence gives rise to a DA whose states are the equivalence classes of
the right congruence, whose start state is the empty word, and whose transition functiuon
is concatenation on the right of the input symbol. Note that the transition function is
well-defined only because `c` is a right congruence. -/
@[scoped grind =]
def RightCongruence.toDA [c : RightCongruence Symbol] : Automata.DA (Quotient c.eq) Symbol where
  tr s x := Quotient.lift (fun u ↦ ⟦ u ++ [x] ⟧) (by
    intro u v h_eq
    apply Quotient.sound
    exact right_cov.elim [x] h_eq
  ) s
  start := ⟦ [] ⟧

namespace Automata.DA

variable [c : RightCongruence Symbol]

/-- After consuming a finite word `xs`, `c.toDA` reaches the state `⟦ xs ⟧` which is
the equivalence class of `xs`. -/
@[simp, scoped grind =]
theorem congr_mtr_eq {xs : List Symbol} :
    c.toDA.mtr c.toDA.start xs = ⟦ xs ⟧ := by
  generalize h_rev : xs.reverse = ys
  induction ys generalizing xs
  case nil => grind [List.reverse_eq_nil_iff]
  case cons y ys h_ind =>
    obtain ⟨rfl⟩ := List.reverse_eq_cons_iff.mp h_rev
    specialize h_ind (xs := ys.reverse) (by grind)
    grind [Quotient.lift_mk]

namespace FinAcc

open Acceptor RightCongruence

/-- The language of `c.toDA` with a single accepting state `s` is exactly
the equivalence class corresponding to `s`. -/
@[simp]
theorem congr_language_eq {a : Quotient c.eq} : language (FinAcc.mk c.toDA {a}) = eqvCls a := by
  ext
  grind

end FinAcc

end Automata.DA

end Cslib
