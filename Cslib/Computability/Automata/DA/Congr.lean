/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Languages.Congruences.Basic

/-! # Deterministic automaton corresponding to a right congruence. -/

@[expose] public section

variable {Symbol : Type*}

namespace Language

open Cslib

/-- Every right congruence gives rise to a DA whose states are the equivalence classes of
the right congruence, whose start state is the empty word, and whose transition functiuon
is concatenation on the right of the input symbol. Note that the transition function is
well-defined only because `c` is a right congruence. -/
@[scoped grind =]
def RightCongruence.toDA [c : RightCongruence Symbol] : Automata.DA (Quotient c.eq) Symbol where
  tr s x := Quotient.lift (fun u ↦ ⟦ u ++ [x] ⟧) (by
    intro u v h_eq
    apply Quotient.sound
    exact c.right_cov.elim [x] h_eq
  ) s
  start := ⟦ [] ⟧

end Language

namespace Cslib.Automata.DA

open Language
open scoped FLTS RightCongruence

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

/-- After consuming a finite word `ys` from the state `⟦ xs ⟧`, `c.toDA` reaches
the state `⟦ xs ++ ys ⟧`. -/
@[simp, scoped grind =]
theorem congr_mtr_append {xs ys : List Symbol} :
    c.toDA.mtr ⟦ xs ⟧ ys = ⟦ xs ++ ys ⟧ := by
  nth_rewrite 1 [← congr_mtr_eq, ← FLTS.mtr_append_eq]
  rw [congr_mtr_eq]

namespace FinAcc

open Acceptor RightCongruence

/-- The language of `c.toDA` with a single accepting state `s` is exactly
the equivalence class corresponding to `s`. -/
@[simp]
theorem congr_language_eq {a : Quotient c.eq} : language (FinAcc.mk c.toDA {a}) = eqvCls a := by
  ext
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  constructor <;>
  · intro h
    simpa [mem_language, Accepts, congr_mtr_eq] using! h

end FinAcc

end Cslib.Automata.DA
