/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Pair

@[expose] public section

/-!
# Buchi Congruence

A special type of right congruences used by J.R. Büchi to prove the closure
of ω-regular languages under complementation.
-/

namespace Cslib.Automata.NA.Buchi

open Function

variable {Symbol : Type*} {State : Type}

/-- Given a Buchi automaton `na`, two finite words `u` and `v` are Buchi-congruent
according to `na` iff for every pair of states `s` and `t` of `na`, both of the
following two conditions hold:
(1) `u` can move `na` from `s` to `t` iff `v` can move `na` from `s` to `t`;
(2) `u` can move `na` from `s` to `t` via an acceptingg states iff `v` can move `na`
from `s` to `t` via an acceptingg states. -/
def BuchiCongruence (na : Buchi State Symbol) : RightCongruence Symbol where
  eq.r u v :=
    ∀ {s t}, (u ∈ na.pairLang s t ↔ v ∈ na.pairLang s t) ∧
      (u ∈ na.pairViaLang na.accept s t ↔ v ∈ na.pairViaLang na.accept s t)
  eq.iseqv.refl := by grind
  eq.iseqv.symm := by grind
  eq.iseqv.trans := by grind
  right_cov.elim := by
    grind [Covariant, → LTS.pairLang_split, <= LTS.pairLang_append, → LTS.pairViaLang_split,
      <= LTS.pairViaLang_append_pairLang, <= LTS.pairLang_append_pairViaLang]

open scoped Classical in
/-- `BuchiCongrParam` is a parameterization of the equivalence classes of `na.BuchiCongruence`
using the type `State → State → Prop × Prop`, which is finite if `State` is. -/
noncomputable def BuchiCongrParam (na : Buchi State Symbol)
    (f : State → State → Prop × Prop) : Quotient na.BuchiCongruence.eq :=
  if h : ∃ u, ∀ s t, ((f s t).1 ↔ u ∈ na.pairLang s t) ∧
      ((f s t).2 ↔ u ∈ na.pairViaLang na.accept s t)
  then ⟦ Classical.choose h ⟧
  else ⟦ [] ⟧

variable {na : Buchi State Symbol}

/-- `BuchiCongrParam` is surjective. -/
lemma buchiCongrParam_surjective : Surjective na.BuchiCongrParam := by
  intro q
  let f s t := (q.out ∈ na.pairLang s t, q.out ∈ na.pairViaLang na.accept s t)
  have h : ∃ u, ∀ s t, ((f s t).1 ↔ u ∈ na.pairLang s t) ∧
        ((f s t).2 ↔ u ∈ na.pairViaLang na.accept s t) := by
    use q.out
    grind
  use f
  simp only [BuchiCongrParam, h, ↓reduceDIte]
  rw [← Quotient.out_eq q]
  apply Quotient.sound
  intro s t
  grind

/-- `na.BuchiCongruence` is of finite index if `na` has only finitely many states. -/
theorem buchiCongruence_fin_index [Finite State] : Finite (Quotient na.BuchiCongruence.eq) :=
  Finite.of_surjective na.BuchiCongrParam buchiCongrParam_surjective

end Cslib.Automata.NA.Buchi
