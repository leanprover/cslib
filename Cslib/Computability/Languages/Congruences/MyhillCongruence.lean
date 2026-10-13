/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.MyhillNerode

/-! # Myhill congruence

The Myhill congruence of a language `l` is a two-sided congruence that is finer than
the Nerode congruence of the same language `l` (which is a right congruence).  It will be
used to define the syntactic monoid of `l`.

## References

[Holcombe1982] Holcombe, W.M.L. (1982). Algebraic automata theory. Section 5.3
-/

@[expose] public section

variable {α : Type}

namespace Language

open Cslib Language Automata DA FinAcc Acceptor
open scoped RightCongruence

/-- The Myhill congruence of a language `l` is the two-sided congruence on finite words
such that two words are related iff all their two-sided extensions are either both in `l`
or both not in `l`. -/
@[implicit_reducible]
def MyhillCongruence (l : Language α) : Congruence α where
  r x y := ∀ w z, w ++ x ++ z ∈ l ↔ w ++ y ++ z ∈ l
  iseqv.refl := by grind
  iseqv.symm := by grind
  iseqv.trans := by grind
  right_cov.elim := by grind [Covariant]
  left_cov.elim := by grind [Covariant]

/-- The Myhill quotient of a language `l` is the quotient of its Myhill congruence. -/
abbrev MyhillQuotient (l : Language α) := Quotient l.MyhillCongruence.eq

/-- Given a language `l` and a finite word `x`, the Nerode map is a map from the Nerode quotient
to itself induced by the `x`-transition of the Nerode congruence deterministic automaton of `l`. -/
def nerodeMap (l : Language α) (x : List α) : l.NerodeQuotient → l.NerodeQuotient :=
  fun q ↦ l.NerodeCongruenceDA.mtr q x

theorem nerodeMap_append (l : Language α) (x y : List α) :
    l.nerodeMap (x ++ y) = l.nerodeMap y ∘ l.nerodeMap x := by
  ext q
  simp [nerodeMap, FLTS.mtr_append_eq]

theorem nerodeMap_accept (l : Language α) (x : List α) :
    x ∈ l ↔ l.nerodeMap x l.NerodeCongruenceDA.start ∈ l.NerodeCongruenceDA.accept := by
  nth_rewrite 1 [← nerodeCongruenceDA_language_eq l]
  constructor <;> intro <;> assumption

/-- The Myhill congruence is in fact the congruence induced by the Nerode map. -/
theorem myhillCongruence_iff (l : Language α) (x y : List α) :
    l.MyhillCongruence.r x y ↔ l.nerodeMap x = l.nerodeMap y := by
  constructor <;> intro h
  · ext q
    obtain ⟨w, rfl⟩ := Quotient.mk_surjective q
    simp only [nerodeMap, NerodeCongruenceDA, congr_mtr_append, Quotient.eq_iff_equiv]
    exact h w
  · intro w z
    simp [nerodeMap_accept, nerodeMap_append, h]

/-- The Myhill quotient of a regular language is finite. -/
theorem IsRegular.finite_myhillQuotient {l : Language α}
    (h : l.IsRegular) : Finite (l.MyhillQuotient) := by
  have h1 : l.MyhillCongruence.eq = Setoid.ker l.nerodeMap := by
    ext
    exact myhillCongruence_iff _ _ _
  rw [MyhillQuotient, h1]
  have := IsRegular.finite_nerodeQuotient h
  have : Finite (l.NerodeQuotient → l.NerodeQuotient) := inferInstance
  exact Finite.of_injective _ (Setoid.kerLift_injective l.nerodeMap)

/-- The deterministic automaton corresponding to the Myhill congruence of a language `l`. -/
def myhillCongruenceDA (l : Language α) : DA.FinAcc (l.MyhillQuotient) α :=
  FinAcc.mk l.MyhillCongruence.toDA ((⟦·⟧) '' l)

/-- The deterministic automaton corresponding to the Myhill congruence of a language `l`
accepts the same language `l`. -/
theorem myhillCongruenceDA_language_eq (l : Language α) :
    language (l.myhillCongruenceDA) = l := by
  ext x
  simp only [myhillCongruenceDA, language, Acceptor.Accepts,
    congr_mtr_eq (c := l.MyhillCongruence.toRightCongruence)]
  constructor
  · rintro ⟨y, hy, heq⟩
    have h1 := Quotient.eq.mp heq [] []
    simp only [List.append_nil, List.nil_append] at h1
    simpa [← h1]
  · intro hx
    use x, hx
    congr

/-- A language is regular if and only if its Myhill quotient is finite. -/
theorem IsRegular.iff_finite_myhillQuotient (l : Language α) :
    l.IsRegular ↔ Finite (l.MyhillQuotient) := by
  apply Iff.intro
  case mp => exact IsRegular.finite_myhillQuotient
  case mpr =>
    intro h
    apply IsRegular.iff_dfa.mpr
    use l.MyhillQuotient, h, l.myhillCongruenceDA, myhillCongruenceDA_language_eq l

end Language
