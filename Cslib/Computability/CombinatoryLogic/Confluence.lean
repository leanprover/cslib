/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Computability.CombinatoryLogic.Defs
import Cslib.Utils.Relation

/-!
# SKI reduction is confluent

This file proves the **Church-Rosser** theorem for the SKI calculus, that is, if `a ⇒* b` and
`a ⇒* c`, `b ⇒* d` and `c ⇒* d` for some term `d`. More strongly (though equivalently), we show
that the relation of having a common reduct is transitive — in the above situation, `a` and `b`,
and `a` and `c` have common reducts, so the result implies the same of `b` and `c`. Our proof
follows the method of Tait and Martin-Löf for the lambda calculus, as presented for instance in
Chapter 4 of Peter Selinger's notes:
<https://www.irif.fr/~mellies/mpri/mpri-ens/biblio/Selinger-Lambda-Calculus-Notes.pdf>.

## Main definitions

- `ParallelReduction` : a relation `⇒'` on terms such that `⇒ ⊆ ⇒' ⊆ ⇒*`, allowing simultaneous
reduction on the head and tail of a term.

## Main results

- `parallelReduction_diamond` : parallel reduction satisfies the diamond property, that is, it is
confluent in a single step.
- `commonReduct_equivalence` : by a general result, the diamond property for `⇒'` implies the same
for its reflexive-transitive closure. This closure is exactly `⇒*`, which implies the
**Church-Rosser** theorem as sketched above.
-/

open SKI ReductionStep

inductive ParallelReduction : SKI → SKI → Prop
  /-- Parallel reduction is reflexive, -/
  | refl (a : SKI) : ParallelReduction a a
  /-- Contains `ReductionStep`, -/
  | red_I' (a : SKI) : ParallelReduction (I ⬝ a) a
  | red_K' (a b : SKI) : ParallelReduction (K ⬝ a ⬝ b) a
  | red_S' (a b c : SKI) : ParallelReduction (S ⬝ a ⬝ b ⬝ c) (a ⬝ c ⬝ (b ⬝ c))
  /-- and allows simultaneous reduction of disjoint redexes. -/
  | par (a a' b b' : SKI) :
      ParallelReduction a a' → ParallelReduction b b' → ParallelReduction (a ⬝ b) (a' ⬝ b')


infix:90 " ⇒' " => ParallelReduction

/-- The inclusion `⇒' ⊆ ⇒*` -/
theorem largeReduction_of_parallelReduction (a a' : SKI) (h : a ⇒' a') : a ⇒* a' := by
  cases h
  case refl => exact Relation.ReflTransGen.refl
  case par a a' b b' ha hb =>
    apply parallel_large_reduction
    exact largeReduction_of_parallelReduction a a' ha
    exact largeReduction_of_parallelReduction b b' hb
  case red_I' => apply Relation.ReflTransGen.single; exact red_I a'
  case red_K' b => apply Relation.ReflTransGen.single; exact red_K a' b
  case red_S' a b c => apply Relation.ReflTransGen.single; exact red_S a b c

/-- The inclusion `⇒ ⊆ ⇒'` -/
theorem parallelReduction_of_reductionStep (a a' : SKI) (h : a ⇒ a') : a ⇒' a' := by
  cases h
  case red_S => apply ParallelReduction.red_S'
  case red_K => apply ParallelReduction.red_K'
  case red_I => apply ParallelReduction.red_I'
  case red_head a a' b h =>
    apply ParallelReduction.par
    exact parallelReduction_of_reductionStep a a' h
    exact ParallelReduction.refl b
  case red_tail a b b' h =>
    apply ParallelReduction.par
    exact ParallelReduction.refl a
    exact parallelReduction_of_reductionStep b b' h

/-- The inclusions of `largeReduction_of_parallelReduction` and
`parallelReduction_of_reductionStep` imply that `⇒` and `⇒'` have the same reflexive-transitive
closure. -/
theorem reflTransGen_parallelReduction_largeReduction :
    Relation.ReflTransGen ParallelReduction = LargeReduction := by
  ext a b
  constructor
  . apply Relation.reflTransGen_minimal
    . exact largeReduction_reflexive
    . exact largeReduction_transitive
    . exact largeReduction_of_parallelReduction
  . apply Relation.reflTransGen_minimal
    . exact Relation.reflexive_reflTransGen
    . exact Relation.transitive_reflTransGen
    . intro a a' h
      apply Relation.ReflTransGen.single
      exact parallelReduction_of_reductionStep a a' h

/-!
Irreducibility for the (partially applied) primitive combinators.

TODO: possibly these should be proven more generally (in another file) for `⇒*`. -/

lemma I_irreducible (a : SKI) (h : I ⇒' a) : a = I := by
  cases h
  rfl

lemma K_irreducible (a : SKI) (h : K ⇒' a) : a = K := by
  cases h
  rfl

lemma Ka_irreducible (a c : SKI) (h : K ⬝ a ⇒' c) : ∃ a', a ⇒' a' ∧ c = K ⬝ a' := by
  cases h
  case refl =>
    use a
    exact ⟨ParallelReduction.refl a, rfl⟩
  case par b a' h h' =>
    use a'
    rw [K_irreducible b h]
    exact ⟨h', rfl⟩

lemma S_irreducible (a : SKI) (h : S ⇒' a) : a = S := by
  cases h
  rfl

lemma Sa_irreducible (a c : SKI) (h : S ⬝ a ⇒' c) : ∃ a', a ⇒' a' ∧ c = S ⬝ a' := by
  cases h
  case refl =>
    use a
    exact ⟨ParallelReduction.refl a, rfl⟩
  case par b a' h h' =>
    use a'
    rw [S_irreducible b h]
    exact ⟨h', rfl⟩

lemma Sab_irreducible (a b c : SKI) (h : S ⬝ a ⬝ b ⇒' c) : ∃ a' b', a ⇒' a' ∧ b ⇒' b' ∧ c = S ⬝ a' ⬝ b' := by
  cases h
  case refl =>
    use a; use b
    exact ⟨ParallelReduction.refl a, ParallelReduction.refl b, rfl⟩
  case par c b' hc hb =>
    let ⟨d, hd⟩ := Sa_irreducible a c hc
    rw [hd.2]
    use d; use b'
    exact ⟨hd.1, hb, rfl⟩


/--
The key result: the Church-Rosser property holds for `⇒'`. The proof is a lengthy case analysis
on the reductions `a ⇒' a₁` and `a ⇒' a₂`, but is entirely mechanical.
-/
theorem parallelReduction_diamond (a a₁ a₂ : SKI) (h₁ : a ⇒' a₁) (h₂ : a ⇒' a₂) :
    Relation.Join ParallelReduction a₁ a₂ := by
  cases h₁
  case refl =>
    use a₂; exact ⟨h₂, ParallelReduction.refl a₂⟩
  case par a a' b b' ha' hb' =>
    cases h₂
    case refl =>
      use a' ⬝ b'
      exact ⟨ParallelReduction.refl (a' ⬝ b'), ParallelReduction.par a a' b b' ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      let ⟨a₃, ha⟩ := parallelReduction_diamond a a' a'' ha' ha''
      let ⟨b₃, hb⟩ := parallelReduction_diamond b b' b'' hb' hb''
      use a₃ ⬝ b₃
      constructor
      . exact ParallelReduction.par a' a₃ b' b₃ ha.1 hb.1
      . exact ParallelReduction.par a'' a₃ b'' b₃ ha.2 hb.2
    case red_I' =>
      rw [I_irreducible a' ha']
      use b'
      exact ⟨ParallelReduction.red_I' b', hb'⟩
    case red_K' =>
      let ⟨a₂', ha₂'⟩ := Ka_irreducible a₂ a' ha'
      rw [ha₂'.2]
      use a₂'
      exact ⟨ParallelReduction.red_K' a₂' b', ha₂'.1⟩
    case red_S' a c =>
      let ⟨a'', c', h⟩ := Sab_irreducible a c a' ha'
      rw [h.2.2]
      use a'' ⬝ b' ⬝ (c' ⬝ b')
      refine ⟨ParallelReduction.red_S' a'' c' b', ?_⟩
      apply ParallelReduction.par
      . apply ParallelReduction.par
        . exact h.1
        . exact hb'
      . apply ParallelReduction.par
        . exact h.2.1
        . exact hb'
  case red_I' =>
    cases h₂
    case refl => use a₁; exact ⟨ParallelReduction.refl a₁, ParallelReduction.red_I' a₁⟩
    case par c a₁' hc ha =>
      rw [I_irreducible c hc]
      use a₁'
      exact ⟨ha, ParallelReduction.red_I' a₁'⟩
    case red_I' => use a₁; exact ⟨ParallelReduction.refl a₁, ParallelReduction.refl a₁⟩
  case red_K' c =>
    cases h₂
    case refl => use a₁; exact ⟨ParallelReduction.refl a₁, ParallelReduction.red_K' a₁ c⟩
    case par a' c' ha hc =>
      let ⟨a₁', h'⟩ := Ka_irreducible a₁ a' ha
      rw [h'.2]
      use a₁'
      exact ⟨h'.1, ParallelReduction.red_K' a₁' c'⟩
    case red_K' =>
      use a₁; exact ⟨ParallelReduction.refl a₁, ParallelReduction.refl a₁⟩
  case red_S' a b c =>
    cases h₂
    case refl =>
      use a ⬝ c ⬝ (b ⬝ c)
      exact ⟨ParallelReduction.refl _, ParallelReduction.red_S' _ _ _⟩
    case par d c' hd hc =>
      let ⟨a', b', h⟩ := Sab_irreducible a b d hd
      rw [h.2.2]
      use a' ⬝ c' ⬝ (b' ⬝ c')
      constructor
      . apply ParallelReduction.par
        . apply ParallelReduction.par
          exact h.1; exact hc
        . apply ParallelReduction.par
          exact h.2.1; exact hc
      . exact ParallelReduction.red_S' _ _ _
    case red_S' =>
      use a ⬝ c ⬝ (b ⬝ c)
      exact ⟨ParallelReduction.refl _, ParallelReduction.refl _,⟩

theorem join_parallelReduction_equivalence :
    Equivalence (Relation.Join (Relation.ReflTransGen ParallelReduction)) := by
  apply church_rosser_of_diamond
  exact parallelReduction_diamond

/-- The **Church-Rosser theorem** in its general form. -/
theorem commonReduct_equivalence : Equivalence CommonReduct := by
  unfold CommonReduct
  rw [←reflTransGen_parallelReduction_largeReduction]
  exact join_parallelReduction_equivalence

/-- The **Church-Rosser theorem** in the form it is usually stated. -/
theorem largeReduction_diamond (a b c : SKI) (hab : a ⇒* b) (hac : a ⇒* c) : CommonReduct b c := by
  apply commonReduct_equivalence.trans (y := a)
  . refine commonReduct_equivalence.symm ?_
    exact commonReduct_of_single a b hab
  . exact commonReduct_of_single a c hac
