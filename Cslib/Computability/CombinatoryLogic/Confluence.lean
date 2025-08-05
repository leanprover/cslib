/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Computability.CombinatoryLogic.Defs
import Cslib.Data.Relation

/-!
# SKI reduction is confluent

This file proves the **Church-Rosser** theorem for the SKI calculus, that is, if `a ⇒* b` and
`a ⇒* c`, `b ⇒* d` and `c ⇒* d` for some term `d`. More strongly (though equivalently), we show
that the relation of having a common reduct is transitive — in the above situation, `a` and `b`,
and `a` and `c` have common reducts, so the result implies the same of `b` and `c`. Note that
`CommonReduct` is symmetric (trivially) and reflexive (since `⇒*` is), so we in fact show that
`CommonReduct` is an equivalence.

Our proof
follows the method of Tait and Martin-Löf for the lambda calculus, as presented for instance in
Chapter 4 of Peter Selinger's notes:
<https://www.mscs.dal.ca/~selinger/papers/papers/lambdanotes.pdf>.

## Main definitions

- `ParallelReduction` : a relation `⇒ₚ` on terms such that `⇒ ⊆ ⇒ₚ ⊆ ⇒*`, allowing simultaneous
reduction on the head and tail of a term.

## Main results

- `parallelReduction_diamond` : parallel reduction satisfies the diamond property, that is, it is
confluent in a single step.
- `commonReduct_equivalence` : by a general result, the diamond property for `⇒ₚ` implies the same
for its reflexive-transitive closure. This closure is exactly `⇒*`, which implies the
**Church-Rosser** theorem as sketched above.
-/

namespace SKI

open Red MRed

/-- A reduction step allowing simultaneous reduction of disjoint redexes -/
inductive ParallelReduction : SKI → SKI → Prop
  /-- Parallel reduction is reflexive, -/
  | refl (a : SKI) : ParallelReduction a a
  /-- Contains `Red`, -/
  | red_I (a : SKI) : ParallelReduction (I ⬝ a) a
  | red_K (a b : SKI) : ParallelReduction (K ⬝ a ⬝ b) a
  | red_S (a b c : SKI) : ParallelReduction (S ⬝ a ⬝ b ⬝ c) (a ⬝ c ⬝ (b ⬝ c))
  /-- and allows simultaneous reduction of disjoint redexes. -/
  | par ⦃a a' b b' : SKI⦄ :
      ParallelReduction a a' → ParallelReduction b b' → ParallelReduction (a ⬝ b) (a' ⬝ b')


/-- Notation for parallel reduction -/
scoped infix:90 " ⇒ₚ " => ParallelReduction

/-- The inclusion `⇒ₚ ⊆ ⇒*` -/
theorem mRed_of_parallelReduction {a a' : SKI} (h : a ⇒ₚ a') : a ⇒* a' := by
  cases h
  case refl => exact Relation.ReflTransGen.refl
  case par a a' b b' ha hb =>
    apply parallel_mRed
    · exact mRed_of_parallelReduction ha
    · exact mRed_of_parallelReduction hb
  case red_I => exact Relation.ReflTransGen.single (red_I a')
  case red_K b => exact Relation.ReflTransGen.single (red_K a' b)
  case red_S a b c => exact Relation.ReflTransGen.single (red_S a b c)

/-- The inclusion `⇒ ⊆ ⇒ₚ` -/
theorem parallelReduction_of_red {a a' : SKI} (h : a ⇒ a') : a ⇒ₚ a' := by
  cases h
  case red_S => apply ParallelReduction.red_S
  case red_K => apply ParallelReduction.red_K
  case red_I => apply ParallelReduction.red_I
  case red_head a a' b h =>
    apply ParallelReduction.par
    · exact parallelReduction_of_red h
    · exact ParallelReduction.refl b
  case red_tail a b b' h =>
    apply ParallelReduction.par
    · exact ParallelReduction.refl a
    · exact parallelReduction_of_red h

/-- The inclusions of `mRed_of_parallelReduction` and
`parallelReduction_of_red` imply that `⇒` and `⇒ₚ` have the same reflexive-transitive
closure. -/
theorem reflTransGen_parallelReduction_mRed :
    Relation.ReflTransGen ParallelReduction = MRed := by
  ext a b
  constructor
  · apply Relation.reflTransGen_minimal
    · exact MRed.reflexive
    · exact MRed.transitive
    · exact @mRed_of_parallelReduction
  · apply Relation.reflTransGen_minimal
    · exact Relation.reflexive_reflTransGen
    · exact Relation.transitive_reflTransGen
    · exact fun a a' h => Relation.ReflTransGen.single (parallelReduction_of_red h)

/-!
Irreducibility for the (partially applied) primitive combinators.

TODO: possibly these should be proven more generally (in another file) for `⇒*`.
-/

lemma I_irreducible (a : SKI) (h : I ⇒ₚ a) : a = I := by
  cases h
  rfl

lemma K_irreducible (a : SKI) (h : K ⇒ₚ a) : a = K := by
  cases h
  rfl

lemma Ka_irreducible (a c : SKI) (h : K ⬝ a ⇒ₚ c) : ∃ a', a ⇒ₚ a' ∧ c = K ⬝ a' := by
  cases h
  case refl =>
    use a
    exact ⟨ParallelReduction.refl a, rfl⟩
  case par b a' h h' =>
    use a'
    rw [K_irreducible b h]
    exact ⟨h', rfl⟩

lemma S_irreducible (a : SKI) (h : S ⇒ₚ a) : a = S := by
  cases h
  rfl

lemma Sa_irreducible (a c : SKI) (h : S ⬝ a ⇒ₚ c) : ∃ a', a ⇒ₚ a' ∧ c = S ⬝ a' := by
  cases h
  case refl =>
    exact ⟨a, ParallelReduction.refl a, rfl⟩
  case par b a' h h' =>
    use a'
    rw [S_irreducible b h]
    exact ⟨h', rfl⟩

lemma Sab_irreducible (a b c : SKI) (h : S ⬝ a ⬝ b ⇒ₚ c) :
    ∃ a' b', a ⇒ₚ a' ∧ b ⇒ₚ b' ∧ c = S ⬝ a' ⬝ b' := by
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
The key result: the Church-Rosser property holds for `⇒ₚ`. The proof is a lengthy case analysis
on the reductions `a ⇒ₚ a₁` and `a ⇒ₚ a₂`, but is entirely mechanical.
-/
theorem parallelReduction_diamond (a a₁ a₂ : SKI) (h₁ : a ⇒ₚ a₁) (h₂ : a ⇒ₚ a₂) :
    Relation.Join ParallelReduction a₁ a₂ := by
  cases h₁
  case refl => exact ⟨a₂, h₂, ParallelReduction.refl a₂⟩
  case par a a' b b' ha' hb' =>
    cases h₂
    case refl =>
      use a' ⬝ b'
      exact ⟨ParallelReduction.refl (a' ⬝ b'), ParallelReduction.par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      let ⟨a₃, ha⟩ := parallelReduction_diamond a a' a'' ha' ha''
      let ⟨b₃, hb⟩ := parallelReduction_diamond b b' b'' hb' hb''
      use a₃ ⬝ b₃
      constructor
      · exact ParallelReduction.par ha.1 hb.1
      · exact ParallelReduction.par ha.2 hb.2
    case red_I =>
      rw [I_irreducible a' ha']
      use b'
      exact ⟨ParallelReduction.red_I b', hb'⟩
    case red_K =>
      let ⟨a₂', ha₂'⟩ := Ka_irreducible a₂ a' ha'
      rw [ha₂'.2]
      use a₂'
      exact ⟨ParallelReduction.red_K a₂' b', ha₂'.1⟩
    case red_S a c =>
      let ⟨a'', c', h⟩ := Sab_irreducible a c a' ha'
      rw [h.2.2]
      use a'' ⬝ b' ⬝ (c' ⬝ b')
      refine ⟨ParallelReduction.red_S a'' c' b', ?_⟩
      apply ParallelReduction.par
      · apply ParallelReduction.par
        · exact h.1
        · exact hb'
      · apply ParallelReduction.par
        · exact h.2.1
        · exact hb'
  case red_I =>
    cases h₂
    case refl => use a₁; exact ⟨ParallelReduction.refl a₁, ParallelReduction.red_I a₁⟩
    case par c a₁' hc ha =>
      rw [I_irreducible c hc]
      use a₁'
      exact ⟨ha, ParallelReduction.red_I a₁'⟩
    case red_I => use a₁; exact ⟨ParallelReduction.refl a₁, ParallelReduction.refl a₁⟩
  case red_K c =>
    cases h₂
    case refl => use a₁; exact ⟨ParallelReduction.refl a₁, ParallelReduction.red_K a₁ c⟩
    case par a' c' ha hc =>
      let ⟨a₁', h'⟩ := Ka_irreducible a₁ a' ha
      rw [h'.2]
      use a₁'
      exact ⟨h'.1, ParallelReduction.red_K a₁' c'⟩
    case red_K =>
      use a₁; exact ⟨ParallelReduction.refl a₁, ParallelReduction.refl a₁⟩
  case red_S a b c =>
    cases h₂
    case refl =>
      use a ⬝ c ⬝ (b ⬝ c)
      exact ⟨ParallelReduction.refl _, ParallelReduction.red_S _ _ _⟩
    case par d c' hd hc =>
      let ⟨a', b', h⟩ := Sab_irreducible a b d hd
      rw [h.2.2]
      use a' ⬝ c' ⬝ (b' ⬝ c')
      constructor
      · apply ParallelReduction.par
        · exact ParallelReduction.par h.left hc
        · exact ParallelReduction.par h.2.1 hc
      · exact ParallelReduction.red_S _ _ _
    case red_S => exact ⟨a ⬝ c ⬝ (b ⬝ c), ParallelReduction.refl _, ParallelReduction.refl _,⟩

theorem join_parallelReduction_equivalence :
    Equivalence (Relation.Join (Relation.ReflTransGen ParallelReduction)) :=
  church_rosser_of_diamond parallelReduction_diamond

/-- The **Church-Rosser** theorem in its general form. -/
theorem commonReduct_equivalence : Equivalence CommonReduct := by
  unfold CommonReduct
  rw [←reflTransGen_parallelReduction_mRed]
  exact join_parallelReduction_equivalence

/-- The **Church-Rosser** theorem in the form it is usually stated. -/
theorem MRed.diamond (a b c : SKI) (hab : a ⇒* b) (hac : a ⇒* c) : CommonReduct b c := by
  apply commonReduct_equivalence.trans (y := a)
  · exact commonReduct_equivalence.symm (commonReduct_of_single hab)
  · exact commonReduct_of_single hac

end SKI
