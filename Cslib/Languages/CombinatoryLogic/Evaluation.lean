/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Languages.CombinatoryLogic.Confluence
public import Cslib.Languages.CombinatoryLogic.Recursion

@[expose] public section

/-!
# Evaluation results

This file formalises evaluation and normal forms of SKI terms.

## Main definitions

- `RedexFree` : a predicate expressing that a term has no redexes
- `evalStep` : SKI-reduction as a function

## Main results

- `evalStep_right_correct` : correctness for `evalStep`
- `redexFree_iff` and `redexFree_iff_mred_eq` : a term is redex free if and only if it has
(respectively) no one-step reductions, or if its only many step reduction is itself.
- `unique_normal_form` : if `x` reduces to both `y` and `z`, and both `y` and `z` are in normal
form, then they are equal.
- **Rice's theorem**: no SKI term is a non-trivial predicate.

## References

This file draws heavily from <https://gist.github.com/b-mehta/e412c837818223b8f16ca0b4aa19b166>.
-/

namespace Cslib

namespace SKI

open Red Relation

/-- The predicate that a term has no reducible sub-terms. -/
def RedexFree : SKI → Prop
  | S => True
  | K => True
  | I => True
  | S ⬝ x => x.RedexFree
  | K ⬝ x => x.RedexFree
  | I ⬝ _ => False
  | S ⬝ x ⬝ y => x.RedexFree ∧ y.RedexFree
  | K ⬝ _ ⬝ _ => False
  | I ⬝ _ ⬝ _ => False
  | S ⬝ _ ⬝ _ ⬝ _ => False
  | K ⬝ _ ⬝ _ ⬝ _ => False
  | I ⬝ _ ⬝ _ ⬝ _ => False
  | a ⬝ b ⬝ c ⬝ d ⬝ e => RedexFree (a ⬝ b ⬝ c ⬝ d) ∧ RedexFree e

/--
One-step evaluation as a function: either it returns a term that has been reduced by one step,
or a proof that the term is redex free. Uses normal-order reduction.
-/
def evalStep : (x : SKI) → PLift (x.RedexFree) ⊕ SKI
  | S => Sum.inl (PLift.up trivial)
  | K => Sum.inl (PLift.up trivial)
  | I => Sum.inl (PLift.up trivial)
  | S ⬝ x => match x.evalStep with
    | Sum.inl h => Sum.inl h
    | Sum.inr x' => Sum.inr (S ⬝ x')
  | K ⬝ x => match x.evalStep with
    | Sum.inl h => Sum.inl h
    | Sum.inr x' => Sum.inr (K ⬝ x')
  | I ⬝ x => Sum.inr x
  | S ⬝ x ⬝ y => match x.evalStep, y.evalStep with
    | Sum.inl h1, Sum.inl h2 => Sum.inl (.up ⟨h1.down, h2.down⟩)
    | Sum.inl _, Sum.inr y' => Sum.inr (S ⬝ x ⬝ y')
    | Sum.inr x', _ => Sum.inr (S ⬝ x' ⬝ y)
  | K ⬝ x ⬝ _ => Sum.inr x
  | I ⬝ x ⬝ y => Sum.inr (x ⬝ y)
  | S ⬝ x ⬝ y ⬝ z => Sum.inr (x ⬝ z ⬝ (y ⬝ z))
  | K ⬝ x ⬝ _ ⬝ z => Sum.inr (x ⬝ z)
  | I ⬝ x ⬝ y ⬝ z => Sum.inr (x ⬝ y ⬝ z)
  | a ⬝ b ⬝ c ⬝ d ⬝ e => match evalStep (a ⬝ b ⬝ c ⬝ d), evalStep e with
    | Sum.inl h1, Sum.inl h2 => Sum.inl (.up ⟨h1.down, h2.down⟩)
    | Sum.inl _, Sum.inr e' => Sum.inr (a ⬝ b ⬝ c ⬝ d ⬝ e')
    | Sum.inr abcd', _ => Sum.inr (abcd' ⬝ e)

/-- The normal-order reduction implemented by `evalStep` indeed computes a one-step reduction. -/
theorem evalStep_right_correct : (x y : SKI) → (x.evalStep = Sum.inr y) → x ⭢ y
  | S ⬝ x, a, h =>
    match hx : x.evalStep with
    | Sum.inl _ => by simp only [hx, evalStep, reduceCtorEq] at h
    | Sum.inr x' => by
        simp only [evalStep, hx, Sum.inr.injEq] at h
        rw [←h]
        exact .red_tail _ _ _ (evalStep_right_correct _ _ hx)
  | K ⬝ x, a, h =>
    match hx : x.evalStep with
    | Sum.inl _ => by simp only [hx, evalStep, reduceCtorEq] at h
    | Sum.inr x' => by
        simp only [evalStep, hx, Sum.inr.injEq] at h
        rw [←h]
        exact .red_tail _ _ _ (evalStep_right_correct _ _ hx)
  | I ⬝ x, a, h => Sum.inr.inj h ▸ red_I _
  | S ⬝ x ⬝ y, a, h =>
      match hx : x.evalStep, hy : y.evalStep with
      | Sum.inl _, Sum.inl _ => by simp only [hx, hy, evalStep, reduceCtorEq] at h
      | Sum.inl _, Sum.inr y' => by
          simp only [hx, hy, evalStep, Sum.inr.injEq] at h
          rw [←h]
          exact .red_tail _ _ _ <| evalStep_right_correct _ _ hy
      | Sum.inr x', _ => by
          simp only [hx, hy, evalStep, Sum.inr.injEq] at h
          rw [←h]
          exact .red_head _ _ _ <| .red_tail _ _ _ <| evalStep_right_correct _ _ hx
  | K ⬝ x ⬝ y, a, h => Sum.inr.inj h ▸ red_K ..
  | I ⬝ x ⬝ y, a, h => Sum.inr.inj h ▸ (red_head _ _ _ <| red_I _)
  | S ⬝ x ⬝ y ⬝ z, a, h => Sum.inr.inj h ▸ red_S ..
  | K ⬝ x ⬝ y ⬝ z, a, h => Sum.inr.inj h ▸ (red_head _ _ _ <| red_K ..)
  | I ⬝ x ⬝ y ⬝ z, a, h => Sum.inr.inj h ▸ (red_head _ _ _ <| red_head _ _ _ <| red_I _)
  | a ⬝ b ⬝ c ⬝ d ⬝ e, x, h =>
      match habcd : evalStep (a ⬝ b ⬝ c ⬝ d), he : evalStep e with
      | Sum.inl _, Sum.inl _ => by simp only [habcd, he, evalStep, reduceCtorEq] at h
      | Sum.inl _, Sum.inr e' => by
          simp only [habcd, he, evalStep, Sum.inr.injEq] at h
          rw [←h]
          exact red_tail _ _ _ <| evalStep_right_correct _ _ he
      | Sum.inr abcd', _ => by
          simp only [habcd, he, evalStep, Sum.inr.injEq] at h
          rw [←h]
          exact red_head _ _ _ <| evalStep_right_correct _ _ habcd

theorem redexFree_of_normal_red {x : SKI} (h : Normal Red x) : x.RedexFree := by
  match hx : x.evalStep with
  | Sum.inl h' => exact h'.down
  | Sum.inr y => rw [Normal_iff] at h; cases h _ (evalStep_right_correct x y hx)

theorem RedexFree.normal_red {x : SKI} (hx : x.RedexFree) : Normal Red x := by
  simp_rw [Normal_iff]
  intro y hy
  match x, hx, y, hy with
  | S ⬝ x, hx, S ⬝ y, red_tail _ _ _ hx' => rw [RedexFree] at hx; exact hx.normal_red ⟨_, hx'⟩
  | K ⬝ x, hx, K ⬝ y, red_tail _ _ _ hx' => rw [RedexFree] at hx; exact hx.normal_red ⟨_, hx'⟩
  | S ⬝ _ ⬝ _, ⟨hx, _⟩, S ⬝ _ ⬝ _, red_head _ _ _ (red_tail _ _ _ h3) => exact hx.normal_red ⟨_, h3⟩
  | S ⬝ _ ⬝ _, ⟨_, hy⟩, S ⬝ _ ⬝ _, red_tail _ _ _ h3 => exact hy.normal_red ⟨_, h3⟩
  | _ ⬝ _ ⬝ _ ⬝ _ ⬝ _, ⟨hx, _⟩, _ ⬝ _, red_head _ _ _ hq => exact hx.normal_red ⟨_, hq⟩
  | _ ⬝ _ ⬝ _ ⬝ _ ⬝ _, ⟨_, hy⟩, _ ⬝ _, red_tail _ _ _ he => exact hy.normal_red ⟨_, he⟩

/-- A term is redex free iff it has no one-step reductions. -/
theorem redexFree_iff {x : SKI} : x.RedexFree ↔ Normal Red x :=
  ⟨RedexFree.normal_red, redexFree_of_normal_red⟩

theorem redexFree_iff_evalStep {x : SKI} : x.RedexFree ↔ (x.evalStep).isLeft = true := by
  constructor
  case mp =>
    intro h
    match hx : x.evalStep with
    | Sum.inl h' => exact rfl
    | Sum.inr y => cases h.normal_red ⟨_, (evalStep_right_correct _ _ hx)⟩
  case mpr =>
    intro h
    match hx : x.evalStep with
    | Sum.inl h' => exact h'.down
    | Sum.inr y => rw [hx] at h; cases h

instance : DecidablePred RedexFree := fun _ => decidable_of_iff' _ redexFree_iff_evalStep

/-- A term is redex free iff its only many-step reduction is itself. -/
theorem redexFree_iff_mred_eq {x : SKI} : x.RedexFree ↔ ∀ y, (x ↠ y) ↔ x = y := by
  constructor
  case mp => grind [RedexFree.normal_red]
  case mpr =>
    intro h
    rw [redexFree_iff]
    intro ⟨y, hy⟩
    specialize h y
    exact Red.ne hy (h.1 (Relation.ReflTransGen.single hy))

/-- If a term has a common reduct with a normal term, it in fact reduces to that term. -/
theorem mJoin_red_redexFree {x y : SKI} (hy : y.RedexFree) (h : MJoin Red x y) : x ↠ y :=
  let ⟨w, hyw, hzw⟩ := h
  (redexFree_iff_mred_eq.1 hy _ |>.1 hzw : y = w) ▸ hyw

/-- If `x` reduces to both `y` and `z`, and `z` is not reducible, then `y` reduces to `z`. -/
lemma confluent_redexFree {x y z : SKI} (hxy : x ↠ y) (hxz : x ↠ z) (hz : RedexFree z) : y ↠ z :=
  let ⟨w, hyw, hzw⟩ := MRed.diamond hxy hxz
  (redexFree_iff_mred_eq.1 hz _ |>.1 hzw : z = w) ▸ hyw

/--
If `x` reduces to both `y` and `z`, and both `y` and `z` are in normal form, then they are equal.
-/
lemma unique_normal_form {x y z : SKI}
    (hxy : x ↠ y) (hxz : x ↠ z) (hy : y.RedexFree) (hz : RedexFree z) : y = z :=
  (redexFree_iff_mred_eq.1 hy _).1 (confluent_redexFree hxy hxz hz)

/-- If `x` and `y` are normal and have a common reduct, then they are equal. -/
lemma eq_of_mJoin_red_redexFree {x y : SKI} (h : MJoin Red x y)
    (hx : x.RedexFree) (hy : y.RedexFree) : x = y :=
  (redexFree_iff_mred_eq.1 hx _).1 (mJoin_red_redexFree hy h)

/-! ### Injectivity for datatypes -/

lemma sk_nequiv : ¬ MJoin Red S K := by
  intro ⟨z, hsz, hkz⟩
  have hS : RedexFree S := by simp [RedexFree]
  have hK : RedexFree K := by simp [RedexFree]
  cases (redexFree_iff_mred_eq.1 hS z).1 hsz
  cases (redexFree_iff_mred_eq.1 hK _).1 hkz

/-- Injectivity for booleans. -/
theorem isBool_injective (x y : SKI) (u v : Bool) (hx : IsBool u x) (hy : IsBool v y)
    (hxy : MJoin Red x y) : u = v := by
  have h : MJoin Red (if u then S else K) (if v then S else K) := by
    apply mJoin_red_equivalence.trans (y := x ⬝ S ⬝ K)
    · apply mJoin_red_equivalence.symm
      apply Relation.MJoin.single
      exact hx S K
    · apply mJoin_red_equivalence.trans (y := y ⬝ S ⬝ K)
      · exact mJoin_red_head K <| mJoin_red_head S hxy
      · apply Relation.MJoin.single
        exact hy S K
  grind [sk_nequiv, mJoin_red_equivalence.symm h]

lemma TF_nequiv : ¬ MJoin Red TT FF := fun h =>
  (Bool.eq_not_self true).mp <| isBool_injective TT FF true false TT_correct FF_correct h

/-- A specialisation of `Church : Nat → SKI`. -/
def churchK : Nat → SKI
  | 0 => K
  | n+1 => K ⬝ (churchK n)

lemma churchK_church : (n : Nat) → churchK n = Church n K K
  | 0 => rfl
  | n+1 => by simp [churchK, Church, churchK_church n]

lemma churchK_redexFree : (n : Nat) → RedexFree (churchK n)
  | 0 => trivial
  | n+1 => churchK_redexFree n

@[simp]
lemma churchK_size : (n : Nat) → (churchK n).size = n+1
  | 0 => rfl
  | n + 1 => by rw [churchK, size, size, churchK_size, Nat.add_comm]

lemma churchK_injective : Function.Injective churchK :=
  fun n m h => by simpa using congrArg SKI.size h

/-- Injectivity for Church numerals -/
theorem isChurch_injective (x y : SKI) (n m : Nat) (hx : IsChurch n x) (hy : IsChurch m y)
    (hxy : MJoin Red x y) : n = m := by
  suffices MJoin Red (churchK n) (churchK m) by
    apply churchK_injective
    exact eq_of_mJoin_red_redexFree this (churchK_redexFree n) (churchK_redexFree m)
  apply mJoin_red_equivalence.trans (y := x ⬝ K ⬝ K)
  · simp_rw [churchK_church]
    exact mJoin_red_equivalence.symm <| Relation.MJoin.single (hx K K)
  · apply mJoin_red_equivalence.trans (y := y ⬝ K ⬝ K)
    · apply mJoin_red_head; apply mJoin_red_head; assumption
    · simp_rw [churchK_church]
      exact Relation.MJoin.single (hy K K)

/--
**Rice's theorem**: no SKI term is a non-trivial predicate.

More specifically, say a term `P` is a *predicate* if, for every term `x`, `P · x` reduces to either
`TT` or `FF`. A predicate `P` is *trivial* if either it always reduces to true, or always to false.
This version of Rice's theorem derives a contradiction from the existence of a predicate `P` and the
existence of terms `x` for which `P · x` is true (`P · x ↠ TT`) and for which `P · x` is false
(`P · x ↠ FF`).
-/
theorem rice {P : SKI} (hP : ∀ x : SKI, ((P ⬝ x) ↠ TT) ∨ (P ⬝ x) ↠ FF)
    (hxt : ∃ x : SKI, (P ⬝ x) ↠ TT) (hxf : ∃ x : SKI, (P ⬝ x) ↠ FF) : False := by
  obtain ⟨a, ha⟩ := hxt
  obtain ⟨b, hb⟩ := hxf
  let Neg : SKI := P ⬝' &0 ⬝' b ⬝' a |>.toSKI (n := 1)
  let Abs : SKI := Neg.fixedPoint
  have Neg_app : ∀ x : SKI, (Neg ⬝ x) ↠ P ⬝ x ⬝ b ⬝ a :=
    fun x => (P ⬝' &0 ⬝' b ⬝' a) |>.toSKI_correct (n := 1) [x] (by simp)
  cases hP Abs
  case inl h =>
    have : (P ⬝ Abs) ↠ FF := calc
      _ ↠ P ⬝ (Neg ⬝ Abs) := by apply MRed.tail; apply fixedPoint_correct
      _ ↠ P ⬝ (P ⬝ Abs ⬝ b ⬝ a) := by apply MRed.tail; apply Neg_app
      _ ↠ P ⬝ (TT ⬝ b ⬝ a) := by apply MRed.tail; apply MRed.head; apply MRed.head; exact h
      _ ↠ P ⬝ b := by apply MRed.tail; apply TT_correct
      _ ↠ FF := hb
    exact TF_nequiv <| MRed.diamond h this
  case inr h =>
    have : (P ⬝ Abs) ↠ TT := calc
      _ ↠ P ⬝ (Neg ⬝ Abs) := by apply MRed.tail; apply fixedPoint_correct
      _ ↠ P ⬝ (P ⬝ Abs ⬝ b ⬝ a) := by apply MRed.tail; apply Neg_app
      _ ↠ P ⬝ (FF ⬝ b ⬝ a) := by apply MRed.tail; apply MRed.head; apply MRed.head; exact h
      _ ↠ P ⬝ a := by apply MRed.tail; apply FF_correct
      _ ↠ TT := ha
    exact TF_nequiv <| MRed.diamond this h

/-- **Rice's theorem**: any SKI predicate is trivial.

This version of Rice's theorem proves (classically) that any SKI predicate `P` either is constantly
true (ie `P · x ↠ TT` for every `x`) or is constantly false (`P · x ↠ FF` for every `x`).
-/
theorem rice' {P : SKI} (hP : ∀ x : SKI, ((P ⬝ x) ↠ TT) ∨ (P ⬝ x) ↠ FF) :
    (∀ x : SKI, (P ⬝ x) ↠ TT) ∨ (∀ x : SKI, (P ⬝ x) ↠ FF) := by
  by_contra! h
  obtain ⟨⟨a, ha⟩, b, hb⟩ := h
  exact rice hP ⟨b, (hP _).resolve_right hb⟩ ⟨a, (hP _).resolve_left ha⟩

end SKI

end Cslib
