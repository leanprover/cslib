/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Languages.CombinatoryLogic.Realizes

@[expose] public section

/-!
# General recursion in the SKI calculus

In this file we implement general recursion functions (on the natural numbers), inspired by the
formalisation of `Mathlib.Computability.Partrec`. Since composition (`B`-combinator) and pairs
(`MkPair`, `Fst`, `Snd`) have been implemented in `Cslib.Computability.CombinatoryLogic.Basic`,
what remains are the following definitions and proofs of their correctness.

- Church numerals : a predicate `IsChurch n a` expressing that the term `a` is βη-equivalent to
the standard church numeral `n` — that is, `a ⬝ f ⬝ x ↠ f ⬝ (f ⬝ ... ⬝ (f ⬝ x)))`.
- SKI numerals : `Zero` and `Succ`, corresponding to `Partrec.zero` and `Partrec.succ`, and
correctness proofs `zero_correct` and `succ_correct`.
- Predecessor : a term `Pred` so that (`pred_correct`)
`IsChurch n a → IsChurch n.pred (Pred ⬝ a)`.
- Primitive recursion : a term `Rec` so that (`rec_correct_succ`) `IsChurch (n+1) a` implies
`Rec ⬝ x ⬝ g ⬝ a ↠ g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))` and (`rec_correct_zero`) `IsChurch 0 a`
implies `Rec ⬝ x ⬝ g ⬝ a ↠ x`.
- Unbounded root finding (μ-recursion) : given a term  `f` representing a function `fℕ: Nat → Nat`,
which takes on the value 0 a term `RFind` such that (`rFind_correct`) `RFind ⬝ f ↠ a` such that
`IsChurch n a` for `n` the smallest root of `fℕ`.

## References

- For church numerals and recursion via the fixed-point combinator, see sections 3.2 and 3.3 of
Selinger's notes <https://www.mscs.dal.ca/~selinger/papers/papers/lambdanotes.pdf>

## TODO

- One could unify `is_bool`, `IsChurch` and `IsChurchPair` into a predicate
`represents : α → SKI → Prop`, for any type `α` "built from pieces that we understand" — something
along the lines of "pure finite types"
(see eg <https://en.wikipedia.org/wiki/Primitive_recursive_functional>). This would also clean up
the statement of `rfind_correct`.
- The predicate `∃ n : Nat, IsChurch n : SKI → Prop` is semidecidable: by confluence, it suffices
to normal-order reduce `a ⬝ f ⬝ x` for any "atomic" terms `f` and `x`. This could be implemented
by defining reduction on polynomials.
- With such a decision procedure, every SKI-term defines a partial function `Nat →. Nat`, in the
sense of `Mathlib.Data.Part` (as used in `Mathlib.Computability.Partrec`).
- The results of this file should define a surjection `SKI → Nat.Partrec`.
-/

namespace Cslib

namespace SKI

open Red MRed

/-- Function form of the church numerals. -/
def Church (n : Nat) (f x : SKI) : SKI :=
match n with
| 0 => x
| n+1 => f ⬝ (Church n f x)

@[simp] lemma Church_zero (f x : SKI) : Church 0 f x = x := rfl
@[simp] lemma Church_succ (n : Nat) (f x : SKI) : Church (n+1) f x = f ⬝ Church n f x := rfl

/-- `church` commutes with reduction. -/
lemma church_red (n : Nat) (f f' x x' : SKI) (hf : f ↠ f') (hx : x ↠ x') :
    Church n f x ↠ Church n f' x' := by
  induction n with
  | zero => exact hx
  | succ n ih => exact parallel_mRed hf ih

instance instHasRealizerLiftNat : HasRealizerLift Nat Red where
  Realizes a n := ∀ f x : SKI, (a ⬝ f ⬝ x) ↠ (Church n f x)
  realizes_left_of_red := by
    intro n a a' ha' h f x
    calc
    (a ⬝ f ⬝ x) ⭢ a' ⬝ f ⬝ x := red_head _ _ x <| red_head _ _ f <| h
    _ ↠ Church n f x := by apply ha'

/-! ### Church numeral basics

Canonical constructors, iteration and primitive recursion.
-/

/-- Church zero := λ f x. x -/
protected def Zero : SKI := K ⬝ I

@[scoped grind .]
theorem realizes_zero : SKI.Zero ⊩ 0 := by
  intro f x
  calc
  _ ↠ I ⬝ x := by apply Relation.ReflTransGen.single; apply red_head; apply red_K
  _ ⭢ x := by apply red_I

/-- Church one := λ f x. f x -/
protected def One : SKI := I

@[scoped grind .]
theorem realizes_one : SKI.One ⊩ 1 := by
  intro f x
  apply head
  exact .single (red_I f)

/-- Church succ := λ a f x. f (a f x) ~ λ a f. B f (a f) ~ λ a. S B a ~ S B -/
protected def Succ : SKI := S ⬝ B

theorem realizes_succ : SKI.Succ ⊩ Nat.succ := by
  intro n xn hn f x
  calc
  _ ⭢ B ⬝ f ⬝ (xn ⬝ f) ⬝ x := by apply red_head; apply red_S
  _ ↠ f ⬝ (xn ⬝ f ⬝ x) := by apply B_def
  _ ↠ f ⬝ (Church n  f x) := by apply MRed.tail; exact hn f x

/-- Build the canonical SKI Church numeral for `n`. -/
def toChurch : ℕ → SKI
  | 0 => SKI.Zero
  | n + 1 => SKI.Succ ⬝ (toChurch n)

/-- `toChurch 0 = Zero`. -/
@[simp] lemma toChurch_zero : toChurch 0 = SKI.Zero := rfl

/-- `toChurch (n + 1) = Succ ⬝ toChurch n`. -/
@[simp] lemma toChurch_succ (n : ℕ) : toChurch (n + 1) = SKI.Succ ⬝ (toChurch n) := rfl

/-- `toChurch n` correctly represents `n`. -/
@[scoped grind .]
theorem realizes_toChurch (n : ℕ) : (toChurch n) ⊩ n := by
  induction n with
  | zero => exact realizes_zero
  | succ n ih => exact realizes_succ ih

variable {α : Type*} [HasRealizerLift α Red]

def Iter := R

lemma realizes_iter : Iter ⊩ (Nat.iterate (α := α)) := by
  intro f xf hf n xn hn a xa ha
  suffices (Church n xf xa) ⊩ f^[n] a by
    apply this.left_of_mRed
    calc
      _ ↠ xn ⬝ xf ⬝ xa := MRed.head _ <| R_def ..
      _ ↠ Church n xf xa := hn ..
  clear hn
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [Function.iterate_succ']
      exact hf ih

def Nat.recPairStep (f : Nat → α → α) : α × Nat → α × Nat
  | ⟨y, m⟩ => ⟨f m y, m + 1⟩

lemma Nat.realizes_recPairStep {α' : Type*} (a : α') (f : Nat → α' → α') (n : Nat) :
    (Nat.recPairStep f)^[n] ⟨a, 0⟩ = ⟨Nat.rec a f n, n⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih, recPairStep]

/-- We encode primitive recursion on `Nat` by the usual Kleene dentist trick. -/
def natRecAuxPoly : SKI.Polynomial 2 :=
  SKI.MkPair ⬝' (&0 ⬝' (Snd ⬝' &1) ⬝' (Fst ⬝' &1)) ⬝' (SKI.Succ ⬝' (Snd ⬝' &1))
def natRecAux := natRecAuxPoly.toSKI
lemma natRecAux_def (f p : SKI) :
    (natRecAux ⬝ f ⬝ p) ↠ SKI.MkPair ⬝ (f ⬝ (Snd ⬝ p) ⬝ (Fst ⬝ p)) ⬝ (SKI.Succ ⬝ (Snd ⬝ p)) :=
  natRecAuxPoly.toSKI_correct [f, p] (by simp)

lemma natRecAux_realizes {f : Nat → α → α} {xf : SKI} (hf : xf ⊩ f) :
    (natRecAux ⬝ xf) ⊩ (Nat.recPairStep f) := by
  intro p xp hp
  suffices (SKI.MkPair ⬝ (xf ⬝ (Snd ⬝ xp) ⬝ (Fst ⬝ xp)) ⬝ (SKI.Succ ⬝ (Snd ⬝ xp))) ⊩
      (Nat.recPairStep f p) by
    exact this.left_of_mRed <| natRecAux_def ..
  apply realizes_mkPair
  · exact hf hp.2 hp.1
  · exact SKI.realizes_succ hp.2

lemma realizes_recPairStep_iter {a : α} {xa : SKI} (ha : xa ⊩ a)
    {f : Nat → α → α} {xf : SKI} (hf : xf ⊩ f) {n : Nat} {xn : SKI} (hn : xn ⊩ n) :
    (R ⬝ (natRecAux ⬝ xf) ⬝ xn ⬝ (MkPair ⬝ xa ⬝ SKI.Zero)) ⊩ (⟨Nat.rec a f n, n⟩ : α × Nat) := by
  rw [←Nat.realizes_recPairStep]
  refine realizes_iter (natRecAux_realizes hf) hn ?_
  apply realizes_mkPair
  · exact ha
  · exact realizes_zero

def natRecPoly : SKI.Polynomial 3 :=
  Fst ⬝' (R ⬝' (natRecAux ⬝' &1) ⬝' &2 ⬝' (MkPair ⬝' &0 ⬝' SKI.Zero))
def natRec := natRecPoly.toSKI
lemma natRec_def (xa xf xn : SKI) :
    (natRec ⬝ xa ⬝ xf ⬝ xn) ↠ Fst ⬝ (R ⬝ (natRecAux ⬝ xf) ⬝ xn ⬝ (MkPair ⬝ xa ⬝ SKI.Zero)) :=
  natRecPoly.toSKI_correct [xa, xf, xn] (by simp)

/-- Primitive recursion on `Nat`. -/
theorem realizes_nat_rec :
    natRec ⊩ (Nat.rec : α → (Nat → α → α) → Nat → α) := by
  intro a xa ha f xf hf n xn hn
  exact Realizes.left_of_mRed (realizes_recPairStep_iter ha hf hn).1 (natRec_def xa xf xn)

def Pred : SKI := natRec ⬝ SKI.Zero ⬝ K

theorem realizes_pred : Pred ⊩ Nat.pred := by
  intro n xn hn
  have : n.pred = n.rec 0 (fun a _ => a) := by induction n <;> simp
  rw [this]
  refine realizes_nat_rec realizes_zero ?_ hn
  intro _ _ h _ _ _
  exact h.left_of_red <| red_K ..

/-- IsZero := λ n. n (K FF) TT -/
def IsZeroPoly : SKI.Polynomial 1 := &0 ⬝' (K ⬝ FF) ⬝' TT
/-- A term representing IsZero -/
def IsZero : SKI := IsZeroPoly.toSKI
theorem isZero_def (a : SKI) : (IsZero ⬝ a) ↠ a ⬝ (K ⬝ FF) ⬝ TT :=
  IsZeroPoly.toSKI_correct [a] (by simp)

theorem realizes_isZero : IsZero ⊩ (· == 0) := by
  intro n xn hn
  refine Realizes.left_of_mRed ?_ (isZero_def _)
  by_cases n = 0
  case pos h0 =>
    simp_rw [h0] at hn ⊢
    exact realizes_true.left_of_mRed <| hn ..
  case neg h0 =>
    simp_rw [beq_false_of_ne h0]
    let ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [hk] at hn
    apply realizes_false.left_of_mRed
    calc
    _ ↠ (K ⬝ FF) ⬝ Church k (K ⬝ FF) TT := hn ..
    _ ⭢ FF := red_K ..

/-! ### Root-finding (μ-recursion) -/

/--
First define an auxiliary function `RFindAbove` that looks for roots above a fixed number n, as a
fixed point of R ↦ λ n f. if f n = 0 then n else R f (n+1)
                 ~ λ n f. Cond ⬝ n (R f (Succ n)) (IsZero (f n))
-/
def RFindAboveAuxPoly : SKI.Polynomial 3 :=
    SKI.Cond ⬝' &1 ⬝' (&0 ⬝' (SKI.Succ ⬝' &1) ⬝' &2) ⬝' (IsZero ⬝' (&2 ⬝' &1))
/-- A term representing RFindAboveAux -/
def RFindAboveAux : SKI := RFindAboveAuxPoly.toSKI
lemma rfindAboveAux_def (R₀ f a : SKI) :
    (RFindAboveAux ⬝ R₀ ⬝ a ⬝ f) ↠ SKI.Cond ⬝ a ⬝ (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) :=
  RFindAboveAuxPoly.toSKI_correct [R₀, a, f] (by trivial)

theorem rfindAboveAux_base (R₀ f a : SKI) (hfa : (f ⬝ a) ⊩ 0) :
    (RFindAboveAux ⬝ R₀ ⬝ a ⬝ f) ↠ a := calc
  _ ↠ SKI.Cond ⬝ a ⬝ (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) := rfindAboveAux_def _ _ _
  _ ↠ if (Nat.beq 0 0) then a else (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) := by
      exact cond_def <| realizes_isZero hfa

theorem rfindAboveAux_step (R₀ f a : SKI) {m : Nat} (hfa : (f ⬝ a) ⊩ m + 1) :
    (RFindAboveAux ⬝ R₀ ⬝ a ⬝ f) ↠ R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f := calc
  _ ↠ SKI.Cond ⬝ a ⬝ (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) := rfindAboveAux_def _ _ _
  _ ↠ if (Nat.beq (m + 1) 0) then a else (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) := by
      exact cond_def <| realizes_isZero hfa

/-- Find the minimal root of `fNat` above a number n -/
def RFindAbove : SKI := RFindAboveAux.fixedPoint

theorem RFindAbove_correct (f : Nat → Nat) (xf x : SKI) (hf : xf ⊩ f) (n m : Nat) (hx : x ⊩ m)
    (hroot : f (m + n) = 0) (hpos : ∀ i < n, f (m + i) ≠ 0) :
    (RFindAbove ⬝ x ⬝ xf) ⊩ (m + n) := by
  induction n generalizing m x
  all_goals apply Realizes.left_of_mRed (y := RFindAboveAux ⬝ RFindAbove ⬝ x ⬝ xf)
  case zero.ha =>
    apply hx.left_of_mRed
    apply rfindAboveAux_base
    exact hroot ▸ hf hx
  case succ.ha n ih =>
    apply Realizes.left_of_mRed (y := RFindAbove ⬝ (SKI.Succ ⬝ x) ⬝ xf)
    · replace ih := ih (SKI.Succ ⬝ x) (m + 1) (realizes_succ hx)
      grind
    · have : (xf ⬝ x) ⊩ ((f m).pred + 1) := Nat.succ_pred_eq_of_ne_zero (hpos 0 (by simp)) ▸ hf hx
      exact rfindAboveAux_step _ _ _ this
  -- close the `h` goals of the above `apply isChurch_trans`
  all_goals {apply MRed.head; apply MRed.head; exact fixedPoint_correct _}

/-- Ordinary root finding is root finding above zero -/
def RFind := RFindAbove ⬝ SKI.Zero
theorem RFind_correct (f : Nat → Nat) (xf : SKI) (hf : xf ⊩ f)
    (n : Nat) (hroot : f n = 0) (hpos : ∀ i < n, f i ≠ 0) : (RFind ⬝ xf) ⊩ n := by
  have :_ := RFindAbove_correct (n := n) (f := f) (hf := hf) (hx := realizes_zero)
  simp_rw [Nat.zero_add] at this
  exact this hroot hpos

/-! ### Further numeric operations -/

/-- Addition: λ n m. n Succ m -/
def AddPoly : SKI.Polynomial 2 := &0 ⬝' SKI.Succ ⬝' &1
/-- A term representing addition on church numerals -/
protected def Add : SKI := AddPoly.toSKI
theorem add_def (a b : SKI) : (SKI.Add ⬝ a ⬝ b) ↠ a ⬝ SKI.Succ ⬝ b :=
  AddPoly.toSKI_correct [a, b] (by simp)

theorem realizes_add : SKI.Add ⊩ Nat.add:= by
  intro n xn hn m xm hm
  refine Realizes.left_of_mRed (y := Church n SKI.Succ xm) ?_ ?_
  · clear hn
    induction n with
      | zero => simpa
      | succ n ih =>
        simpa [Nat.add_right_comm] using realizes_succ ih
  · calc
    _ ↠ xn ⬝ SKI.Succ ⬝ xm := add_def ..
    _ ↠ Church n SKI.Succ xm := hn ..

/-- Multiplication: λ n m. n (Add m) Zero -/
def MulPoly : SKI.Polynomial 2 := &0 ⬝' (SKI.Add ⬝' &1) ⬝' SKI.Zero
/-- A term representing multiplication on church numerals -/
protected def Mul : SKI := MulPoly.toSKI
theorem mul_def (a b : SKI) : (SKI.Mul ⬝ a ⬝ b) ↠ a ⬝ (SKI.Add ⬝ b) ⬝ SKI.Zero :=
  MulPoly.toSKI_correct [a, b] (by simp)

theorem realizes_mul : SKI.Mul ⊩ Nat.mul := by
  intro n xn hn m xm hm
  refine Realizes.left_of_mRed (y := Church n (SKI.Add ⬝ xm) SKI.Zero) ?_ ?_
  · clear hn
    induction n with
      | zero => simpa using realizes_zero
      | succ n ih =>
        simpa [Nat.add_mul, Nat.one_mul, Nat.add_comm, Church] using realizes_add hm ih
  · exact Trans.trans (mul_def xn xm) (hn (SKI.Add ⬝ xm) SKI.Zero)

/-- Subtraction: λ n m. n Pred m -/
def SubPoly : SKI.Polynomial 2 := &1 ⬝' Pred ⬝' &0
/-- A term representing subtraction on church numerals -/
protected def Sub : SKI := SubPoly.toSKI
theorem sub_def (a b : SKI) : (SKI.Sub ⬝ a ⬝ b) ↠ b ⬝ Pred ⬝ a :=
  SubPoly.toSKI_correct [a, b] (by simp)

theorem realizes_sub : SKI.Sub ⊩ Nat.sub := by
  intro n xn hn m xm hm
  refine Realizes.left_of_mRed (y := Church m Pred xn) ?_ ?_
  · clear hm
    induction m with
      | zero => simpa using hn
      | succ m ih =>
        simpa using realizes_pred ih
  · calc
    _ ↠ xm ⬝ Pred ⬝ xn := sub_def ..
    _ ↠ Church m Pred xn := hm Pred xn

/-- Comparison: (. ≤ .) := λ n m. IsZero ⬝ (Sub ⬝ n ⬝ m) -/
def LEPoly : SKI.Polynomial 2 := IsZero ⬝' (SKI.Sub ⬝' &0 ⬝' &1)
/-- A term representing comparison on church numerals -/
protected def LE : SKI := LEPoly.toSKI
theorem le_def (a b : SKI) : (SKI.LE ⬝ a ⬝ b) ↠ IsZero ⬝ (SKI.Sub ⬝ a ⬝ b) :=
  LEPoly.toSKI_correct [a, b] (by simp)

theorem realizes_le : SKI.LE ⊩ (· ≤ · : Nat → Nat → Bool) := by
  intro n xn hn m xm hm
  simp_rw [← decide_eq_decide.mpr <| Nat.sub_eq_zero_iff_le]
  apply Realizes.left_of_mRed (y := IsZero ⬝ (SKI.Sub ⬝ xn ⬝ xm)) (h := le_def _ _)
  apply realizes_isZero
  apply realizes_sub <;> assumption

end SKI

end Cslib
