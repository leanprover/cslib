/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Computability.CombinatoryLogic.Defs
import Cslib.Computability.CombinatoryLogic.Basic

/-!
# General recursion in the SKI calculus

In this file we implement general recursion functions (on the natural numbers), inspired by the
formalisation of `Mathlib.Computability.Partrec`. Since composition (`B`-combinator) and pairs
(`MkPair`, `Fst`, `Snd`) have been implemented in `Cslib.Computability.CombinatoryLogic.Basic`,
what remains are the following definitions and proofs of their correctness.

- Church numerals : a predicate `is_church n a` expressing that the term `a` is βη-equivalent to
the standard church numeral `n` — that is, `a ⬝ f ⬝ x ⇒* f ⬝ (f ⬝ ... ⬝ (f ⬝ x)))`.
- SKI numerals : `Zero` and `Succ`, corresponding to `Partrec.zero` and `Partrec.succ`, and
correctness proofs `zero_correct` and `succ_correct`.
- Predecessor : a term `Pred` so that (`pred_correct`)
`is_church n a → is_church n.pred (Pred ⬝ a)`.
- Primitive recursion : a term `Rec` so that (`rec_correct_succ`) `is_church (n+1) a` implies
`Rec ⬝ x ⬝ g ⬝ a ⇒* g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))` and (`rec_correct_zero`) `is_church 0 a` implies
`Rec ⬝ x ⬝ g ⬝ a ⇒* x`.
- Unbounded root finding (μ-recursion) : given a term  `f` representing a function `fℕ: Nat → Nat`,
which takes on the value 0 a term `RFind` such that (`rFind_correct`) `RFind ⬝ f ⇒* a` such that
`is_church n a` for `n` the smallest root of `fℕ`.

## References

- For church numerals and recursion via the fixed-point combinator, see sections 3.2 and 3.3 of
Selinger's notes <https://www.mscs.dal.ca/~selinger/papers/papers/lambdanotes.pdf>

## TODO

- The predicate `∃ n : Nat, is_church n : SKI → Prop` is semidecidable: by confluence, it suffices
to normal-order reduce `a ⬝ f ⬝ x` for any "atomic" terms `f` and `x`. This could be implemented
by defining reduction on Polynomials.
- With such a decision procedure, every SKI-term defines a partial function `Nat →. Nat`, in the
sense of `Mathlib.Data.Part` (as used in `Mathlib.Computability.Partrec`).
- The results of this file should define a surjection `SKI → Nat.Partrec`.
-/

open SKI ReductionStep

/-- Function form of the church numerals. -/
def church (n : Nat) (f x : SKI) : SKI :=
match n with
| 0 => x
| n+1 => f ⬝ (church n f x)

/-- `church` commutes with reduction. -/
lemma church_red (n : Nat) (f f' x x' : SKI) (hf : f ⇒* f') (hx : x ⇒* x') :
    church n f x ⇒* church n f' x' := by
  induction n with
  | zero => unfold church; exact hx
  | succ n ih =>
    unfold church
    exact parallel_large_reduction _ _ _ _ hf ih

/-- The term `a` is βη-equivalent to a standard church numeral. -/
def is_church (n : Nat) (a : SKI) : Prop := ∀ f x : SKI, a ⬝ f ⬝ x ⇒* church n f x

/-- To show `is_church n a` it suffices to show the same for a reduct of `a`. -/
theorem is_church_trans (n : Nat) (a a' : SKI) (h : a ⇒* a') : is_church n a' → is_church n a := by
  simp_rw [is_church]
  intro ha' f x
  calc
  _ ⇒* a' ⬝ f ⬝ x := by apply largeRed_head; apply largeRed_head; exact h
  _ ⇒* church n f x := by apply ha'


/-! ### Church numeral basics -/

/-- Church zero := λ f x. x -/
protected def SKI.Zero : SKI := K ⬝ I
theorem zero_correct : is_church 0 SKI.Zero := by
  unfold is_church SKI.Zero church
  intro f x
  calc
  _ ⇒ I ⬝ x := by apply red_head; apply red_K
  _ ⇒ x := by apply red_I

/-- Church one := λ f x. f x -/
protected def SKI.One : SKI := I
theorem one_correct : is_church 1 SKI.One := by
  simp_rw [is_church, SKI.One, church]
  intro f x
  apply largeRed_head
  apply largeRed_single
  apply red_I

/-- Church succ := λ a f x. f (a f x) ~ λ a f. B f (a f) ~ λ a. S B a ~ S B -/
def Succ : SKI := S ⬝ B
theorem succ_correct (n : Nat) (a : SKI) (h : is_church n a) : is_church (n+1) (Succ ⬝ a) := by
  unfold is_church at h ⊢
  unfold Succ church
  intro f x
  calc
  _ ⇒ B ⬝ f ⬝ (a ⬝ f) ⬝ x := by apply red_head; apply red_S
  _ ⇒* f ⬝ (a ⬝ f ⬝ x) := by apply B_def
  _ ⇒* f ⬝ (church n  f x) := by apply largeRed_tail; exact h f x

/--
To define the predecessor, iterate the function `PredAux` ⟨i, j⟩ ↦ ⟨j, j+1⟩ on ⟨0,0⟩, then take
the  first component.
-/
def PredAuxPoly : SKI.Polynomial 1 := MkPair ⬝' (Snd ⬝' &0) ⬝' (Succ ⬝' (Snd ⬝' &0))
def PredAux : SKI := PredAuxPoly.toSKI
theorem predAux_def (p : SKI) :  PredAux ⬝ p ⇒* MkPair ⬝ (Snd ⬝ p) ⬝ (Succ ⬝ (Snd ⬝ p)) := by
  have : _ := PredAuxPoly.toSKI_correct [p] (by simp)
  simp_rw [applyList] at this
  assumption

/-- Useful auxilliary definition expressing that `p` represents ns ∈ Nat × Nat. -/
def is_church_pair (ns : Nat × Nat) (x : SKI) : Prop :=
  is_church ns.1 (Fst ⬝ x) ∧ is_church ns.2 (Snd ⬝ x)

theorem is_church_pair_trans (ns : Nat × Nat) (a a' : SKI) (h : a ⇒* a') :
    is_church_pair ns a' → is_church_pair ns a := by
  simp_rw [is_church_pair]
  intro ⟨ha₁,ha₂⟩
  constructor
  . apply is_church_trans (a' := Fst ⬝ a')
    apply largeRed_tail; exact h; exact ha₁
  . apply is_church_trans (a' := Snd ⬝ a')
    apply largeRed_tail; exact h; exact ha₂

theorem predAux_correct (p : SKI) (ns : Nat × Nat) (h : is_church_pair ns p) :
    is_church_pair ⟨ns.2, ns.2+1⟩ (PredAux ⬝ p) := by
  refine is_church_pair_trans _ _ (MkPair ⬝ (Snd ⬝ p) ⬝ (Succ ⬝ (Snd ⬝ p))) (predAux_def p) ?_
  constructor
  · exact is_church_trans ns.2 _ (Snd ⬝ p) (fst_correct _ _) h.2
  · refine is_church_trans (ns.2+1) _ (Succ ⬝ (Snd ⬝ p)) (snd_correct _ _) ?_
    exact succ_correct ns.2 (Snd ⬝ p) h.2

/-- The stronger induction hypothesis necessary for the proof of `pred_correct`. -/
theorem predAux_correct' (n : Nat) :
    is_church_pair (n.pred, n) <| church n PredAux  (MkPair ⬝ SKI.Zero ⬝ SKI.Zero) := by
  induction n with
    | zero =>
      apply is_church_pair_trans ⟨0,0⟩ _ (MkPair ⬝ SKI.Zero ⬝ SKI.Zero)
        (by simp [church, largeRed_refl])
      constructor <;> apply is_church_trans 0 _ SKI.Zero ?_ zero_correct
      · exact fst_correct _ _
      · exact snd_correct _ _
    | succ n ih =>
      simp_rw [church]
      apply predAux_correct (ns := ⟨n.pred, n⟩) (h := ih)

/-- Predecessor := λ n. Fst ⬝ (n ⬝ PredAux ⬝ (MkPair ⬝ Zero ⬝ Zero)) -/
def PredPoly : SKI.Polynomial 1 := Fst ⬝' (&0 ⬝' PredAux ⬝' (MkPair ⬝ SKI.Zero ⬝ SKI.Zero))
def Pred : SKI := PredPoly.toSKI
theorem pred_def (a : SKI) : Pred ⬝ a ⇒* Fst ⬝ (a ⬝ PredAux ⬝ (MkPair ⬝ SKI.Zero ⬝ SKI.Zero)) := by
  have : _ := PredPoly.toSKI_correct [a] (by simp)
  simp_rw [applyList] at this
  assumption

theorem pred_correct (n : Nat) (a : SKI) (h : is_church n a) : is_church n.pred (Pred ⬝ a) := by
  refine is_church_trans n.pred _ (Fst ⬝ (a ⬝ PredAux ⬝ (MkPair ⬝ SKI.Zero ⬝ SKI.Zero)))
    (pred_def a) ?_
  refine is_church_trans _ _ (a' := Fst ⬝ (church n PredAux (MkPair ⬝ SKI.Zero ⬝ SKI.Zero))) ?_ ?_
  · apply largeRed_tail
    exact h _ _
  · exact predAux_correct' n |>.1


/-! ### Primitive recursion -/

def IsZeroPoly : SKI.Polynomial 1 := &0 ⬝' (K ⬝ FF) ⬝' TT
def IsZero : SKI := IsZeroPoly.toSKI
theorem isZero_def (a : SKI) : IsZero ⬝ a ⇒* a ⬝ (K ⬝ FF) ⬝ TT := by
  have : _ := IsZeroPoly.toSKI_correct [a] (by simp)
  simp_rw [applyList] at this
  assumption
theorem isZero_correct (n : Nat) (a : SKI) (h : is_church n a) :
    is_bool (Nat.beq n 0) (IsZero ⬝ a) := by
  apply is_bool_trans (a' := a ⬝ (K ⬝ FF) ⬝ TT) (h := isZero_def a)
  by_cases Nat.beq n 0
  case pos h0 =>
    simp_rw [h0]
    replace h0 := Nat.eq_of_beq_eq_true (n:=n) (m:=0) h0
    rw [h0] at h
    apply is_bool_trans (ha' := TT_correct)
    exact h _ _
  case neg h0 =>
    simp_rw [h0]
    replace h0 := Nat.ne_of_beq_eq_false <| eq_false_of_ne_true h0
    let ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [hk] at h
    apply is_bool_trans (ha' := FF_correct)
    calc
    _ ⇒* (K ⬝ FF) ⬝ church k (K ⬝ FF) TT := h _ _
    _ ⇒ FF := red_K _ _


/--
To define `Rec x g n := if n==0 then x else (Rec x g (Pred n))`, we obtain a fixed point of
R ↦ λ x g n. Cond ⬝ (IsZero ⬝ n) ⬝ x ⬝ (g ⬝ a ⬝ (R ⬝ x ⬝ g ⬝ (Pred ⬝ n)))
-/
def RecAuxPoly : SKI.Polynomial 4 :=
  SKI.Cond ⬝' &1 ⬝' (&2 ⬝' &3 ⬝' (&0 ⬝' &1 ⬝' &2 ⬝' (Pred ⬝' &3))) ⬝' (IsZero ⬝' &3)
def RecAux : SKI := RecAuxPoly.toSKI
theorem recAux_def (R₀ x g a : SKI) :
    RecAux ⬝ R₀ ⬝ x ⬝ g ⬝ a ⇒* SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (R₀ ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a)  := by
  have : _ := RecAuxPoly.toSKI_correct [R₀, x, g, a] (by simp)
  simp_rw [applyList] at this
  assumption

/--
We define Rec so that
`Rec ⬝ x ⬝ g ⬝ a ⇒* SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a)`
-/
def Rec : SKI := fixedPoint RecAux
theorem rec_def (x g a : SKI) :
  Rec ⬝ x ⬝ g ⬝ a ⇒* SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) := calc
  _ ⇒* RecAux ⬝ Rec ⬝ x ⬝ g ⬝ a := by
      apply largeRed_head; apply largeRed_head; apply largeRed_head
      apply fixedPoint_correct
  _ ⇒* SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) := recAux_def Rec x g a

theorem rec_zero (x g a : SKI) (ha : is_church 0 a) : Rec ⬝ x ⬝ g ⬝ a ⇒* x := by
  calc
  _ ⇒* SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) := rec_def _ _ _
  _ ⇒* if (Nat.beq 0 0) then x else (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) := by
      apply cond_correct
      exact isZero_correct 0 a ha

theorem rec_succ (n : Nat) (x g a : SKI) (ha : is_church (n+1) a) :
    Rec ⬝ x ⬝ g ⬝ a ⇒* g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a)) := by
  calc
  _ ⇒* SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) := rec_def _ _ _
  _ ⇒* if (Nat.beq (n+1) 0) then x else (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) := by
      apply cond_correct
      exact isZero_correct (n+1) a ha


/-! ### Root-finding (μ-Minimisation) -/

/--
First define an auxilliary function `RFindAbove` that looks for roots above a fixed number n, as a
fixed point of R ↦ λ n f. if f n = 0 then n else R f (n+1)
                 ~ λ n f. Cond ⬝ n (R f (Succ n)) (IsZero (f n))
-/
def RFindAboveAuxPoly : SKI.Polynomial 3 :=
    SKI.Cond ⬝' &1 ⬝' (&0 ⬝' (Succ ⬝' &1) ⬝' &2) ⬝' (IsZero ⬝' (&2 ⬝' &1))
def RFindAboveAux : SKI := RFindAboveAuxPoly.toSKI
lemma rfindAboveAux_def (R₀ f a : SKI) :
    RFindAboveAux ⬝ R₀ ⬝ a ⬝ f ⇒* SKI.Cond ⬝ a ⬝ (R₀ ⬝ (Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) := by
  have :_ := RFindAboveAuxPoly.toSKI_correct [R₀, a, f] (by trivial)
  simp_rw [applyList] at this
  assumption

theorem rfindAboveAux_base (R₀ f a : SKI) (hfa : is_church 0 (f ⬝ a)) :
    RFindAboveAux ⬝ R₀ ⬝ a ⬝ f ⇒* a := by
  calc
  _ ⇒* SKI.Cond ⬝ a ⬝ (R₀ ⬝ (Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) := rfindAboveAux_def _ _ _
  _ ⇒* if (Nat.beq 0 0) then a else (R₀ ⬝ (Succ ⬝ a) ⬝ f) := by
      apply cond_correct
      apply isZero_correct _ _ hfa
theorem rfindAboveAux_step (R₀ f a : SKI) {m : Nat} (hfa : is_church (m+1) (f ⬝ a)) :
    RFindAboveAux ⬝ R₀ ⬝ a ⬝ f ⇒* R₀ ⬝ (Succ ⬝ a) ⬝ f := by
  calc
    _ ⇒* SKI.Cond ⬝ a ⬝ (R₀ ⬝ (Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) := rfindAboveAux_def _ _ _
    _ ⇒* if (Nat.beq (m+1) 0) then a else (R₀ ⬝ (Succ ⬝ a) ⬝ f) := by
        apply cond_correct
        apply isZero_correct _ _ hfa

/- Find the minimal root of `fNat` above a number n -/
def RFindAbove : SKI := RFindAboveAux.fixedPoint
theorem RFindAbove_correct (fNat : Nat → Nat) (f x : SKI)
    (hf : ∀ i : Nat, ∀ y : SKI, is_church i y →  is_church (fNat i) (f ⬝ y))
    (n m : Nat) (hx : is_church m x) (hroot : fNat (m+n) = 0) (hpos : ∀ i < n, fNat (m+i) ≠ 0) :
    is_church (m+n) (RFindAbove ⬝ x ⬝ f) := by
  induction n generalizing m x with
  | zero =>
    apply is_church_trans (a' := x)
    . have : is_church (fNat m) (f ⬝ x) := hf m x hx
      rw [Nat.add_zero] at hroot
      simp_rw [hroot] at this
      calc
      _ ⇒* RFindAboveAux ⬝ RFindAbove ⬝ x ⬝ f := by
          apply largeRed_head; apply largeRed_head; exact fixedPoint_correct _
      _ ⇒* x := by apply rfindAboveAux_base; assumption
    . assumption
  | succ n ih =>
    unfold RFindAbove
    apply is_church_trans (a' := RFindAbove ⬝ (Succ ⬝ x) ⬝ f)
    . let y := (fNat m).pred
      have : is_church (y+1) (f ⬝ x) := by
        subst y
        have : fNat m ≠ 0 := hpos 0 (by simp)
        have : (fNat m).pred + 1 = fNat m := Nat.succ_pred_eq_of_ne_zero this
        simp_rw [this]
        exact hf m x hx
      calc
      _ ⇒* RFindAboveAux ⬝ RFindAbove ⬝ x ⬝ f := by
          apply largeRed_head; apply largeRed_head; exact fixedPoint_correct _
      _ ⇒* RFindAbove ⬝ (Succ ⬝ x) ⬝ f := by apply rfindAboveAux_step; assumption
    .
      replace ih := ih (Succ ⬝ x) (m+1) (succ_correct _ x hx)
      simp_rw [Nat.add_assoc, Nat.add_comm] at ih
      apply ih
      . assumption
      . intro i hi
        apply hpos (i+1)
        simp [hi]

/-- Ordinary root finding is root finding above zero -/
def RFind := RFindAbove ⬝ SKI.Zero
theorem RFind_correct (fNat : Nat → Nat) (f : SKI)
    (hf : ∀ (i : Nat) (y : SKI), is_church i y → is_church (fNat i) (f ⬝ y))
    (n : Nat) (hroot : fNat n = 0) (hpos : ∀ i < n, fNat i ≠ 0) : is_church n (RFind ⬝ f) := by
  have :_ := RFindAbove_correct (n := n) (fNat := fNat) (hf := hf) (hx := zero_correct)
  simp_rw [Nat.zero_add] at this
  exact this hroot hpos



/-! ### Further numeric operations -/

/-- Addition: λ n m. n Succ m -/
def AddPoly : SKI.Polynomial 2 := &0 ⬝' Succ ⬝' &1
protected def SKI.Add : SKI := AddPoly.toSKI
theorem add_def (a b : SKI) : SKI.Add ⬝ a ⬝ b ⇒* a ⬝ Succ ⬝ b := by
  have : _ := AddPoly.toSKI_correct [a, b] (by simp)
  simp_rw [applyList] at this
  assumption

theorem add_correct (n m : Nat) (a b : SKI) (ha : is_church n a) (hb : is_church m b) :
    is_church (n+m) (SKI.Add ⬝ a ⬝ b) := by
  refine is_church_trans (n+m) _ (church n Succ b) ?_ ?_
  · calc
    _ ⇒* a ⬝ Succ ⬝ b := add_def a b
    _ ⇒* church n Succ b := ha Succ b
  · clear ha
    induction n with
      | zero => simp_rw [Nat.zero_add, church]; exact hb
      | succ n ih =>
        simp_rw [Nat.add_right_comm, church]
        exact succ_correct _ _ ih

/-- Multiplication: λ n m. n (Add m) Zero -/
def MulPoly : SKI.Polynomial 2 := &0 ⬝' (SKI.Add ⬝' &1) ⬝' SKI.Zero
protected def SKI.Mul : SKI := MulPoly.toSKI
theorem mul_def (a b : SKI) : SKI.Mul ⬝ a ⬝ b ⇒* a ⬝ (SKI.Add ⬝ b) ⬝ SKI.Zero := by
  have : _ := MulPoly.toSKI_correct [a, b] (by simp)
  simp_rw [applyList] at this
  assumption

theorem mul_correct (n m : Nat) (a b : SKI) (ha : is_church n a) (hb : is_church m b) :
    is_church (n*m) (SKI.Mul ⬝ a ⬝ b) := by
  refine is_church_trans (n*m) _ (church n (SKI.Add ⬝ b) SKI.Zero) ?_ ?_
  · calc
    _ ⇒* a ⬝ (SKI.Add ⬝ b) ⬝ SKI.Zero := mul_def a b
    _ ⇒* church n (SKI.Add ⬝ b) SKI.Zero := ha _ _
  · clear ha
    induction n with
      | zero => simp_rw [Nat.zero_mul, church]; exact zero_correct
      | succ n ih =>
        simp_rw [Nat.add_mul, Nat.one_mul, Nat.add_comm, church]
        exact add_correct m (n*m) b (church n (SKI.Add ⬝ b) SKI.Zero) hb ih

/-- Subtraction: λ n m. n Pred m -/
def SubPoly : SKI.Polynomial 2 := &1 ⬝' Pred ⬝' &0
protected def SKI.Sub : SKI := SubPoly.toSKI
theorem sub_def (a b : SKI) : SKI.Sub ⬝ a ⬝ b ⇒* b ⬝ Pred ⬝ a := by
  have : _ := SubPoly.toSKI_correct [a, b] (by simp)
  simp_rw [applyList] at this
  assumption

theorem sub_correct (n m : Nat) (a b : SKI) (ha : is_church n a) (hb : is_church m b) :
    is_church (n-m) (SKI.Sub ⬝ a ⬝ b) := by
  refine is_church_trans (n-m) _ (church m Pred a) ?_ ?_
  · calc
    _ ⇒* b ⬝ Pred ⬝ a := sub_def a b
    _ ⇒* church m Pred a := hb Pred a
  · clear hb
    induction m with
      | zero => simp_rw [Nat.sub_zero, church]; exact ha
      | succ m ih =>
        simp_rw [←Nat.sub_sub, church]
        exact pred_correct _ _ ih
