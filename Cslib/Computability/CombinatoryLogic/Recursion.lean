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

- Church numerals : a predicate `IsChurch n a` expressing that the term `a` is βη-equivalent to
the standard church numeral `n` — that is, `a ⬝ f ⬝ x ⇒* f ⬝ (f ⬝ ... ⬝ (f ⬝ x)))`.
- SKI numerals : `Zero` and `Succ`, corresponding to `Partrec.zero` and `Partrec.succ`, and
correctness proofs `zero_correct` and `succ_correct`.
- Predecessor : a term `Pred` so that (`pred_correct`)
`IsChurch n a → IsChurch n.pred (Pred ⬝ a)`.
- Primitive recursion : a term `Rec` so that (`rec_correct_succ`) `IsChurch (n+1) a` implies
`Rec ⬝ x ⬝ g ⬝ a ⇒* g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))` and (`rec_correct_zero`) `IsChurch 0 a` implies
`Rec ⬝ x ⬝ g ⬝ a ⇒* x`.
- Unbounded root finding (μ-recursion) : given a term  `f` representing a function `fℕ: Nat → Nat`,
which takes on the value 0 a term `RFind` such that (`rFind_correct`) `RFind ⬝ f ⇒* a` such that
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

open SKI ReductionStep

/-- Function form of the church numerals. -/
def Church (n : Nat) (f x : SKI) : SKI :=
match n with
| 0 => x
| n+1 => f ⬝ (Church n f x)

/-- `church` commutes with reduction. -/
lemma church_red (n : Nat) (f f' x x' : SKI) (hf : f ⇒* f') (hx : x ⇒* x') :
    Church n f x ⇒* Church n f' x' := by
  induction n with
  | zero => unfold Church; exact hx
  | succ n ih =>
    unfold Church
    exact parallel_large_reduction _ _ _ _ hf ih

/-- The term `a` is βη-equivalent to a standard church numeral. -/
def IsChurch (n : Nat) (a : SKI) : Prop := ∀ f x : SKI, a ⬝ f ⬝ x ⇒* Church n f x

/-- To show `IsChurch n a` it suffices to show the same for a reduct of `a`. -/
theorem isChurch_trans (n : Nat) (a a' : SKI) (h : a ⇒* a') : IsChurch n a' → IsChurch n a := by
  simp_rw [IsChurch]
  intro ha' f x
  calc
  _ ⇒* a' ⬝ f ⬝ x := by apply largeRed_head; apply largeRed_head; exact h
  _ ⇒* Church n f x := by apply ha'


/-! ### Church numeral basics -/

/-- Church zero := λ f x. x -/
protected def SKI.Zero : SKI := K ⬝ I
theorem zero_correct : IsChurch 0 SKI.Zero := by
  unfold IsChurch SKI.Zero Church
  intro f x
  calc
  _ ⇒ I ⬝ x := by apply red_head; apply red_K
  _ ⇒ x := by apply red_I

/-- Church one := λ f x. f x -/
protected def SKI.One : SKI := I
theorem one_correct : IsChurch 1 SKI.One := by
  simp_rw [IsChurch, SKI.One, Church]
  intro f x
  apply largeRed_head
  apply largeRed_single
  apply red_I

/-- Church succ := λ a f x. f (a f x) ~ λ a f. B f (a f) ~ λ a. S B a ~ S B -/
def Succ : SKI := S ⬝ B
theorem succ_correct (n : Nat) (a : SKI) (h : IsChurch n a) : IsChurch (n+1) (Succ ⬝ a) := by
  unfold IsChurch at h ⊢
  unfold Succ Church
  intro f x
  calc
  _ ⇒ B ⬝ f ⬝ (a ⬝ f) ⬝ x := by apply red_head; apply red_S
  _ ⇒* f ⬝ (a ⬝ f ⬝ x) := by apply B_def
  _ ⇒* f ⬝ (Church n  f x) := by apply largeRed_tail; exact h f x

/--
To define the predecessor, iterate the function `PredAux` ⟨i, j⟩ ↦ ⟨j, j+1⟩ on ⟨0,0⟩, then take
the  first component.
-/
def PredAuxPoly : SKI.Polynomial 1 := MkPair ⬝' (Snd ⬝' &0) ⬝' (Succ ⬝' (Snd ⬝' &0))
/-- A term representing PredAux-/
def PredAux : SKI := PredAuxPoly.toSKI
theorem predAux_def (p : SKI) :  PredAux ⬝ p ⇒* MkPair ⬝ (Snd ⬝ p) ⬝ (Succ ⬝ (Snd ⬝ p)) :=
  PredAuxPoly.toSKI_correct [p] (by simp)

/-- Useful auxilliary definition expressing that `p` represents ns ∈ Nat × Nat. -/
def IsChurchPair (ns : Nat × Nat) (x : SKI) : Prop :=
  IsChurch ns.1 (Fst ⬝ x) ∧ IsChurch ns.2 (Snd ⬝ x)

theorem isChurchPair_trans (ns : Nat × Nat) (a a' : SKI) (h : a ⇒* a') :
    IsChurchPair ns a' → IsChurchPair ns a := by
  simp_rw [IsChurchPair]
  intro ⟨ha₁,ha₂⟩
  constructor
  . apply isChurch_trans (a' := Fst ⬝ a')
    apply largeRed_tail; exact h; exact ha₁
  . apply isChurch_trans (a' := Snd ⬝ a')
    apply largeRed_tail; exact h; exact ha₂

theorem predAux_correct (p : SKI) (ns : Nat × Nat) (h : IsChurchPair ns p) :
    IsChurchPair ⟨ns.2, ns.2+1⟩ (PredAux ⬝ p) := by
  refine isChurchPair_trans _ _ (MkPair ⬝ (Snd ⬝ p) ⬝ (Succ ⬝ (Snd ⬝ p))) (predAux_def p) ?_
  constructor
  · exact isChurch_trans ns.2 _ (Snd ⬝ p) (fst_correct _ _) h.2
  · refine isChurch_trans (ns.2+1) _ (Succ ⬝ (Snd ⬝ p)) (snd_correct _ _) ?_
    exact succ_correct ns.2 (Snd ⬝ p) h.2

/-- The stronger induction hypothesis necessary for the proof of `pred_correct`. -/
theorem predAux_correct' (n : Nat) :
    IsChurchPair (n.pred, n) <| Church n PredAux  (MkPair ⬝ SKI.Zero ⬝ SKI.Zero) := by
  induction n with
    | zero =>
      apply isChurchPair_trans ⟨0,0⟩ _ (MkPair ⬝ SKI.Zero ⬝ SKI.Zero)
        (by simp [Church, largeRed_refl])
      constructor <;> apply isChurch_trans 0 _ SKI.Zero ?_ zero_correct
      · exact fst_correct _ _
      · exact snd_correct _ _
    | succ n ih =>
      simp_rw [Church]
      apply predAux_correct (ns := ⟨n.pred, n⟩) (h := ih)

/-- Predecessor := λ n. Fst ⬝ (n ⬝ PredAux ⬝ (MkPair ⬝ Zero ⬝ Zero)) -/
def PredPoly : SKI.Polynomial 1 := Fst ⬝' (&0 ⬝' PredAux ⬝' (MkPair ⬝ SKI.Zero ⬝ SKI.Zero))
/-- A term representing Pred -/
def Pred : SKI := PredPoly.toSKI
theorem pred_def (a : SKI) : Pred ⬝ a ⇒* Fst ⬝ (a ⬝ PredAux ⬝ (MkPair ⬝ SKI.Zero ⬝ SKI.Zero)) :=
  PredPoly.toSKI_correct [a] (by simp)

theorem pred_correct (n : Nat) (a : SKI) (h : IsChurch n a) : IsChurch n.pred (Pred ⬝ a) := by
  refine isChurch_trans n.pred _ (Fst ⬝ (a ⬝ PredAux ⬝ (MkPair ⬝ SKI.Zero ⬝ SKI.Zero)))
    (pred_def a) ?_
  refine isChurch_trans _ _ (a' := Fst ⬝ (Church n PredAux (MkPair ⬝ SKI.Zero ⬝ SKI.Zero))) ?_ ?_
  · apply largeRed_tail
    exact h _ _
  · exact predAux_correct' n |>.1


/-! ### Primitive recursion -/

/-- IsZero := λ n. n (K FF) TT -/
def IsZeroPoly : SKI.Polynomial 1 := &0 ⬝' (K ⬝ FF) ⬝' TT
/-- A term representing IsZero -/
def IsZero : SKI := IsZeroPoly.toSKI
theorem isZero_def (a : SKI) : IsZero ⬝ a ⇒* a ⬝ (K ⬝ FF) ⬝ TT :=
  IsZeroPoly.toSKI_correct [a] (by simp)
theorem isZero_correct (n : Nat) (a : SKI) (h : IsChurch n a) :
    IsBool (n = 0) (IsZero ⬝ a) := by
  apply isBool_trans (a' := a ⬝ (K ⬝ FF) ⬝ TT) (h := isZero_def a)
  by_cases n=0
  case pos h0 =>
    simp_rw [h0]
    rw [h0] at h
    apply isBool_trans (ha' := TT_correct)
    exact h _ _
  case neg h0 =>
    simp_rw [h0]
    let ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [hk] at h
    apply isBool_trans (ha' := FF_correct)
    calc
    _ ⇒* (K ⬝ FF) ⬝ Church k (K ⬝ FF) TT := h _ _
    _ ⇒ FF := red_K _ _


/--
To define `Rec x g n := if n==0 then x else (Rec x g (Pred n))`, we obtain a fixed point of
R ↦ λ x g n. Cond ⬝ (IsZero ⬝ n) ⬝ x ⬝ (g ⬝ a ⬝ (R ⬝ x ⬝ g ⬝ (Pred ⬝ n)))
-/
def RecAuxPoly : SKI.Polynomial 4 :=
  SKI.Cond ⬝' &1 ⬝' (&2 ⬝' &3 ⬝' (&0 ⬝' &1 ⬝' &2 ⬝' (Pred ⬝' &3))) ⬝' (IsZero ⬝' &3)
/-- A term representing RecAux -/
def RecAux : SKI := RecAuxPoly.toSKI
theorem recAux_def (R₀ x g a : SKI) :
    RecAux ⬝ R₀ ⬝ x ⬝ g ⬝ a ⇒* SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (R₀ ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a)  :=
  RecAuxPoly.toSKI_correct [R₀, x, g, a] (by simp)

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

theorem rec_zero (x g a : SKI) (ha : IsChurch 0 a) : Rec ⬝ x ⬝ g ⬝ a ⇒* x := by
  calc
  _ ⇒* SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) := rec_def _ _ _
  _ ⇒* if (Nat.beq 0 0) then x else (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) := by
      apply cond_correct
      exact isZero_correct 0 a ha

theorem rec_succ (n : Nat) (x g a : SKI) (ha : IsChurch (n+1) a) :
    Rec ⬝ x ⬝ g ⬝ a ⇒* g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a)) := by
  calc
  _ ⇒* SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) := rec_def _ _ _
  _ ⇒* if (Nat.beq (n+1) 0) then x else (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) := by
      apply cond_correct
      exact isZero_correct (n+1) a ha


/-! ### Root-finding (μ-recursion) -/

/--
First define an auxilliary function `RFindAbove` that looks for roots above a fixed number n, as a
fixed point of R ↦ λ n f. if f n = 0 then n else R f (n+1)
                 ~ λ n f. Cond ⬝ n (R f (Succ n)) (IsZero (f n))
-/
def RFindAboveAuxPoly : SKI.Polynomial 3 :=
    SKI.Cond ⬝' &1 ⬝' (&0 ⬝' (Succ ⬝' &1) ⬝' &2) ⬝' (IsZero ⬝' (&2 ⬝' &1))
/-- A term representing RFindAboveAux -/
def RFindAboveAux : SKI := RFindAboveAuxPoly.toSKI
lemma rfindAboveAux_def (R₀ f a : SKI) :
    RFindAboveAux ⬝ R₀ ⬝ a ⬝ f ⇒* SKI.Cond ⬝ a ⬝ (R₀ ⬝ (Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) :=
  RFindAboveAuxPoly.toSKI_correct [R₀, a, f] (by trivial)

theorem rfindAboveAux_base (R₀ f a : SKI) (hfa : IsChurch 0 (f ⬝ a)) :
    RFindAboveAux ⬝ R₀ ⬝ a ⬝ f ⇒* a := calc
  _ ⇒* SKI.Cond ⬝ a ⬝ (R₀ ⬝ (Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) := rfindAboveAux_def _ _ _
  _ ⇒* if (Nat.beq 0 0) then a else (R₀ ⬝ (Succ ⬝ a) ⬝ f) := by
      apply cond_correct
      apply isZero_correct _ _ hfa
theorem rfindAboveAux_step (R₀ f a : SKI) {m : Nat} (hfa : IsChurch (m+1) (f ⬝ a)) :
    RFindAboveAux ⬝ R₀ ⬝ a ⬝ f ⇒* R₀ ⬝ (Succ ⬝ a) ⬝ f := calc
  _ ⇒* SKI.Cond ⬝ a ⬝ (R₀ ⬝ (Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) := rfindAboveAux_def _ _ _
  _ ⇒* if (Nat.beq (m+1) 0) then a else (R₀ ⬝ (Succ ⬝ a) ⬝ f) := by
      apply cond_correct
      apply isZero_correct _ _ hfa

/-- Find the minimal root of `fNat` above a number n -/
def RFindAbove : SKI := RFindAboveAux.fixedPoint
theorem RFindAbove_correct (fNat : Nat → Nat) (f x : SKI)
    (hf : ∀ i : Nat, ∀ y : SKI, IsChurch i y →  IsChurch (fNat i) (f ⬝ y))
    (n m : Nat) (hx : IsChurch m x) (hroot : fNat (m+n) = 0) (hpos : ∀ i < n, fNat (m+i) ≠ 0) :
    IsChurch (m+n) (RFindAbove ⬝ x ⬝ f) := by
  induction n generalizing m x
  all_goals apply isChurch_trans (a' := RFindAboveAux ⬝ RFindAbove ⬝ x ⬝ f)
  case zero.a =>
    apply isChurch_trans (a' := x)
    · have : IsChurch (fNat m) (f ⬝ x) := hf m x hx
      rw [Nat.add_zero] at hroot
      simp_rw [hroot] at this
      apply rfindAboveAux_base
      assumption
    · assumption
  case succ.a n ih =>
    unfold RFindAbove
    apply isChurch_trans (a' := RFindAbove ⬝ (Succ ⬝ x) ⬝ f)
    · let y := (fNat m).pred
      have : IsChurch (y+1) (f ⬝ x) := by
        subst y
        exact Nat.succ_pred_eq_of_ne_zero (hpos 0 (by simp)) ▸ hf m x hx
      apply rfindAboveAux_step
      assumption
    · replace ih := ih (Succ ⬝ x) (m+1) (succ_correct _ x hx)
      simp_rw [Nat.add_assoc, Nat.add_comm] at ih
      apply ih
      · assumption
      · intro i hi
        apply hpos (i+1)
        simp [hi]
  -- close the `h` goals of the above `apply isChurch_trans`
  all_goals {apply largeRed_head; apply largeRed_head; exact fixedPoint_correct _}


/-- Ordinary root finding is root finding above zero -/
def RFind := RFindAbove ⬝ SKI.Zero
theorem RFind_correct (fNat : Nat → Nat) (f : SKI)
    (hf : ∀ (i : Nat) (y : SKI), IsChurch i y → IsChurch (fNat i) (f ⬝ y))
    (n : Nat) (hroot : fNat n = 0) (hpos : ∀ i < n, fNat i ≠ 0) : IsChurch n (RFind ⬝ f) := by
  have :_ := RFindAbove_correct (n := n) (fNat := fNat) (hf := hf) (hx := zero_correct)
  simp_rw [Nat.zero_add] at this
  exact this hroot hpos



/-! ### Further numeric operations -/

/-- Addition: λ n m. n Succ m -/
def AddPoly : SKI.Polynomial 2 := &0 ⬝' Succ ⬝' &1
/-- A term representing addition on church numerals -/
protected def SKI.Add : SKI := AddPoly.toSKI
theorem add_def (a b : SKI) : SKI.Add ⬝ a ⬝ b ⇒* a ⬝ Succ ⬝ b :=
  AddPoly.toSKI_correct [a, b] (by simp)

theorem add_correct (n m : Nat) (a b : SKI) (ha : IsChurch n a) (hb : IsChurch m b) :
    IsChurch (n+m) (SKI.Add ⬝ a ⬝ b) := by
  refine isChurch_trans (n+m) _ (Church n Succ b) ?_ ?_
  · calc
    _ ⇒* a ⬝ Succ ⬝ b := add_def a b
    _ ⇒* Church n Succ b := ha Succ b
  · clear ha
    induction n with
      | zero => simp_rw [Nat.zero_add, Church]; exact hb
      | succ n ih =>
        simp_rw [Nat.add_right_comm, Church]
        exact succ_correct _ _ ih

/-- Multiplication: λ n m. n (Add m) Zero -/
def MulPoly : SKI.Polynomial 2 := &0 ⬝' (SKI.Add ⬝' &1) ⬝' SKI.Zero
/-- A term representing multiplication on church numerals -/
protected def SKI.Mul : SKI := MulPoly.toSKI
theorem mul_def (a b : SKI) : SKI.Mul ⬝ a ⬝ b ⇒* a ⬝ (SKI.Add ⬝ b) ⬝ SKI.Zero :=
  MulPoly.toSKI_correct [a, b] (by simp)

theorem mul_correct (n m : Nat) (a b : SKI) (ha : IsChurch n a) (hb : IsChurch m b) :
    IsChurch (n*m) (SKI.Mul ⬝ a ⬝ b) := by
  refine isChurch_trans (n*m) _ (Church n (SKI.Add ⬝ b) SKI.Zero) ?_ ?_
  · calc
    _ ⇒* a ⬝ (SKI.Add ⬝ b) ⬝ SKI.Zero := mul_def a b
    _ ⇒* Church n (SKI.Add ⬝ b) SKI.Zero := ha _ _
  · clear ha
    induction n with
      | zero => simp_rw [Nat.zero_mul, Church]; exact zero_correct
      | succ n ih =>
        simp_rw [Nat.add_mul, Nat.one_mul, Nat.add_comm, Church]
        exact add_correct m (n*m) b (Church n (SKI.Add ⬝ b) SKI.Zero) hb ih

/-- Subtraction: λ n m. n Pred m -/
def SubPoly : SKI.Polynomial 2 := &1 ⬝' Pred ⬝' &0
/-- A term representing subtraction on church numerals -/
protected def SKI.Sub : SKI := SubPoly.toSKI
theorem sub_def (a b : SKI) : SKI.Sub ⬝ a ⬝ b ⇒* b ⬝ Pred ⬝ a :=
  SubPoly.toSKI_correct [a, b] (by simp)

theorem sub_correct (n m : Nat) (a b : SKI) (ha : IsChurch n a) (hb : IsChurch m b) :
    IsChurch (n-m) (SKI.Sub ⬝ a ⬝ b) := by
  refine isChurch_trans (n-m) _ (Church m Pred a) ?_ ?_
  · calc
    _ ⇒* b ⬝ Pred ⬝ a := sub_def a b
    _ ⇒* Church m Pred a := hb Pred a
  · clear hb
    induction m with
      | zero => simp_rw [Nat.sub_zero, Church]; exact ha
      | succ m ih =>
        simp_rw [←Nat.sub_sub, Church]
        exact pred_correct _ _ ih

/-- Comparison: (. ≤ .) := λ n m. IsZero ⬝ (Sub ⬝ n ⬝ m) -/
def LEPoly : SKI.Polynomial 2 := IsZero ⬝' (SKI.Sub ⬝' &0 ⬝' &1)
/-- A term representing comparison on church numerals -/
protected def SKI.LE : SKI := LEPoly.toSKI
theorem le_def (a b : SKI) : SKI.LE ⬝ a ⬝ b ⇒* IsZero ⬝ (SKI.Sub ⬝ a ⬝ b) :=
  LEPoly.toSKI_correct [a, b] (by simp)

theorem le_correct (n m : Nat) (a b : SKI) (ha : IsChurch n a) (hb : IsChurch m b) :
    IsBool (n ≤ m) (SKI.LE ⬝ a ⬝ b) := by
  simp [← decide_eq_decide.mpr <| Nat.sub_eq_zero_iff_le]
  apply isBool_trans (a' := IsZero ⬝ (SKI.Sub ⬝ a ⬝ b)) (h := le_def _ _)
  apply isZero_correct
  apply sub_correct <;> assumption
