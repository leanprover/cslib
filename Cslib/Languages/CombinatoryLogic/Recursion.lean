/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Jesse Alama
-/

module

public import Cslib.Languages.CombinatoryLogic.Basic
public import Mathlib.Data.Nat.Pairing

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
- Integer square root : a term `Sqrt` so that (`sqrt_correct`)
`IsChurch n a → IsChurch n.sqrt (Sqrt ⬝ a)`.
- Nat pairing : a term `NatPair` so that (`natPair_correct`)
`IsChurch a x → IsChurch b y → IsChurch (Nat.pair a b) (NatPair ⬝ x ⬝ y)`.
- Nat unpairing : terms `NatUnpairLeft` and `NatUnpairRight` so that (`natUnpairLeft_correct`)
`IsChurch n a → IsChurch n.unpair.1 (NatUnpairLeft ⬝ a)` and (`natUnpairRight_correct`)
`IsChurch n a → IsChurch n.unpair.2 (NatUnpairRight ⬝ a)`.

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

@[expose] public section

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

/-- The term `a` is βη-equivalent to a standard church numeral. -/
def IsChurch (n : Nat) (a : SKI) : Prop :=
    ∀ f x :SKI, (a ⬝ f ⬝ x) ↠ (Church n f x)

/-- To show `IsChurch n a` it suffices to show the same for a reduct of `a`. -/
theorem isChurch_trans (n : Nat) {a a' : SKI} (h : a ↠ a') :
    IsChurch n a' → IsChurch n a := by
  simp_rw [IsChurch]
  intro ha' f x
  calc
  _ ↠ a' ⬝ f ⬝ x := by apply MRed.head; apply MRed.head; exact h
  _ ↠ Church n f x := by apply ha'


/-! ### Church numeral basics -/

/-- Church zero := λ f x. x -/
protected def Zero : SKI := K ⬝ I
@[scoped grind .]
theorem zero_correct : IsChurch 0 SKI.Zero := by
  unfold IsChurch SKI.Zero Church
  intro f x
  calc
  _ ↠ I ⬝ x := by apply Relation.ReflTransGen.single; apply red_head; apply red_K
  _ ⭢ x := by apply red_I

/-- Church one := λ f x. f x -/
protected def One : SKI := I
@[scoped grind .]
theorem one_correct : IsChurch 1 SKI.One := by
  intro f x
  apply head
  exact .single (red_I f)

/-- Church succ := λ a f x. f (a f x) ~ λ a f. B f (a f) ~ λ a. S B a ~ S B -/
protected def Succ : SKI := S ⬝ B
@[scoped grind →]
theorem succ_correct (n : Nat) (a : SKI) (h : IsChurch n a) :
    IsChurch (n+1) (SKI.Succ ⬝ a) := by
  intro f x
  calc
  _ ⭢ B ⬝ f ⬝ (a ⬝ f) ⬝ x := by apply red_head; apply red_S
  _ ↠ f ⬝ (a ⬝ f ⬝ x) := by apply B_def
  _ ↠ f ⬝ (Church n  f x) := by apply MRed.tail; exact h f x

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
theorem toChurch_correct (n : ℕ) : IsChurch n (toChurch n) := by
  induction n with
  | zero => exact zero_correct
  | succ n ih => exact succ_correct n (toChurch n) ih

/--
To define the predecessor, iterate the function `PredAux` ⟨i, j⟩ ↦ ⟨j, j+1⟩ on ⟨0,0⟩, then take
the  first component.
-/
def PredAuxPoly : SKI.Polynomial 1 := MkPair ⬝' (Snd ⬝' &0) ⬝' (SKI.Succ ⬝' (Snd ⬝' &0))
/-- A term representing PredAux -/
def PredAux : SKI := PredAuxPoly.toSKI
theorem predAux_def (p : SKI) :  (PredAux ⬝ p) ↠ MkPair ⬝ (Snd ⬝ p) ⬝ (SKI.Succ ⬝ (Snd ⬝ p)) :=
  PredAuxPoly.toSKI_correct [p] (by simp)

/-- Useful auxiliary definition expressing that `p` represents ns ∈ Nat × Nat. -/
def IsChurchPair (ns : Nat × Nat) (x : SKI) : Prop :=
  IsChurch ns.1 (Fst ⬝ x) ∧ IsChurch ns.2 (Snd ⬝ x)

theorem isChurchPair_trans (ns : Nat × Nat) (a a' : SKI) (h : a ↠ a') :
    IsChurchPair ns a' → IsChurchPair ns a := by
  simp_rw [IsChurchPair]
  intro ⟨ha₁,ha₂⟩
  constructor
  · apply isChurch_trans (a' := Fst ⬝ a')
    · apply MRed.tail; exact h
    · exact ha₁
  · apply isChurch_trans (a' := Snd ⬝ a')
    · apply MRed.tail; exact h
    · exact ha₂

theorem predAux_correct (p : SKI) (ns : Nat × Nat) (h : IsChurchPair ns p) :
    IsChurchPair ⟨ns.2, ns.2+1⟩ (PredAux ⬝ p) := by
  refine isChurchPair_trans _ _ (MkPair ⬝ (Snd ⬝ p) ⬝ (SKI.Succ ⬝ (Snd ⬝ p))) (predAux_def p) ?_
  constructor
  · exact isChurch_trans ns.2 (fst_correct _ _) h.2
  · refine isChurch_trans (ns.2+1) (snd_correct _ _) ?_
    exact succ_correct ns.2 (Snd ⬝ p) h.2

/-- The stronger induction hypothesis necessary for the proof of `pred_correct`. -/
theorem predAux_correct' (n : Nat) :
    IsChurchPair (n.pred, n) <| Church n PredAux  (MkPair ⬝ SKI.Zero ⬝ SKI.Zero) := by
  induction n with
    | zero =>
      apply isChurchPair_trans ⟨0,0⟩ _ (MkPair ⬝ SKI.Zero ⬝ SKI.Zero)
        (by rfl)
      constructor <;> apply isChurch_trans 0 ?_ zero_correct
      · exact fst_correct _ _
      · exact snd_correct _ _
    | succ n ih =>
      simp_rw [Church_succ]
      apply predAux_correct (ns := ⟨n.pred, n⟩) (h := ih)

/-- Predecessor := λ n. Fst ⬝ (n ⬝ PredAux ⬝ (MkPair ⬝ Zero ⬝ Zero)) -/
def PredPoly : SKI.Polynomial 1 := Fst ⬝' (&0 ⬝' PredAux ⬝' (MkPair ⬝ SKI.Zero ⬝ SKI.Zero))
/-- A term representing Pred -/
def Pred : SKI := PredPoly.toSKI
theorem pred_def (a : SKI) : (Pred ⬝ a) ↠ Fst ⬝ (a ⬝ PredAux ⬝ (MkPair ⬝ SKI.Zero ⬝ SKI.Zero)) :=
  PredPoly.toSKI_correct [a] (by simp)

theorem pred_correct (n : Nat) (a : SKI) (h : IsChurch n a) : IsChurch n.pred (Pred ⬝ a) := by
  refine isChurch_trans n.pred
    (pred_def a) ?_
  refine isChurch_trans _ (a' := Fst ⬝ (Church n PredAux (MkPair ⬝ SKI.Zero ⬝ SKI.Zero))) ?_ ?_
  · apply MRed.tail
    exact h _ _
  · exact predAux_correct' n |>.1


/-! ### Primitive recursion -/

/-- IsZero := λ n. n (K FF) TT -/
def IsZeroPoly : SKI.Polynomial 1 := &0 ⬝' (K ⬝ FF) ⬝' TT
/-- A term representing IsZero -/
def IsZero : SKI := IsZeroPoly.toSKI
theorem isZero_def (a : SKI) : (IsZero ⬝ a) ↠ a ⬝ (K ⬝ FF) ⬝ TT :=
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
    _ ↠ (K ⬝ FF) ⬝ Church k (K ⬝ FF) TT := h _ _
    _ ⭢ FF := red_K _ _


/--
To define `Rec x g n := if n==0 then x else (Rec x g (Pred n))`, we obtain a fixed point of
R ↦ λ x g n. Cond ⬝ (IsZero ⬝ n) ⬝ x ⬝ (g ⬝ a ⬝ (R ⬝ x ⬝ g ⬝ (Pred ⬝ n)))
-/
def RecAuxPoly : SKI.Polynomial 4 :=
  SKI.Cond ⬝' &1 ⬝' (&2 ⬝' &3 ⬝' (&0 ⬝' &1 ⬝' &2 ⬝' (Pred ⬝' &3))) ⬝' (IsZero ⬝' &3)
/-- A term representing RecAux -/
def RecAux : SKI := RecAuxPoly.toSKI
theorem recAux_def (R₀ x g a : SKI) :
    (RecAux ⬝ R₀ ⬝ x ⬝ g ⬝ a) ↠
      SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (R₀ ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a)  :=
  RecAuxPoly.toSKI_correct [R₀, x, g, a] (by simp)

/--
We define Rec so that
`Rec ⬝ x ⬝ g ⬝ a ↠ SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a)`
-/
def Rec : SKI := fixedPoint RecAux
theorem rec_def (x g a : SKI) :
  (Rec ⬝ x ⬝ g ⬝ a) ↠ SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) := calc
  _ ↠ RecAux ⬝ Rec ⬝ x ⬝ g ⬝ a := by
      apply MRed.head; apply MRed.head; apply MRed.head
      apply fixedPoint_correct
  _ ↠ SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) := recAux_def Rec x g a

theorem rec_zero (x g a : SKI) (ha : IsChurch 0 a) : (Rec ⬝ x ⬝ g ⬝ a) ↠ x := by
  calc
  _ ↠ SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) := rec_def _ _ _
  _ ↠ if (Nat.beq 0 0) then x else (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) := by
      apply cond_correct
      exact isZero_correct 0 a ha

theorem rec_succ (n : Nat) (x g a : SKI) (ha : IsChurch (n + 1) a) :
    (Rec ⬝ x ⬝ g ⬝ a) ↠ g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a)) := by
  calc
  _ ↠ SKI.Cond ⬝ x ⬝ (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) ⬝ (IsZero ⬝ a) := rec_def _ _ _
  _ ↠ if (Nat.beq (n+1) 0) then x else (g ⬝ a ⬝ (Rec ⬝ x ⬝ g ⬝ (Pred ⬝ a))) := by
      apply cond_correct
      exact isZero_correct (n+1) a ha


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

theorem rfindAboveAux_base (R₀ f a : SKI) (hfa : IsChurch 0 (f ⬝ a)) :
    (RFindAboveAux ⬝ R₀ ⬝ a ⬝ f) ↠ a := calc
  _ ↠ SKI.Cond ⬝ a ⬝ (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) := rfindAboveAux_def _ _ _
  _ ↠ if (Nat.beq 0 0) then a else (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) := by
      apply cond_correct
      apply isZero_correct _ _ hfa
theorem rfindAboveAux_step (R₀ f a : SKI) {m : Nat} (hfa : IsChurch (m + 1) (f ⬝ a)) :
    (RFindAboveAux ⬝ R₀ ⬝ a ⬝ f) ↠ R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f := calc
  _ ↠ SKI.Cond ⬝ a ⬝ (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) ⬝ (IsZero ⬝ (f ⬝ a)) := rfindAboveAux_def _ _ _
  _ ↠ if (Nat.beq (m+1) 0) then a else (R₀ ⬝ (SKI.Succ ⬝ a) ⬝ f) := by
      apply cond_correct
      apply isZero_correct _ _ hfa

/-- Find the minimal root of `fNat` above a number n -/
def RFindAbove : SKI := RFindAboveAux.fixedPoint

/-- One unfolding of `RFindAbove`: apply the fixed-point combinator once. -/
theorem RFindAbove_unfold (x g : SKI) :
    (RFindAbove ⬝ x ⬝ g) ↠ RFindAboveAux ⬝ RFindAbove ⬝ x ⬝ g := by
  apply MRed.head; apply MRed.head; exact fixedPoint_correct _

/-- Generalized root-finding that works with pointwise properties rather than a total
    function. At the root `m + n`, `f` yields Church 0; below, a nonzero Church numeral. -/
theorem RFindAbove_correct' (f x : SKI) (n m : Nat) (hx : IsChurch m x)
    (hf_root : ∀ y, IsChurch (m + n) y → IsChurch 0 (f ⬝ y))
    (hf_below : ∀ i < n, ∀ y, IsChurch (m + i) y →
      ∃ k, IsChurch (k + 1) (f ⬝ y)) :
    IsChurch (m + n) (RFindAbove ⬝ x ⬝ f) := by
  induction n generalizing m x
  all_goals apply isChurch_trans _ (RFindAbove_unfold x f)
  case zero =>
    simp only [Nat.add_zero] at *
    apply isChurch_trans (a' := x)
    · exact rfindAboveAux_base _ _ _ (hf_root x hx)
    · exact hx
  case succ n ih =>
    apply isChurch_trans (a' := RFindAbove ⬝ (SKI.Succ ⬝ x) ⬝ f)
    · obtain ⟨k, hk⟩ := hf_below 0 (by omega) x (by simpa using hx)
      exact rfindAboveAux_step _ _ _ hk
    · rw [show m + (n + 1) = (m + 1) + n from by omega]
      exact ih (SKI.Succ ⬝ x) (m + 1) (succ_correct _ x hx)
        (fun y hy => hf_root y (by rw [show m + 1 + n = m + (n + 1) from by omega] at hy; exact hy))
        (fun i hi y hy => hf_below (i + 1) (by omega) y (by
          rw [show m + 1 + i = m + (i + 1) from by omega] at hy; exact hy))

theorem RFindAbove_correct (fNat : Nat → Nat) (f x : SKI)
    (hf : ∀ i : Nat, ∀ y : SKI, IsChurch i y → IsChurch (fNat i) (f ⬝ y))
    (n m : Nat) (hx : IsChurch m x) (hroot : fNat (m+n) = 0) (hpos : ∀ i < n, fNat (m+i) ≠ 0) :
    IsChurch (m+n) (RFindAbove ⬝ x ⬝ f) := by
  apply RFindAbove_correct' f x n m hx
  · intro y hy; exact hroot ▸ hf (m + n) y hy
  · intro i hi y hy
    have hne := hpos i hi
    refine ⟨(fNat (m + i)) - 1, ?_⟩
    have : fNat (m + i) - 1 + 1 = fNat (m + i) := by omega
    rw [this]; exact hf (m + i) y hy


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
def AddPoly : SKI.Polynomial 2 := &0 ⬝' SKI.Succ ⬝' &1
/-- A term representing addition on church numerals -/
protected def Add : SKI := AddPoly.toSKI
theorem add_def (a b : SKI) : (SKI.Add ⬝ a ⬝ b) ↠ a ⬝ SKI.Succ ⬝ b :=
  AddPoly.toSKI_correct [a, b] (by simp)

theorem add_correct (n m : Nat) (a b : SKI) (ha : IsChurch n a) (hb : IsChurch m b) :
    IsChurch (n + m) (SKI.Add ⬝ a ⬝ b) := by
  refine isChurch_trans (n + m) (a' := Church n SKI.Succ b) ?_ ?_
  · calc
    _ ↠ a ⬝ SKI.Succ ⬝ b := add_def a b
    _ ↠ Church n SKI.Succ b := ha SKI.Succ b
  · clear ha
    induction n with
      | zero => simp_rw [Nat.zero_add, Church]; exact hb
      | succ n ih =>
        simp_rw [Nat.add_right_comm, Church]
        exact succ_correct _ _ ih

/-- Multiplication: λ n m. n (Add m) Zero -/
def MulPoly : SKI.Polynomial 2 := &0 ⬝' (SKI.Add ⬝' &1) ⬝' SKI.Zero
/-- A term representing multiplication on church numerals -/
protected def Mul : SKI := MulPoly.toSKI
theorem mul_def (a b : SKI) : (SKI.Mul ⬝ a ⬝ b) ↠ a ⬝ (SKI.Add ⬝ b) ⬝ SKI.Zero :=
  MulPoly.toSKI_correct [a, b] (by simp)

theorem mul_correct {n m : Nat} {a b : SKI} (ha : IsChurch n a) (hb : IsChurch m b) :
    IsChurch (n * m) (SKI.Mul ⬝ a ⬝ b) := by
  refine isChurch_trans (n * m) (a' := Church n (SKI.Add ⬝ b) SKI.Zero) ?_ ?_
  · exact Trans.trans (mul_def a b) (ha (SKI.Add ⬝ b) SKI.Zero)
  · clear ha
    induction n with
      | zero => simp_rw [Nat.zero_mul, Church]; exact zero_correct
      | succ n ih =>
        simp_rw [Nat.add_mul, Nat.one_mul, Nat.add_comm, Church]
        exact add_correct m (n * m) b (Church n (SKI.Add ⬝ b) SKI.Zero) hb ih

/-- Subtraction: λ n m. n Pred m -/
def SubPoly : SKI.Polynomial 2 := &1 ⬝' Pred ⬝' &0
/-- A term representing subtraction on church numerals -/
protected def Sub : SKI := SubPoly.toSKI
theorem sub_def (a b : SKI) : (SKI.Sub ⬝ a ⬝ b) ↠ b ⬝ Pred ⬝ a :=
  SubPoly.toSKI_correct [a, b] (by simp)

theorem sub_correct (n m : Nat) (a b : SKI) (ha : IsChurch n a) (hb : IsChurch m b) :
    IsChurch (n - m) (SKI.Sub ⬝ a ⬝ b) := by
  refine isChurch_trans (n - m) (a' := Church m Pred a) ?_ ?_
  · calc
    _ ↠ b ⬝ Pred ⬝ a := sub_def a b
    _ ↠ Church m Pred a := hb Pred a
  · clear hb
    induction m with
      | zero => simp_rw [Nat.sub_zero, Church]; exact ha
      | succ m ih =>
        simp_rw [←Nat.sub_sub, Church]
        exact pred_correct _ _ ih

/-- Comparison: (. ≤ .) := λ n m. IsZero ⬝ (Sub ⬝ n ⬝ m) -/
def LEPoly : SKI.Polynomial 2 := IsZero ⬝' (SKI.Sub ⬝' &0 ⬝' &1)
/-- A term representing comparison on church numerals -/
protected def LE : SKI := LEPoly.toSKI
theorem le_def (a b : SKI) : (SKI.LE ⬝ a ⬝ b) ↠ IsZero ⬝ (SKI.Sub ⬝ a ⬝ b) :=
  LEPoly.toSKI_correct [a, b] (by simp)

theorem le_correct (n m : Nat) (a b : SKI) (ha : IsChurch n a) (hb : IsChurch m b) :
    IsBool (n ≤ m) (SKI.LE ⬝ a ⬝ b) := by
  simp only [← decide_eq_decide.mpr <| Nat.sub_eq_zero_iff_le]
  apply isBool_trans (a' := IsZero ⬝ (SKI.Sub ⬝ a ⬝ b)) (h := le_def _ _)
  apply isZero_correct
  apply sub_correct <;> assumption

/-! ### Integer square root -/

/-- Inner condition for Sqrt: with &0 = n, &1 = k,
    computes `if n < (k+1)² then 0 else 1`. -/
def SqrtCondPoly : SKI.Polynomial 2 :=
  SKI.Cond ⬝' SKI.Zero ⬝' SKI.One
           ⬝' (SKI.Neg ⬝' (SKI.LE ⬝' (SKI.Mul ⬝' (SKI.Succ ⬝' &1) ⬝' (SKI.Succ ⬝' &1)) ⬝' &0))

/-- SKI term for the inner condition of Sqrt -/
def SqrtCond : SKI := SqrtCondPoly.toSKI

/-- `SqrtCond ⬝ n ⬝ k` reduces to: return 0 if `(k+1)² > n`, else 1.
    Used by `RFind` to locate the smallest such `k`, which is `√n`. -/
theorem sqrtCond_def (cn ck : SKI) :
    (SqrtCond ⬝ cn ⬝ ck) ↠
      SKI.Cond ⬝ SKI.Zero ⬝ SKI.One ⬝
        (SKI.Neg ⬝ (SKI.LE ⬝ (SKI.Mul ⬝ (SKI.Succ ⬝ ck) ⬝ (SKI.Succ ⬝ ck)) ⬝ cn)) :=
  SqrtCondPoly.toSKI_correct [cn, ck] (by simp)

/-- Sqrt n = smallest k such that (k+1)² > n, i.e., the integer square root.
    Defined as `λ n. RFind (SqrtCond n)`. -/
def SqrtPoly : SKI.Polynomial 1 := RFind ⬝' (SqrtCond ⬝' &0)

/-- SKI term for integer square root -/
def Sqrt : SKI := SqrtPoly.toSKI

/-- `Sqrt ⬝ n` reduces to an `RFind` search for the smallest `k` with `(k+1)² > n`. -/
theorem sqrt_def (cn : SKI) : (Sqrt ⬝ cn) ↠ RFind ⬝ (SqrtCond ⬝ cn) :=
  SqrtPoly.toSKI_correct [cn] (by simp)

/-- `Sqrt` correctly computes `Nat.sqrt`. -/
theorem sqrt_correct (n : Nat) (cn : SKI) (hcn : IsChurch n cn) :
    IsChurch (Nat.sqrt n) (Sqrt ⬝ cn) := by
  apply isChurch_trans _ (sqrt_def cn)
  apply RFind_correct (fun k => if n < (k + 1) * (k + 1) then 0 else 1) (SqrtCond ⬝ cn)
  · -- SqrtCond ⬝ cn correctly computes the function
    intro i y hy
    apply isChurch_trans _ (sqrtCond_def cn y)
    have hsucc := succ_correct i y hy
    have hle := le_correct _ n _ cn (mul_correct hsucc hsucc) hcn
    have hneg := neg_correct _ _ hle
    apply isChurch_trans _ (cond_correct _ _ _ _ hneg)
    grind
  · -- fNat (Nat.sqrt n) = 0
    simp [Nat.lt_succ_sqrt]
  · -- ∀ i < Nat.sqrt n, fNat i ≠ 0
    grind [Nat.le_sqrt]

/-! ### Nat pairing (matching Mathlib's `Nat.pair`) -/

/-- NatPair a b = if a < b then b*b + a else a*a + a + b.
    With &0 = a, &1 = b. The condition `a < b` is `¬(b ≤ a)`. -/
def NatPairPoly : SKI.Polynomial 2 :=
  SKI.Cond ⬝' (SKI.Add ⬝' (SKI.Mul ⬝' &1 ⬝' &1) ⬝' &0)
           ⬝' (SKI.Add ⬝' (SKI.Add ⬝' (SKI.Mul ⬝' &0 ⬝' &0) ⬝' &0) ⬝' &1)
           ⬝' (SKI.Neg ⬝' (SKI.LE ⬝' &1 ⬝' &0))

/-- SKI term for Nat pairing -/
def NatPair : SKI := NatPairPoly.toSKI

/-- `NatPair ⬝ a ⬝ b` reduces to: if `a < b` then `b² + a`, else `a² + a + b`. -/
theorem natPair_def (ca cb : SKI) :
    (NatPair ⬝ ca ⬝ cb) ↠
      SKI.Cond ⬝ (SKI.Add ⬝ (SKI.Mul ⬝ cb ⬝ cb) ⬝ ca)
               ⬝ (SKI.Add ⬝ (SKI.Add ⬝ (SKI.Mul ⬝ ca ⬝ ca) ⬝ ca) ⬝ cb)
               ⬝ (SKI.Neg ⬝ (SKI.LE ⬝ cb ⬝ ca)) :=
  NatPairPoly.toSKI_correct [ca, cb] (by simp)

/-- `NatPair` correctly computes `Nat.pair`. -/
theorem natPair_correct (a b : Nat) (ca cb : SKI)
    (ha : IsChurch a ca) (hb : IsChurch b cb) :
    IsChurch (Nat.pair a b) (NatPair ⬝ ca ⬝ cb) := by
  simp only [Nat.pair]
  apply isChurch_trans _ (natPair_def ca cb)
  have hcond := neg_correct _ _ (le_correct b a cb ca hb ha)
  apply isChurch_trans _ (cond_correct _ _ _ _ hcond)
  by_cases hab : a < b
  · grind [add_correct _ _ _ _ (mul_correct hb hb) ha]
  · grind [add_correct _ _ _ _ (add_correct _ _ _ _ (mul_correct ha ha) ha) hb]

/-! ### Nat unpairing (matching Mathlib's `Nat.unpair`) -/

/-- `NatUnpairLeft n = if n - s² < s then n - s² else s` where `s = Nat.sqrt n`. -/
def NatUnpairLeftPoly : SKI.Polynomial 1 :=
  let s := Sqrt ⬝' &0
  let s2 := SKI.Mul ⬝' s ⬝' s
  let diff := SKI.Sub ⬝' &0 ⬝' s2
  let cond := SKI.Neg ⬝' (SKI.LE ⬝' s ⬝' diff)
  SKI.Cond ⬝' diff ⬝' s ⬝' cond

/-- SKI term for left projection of Nat.unpair -/
def NatUnpairLeft : SKI := NatUnpairLeftPoly.toSKI

/-- `NatUnpairLeft ⬝ n` reduces to: let `s = √n` and `d = n - s²`;
    return `d` if `d < s`, else `s`. -/
theorem natUnpairLeft_def (cn : SKI) :
    (NatUnpairLeft ⬝ cn) ↠
      SKI.Cond ⬝ (SKI.Sub ⬝ cn ⬝ (SKI.Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn)))
               ⬝ (Sqrt ⬝ cn)
               ⬝ (SKI.Neg ⬝ (SKI.LE ⬝ (Sqrt ⬝ cn)
                    ⬝ (SKI.Sub ⬝ cn ⬝ (SKI.Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn))))) :=
  NatUnpairLeftPoly.toSKI_correct [cn] (by simp)

/-- Common Church numeral witnesses for `Nat.sqrt` and the difference `n - (Nat.sqrt n)²`. -/
private theorem natUnpair_church (n : Nat) (cn : SKI) (hcn : IsChurch n cn) :
    IsChurch (Nat.sqrt n) (Sqrt ⬝ cn) ∧
    IsChurch (n - Nat.sqrt n * Nat.sqrt n)
      (SKI.Sub ⬝ cn ⬝ (SKI.Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn))) := by
  have hs := sqrt_correct n cn hcn
  exact ⟨hs, sub_correct n _ cn _ hcn (mul_correct hs hs)⟩

/-- `NatUnpairLeft` correctly computes the first component of `Nat.unpair`. -/
theorem natUnpairLeft_correct (n : Nat) (cn : SKI) (hcn : IsChurch n cn) :
    IsChurch (Nat.unpair n).1 (NatUnpairLeft ⬝ cn) := by
  apply isChurch_trans _ (natUnpairLeft_def cn)
  obtain ⟨hs, hdiff⟩ := natUnpair_church n cn hcn
  have hcond := neg_correct _ _ (le_correct _ _ _ _ hs hdiff)
  apply isChurch_trans _ (cond_correct _ _ _ _ hcond)
  by_cases h : n - n.sqrt ^ 2 < n.sqrt <;> grind [Nat.unpair]

/-- NatUnpairRight n = let s = sqrt n in if n - s² < s then s else n - s² - s. -/
def NatUnpairRightPoly : SKI.Polynomial 1 :=
  let s := Sqrt ⬝' &0
  let s2 := SKI.Mul ⬝' s ⬝' s
  let diff := SKI.Sub ⬝' &0 ⬝' s2
  let cond := SKI.Neg ⬝' (SKI.LE ⬝' s ⬝' diff)
  SKI.Cond ⬝' s ⬝' (SKI.Sub ⬝' diff ⬝' s) ⬝' cond

/-- SKI term for right projection of Nat.unpair -/
def NatUnpairRight : SKI := NatUnpairRightPoly.toSKI

/-- `NatUnpairRight ⬝ n` reduces to: let `s = √n` and `d = n - s²`;
    return `s` if `d < s`, else `d - s`. -/
theorem natUnpairRight_def (cn : SKI) :
    (NatUnpairRight ⬝ cn) ↠
      SKI.Cond ⬝ (Sqrt ⬝ cn)
               ⬝ (SKI.Sub ⬝ (SKI.Sub ⬝ cn ⬝ (SKI.Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn)))
                            ⬝ (Sqrt ⬝ cn))
               ⬝ (SKI.Neg ⬝ (SKI.LE ⬝ (Sqrt ⬝ cn)
                    ⬝ (SKI.Sub ⬝ cn ⬝ (SKI.Mul ⬝ (Sqrt ⬝ cn) ⬝ (Sqrt ⬝ cn))))) :=
  NatUnpairRightPoly.toSKI_correct [cn] (by simp)

/-- `NatUnpairRight` correctly computes the second component of `Nat.unpair`. -/
theorem natUnpairRight_correct (n : Nat) (cn : SKI) (hcn : IsChurch n cn) :
    IsChurch (Nat.unpair n).2 (NatUnpairRight ⬝ cn) := by
  apply isChurch_trans _ (natUnpairRight_def cn)
  obtain ⟨hs, hdiff⟩ := natUnpair_church n cn hcn
  have hcond := neg_correct _ _ (le_correct _ _ _ _ hs hdiff)
  apply isChurch_trans _ (cond_correct _ _ _ _ hcond)
  grind [Nat.unpair, sub_correct _ _ _ _ hdiff hs]

end SKI

end Cslib
