/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Computability.CombinatoryLogic.Defs

/-!
# Basic results for the SKI calculus

## Main definition

- `Polynomial`: the type of SKI terms with fixed number of "holes" (read: free variables).

## Notation

- `⬝'` : application between polynomials,
- `&i` : the ith free variable of a polynomial.

## Main results

- Bracket abstraction: an algorithm `Polynomial.toSKI` to convert a polynomial
$Γ(x_0, ..., x_{n-1})$ into a term such that (`Polynomial.toSKI_correct`)
`Γ.toSKI ⬝ t₁ ⬝ ... ⬝ tₙ` reduces to `Γ(t₁, ..., tₙ)`.

## References

For a presentation of the bracket abstraction algorithm see:
<https://web.archive.org/web/19970727171324/http://www.cs.oberlin.edu/classes/cs280/labs/lab4/lab43.html#@l13>
-/

namespace SKI

open ReductionStep

/-! ### Polynomials and the bracket astraction algorithm -/

protected inductive Polynomial (n : Nat) : Type _ where
  | term : SKI → SKI.Polynomial n
  | var : Fin n → SKI.Polynomial n
  | ap : SKI.Polynomial n → SKI.Polynomial n → SKI.Polynomial n

infixl:100 " ⬝' " => SKI.Polynomial.ap

/-- Notation by analogy with pointers in C -/
prefix:101 "&" => SKI.Polynomial.var

instance CoeTermContext (n : Nat) : Coe SKI (SKI.Polynomial n) := ⟨SKI.Polynomial.term⟩

def Polynomial.eval {n : Nat} (Γ : SKI.Polynomial n) (l : List SKI) (hl : List.length l = n) :
    SKI :=
  match Γ with
  | SKI.Polynomial.term x => x
  | SKI.Polynomial.var i => l[i]
  | SKI.Polynomial.ap Γ Δ => (Γ.eval l hl) ⬝ (Δ.eval l hl)

def Polynomial.varFreeToSKI (Γ : SKI.Polynomial 0) : SKI := Γ.eval [] (by trivial)

/-- Inductively define a polynomial `Γ'` so that (up to the fact that we haven't
defined reduction on polynomials) `Γ' ⬝ t ⇒* Γ[xₙ ← t]`. -/
def Polynomial.elimVar {n : Nat} (Γ : SKI.Polynomial (n+1)) : SKI.Polynomial n :=
  match Γ with
  /- The K-combinator leaves plain terms unchanged by substitution `K ⬝ x ⬝ t ⇒ x` -/
  | SKI.Polynomial.term x => K ⬝' x
  /- Variables other than `xₙ` use the K-combinator as above, for `xₙ` we use `I`. -/
  | SKI.Polynomial.var i => by
    by_cases i<n
    case pos h =>
      exact K ⬝' (SKI.Polynomial.var <| @Fin.ofNat n ⟨Nat.ne_zero_of_lt h⟩ i)
    case neg h => exact ↑I
  /- The S-combinator inductively applies the substitution to the subterms of an application. -/
  | SKI.Polynomial.ap Γ Δ => S ⬝' Γ.elimVar ⬝' Δ.elimVar


/--
Correctness for the elimVar algorithm, which provides the inductive step of the bracket abstraction
algorithm. We induct backwards on the list, corresponding to applying the transformation from the
inside out. Since we haven't defined reduction for polynomials, we substitute arbitrary terms
for the inner variables.
-/
theorem Polynomial.elimVar_correct {n : Nat} (Γ : SKI.Polynomial (n+1)) (ys : List SKI)
    (hys : ys.length = n) (z : SKI) :
    Γ.elimVar.eval ys hys ⬝ z ⇒* Γ.eval (ys ++ [z])
      (by rw [List.length_append, hys, List.length_singleton])
    := by
  match n, Γ with
  | _, SKI.Polynomial.term x =>
    simp_rw [SKI.Polynomial.elimVar, SKI.Polynomial.eval]
    exact largeRed_K _ _
  | _, SKI.Polynomial.ap Γ Δ =>
    simp_rw [SKI.Polynomial.elimVar, SKI.Polynomial.eval]
    trans Γ.elimVar.eval ys hys ⬝ z ⬝ (Δ.elimVar.eval ys hys ⬝ z)
    . exact largeRed_S _ _ _
    . apply parallel_large_reduction
      . exact elimVar_correct Γ ys hys z
      . exact elimVar_correct Δ ys hys z
  | n, SKI.Polynomial.var i =>
    rw [SKI.Polynomial.elimVar]
    split
    /- This part is quite messy because of the list indexing: possibly it could be cleaned up. -/
    case isTrue hi =>
      simp_rw [SKI.Polynomial.eval]
      have h : ys[↑i] = (ys ++ [z])[i]'(by simp [hys]) := by
        simp only [Fin.getElem_fin]
        rw [List.getElem_append_left]
      rw [←h]
      simp only [Fin.getElem_fin, Fin.val_ofNat]
      have : ↑i%n=↑i := by exact Nat.mod_eq_of_lt hi
      simp_rw [this]
      exact largeRed_K _ _
    case isFalse hi =>
      have app_len : (ys ++ [z]).length = n+1 := by simpa
      simp_rw [SKI.Polynomial.eval]
      replace hi := Nat.eq_of_lt_succ_of_not_lt i.isLt hi
      simp_rw [Fin.getElem_fin, hi]
      have : (ys ++ [z])[n]'(by rw [app_len]; exact Nat.lt_add_one n) = z := by
        rw [List.getElem_append_right] <;> simp [hys]
      rw [this]
      exact largeRed_I _

def Polynomial.toSKI {n : Nat} (Γ : SKI.Polynomial n) : SKI :=
  match n with
  | 0 => Γ.varFreeToSKI
  | _+1 => Γ.elimVar.toSKI

/-- Correctness for the toSKI (bracket abstraction) algorithm. -/
theorem Polynomial.toSKI_correct {n : Nat} (Γ : SKI.Polynomial n) (xs : List SKI)
    (hxs : xs.length = n) : Γ.toSKI.applyList xs ⇒* Γ.eval xs hxs := by
  match n with
  | 0 =>
    unfold toSKI varFreeToSKI applyList
    rw [List.length_eq_zero_iff] at hxs
    simp_rw [hxs, List.foldl_nil]
    apply largeRed_refl
  | n+1 =>
    -- show that xs = ys + [z]
    have : xs ≠ [] := List.ne_nil_of_length_eq_add_one hxs
    let h : xs = [] ∨ ∃ (l' : List SKI), ∃ (b : SKI), xs = l'.concat b :=
      List.eq_nil_or_concat xs
    simp_rw [this, false_or, List.concat_eq_append] at h
    replace ⟨ys, z, h⟩ := h
    -- apply inductive step, using elimVar_correct
    unfold toSKI
    have : ys.length = n := by
      replace h := congr_arg List.length <| h
      simp_rw [List.length_append, List.length_singleton, hxs] at h
      exact Nat.succ_inj.mp (id (Eq.symm h))
    simp_rw [h, applyList_concat]
    trans Γ.elimVar.eval ys this ⬝ z
    · apply largeRed_head
      exact SKI.Polynomial.toSKI_correct Γ.elimVar ys this
    · exact SKI.Polynomial.elimVar_correct Γ ys this z


/-!
### Basic auxilliary combinators.

Each combinator is defined by a polynomial, which is then proved to have the reduction property
we want. Before each definition we provide its lambda calculus equivalent. If there is accepted
notation for a given combinator, we use that (given everywhere a capital letter), otherwise we
choose a descriptive name.
-/

/-- Reversal: R := λ x y. y x -/
def RPoly : SKI.Polynomial 2 := &1 ⬝' &0
def R : SKI := RPoly.toSKI
theorem R_def (x y : SKI) : R ⬝ x ⬝ y ⇒* y ⬝ x := by
  have : _ := RPoly.toSKI_correct [x, y] (by simp)
  simp_rw [applyList] at this
  simpa

/-- Composition: B := λ f g x. f (g x) -/
def BPoly : SKI.Polynomial 3 := &0 ⬝' (&1 ⬝' &2)
def B : SKI := BPoly.toSKI
theorem B_def (f g x : SKI) : B ⬝ f ⬝ g ⬝ x ⇒* f ⬝ (g ⬝ x) := by
  have : _ := BPoly.toSKI_correct [f, g, x] (by simp)
  simp_rw [applyList] at this
  simpa

/-- C := λ f x y. f y x -/
def CPoly : SKI.Polynomial 3 := &0 ⬝' &2 ⬝' &1
def C : SKI := CPoly.toSKI
theorem C_def (f x y : SKI) : C ⬝ f ⬝ x ⬝ y ⇒* f ⬝ y ⬝ x := by
  have : _ := CPoly.toSKI_correct [f, x, y] (by simp)
  simp_rw [applyList] at this
  simpa

/-- Rotate right: RotR := λ x y z. z x y -/
def RotRPoly : SKI.Polynomial 3 := &2 ⬝' &0 ⬝' &1
def RotR : SKI := RotRPoly.toSKI
theorem rotR_def (x y z : SKI) : RotR ⬝ x ⬝ y ⬝ z ⇒* z ⬝ x ⬝ y := by
  have : _ := RotRPoly.toSKI_correct [x, y, z] (by simp)
  simp_rw [applyList] at this
  simpa

/-- Rotate left: RotR := λ x y z. y z x -/
def RotLPoly : SKI.Polynomial 3 := &1 ⬝' &2 ⬝' &0
def RotL : SKI := RotLPoly.toSKI
theorem rotL_def (x y z : SKI) : RotL ⬝ x ⬝ y ⬝ z ⇒* y ⬝ z ⬝ x := by
  have : _ := RotLPoly.toSKI_correct [x, y, z] (by simp)
  simp_rw [applyList] at this
  simpa

/-- Self application: δ := λ x. x x -/
def δPoly : SKI.Polynomial 1 := &0 ⬝' &0
def δ : SKI := δPoly.toSKI
theorem δ_def (x : SKI) : δ ⬝ x ⇒* x ⬝ x := by
  have : _ := δPoly.toSKI_correct [x] (by simp)
  simp_rw [applyList] at this
  simpa

/-- H := λ f x. f (x x) -/
def HPoly : SKI.Polynomial 2 := &0 ⬝' (&1 ⬝' &1)
def H : SKI := HPoly.toSKI
theorem H_def (f x : SKI) : H ⬝ f ⬝ x ⇒* f ⬝ (x ⬝ x) := by
  have : _ := HPoly.toSKI_correct [f, x] (by simp)
  simp_rw [applyList] at this
  simpa

/-- Haskell's fixed-point combinator: Y := λ f. H f (H f) -/
def YPoly : SKI.Polynomial 1 := H ⬝' &0 ⬝' (H ⬝' &0)
def Y : SKI := YPoly.toSKI
theorem Y_def (f : SKI) : Y ⬝ f ⇒* H ⬝ f ⬝ (H ⬝ f) := by
  have : _ := YPoly.toSKI_correct [f] (by simp)
  simp_rw [applyList] at this
  simpa

/-- The fixed-point property of the Y-combinator -/
theorem Y_correct (f : SKI) : CommonReduct (Y ⬝ f) (f ⬝ (Y ⬝ f)) := by
  use f ⬝ (H ⬝ f ⬝ (H ⬝ f))
  constructor
  · calc
    _ ⇒* H ⬝ f ⬝ (H ⬝ f) := Y_def f
    _ ⇒* f ⬝ (H ⬝ f ⬝ (H ⬝ f)) := H_def f (H ⬝ f)
  · apply largeRed_tail
    exact Y_def f

/--
It is useful to be able to produce a term such that the fixed point property holds on-the-nose,
rather than up to a common reduct. An alternative is to use Turing's fixed-point combinator
(defined below).
-/
def fixedPoint (f : SKI) : SKI := H ⬝ f ⬝ (H ⬝ f)
theorem fixedPoint_correct (f : SKI) : f.fixedPoint ⇒* f ⬝ f.fixedPoint := H_def f (H ⬝ f)


def ΘAuxPoly : SKI.Polynomial 2 := &1 ⬝' (&0 ⬝' &0 ⬝' &1)
def ΘAux : SKI := ΘAuxPoly.toSKI
theorem ΘAux_def (x y : SKI) : ΘAux ⬝ x ⬝ y ⇒* y ⬝ (x ⬝ x ⬝ y) := by
  have : _ := ΘAuxPoly.toSKI_correct [x, y] (by simp)
  simp_rw [applyList] at this
  simpa

/--Turing's fixed-point combinator: Θ := (λ x y. y (x x y)) (λ x y. y (x x y)) -/
def Θ : SKI := ΘAux ⬝ ΘAux
theorem Θ_correct (f : SKI) : Θ ⬝ f ⇒* f ⬝ (Θ ⬝ f) := ΘAux_def ΘAux f


/-! ### Church Booleans -/

def IsBool (u : Bool) (a : SKI) : Prop :=
  ∀ x y : SKI, a ⬝ x ⬝ y ⇒* (if u then x else y)

theorem isBool_trans (u : Bool) (a a' : SKI) (h : a ⇒* a') (ha' : IsBool u a') :
    IsBool u a := by
  intro x y
  trans a' ⬝ x ⬝ y
  · apply largeRed_head
    apply largeRed_head
    exact h
  · exact ha' x y

/-- Standard true: TT := λ x y. x -/
def TT : SKI := K
theorem TT_correct : IsBool true TT := fun x y ↦ largeRed_K x y

/-- Standard false: FF := λ x y. y -/
def FF : SKI := K ⬝ I
theorem FF_correct : IsBool false FF :=
  fun x y ↦ calc
    FF ⬝ x ⬝ y ⇒ I ⬝ y := by apply red_head; exact red_K I x
    _         ⇒ y := red_I y

/-- Conditional: Cond x y b := if b then x else y -/
protected def Cond : SKI := RotR
theorem cond_correct (a x y : SKI) (u : Bool) (h : IsBool u a) :
    SKI.Cond ⬝ x ⬝ y ⬝ a ⇒* if u then x else y := by
  trans a ⬝ x ⬝ y
  · exact rotR_def x y a
  · exact h x y

/-- Neg := λ a. Cond FF TT a -/
protected def Neg : SKI := SKI.Cond ⬝ FF ⬝ TT
theorem neg_correct (a : SKI) (ua : Bool) (h : IsBool ua a) : IsBool (¬ ua) (SKI.Neg ⬝ a) := by
  apply isBool_trans (a' := if ua then FF else TT)
  · apply cond_correct (h := h)
  · cases ua
    · simp [TT_correct]
    · simp [FF_correct]

/-- And := λ a b. Cond (Cond TT FF b) FF a -/
def AndPoly : SKI.Polynomial 2 := SKI.Cond ⬝' (SKI.Cond ⬝ TT ⬝ FF ⬝' &1) ⬝' FF ⬝' &0
protected def And : SKI := AndPoly.toSKI
theorem and_def (a b : SKI) : SKI.And ⬝ a ⬝ b ⇒* SKI.Cond ⬝ (SKI.Cond ⬝ TT ⬝ FF ⬝ b) ⬝ FF ⬝ a := by
  have : _ := AndPoly.toSKI_correct [a, b] (by simp)
  simp_rw [applyList] at this
  simpa
theorem and_correct (a b : SKI) (ua ub : Bool) (ha : IsBool ua a) (hb : IsBool ub b) :
    IsBool (ua && ub) (SKI.And ⬝ a ⬝ b) := by
  apply isBool_trans (a' := SKI.Cond ⬝ (SKI.Cond ⬝ TT ⬝ FF ⬝ b) ⬝ FF ⬝ a) (h := and_def _ _)
  cases ua
  · simp_rw [Bool.false_and] at ⊢
    apply isBool_trans (a' := FF) (ha' := FF_correct) (h := cond_correct a _ _ false ha)
  · simp_rw [Bool.true_and] at ⊢
    apply isBool_trans (a' := SKI.Cond ⬝ TT ⬝ FF ⬝ b) (h := cond_correct a _ _ true ha)
    apply isBool_trans (a' := if ub = true then TT else FF) (h := cond_correct b _ _ ub hb)
    cases ub
    · simp [FF_correct]
    · simp [TT_correct]

def OrPoly : SKI.Polynomial 2 := SKI.Cond ⬝' TT ⬝' (SKI.Cond ⬝ TT ⬝ FF ⬝' &1) ⬝' &0
protected def Or : SKI := OrPoly.toSKI
theorem or_def (a b : SKI) : SKI.Or ⬝ a ⬝ b ⇒* SKI.Cond ⬝ TT ⬝ (SKI.Cond ⬝ TT ⬝ FF ⬝ b) ⬝ a := by
  have : _ := OrPoly.toSKI_correct [a, b] (by simp)
  simp_rw [applyList] at this
  simpa
theorem or_correct (a b : SKI) (ua ub : Bool) (ha : IsBool ua a) (hb : IsBool ub b) :
  IsBool (ua || ub) (SKI.Or ⬝ a ⬝ b) := by
  apply isBool_trans (a' := SKI.Cond ⬝ TT ⬝ (SKI.Cond ⬝ TT ⬝ FF ⬝ b) ⬝ a) (h := or_def _ _)
  cases ua
  · simp_rw [Bool.false_or]
    apply isBool_trans (a' := SKI.Cond ⬝ TT ⬝ FF ⬝ b) (h := cond_correct a _ _ false ha)
    apply isBool_trans (a' := if ub = true then TT else FF) (h := cond_correct b _ _ ub hb)
    cases ub
    · simp [FF_correct]
    · simp [TT_correct]
  · apply isBool_trans (a' := TT) (h := cond_correct a _ _ true ha)
    simp [TT_correct]


/- TODO?: other boolean connectives -/


/-! ### Pairs -/

def MkPair : SKI := SKI.Cond
def Fst : SKI := R ⬝ TT
def Snd : SKI := R ⬝ FF

theorem fst_correct (a b : SKI) : Fst ⬝ (MkPair ⬝ a ⬝ b) ⇒* a := by calc
  _ ⇒* SKI.Cond ⬝ a ⬝ b ⬝ TT := R_def _ _
  _ ⇒* a := cond_correct TT a b true TT_correct

theorem snd_correct (a b : SKI) : Snd ⬝ (MkPair ⬝ a ⬝ b) ⇒* b := by calc
  _ ⇒* SKI.Cond ⬝ a ⬝ b ⬝ FF := R_def _ _
  _ ⇒* b := cond_correct FF a b false FF_correct

/-- Unpaired f ⟨x, y⟩ := f x y, cf `Nat.unparied`. -/
def UnpairedPoly : SKI.Polynomial 2 := &0 ⬝' (Fst ⬝' &1) ⬝' (Snd ⬝' &1)
protected def Unpaired : SKI := UnpairedPoly.toSKI
theorem unpaired_def (f p : SKI) : SKI.Unpaired ⬝ f ⬝ p ⇒* f ⬝ (Fst ⬝ p) ⬝ (Snd ⬝ p) := by
  have : _ := UnpairedPoly.toSKI_correct [f, p] (by simp)
  simp_rw [applyList] at this
  assumption
theorem unpaired_correct (f x y : SKI) : SKI.Unpaired ⬝ f ⬝ (MkPair ⬝ x ⬝ y) ⇒* f ⬝ x ⬝ y := by
  trans f ⬝ (Fst ⬝ (MkPair ⬝ x ⬝ y)) ⬝ (Snd ⬝ (MkPair ⬝ x ⬝ y))
  . exact unpaired_def f _
  . apply parallel_large_reduction
    . apply largeRed_tail
      exact fst_correct _ _
    . exact snd_correct _ _

/-- Pair f g x := ⟨f x, g x⟩, cf `Primrec.Pair`. -/
def PairPoly : SKI.Polynomial 3 := MkPair ⬝' (&0 ⬝' &2) ⬝' (&1 ⬝' &2)
protected def Pair : SKI := PairPoly.toSKI
theorem pair_def (f g x : SKI) : SKI.Pair ⬝ f ⬝ g ⬝ x ⇒* MkPair ⬝ (f ⬝ x) ⬝ (g ⬝ x) := by
  have : _ := PairPoly.toSKI_correct [f, g, x] (by simp)
  simp_rw [applyList] at this
  assumption
