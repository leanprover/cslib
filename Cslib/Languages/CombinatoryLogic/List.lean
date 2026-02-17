/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Languages.CombinatoryLogic.Recursion

@[expose] public section

/-!
# Church-Encoded Lists in SKI Combinatory Logic

Church-encoded lists for proving SKI ≃ TM equivalence. A list is encoded as
`λ c n. c a₀ (c a₁ (... (c aₖ n)...))` where each `aᵢ` is a Church numeral.
-/

namespace Cslib

namespace SKI

open Red MRed

/-! ### Church List Representation -/

/-- A term correctly Church-encodes a list of natural numbers. -/
def IsChurchList : List ℕ → SKI → Prop
  | [], cns => ∀ c n : SKI, (cns ⬝ c ⬝ n) ↠ n
  | x :: xs, cns => ∀ c n : SKI,
      ∃ cx cxs : SKI, IsChurch x cx ∧ IsChurchList xs cxs ∧
        (cns ⬝ c ⬝ n) ↠ c ⬝ cx ⬝ (cxs ⬝ c ⬝ n)

/-- `IsChurchList` is preserved under multi-step reduction of the term. -/
theorem isChurchList_trans {ns : List ℕ} {cns cns' : SKI} (h : cns ↠ cns')
    (hcns' : IsChurchList ns cns') : IsChurchList ns cns := by
  match ns with
  | [] =>
    intro c n
    exact Trans.trans (parallel_mRed (MRed.head c h) .refl) (hcns' c n)
  | x :: xs =>
    intro c n
    obtain ⟨cx, cxs, hcx, hcxs, hred⟩ := hcns' c n
    exact ⟨cx, cxs, hcx, hcxs, Trans.trans (parallel_mRed (MRed.head c h) .refl) hred⟩

/-- Both components of a pair are Church lists. -/
structure IsChurchListPair (prev curr : List ℕ) (p : SKI) : Prop where
  fst : IsChurchList prev (Fst ⬝ p)
  snd : IsChurchList curr (Snd ⬝ p)

/-- IsChurchListPair is preserved under reduction. -/
@[scoped grind →]
theorem isChurchListPair_trans {prev curr : List ℕ} {p p' : SKI} (hp : p ↠ p')
    (hp' : IsChurchListPair prev curr p') : IsChurchListPair prev curr p := by
  constructor
  · apply isChurchList_trans (MRed.tail Fst hp)
    exact hp'.1
  · apply isChurchList_trans (MRed.tail Snd hp)
    exact hp'.2

namespace List

/-! ### Nil: The empty list -/

/-- nil = λ c n. n -/
def NilPoly : SKI.Polynomial 2 := &1

/-- The SKI term for the empty list. -/
def Nil : SKI := NilPoly.toSKI

/-- Reduction: `Nil ⬝ c ⬝ n ↠ n`. -/
theorem nil_def (c n : SKI) : (Nil ⬝ c ⬝ n) ↠ n :=
  NilPoly.toSKI_correct [c, n] (by simp)

/-- The empty list term correctly represents `[]`. -/
theorem nil_correct : IsChurchList [] Nil := nil_def

/-! ### Cons: Consing an element onto a list -/

/-- cons = λ x xs c n. c x (xs c n) -/
def ConsPoly : SKI.Polynomial 4 := &2 ⬝' &0 ⬝' (&1 ⬝' &2 ⬝' &3)

/-- The SKI term for list cons. -/
def Cons : SKI := ConsPoly.toSKI

/-- Reduction: `Cons ⬝ x ⬝ xs ⬝ c ⬝ n ↠ c ⬝ x ⬝ (xs ⬝ c ⬝ n)`. -/
theorem cons_def (x xs c n : SKI) :
    (Cons ⬝ x ⬝ xs ⬝ c ⬝ n) ↠ c ⬝ x ⬝ (xs ⬝ c ⬝ n) :=
  ConsPoly.toSKI_correct [x, xs, c, n] (by simp)

/-- Cons preserves Church list representation. -/
theorem cons_correct {x : ℕ} {xs : List ℕ} {cx cxs : SKI}
    (hcx : IsChurch x cx) (hcxs : IsChurchList xs cxs) :
    IsChurchList (x :: xs) (Cons ⬝ cx ⬝ cxs) := by
  intro c n
  use cx, cxs, hcx, hcxs
  exact cons_def cx cxs c n

/-- Singleton list correctness. -/
theorem singleton_correct {x : ℕ} {cx : SKI} (hcx : IsChurch x cx) :
    IsChurchList [x] (Cons ⬝ cx ⬝ Nil) :=
  cons_correct hcx nil_correct

/-- The canonical SKI term for a Church-encoded list. -/
def toChurch : List ℕ → SKI
  | [] => Nil
  | x :: xs => Cons ⬝ (SKI.toChurch x) ⬝ (toChurch xs)

/-- `toChurch [] = Nil`. -/
@[simp]
lemma toChurch_nil : toChurch [] = Nil := rfl

/-- `toChurch (x :: xs) = Cons ⬝ SKI.toChurch x ⬝ toChurch xs`. -/
@[simp]
lemma toChurch_cons (x : ℕ) (xs : List ℕ) :
    toChurch (x :: xs) = Cons ⬝ (SKI.toChurch x) ⬝ (toChurch xs) := rfl

/-- `toChurch ns` correctly represents `ns`. -/
theorem toChurch_correct (ns : List ℕ) : IsChurchList ns (toChurch ns) := by
  induction ns with
  | nil => exact nil_correct
  | cons x xs ih => exact cons_correct (SKI.toChurch_correct x) ih

/-! ### Head: Extract the head of a list -/

/-- headD d xs = xs K d (returns d for empty list) -/
def HeadDPoly : SKI.Polynomial 2 := &1 ⬝' K ⬝' &0

/-- The SKI term for list head with default. -/
def HeadD : SKI := HeadDPoly.toSKI

/-- Reduction: `HeadD ⬝ d ⬝ xs ↠ xs ⬝ K ⬝ d`. -/
theorem headD_def (d xs : SKI) : (HeadD ⬝ d ⬝ xs) ↠ xs ⬝ K ⬝ d :=
  HeadDPoly.toSKI_correct [d, xs] (by simp)

/-- General head-with-default correctness. -/
theorem headD_correct {d : ℕ} {cd : SKI} (hcd : IsChurch d cd)
    {ns : List ℕ} {cns : SKI} (hcns : IsChurchList ns cns) :
    IsChurch (ns.headD d) (HeadD ⬝ cd ⬝ cns) := by
  match ns with
  | [] =>
    simp only [List.headD_nil]
    apply isChurch_trans d (headD_def cd cns)
    apply isChurch_trans d (hcns K cd)
    exact hcd
  | x :: xs =>
    simp only [List.headD_cons]
    apply isChurch_trans x (headD_def cd cns)
    obtain ⟨cx, cxs, hcx, _, hred⟩ := hcns K cd
    exact isChurch_trans x hred (isChurch_trans x (MRed.K cx _) hcx)

/-- The SKI term for list head (default 0). -/
def Head : SKI := HeadD ⬝ SKI.Zero

/-- Reduction: `Head ⬝ xs ↠ xs ⬝ K ⬝ Zero`. -/
theorem head_def (xs : SKI) : (Head ⬝ xs) ↠ xs ⬝ K ⬝ SKI.Zero :=
  headD_def SKI.Zero xs

/-- Head correctness (default 0). -/
theorem head_correct (ns : List ℕ) (cns : SKI) (hcns : IsChurchList ns cns) :
    IsChurch (ns.headD 0) (Head ⬝ cns) :=
  headD_correct zero_correct hcns

/-! ### Tail: Extract the tail of a list -/

/-- Step function for tail: (prev, curr) → (curr, cons h curr) -/
def TailStepPoly : SKI.Polynomial 2 :=
  MkPair ⬝' (Snd ⬝' &1) ⬝' (Cons ⬝' &0 ⬝' (Snd ⬝' &1))

/-- The step function for computing list tail. -/
def TailStep : SKI := TailStepPoly.toSKI

/-- Reduction of the tail step function. -/
theorem tailStep_def (h p : SKI) :
    (TailStep ⬝ h ⬝ p) ↠ MkPair ⬝ (Snd ⬝ p) ⬝ (Cons ⬝ h ⬝ (Snd ⬝ p)) :=
  TailStepPoly.toSKI_correct [h, p] (by simp)

/-- tail xs = Fst (xs TailStep (MkPair Nil Nil)) -/
def TailPoly : SKI.Polynomial 1 :=
  Fst ⬝' (&0 ⬝' TailStep ⬝' (MkPair ⬝ Nil ⬝ Nil))

/-- The tail of a Church-encoded list. -/
def Tail : SKI := TailPoly.toSKI

/-- Reduction: `Tail ⬝ xs ↠ Fst ⬝ (xs ⬝ TailStep ⬝ (MkPair ⬝ Nil ⬝ Nil))`. -/
theorem tail_def (xs : SKI) :
    (Tail ⬝ xs) ↠ Fst ⬝ (xs ⬝ TailStep ⬝ (MkPair ⬝ Nil ⬝ Nil)) :=
  TailPoly.toSKI_correct [xs] (by simp)

/-- The initial pair (nil, nil) satisfies the invariant. -/
@[simp]
theorem tail_init : IsChurchListPair [] [] (MkPair ⬝ Nil ⬝ Nil) := by
  constructor
  · apply isChurchList_trans (fst_correct _ _); exact nil_correct
  · apply isChurchList_trans (snd_correct _ _); exact nil_correct

/-- The step function preserves the tail-computing invariant. -/
theorem tailStep_correct {x : ℕ} {xs : List ℕ} {cx p : SKI}
    (hcx : IsChurch x cx) (hp : IsChurchListPair xs.tail xs p) :
    IsChurchListPair xs (x :: xs) (TailStep ⬝ cx ⬝ p) := by
  apply isChurchListPair_trans (tailStep_def cx p)
  exact ⟨isChurchList_trans (fst_correct _ _) hp.2,
         isChurchList_trans (snd_correct _ _) (cons_correct hcx hp.2)⟩

theorem tailFold_correct (ns : List ℕ) (cns : SKI) (hcns : IsChurchList ns cns) :
    ∃ p, (cns ⬝ TailStep ⬝ (MkPair ⬝ Nil ⬝ Nil)) ↠ p ∧
         IsChurchListPair ns.tail ns p := by
  induction ns generalizing cns with
  | nil =>
    -- For empty list, the fold returns the initial pair
    use MkPair ⬝ Nil ⬝ Nil
    constructor
    · exact hcns TailStep (MkPair ⬝ Nil ⬝ Nil)
    · exact tail_init
  | cons x xs ih =>
    -- For x :: xs, first fold xs, then apply step
    -- cns ⬝ TailStep ⬝ init ↠ TailStep ⬝ cx ⬝ (cxs ⬝ TailStep ⬝ init)
    -- Get the Church representations for x and xs
    obtain ⟨cx, cxs, hcx, hcxs, hred⟩ := hcns TailStep (MkPair ⬝ Nil ⬝ Nil)
    -- By IH, folding xs gives a pair representing (xs.tail, xs)
    obtain ⟨p_xs, hp_xs_red, hp_xs_pair⟩ := ih cxs hcxs
    -- After step, we get a pair representing (xs, x :: xs)
    have hstep := tailStep_correct hcx hp_xs_pair
    -- The full fold: cns ⬝ TailStep ⬝ init ↠ TailStep ⬝ cx ⬝ (cxs ⬝ TailStep ⬝ init)
    --                                         ↠ TailStep ⬝ cx ⬝ p_xs
    use TailStep ⬝ cx ⬝ p_xs
    constructor
    · exact Trans.trans hred (MRed.tail _ hp_xs_red)
    · exact hstep

/-- Tail correctness. -/
theorem tail_correct (ns : List ℕ) (cns : SKI) (hcns : IsChurchList ns cns) :
    IsChurchList ns.tail (Tail ⬝ cns) := by
  -- Tail ⬝ cns ↠ Fst ⬝ (cns ⬝ TailStep ⬝ (MkPair ⬝ Nil ⬝ Nil))
  apply isChurchList_trans (tail_def cns)
  -- Get the fold result
  obtain ⟨p, hp_red, hp_pair⟩ := tailFold_correct ns cns hcns
  -- Fst ⬝ (cns ⬝ TailStep ⬝ init) ↠ Fst ⬝ p
  apply isChurchList_trans (MRed.tail Fst hp_red)
  -- Fst ⬝ p represents ns.tail (from hp_pair)
  exact hp_pair.1

/-! ### Prepending zero to a list (for Code.zero') -/

/-- PrependZero xs = cons 0 xs = Cons ⬝ Zero ⬝ xs -/
def PrependZeroPoly : SKI.Polynomial 1 := Cons ⬝' SKI.Zero ⬝' &0

/-- Prepend zero to a Church-encoded list. -/
def PrependZero : SKI := PrependZeroPoly.toSKI

/-- Reduction: `PrependZero ⬝ xs ↠ Cons ⬝ Zero ⬝ xs`. -/
theorem prependZero_def (xs : SKI) : (PrependZero ⬝ xs) ↠ Cons ⬝ SKI.Zero ⬝ xs :=
  PrependZeroPoly.toSKI_correct [xs] (by simp)

/-- Prepending zero preserves Church list representation. -/
theorem prependZero_correct {ns : List ℕ} {cns : SKI} (hcns : IsChurchList ns cns) :
    IsChurchList (0 :: ns) (PrependZero ⬝ cns) := by
  apply isChurchList_trans (prependZero_def cns)
  exact cons_correct zero_correct hcns

/-! ### Successor on list head (for Code.succ) -/

/-- SuccHead xs = cons (succ (head xs)) nil -/
def SuccHead : SKI := B ⬝ (C ⬝ Cons ⬝ Nil) ⬝ (B ⬝ SKI.Succ ⬝ Head)

/-- `SuccHead` correctly computes a singleton containing `succ(head ns)`. -/
theorem succHead_correct (ns : List ℕ) (cns : SKI) (hcns : IsChurchList ns cns) :
    IsChurchList [ns.headD 0 + 1] (SuccHead ⬝ cns) := by
  have hhead := head_correct ns cns hcns
  have hsucc := succ_correct (ns.headD 0) (Head ⬝ cns) hhead
  apply isChurchList_trans (.trans (B_tail_mred _ _ _ _ (B_def .Succ Head cns)) (C_def Cons Nil _))
  exact cons_correct hsucc nil_correct

end List

end SKI

end Cslib
