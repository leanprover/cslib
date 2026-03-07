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

Church-encoded lists for proving SKI ≃ TM equivalence. A list `[a₀, ... aₖ]` is encoded as
`λ c n. c xa₀ (c xa₁ (... (c xaₖ n)...))` where each `xaᵢ` represents `aᵢ`.
-/

namespace Cslib

namespace SKI

open Red MRed

variable {α β : Type*} [HasRealizer α SKI] [HasRealizer β SKI]

/-! ### Church List Representation -/

/-- A term correctly Church-encodes a list. -/
def RealizesList (cns : SKI) : List α → Prop
  | [] => ∀ c n : SKI, (cns ⬝ c ⬝ n) ↠ n
  | a :: as => ∀ c n : SKI,
      ∃ cx cxs : SKI, Realizes cx a ∧ RealizesList cxs as ∧
        (cns ⬝ c ⬝ n) ↠ c ⬝ cx ⬝ (cxs ⬝ c ⬝ n)

instance instEncodedList : HasRealizer (List α) SKI where
  Realizes := RealizesList

instance instHasRealizerLiftList [HasRealizerLift α Red] : HasRealizerLift (List α) Red where
  realizes_left_of_red := by
    intro as cns cns' has h
    induction as generalizing cns cns' with
    | nil =>
      intro c n
      refine Relation.ReflTransGen.head ?_ (has c n)
      exact red_head _ _ _ <| red_head _ _ _ h
    | cons a as ih =>
      intro c n
      obtain ⟨cx', cxs', hcx, hcxs, hred⟩ := has c n
      use cx', cxs', hcx, hcxs
      refine Relation.ReflTransGen.head ?_ hred
      exact red_head _ _ _ <| red_head _ _ _ h

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
theorem realizes_nil : Nil ⊩ ([] : List α) := nil_def

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
theorem realizes_cons : Cons ⊩ (List.cons : α → List α → List α) := by
  intro c cx hx xs cxs hxs c n
  use cx, cxs, hx, hxs
  exact cons_def cx cxs c n

/-- Singleton list correctness. -/
theorem realizes_singleton {x : α} {cx : SKI} (hcx : cx ⊩ x) :
    (Cons ⬝ cx ⬝ Nil) ⊩ [x] :=
  realizes_cons hcx realizes_nil

/-! ### Basic recursion on lists -/

def FoldR := RotR

lemma realizes_list_foldr {α β : Type*} [HasRealizer α SKI] [HasRealizerLift β Red] :
    FoldR ⊩ (List.foldr : (α → β → β) → β → List α → β) := by
  intro f xf hf b xb hb l xl hl
  suffices (xl ⬝ xf ⬝ xb) ⊩ (l.foldr f b) by apply this.left_of_mRed <| rotR_def ..
  induction l generalizing xl with
  | nil => exact hb.left_of_mRed <| hl ..
  | cons a l ih =>
    obtain ⟨xa, xl', ha, hl', hred⟩ := hl xf xb
    have : Realizes (xf ⬝ xa ⬝ (xl' ⬝ xf ⬝ xb)) (f a (List.foldr f b l)) :=
      hf ha (ih hl')
    exact this.left_of_mRed hred

def recPairStep (f : α → List α → β → β) : α → (β × List α) → (β × List α)
  | a, ⟨y, as⟩ => ⟨f a as y, a :: as⟩

lemma recPairStep_foldr {α' β' : Type*} (b : β') (f : α' → List α' → β' → β') (as : List α') :
    List.foldr (β := β' × List α') (List.recPairStep f) ⟨b, []⟩ as = ⟨List.rec b f as, as⟩ := by
  induction as <;> simp_all [recPairStep]

def listRecAuxPoly : SKI.Polynomial 3 :=
  SKI.MkPair ⬝' (&0 ⬝' &1 ⬝' (Snd ⬝' &2) ⬝' (Fst ⬝' &2)) ⬝' (Cons ⬝' &1 ⬝' (Snd ⬝' &2))
def listRecAux : SKI := listRecAuxPoly.toSKI
lemma listRecAux_def (xf xa xp : SKI) :
    (listRecAux ⬝ xf ⬝ xa ⬝ xp) ↠
      SKI.MkPair ⬝ (xf ⬝ xa ⬝ (Snd ⬝ xp) ⬝ (Fst ⬝ xp)) ⬝ (Cons ⬝ xa ⬝ (Snd ⬝ xp)) :=
  listRecAuxPoly.toSKI_correct [xf, xa, xp] (by simp)

lemma realizes_listRecAux {α β : Type*} [HasRealizerLift α Red] [HasRealizerLift β Red]
    {f : α → List α → β → β} {xf : SKI} (hf : xf ⊩ f) :
    (listRecAux ⬝ xf) ⊩ (List.recPairStep f) := by
  intro a xa ha p xp hp
  refine Realizes.left_of_mRed (α := β × List α) ?_ (listRecAux_def xf xa xp)
  apply realizes_mkPair
  · exact hf ha hp.2 hp.1
  · exact realizes_cons ha hp.2

lemma realizes_recPairStep_foldr {α β : Type*} [HasRealizerLift α Red] [HasRealizerLift β Red]
    {b : β} {xb : SKI} (hb : xb ⊩ b)
    {f : α → List α → β → β} {xf : SKI} (hf : xf ⊩ f) {as : List α} {xas : SKI} (has : xas ⊩ as) :
    (SKI.RotR ⬝ (listRecAux ⬝ xf) ⬝ (MkPair ⬝ xb ⬝ Nil) ⬝ xas) ⊩
      (⟨List.rec b f as, as⟩ : β × List α) := by
  rw [←List.recPairStep_foldr]
  refine realizes_list_foldr (realizes_listRecAux hf) ?_ has
  exact realizes_mkPair hb realizes_nil

def listRecPoly : SKI.Polynomial 3 :=
  Fst ⬝' (SKI.RotR ⬝' (listRecAux ⬝' &1) ⬝' (MkPair ⬝' &0 ⬝' Nil) ⬝' &2)
def listRec := listRecPoly.toSKI
lemma listRec_def (xb xf xas : SKI) :
    (listRec ⬝ xb ⬝ xf ⬝ xas) ↠ Fst ⬝ (SKI.RotR ⬝ (listRecAux ⬝ xf) ⬝ (MkPair ⬝ xb ⬝ Nil) ⬝ xas) :=
  listRecPoly.toSKI_correct [xb, xf, xas] (by simp)

theorem realizes_list_rec {α β : Type*} [HasRealizerLift α Red] [HasRealizerLift β Red] :
    listRec ⊩ (List.rec : β → (α → List α → β → β) → List α → β) := by
  intro b xb hb f xf hf as xas has
  have := realizes_recPairStep_foldr hb hf has
  exact this.1.left_of_mRed <| listRec_def ..

def Tail := (listRec ⬝ Nil ⬝ (&1 : SKI.Polynomial 3).toSKI)

lemma realizes_tail {α β : Type*} [HasRealizerLift α Red] [HasRealizerLift β Red] :
    Tail ⊩ (List.tail : List α → List α) := by
  intro as xas has
  have : (as.tail = as.rec [] (fun _ t _ => t)) := by cases as <;> rfl
  rw [this]
  refine realizes_list_rec realizes_nil ?_ has
  intro _ xs _ t xt ht _ xu _
  apply ht.left_of_mRed <| (&1 : SKI.Polynomial 3).toSKI_correct [xs, xt, xu] (by simp)

/-! ### Head: Extract the head of a list -/

/-- headD d xs = xs K d (returns d for empty list) -/
def HeadDPoly : SKI.Polynomial 2 := &1 ⬝' K ⬝' &0

/-- The SKI term for list head with default. -/
def HeadD : SKI := HeadDPoly.toSKI

/-- Reduction: `HeadD ⬝ d ⬝ xs ↠ xs ⬝ K ⬝ d`. -/
theorem headD_def (d xs : SKI) : (HeadD ⬝ d ⬝ xs) ↠ xs ⬝ K ⬝ d :=
  HeadDPoly.toSKI_correct [d, xs] (by simp)

/-- General head-with-default correctness. -/
theorem realizes_headD {α : Type*} [HasRealizerLift α Red] :
    HeadD ⊩ (fun a (as : List α) => as.headD a) := by
  intro a xa ha as xas has
  match as with
  | [] =>
    simp only [List.headD_nil]
    refine Realizes.left_of_mRed ?_ (headD_def xa xas)
    apply ha.left_of_mRed
    exact has K xa
  | x :: xs =>
    simp only [List.headD_cons]
    refine Realizes.left_of_mRed ?_ (headD_def xa xas)
    obtain ⟨cx, cxs, hcx, _, hred⟩ := has K xa
    apply hcx.left_of_mRed
    exact hred.trans <| MRed.K ..

/-- The SKI term for list head (default 0). -/
def Head : SKI := HeadD ⬝ SKI.Zero

/-- Reduction: `Head ⬝ xs ↠ xs ⬝ K ⬝ Zero`. -/
theorem head_def (xs : SKI) : (Head ⬝ xs) ↠ xs ⬝ K ⬝ SKI.Zero :=
  headD_def SKI.Zero xs

/-- Head correctness (default 0). -/
theorem realizes_head : Head ⊩ (fun (xs : List Nat) => xs.headD 0) := by
  intro ns xns hns
  exact realizes_headD realizes_zero hns

/-! ### Prepending zero to a list (for Code.zero') -/

/-- PrependZero xs = cons 0 xs = Cons ⬝ Zero ⬝ xs -/
def PrependZeroPoly : SKI.Polynomial 1 := Cons ⬝' SKI.Zero ⬝' &0

/-- Prepend zero to a Church-encoded list. -/
def PrependZero : SKI := PrependZeroPoly.toSKI

/-- Reduction: `PrependZero ⬝ xs ↠ Cons ⬝ Zero ⬝ xs`. -/
theorem prependZero_def (xs : SKI) : (PrependZero ⬝ xs) ↠ Cons ⬝ SKI.Zero ⬝ xs :=
  PrependZeroPoly.toSKI_correct [xs] (by simp)

/-- Prepending zero preserves Church list representation. -/
theorem realizes_prependZero : PrependZero ⊩ (fun ns => 0 :: ns) := by
  intro ns cns hns
  refine Realizes.left_of_mRed ?_ (prependZero_def cns)
  exact realizes_cons realizes_zero hns

/-! ### Successor on list head (for Code.succ) -/

/-- SuccHead xs = cons (succ (head xs)) nil -/
def SuccHead : SKI := B ⬝ (C ⬝ Cons ⬝ Nil) ⬝ (B ⬝ SKI.Succ ⬝ Head)

/-- `SuccHead` correctly computes a singleton containing `succ(head ns)`. -/
theorem realizes_prependSucc : SuccHead ⊩ (fun (ns : List Nat) => [ns.headD 0 + 1]) := by
  intro ns cns hcns
  have hhead := realizes_head hcns
  have hsucc := realizes_succ hhead
  refine Realizes.left_of_mRed ?_
    (.trans (B_tail_mred _ _ _ _ (B_def .Succ Head cns)) (C_def Cons Nil _))
  exact realizes_cons hsucc realizes_nil

end List

end SKI

end Cslib
