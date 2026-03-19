/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Languages.CombinatoryLogic.Recursion
public import Mathlib.Computability.PartrecCode

@[expose] public section

/-!
# Partial Recursive → SKI-computable (Nat.Partrec)

This file defines a notion of computability for SKI terms on natural numbers
(using Church numerals) and translates `Nat.Partrec.Code` to SKI terms.

## Main definitions

- `Computes t f`: SKI term `t` computes a partial function `f : ℕ →. ℕ` on Church numerals.
- `codeToSKINat`: translates `Nat.Partrec.Code` constructors to SKI terms.

## Main results

- `codeToSKINat_correct`: each translated code computes the corresponding `Code.eval`.
- `natPartrec_skiComputable`: every `Nat.Partrec` function is SKI-computable.

-/

namespace Cslib

namespace SKI

open Red MRed
open Nat.Partrec

/-! ### Computability predicate for functions on ℕ -/

/-- An SKI term `t` computes a partial function `f : ℕ →. ℕ` if,
for every Church numeral input, `t` applied to the input is a Church numeral
for the output whenever `f` is defined. -/
def Computes (t : SKI) (f : ℕ →. ℕ) : Prop :=
  ∀ n : ℕ, ∀ cn : SKI, IsChurch n cn →
    ∀ m : ℕ, f n = Part.some m →
      IsChurch m (t ⬝ cn)

/-! ### Helper terms for `Code.prec` and `Code.rfind'` -/

/-- Step function for primitive recursion:
    `λ a cn prev. tg ⬝ (NatPair ⬝ a ⬝ (NatPair ⬝ (Pred ⬝ cn) ⬝ prev))`
    Variables: &0 = a, &1 = cn, &2 = prev -/
def PrecStepPoly (tg : SKI) : SKI.Polynomial 3 :=
  tg ⬝' (NatPair ⬝' &0 ⬝' (NatPair ⬝' (Pred ⬝' &1) ⬝' &2))

/-- SKI term for the primitive recursion step function. -/
def PrecStep (tg : SKI) : SKI := (PrecStepPoly tg).toSKI

theorem precStep_def (tg a cn prev : SKI) :
    (PrecStep tg ⬝ a ⬝ cn ⬝ prev) ↠
      tg ⬝ (NatPair ⬝ a ⬝ (NatPair ⬝ (Pred ⬝ cn) ⬝ prev)) :=
  (PrecStepPoly tg).toSKI_correct [a, cn, prev] (by simp)

/-- Full primitive recursion translation:
    `λ n. Rec (tf (left n)) (PrecStep tg (left n)) (right n)` -/
def PrecTransPoly (tf tg : SKI) : SKI.Polynomial 1 :=
  Rec ⬝' (tf ⬝' (NatUnpairLeft ⬝' &0))
      ⬝' (PrecStep tg ⬝' (NatUnpairLeft ⬝' &0))
      ⬝' (NatUnpairRight ⬝' &0)

/-- SKI term for primitive recursion via `Rec` with pair/unpair plumbing. -/
def PrecTrans (tf tg : SKI) : SKI := (PrecTransPoly tf tg).toSKI

theorem precTrans_def (tf tg cn : SKI) :
    (PrecTrans tf tg ⬝ cn) ↠
      Rec ⬝ (tf ⬝ (NatUnpairLeft ⬝ cn))
          ⬝ (PrecStep tg ⬝ (NatUnpairLeft ⬝ cn))
          ⬝ (NatUnpairRight ⬝ cn) :=
  (PrecTransPoly tf tg).toSKI_correct [cn] (by simp)

/-- Unbounded search translation:
    `λ n. RFindAbove ⬝ (NatUnpairRight ⬝ n) ⬝ (B ⬝ tf ⬝ (NatPair ⬝ (NatUnpairLeft ⬝ n)))` -/
def RFindTransPoly (tf : SKI) : SKI.Polynomial 1 :=
  RFindAbove ⬝' (NatUnpairRight ⬝' &0)
             ⬝' (B ⬝' tf ⬝' (NatPair ⬝' (NatUnpairLeft ⬝' &0)))

/-- SKI term for unbounded search (μ-recursion). -/
def RFindTrans (tf : SKI) : SKI := (RFindTransPoly tf).toSKI

theorem rfindTrans_def (tf cn : SKI) :
    (RFindTrans tf ⬝ cn) ↠
      RFindAbove ⬝ (NatUnpairRight ⬝ cn)
                 ⬝ (B ⬝ tf ⬝ (NatPair ⬝ (NatUnpairLeft ⬝ cn))) :=
  (RFindTransPoly tf).toSKI_correct [cn] (by simp)

/-! ### Translation from Nat.Partrec.Code to SKI -/

/-- Translate `Nat.Partrec.Code` to SKI terms operating on Church numerals. -/
def codeToSKINat : Code → SKI
  | .zero => K ⬝ SKI.Zero
  | .succ => SKI.Succ
  | .left => NatUnpairLeft
  | .right => NatUnpairRight
  | .pair f g =>
    let tf := codeToSKINat f
    let tg := codeToSKINat g
    S ⬝ (B ⬝ NatPair ⬝ tf) ⬝ tg
  | .comp f g =>
    B ⬝ (codeToSKINat f) ⬝ (codeToSKINat g)
  | .prec f g =>
    PrecTrans (codeToSKINat f) (codeToSKINat g)
  | .rfind' f =>
    RFindTrans (codeToSKINat f)

/-! ### Correctness proofs -/

/-- `Code.zero` computes the constant zero function. -/
theorem zero_computes : Computes (K ⬝ SKI.Zero) (Code.eval .zero) := by
  intro n cn hcn m hm
  have h0 : Code.eval .zero n = Part.some 0 := by
    rw [show Code.zero = Code.const 0 from rfl, Code.eval_const]
  rw [h0] at hm; obtain rfl := Part.some_injective hm
  exact isChurch_trans 0 (MRed.K SKI.Zero cn) zero_correct

/-- `Code.succ` computes the successor function. -/
theorem succ_computes : Computes SKI.Succ (Code.eval .succ) := by
  intro n cn hcn m hm
  have h0 : Code.eval .succ n = Part.some (n + 1) := by
    simp only [Code.eval, PFun.coe_val]
  rw [h0] at hm; obtain rfl := Part.some_injective hm
  exact succ_correct n cn hcn

/-- `Code.left` computes the left projection of `Nat.unpair`. -/
theorem left_computes : Computes NatUnpairLeft (Code.eval .left) := by
  intro n cn hcn m hm
  have h0 : Code.eval .left n = Part.some (Nat.unpair n).1 := by
    simp only [Code.eval, PFun.coe_val]
  rw [h0] at hm; obtain rfl := Part.some_injective hm
  exact natUnpairLeft_correct n cn hcn

/-- `Code.right` computes the right projection of `Nat.unpair`. -/
theorem right_computes : Computes NatUnpairRight (Code.eval .right) := by
  intro n cn hcn m hm
  have h0 : Code.eval .right n = Part.some (Nat.unpair n).2 := by
    simp only [Code.eval, PFun.coe_val]
  rw [h0] at hm; obtain rfl := Part.some_injective hm
  exact natUnpairRight_correct n cn hcn

/-- Composition of computable functions is computable. -/
theorem comp_computes {f g : ℕ →. ℕ} {tf tg : SKI}
    (hf : Computes tf f) (hg : Computes tg g) :
    Computes (B ⬝ tf ⬝ tg) (fun n => g n >>= f) := by
  intro n cn hcn m hm
  simp only at hm
  have hm' : m ∈ (g n >>= f) := by rw [hm]; exact Part.mem_some m
  obtain ⟨intermediate, hint_mem, hm_mem⟩ := Part.mem_bind_iff.mp hm'
  have hgn : g n = Part.some intermediate := Part.eq_some_iff.mpr hint_mem
  have hfint : f intermediate = Part.some m := Part.eq_some_iff.mpr hm_mem
  have hcint := hg n cn hcn intermediate hgn
  have hcm := hf intermediate (tg ⬝ cn) hcint m hfint
  exact isChurch_trans _ (B_def tf tg cn) hcm

/-- Pairing of computable functions is computable. -/
theorem pair_computes {f g : ℕ →. ℕ} {tf tg : SKI}
    (hf : Computes tf f) (hg : Computes tg g) :
    Computes (S ⬝ (B ⬝ NatPair ⬝ tf) ⬝ tg)
      (fun n => Nat.pair <$> f n <*> g n) := by
  intro n cn hcn m hm
  simp only at hm
  -- hm : Nat.pair <$> f n <*> g n = Part.some m
  have hm' : m ∈ (Nat.pair <$> f n <*> g n) := by rw [hm]; exact Part.mem_some m
  -- Unfold <*> into bind: pf <*> pa = pf >>= fun h => h <$> pa
  have hm_bind : m ∈ Part.bind (Part.map Nat.pair (f n)) (fun h => Part.map h (g n)) := hm'
  obtain ⟨h, hh_mem, hm_in_h⟩ := Part.mem_bind_iff.mp hm_bind
  obtain ⟨a, ha_mem, hh_eq⟩ := (Part.mem_map_iff _).mp hh_mem
  subst hh_eq
  obtain ⟨b, hb_mem, hm_eq⟩ := (Part.mem_map_iff _).mp hm_in_h
  have hfn : f n = Part.some a := Part.eq_some_iff.mpr ha_mem
  have hgn : g n = Part.some b := Part.eq_some_iff.mpr hb_mem
  have hca := hf n cn hcn a hfn
  have hcb := hg n cn hcn b hgn
  subst hm_eq
  have hred : (S ⬝ (B ⬝ NatPair ⬝ tf) ⬝ tg ⬝ cn) ↠
      (NatPair ⬝ (tf ⬝ cn) ⬝ (tg ⬝ cn)) := calc
    _ ↠ (B ⬝ NatPair ⬝ tf) ⬝ cn ⬝ (tg ⬝ cn) := MRed.S _ _ _
    _ ↠ NatPair ⬝ (tf ⬝ cn) ⬝ (tg ⬝ cn) := MRed.head _ (B_def _ _ _)
  exact isChurch_trans _ hred (natPair_correct a b _ _ hca hcb)

/-- Helper: `Rec` correctly implements primitive recursion from `Code.prec`. -/
private theorem prec_rec_correct (f g : Code) (tf tg : SKI)
    (ihf : Computes tf f.eval) (ihg : Computes tg g.eval)
    (a₀ : ℕ) (ca : SKI) (hca : IsChurch a₀ ca) :
    ∀ b₀ : ℕ, ∀ m : ℕ,
    Code.eval (f.prec g) (Nat.pair a₀ b₀) = Part.some m →
    ∀ cb : SKI, IsChurch b₀ cb →
    IsChurch m (Rec ⬝ (tf ⬝ ca) ⬝ (PrecStep tg ⬝ ca) ⬝ cb) := by
  intro b₀
  induction b₀ with
  | zero =>
    intro m hm cb hcb
    rw [Code.eval_prec_zero] at hm
    exact isChurch_trans _ (rec_zero _ _ cb hcb) (ihf a₀ ca hca m hm)
  | succ k ih =>
    intro m hm cb hcb
    rw [Code.eval_prec_succ] at hm
    -- Extract the intermediate value from the bind
    have hm' : m ∈ (Code.eval (f.prec g) (Nat.pair a₀ k) >>=
      fun i => g.eval (Nat.pair a₀ (Nat.pair k i))) := by
      rw [hm]; exact Part.mem_some m
    obtain ⟨ih_val, hih_mem, hm_mem⟩ := Part.mem_bind_iff.mp hm'
    have hih_eq := Part.eq_some_iff.mpr hih_mem
    have hm_eq := Part.eq_some_iff.mpr hm_mem
    -- By IH, Rec computes the intermediate value on Pred ⬝ cb
    have hpred : IsChurch k (Pred ⬝ cb) := pred_correct (k + 1) cb hcb
    set step := PrecStep tg ⬝ ca
    set base := tf ⬝ ca
    have hcih := ih ih_val hih_eq (Pred ⬝ cb) hpred
    -- Build Church numeral for the argument to g
    have hpair_inner := natPair_correct k ih_val (Pred ⬝ cb)
      (Rec ⬝ base ⬝ step ⬝ (Pred ⬝ cb)) hpred hcih
    have hpair_full := natPair_correct a₀ (Nat.pair k ih_val) ca
      (NatPair ⬝ (Pred ⬝ cb) ⬝ (Rec ⬝ base ⬝ step ⬝ (Pred ⬝ cb))) hca hpair_inner
    -- By ihg, tg computes the result
    have hcm := ihg _ _ hpair_full m hm_eq
    -- Chain the reductions
    have hred := (rec_succ k base step cb hcb).trans
      (precStep_def tg ca cb (Rec ⬝ base ⬝ step ⬝ (Pred ⬝ cb)))
    exact isChurch_trans _ hred hcm

/-- Extract eval facts from `Nat.rfind` membership. -/
private theorem rfind_eval_facts {f : Code} {a₀ m₀ k : ℕ}
    (hk : k ∈ Nat.rfind (fun n =>
      (fun m => decide (m = 0)) <$> f.eval (Nat.pair a₀ (n + m₀)))) :
    f.eval (Nat.pair a₀ (m₀ + k)) = Part.some 0 ∧
    ∀ i < k, ∃ vi, vi ≠ 0 ∧ f.eval (Nat.pair a₀ (m₀ + i)) = Part.some vi := by
  constructor
  · have hspec := Nat.rfind_spec hk
    obtain ⟨val, hval_mem, hval_eq⟩ := (Part.mem_map_iff _).mp hspec
    have : val = 0 := by simpa using hval_eq
    subst this; rw [Nat.add_comm] at hval_mem
    exact Part.eq_some_iff.mpr hval_mem
  · intro i hi
    have hmin := Nat.rfind_min hk hi
    obtain ⟨val, hval_mem, hval_eq⟩ := (Part.mem_map_iff _).mp hmin
    have hval_ne : val ≠ 0 := by simpa using hval_eq
    rw [Nat.add_comm] at hval_mem
    exact ⟨val, hval_ne, Part.eq_some_iff.mpr hval_mem⟩

/-- Helper: `RFindAbove` correctly implements `Code.rfind'` by induction on
    the number of steps until the root. -/
private theorem rfindAbove_induction (f : Code) (tf : SKI)
    (ihf : Computes tf f.eval) (a₀ : ℕ) (ca : SKI) (hca : IsChurch a₀ ca)
    (g : SKI) (hg : g = B ⬝ tf ⬝ (NatPair ⬝ ca)) :
    ∀ n m : ℕ, ∀ x : SKI, IsChurch m x →
    f.eval (Nat.pair a₀ (m + n)) = Part.some 0 →
    (∀ i < n, ∃ vi, vi ≠ 0 ∧
      f.eval (Nat.pair a₀ (m + i)) = Part.some vi) →
    IsChurch (m + n) (RFindAbove ⬝ x ⬝ g) := by
  intro n
  induction n with
  | zero =>
    intro m x hx hroot _
    simp only [Nat.add_zero] at hroot ⊢
    apply isChurch_trans (a' := RFindAboveAux ⬝ RFindAbove ⬝ x ⬝ g)
    · apply MRed.head; apply MRed.head; exact fixedPoint_correct _
    apply isChurch_trans (a' := x)
    · apply rfindAboveAux_base
      -- Need: IsChurch 0 (g ⬝ x)
      subst hg
      apply isChurch_trans _ (B_def tf (NatPair ⬝ ca) x)
      have hpair := natPair_correct a₀ m ca x hca hx
      exact ihf _ _ hpair 0 hroot
    · exact hx
  | succ n ih =>
    intro m x hx hroot hbelow
    apply isChurch_trans (a' := RFindAboveAux ⬝ RFindAbove ⬝ x ⬝ g)
    · apply MRed.head; apply MRed.head; exact fixedPoint_correct _
    -- f at m is nonzero, so step
    obtain ⟨v₀, hv₀_ne, hv₀_eval⟩ := hbelow 0 (by omega)
    simp only [Nat.add_zero] at hv₀_eval
    apply isChurch_trans (a' := RFindAbove ⬝ (SKI.Succ ⬝ x) ⬝ g)
    · apply rfindAboveAux_step (m := v₀ - 1)
      subst hg
      apply isChurch_trans _ (B_def tf (NatPair ⬝ ca) x)
      have hpair := natPair_correct a₀ m ca x hca hx
      have hv₀_pos : v₀ - 1 + 1 = v₀ := Nat.succ_pred_eq_of_ne_zero hv₀_ne
      rw [hv₀_pos]
      exact ihf _ _ hpair v₀ hv₀_eval
    · have h := ih (m + 1) (SKI.Succ ⬝ x) (succ_correct m x hx)
        (by rw [show m + 1 + n = m + (n + 1) from by omega]; exact hroot)
        (by
          intro i hi
          obtain ⟨vi, hvi_ne, hvi_eval⟩ := hbelow (i + 1) (by omega)
          exact ⟨vi, hvi_ne, by
            rw [show m + 1 + i = m + (i + 1) from by omega]; exact hvi_eval⟩)
      rw [show m + (n + 1) = m + 1 + n from by omega]
      exact h

/-- Main correctness theorem: `codeToSKINat` correctly computes `Code.eval`. -/
theorem codeToSKINat_correct (c : Code) : Computes (codeToSKINat c) c.eval := by
  induction c with
  | zero => exact zero_computes
  | succ => exact succ_computes
  | left => exact left_computes
  | right => exact right_computes
  | pair f g ihf ihg =>
    simp only [codeToSKINat, Code.eval]
    exact pair_computes ihf ihg
  | comp f g ihf ihg =>
    simp only [codeToSKINat, Code.eval]
    exact comp_computes ihf ihg
  | prec f g ihf ihg =>
    simp only [codeToSKINat]
    intro n cn hcn m hm
    have hca := natUnpairLeft_correct n cn hcn
    have hcb := natUnpairRight_correct n cn hcn
    have hred := precTrans_def (codeToSKINat f) (codeToSKINat g) cn
    -- Rewrite eval in terms of unpair components
    have hpair : n = Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 :=
      (Nat.pair_unpair n).symm
    rw [hpair] at hm
    exact isChurch_trans _ hred (prec_rec_correct f g _ _ ihf ihg
      (Nat.unpair n).1 (NatUnpairLeft ⬝ cn) hca
      (Nat.unpair n).2 m hm (NatUnpairRight ⬝ cn) hcb)
  | rfind' f ihf =>
    simp only [codeToSKINat]
    intro n cn hcn result hresult
    set tf := codeToSKINat f
    set a₀ := (Nat.unpair n).1
    set m₀ := (Nat.unpair n).2
    have hca := natUnpairLeft_correct n cn hcn
    have hcm₀ := natUnpairRight_correct n cn hcn
    have hred := rfindTrans_def tf cn
    -- Extract k from the rfind result
    have hresult' : result ∈ Code.eval (Code.rfind' f) n := by
      rw [hresult]; exact Part.mem_some _
    simp only [Code.eval, Nat.unpaired,
      show (Nat.unpair n).1 = a₀ from rfl,
      show (Nat.unpair n).2 = m₀ from rfl] at hresult'
    obtain ⟨k, hk_mem, hresult_eq⟩ := (Part.mem_map_iff _).mp hresult'
    subst hresult_eq
    obtain ⟨heval_root, heval_below⟩ := rfind_eval_facts hk_mem
    set g := B ⬝ tf ⬝ (NatPair ⬝ (NatUnpairLeft ⬝ cn))
    have hind := rfindAbove_induction f tf ihf a₀
      (NatUnpairLeft ⬝ cn) hca g rfl k m₀
      (NatUnpairRight ⬝ cn) hcm₀ heval_root heval_below
    rw [Nat.add_comm] at hind
    exact isChurch_trans _ hred hind

/-! ### Main result -/

/-- Every partial recursive function on `ℕ` is SKI-computable. -/
theorem natPartrec_skiComputable (f : ℕ →. ℕ) (hf : Nat.Partrec f) :
    ∃ t : SKI, Computes t f := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  exact ⟨codeToSKINat c, hc ▸ codeToSKINat_correct c⟩

end SKI

end Cslib
