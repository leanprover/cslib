/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import Cslib.Foundations.Data.Part
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

/-- Helper for total functions: if `c.eval` is total with output `g n`, and `t` reduces
    to a Church numeral for `g n`, then `t` computes `c.eval`. -/
private theorem computes_of_total (t : SKI) (c : Code) (g : ℕ → ℕ)
    (heval : ∀ n, c.eval n = Part.some (g n))
    (hcorrect : ∀ n cn, IsChurch n cn → IsChurch (g n) (t ⬝ cn)) :
    Computes t c.eval := by
  intro n cn hcn m hm; rw [heval] at hm; obtain rfl := Part.some_injective hm
  exact hcorrect n cn hcn

/-- `Code.zero` computes the constant zero function. -/
theorem zero_computes : Computes (K ⬝ SKI.Zero) (Code.eval .zero) :=
  computes_of_total _ .zero (fun _ => 0)
    (fun n => by rw [show Code.zero = Code.const 0 from rfl, Code.eval_const])
    (fun _ _ _ => isChurch_trans 0 (MRed.K SKI.Zero _) zero_correct)

/-- `Code.succ` computes the successor function. -/
theorem succ_computes : Computes SKI.Succ (Code.eval .succ) :=
  computes_of_total _ .succ (· + 1)
    (fun _ => by simp only [Code.eval, PFun.coe_val])
    (fun n cn hcn => succ_correct n cn hcn)

/-- `Code.left` computes the left projection of `Nat.unpair`. -/
theorem left_computes : Computes NatUnpairLeft (Code.eval .left) :=
  computes_of_total _ .left (fun n => (Nat.unpair n).1)
    (fun _ => by simp only [Code.eval, PFun.coe_val])
    (fun n cn hcn => natUnpairLeft_correct n cn hcn)

/-- `Code.right` computes the right projection of `Nat.unpair`. -/
theorem right_computes : Computes NatUnpairRight (Code.eval .right) :=
  computes_of_total _ .right (fun n => (Nat.unpair n).2)
    (fun _ => by simp only [Code.eval, PFun.coe_val])
    (fun n cn hcn => natUnpairRight_correct n cn hcn)

/-- Composition of computable functions is computable. -/
theorem comp_computes {f g : ℕ →. ℕ} {tf tg : SKI}
    (hf : Computes tf f) (hg : Computes tg g) :
    Computes (B ⬝ tf ⬝ tg) (fun n => g n >>= f) := by
  intro n cn hcn m hm
  obtain ⟨intermediate, hint_eq, hm_eq⟩ := Part.eq_some_of_bind_eq_some hm
  exact isChurch_trans _ (B_def tf tg cn)
    (hf intermediate (tg ⬝ cn) (hg n cn hcn intermediate hint_eq) m hm_eq)

/-- Pairing of computable functions is computable. -/
theorem pair_computes {f g : ℕ →. ℕ} {tf tg : SKI}
    (hf : Computes tf f) (hg : Computes tg g) :
    Computes (S ⬝ (B ⬝ NatPair ⬝ tf) ⬝ tg)
      (fun n => Nat.pair <$> f n <*> g n) := by
  intro n cn hcn m hm
  simp only at hm
  obtain ⟨h, hh_mem, hm_in_h⟩ := Part.mem_bind_iff.mp (hm ▸ Part.mem_some m)
  obtain ⟨a, ha_mem, rfl⟩ := (Part.mem_map_iff _).mp hh_mem
  obtain ⟨b, hb_mem, rfl⟩ := (Part.mem_map_iff _).mp hm_in_h
  have hca := hf n cn hcn a (Part.eq_some_iff.mpr ha_mem)
  have hcb := hg n cn hcn b (Part.eq_some_iff.mpr hb_mem)
  exact isChurch_trans _ ((MRed.S _ _ _).trans (MRed.head _ (B_def _ _ _)))
    (natPair_correct a b _ _ hca hcb)

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
    obtain ⟨ih_val, hih_eq, hm_eq⟩ := Part.eq_some_of_bind_eq_some hm
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

/-- If `k ∈ Nat.rfind …`, then `f` evaluates to 0 at the root. -/
private theorem rfind_eval_root {f : Code} {a₀ m₀ k : ℕ}
    (hk : k ∈ Nat.rfind (fun n =>
      (fun m => decide (m = 0)) <$> f.eval (Nat.pair a₀ (n + m₀)))) :
    f.eval (Nat.pair a₀ (m₀ + k)) = Part.some 0 := by
  have hspec := Nat.rfind_spec hk
  obtain ⟨val, hval_mem, hval_eq⟩ := (Part.mem_map_iff _).mp hspec
  have : val = 0 := by simpa using hval_eq
  subst this; rw [Nat.add_comm] at hval_mem
  exact Part.eq_some_iff.mpr hval_mem

/-- If `k ∈ Nat.rfind …`, then `f` evaluates to a nonzero value below `k`. -/
private theorem rfind_eval_pos_below {f : Code} {a₀ m₀ k : ℕ}
    (hk : k ∈ Nat.rfind (fun n =>
      (fun m => decide (m = 0)) <$> f.eval (Nat.pair a₀ (n + m₀)))) :
    ∀ i < k, ∃ vi, vi ≠ 0 ∧ f.eval (Nat.pair a₀ (m₀ + i)) = Part.some vi := by
  intro i hi
  have hmin := Nat.rfind_min hk hi
  obtain ⟨val, hval_mem, hval_eq⟩ := (Part.mem_map_iff _).mp hmin
  have hval_ne : val ≠ 0 := by simpa using hval_eq
  rw [Nat.add_comm] at hval_mem
  exact ⟨val, hval_ne, Part.eq_some_iff.mpr hval_mem⟩

/-- Primitive recursion of computable functions is computable. -/
private theorem prec_computes {f g : Code} {tf tg : SKI}
    (ihf : Computes tf f.eval) (ihg : Computes tg g.eval) :
    Computes (PrecTrans tf tg) (f.prec g).eval := by
  intro n cn hcn m hm
  have hca := natUnpairLeft_correct n cn hcn
  have hcb := natUnpairRight_correct n cn hcn
  have hred := precTrans_def tf tg cn
  have hpair : n = Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 :=
    (Nat.pair_unpair n).symm
  rw [hpair] at hm
  exact isChurch_trans _ hred (prec_rec_correct f g _ _ ihf ihg
    (Nat.unpair n).1 (NatUnpairLeft ⬝ cn) hca
    (Nat.unpair n).2 m hm (NatUnpairRight ⬝ cn) hcb)

/-- Unbounded search of a computable function is computable. -/
private theorem rfind_computes {f : Code} {tf : SKI}
    (ihf : Computes tf f.eval) :
    Computes (RFindTrans tf) (Code.rfind' f).eval := by
  intro n cn hcn result hresult
  set a₀ := (Nat.unpair n).1
  set m₀ := (Nat.unpair n).2
  have hca := natUnpairLeft_correct n cn hcn
  have hcm₀ := natUnpairRight_correct n cn hcn
  -- Extract k from the rfind result
  have hresult' : result ∈ Code.eval (Code.rfind' f) n := by
    rw [hresult]; exact Part.mem_some _
  simp only [Code.eval, Nat.unpaired,
    show (Nat.unpair n).1 = a₀ from rfl,
    show (Nat.unpair n).2 = m₀ from rfl] at hresult'
  obtain ⟨k, hk_mem, hresult_eq⟩ := (Part.mem_map_iff _).mp hresult'
  subst hresult_eq
  -- Build the callback: the composed SKI term computes f on paired arguments
  set g := B ⬝ tf ⬝ (NatPair ⬝ (NatUnpairLeft ⬝ cn))
  have hg : ∀ i y, IsChurch i y → ∀ v, f.eval (Nat.pair a₀ i) = Part.some v →
      IsChurch v (g ⬝ y) := fun i y hy v hv =>
    isChurch_trans _ (B_def tf (NatPair ⬝ (NatUnpairLeft ⬝ cn)) y)
      (ihf _ _ (natPair_correct a₀ i (NatUnpairLeft ⬝ cn) y hca hy) v hv)
  -- Apply generalized RFindAbove_correct'
  have hind := RFindAbove_correct' g (NatUnpairRight ⬝ cn) k m₀ hcm₀
    (fun y hy => hg (m₀ + k) y hy 0 (rfind_eval_root hk_mem))
    (fun i hi y hy => by
      obtain ⟨vi, hvi_ne, hvi_eq⟩ := rfind_eval_pos_below hk_mem i hi
      exact ⟨vi - 1, by have : vi - 1 + 1 = vi := by omega
                        rw [this]; exact hg (m₀ + i) y hy vi hvi_eq⟩)
  rw [Nat.add_comm] at hind
  exact isChurch_trans _ (rfindTrans_def tf cn) hind

/-- Main correctness theorem: `codeToSKINat` correctly computes `Code.eval`. -/
theorem codeToSKINat_correct (c : Code) : Computes (codeToSKINat c) c.eval := by
  induction c with
  | zero => exact zero_computes
  | succ => exact succ_computes
  | left => exact left_computes
  | right => exact right_computes
  | pair f g ihf ihg =>
    simp only [codeToSKINat, Code.eval]; exact pair_computes ihf ihg
  | comp f g ihf ihg =>
    simp only [codeToSKINat, Code.eval]; exact comp_computes ihf ihg
  | prec f g ihf ihg =>
    simp only [codeToSKINat]; exact prec_computes ihf ihg
  | rfind' f ihf =>
    simp only [codeToSKINat]; exact rfind_computes ihf

/-! ### Main result -/

/-- Every partial recursive function on `ℕ` is SKI-computable. -/
theorem natPartrec_skiComputable (f : ℕ →. ℕ) (hf : Nat.Partrec f) :
    ∃ t : SKI, Computes t f := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  exact ⟨codeToSKINat c, hc ▸ codeToSKINat_correct c⟩

end SKI

end Cslib
