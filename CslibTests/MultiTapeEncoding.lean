/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id
import Cslib.Computability.Machines.Turing.MultiTape.Encodings.List
import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Nat
import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Prod
import Cslib.Computability.Machines.Turing.MultiTape.Encodings.Sum

namespace CslibTests.MultiTapeEncoding

open Turing.MultiTapeTM Cslib.Encoding

/-! ### One-way machines -/

-- The output and running time of a one-way machine are functions on words.
example : oneWayOutput (fun (_ : Unit) b => ([b, b], ())) (fun _ => [false]) () [true, false] =
    [true, true, false, false, false] := rfl
example : oneWayTime (fun (_ : Unit) b => ([b, b], ())) (fun _ => [false]) () [true, false] = 5 :=
  rfl
-- Emitting nothing still takes one step per input symbol.
example : oneWayTime (fun (_ : Unit) (_ : Bool) => ([], ())) (fun _ => []) () [true, false] = 3 :=
  rfl
-- The time is linear in the input and the output.
example : oneWayTime (fun (_ : Unit) b => ([b, b], ())) (fun _ => [false]) () [true, false] ≤
    2 + 5 + 1 := oneWayTime_le ..

/-! ### Extending the library -/

-- A function not covered by the library is shown to be computable by giving a function on words
-- that realizes it. Here: doubling a natural number, which prepends a `false` bit to the code of
-- every number but zero.
example : ComputableInTimeAndSpace (2 * ·) encNat encNat (fun n => 2 * (encNat n).length + 3)
    (fun _ => 0) :=
  ((computableInTimeAndSpace_headCases [] (fun b => [false, b]) fun _ => true).of_realizes
    fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rfl
      · rw [encNat_two_mul (by lia)]
        cases h : encNat n with
        | nil => simp_all
        | cons b w => simp).mono (fun _ => by simp) fun _ => le_rfl

-- A machine given directly as a transducer: the bitwise complement.
example : ComputableInTimeAndSpace (List.map not) encBits encBits (fun w => 2 * w.length + 1)
    (fun _ => 0) :=
  (computableInTimeAndSpace_of_oneWayOutput_eq () (fun _ b => ([!b], ())) (fun _ => [])
    fun w => by induction w <;> simp [*]).mono (fun _ => by simp; lia) fun _ => le_rfl

/-! ### Functions on words -/

example : headCases [] (fun b => [!b]) (fun _ => true) [true, false] = [false, false] := rfl
example : headCases [true] (fun b => [!b]) (fun _ => true) [] = [true] := rfl

example : ComputableInTimeAndSpace (undelimitOr [true]) encBits encBits
    (fun w => 2 * w.length + 2) (fun _ => 0) := computableInTimeAndSpace_undelimitOr [true]

/-! ### Pairs -/

-- Bounds in terms of the components.
example : ComputableInTimeAndSpace (Prod.fst : ℕ × List Bool → ℕ) (encProd encNat encBits) encNat
    (fun p => 4 * (encNat p.1).length + 2 * p.2.length + 3) (fun _ => 0) :=
  computableInTimeAndSpace_prod_fst.mono (fun p => by simp; lia) fun _ => le_rfl

example : ComputableInTimeAndSpace (Prod.snd : ℕ × List Bool → List Bool) (encProd encNat encBits)
    encBits (fun p => 4 * (encNat p.1).length + 2 * p.2.length + 3) (fun _ => 0) :=
  computableInTimeAndSpace_prod_snd.mono (fun p => by simp; lia) fun _ => le_rfl

example : ComputableInTimeAndSpace (Sigma.fst : (n : ℕ) × Fin n → ℕ)
    (encSigma encNat fun n => encFin n) encNat
    (fun x => 4 * (encNat x.1).length + 2 * Nat.clog 2 x.1 + 3) (fun _ => 0) :=
  computableInTimeAndSpace_sigma_fst.mono (fun x => by simp; lia) fun _ => le_rfl

-- Pairs are formed from machines that compute the components from the same input: here the
-- successor and the parity of a number.
example : ComputableInTimeAndSpace (fun n : ℕ => (n + 1, n.bodd)) encNat (encProd encNat encBool)
    (fun n => 10 * (encNat n).length + 14) (fun _ => 0) :=
  (computableInTimeAndSpace_nat_succ.prod_mk computableInTimeAndSpace_nat_bodd).mono
    (fun _ => by lia) fun _ => by lia

-- Accessors and constructors compose across types.
example : ComputableInTimeAndSpace (fun x : ℕ ⊕ Bool => (x.isLeft, x.swap)) (encSum encNat encBool)
    (encProd encBool (encSum encBool encNat))
    (fun x => 10 * (encSum encNat encBool x).length + 14) (fun _ => 0) :=
  (computableInTimeAndSpace_sum_isLeft.prod_mk computableInTimeAndSpace_sum_swap).mono
    (fun _ => by lia) fun _ => by lia

/-! ### Sums and options -/

example : ComputableInTimeAndSpace (fun n : ℕ => (Sum.inl (n + 1) : ℕ ⊕ Bool)) encNat
    (encSum encNat encBool) (fun n => 2 * (encNat n).length + 10) (fun _ => 0) :=
  computableInTimeAndSpace_nat_succ.sum_inl.mono (fun _ => le_rfl) fun _ => le_rfl

example : ComputableInTimeAndSpace (fun n : ℕ => (Sum.inr n.bodd : ℕ ⊕ Bool)) encNat
    (encSum encNat encBool) (fun n => 2 * (encNat n).length + 10) (fun _ => 0) :=
  computableInTimeAndSpace_nat_bodd.sum_inr.mono (fun _ => le_rfl) fun _ => le_rfl

example : ComputableInTimeAndSpace (fun n : ℕ => some (n / 2)) encNat (encOption encNat)
    (fun n => 2 * (encNat n).length + 9) (fun _ => 0) :=
  computableInTimeAndSpace_nat_div_two.option_some.mono (fun _ => le_rfl) fun _ => le_rfl

-- Constants are computable relative to every input encoding.
example : ComputableInTimeAndSpace (fun _ : List ℕ => (none : Option ℕ)) (encList encNat)
    (encOption encNat) (fun _ => 3) (fun _ => 0) :=
  (computableInTimeAndSpace_const none).mono (fun _ => by simp) fun _ => le_rfl

example : ComputableInTimeAndSpace (fun x : ℕ ⊕ Bool => (x.getLeft?, x.getRight?))
    (encSum encNat encBool) (encProd (encOption encNat) (encOption encBool))
    (fun x => 10 * (encSum encNat encBool x).length + 14) (fun _ => 0) :=
  (computableInTimeAndSpace_sum_getLeft?.prod_mk computableInTimeAndSpace_sum_getRight?).mono
    (fun _ => by lia) fun _ => by lia

example : ComputableInTimeAndSpace (fun o : Option ℕ => (o.isSome, o.isNone)) (encOption encNat)
    (encProd encBool encBool) (fun _ => 29) (fun _ => 0) :=
  (computableInTimeAndSpace_option_isSome.prod_mk computableInTimeAndSpace_option_isNone).mono
    (fun _ => le_rfl) fun _ => le_rfl

-- The default of `getD` is part of the machine and contributes to the running time.
example : ComputableInTimeAndSpace (Option.getD · 6 : Option ℕ → ℕ) (encOption encNat) encNat
    (fun o => 2 * (encOption encNat o).length + 4) (fun _ => 0) :=
  (computableInTimeAndSpace_option_getD 6).mono
    (fun _ => by simp [show encNat 6 = [false, true, true] by decide]) fun _ => le_rfl

/-! ### Lists -/

-- Lists are built from machines that compute their parts from the same input.
example : ComputableInTimeAndSpace (fun l : List ℕ => l.headD 0 :: l.tail) (encList encNat)
    (encList encNat) (fun l => 10 * (encList encNat l).length + 9) (fun _ => 0) :=
  ((computableInTimeAndSpace_list_headD 0).list_cons computableInTimeAndSpace_list_tail).mono
    (fun _ => by simp; lia) fun _ => le_rfl

example : ComputableInTimeAndSpace (fun l : List ℕ => l ++ l.tail) (encList encNat)
    (encList encNat) (fun l => 4 * (encList encNat l).length + 5) (fun _ => 0) :=
  (computableInTimeAndSpace_id.list_append computableInTimeAndSpace_list_tail).mono
    (fun _ => by lia) fun _ => le_rfl

example : ComputableInTimeAndSpace (fun n : ℕ => [n + 1]) encNat (encList encNat)
    (fun n => 4 * (encNat n).length + 5) (fun _ => 0) :=
  computableInTimeAndSpace_nat_succ.list_singleton.mono (fun _ => by lia) fun _ => le_rfl

example : ComputableInTimeAndSpace (fun l : List (List ℕ) => (l.isEmpty, l.flatten))
    (encList (encList encNat)) (encProd encBool (encList encNat))
    (fun l => 2 * (encList (encList encNat) l).length + 21) (fun _ => 0) :=
  (computableInTimeAndSpace_list_isEmpty.prod_mk computableInTimeAndSpace_list_flatten).mono
    (fun _ => by lia) fun _ => le_rfl

/-! ### Natural numbers -/

-- Time bounds can be stated in terms of the number: its code has `Nat.size` bits.
example : ComputableInTimeAndSpace (· + 1) encNat encNat (fun n => 2 * n.size + 2) (fun _ => 0) :=
  computableInTimeAndSpace_nat_succ.mono (fun n => by rw [length_encNat]) fun _ => le_rfl

example : ComputableInTimeAndSpace (fun n : ℕ => (decide (n = 0), n / 2)) encNat
    (encProd encBool encNat) (fun n => 2 * (encNat n).length + 21) (fun _ => 0) :=
  (computableInTimeAndSpace_nat_decide_eq_zero.prod_mk computableInTimeAndSpace_nat_div_two).mono
    (fun _ => by lia) fun _ => le_rfl

end CslibTests.MultiTapeEncoding
