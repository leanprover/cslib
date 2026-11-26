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

/-! ### Pairs -/

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

example : ComputableInTimeAndSpace (· + 1) encNat encNat (fun n => 2 * n.size + 2) (fun _ => 0) :=
  computableInTimeAndSpace_nat_succ.mono (fun n => by grind) fun _ => le_rfl

example : ComputableInTimeAndSpace (fun n : ℕ => (decide (n = 0), n / 2)) encNat
    (encProd encBool encNat) (fun n => 2 * (encNat n).length + 21) (fun _ => 0) :=
  (computableInTimeAndSpace_nat_decide_eq_zero.prod_mk computableInTimeAndSpace_nat_div_two).mono
    (fun _ => by lia) fun _ => le_rfl

end CslibTests.MultiTapeEncoding
