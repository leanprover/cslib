/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Cslib.Computability.Encoding.Basic
import Mathlib.Computability.Encoding

namespace CslibTests.Encoding

open Cslib.Encoding

variable {α : Type*}

/-! ### `delimit` -/

example : delimit [] = [false] := rfl
example : delimit [false, true] = [true, false, true, true, false] := rfl

-- Undelimiting recovers the word and the data after it, also after `delimit_cons` fired.
example : undelimit (delimit [true, false] ++ [true, true]) = [true, false] := by simp
example : dropDelimited (delimit [true, false] ++ [true, true]) = [true, true] := by simp
example (b : Bool) (w u : List Bool) : undelimit (delimit (b :: w) ++ u) = b :: w := by simp
example (b : Bool) (w u : List Bool) : dropDelimited (delimit (b :: w) ++ u) = u := by simp

-- Words that are prefixes of each other have delimited codes that are not.
example : ¬ delimit [true] <+: delimit [true, false] := by simp

-- Injectivity is available to `simp`.
example (w v : List Bool) : delimit w = delimit v ↔ w = v := by simp
example (w v u u' : List Bool) : delimit w ++ u = delimit v ++ u' ↔ w = v ∧ u = u' := by simp

/-! ### Basic encodings -/

-- `encBool` agrees with Mathlib's encoding, and `encNat` is `Nat.bits`.
example : ⇑encBool = Computability.encodingBoolBool.encode := rfl
example (n : ℕ) : encNat n = n.bits := rfl

-- Binary, least significant bit first.
example : encNat 0 = [] := by decide
example : encNat 6 = [false, true, true] := by decide

-- `simp` unfolds `encNat` to `Nat.bits`, which gives it Mathlib's lemmas and injectivity.
example (n : ℕ) : encNat (2 * n + 1) = true :: encNat n := by simp
example (n : ℕ) (h : n ≠ 0) : encNat (2 * n) = false :: encNat n := by simp [h]
example (m n : ℕ) : encNat m = encNat n ↔ m = n := by simp
example (n : ℕ) : encNat n = [] ↔ n = 0 := by simp

/-! ### Finite types -/

-- Fixed width `⌈log₂ n⌉`, least significant bit first.
example : encFin 5 3 = [true, true, false] := by
  have h : Nat.clog 2 5 = 3 := le_antisymm (Nat.clog_le_of_le_pow (by decide))
    ((Nat.lt_clog_iff_pow_lt one_lt_two).2 (by decide))
  simp only [encFin_apply, h]
  decide
example : encFin 8 5 = [true, false, true] := by
  simp only [encFin_apply, show Nat.clog 2 8 = 3 by simpa using Nat.clog_pow 2 3 one_lt_two]
  decide

-- `Fin 2` agrees with `encBool`.
example : encFin 2 0 = encBool false ∧ encFin 2 1 = encBool true := by
  simp only [encFin_apply, show Nat.clog 2 2 = 1 by simpa using Nat.clog_pow 2 1 one_lt_two]
  decide

-- Sub-singletons are encoded as the empty word, without any special case in the definition.
example (a : Fin 1) : encFin 1 a = [] := by simp
example (a : Fin 1) : encFin 1 a = [] := rfl
example (u : Unit) : encFintype Unit u = [] := by simp
example (a : Fin 1) : encFintype (Fin 1) a = [] := by simp
example [Fintype α] [Subsingleton α] (a : α) : (encFintype α a).length = 0 := by simp

-- `encSubsingleton` needs neither `Fintype` nor `Decidable`, and also encodes proofs.
example (p : Prop) (h : p) : encSubsingleton p h = [] := rfl
example (u : Unit) : encSubsingleton Unit u = encFintype Unit u := by simp
example (x : (n : ℕ) ×' n < 4) :
    (encSigma encNat (fun n => encSubsingleton (PLift (n < 4))) ⟨x.1, ⟨x.2⟩⟩).length =
      2 * (encNat x.1).length + 1 := by simp

-- Only the code length of `encFintype` is known in general.
example [Fintype α] (a : α) : (encFintype α a).length = Nat.clog 2 (Fintype.card α) := by simp
example (a : Fin 5 ⊕ Fin 3) : (encFintype _ a).length = 3 := by
  simpa using Nat.clog_pow 2 3 one_lt_two

-- Concrete finite types are encoded by composing an explicit embedding with `encFin`.
example : (Function.Embedding.subtype (fun n : Fin 4 => n.val ≠ 1)).trans (encFin 4) ⟨3, by decide⟩
    = encFin 4 3 := rfl

/-! ### Encoding combinators -/

example : encProd encBool encBool (true, false) = [true, true, false, false] := rfl
example : encProd encBits encBits ([], [true]) = [false, true] := rfl

-- The second component of a dependent pair is encoded with the width chosen by the first one.
example : encSigma encNat (fun n => encFin n) ⟨2, 1⟩ = [true, false, true, true, false, true] := by
  simp only [encSigma_apply, encFin_apply, show Nat.clog 2 2 = 1 by
    simpa using Nat.clog_pow 2 1 one_lt_two]
  decide
example : encSigma encNat (fun n => encFin n) ⟨1, 0⟩ = [true, true, false] := by
  simp only [encSigma_apply, encFin_eq_nil le_rfl]
  decide

example : encSum encBool encBits (.inl true) = [false, true] := rfl
example : encSum encBool encBits (.inr [true]) = [true, true] := rfl

example : encOption encBool none = [false] := rfl
example : encOption encBool (some false) = [true, false] := rfl
example : encOption (encOption encBool) (some none) = [true, false] := rfl
example (o : Option Bool) :
    encOption encBool o = encSum (encSubsingleton Unit) encBool (o.elim (.inl ()) .inr) := by
  cases o <;> rfl
example : encOption (encOption encBool) (some (some true)) = [true, true, true] := rfl

example : encList encBits [[], [true]] = [false, true, true, false] := rfl
example : encList encBits [] = [] := rfl

-- Nested combinators.
example : encList (encProd encBool encBits) [(true, [false])] =
    [true, true, true, true, true, false, true, false, false] := rfl

-- The same word encodes different values under different encodings.
example : encOption encBool none = encBool false := rfl

-- The product is the dependent pair with a constant second type.
example (p : Bool × List Bool) :
    encProd encBool encBits p = encSigma encBool (fun _ => encBits) ⟨p.1, p.2⟩ := rfl

example : (encProd encBits encBits ([true], [false, false])).length = 5 := by simp
example : (encList encBits [[true], []]).length = 4 := by simp

-- The encodings are not prefix-free.
example : encProd encBool encBits (true, []) ++ [true] = encProd encBool encBits (true, [true]) :=
  rfl
example : encList encBits [[true]] ++ encList encBits [[]] = encList encBits [[true], []] := by
  simp

-- A delimited code followed by data can be split again.
example : encDelimited encBits [true] = [true, true, false] := rfl
example (a b : Bool × Bool) (u v : List Bool)
    (h : encDelimited (encProd encBool encBool) a ++ u =
      encDelimited (encProd encBool encBool) b ++ v) :
    a = b ∧ u = v := by
  simpa [Prod.ext_iff, and_assoc] using h

/-! ### Injectivity through `simp` -/

example (a b : Bool × List Bool) : encProd encBool encBits a = encProd encBool encBits b ↔ a = b :=
  by simp [Prod.ext_iff]
example (a b : Bool) (l l' : List Bool) :
    encList encBool (a :: l) = encList encBool (b :: l') ↔ a = b ∧ l = l' := by simp
example (o o' : Option Bool) : encOption encBool o = encOption encBool o' ↔ o = o' := by simp
example (x y : Bool ⊕ List Bool) : encSum encBool encBits x = encSum encBool encBits y ↔ x = y := by
  simp

/-! ### `grind` -/

example (w v : List Bool) (h : delimit w = delimit v) : w = v := by grind
example (w v u u' : List Bool) (h : w ≠ v) : delimit w ++ u ≠ delimit v ++ u' := by grind

-- Length bounds, as needed for complexity bounds.
example (b : Bool) : (encBool b).length = 1 := by grind
example (p : Bool × List Bool) :
    (encProd encBool encBits p).length = p.2.length + 3 := by grind
example (x : (n : ℕ) × Fin n) :
    (encSigma encNat (fun n => encFin n) x).length =
      2 * (encNat x.1).length + 1 + Nat.clog 2 x.1 := by grind
example (x : Bool ⊕ List Bool) : (encSum encBool encBits x).length ≤ x.elim (fun _ => 2)
    (fun l => l.length + 1) := by
  cases x <;> grind
example (enc : α ↪ List Bool) (a : α) (l : List α) :
    (encList enc (l ++ [a])).length = (encList enc l).length + 2 * (enc a).length + 1 := by
  grind
example (enc : α ↪ List Bool) (l : List α) : l.length ≤ (encList enc l).length := by grind
example [Fintype α] (l : List α) :
    (encList (encFintype α) l).length = (2 * Nat.clog 2 (Fintype.card α) + 1) * l.length := by
  induction l <;> grind

-- Decoding the first element of a list.
example (enc : α ↪ List Bool) (a : α) (l : List α) :
    undelimit (encList enc (a :: l)) = enc a := by grind

-- Injectivity of nested encodings.
example (l l' : List (Bool × List Bool)) (h : encList (encProd encBool encBits) l =
    encList (encProd encBool encBits) l') : l = l' := by grind

end CslibTests.Encoding
