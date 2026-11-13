/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Cslib.Computability.Encoding.Basic

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

-- `encBool` and `encNat` agree with Mathlib's encodings.
example : ⇑encBool = Computability.encodingBoolBool.encode := rfl
example : ⇑encNat = Computability.encodingNatBool.encode := rfl

-- Binary, least significant bit first.
example : encNat 0 = [] := by decide
example : encNat 6 = [false, true, true] := by decide

/-! ### Encoding combinators -/

example : encProd encBool encBool (true, false) = [true, true, false, false] := rfl
example : encProd encBits encBits ([], [true]) = [false, true] := rfl

example : encOption encBool none = [] := rfl
example : encOption encBool (some false) = [true, false] := rfl
example : encOption (encOption encBool) (some none) = [true] := rfl
example : encOption (encOption encBool) (some (some true)) = [true, true, true] := rfl

example : encList encBits [[], [true]] = [false, true, true, false] := rfl
example : encList encBits [] = [] := rfl

-- Nested combinators.
example : encList (encProd encBool encBits) [(true, [false])] =
    [true, true, true, true, true, false, true, false, false] := rfl

-- The same word encodes different values under different encodings.
example : encOption encBool none = encList encBool [] := rfl

-- The encodings are not prefix-free.
example : encProd encBool encBits (true, []) ++ [true] = encProd encBool encBits (true, [true]) :=
  rfl
example : encList encBits [[true]] ++ encList encBits [[]] = encList encBits [[true], []] := by
  simp

example : (encProd encBits encBits ([true], [false, false])).length = 5 := by simp
example : (encList encBits [[true], []]).length = 4 := by simp

/-! ### Injectivity through `simp` -/

example (a b : Bool × List Bool) : encProd encBool encBits a = encProd encBool encBits b ↔ a = b :=
  by simp [Prod.ext_iff]
example (a b : Bool) (l l' : List Bool) :
    encList encBool (a :: l) = encList encBool (b :: l') ↔ a = b ∧ l = l' := by simp
example (o o' : Option Bool) : encOption encBool o = encOption encBool o' ↔ o = o' := by simp

/-! ### `grind` -/

example (w v : List Bool) (h : delimit w = delimit v) : w = v := by grind
example (w v u u' : List Bool) (h : w ≠ v) : delimit w ++ u ≠ delimit v ++ u' := by grind

-- Length bounds, as needed for complexity bounds.
example (b : Bool) : (encBool b).length = 1 := by grind
example (p : Bool × List Bool) :
    (encProd encBool encBits p).length = p.2.length + 3 := by grind
example (enc : α ↪ List Bool) (a : α) (l : List α) :
    (encList enc (l ++ [a])).length = (encList enc l).length + 2 * (enc a).length + 1 := by
  grind
example (enc : α ↪ List Bool) (l : List α) : l.length ≤ (encList enc l).length := by grind

-- Decoding the first element of a list.
example (enc : α ↪ List Bool) (a : α) (l : List α) :
    undelimit (encList enc (a :: l)) = enc a := by grind

-- Injectivity of nested encodings.
example (l l' : List (Bool × List Bool)) (h : encList (encProd encBool encBits) l =
    encList (encProd encBool encBits) l') : l = l' := by grind

end CslibTests.Encoding
