

import Mathlib.Computability.Encoding
import Mathlib.Data.List.SplitOn

open Computability

section Encodings
/-
These encodings are used in the formalization of complexity classes such as P and NP.
Note that in a Zulip discussion thread, Daniel Weber contributed some more general encodings.
We might eventually want to replace these with his more general versions.
see: https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Formalise.20the.20proposition.20P.20.E2.89.A0NP/with/453031558
-/

def finEncodingListBool : Computability.FinEncoding (List Bool) where
  Γ := Bool
  encode := id
  decode := Option.some
  decode_encode _ := rfl
  ΓFin := Bool.fintype


def encode_list_bool_prod_list_bool :
    (List Bool × List Bool) → List (Bool) :=
  fun ⟨l1, l2⟩ ↦ ((l1.map some) ++ [none] ++ (l2.map some)).flatMap (fun
    | some b => [true, b]
    | none   => [false, false])

def decode_list_bool_prod_list_bool :
    List (Bool) → Option (List Bool × List Bool) := sorry

lemma decode_encode_list_bool_prod_list_bool :
    ∀ x : List Bool × List Bool,
      decode_list_bool_prod_list_bool (encode_list_bool_prod_list_bool x) = some x := sorry


end Encodings
