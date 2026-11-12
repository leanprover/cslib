/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Computability.Encoding
public import Cslib.Computability.Encoding.Delimit

/-!
# Default encodings

Provides default encodings and encoding combinators for basic Lean types such as natural numbers,
products, options and lists into Boolean words.

Since the complexity of a function depends on the exact encoding used, and thus the encoding
is part of the definition of the function, we do not use a class but instead provide encodings
merely as a convenience.

The `delimit` function is used as the basic building block here: It creates a self-delimiting,
prefix-free code by replacing each bit `b` of a word with `[true, b]` and appending `[false]`.

The product encoding delimits the first component and lists are encoded by delimiting each element.
Options use the empty word for `none` and prefix `some` with `true`. Natural numbers use Mathlib's
binary encoding `Computability.encodeNat`.

Only `delimit` itself is prefix-free; none of the encodings defined here are. For example,
`encList enc [a]` is a prefix of `encList enc [a, b]`, and `encProd enc₁ enc₂` does not delimit its
second component. Hence `encProd enc₁ (encProd enc₂ enc₃)` is a valid encoding of `α × β × γ`, but
a code word followed by further data can in general not be split again. Wrap an encoding with
`delimit` (as `encList` does for its elements) when its end has to be recognizable.

We do not use Mathlib's `Computability.Encoding` combinators since they change the alphabet
(e.g. `encodingProd` encodes into `Γ₁ ⊕ Γ₂`), while here every encoding targets `List Bool`.
-/

@[expose] public section

namespace Cslib.Encoding

variable {α β : Type*}

/-- A Boolean is encoded by its single bit. -/
def encBool : Bool ↪ List Bool :=
  ⟨fun b => [b], fun _ _ h => (List.cons.inj h).1⟩

/-- Boolean words already are codes. -/
def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

/-- A natural number is encoded in binary, least significant bit first, using Mathlib's
`Computability.encodeNat`. -/
def encNat : ℕ ↪ List Bool :=
  ⟨Computability.encodeNat, Computability.encodingNatBool.encode_injective⟩

@[simp] theorem encBool_apply (b : Bool) : encBool b = [b] := rfl

@[simp] theorem encBits_apply (w : List Bool) : encBits w = w := rfl

@[simp] theorem encNat_apply (n : ℕ) : encNat n = Computability.encodeNat n := rfl

/-- A product is encoded as the delimited first component followed by the second component. -/
def encProd (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨fun p => delimit (enc₁ p.1) ++ enc₂ p.2, fun _ _ h =>
    Prod.ext (enc₁.injective (delimit_append_inj h).1)
      (enc₂.injective (delimit_append_inj h).2)⟩

/-- Encoding of `Option`: `none` is encoded as the empty word while `some a` as `true` followed by
the code of `a`. -/
def encOption (enc : α ↪ List Bool) : Option α ↪ List Bool :=
  ⟨fun o => o.elim [] (true :: enc ·), by
    rintro (_ | a) (_ | b) h <;> simp_all⟩

/-- A list is encoded as the concatenation of the delimited codes of its elements. -/
def encList (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨fun l => l.flatMap (delimit ∘ enc), fun l l' h => by
    induction l generalizing l' with
    | nil => cases l' <;> simp_all
    | cons a l ih =>
      cases l' with
      | nil => simp at h
      | cons a' l' =>
        rw [enc.injective (delimit_append_inj h).1, ih _ (delimit_append_inj h).2]⟩

@[simp] theorem encProd_apply (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    encProd enc₁ enc₂ p = delimit (enc₁ p.1) ++ enc₂ p.2 := rfl

@[simp] theorem encOption_none (enc : α ↪ List Bool) : encOption enc none = [] := rfl

@[simp] theorem encOption_some (enc : α ↪ List Bool) (a : α) :
    encOption enc (some a) = true :: enc a := rfl

@[simp] theorem encList_nil (enc : α ↪ List Bool) : encList enc [] = [] := rfl

@[simp] theorem encList_cons (enc : α ↪ List Bool) (a : α) (l : List α) :
    encList enc (a :: l) = delimit (enc a) ++ encList enc l := rfl

theorem encList_singleton (enc : α ↪ List Bool) (a : α) :
    encList enc [a] = delimit (enc a) := by
  simp

@[simp] theorem encList_append (enc : α ↪ List Bool) (l l' : List α) :
    encList enc (l ++ l') = encList enc l ++ encList enc l' := by
  induction l <;> simp_all

-- Not a `simp` lemma, since `simp` proves it from `encProd_apply` and `length_delimit`.
theorem length_encProd (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    (encProd enc₁ enc₂ p).length = 2 * (enc₁ p.1).length + 1 + (enc₂ p.2).length := by
  simp

theorem length_encOption (enc : α ↪ List Bool) (o : Option α) :
    (encOption enc o).length = o.elim 0 (fun a => (enc a).length + 1) := by
  cases o <;> simp

theorem length_encOption_none (enc : α ↪ List Bool) : (encOption enc none).length = 0 := rfl

theorem length_encOption_some (enc : α ↪ List Bool) (a : α) :
    (encOption enc (some a)).length = (enc a).length + 1 := rfl

/-- Each element contributes twice the length of its code plus one delimiter bit. -/
@[simp] theorem length_encList (enc : α ↪ List Bool) (l : List α) :
    (encList enc l).length = 2 * (l.map fun a => (enc a).length).sum + l.length := by
  induction l <;> grind [encList_nil, encList_cons, length_delimit]

/-- Delimiters account for at least one bit per list element, even for empty element codes. -/
theorem length_le_length_encList (enc : α ↪ List Bool) (l : List α) :
    l.length ≤ (encList enc l).length := by
  simp

end Cslib.Encoding
