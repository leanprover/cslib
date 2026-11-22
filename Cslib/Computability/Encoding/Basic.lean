/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Log
public import Cslib.Computability.Encoding.Delimit

/-!
# Default encodings

Provides default encodings and encoding combinators for basic Lean types such as natural numbers,
finite types, products, dependent pairs, sums, options and lists into Boolean words.

Since the complexity of a function depends on the exact encoding used, and thus the encoding
is part of the definition of the function, we do not use a class but instead provide encodings
merely as a convenience.

The `delimit` function is used as the basic building block here: It creates a self-delimiting,
prefix-free code by replacing each bit `b` of a word with `[true, b]` and appending `[false]`.

The product encoding delimits the first component and appends the second, and lists are encoded by
delimiting each element. Dependent pairs are encoded like products, with the second component
encoded under the encoding selected by the first one. Sums prefix the code of the component with a
tag bit, and options are encoded as the sum `Unit ⊕ α`. Booleans are their single bit, natural
numbers use the little-endian binary code `Nat.bits`, and `Fin n` uses a fixed-width binary code of
`Nat.clog 2 n` bits, which `encFintype` transfers to any finite type via `Fintype.equivFin`.
Subsingletons, including propositions, are encoded as the empty word by `encSubsingleton`.

Products delimit only their first component because the second one extends to the end of the code
word, so a delimiter would add nothing for parsing; this keeps the second component undoubled and
the size of right-nested products linear. Lists delimit every element since their number is not
known in advance, and sums use a tag bit rather than a delimiter since it has a fixed length.

In general, a code word followed by further data cannot be split again; for example,
`encList enc [a]` is a prefix of `encList enc [a, b]`. Wrap an encoding with `encDelimited` (as
`encList` does for its elements) when its end has to be recognizable, see `delimit_append_inj`.

We do not use Mathlib's `Computability.Encoding` combinators since they change the alphabet
(e.g. `encodingProd` encodes into `Γ₁ ⊕ Γ₂`), while here every encoding targets `List Bool`.
-/

@[expose] public section

namespace Cslib.Encoding

variable {α β : Type*}

/-- Wraps every code word of an encoding with `delimit`, so that it can be followed by further
data. -/
@[simps (attr := scoped grind =)]
def encDelimited (enc : α ↪ List Bool) : α ↪ List Bool :=
  ⟨fun a => delimit (enc a), delimit_injective.comp enc.injective⟩

/-! ### Basic types -/

/-- A Boolean is encoded by its single bit. -/
@[simps (attr := scoped grind =)]
def encBool : Bool ↪ List Bool :=
  ⟨([·]), List.singleton_injective⟩

/-- Boolean words already are codes. -/
@[simps (attr := scoped grind =)]
def encBits : List Bool ↪ List Bool := ⟨id, Function.injective_id⟩

/-- `Nat.bits` is injective. Candidate for upstreaming to `Mathlib.Data.Nat.Bits`. -/
theorem _root_.Nat.bits_injective : Function.Injective Nat.bits := by
  intro m n h
  induction m using Nat.binaryRec' generalizing n <;> induction n using Nat.binaryRec' <;>
    grind [Nat.bits_append_bit, Nat.zero_bits]

@[simp]
theorem _root_.Nat.bits_inj {m n : ℕ} : m.bits = n.bits ↔ m = n := Nat.bits_injective.eq_iff

@[simp]
theorem _root_.Nat.bits_eq_nil {n : ℕ} : n.bits = [] ↔ n = 0 := by
  simpa using Nat.bits_inj (m := n) (n := 0)

/-- A natural number is encoded in binary, least significant bit first, as `Nat.bits`. -/
@[simps (attr := scoped grind =)]
def encNat : ℕ ↪ List Bool := ⟨Nat.bits, Nat.bits_injective⟩

/-! ### Finite types -/

/-- `Fin n` is encoded in binary as a fixed-width code of `Nat.clog 2 n` bits, least significant
bit first. -/
def encFin (n : ℕ) : Fin n ↪ List Bool :=
  ⟨fun a => (List.range (Nat.clog 2 n)).map (a.val.testBit ·), fun a b h => by
    refine Fin.ext (Nat.eq_of_testBit_eq fun i => ?_)
    have := Nat.le_pow_clog Nat.one_lt_two n
    have := @Nat.pow_le_pow_right 2 Nat.two_pos (Nat.clog 2 n) i
    grind [Nat.testBit_lt_two_pow, List.map_inj_left]⟩

theorem encFin_apply (n : ℕ) (a : Fin n) :
    encFin n a = (List.range (Nat.clog 2 n)).map (a.val.testBit ·) := rfl

@[simp, scoped grind =]
theorem length_encFin (n : ℕ) (a : Fin n) : (encFin n a).length = Nat.clog 2 n := by
  simp [encFin_apply]

/-- The `i`-th bit of the code is the `i`-th bit of the number. -/
@[simp, scoped grind =]
theorem getElem_encFin (n : ℕ) (a : Fin n) (i : ℕ) (h : i < (encFin n a).length) :
    (encFin n a)[i] = a.val.testBit i := by
  simp [encFin_apply]

/-- Types with at most one element are encoded as the empty word. -/
@[simp]
theorem encFin_eq_nil {n : ℕ} (h : n ≤ 1) (a : Fin n) : encFin n a = [] := by
  rw [← List.length_eq_zero_iff, length_encFin, Nat.clog_of_right_le_one h]

/-- A finite type is encoded with the fixed width `Nat.clog 2 (Fintype.card α)` through
`Fintype.equivFin`. The enumeration is not computable and depends on the `Fintype` instance, so
this encoding serves existence results where only the code length matters. Concrete machines
should instead compose an explicit embedding `α ↪ Fin n` with `encFin n`. -/
noncomputable def encFintype (α : Type*) [Fintype α] : α ↪ List Bool :=
  (Fintype.equivFin α).toEmbedding.trans (encFin _)

theorem encFintype_apply [Fintype α] (a : α) :
    encFintype α a = encFin _ (Fintype.equivFin α a) := rfl

@[simp, scoped grind =]
theorem length_encFintype [Fintype α] (a : α) :
    (encFintype α a).length = Nat.clog 2 (Fintype.card α) :=
  length_encFin _ _

/-- Subsingletons are encoded as the empty word via `encFintype`. -/
@[simp]
theorem encFintype_eq_nil [Fintype α] [Subsingleton α] (a : α) : encFintype α a = [] :=
  encFin_eq_nil (Fintype.card_le_one_iff_subsingleton.2 ‹_›) _

/-- A type with at most one element, such as a proposition, is encoded as the empty word. Unlike
`encFintype`, this is computable and needs no `Fintype` instance. -/
@[simps (attr := scoped grind =)]
def encSubsingleton (α : Sort*) [Subsingleton α] : α ↪ List Bool :=
  ⟨fun _ => [], fun _ _ _ => Subsingleton.elim _ _⟩

/-- On finite subsingletons, `encSubsingleton` agrees with `encFintype`. -/
theorem encFintype_eq_encSubsingleton [Fintype α] [Subsingleton α] :
    encFintype α = encSubsingleton α :=
  DFunLike.ext _ _ fun a => encFintype_eq_nil a

/-! ### Combinators -/

/-- A product is encoded as the delimited first component followed by the second component.
Only the first component is delimited since the second one extends to the end of the code word;
this keeps the second component undoubled and right-nested products linear in size. -/
@[simps (attr := scoped grind =)]
def encProd (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨fun p => delimit (enc₁ p.1) ++ enc₂ p.2, fun _ _ h => by simpa [Prod.ext_iff] using h⟩

/-- A dependent pair is encoded as the delimited first component followed by the second component,
encoded under the encoding selected by the first component. As for `encProd`, only the first
component is delimited, which is exactly what is needed to know the encoding of the second one. -/
@[simps (attr := scoped grind =)]
def encSigma {β : α → Type*} (enc₁ : α ↪ List Bool) (enc₂ : ∀ a, β a ↪ List Bool) :
    (a : α) × β a ↪ List Bool :=
  ⟨fun x => delimit (enc₁ x.1) ++ enc₂ x.1 x.2, by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨h₁, h₂⟩ := delimit_append_inj h
    dsimp only at h₁ h₂
    obtain rfl := enc₁.injective h₁
    rw [(enc₂ a).injective h₂]⟩

/-- A product is a dependent pair with a constant second type. -/
theorem encProd_eq_encSigma (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    encProd enc₁ enc₂ p = encSigma enc₁ (fun _ => enc₂) ⟨p.1, p.2⟩ := rfl

/-- A sum is encoded by a tag bit, `false` for `inl` and `true` for `inr`, followed by the code of
the component. A tag bit is used instead of a delimiter since it has a fixed length and does not
double the component. -/
def encSum (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) : α ⊕ β ↪ List Bool :=
  ⟨fun x => x.elim (false :: enc₁ ·) (true :: enc₂ ·), by rintro (a | a) (b | b) h <;> simp_all⟩

/-- An option is encoded as the sum `Unit ⊕ α`: `none` is encoded as `[false]` and `some a` as
`true` followed by the code of `a`. -/
def encOption (enc : α ↪ List Bool) : Option α ↪ List Bool :=
  ((Equiv.optionEquivSumPUnit.{0} α).trans (Equiv.sumComm α Unit)).toEmbedding.trans
    (encSum (encSubsingleton Unit) enc)

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

@[simp, scoped grind =] theorem encSum_inl (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (a : α) :
    encSum enc₁ enc₂ (.inl a) = false :: enc₁ a := rfl

@[simp, scoped grind =] theorem encSum_inr (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (b : β) :
    encSum enc₁ enc₂ (.inr b) = true :: enc₂ b := rfl

@[simp, scoped grind =]
theorem encOption_none (enc : α ↪ List Bool) : encOption enc none = [false] := rfl

@[simp, scoped grind =] theorem encOption_some (enc : α ↪ List Bool) (a : α) :
    encOption enc (some a) = true :: enc a := rfl

@[simp, scoped grind =] theorem encList_nil (enc : α ↪ List Bool) : encList enc [] = [] := rfl

@[simp, scoped grind =] theorem encList_cons (enc : α ↪ List Bool) (a : α) (l : List α) :
    encList enc (a :: l) = delimit (enc a) ++ encList enc l := rfl

theorem encList_singleton (enc : α ↪ List Bool) (a : α) :
    encList enc [a] = delimit (enc a) := by
  simp

@[simp] theorem encList_append (enc : α ↪ List Bool) (l l' : List α) :
    encList enc (l ++ l') = encList enc l ++ encList enc l' := List.flatMap_append ..

/-! ### Lengths -/

-- Not a `simp` lemma, since `simp` proves it from `encProd_apply` and `length_delimit`.
theorem length_encProd (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    (encProd enc₁ enc₂ p).length = 2 * (enc₁ p.1).length + 1 + (enc₂ p.2).length := by
  simp

theorem length_encSigma {β : α → Type*} (enc₁ : α ↪ List Bool) (enc₂ : ∀ a, β a ↪ List Bool)
    (x : (a : α) × β a) :
    (encSigma enc₁ enc₂ x).length = 2 * (enc₁ x.1).length + 1 + (enc₂ x.1 x.2).length := by
  simp

theorem length_encSum (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (x : α ⊕ β) :
    (encSum enc₁ enc₂ x).length =
      x.elim (fun a => (enc₁ a).length + 1) (fun b => (enc₂ b).length + 1) := by
  cases x <;> simp

theorem length_encOption (enc : α ↪ List Bool) (o : Option α) :
    (encOption enc o).length = o.elim 1 (fun a => (enc a).length + 1) := by
  cases o <;> simp

theorem length_encOption_none (enc : α ↪ List Bool) : (encOption enc none).length = 1 := rfl

theorem length_encOption_some (enc : α ↪ List Bool) (a : α) :
    (encOption enc (some a)).length = (enc a).length + 1 := rfl

/-- Each element contributes twice the length of its code plus one delimiter bit. -/
@[simp, scoped grind =] theorem length_encList (enc : α ↪ List Bool) (l : List α) :
    (encList enc l).length = 2 * (l.map fun a => (enc a).length).sum + l.length := by
  induction l <;> grind

/-- Delimiters account for at least one bit per list element, even for empty element codes. -/
theorem length_le_length_encList (enc : α ↪ List Bool) (l : List α) :
    l.length ≤ (encList enc l).length := by
  simp

end Cslib.Encoding
