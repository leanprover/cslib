/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Mathlib.Computability.Encoding
public import Mathlib.Data.List.SplitOn
public import Mathlib.Algebra.Field.Rat

/-!
# Bitstring Encodings

This section provides a type`class`-inferrable version of Mathlib's `Computability.Encoding`,
specialized to the alphabet `Bool`.
(Note that `Computability.Encoding` itself has undergone a rewrite recently.)

Making it a `class` makes it easier to quickly ask if a function is computable in polynomial time,
without having to explicitly pass around the encoding.

The idea of this class is to set up instances for common types like Bool, ℕ, ℤ, ℚ,
and instance derivations for product and list types,
so that the resulting instance for any common type will be polytime-transcodable
with any other reasonable binary encoding of that type.

Thus, while it may not be obvious without looking carefully
which of several essentially equivalent encodings of a type is being used,
we can at least be sure that for functions between types with `BitstringEncoding` instances,
questions of polynomial-time computability are well-defined, in the sense that
the formalization will capture the intended meaning.
-/

@[expose] public section

open Computability

/-- A canonical encoding of a type as bitstrings (`List Bool`).

This is a class version of Mathlib's (bundled) `Computability.Encoding`, specialized to the
alphabet `Bool`. -/
class BitstringEncoding (α : Type*) where
  /-- The encoding function. -/
  encode : α → List Bool
  /-- The decoding function; `none` on bitstrings that encode nothing. -/
  decode : List Bool → Option α
  /-- Decoding is a left inverse of encoding. -/
  decode_encode : ∀ x, decode (encode x) = some x

attribute [simp] BitstringEncoding.decode_encode

namespace BitstringEncoding

variable {α β : Type*}

theorem encode_injective [BitstringEncoding α] :
    Function.Injective (encode : α → List Bool) := fun _ _ h =>
  Option.some_injective _ (by rw [← decode_encode, ← decode_encode, h])

/-- Transport a `BitstringEncoding` along an injection `f` with partial inverse `g`. -/
@[reducible]
def ofLeftInverse [BitstringEncoding β] (f : α → β) (g : β → Option α)
    (h : ∀ x, g (f x) = some x) : BitstringEncoding α where
  encode a := encode (f a)
  decode l := (decode l).bind g
  decode_encode a := by simp [h]

/- ## Ground instances -/

/-- `ℕ` is encoded by its (little-endian) binary representation, as in
`Computability.encodeNat`. -/
instance : BitstringEncoding ℕ where
  encode := Computability.encodeNat
  decode l := some (Computability.decodeNat l)
  decode_encode n := congrArg some (Computability.decode_encodeNat n)

/-- `Bool` is encoded as a singleton bitstring. -/
instance : BitstringEncoding Bool where
  encode b := [b]
  decode l := match l with
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/- ## Self-delimiting blocks

To concatenate encodings of multipartite data structures,
we need each piece to announce its own end.
`delimit` writes each payload bit `b` as `true :: b :: ·` and terminates with `false`;
`undelimit` parses one such block off the front of the input. -/

/-- Make a bitstring self-delimiting: each payload bit `b` becomes the two bits
`[true, b]`, and the block is terminated by `false`. -/
def delimit : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delimit l

/-- Parse one self-delimiting block from the front of the input, returning the payload
and the remaining input. -/
def undelimit : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: input => (undelimit input).map fun p => (b :: p.1, p.2)
  | _ => none

@[simp]
theorem undelimit_delimit (l rest : List Bool) :
    undelimit (delimit l ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, undelimit, ih]

@[simp]
theorem delimit_length (l : List Bool) : (delimit l).length = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, ih]; omega

/-- Parse a sequence of self-delimiting blocks, using `fuel` to bound the number of blocks.

This is the auxiliary, fuel-carrying implementation of `undelimitBlocks`; since every block
is nonempty, `input.length` is always enough fuel. -/
def undelimitBlocksAux : ℕ → List Bool → Option (List (List Bool))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, input => do
    let (block, rest) ← undelimit input
    let blocks ← undelimitBlocksAux fuel rest
    return block :: blocks

/-- Parse a sequence of self-delimiting blocks off the front of the input.

Since every block is nonempty, `input.length` bounds the number of blocks, so it always
suffices as fuel for `undelimitBlocksAux`. -/
def undelimitBlocks (input : List Bool) : Option (List (List Bool)) :=
  undelimitBlocksAux input.length input

theorem length_le_length_flatten_delimit (l : List (List Bool)) :
    l.length ≤ ((l.map delimit).flatten).length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      delimit_length]
    omega

private theorem undelimitBlocksAux_flatten_delimit (l : List (List Bool)) :
    ∀ fuel, l.length ≤ fuel → undelimitBlocksAux fuel ((l.map delimit).flatten) = some l := by
  induction l with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons b t ih =>
    intro fuel hfuel
    rw [List.length_cons] at hfuel
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨hd, tl, hcons⟩ : ∃ hd tl, delimit b ++ (t.map delimit).flatten = hd :: tl := by
      cases b <;> exact ⟨_, _, rfl⟩
    simp only [List.map_cons, List.flatten_cons, hcons, undelimitBlocksAux]
    rw [← hcons, undelimit_delimit]
    simp [ih fuel (by omega)]

theorem undelimitBlocks_flatten_delimit (l : List (List Bool)) :
    undelimitBlocks ((l.map delimit).flatten) = some l :=
  undelimitBlocksAux_flatten_delimit l _ (length_le_length_flatten_delimit l)

/-- Decode every block in a list of bitstrings, failing if any block fails to decode.

(This is `List.mapM decode` in the `Option` monad, written out by hand so that it works
for `α` in any universe.) -/
def decodeAll [BitstringEncoding α] : List (List Bool) → Option (List α)
  | [] => some []
  | b :: t =>
    match decode b, decodeAll t with
    | some a, some l => some (a :: l)
    | _, _ => none

@[simp]
theorem decodeAll_map_encode [BitstringEncoding α] (l : List α) :
    decodeAll (l.map encode) = some l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [decodeAll, ih]

/- ## Derived instances -/

/--
An encoding of `Option α` is obtained encoding `none` as the empty bitstring
and `some a` as the encoding of `a` prefixed by a `true`.
-/
instance [BitstringEncoding α] : BitstringEncoding (Option α) where
  encode
    | none => []
    | some a => true :: encode a
  decode input :=
    match input with
    | [] => some none
    | true :: rest => (decode rest).map some
    | false :: _ => none
  decode_encode
    | none => rfl
    | some a => by simp

/-- A pair is encoded as a self-delimiting block for the first component followed by the
encoding of the second. -/
instance [BitstringEncoding α] [BitstringEncoding β] : BitstringEncoding (α × β) where
  encode p := delimit (encode p.1) ++ encode p.2
  decode input :=
    match undelimit input with
    | none => none
    | some (block, rest) =>
      match decode block, decode rest with
      | some a, some b => some (a, b)
      | _, _ => none
  decode_encode p := by simp

/-- A list is encoded as the concatenation of self-delimiting blocks for its elements. -/
instance [BitstringEncoding α] : BitstringEncoding (List α) where
  encode l := ((l.map encode).map delimit).flatten
  decode input :=
    match undelimitBlocks input with
    | none => none
    | some blocks => decodeAll blocks
  decode_encode l := by
    rw [undelimitBlocks_flatten_delimit (l.map encode)]
    exact decodeAll_map_encode l

/-- A subtype inherits the encoding of the ambient type; decoding additionally checks the
defining predicate. This yields encodings for `ℕ+` and friends for free. -/
instance {p : α → Prop} [BitstringEncoding α] [DecidablePred p] :
    BitstringEncoding (Subtype p) where
  encode x := encode x.val
  decode input := (decode input).bind fun a => if h : p a then some ⟨a, h⟩ else none
  decode_encode x := by simp [x.property]

/-- `ℕ+` is encoded as the subtype `{n : ℕ // 0 < n}` it is defined to be. -/
instance : BitstringEncoding ℕ+ :=
  inferInstanceAs (BitstringEncoding {n : ℕ // 0 < n})

/-- `ℤ` is encoded via the pair `(n.toNat, (-n).toNat)` (one component is always `0`). -/
instance : BitstringEncoding ℤ :=
  ofLeftInverse (fun n : ℤ => (n.toNat, (-n).toNat))
    (fun p => some ((p.1 : ℤ) - (p.2 : ℤ))) (fun n => congrArg some (by dsimp only; omega))

/-- `ℚ` is encoded as its (reduced) numerator-denominator pair. -/
instance : BitstringEncoding ℚ :=
  ofLeftInverse (fun q : ℚ => (q.num, q.den))
    (fun p => some ((p.1 : ℚ) / (p.2 : ℚ))) (fun q => by simp [Rat.num_div_den])

end BitstringEncoding
