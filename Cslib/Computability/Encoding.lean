/-
Copyright (c) 2026 Silvère Gangloff. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Silvère Gangloff
-/

module

public import Mathlib.Tactic.Basic
public import Mathlib.Data.Fintype.Defs

/-!
# String Encodings

This file defines:

* `StringEncoding α Symbol` — the primitive notion: a concrete encoder/decoder
  pair for `α` onto `List Symbol`, together with a roundtrip proof. A single
  type can carry many encodings (for example, unary and binary encodings of
  `Nat` over the `Bool` alphabet are both provided below).

* `StringEncodable α Symbol` — the *property* that some encoding exists.
  Useful for declarations that only need the existence of an encoding without
  committing to a particular choice.

The concrete encodings provided here are:

* `StringEncoding.listSymbol`: identity encoding of `List Symbol`.
* `StringEncoding.bool`: single-bit encoding of `Bool`.
* `StringEncoding.natUnary`: self-delimiting unary `Nat` encoding.
* `StringEncoding.natBinary`: Least significant bit first binary `Nat` encoding.
* `StringEncoding.option`: derived `Option α` encoding given any encoding of `α`.
* `StringEncoding.natUnaryPair`: a nontrivial example, `Nat × Nat` via two
  concatenated unary codes.
-/

@[expose] public section

namespace Encodable

variable {Symbol : Type} [Fintype Symbol]

/--
The primitive notion of encoding: a function `α → List Symbol` together with
a partial inverse `List Symbol → Option α` and a proof that the inverse
recovers any encoded value. The alphabet `Symbol` must be finite — without
this constraint the notion is vacuous (one could take `Symbol = α`).
-/
structure StringEncoding (α : Type) (Symbol : Type) [Fintype Symbol] where
  /-- The encoder. -/
  encode : α → List Symbol
  /-- The decoder; returns `none` on inputs that aren't valid codes. -/
  decode : List Symbol → Option α
  /-- Decoding recovers an encoded value. -/
  decode_encode_eq : ∀ (a : α), decode (encode a) = some a

/--
A type is `StringEncodable α Symbol` when some `StringEncoding α Symbol` exists.
This is a property, the specific choice of encoding is *not*
part of the typeclass and must be supplied separately when it matters.
-/
class StringEncodable (α : Type) (Symbol : Type) [Fintype Symbol] : Prop where
  /-- An encoding of `α` exists. -/
  nonempty_encoding : Nonempty (StringEncoding α Symbol)

/-- Promote a concrete `StringEncoding` to the existence property `StringEncodable`. -/
theorem StringEncodable.of_encoding {α : Type} {Symbol : Type} [Fintype Symbol]
    (e : StringEncoding α Symbol) : StringEncodable α Symbol :=
  ⟨⟨e⟩⟩

namespace StringEncoding

/-! ## Generic trivial encoding -/

/--
The trivial identity encoding for `List Symbol`. Compatible with machines
that already operate directly on tape strings.
-/
def listSymbol : StringEncoding (List Symbol) Symbol where
  encode := id
  decode := some
  decode_encode_eq _ := rfl

instance : StringEncodable (List Symbol) Symbol := .of_encoding listSymbol

/-! ## Basic encodings over the `Bool` alphabet -/

/-- Single-bit encoding of `Bool`: `b ↦ [b]`. -/
def bool : StringEncoding Bool Bool where
  encode b := [b]
  decode
    | [b] => some b
    | _ => none
  decode_encode_eq _ := rfl

instance : StringEncodable Bool Bool := .of_encoding bool

/--
Unary encoding of `Nat` over the `Bool` alphabet:
`n ↦ replicate n true ++ [false]`. The trailing `false` makes the encoding
self-delimiting — a decoder can locate the end of the code without an
external length field. This is what makes `natUnaryPair` below work.
-/
def natUnary : StringEncoding Nat Bool where
  encode n := List.replicate n true ++ [false]
  decode l := some (l.takeWhile id).length
  decode_encode_eq n := by
    induction n with
    | zero => rfl
    | succ k _ => simp [List.replicate_succ]

/-! ### Binary encoding of `Nat` -/

/-- Least significant bit first binary encoder for `Nat`, used by `natBinary`. -/
def encodeBinaryNat : Nat → List Bool
  | 0 => []
  | n+1 =>
    have : (n+1) / 2 < n+1 := Nat.div_lt_self (Nat.succ_pos n) (by omega)
    decide ((n+1) % 2 = 1) :: encodeBinaryNat ((n+1) / 2)

/-- Least significant bit first binary decoder for `Nat`, used by `natBinary`. -/
def decodeBinaryNat : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * decodeBinaryNat bs

lemma decodeBinaryNat_encodeBinaryNat (n : Nat) :
    decodeBinaryNat (encodeBinaryNat n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => rw [encodeBinaryNat, decodeBinaryNat]
    | k+1 =>
      have hlt : (k+1) / 2 < k+1 := Nat.div_lt_self (Nat.succ_pos k) (by omega)
      rw [encodeBinaryNat, decodeBinaryNat, ih ((k+1) / 2) hlt]
      by_cases h : (k+1) % 2 = 1
      · simp [h]; omega
      · simp [h]; omega

/--
Least significant bit first binary encoding of `Nat` over the `Bool` alphabet.
-/
def natBinary : StringEncoding Nat Bool where
  encode := encodeBinaryNat
  decode l := some (decodeBinaryNat l)
  decode_encode_eq n := by simp [decodeBinaryNat_encodeBinaryNat]

instance : StringEncodable Nat Bool := .of_encoding natUnary

/-! ## Derived / composite encodings -/

/--
Tagged encoding of `Option α`: prefix `false` for `none`, prefix `true` for
`some a` followed by `e.encode a`. Parameterized by the underlying encoding
`e` — different choices of `e` yield different `Option`-encodings.
-/
def option {α : Type} (e : StringEncoding α Bool) : StringEncoding (Option α) Bool where
  encode
    | .none => [false]
    | .some a => true :: e.encode a
  decode
    | [] => none
    | false :: _ => some none
    | true :: rest => (e.decode rest).map some
  decode_encode_eq
    | .none => rfl
    | .some a => by
        change Option.map some (e.decode (e.encode a)) = some (some a)
        rw [e.decode_encode_eq]
        rfl

instance {α : Type} [h : StringEncodable α Bool] : StringEncodable (Option α) Bool := by
  obtain ⟨e⟩ := h.nonempty_encoding
  exact .of_encoding (option e)

/-! ## Encoding of `Nat × Nat` -/

lemma takeWhile_id_encode_natUnary_append (a : Nat) (rest : List Bool) :
    (List.replicate a true ++ false :: rest).takeWhile id = List.replicate a true := by
  induction a with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

lemma dropWhile_id_encode_natUnary_append (a : Nat) (rest : List Bool) :
    (List.replicate a true ++ false :: rest).dropWhile id = false :: rest := by
  induction a with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/--
Encoding of `Nat × Nat` as the concatenation of two unary `Nat`-encodings.
The canonical illustration of why self-delimiting codes matter: the decoder
splits the flat list at the first `false` without any auxiliary length field.
-/
def natUnaryPair : StringEncoding (Nat × Nat) Bool where
  encode := fun ⟨a, b⟩ => natUnary.encode a ++ natUnary.encode b
  decode l :=
    let first := (l.takeWhile id).length
    match l.dropWhile id with
    | [] => none
    | _ :: rest => some (first, (rest.takeWhile id).length)
  decode_encode_eq := by
    rintro ⟨a, b⟩
    have hencode : natUnary.encode a ++ natUnary.encode b =
        List.replicate a true ++ false :: (List.replicate b true ++ [false]) := by
      change (List.replicate a true ++ [false]) ++ (List.replicate b true ++ [false]) = _
      simp
    have htake_b : (List.replicate b true ++ [false]).takeWhile id = List.replicate b true := by
      simp [takeWhile_id_encode_natUnary_append b []]
    simp only [hencode, takeWhile_id_encode_natUnary_append, dropWhile_id_encode_natUnary_append,
      htake_b, List.length_replicate]

instance : StringEncodable (Nat × Nat) Bool := .of_encoding natUnaryPair

end StringEncoding

end Encodable
