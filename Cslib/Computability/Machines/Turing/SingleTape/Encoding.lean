/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/

module

public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-!
# Tape Encodings for Single-Tape Turing Machines

This file defines a typeclass framework for encoding arbitrary types onto single-tape Turing
machine alphabets, together with typed time-bounded and polynomial-time computability.

## Main Declarations

* `TapeEncodable α Symbol`: typeclass providing `encode : α → List Symbol` and partial inverse
  `decode : List Symbol → Option α` satisfying `decode (encode a) = some a`.
* `TapeEncodable.encode_injective`, `TapeEncodable.toEmbedding`, `TapeEncodable.ofEquiv`:
  injectivity of encoding, bundled embedding `α ↪ List Symbol`, and transport along equivalences.
* `PrefixTapeEncodable α Symbol`: extension of `TapeEncodable` for self-delimiting (prefix-free)
  encodings supporting stream prefix decoding `decodePrefix`.
* `bitStuff`, `bitUnstuff`: self-delimiting bit-stuffing encoding on `List Bool` with linear length
  overhead `2 * bs.length + 1`, powering the general product instance `TapeEncodable (α × β) Bool`.
* Concrete `TapeEncodable` instances for `List Symbol`, `PUnit`/`Unit`, `Bool`, `ℕ`, `Fin n`,
  `Option α`, `α ⊕ β`, and `α × β`.
* `TypedTimeComputable f` and `TypedPolyTimeComputable f`: time-bounded and polynomial-time
  computability of functions `f : α → β` between `TapeEncodable` types, closed under identity
  (`id`) and composition (`comp`).
-/

@[expose] public section

open Relation

namespace Cslib.Turing

universe u v w

/-!
## `TapeEncodable` Typeclass and Core Lemmas
-/

/-- A typeclass for encoding values of type `α` as lists of symbols over a tape alphabet `Symbol`,
equipped with a partial inverse `decode`. -/
class TapeEncodable (α : Type u) (Symbol : Type v) where
  /-- Encode a value of type `α` as a list of tape symbols. -/
  encode : α → List Symbol
  /-- Attempt to decode a list of tape symbols back into a value of type `α`. -/
  decode : List Symbol → Option α
  /-- Decoding the encoding of any value recovers the original value. -/
  decode_encode : ∀ a : α, decode (encode a) = some a

attribute [simp, scoped grind =] TapeEncodable.decode_encode

namespace TapeEncodable

variable {α : Type u} {β : Type w} {Symbol : Type v}

/-- `TapeEncodable.encode` is injective because `decode` is a left inverse. -/
theorem encode_injective [TapeEncodable α Symbol] :
    Function.Injective (encode (α := α) (Symbol := Symbol)) := by
  intro a b h
  have hdec := congrArg (decode (α := α) (Symbol := Symbol)) h
  simpa using hdec

/-- Two values have equal tape encodings if and only if they are equal. -/
@[simp]
theorem encode_inj [TapeEncodable α Symbol] {a b : α} :
    encode (Symbol := Symbol) a = encode (Symbol := Symbol) b ↔ a = b :=
  (encode_injective (α := α) (Symbol := Symbol)).eq_iff

/-- Bundle `TapeEncodable.encode` as an injective embedding `α ↪ List Symbol`. -/
def toEmbedding (α : Type u) (Symbol : Type v) [TapeEncodable α Symbol] : α ↪ List Symbol :=
  ⟨encode, encode_injective⟩

@[simp]
theorem toEmbedding_apply [TapeEncodable α Symbol] (a : α) :
    toEmbedding α Symbol a = encode a :=
  rfl

/-- Transport a `TapeEncodable β Symbol` instance along a function `f : α → β` with a partial left
inverse `finv : β → Option α`. -/
@[instance_reducible]
def ofLeftInjection [TapeEncodable β Symbol] (f : α → β) (finv : β → Option α)
    (linv : ∀ a, finv (f a) = some a) : TapeEncodable α Symbol where
  encode a := encode (Symbol := Symbol) (f a)
  decode s := (decode (α := β) (Symbol := Symbol) s).bind finv
  decode_encode a := by simp [linv]

/-- Transport a `TapeEncodable β Symbol` instance along a function `f : α → β` with a total left
inverse `finv : β → α`. -/
@[instance_reducible]
def ofLeftInverse [TapeEncodable β Symbol] (f : α → β) (finv : β → α)
    (linv : ∀ a, finv (f a) = a) : TapeEncodable α Symbol where
  encode a := encode (Symbol := Symbol) (f a)
  decode s := (decode (α := β) (Symbol := Symbol) s).map finv
  decode_encode a := by simp [linv]

/-- Transport a `TapeEncodable β Symbol` instance across an equivalence `e : α ≃ β`. -/
@[instance_reducible]
def ofEquiv [TapeEncodable β Symbol] (e : α ≃ β) : TapeEncodable α Symbol :=
  ofLeftInverse e e.symm e.left_inv

theorem encode_ofEquiv [TapeEncodable β Symbol] (e : α ≃ β) (a : α) :
    @encode α Symbol (ofEquiv e) a = encode (Symbol := Symbol) (e a) :=
  rfl

theorem decode_ofEquiv [TapeEncodable β Symbol] (e : α ≃ β) (s : List Symbol) :
    @decode α Symbol (ofEquiv e) s = (decode (α := β) (Symbol := Symbol) s).map e.symm :=
  rfl

end TapeEncodable

open TapeEncodable

/-!
## Self-Delimiting (`PrefixTapeEncodable`) Encodings
-/

/-- A self-delimiting (prefix-free) tape encoding, supporting stream prefix decoding that recovers
both the encoded value and any unconsumed trailing symbols. -/
class PrefixTapeEncodable (α : Type u) (Symbol : Type v) extends TapeEncodable α Symbol where
  /-- Parse an encoded value from the front of a symbol list, returning the decoded value and the
  remaining unconsumed suffix. -/
  decodePrefix : List Symbol → Option (α × List Symbol)
  /-- Prefix-decoding `encode a ++ rest` recovers `(a, rest)`. -/
  decodePrefix_encode_append :
    ∀ (a : α) (rest : List Symbol), decodePrefix (encode a ++ rest) = some (a, rest)

attribute [simp, scoped grind =] PrefixTapeEncodable.decodePrefix_encode_append

namespace PrefixTapeEncodable

variable {α : Type u} {β : Type w} {Symbol : Type v}

@[simp]
theorem decodePrefix_encode [PrefixTapeEncodable α Symbol] (a : α) :
    decodePrefix (Symbol := Symbol) (encode (Symbol := Symbol) a) = some (a, []) := by
  simpa using decodePrefix_encode_append (Symbol := Symbol) a []

/-- Concatenating a prefix-free encoding with a suffix is injective in both arguments. -/
theorem encode_append_inj [PrefixTapeEncodable α Symbol] {a₁ a₂ : α} {l₁ l₂ : List Symbol} :
    encode (Symbol := Symbol) a₁ ++ l₁ = encode (Symbol := Symbol) a₂ ++ l₂ ↔
      a₁ = a₂ ∧ l₁ = l₂ := by
  constructor
  · intro h
    have hdec := congrArg (decodePrefix (α := α) (Symbol := Symbol)) h
    simpa using hdec
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Prefix-freeness: `encode a₁` is a list prefix of `encode a₂` if and only if `a₁ = a₂`. -/
theorem isPrefix_encode_iff [PrefixTapeEncodable α Symbol] {a₁ a₂ : α} :
    encode (Symbol := Symbol) a₁ <+: encode (Symbol := Symbol) a₂ ↔ a₁ = a₂ := by
  constructor
  · rintro ⟨t, ht⟩
    have ht' : encode (Symbol := Symbol) a₁ ++ t = encode (Symbol := Symbol) a₂ ++ [] := by
      simpa using ht
    exact (encode_append_inj.mp ht').1
  · rintro rfl
    exact List.prefix_rfl

/-- Concatenation product of two `PrefixTapeEncodable` types over any alphabet `Symbol`. -/
@[instance_reducible]
def prod [PrefixTapeEncodable α Symbol] [PrefixTapeEncodable β Symbol] :
    PrefixTapeEncodable (α × β) Symbol where
  encode p := encode (Symbol := Symbol) p.1 ++ encode (Symbol := Symbol) p.2
  decode s :=
    match decodePrefix (α := α) (Symbol := Symbol) s with
    | some (a, rest) => (decode (α := β) (Symbol := Symbol) rest).map (Prod.mk a)
    | none => none
  decode_encode p := by simp
  decodePrefix s :=
    match decodePrefix (α := α) (Symbol := Symbol) s with
    | some (a, rest) =>
      match decodePrefix (α := β) (Symbol := Symbol) rest with
      | some (b, rest') => some ((a, b), rest')
      | none => none
    | none => none
  decodePrefix_encode_append p rest := by
    simp only [List.append_assoc, decodePrefix_encode_append]

end PrefixTapeEncodable

/-!
## Concrete `TapeEncodable` and `PrefixTapeEncodable` Instances
-/

section Instances

/-- Identity tape encoding for `List Symbol` over `Symbol`. -/
instance instTapeEncodableList {Symbol : Type v} : TapeEncodable (List Symbol) Symbol where
  encode l := l
  decode l := some l
  decode_encode _ := rfl

theorem encode_list {Symbol : Type v} (l : List Symbol) :
    encode (Symbol := Symbol) l = l :=
  rfl

theorem decode_list {Symbol : Type v} (l : List Symbol) :
    decode (α := List Symbol) l = some l :=
  rfl

@[simp]
theorem encode_list_length {Symbol : Type v} (l : List Symbol) :
    (encode (Symbol := Symbol) l).length = l.length :=
  rfl

/-- Tape encoding of `PUnit` (including `Unit`) over `Bool` as the empty list `[]`. -/
instance instTapeEncodablePUnit : TapeEncodable PUnit.{u + 1} Bool where
  encode _ := []
  decode
    | [] => some PUnit.unit
    | _ :: _ => none
  decode_encode _ := rfl

/-- Self-delimiting tape encoding of `PUnit` (including `Unit`) over `Bool`. -/
instance instPrefixTapeEncodablePUnit : PrefixTapeEncodable PUnit.{u + 1} Bool where
  toTapeEncodable := instTapeEncodablePUnit
  decodePrefix rest := some (PUnit.unit, rest)
  decodePrefix_encode_append _ _ := rfl

theorem encode_punit (x : PUnit.{u + 1}) : encode (Symbol := Bool) x = [] := rfl

theorem encode_unit (x : Unit) : encode (Symbol := Bool) x = [] := rfl

@[simp]
theorem encode_punit_length (x : PUnit.{u + 1}) : (encode (Symbol := Bool) x).length = 0 := rfl

/-- Single-symbol tape encoding of `Bool` over `Bool`. -/
instance instTapeEncodableBool : TapeEncodable Bool Bool where
  encode b := [b]
  decode
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/-- Self-delimiting single-symbol tape encoding of `Bool` over `Bool`. -/
instance instPrefixTapeEncodableBool : PrefixTapeEncodable Bool Bool where
  toTapeEncodable := instTapeEncodableBool
  decodePrefix
    | b :: rest => some (b, rest)
    | [] => none
  decodePrefix_encode_append _ _ := rfl

theorem encode_bool (b : Bool) : encode (Symbol := Bool) b = [b] := rfl

@[simp]
theorem encode_bool_length (b : Bool) : (encode (Symbol := Bool) b).length = 1 := rfl

/-- Unary tape encoding of `ℕ` over `Bool`, mapping `n` to `List.replicate n true`. -/
instance instTapeEncodableNat : TapeEncodable ℕ Bool where
  encode n := List.replicate n true
  decode l := if l.all (· == true) then some l.length else none
  decode_encode n := by simp

theorem encode_nat (n : ℕ) : encode (Symbol := Bool) n = List.replicate n true := rfl

@[simp]
theorem encode_nat_length (n : ℕ) : (encode (Symbol := Bool) n).length = n :=
  List.length_replicate

/-- Unary tape encoding of `Fin n` over `Bool`. -/
instance instTapeEncodableFin (n : ℕ) : TapeEncodable (Fin n) Bool where
  encode i := List.replicate i.val true
  decode l := if h : l.all (· == true) ∧ l.length < n then some ⟨l.length, h.2⟩ else none
  decode_encode i := by simp [i.isLt]

theorem encode_fin {n : ℕ} (i : Fin n) :
    encode (Symbol := Bool) i = List.replicate i.val true :=
  rfl

@[simp]
theorem encode_fin_length {n : ℕ} (i : Fin n) : (encode (Symbol := Bool) i).length = i.val :=
  List.length_replicate

/-- Tape encoding of `Option α` over `Bool`: `none` maps to `[]` and `some a` maps to
`true :: encode a`. -/
instance instTapeEncodableOption {α : Type u} [TapeEncodable α Bool] :
    TapeEncodable (Option α) Bool where
  encode
    | none => []
    | some a => true :: encode (Symbol := Bool) a
  decode
    | [] => some none
    | true :: xs => (decode (α := α) (Symbol := Bool) xs).map some
    | false :: _ => none
  decode_encode
    | none => rfl
    | some _ => by simp

theorem encode_none {α : Type u} [TapeEncodable α Bool] :
    encode (Symbol := Bool) (none : Option α) = [] :=
  rfl

theorem encode_some {α : Type u} [TapeEncodable α Bool] (a : α) :
    encode (Symbol := Bool) (some a) = true :: encode (Symbol := Bool) a :=
  rfl

@[simp]
theorem encode_none_length {α : Type u} [TapeEncodable α Bool] :
    (encode (Symbol := Bool) (none : Option α)).length = 0 :=
  rfl

@[simp]
theorem encode_some_length {α : Type u} [TapeEncodable α Bool] (a : α) :
    (encode (Symbol := Bool) (some a)).length = (encode (Symbol := Bool) a).length + 1 :=
  rfl

/-- Tagged tape encoding of `α ⊕ β` over `Bool`: `Sum.inl a` is prefixed with `false` and
`Sum.inr b` is prefixed with `true`. -/
instance instTapeEncodableSum {α : Type u} {β : Type v}
    [TapeEncodable α Bool] [TapeEncodable β Bool] :
    TapeEncodable (α ⊕ β) Bool where
  encode
    | .inl a => false :: encode (Symbol := Bool) a
    | .inr b => true :: encode (Symbol := Bool) b
  decode
    | false :: xs => (decode (α := α) (Symbol := Bool) xs).map Sum.inl
    | true :: xs => (decode (α := β) (Symbol := Bool) xs).map Sum.inr
    | [] => none
  decode_encode
    | .inl _ => by simp
    | .inr _ => by simp

theorem encode_inl {α : Type u} {β : Type v} [TapeEncodable α Bool] [TapeEncodable β Bool]
    (a : α) :
    encode (Symbol := Bool) (Sum.inl a : α ⊕ β) = false :: encode (Symbol := Bool) a :=
  rfl

theorem encode_inr {α : Type u} {β : Type v} [TapeEncodable α Bool] [TapeEncodable β Bool]
    (b : β) :
    encode (Symbol := Bool) (Sum.inr b : α ⊕ β) = true :: encode (Symbol := Bool) b :=
  rfl

/-- Self-delimiting tagged tape encoding of `α ⊕ β` over `Bool`. -/
instance instPrefixTapeEncodableSum {α : Type u} {β : Type v}
    [PrefixTapeEncodable α Bool] [PrefixTapeEncodable β Bool] :
    PrefixTapeEncodable (α ⊕ β) Bool where
  toTapeEncodable := instTapeEncodableSum
  decodePrefix
    | false :: xs =>
      (PrefixTapeEncodable.decodePrefix (α := α) (Symbol := Bool) xs).map fun (a, rest) =>
        (.inl a, rest)
    | true :: xs =>
      (PrefixTapeEncodable.decodePrefix (α := β) (Symbol := Bool) xs).map fun (b, rest) =>
        (.inr b, rest)
    | [] => none
  decodePrefix_encode_append
    | .inl _, _ => by simp [encode_inl]
    | .inr _, _ => by simp [encode_inr]

@[simp]
theorem encode_inl_length {α : Type u} {β : Type v}
    [TapeEncodable α Bool] [TapeEncodable β Bool] (a : α) :
    (encode (Symbol := Bool) (Sum.inl a : α ⊕ β)).length =
      (encode (Symbol := Bool) a).length + 1 :=
  rfl

@[simp]
theorem encode_inr_length {α : Type u} {β : Type v}
    [TapeEncodable α Bool] [TapeEncodable β Bool] (b : β) :
    (encode (Symbol := Bool) (Sum.inr b : α ⊕ β)).length =
      (encode (Symbol := Bool) b).length + 1 :=
  rfl

/-!
### Self-Delimiting Bit-Stuffing and Product Encoding
-/

/-- Encode a list of booleans in self-delimiting form by prefixing each bit `b` with `true` and
terminating with `false`. -/
def bitStuff : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: bitStuff bs

/-- Decode a `bitStuff`-encoded prefix from a boolean list, returning the decoded list and the
remaining unconsumed suffix. -/
def bitUnstuff : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest =>
    match bitUnstuff rest with
    | some (bs, tail) => some (b :: bs, tail)
    | none => none
  | _ => none

/-- `bitStuff bs` has exact linear length `2 * bs.length + 1`. -/
@[simp]
theorem length_bitStuff (bs : List Bool) : (bitStuff bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons _ bs ih =>
    simp only [bitStuff, List.length_cons, ih]
    omega

/-- `bitUnstuff` recovers `bs` and any trailing suffix `rest` from `bitStuff bs ++ rest`. -/
@[simp, scoped grind =]
theorem bitUnstuff_bitStuff_append (bs rest : List Bool) :
    bitUnstuff (bitStuff bs ++ rest) = some (bs, rest) := by
  induction bs with
  | nil => rfl
  | cons _ _ ih => simp only [bitStuff, List.cons_append, bitUnstuff, ih]

@[simp]
theorem bitUnstuff_bitStuff (bs : List Bool) : bitUnstuff (bitStuff bs) = some (bs, []) := by
  simpa using bitUnstuff_bitStuff_append bs []

/-- General product encoding over `Bool` for arbitrary `TapeEncodable` types `α` and `β`,
using `bitStuff` to self-delimit `encode a` before `encode b`. -/
instance instTapeEncodableProd {α : Type u} {β : Type v}
    [TapeEncodable α Bool] [TapeEncodable β Bool] :
    TapeEncodable (α × β) Bool where
  encode p := bitStuff (encode (Symbol := Bool) p.1) ++ encode (Symbol := Bool) p.2
  decode s :=
    match bitUnstuff s with
    | some (sa, sb) =>
      match decode (α := α) (Symbol := Bool) sa, decode (α := β) (Symbol := Bool) sb with
      | some a, some b => some (a, b)
      | _, _ => none
    | none => none
  decode_encode p := by simp

/-- When `β` is `PrefixTapeEncodable` over `Bool`, the `bitStuff` product encoding of `α × β` is
also `PrefixTapeEncodable` (for any `TapeEncodable α Bool`). -/
instance instPrefixTapeEncodableProd {α : Type u} {β : Type v}
    [TapeEncodable α Bool] [PrefixTapeEncodable β Bool] :
    PrefixTapeEncodable (α × β) Bool where
  toTapeEncodable := instTapeEncodableProd
  decodePrefix s :=
    match bitUnstuff s with
    | some (sa, rest) =>
      match decode (α := α) (Symbol := Bool) sa,
          PrefixTapeEncodable.decodePrefix (α := β) (Symbol := Bool) rest with
      | some a, some (b, tail) => some ((a, b), tail)
      | _, _ => none
    | none => none
  decodePrefix_encode_append p rest := by
    change (match bitUnstuff ((bitStuff (encode (Symbol := Bool) p.1) ++
        encode (Symbol := Bool) p.2) ++ rest) with
      | some (sa, rest) =>
        match decode (α := α) (Symbol := Bool) sa,
            PrefixTapeEncodable.decodePrefix (α := β) (Symbol := Bool) rest with
        | some a, some (b, tail) => some ((a, b), tail)
        | _, _ => none
      | none => none) = some (p, rest)
    simp only [List.append_assoc, bitUnstuff_bitStuff_append, decode_encode,
      PrefixTapeEncodable.decodePrefix_encode_append]

theorem encode_prod {α : Type u} {β : Type v} [TapeEncodable α Bool] [TapeEncodable β Bool]
    (a : α) (b : β) :
    encode (Symbol := Bool) (a, b) =
      bitStuff (encode (Symbol := Bool) a) ++ encode (Symbol := Bool) b :=
  rfl

/-- Exact linear length formula for the product tape encoding over `Bool`. -/
@[simp]
theorem encode_prod_length {α : Type u} {β : Type v}
    [TapeEncodable α Bool] [TapeEncodable β Bool] (a : α) (b : β) :
    (encode (Symbol := Bool) (a, b)).length =
      2 * (encode (Symbol := Bool) a).length + 1 + (encode (Symbol := Bool) b).length := by
  simp [encode_prod]

end Instances

/-!
## Typed Time-Bounded and Polynomial-Time Computability
-/

section TypedComputability

open SingleTapeTM Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {α : Type u} {β : Type v} {γ : Type w}

/-- A single-tape Turing machine together with a time bound witnessing that `f : α → β` is
computed on encoded inputs within `timeBound (encode a).length` steps. -/
structure TypedTimeComputable [TapeEncodable α Symbol] [TapeEncodable β Symbol] (f : α → β) where
  /-- The underlying single-tape Turing machine. -/
  tm : SingleTapeTM Symbol
  /-- Upper bound on the step count as a function of the encoded input length. -/
  timeBound : ℕ → ℕ
  /-- Proof that on every `a : α`, `tm` outputs `encode (f a)` from `encode a` within
  `timeBound (encode a).length` steps. -/
  outputsFunInTime (a : α) :
    tm.OutputsWithinTime (encode (Symbol := Symbol) a) (encode (Symbol := Symbol) (f a))
      (timeBound (encode (Symbol := Symbol) a).length)

/-- The identity function on any `TapeEncodable` type is computable in constant time `1`. -/
def TypedTimeComputable.id [TapeEncodable α Symbol] :
    TypedTimeComputable (Symbol := Symbol) (id : α → α) where
  tm := idComputer
  timeBound _ := 1
  outputsFunInTime a := TimeComputable.id.outputsFunInTime (encode (Symbol := Symbol) a)

/-- Lift a raw list computation `TimeComputable g` to `TypedTimeComputable f` when `g` agrees with
`f` on all encodings. -/
def TypedTimeComputable.ofTimeComputable [TapeEncodable α Symbol] [TapeEncodable β Symbol]
    {f : α → β} {g : List Symbol → List Symbol} (hg : TimeComputable g)
    (hfg : ∀ a : α, g (encode (Symbol := Symbol) a) = encode (Symbol := Symbol) (f a)) :
    TypedTimeComputable (Symbol := Symbol) f where
  tm := hg.tm
  timeBound := hg.timeBound
  outputsFunInTime a := hfg a ▸ hg.outputsFunInTime (encode (Symbol := Symbol) a)

/-- View a raw `TimeComputable f` on `List Symbol` as a `TypedTimeComputable f` via the identity
list encoding. -/
def TypedTimeComputable.ofList {f : List Symbol → List Symbol} (hf : TimeComputable f) :
    TypedTimeComputable (Symbol := Symbol) f :=
  ofTimeComputable hf fun _ => rfl

/-- Extract a raw `TimeComputable f` from a `TypedTimeComputable f` on `List Symbol`. -/
def TypedTimeComputable.toTimeComputable {f : List Symbol → List Symbol}
    (hf : TypedTimeComputable (Symbol := Symbol) f) : TimeComputable f where
  tm := hf.tm
  timeBound := hf.timeBound
  outputsFunInTime := hf.outputsFunInTime

/-- Replace the time bound of a `TypedTimeComputable` witness with a monotone bound (`partialSups`)
without modifying the underlying Turing machine. -/
def TypedTimeComputable.withMonotoneBound [TapeEncodable α Symbol] [TapeEncodable β Symbol]
    {f : α → β} (hf : TypedTimeComputable (Symbol := Symbol) f) :
    TypedTimeComputable (Symbol := Symbol) f where
  tm := hf.tm
  timeBound := partialSups hf.timeBound
  outputsFunInTime a :=
    RelatesWithinSteps.mono (le_partialSups hf.timeBound _) (hf.outputsFunInTime a)

lemma TypedTimeComputable.withMonotoneBound_timeBound_monotone
    [TapeEncodable α Symbol] [TapeEncodable β Symbol] {f : α → β}
    (hf : TypedTimeComputable (Symbol := Symbol) f) :
    Monotone hf.withMonotoneBound.timeBound :=
  (partialSups hf.timeBound).monotone

/-- Compose two `TypedTimeComputable` functions via `hf.tm ∘ₜₘ hg.tm`, assuming the second
machine's time bound is monotone. -/
def TypedTimeComputable.comp
    [TapeEncodable α Symbol] [TapeEncodable β Symbol] [TapeEncodable γ Symbol]
    {f : α → β} {g : β → γ}
    (hf : TypedTimeComputable (Symbol := Symbol) f)
    (hg : TypedTimeComputable (Symbol := Symbol) g)
    (h_mono : Monotone hg.timeBound) :
    TypedTimeComputable (Symbol := Symbol) (g ∘ f) where
  tm := hf.tm ∘ₜₘ hg.tm
  timeBound l := hf.timeBound l + hg.timeBound (max 1 l + hf.timeBound l)
  outputsFunInTime a := by
    have hcomp := OutputsWithinTime.comp (hf.outputsFunInTime a) (hg.outputsFunInTime (f a))
    refine RelatesWithinSteps.mono ?_ hcomp
    refine Nat.add_le_add_left ?_ _
    exact h_mono (output_length_le_input_length_add_time hf.tm _ _ _ (hf.outputsFunInTime a))

/-- A polynomial-time computable function `f : α → β` between `TapeEncodable` types over `Symbol`.
-/
structure TypedPolyTimeComputable [TapeEncodable α Symbol] [TapeEncodable β Symbol] (f : α → β)
    extends TypedTimeComputable (Symbol := Symbol) f where
  /-- Polynomial upper bound on the runtime. -/
  poly : Polynomial ℕ
  /-- Proof that `timeBound n` is bounded by `poly.eval n` for every encoded input length `n`. -/
  bounds : ∀ n, timeBound n ≤ poly.eval n

/-- The identity function on any `TapeEncodable` type is computable in polynomial time. -/
noncomputable def TypedPolyTimeComputable.id [TapeEncodable α Symbol] :
    TypedPolyTimeComputable (Symbol := Symbol) (id : α → α) where
  toTypedTimeComputable := TypedTimeComputable.id
  poly := 1
  bounds _ := by simp [TypedTimeComputable.id]

/-- Lift a raw `PolyTimeComputable g` to `TypedPolyTimeComputable f` when `g` agrees with `f` on
all encodings. -/
noncomputable def TypedPolyTimeComputable.ofPolyTimeComputable
    [TapeEncodable α Symbol] [TapeEncodable β Symbol]
    {f : α → β} {g : List Symbol → List Symbol} (hg : PolyTimeComputable g)
    (hfg : ∀ a : α, g (encode (Symbol := Symbol) a) = encode (Symbol := Symbol) (f a)) :
    TypedPolyTimeComputable (Symbol := Symbol) f where
  toTypedTimeComputable := TypedTimeComputable.ofTimeComputable hg.toTimeComputable hfg
  poly := hg.poly
  bounds := hg.bounds

/-- Replace the time bound of a `TypedPolyTimeComputable` witness with a monotone bound while
preserving the polynomial bound. -/
noncomputable def TypedPolyTimeComputable.withMonotoneBound
    [TapeEncodable α Symbol] [TapeEncodable β Symbol] {f : α → β}
    (hf : TypedPolyTimeComputable (Symbol := Symbol) f) :
    TypedPolyTimeComputable (Symbol := Symbol) f where
  toTypedTimeComputable := hf.toTypedTimeComputable.withMonotoneBound
  poly := hf.poly
  bounds _ := partialSups_le _ _ _ fun k hk => (hf.bounds k).trans (hf.poly.monotone_eval hk)

/-- The composition of two `TypedPolyTimeComputable` functions is polynomial-time computable. -/
noncomputable def TypedPolyTimeComputable.comp
    [TapeEncodable α Symbol] [TapeEncodable β Symbol] [TapeEncodable γ Symbol]
    {f : α → β} {g : β → γ}
    (hf : TypedPolyTimeComputable (Symbol := Symbol) f)
    (hg : TypedPolyTimeComputable (Symbol := Symbol) g) :
    TypedPolyTimeComputable (Symbol := Symbol) (g ∘ f) where
  toTypedTimeComputable :=
    TypedTimeComputable.comp hf.toTypedTimeComputable
      hg.withMonotoneBound.toTypedTimeComputable
      hg.toTypedTimeComputable.withMonotoneBound_timeBound_monotone
  poly := hf.poly + hg.poly.comp (1 + X + hf.poly)
  bounds n := by
    simp only [TypedTimeComputable.comp, eval_add, eval_comp, eval_X, eval_one]
    apply add_le_add
    · exact hf.bounds n
    · exact (hg.toTypedTimeComputable.withMonotoneBound_timeBound_monotone
        (add_le_add (by omega) (hf.bounds n))).trans (hg.withMonotoneBound.bounds _)

end TypedComputability

end Cslib.Turing
