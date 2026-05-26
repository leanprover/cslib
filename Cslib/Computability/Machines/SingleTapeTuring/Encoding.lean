/-
Copyright (c) 2026 Silvère Gangloff. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Silvère Gangloff
-/

import Mathlib.Tactic.Basic

/-!
# Turing Machine Tape Encodings

This file defines the `TapeEncodable` typeclass, which provides a framework
for encoding arbitrary types onto a Turing machine tape. This allows us to
define computability for functions on types other than just `List Symbol`.
-/

namespace Turing

variable {Symbol : Type}

/-- 
A typeclass for types that can be encoded onto a Turing machine tape.
Provides a canonical way to translate back and forth between a type `α` 
and a `List Symbol`, alongside a proof that decoding an encoded value succeeds.
-/
class TapeEncodable (α : Type) (Symbol : Type) where
  /-- Translates the type into a tape-compatible list of symbols -/
  encode : α → List Symbol
  /-- Attempts to parse a list of symbols back into the type -/
  decode : List Symbol → Option α
  /-- Proof that decoding a freshly encoded value yields the original value -/
  decode_encode_eq : ∀ (a : α), decode (encode a) = some a

/-- 
The trivial encoding for `List Symbol` itself. 
This ensures backward compatibility with machines that already operate 
directly on tape strings.
-/
instance : TapeEncodable (List Symbol) Symbol where
  encode := id
  decode := some
  decode_encode_eq _ := rfl

end Turing
