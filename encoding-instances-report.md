# Report: Encoding.lean refactor and example encodings

## Context

PR review feedback from SamuelSchlesinger on the `StringEncodable` typeclass:

> I think it would be nice if we had instances for common types, which I
> understand is hard to do with a generic Symbol. Feels not so useful without
> that.

In parallel, the file `StringEncoding.lean` had been moved from
`Cslib/Computability/Machines/SingleTapeTuring/Encoding.lean` to
`Cslib/Computability/Encoding.lean`, leaving a broken import in
`Machines/SingleTapeTuring/Basic.lean` and an untracked file in the new
location.

After an initial pass adding instances directly to a class-based
`StringEncodable`, the user pointed out a deeper design issue: for Turing
machines you typically want to *commit to a particular encoding* (unary,
binary, …), and the same type can carry several. Bundling encoder/decoder as
typeclass data forces a single canonical choice, which is the wrong shape.

This report documents the cleanup and the refactor.

## Changes

### 1. File location

Kept `StringEncoding.lean` at `Cslib/Computability/Encoding.lean`.

**Why:** `StringEncoding α Symbol` and `StringEncodable α Symbol` are generic
notions with no dependency on Turing-machine specifics. Other machine
models (URM, lambda calculus, etc.) could reasonably consume them. Putting
the file under `Machines/SingleTapeTuring/` was overly narrow; the top
level of `Computability/` reflects its scope correctly.

### 2. Fixed broken imports / module wiring

- `Cslib/Computability/Machines/SingleTapeTuring/Basic.lean` line 12:
  `Cslib.Computability.Turing.Encoding` → `Cslib.Computability.Encoding`.
- `Cslib.lean`: added `public import Cslib.Computability.Encoding` in
  alphabetical position.
- `Cslib/Computability/Encoding.lean`: added the `module` declaration and
  an `@[expose] public section` so it can be `public import`-ed by other
  modules (which `Basic.lean` requires).

### 3. Finiteness of the alphabet

Both `StringEncoding` and `StringEncodable` now carry a `[Fintype Symbol]`
instance argument. Without finiteness the abstraction is vacuous — one can
always take `Symbol = α` and encode `a ↦ [a]`. Using `Fintype` (rather than
the weaker `Finite`) matches the constraint already used by
`SingleTapeTM Symbol [Inhabited Symbol] [Fintype Symbol]`, so an encoding
slots into a Turing machine without an extra hypothesis. Required a new
import: `Mathlib.Data.Fintype.Defs`.

### 4. Design refactor: `StringEncoding` as the primitive notion

Previously `StringEncodable` was a class bundling encoder + decoder +
correctness proof — i.e. data masquerading as a property. This forces a
single canonical encoding per type, which is wrong for computability
because the choice of encoding matters (e.g. unary vs. binary `Nat`).

The new design splits these:

```lean
structure StringEncoding (α : Type) (Symbol : Type) where
  encode : α → List Symbol
  decode : List Symbol → Option α
  decode_encode_eq : ∀ a, decode (encode a) = some a

class StringEncodable (α : Type) (Symbol : Type) : Prop where
  nonempty_encoding : Nonempty (StringEncoding α Symbol)
```

- `StringEncoding α Symbol` is a **value-level** record. A type can carry many
  encodings, named distinctly (`StringEncoding.natUnary`, `StringEncoding.natBinary`,
  …). Code that depends on a specific representation takes a `StringEncoding`
  argument explicitly.

- `StringEncodable α Symbol` is a **`Prop`-valued** typeclass — purely the
  existence claim "some encoding exists". It carries no representation
  choice and so cannot accidentally pick one for you.

- `StringEncodable.of_encoding` promotes any concrete `StringEncoding` to the
  existence property.

### 5. Concrete encodings

All instances live over the `Bool` alphabet (the textbook computability
convention).

#### Trivial / basic

- **`StringEncoding.listSymbol`** — identity encoding of `List Symbol`. Generic
  in `Symbol`; the only one that does not fix the alphabet.

- **`StringEncoding.bool`** — `b ↦ [b]`. Sanity-check level.

- **`StringEncoding.natUnary`** — `n ↦ replicate n true ++ [false]`. The
  trailing `false` makes this **self-delimiting** — a decoder can locate
  the end of the code without an external length field. This is the
  property that makes `StringEncoding.natUnaryPair` (below) work.

- **`StringEncoding.natBinary`** — LSB-first binary encoding via `encodeBinaryNat`
  / `decodeBinaryNat`. Exponentially more compact than `natUnary` but
  *not* self-delimiting, so it cannot be naively concatenated. Correctness
  proved by strong induction. Provided as the second `Nat`-encoding to
  demonstrate that multiple choices coexist as plain values.

#### Composite / derived

- **`StringEncoding.option (e : StringEncoding α Bool) : StringEncoding (Option α) Bool`** —
  tagged with a leading bit. Note this is a *function* on encodings, not
  an instance: different choices of `e` give different `Option`-encodings.
  A `StringEncodable` instance is still derived (because *some* encoding
  exists once we have one for `α`).

- **`StringEncoding.natUnaryPair`** (nontrivial example) — `Nat × Nat` as the
  concatenation of two unary codes. The canonical illustration of why
  self-delimiting codes matter: the decoder splits the flat list at the
  first `false` without any auxiliary length field. Proof factored
  through two lemmas describing how a unary `Nat` encoding interacts with
  any trailing list.

### 6. `StringEncodable` instances

Provided for `List Symbol`, `Bool`, `Nat` (via `natUnary` as the default
witness), `Option α` (given `StringEncodable α Bool`), and `Nat × Nat`.
These only register *existence* — the specific `Nat`-encoding is not
fixed by the instance, and downstream code that cares must take an
explicit `StringEncoding Nat Bool` argument.

## Design choices and trade-offs

- **Public, not private, helpers.** Lean's new module system disallows
  exposing a public definition whose RHS directly aliases a `private`
  helper. The helper functions (`encodeBinaryNat`, `decodeBinaryNat`,
  `takeWhile_id_encode_natUnary_append`, …) are therefore public but
  prefixed and docstring-tagged as implementation support. A
  finer-grained encapsulation could be done with explicit `protected`
  declarations if desired.

- **`Bool` alphabet, not generic.** Useful instances over a fully
  generic `Symbol` require extra structure (separators, etc.) — exactly
  the difficulty the reviewer noted. Committing to `Bool` gives concrete
  examples immediately. A follow-up could add encodings over richer
  alphabets (`Char`, `Fin n`, …) or factor out a "self-delimiting"
  predicate.

- **Two `Nat` encodings, one default witness.** The `StringEncodable`
  instance uses `natUnary`. This is a witness, not a canonical choice —
  any code that depends on the representation should not consult
  `StringEncodable` and should instead take a `StringEncoding Nat Bool`
  argument.

- **Single file, not split.** Encodings were added inline rather than in
  `Encoding/Instances.lean`. The file is still under 200 lines; the
  split would be premature.

## Verification

All three files were checked via the Lean LSP and compile with no errors:

- `Cslib/Computability/Encoding.lean`
- `Cslib/Computability/Machines/SingleTapeTuring/Basic.lean`
- `Cslib.lean`

A full `lake build` was attempted but failed unrelated to the code: the
machine is out of disk space (38 MiB free on the volume, mathlib cache
extraction failing with `No space left on device`). The Lean LSP — which
incrementally compiles in-memory and does not need to write `.olean`
files — confirms the code is well-formed.

No commits were made.
