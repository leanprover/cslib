/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.Defs
public import Cslib.Crypto.Protocols.PerfectSecrecy.Internal.PerfectSecrecy

@[expose] public section

/-!
# Perfect Secrecy

Characterisation theorems for perfect secrecy following
[KatzLindell2020], Chapter 2.

## Main results

- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_iff_ciphertextIndist`:
  ciphertext indistinguishability characterization ([KatzLindell2020], Lemma 2.5)
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_keySpace_ge`:
  Shannon's theorem, `|K| ≥ |M|` ([KatzLindell2020], Theorem 2.12)

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

namespace Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme

universe u
variable {M K C : Type u}

/-- A scheme is perfectly secret iff the ciphertext distribution is
independent of the plaintext ([KatzLindell2020], Lemma 2.5). -/
theorem perfectlySecret_iff_ciphertextIndist (scheme : EncScheme M K C) :
    scheme.PerfectlySecret ↔ scheme.CiphertextIndist :=
  ⟨PerfectSecrecy.ciphertextIndist_of_perfectlySecret scheme,
   PerfectSecrecy.perfectlySecret_of_ciphertextIndist scheme⟩

/-- Perfect secrecy requires `|K| ≥ |M|`
([KatzLindell2020], Theorem 2.12). -/
theorem perfectlySecret_keySpace_ge [Finite K]
    (scheme : EncScheme M K C) (h : scheme.PerfectlySecret) :
    Nat.card K ≥ Nat.card M :=
  PerfectSecrecy.shannonKeySpace scheme h

end Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme
