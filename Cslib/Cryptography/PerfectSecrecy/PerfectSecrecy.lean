/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.PerfectSecrecy.PerfectSecrecy.Defs
public import Cslib.Cryptography.PerfectSecrecy.Internal.PerfectSecrecy

@[expose] public section

/-!
# Perfect Secrecy

Characterisation theorems for perfect secrecy following
[KatzLindell2021], Chapter 2.

## Main results

- `Cslib.Cryptography.PerfectSecrecy.EncScheme.perfectlySecret_iff_ciphertextIndist`:
  ciphertext indistinguishability characterization ([KatzLindell2021], Lemma 2.5)
- `Cslib.Cryptography.PerfectSecrecy.EncScheme.perfectlySecret_keySpace_ge`:
  Shannon's theorem, `|K| ≥ |M|` ([KatzLindell2021], Theorem 2.12)

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2021]
-/

namespace Cslib.Cryptography.PerfectSecrecy.EncScheme

universe u
variable {M K C : Type u}

/-- A scheme is perfectly secret iff the ciphertext distribution is
independent of the plaintext ([KatzLindell2021], Lemma 2.5). -/
theorem perfectlySecret_iff_ciphertextIndist (scheme : EncScheme M K C) :
    scheme.PerfectlySecret ↔
    ∀ m₀ m₁ : M, scheme.ciphertextDist m₀ = scheme.ciphertextDist m₁ :=
  ⟨PerfectSecrecy.forward scheme, PerfectSecrecy.backward scheme⟩

/-- Perfect secrecy requires `|K| ≥ |M|`
([KatzLindell2021], Theorem 2.12). -/
theorem perfectlySecret_keySpace_ge [Fintype M] [Fintype K]
    (scheme : EncScheme M K C) (h : scheme.PerfectlySecret) :
    Fintype.card K ≥ Fintype.card M :=
  PerfectSecrecy.shannonKeySpace scheme h

end Cslib.Cryptography.PerfectSecrecy.EncScheme
