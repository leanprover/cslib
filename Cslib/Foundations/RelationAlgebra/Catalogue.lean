/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S0N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S0N1
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S0N2
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0

/-!
# Small integral relation algebras

This catalogue defines all 4527 integral relation algebras through five atoms, up to isomorphism,
with the signatures and counts in
[Peter Jipsen's list](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The first 198 entries retain the source's order. The ⟨1, 2, 1⟩ and ⟨1, 4, 0⟩ rows use increasing
canonical cycle masks: the source gives their counts but does not list their individual cycles.
It covers integral algebras only: the identity is a single atom. The general `RelationAlgebra`
class and `Representable` predicate do not impose integrality or finiteness.

The signature `⟨i, j, k⟩` counts identity atoms, symmetric diversity atoms, and pairs of
nonsymmetric atoms. Thus the total atom count is `i + j + 2 * k`.

| Namespace | Signature | Entries | Representable | Nonrepresentable |
|-----------|-----------|---------|---------------|------------------|
| `I1S0N0` | ⟨1, 0, 0⟩ | 1 | 1 | 0 |
| `I1S1N0` | ⟨1, 1, 0⟩ | 2 | 2 | 0 |
| `I1S0N1` | ⟨1, 0, 1⟩ | 3 | 3 | 0 |
| `I1S2N0` | ⟨1, 2, 0⟩ | 7 | 7 | 0 |
| `I1S1N1` | ⟨1, 1, 1⟩ | 37 | 26 | 11 |
| `I1S3N0` | ⟨1, 3, 0⟩ | 65 | 45 | 20 |
| `I1S0N2` | ⟨1, 0, 2⟩ | 83 | — | — |
| `I1S2N1` | ⟨1, 2, 1⟩ | 1316 | — | — |
| `I1S4N0` | ⟨1, 4, 0⟩ | 3013 | — | — |

Each entry has its own module, such as `I1S1N1.Ra08` or `I1S4N0.Ra0001`.
Entry numbering is one-based;
the row's `Model : Fin N → Type` uses zero-based indices. Each row's `classification` states
that an algebra with the given finite signature is isomorphic to exactly one listed model.

The cycle data and operations are concrete. The algebra laws, cycle characterizations, and
classifications have kernel-checked proofs. Representability decisions are supplied for rows
through four atoms; the five-atom rows supply only their classifications. Executable sanity checks
independently audit the smaller cycle tables and distinguish their entries.
Representations may have infinite bases, as required even for some of these finite algebras.
The constructions use finite groups, dense orders, finitely supported sequences, or successive
composition witnesses. Nonrepresentability is certified by finite network obstructions.
-/
