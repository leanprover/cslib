/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S0N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S0N1
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0

/-!
# Small integral relation algebras

This catalogue defines all 115 entries through four atoms in
[Peter Jipsen's list](https://www1.chapman.edu/~jipsen/gap/ramaddux.html), in its original order.
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

Each entry has its own module, such as `I1S1N1.Ra08`. The source numbering is one-based;
the row's `Model : Fin N → Type` uses zero-based indices. Each row's `classification` states
that an algebra with the given finite signature is isomorphic to exactly one listed model.

The cycle data and operations are concrete. The algebra laws, cycle characterizations,
classifications, and representability decisions have kernel-checked proofs. Executable sanity
checks independently audit the cycle tables and distinguish the entries in each row.
Representations may have infinite bases, as required even for some of these finite algebras.
The constructions use finite groups, dense orders, finitely supported sequences, or successive
composition witnesses. Nonrepresentability is certified by finite network obstructions.
-/
