/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.Counts.I1S0N2
public import Cslib.Foundations.RelationAlgebra.Catalogue.Counts.I1S1N2
public import Cslib.Foundations.RelationAlgebra.Catalogue.Counts.I1S2N1
public import Cslib.Foundations.RelationAlgebra.Catalogue.Counts.I1S3N1
public import Cslib.Foundations.RelationAlgebra.Catalogue.Counts.I1S4N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.Counts.I1S5N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S0N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S0N1
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N0
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0

/-!
# Small integral relation algebras

This catalogue defines all 115 integral relation algebras through four atoms, up to isomorphism,
and proves the isomorphism class counts for the five- and six-atom rows in
[Peter Jipsen's list](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The explicitly defined entries retain the source's order and include representability decisions.
The larger rows use certified searches of canonical cycle masks without individual model modules.
It covers integral algebras only: the identity is a single atom. The general `RelationAlgebra`
class and `Representable` predicate do not impose integrality or finiteness.

The signature `⟨i, j, k⟩` counts identity atoms, symmetric diversity atoms, and pairs of
nonsymmetric atoms. Thus the total atom count is `i + j + 2 * k`.

| Namespace | Signature | Isomorphism classes | Representable | Nonrepresentable |
|-----------|-----------|---------|---------------|------------------|
| `I1S0N0` | ⟨1, 0, 0⟩ | 1 | 1 | 0 |
| `I1S1N0` | ⟨1, 1, 0⟩ | 2 | 2 | 0 |
| `I1S0N1` | ⟨1, 0, 1⟩ | 3 | 3 | 0 |
| `I1S2N0` | ⟨1, 2, 0⟩ | 7 | 7 | 0 |
| `I1S1N1` | ⟨1, 1, 1⟩ | 37 | 26 | 11 |
| `I1S3N0` | ⟨1, 3, 0⟩ | 65 | 45 | 20 |
| `Counts.I1S0N2` | ⟨1, 0, 2⟩ | 83 | — | — |
| `Counts.I1S2N1` | ⟨1, 2, 1⟩ | 1316 | — | — |
| `Counts.I1S4N0` | ⟨1, 4, 0⟩ | 3013 | — | — |
| `Counts.I1S1N2` | ⟨1, 1, 2⟩ | 47965 | — | — |
| `Counts.I1S3N1` | ⟨1, 3, 1⟩ | 988464 | — | — |
| `Counts.I1S5N0` | ⟨1, 5, 0⟩ | 3849920 | — | — |

Through four atoms, each entry has its own module, such as `I1S1N1.Ra08`. Entry numbering is
one-based; the row's `Model : Fin N → Type` uses zero-based indices. Each such row's
`classification` states that an algebra with the given finite signature is isomorphic to
exactly one listed model.

For larger rows, `Counts.I1SxNy.count` states `isomorphismClassCount x y = N`. The counting
infrastructure proves that canonical masks correspond bijectively to isomorphism classes and
classify arbitrary algebras with `HasSignature A 1 x y`. The kernel checks each search certificate,
including rejected branches, forced choices, symmetry comparisons and counts of settled families.
These rows make no representability assertion.

The explicit cycle data and operations are concrete. Algebra laws, cycle characterizations,
classifications and counts have kernel-checked proofs. Executable sanity checks independently
audit the smaller cycle tables and distinguish their entries. Representations may have infinite
bases, as required even for some of these finite algebras. The constructions use finite groups,
dense orders, finitely supported sequences, or successive composition witnesses.
Nonrepresentability is certified by finite network obstructions.
-/
