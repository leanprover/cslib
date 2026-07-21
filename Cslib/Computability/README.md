<pre>
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
</pre>

# Computability

This directory hosts **formal developments in computability and neighbouring areas**. Its scope includes automata, complexity classes, formal languages over finite and infinite words, and other machine models.

## Principles

### Multiple computational models

There is a plethora of computational models in the literature, some of which are very near to each other (e.g., Turing machines and Wang B-machines). Depending on the aim, one can be more convenient than the other.
In general, computability can be studied through different kinds of objects.

These representations can coexist when they serve different purposes. A central goal is to make their tradeoffs explicit and to connect them where possible.

### Reuse of common infrastructure

The [Foundations](../Foundations) directory offers abstractions that are directly useful for computability-theoretic developments and should be reused as much as possible. Examples already present in this directory include the use of labelled transition systems for automata and distributed algorithms, tape structures for Turing machines, and general relation-theoretic tools for machine semantics.

This approach enables:
1. Reusing and transferring constructions and results across different models.
2. Applying CSLib's [logics](../Logics) to reason about computational models.
3. Developing connections between computability models and other areas (like the constructions of automata based on transition systems).

### Separation from languages

Some of the developments here are close to [Languages](../Languages), but are placed here instead because the emphasis is on formal languages over words and models typically linked to computability studies.

## Plans and notes

- We plan on expanding this directory with more machine models and associated results, including equivalence results, closure properties, and other metatheory.
- We plan on clarifying and formalising connections between language-theoretic, automata-theoretic, machine-based, and distributed perspectives on computation.
