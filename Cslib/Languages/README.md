<pre>
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
</pre>

# Languages

This directory hosts **modelling and programming languages** formalised in CSLib and their properties. Their components can include syntax, semantics, typing and other reasoning disciplines, execution facilities (compilers, interpreters, etc.), behavioural theories, supporting metatheory, etc.
We are interested in many kinds of languages, from foundational calculi to applied programming frameworks.

The focus is not only on individual languages in isolation, but also on exposing them through reusable abstractions from [Foundations](../Foundations), such as contexts, substitution, congruence, reduction systems, and labelled transition systems.

## Principles

### Reuse of common infrastructure

The [Foundations](../Foundations) directory offers useful modules for language development, which should be used as much as possible.
These modules include support for syntax (like contexts and congruence relations), semantics (like transition systems),  compiler correctness (like behavioural relations), and more.

### Multiple representations are welcome

Different representations can coexist when they serve different purposes. For example `LambdaCalculus` currently contains both named and locally nameless developments. The goal is to make tradeoffs explicit and to connect them where possible.

## Plans and notes

- We expect this directory to grow with many more languages, as well as connections between languages, logics, and other reasoning techniques.
- A recurring issue is how to handle binders. We still need to develop general facilities for this. Leveraging multiple representations of languages, we also plan on formally exploring the connection between standard pen & paper definitions and convenient formal representations, for example the relation between α-equivalence and techniques based on de Brujin indices.
- We aim at providing reusable infrastructure for defining languages and provably-correct compilers.
- Some topics that are often associated with languages also appear elsewhere in CSLib when a more general placement is preferrable. For example, automata and formal languages over words are in [Computability](../Computability), while reusable semantic infrastructure lives in [Foundations](../Foundations).
