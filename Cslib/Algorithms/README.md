<pre>
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clark Barrett, Swarat Chaudhuri, Jim Grundy, Fabrizio Montesi, Leonardo de Moura, Alexandre Rademaker, Sorrachai Yingchareonthawornchai
</pre>

# Algorithms

This directory hosts **algorithms and their properties**. These properties concern functional correctness, complexity, and other relevant results. The directory also includes dedicated facilities for reasoning about algorithms written in Lean.

The broader aim is to develop a library of verified algorithms, both in Lean and in other languages formalised in CSLib. Accordingly, it is in scope to study algorithms implemented as Lean programs as well as algorithms expressed inside one of CSLib's [Languages](../Languages), depending on the purpose of the development.
All algorithms sit in a language-specific subdirectory depending on the language they are written in, like `Boole`, `Lean`, etc.

## Principles

### Synergies with languages and logics

Important synergies are expected with both [Languages](../Languages) and [Logics](../Logics). Languages provide settings in which algorithms can be written and studied under formal semantics, while logics provide tools for specifying and proving their properties.

One long-term aim is to support principled reasoning pipelines where algorithms are defined in a language, specified through logical notions, and verified inside shared semantic frameworks.

### Dealing with optimisation

Optimising an algorithm can make it harder to reason about it. When this happens, one can prove a relation (e.g., functional or behavioural) to a simpler, less optimised version, and then work by transferring results from it.
In doing this, we expect contributions to leverage Lean's and CSLib's common infrastructures whenever reasonable.

## Plans and notes

- We aim at developing a comprehensive library of verified algorithms, covering both Lean implementations and algorithms represented in other languages.
- We plan on expanding the infrastructure for proving properties of Lean algorithms, including correctness, complexity, and other forms of analysis.
- Reusable mathematical and semantic infrastructure should live elsewhere in CSLib when it is more general-purpose, so developments in this directory should integrate well with [Foundations](../Foundations), [Languages](../Languages), and [Logics](../Logics).
