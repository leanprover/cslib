<pre>
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
</pre>

# Principles and Coding Style of CSLib

This document provides general guidelines for the design, implementation, and documentation of CSLib. It is intended for both contributors and reviewers.

In the absence of more specific guidelines here, we generally follow the [Mathlib style guidelines](https://leanprover-community.github.io/contribute/style.html). Contributors should familiarise themselves with them as well. Here, we focus on principles and conventions that are particularly important for CSLib.

## Principle 0: Guidelines, Not Absolutes

The principles in this document should be applied with good judgement.

Library development is often exploratory. Sometimes we need to formalise concrete examples, experiment with different representations, or develop specialised solutions before we understand what the right general abstractions should be. We should leave room for that exploration.

In particular, we do not expect every contribution to arrive with its final, long-term design already worked out. Good abstractions often emerge through experience, refactoring, and collaboration.

Contributors and reviewers should keep the long-term direction of CSLib in mind, while remaining pragmatic about what can reasonably be achieved at each stage. The goal is to make the library progressively better, not to demand perfection from every contribution.

## API Design

A central goal of CSLib is to provide reusable abstractions and encourage their consistent use across the library.

**New developments should reuse existing abstractions whenever appropriate.** For example, a labelled transition system should use CSLib's `LTS` abstraction rather than introduce an independent representation of the same concept.

We distinguish two complementary forms of reuse: _vertical_ and _horizontal_ reuse. Another important aspect is automation. These are described next.

### Vertical Reuse

Vertical reuse concerns developments within the same domain or family of theories.

When developing a specialised theory, look for definitions, theorems, and infrastructure that can be inherited from more general developments. Common concepts should be formalised at an appropriate shared level rather than duplicated across specialisations. This applies not only to definitions and theorems, but also to notation, instances, and proof automation.

An example is the development of modal logic, whereby many specialised logics (like basic modal logic and Hennessy-Milner Logic) are derived from a generic modal framework.

### Horizontal Reuse

Horizontal reuse concerns abstractions that can be useful across different domains.

When developing a new concept, consider whether it can be expressed using existing general interfaces, or whether parts of the development could usefully be made available to other domains. 

Prefer abstractions that capture genuinely shared structure over ones that are unnecessarily tied to a particular application. At the same time, avoid generality for its own sake: generic infrastructure should make concrete developments easier, not more complicated.

An example is the use of `LTS` API across concurrency theory, automata, and Hennessy-Milner Logic.

### Automation as an API

We consider proof automation an important part of API design in CSLib. The goal is not to automate every proof, but to make commonly needed knowledge easy to activate.

When developing definitions and theorems, consider how easily they can be applied in subsequent developments through tactics such as grind and simp. Well-crafted automation, such as curated grind sets, is part of the API: it can make general results immediately useful to specialised developments, without requiring users to repeatedly unfold definitions, translate between representations, or reconstruct routine arguments.

An example is the `modal` grind set, which supports automated reasoning about modal propositions.

When developing automation, consider predictability and performance. Not every theorem should be registered for automatic use.

Automation can also provide useful feedback about the design of the library. If a simple fact repeatedly requires complicated proofs or substantial manual intervention, consider whether a theorem is missing, an interface could be improved, or an abstraction should be reconsidered.

## Definitions: Terms vs Tactic Mode

Whenever possible, prefer writing definitions (`def`s) directly as terms rather than using `by` blocks.

In general, we want the computational content of definitions to be explicit and reasonably easy to inspect. Tactic mode is appropriate when writing the definition is too difficult or it genuinely improves clarity.

## Proofs

Please make proofs easy to follow whenever possible.

Proof golfing and automation are welcome, provided that proofs remain reasonably readable and do not noticeably increase compilation time.

In particular:

- Keep the logical progression of a proof visible. For example, prefer explicit rewrites and applications when they make the argument easier to understand.
- Avoid using `simp` in the middle of proofs, unless it is in the `simp only` form.
- Avoid large terminal `simpa` calls that hide substantial reasoning. A sequence of rewrites and applications is often preferable.

Use automation where it eliminates routine reasoning without obscuring the essential argument.

## Variable names

Feel free to use variable names that make sense in the domain that you are dealing with. For example, in the `LTS` library, `State` is used for types of states and `μ` is used as variable name for transition labels.

## Notation

The library hosts a number of languages with their own syntax and semantics, so we try to manage notation with reusability and maintainability in mind.

- If you want notation for a common concept, like logical operators, try to find an existing typeclass that fits your need.
- If you define new notation that in principle can apply to different types (e.g., syntax or semantics of other languages), keep it locally scoped or create a new typeclass.

## Documentation

Document your definitions and theorems to ease both use and reviewing.
When formalising a concept that is explained in a published resource, please reference the resource in your documentation.
