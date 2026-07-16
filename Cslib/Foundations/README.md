<pre>
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
</pre>

# Foundations

This directory covers **common foundations** for the rest of CSLib and downstream developments. As such, it acts as its fulcrum of integration through common concepts and APIs. This directory includes also additional results about foundational data objects defined in Mathlib, such as `Nat` and `Set`.

Please browse the subdirectories for details.

The foundational approach to semantics spans multiple directories and has a large role; it is explained below.

## Semantics

A recurring aspect that cuts across different areas is semantics. Examples of such areas include concurrency theory, computational models, logics, modelling languages, programming languages, and security protocols.

Most of the APIs for semantics provided in `Foundations` are in the [Semantics](Semantics) directory. An example of an exception is the [Relation](Relation) directory, which sits at the top level.

The vision is to provide common abstractions that can be reused throughout CSLib. Beyond providing reusable definitions, having common APIs for semantics is important for multiple reasons. The next list covers some illustrative examples.

- The modular use of modal and dynamic logics to reason about programs.
- The sharing of semantic metatheory, such as behavioural equivalences for labelled transition systems (bisimulation, trace equivalence, etc.) and common definitions like confluence.
- The development of provably-correct compilers between languages based on these abstractions, supporting for example proofs of bisimilarity or full abstraction.
- The elicitation of connections between different domains, including computability, crypto, logic, programming languages, etc.

### Plans

- Many modules are still missing, for example facilities for probabilistic operational semantics, derivatives and antiderivatives for transition systems, logical relations, etc. We plan to develop develop a comprehensive library.
- We plan on building general frameworks that give important metatheoretical properties about the semantics of objects that respect certain properties (e.g., rule formats, GSOS) for free (or at least in principled ways rather than doing it from scratch).
- We plan both on developing constructions that embed different semantic models into each other and to prove separation results between them.
- We plan on pushing towards building formal connections between different domains based on a semantic approach.
