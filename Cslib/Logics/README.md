<pre>
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
</pre>

# Logic

CSLib offers **formal logics** for defining specifications and reasoning about programs and systems. Each subdirectory focuses on a specific logic or framework.

Shared foundations can be found in [Foundations/Logic](../Foundations/Logic).

## Principles

### Operators

Please instantiate and use the typeclasses for logical operators (connectives, modalities, etc.) found in [Foundations/Logic](../Foundations/Logic).

### Inference system and logical equivalence

We adopt a unified approach to proof systems and semantics, whereby they instantiate `InferenceSystem`. See [linear logic](LinearLogic) and [modal logic](Modal) for examples.

When defining logical equivalence for a given inference system, instantiate `LogicalEquivalence`. This class also acts as a check that you use the correct APIs.

### Proof relevance in proof systems

A recurring choice when defining a proof system (like a sequent calculus) is whether they should go into `Prop` (proof irrelevance) or a `Type` (proof relevance).
The default choice is to use a `Type` -- at the appropriate universe level, polymorphic if it has type parameters. This makes it easy to define computations on derivations, e.g., to compute their height, display them, or make tools that show how they can be transformed.

### Fragments

To define a fragment of a proof system, you can use a predicate. See [MLL](LinearLogic/CLL/MLL.lean) for an example.

### Notation for judgements

To avoid notation clashes in the notation for judgements, use a wrapper tag that clearly describes the logic. For example, in modal logic this is `Modal[m,w ⊨ φ]`.

## Plans and notes

### Logical equivalence

We plan on leveraging the common infrastructure of `InferenceSystem`, `LogicalEquivalence`, and similar to build common interfaces for manipulating proofs.
If any of these APIs do not suit your needs, we are interested in expanding them or creating new ones that can cover your use cases.

### Notation

We will explore alternative approaches to dealing with notation clashes. An example of a current shortcoming is the necessity of prefixing dynamic logic modalities with a `d`, because they use common notation such as `[...]`. One way of doing this could be to establish typeclasses/syntax also for judgemental notation, such as `m,w ⊨ φ`, and make it accessible within a tag like `Logic`, giving for example `Logic[m,w ⊨ φ]`. This would then scope the notation for propositions only to `φ`.
