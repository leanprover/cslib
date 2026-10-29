<pre>
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
</pre>

# Crypto

This directory hosts **cryptographic definitions, primitives, protocol models, and related security metatheory**. Its scope includes both basic cryptographic notions and larger developments such as security protocols.

We aim at supporting both abstract security reasoning and concrete protocol developments, while making explicit the relations between them. To this end, this part of CSLib has very important relationships with [Languages](../Languages) and [Logics](../Logics), explained in the remainder.

## Principles

### Integration with languages

Whenever appropriate, cryptographic primitives should be developed so that they compose well with CSLib's [languages](../Languages) that offer a way to integrate a computational substrate. This is common, for example, in choreographic programming languages and many process calculi.

The aim is to build end-to-end models where cryptographic operations appear inside larger communicating or computational systems.

To this end, we expect to leverage the combination of `Crypto` and [Languages](../Languages) to define and formally reason about security protocols. CSLib's common semantics APIs connecting [Languages](../Languages) and [Logics](../Logics) should enable such reasoning.

## Plans and notes

- We plan on developing applied calculi and logics for modelling and reasoning about security protocols.
- We plan on developing a comprehensive library of primitives and foundational protocols, together with their proofs of correctness.
- We plan on supporting downstream efforts on the development of secure digital infrastructures (including implementation of complex secure applications and systems).
