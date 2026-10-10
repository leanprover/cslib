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

## Security games

[`Negligible`](Negligible.lean) specializes Mathlib's `SuperpolynomialDecay` to natural security
parameters, with zero, comparison, and polynomial-loss bounds.
[`Game`](Game.lean) gives the acceptance probability, distinguishing advantage and negligible
security of Boolean experiments.
[`Game/Hybrid`](Game/Hybrid.lean) supplies hybrid arguments with polynomially many hops.
[`Game/Statistical`](Game/Statistical.lean) identifies Boolean advantage with statistical
distance, so a statistical approximation can be one hop of a computational argument.

## Pseudorandom generators

[`Primitives/PRG`](Primitives/PRG) formalizes Boneh and Shoup's Attack Game 3.1 using
PMFs. `Generator.Secure G Admissible ε` bounds the distinguishing advantage of every
admissible randomized test. `Family.SecureWithError` allows a parameter-dependent error bound;
`Family.Secure` requires negligible advantage separately for each admissible family, using
`Negligible`, Mathlib's `SuperpolynomialDecay` at natural parameters. A negligible error bound
implies this asymptotic notion.
The caller supplies `Admissible`; these definitions do not assert computational efficiency.
The seed and ideal distributions are explicit parameters, defaulting to uniform sampling on
finite types, so the same experiments apply to distributions on infinite types.

The range-membership adversary has advantage exactly `1 - |range G| / |Output|`, and hence
at least `1 - |Seed| / |Output|`. Any non-negligible lower bound on the image gap rules out
asymptotic security when the range-test family is admissible. The executable `rangeTest`
requires `DecidableEq Output`. Bitstring families eventually stretching by at least one bit
are consequently insecure against any class admitting this test, with both `Fin n → Bool`
and `BitVec n` versions and nonexistence corollaries. Zero-error security against all tests
is equivalent to matching the ideal distribution; with the defaults, this means exactly uniform
output. The identity generator is a nonexpanding example.

## Plans and notes

- We plan on developing applied calculi and logics for modelling and reasoning about security protocols.
- We plan on developing a comprehensive library of primitives and foundational protocols, together with their proofs of correctness.
- We plan on supporting downstream efforts on the development of secure digital infrastructures (including implementation of complex secure applications and systems).
