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

## Pseudorandom generators

[`Primitives/PRG`](Primitives/PRG) formalizes Boneh and Shoup's Attack Game 3.1 using
Mathlib probability measures. `Generator.Secure G Admissible ε` bounds the distinguishing advantage of every
admissible randomized test. `Family.SecureWithError` allows a parameter-dependent error bound;
`Family.Secure` requires negligible advantage separately for each admissible family, using
Mathlib's `SuperpolynomialDecay`. A negligible error bound implies this asymptotic notion.
The caller supplies `Admissible`; these definitions do not assert computational efficiency.

The range-membership adversary has advantage exactly `1 - |range G| / |Output|`, and hence
at least `1 - |Seed| / |Output|`. Any non-negligible lower bound on the image gap rules out
asymptotic security when the range-test family is admissible. The executable `rangeTest`
requires `DecidableEq Output`. Bitstring families eventually stretching by at least one bit
are consequently insecure against any class admitting this test, with both `Fin n → Bool`
and `BitVec n` versions and nonexistence corollaries. Zero-error security against all tests
is equivalent to exactly uniform output; the identity generator is a nonexpanding example.

## Information-theoretic protocols

Perfect secrecy and secret sharing use Mathlib's `Measure` and measurable `Kernel` interfaces.
Normalization is recorded by `IsProbabilityMeasure` and `IsMarkovKernel`. Secrecy means equality
of the joint measure and the product of its marginals, for every probability prior.
This supports continuous distributions as well as discrete ones.

Encryption correctness requires that almost every generated key work for every message,
with decryption succeeding almost surely over encryption randomness. The exceptional set of
keys is shared by all messages. For countable message spaces, Mathlib's `ae_all_iff` shows that
this is equivalent to a separate almost-sure correctness guarantee for each message.

Posterior distributions use Mathlib's regular conditional kernel `ProbabilityTheory.posterior`.
These APIs require a nonempty standard Borel message or secret space, and posterior equality
holds almost everywhere under the observation distribution. On countable observation spaces,
Mathlib's `ae_iff_of_countable` recovers equality at every observation with positive mass.
The core independence definitions do not require standard Borel spaces.

Finite samplers, including the one-time pad and Shamir's finite-field sampler, use Mathlib's
`uniformOn`. The finite PRG games retain their finite-space assumptions.

## Plans and notes

- We plan on developing applied calculi and logics for modelling and reasoning about security protocols.
- We plan on developing a comprehensive library of primitives and foundational protocols, together with their proofs of correctness.
- We plan on supporting downstream efforts on the development of secure digital infrastructures (including implementation of complex secure applications and systems).
