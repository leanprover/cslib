<pre>
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
</pre>

# Mech: Mechanised Choreographic Programming

This directory is a placeholder for the upstreaming of Mech, a language for choreographic programming developed at FORM.

Mech is a verified choreographic programming framework. It can be used to:
1. Codify distributed protocols and systems in a choreographic language, benefitting from the simple global view of the 'Alice and Bob' protocol notation.
2. Reason about choreographic programs with CSLib's foundations and tools
3. Compile choreographies into provably-correct models of distributed programs in a process calculus.


## Principles and plans

### Protocol library development

We plan on using Mech to develop a library of verified protocol for concurrent and distributed systems.

### Support CSLib's compilation infrastructure

Mech is sufficiently complex to test CSLib's infrastructure for compiler verification. We will establish a strong bisimilarity for the choreography compiler, enabling the transference of results from choreographies to their compiled versions.

### Iterative approach

A downstream version of Mech already exists at FORM -- CSLib originally started as a spin-off of some general components developed to make Mech possible, like `LTS`. This version is fairly complete, as it formalises most of the textbook theory of choreographic programming ('Introduction to Choreographies'), but some parts require adaptation or generalisation to be included in CSLib.

We follow an iterative approach, whereby we introduce core components and then gradually augment them with more advanced features (like recursion, nondeterminism, etc.).

### Placement

Components that might be of interest beyond Mech (like [StatefulProcesses](../StatefulProcesses), a calculus used in some variation over different research papers) are placed outside of this directory.

### Ergonomics

- The current development has many unbundled parameters (for types, local computation, etc.). We plan on exploring convenient bundled interfaces for easier use. See also the [tests for StatefulProcesses](/CslibTests/StatefulProcesses.lean).
- We could use a lot more convenience in escaping to Lean for expression evaluation. This is nontrivial because we need to resolve variables from the local store of the appropriate process.