# Code organisation

This document gives an overview of how the codebase is structured, in terms of directories.

**Note** that this organisation is still under active discussion and is subject to change.

# Codebase organisation

- Cslib. The root namespace of the Computer Science library.
  - Foundations. General-purpose definitions and results (complexity theory, semantics, etc.).
    - Data. General-purpose structures and types.
      - HasFresh. Types equipped with a `fresh` generator (given a finite set, it generates an element not in that set).
      - …
    - Control. General-purpose structures and types for expressing control flow.
      - Monad. Monads.
        - Free. Free monads.
    - Semantics. Operational semantics (reduction and transition systems), program equivalences, etc.
      - Lts.
      - Bisimilarity.
      - TraceEq.
      - …
  - Logic. Logics, sequent calculi, etc.
    - HoareLogic.
    - LinearLogic.
    - LinearTemporalLogic.
    - …
  - Languages. Modelling and programming languages.
    - Boole.
    - CCS.
    - LambdaCalculus.
    - PiCalculus.
    - …
  - Computability. Automata theory, turing machines, partial recursive functions, register machines, etc.
    - Dfa
    - Nfa
    - TuringMachine.
    - …
- CslibTests. This directory contains tests for the library.
