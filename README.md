# CSLib

The Lean library for Computer Science.

Official website at <https://www.cslib.io/>.

# What's CSLib?

CSLib aims at formalising Computer Science theories and tools, broadly construed, in the Lean programming language.

## Aims

- Offer APIs and languages for formalisation projects, software verification, and certified software (among others).
- Establish a common ground for connecting different developments in Computer Science, in order to foster synergies and reuse.

## Verified Algorithms

CSLib includes a growing collection of formally verified algorithms with time complexity analysis using the `TimeM` monad:

- **MergeSort**: Proved to be a permutation of the input, sorted, and with $O(n \log n)$ complexity.
- **QuickSort**: Proved to be a permutation of the input, sorted, and with $O(n^2)$ worst-case complexity. Uses the `grind` tactic for automation.

## Decision Procedures (The "Holy Grail")

CSLib now includes foundational decision procedures for formal verification:

- **SAT Solver (DPLL)**: A fully functional, verified SAT solver implementing the DPLL algorithm. It defines CNF syntax, semantics, and includes a soundness proof structure, marking the first step towards a verified SMT kernel in CSLib.

## Formal Languages

- **Symbolic Regular Expressions**: Generic implementation over any Boolean Algebra with Brzozowski derivatives and nullability checks.
- **Trace Execution**: Inductive and indexed definitions for LTS execution traces.

# Using CSLib in your project

To add CSLib as a dependency to your Lean project, add the following to your `lakefile.toml`:

```toml
[[require]]
name = "cslib"
scope = "leanprover"
rev = "main"
```

Or if you're using `lakefile.lean`:

```lean
require cslib from git "https://github.com/leanprover/cslib" @ "main"
```

Then run `lake update cslib` to fetch the dependency. You can also use a release tag instead of `main` for the `rev` value.

# Contributing and discussion

Please see our [contribution guide](/CONTRIBUTING.md) and [code of conduct](/CODE_OF_CONDUCT.md).

For discussions, you can reach out to us on the [Lean prover Zulip chat](https://leanprover.zulipchat.com/).
