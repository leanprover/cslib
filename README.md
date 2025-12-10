# cslib

The Lean library for Computer Science.

Documentation at <https://cs-lean.github.io/>.

# What's cslib?

Cslib aims at formalising Computer Science theories and tools, broadly construed, in the Lean programming language.

## Aims

- Offer APIs and languages for formalisation projects, software verification, and certified software (among others).
- Establish a common ground for connecting different developments in Computer Science, in order to foster synergies and reuse.

# Using cslib in your project

To add cslib as a dependency to your Lean project, add the following to your `lakefile.toml`:

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
