# CSLib

The Lean library for Computer Science.

Official website at <https://www.cslib.io/>.

# What's CSLib?

CSLib aims at formalising Computer Science theories and tools, broadly construed, in the Lean programming language.

## Aims

- Offer APIs and languages for formalisation projects, software verification, and certified software (among others).
- Establish a common ground for connecting different developments in Computer Science, in order to foster synergies and reuse.

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

Download Mathlib's prebuilt files before the first build, or Lake compiles Mathlib from source:

```sh
lake exe cache get
```

`lake exe cache get` does not store CSLib's own build products. To reuse a local CSLib build across checkouts of the same Lean toolchain, opt in to Lake's artifact cache:

```sh
export LAKE_ARTIFACT_CACHE=true
```

Left unset, Lake may read cached artifacts and will not write this package's outputs into the shared cache. `LAKE_RESTORE_ARTIFACTS=true` copies them back into `.lake/build` when a tool expects that layout.

Uploading those artifacts for other people is separate, and this repository does not do it in CI. After a build with `LAKE_ARTIFACT_CACHE=true`, `lake cache put` publishes the local cache. That command needs `LAKE_CACHE_KEY` and a cache service (`LAKE_CACHE_SERVICE`, or `LAKE_CACHE_ARTIFACT_ENDPOINT` together with `LAKE_CACHE_REVISION_ENDPOINT`).

# Contributing and discussion

Please see our [contribution guide](/CONTRIBUTING.md) and [code of conduct](/CODE_OF_CONDUCT.md).

For discussions, you can reach out to us on the [Lean prover Zulip chat](https://leanprover.zulipchat.com/).
