# Contributing to CSLib

It's great that you're interested in contributing to CSLib! :tada:

Please read the rest of this document before submitting a pull request.
If you have any questions, a good place to ask them is the [Lean prover Zulip chat](https://leanprover.zulipchat.com/).

# Contribution model

To get your code approved, you need to submit a [pull request (PR)](https://github.com/leanprover/cslib/pulls).
Each PR needs to be approved by at least one relevant maintainer. You can read the [list of current maintainers](/GOVERNANCE.md#maintainers).

If you are adding something new to CSLib and are in doubt about it, you are very welcome to contact us on the [Lean prover Zulip chat](https://leanprover.zulipchat.com/).

# Style and documentation

We generally follow the [mathlib style for coding and documentation](https://leanprover-community.github.io/contribute/style.html), so please read that as well. Some things worth mentioning and conventions specific to this library are explained next.

## Variable names

Feel free to use variable names that make sense in the domain that you are dealing with. For example, in the `Lts` library, `State` is used for types of states and `μ` is used as variable name for transition labels.

## Proof style and golfing :golf:

Please try to make proofs easy to follow.
Golfing and automation are welcome, as long as proofs remain reasonably readable and compilation does not noticeably slow down.

## Notation

The library hosts a number of languages with their own syntax and semantics, so we try to manage notation with reusability and maintainability in mind.

- If you want notation for a common concept, like reductions or transitions in an operational semantics, try to find an existing typeclass that fits your need.
- If you define new notation that in principle can apply to different types (e.g., syntax or semantics of other languages), keep it locally scoped or create a new typeclass.

## Documentation

Document your definitions and theorems to ease both use and reviewing.
When formalising a concept that is explained in a published resource, please reference the resource in your documentation.

# Design principles

## Reuse

A central focus of CSLib is providing reusable abstractions and their consistent usage across the
library. New definitions should instantiate existing abstractions whenever appropriate: a
labelled transition system should use `LTS`, etc.

# Continuous Integration

There are a number of checks that run in continuous integration. Here is a brief guide that includes
instructions on how to run these locally.

## Pull Request Titles

It is required that pull request titles begun with one of the following categories followed by a
colon: `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`. These may optionally be followed by a 
parenthetical containing what area of the library the PR is working on.

## Testing

There is a [series of tests](/scripts/RunTests.lean) that runs for each PR. The components of this
are

- running the tests found in [CslibTests](/CslibTests)
- checking that all files import [Cslib.Init](/Cslib/Init.lean), which sets up some default linting
  and tactics

You can run these locally with `lake test`.

## Linting

CSLib uses a number of linters, mostly inherited from Batteries and Mathlib. These come in three varieties:

- *syntax linters*, which appear as you write your code and will give warnings in `lake build`
- *environment linters*, which can be run using `lake lint` or the `#lint` command
- *text linters*, which can be run with `lake exe lint-style` and fixed automatically with the `--fix` option

## Imports

There is a also a test that [Cslib.lean](/Cslib.lean) imports all files. You can ensure this by
running `lake exe mk_all --module` locally, which will make the required changes.
