# Contributing to cslib

Great that you're interested in contributing to cslib! :tada:

Please read the rest of this document before submitting a pull request. If you have any questions, a good place to ask them is the [Lean community Zulip chat](https://leanprover.zulipchat.com/).

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
