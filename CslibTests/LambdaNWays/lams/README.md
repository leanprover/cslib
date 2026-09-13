# `lambda-n-ways` test corpus

The `.lam` files in this directory are copied verbatim from the `lams/` directory of
[`lambda-n-ways`](https://github.com/sweirich/lambda-n-ways), a comparison of implementations of
binding in the untyped λ-calculus by Stephanie Weirich. They are used by
`CslibTests/LambdaNWays/Corpus.lean` to test Cslib's locally nameless representation, following
that project's `tests/Main.hs`.

Each `X.lam` file holds one un-normalized λ-term per line, and the matching `X.nf.lam` file holds
the normal form of the term on the corresponding line. `lennart.lam` is the exception: it is a
single term spanning the whole file. Lines beginning with `--` are comments recording statistics
about the term that follows.

Every `X.lam`/`X.nf.lam` pair from upstream is present. Upstream's `constructed.lam`,
`fact5.lam`, `lennartchurch.lam` and `simple.lam` are not, because they have no recorded normal
form, and neither are the `X.eval.lam` files, which record weak head normal forms for upstream's
evaluation benchmark rather than normal forms.

Note that Lake does not track these files as dependencies of the modules that read them with
`include_str`, so editing one after a build will not on its own trigger a re-elaboration of
`Corpus.lean`.

## License

`lambda-n-ways` is distributed under the MIT license:

> MIT License
>
> Copyright (c) 2022 Stephanie Weirich
>
> Permission is hereby granted, free of charge, to any person obtaining a copy
> of this software and associated documentation files (the "Software"), to deal
> in the Software without restriction, including without limitation the rights
> to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
> copies of the Software, and to permit persons to whom the Software is
> furnished to do so, subject to the following conditions:
>
> The above copyright notice and this permission notice shall be included in all
> copies or substantial portions of the Software.
>
> THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
> IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
> FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
> AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
> LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
> OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
> SOFTWARE.
