/-
Copyright (c) 2026 Alex Korbonits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Korbonits
-/

import CslibTests.LambdaNWays.Basic

/-! # The `lambda-n-ways` normalization tests

Each check below normalizes every term of a `.lam` file with Cslib's locally nameless λ-terms and
compares the result with the term recorded in the matching `.nf.lam` file. Every such pair of
files in [`lambda-n-ways`](https://github.com/sweirich/lambda-n-ways) is covered; see
`Basic.lean` for the harness and `lams/README.md` for the provenance of the data.

A failing check reports the offending term, what it normalized to and what was expected, and
fails elaboration of this file.
-/

set_option linter.hashCommand false

namespace CslibTests.LambdaNWays

/-! ## Small terms

`full` and `full-2` place a diverging subterm where a normal-order strategy never needs it,
so an implementation that evaluates too eagerly loops instead of failing. `id` and `lazy` are
short chains of identity functions. -/

#eval run "full" (checkCorpus (include_str "lams" / "full.lam")
  (include_str "lams" / "full.nf.lam"))

#eval run "full-2" (checkCorpus (include_str "lams" / "full-2.lam")
  (include_str "lams" / "full-2.nf.lam"))

#eval run "id" (checkCorpus (include_str "lams" / "id.lam")
  (include_str "lams" / "id.nf.lam"))

#eval run "lazy" (checkCorpus (include_str "lams" / "lazy.lam")
  (include_str "lams" / "lazy.nf.lam"))

/-! ## Terms that have caught bugs

Terms that revealed a bug in one or another implementation upstream. Most of them apply a
term under several binders that shadow each other, which is where an off-by-one in the handling
of de Bruijn indices shows up. -/

#eval run "t1" (checkCorpus (include_str "lams" / "t1.lam")
  (include_str "lams" / "t1.nf.lam"))

#eval run "t2" (checkCorpus (include_str "lams" / "t2.lam")
  (include_str "lams" / "t2.nf.lam"))

#eval run "t3" (checkCorpus (include_str "lams" / "t3.lam")
  (include_str "lams" / "t3.nf.lam"))

#eval run "t4" (checkCorpus (include_str "lams" / "t4.lam")
  (include_str "lams" / "t4.nf.lam"))

#eval run "t5" (checkCorpus (include_str "lams" / "t5.lam")
  (include_str "lams" / "t5.nf.lam"))

#eval run "t6" (checkCorpus (include_str "lams" / "t6.lam")
  (include_str "lams" / "t6.nf.lam"))

#eval run "t7" (checkCorpus (include_str "lams" / "t7.lam")
  (include_str "lams" / "t7.nf.lam"))

#eval run "tests" (checkCorpus (include_str "lams" / "tests.lam")
  (include_str "lams" / "tests.nf.lam"))

#eval run "regression1" (checkCorpus (include_str "lams" / "regression1.lam")
  (include_str "lams" / "regression1.nf.lam"))

/-! ## Constructed terms

Terms built to stress one specific behaviour. `capture10` substitutes, at increasing depth,
a term with a free variable that could be captured: a substitution that is not capture-avoiding
gets these wrong. The other three families each perform a single substitution for a free variable
at an incrementally greater binding depth. -/

#eval run "capture10" (checkCorpus (include_str "lams" / "capture10.lam")
  (include_str "lams" / "capture10.nf.lam"))

#eval run "constructed10" (checkCorpus (include_str "lams" / "constructed10.lam")
  (include_str "lams" / "constructed10.nf.lam"))

#eval run "constructed20" (checkCorpus (include_str "lams" / "constructed20.lam")
  (include_str "lams" / "constructed20.nf.lam"))

#eval run "adjust" (checkCorpus (include_str "lams" / "adjust.lam")
  (include_str "lams" / "adjust.nf.lam"))

#eval run "adjustb" (checkCorpus (include_str "lams" / "adjustb.lam")
  (include_str "lams" / "adjustb.nf.lam"))

/-! ## Increasing numbers of substitutions

Random terms whose normalization performs exactly one, two, three and four substitutions,
100 terms per file. -/

#eval run "onesubst" (checkCorpus (include_str "lams" / "onesubst.lam")
  (include_str "lams" / "onesubst.nf.lam"))

#eval run "twosubst" (checkCorpus (include_str "lams" / "twosubst.lam")
  (include_str "lams" / "twosubst.nf.lam"))

#eval run "threesubst" (checkCorpus (include_str "lams" / "threesubst.lam")
  (include_str "lams" / "threesubst.nf.lam"))

#eval run "foursubst" (checkCorpus (include_str "lams" / "foursubst.lam")
  (include_str "lams" / "foursubst.nf.lam"))

/-! ## Random terms

Randomly generated well-scoped terms, 100 per file (5 for the `random25-*` files), of
increasing depth. Normalizing these performs a large number of substitutions and is the main
source of coverage here. -/

#eval run "random" (checkCorpus (include_str "lams" / "random.lam")
  (include_str "lams" / "random.nf.lam"))

#eval run "random2" (checkCorpus (include_str "lams" / "random2.lam")
  (include_str "lams" / "random2.nf.lam"))

#eval run "random15" (checkCorpus (include_str "lams" / "random15.lam")
  (include_str "lams" / "random15.nf.lam"))

#eval run "random16" (checkCorpus (include_str "lams" / "random16.lam")
  (include_str "lams" / "random16.nf.lam"))

#eval run "random17" (checkCorpus (include_str "lams" / "random17.lam")
  (include_str "lams" / "random17.nf.lam"))

#eval run "random18" (checkCorpus (include_str "lams" / "random18.lam")
  (include_str "lams" / "random18.nf.lam"))

#eval run "random19" (checkCorpus (include_str "lams" / "random19.lam")
  (include_str "lams" / "random19.nf.lam"))

#eval run "random20" (checkCorpus (include_str "lams" / "random20.lam")
  (include_str "lams" / "random20.nf.lam"))

#eval run "random25" (checkCorpus (include_str "lams" / "random25.lam")
  (include_str "lams" / "random25.nf.lam"))

#eval run "random25-19" (checkCorpus (include_str "lams" / "random25-19.lam")
  (include_str "lams" / "random25-19.nf.lam"))

#eval run "random25-20" (checkCorpus (include_str "lams" / "random25-20.lam")
  (include_str "lams" / "random25-20.nf.lam"))

#eval run "random35" (checkCorpus (include_str "lams" / "random35.lam")
  (include_str "lams" / "random35.nf.lam"))

#eval run "lams100" (checkCorpus (include_str "lams" / "lams100.lam")
  (include_str "lams" / "lams100.nf.lam"))

/-! ## A single large term

The term of `lennart.lam` computes `6! = sum [1..37] + 17` over a Scott encoding of the naturals,
written with `let`. Normalizing it takes about 4000 β-steps and some 120000 substitutions; the
two sides are not equal, so the normal form is the Church encoding of `False`. -/

#eval run "lennart" (checkTerm (include_str "lams" / "lennart.lam")
  (include_str "lams" / "lennart.nf.lam"))

end CslibTests.LambdaNWays
