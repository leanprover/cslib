# Boole

**Boole** is an intermediate language for program verification in Lean. It extends the Strata/Core
intermediate language and serves as a research playground for experimenting with new verification
features. This directory contains example algorithms expressed in Boole and verified using
different pipelines.

## Prerequisites

### Lean 4

Boole and Strata are implemented in Lean 4. Install Lean 4 by following the instructions at:
[https://lean-lang.org/install](https://lean-lang.org/install)

### (Optional) SMT Solver

Some verification pipelines rely on external SMT solvers. You may use either **cvc5** or **Z3**; the
examples in this repository assume `cvc5` is available on your `PATH`.

In addition:

- If you run `#eval Strata.Boole.verify "cvc5" <program>`, Lean will try to execute the external
  `cvc5` binary. Make sure `cvc5` is on your `PATH` when running Lean.
- If you use `import Smt` (e.g. to run `all_goals smt`), Lean also needs to load cvc5's native
  bindings at runtime. This requires passing `--load-dynlib` to Lean (see below).
- If you ran `lake update`, you likely already have a suitable `cvc5` binary under
  `.lake/packages/cvc5`; `scripts/boole-smt.sh` can help run Lean with the right setup.

## Build Instructions

Clone the `Boole-sandbox` branch of CSLib:

```bash
git clone --branch Boole-sandbox https://github.com/leanprover/cslib
```

Build and test the project using Lean's standard workflow:

```bash
lake update && lake build
```

Some files will fail to build if you don't have `cvc5` installed on your machine. However, you can
resolve those failures by commenting out commands of the form `#eval Strata.Boole.verify <program>`.

After a successful build, you should be able to open any file in this directory and have Lean
automatically elaborate the code and attempt to verify the stated properties (some may fail if
features are still under development).

## Running Analyses on Boole Examples

Since Boole extends Strata/Core, its syntax closely resembles Boogie. Below is a simple example of a
program written in Boole:

```lean
import Strata.MetaVerifier

open Strata

def maxExample : Strata.Program :=
#strata
program Boole;

procedure max (x: int, y: int) returns (r: int)
{
  if (x >= y) {
    r := x;
  }
  else {
    r := y;
  }
};
#end
```

The `Strata.MetaVerifier` module provides the infrastructure to parse, type-check, and verify Boole
programs.

The code between the `#strata` and `#end` macros defines the program. The line `program Boole;`
instructs the parser to interpret the enclosed code as a Boole program.

## Adding Specifications

For the `max` procedure, we are interested in the following properties:

1. The result is greater than or equal to both inputs.
2. The result is equal to at least one of the inputs.

These properties can be expressed as specifications:

```lean
import Strata.MetaVerifier

open Strata

def maxExample : Strata.Program :=
#strata
program Boole;

procedure max (x: int, y: int) returns (r: int)
spec {
  ensures r >= x && r >= y;
  ensures r == x || r == y;
}
{
  if (x >= y) {
    r := x;
  }
  else {
    r := y;
  }
};
#end
```

## Verification Pipelines

Boole currently supports two verification approaches:

1. **SMT-based verification**: Verification conditions (VCs) are translated to SMT-LIB and
discharged using an external SMT solver (e.g., Z3 or cvc5).
2. **Lean-based verification**: VCs are translated into an intermediate SMT representation and
lifted into Lean propositions, which can then be proved using Lean tactics.

### SMT-Based Verification

To invoke the SMT-based pipeline, add the following line:

```lean
#eval Strata.Boole.verify "cvc5" maxExample
```

If you are using the cvc5 binary vendored via Lake (under `.lake/packages/cvc5`), the easiest way
to run a Boole file with the right environment is:

```bash
./scripts/boole-smt.sh Cslib/Languages/Boole/examples/MaxExample.lean
```

(Manual setup is also possible; the exact `cvc5` binary path is platform-dependent.)

You should see output similar to the following in Lean's InfoView:

```
Obligation: loopSimple_ensures_0
Property: assert
Result: ✅ pass

Obligation: loopSimple_ensures_1
Property: assert
Result: ✅ pass
```

While this approach leverages powerful automated solvers, it has some limitations:

* It does not allow users to inspect or simplify goals before sending them to the solver, which can
hinder debugging.
* It relies on trusting the solver's correctness, which is not guranteed given their complexity.

### Lean-Based Verification

To address these limitations, Boole supports proving verification conditions directly in Lean. This
approach compiles Boole VCs into SMT-LIB, defines a semantics for a subset of SMT-LIB, and lifts the
resulting obligations into Lean.

You can try this approach by proving the following theorem:

```lean
theorem maxExample_smtVCsCorrect : Strata.smtVCsCorrect maxExample := by
  gen_smt_vcs
```

The `gen_smt_vcs` tactic automatically generates the SMT-IR verification conditions and lifts them
to Lean goals. After running it, you will obtain goals of the form:

```lean
case loopSimple_ensures_1
⊢ ∀ («$__y1» «$__x0» : Int),
  (if «$__x0» ≥ «$__y1» then «$__x0» ≥ «$__y1» else True) →
    (if if «$__x0» ≥ «$__y1» then False else True then if «$__x0» ≥ «$__y1» then False else True else True) →
      (if «$__x0» ≥ «$__y1» then «$__x0» else «$__y1») = «$__x0» ∨
        (if «$__x0» ≥ «$__y1» then «$__x0» else «$__y1») = «$__y1»

case loopSimple_ensures_0
⊢ ∀ («$__y1» «$__x0» : Int),
  (if «$__x0» ≥ «$__y1» then «$__x0» ≥ «$__y1» else True) →
    (if if «$__x0» ≥ «$__y1» then False else True then if «$__x0» ≥ «$__y1» then False else True else True) →
      (if «$__x0» ≥ «$__y1» then «$__x0» else «$__y1») ≥ «$__x0» ∧
        (if «$__x0» ≥ «$__y1» then «$__x0» else «$__y1») ≥ «$__y1»
```

These goals can be discharged using standard Lean tactics. For example:

```lean
theorem maxExample_smtVCsCorrect : Strata.smtVCsCorrect maxExample := by
  gen_smt_vcs
  all_goals smt
```

The `smt` tactic attempts to close Lean goals by invoking SMT solvers. It is under active
development and is currently being tailored to prove verification conditions generated by Boole.
To use it, ensure you import:

```lean
import Smt
```

To run files that import `Smt`, you may need to pass `--load-dynlib` so Lean can load cvc5's native
bindings. For convenience, `scripts/boole-smt.sh` attempts to set up `PATH` and `--load-dynlib`
automatically:

```bash
./scripts/boole-smt.sh Cslib/Languages/Boole/examples/MaxExample.lean
```

VS Code note: the `--load-dynlib` requirement is not VS Code-specific; it applies to any way of
running Lean that loads and executes `Smt` code. If you want this to work in the editor, configure
your Lean server to start with that extra argument (and ensure `cvc5` is on `PATH`, e.g. by starting
VS Code from a shell where it is set).

The full example is available in [`MaxExample.lean`](MaxExample.lean).
