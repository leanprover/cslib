# Cslib benchmark suite

This directory contains the cslib benchmark suite.
It is built around [radar](github.com/leanprover/radar)
and benchmark results can be viewed
on the [Lean FRO radar instance](https://radar.lean-lang.org/repos/cslib).

To execute the entire suite, run `scripts/bench/run` in the repo root.
To execute an individual benchmark, run `scripts/bench/<benchmark>/run` in the repo root.
All scripts output their measurements into the file `measurements.jsonl`.

Radar sums any duplicated measurements with matching metrics.
To post-process the `measurements.jsonl` file this way in-place,
run `scripts/bench/combine.py` in the repo root after executing the benchmark suite.

The `*.py` symlinks exist only so the python files are a bit nicer to edit
in text editors that rely on the file ending.

## Adding a benchmark

To add a benchmark to the suite, follow these steps:

1. Create a new folder containing a `run` script and a `README.md` file describing the benchmark,
   as well as any other files required for the benchmark.
2. Edit `scripts/bench/run` to call the `run` script of your new benchmark.
