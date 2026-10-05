# Scripts for working on cslib

This directory contains miscellaneous scripts that are useful for working on or with cslib.
When adding a new script, please make sure to document it here, so other readers have a chance
to learn about it as well!

## Current scripts and their purpose

**Documentation generation**
- `gendocs.sh`
  Generates the documentation for cslib using `lake`.

**Devcontainer helpers**
- `setup-mistral-vibe.sh`
  Installs the Mistral Vibe VS Code extension (`mistralai.mistral-vibe-code`) if
  missing and ensures required Mistral config entries for the `lean` agent and the `lean-lsp` MCP server are present.

  **Usage:**
  ```bash
  ./scripts/setup-mistral-vibe.sh
  ```

  **Optional environment variable:**
  - `MISTRAL_CONFIG_FILE`: Override the path to `config.toml`.

**Managing nightly-testing and bump branches**
- `create-adaptation-pr.sh` is a variant of the script from Batteries and implements some of the steps
  in the workflow for managing nightly and bump branches.

  Specifically, it will:
  - merge `main` into `bump/v4.x.y`
  - create a new branch from `bump/v4.x.y`, called `bump/nightly-YYYY-MM-DD`
  - merge `nightly-testing` into the new branch
  - open a PR to merge the new branch back into `bump/v4.x.y`
  - announce the PR on zulip
  - finally, merge the new branch back into `nightly-testing`, if conflict resolution was required.

  If there are merge conflicts, it pauses and asks for help from the human driver.

  **Usage:**
  ```bash
  ./scripts/create-adaptation-pr.sh <BUMPVERSION> <NIGHTLYDATE>
  ```
  or with named parameters:
  ```bash
  ./scripts/create-adaptation-pr.sh --bumpversion=<BUMPVERSION> --nightlydate=<NIGHTLYDATE> --nightlysha=<SHA> [--auto=<yes|no>]
  ```

  **Parameters:**
  - `BUMPVERSION`: The upcoming release that we are targeting, e.g., 'v4.10.0'
  - `NIGHTLYDATE`: The date of the nightly toolchain currently used on 'nightly-testing'
  - `NIGHTLYSHA`: The SHA of the nightly toolchain that we want to adapt to
  - `AUTO`: Optional flag to specify automatic mode, default is 'no'

  **Requirements:**
  - `gh` (GitHub CLI) must be installed and authenticated
  - Optional: `zulip-send` CLI for automatic Zulip notifications

**Init Imports**
- `CheckInitImports.lean` (run by `lake exe checkInitImports`) checks that all files transitively import `Cslib.Init`.

**Relation algebra catalogue generation**

- `RelationAlgebra/generate.py` reproduces the individual five-atom algebra modules for
  signatures ⟨1,2,1⟩ and ⟨1,4,0⟩, containing 1,316 and 3,013 isomorphism classes respectively.
  It uses `RelationAlgebra/enumerate.cpp` to enumerate all cycle masks, then independently checks
  each rejected mask's associativity counterexample, each renaming witness, and every canonical
  model in Python. No external Python packages or network access are needed. Requirements are
  Python 3.10 or newer and a C++20 compiler supporting `unsigned __int128` (GCC or Clang).

  Run from the repository root:

  ```bash
  # Re-enumerate and check both complete rows without changing source files.
  python3 scripts/RelationAlgebra/generate.py --check --include-classifications

  # Regenerate one row's individual algebra modules.
  python3 scripts/RelationAlgebra/generate.py --row I1S2N1

  # Export enumeration data for generating the row classification certificates.
  python3 scripts/RelationAlgebra/generate.py --data-only --data-dir /tmp/cslib-ra-data
  ```

  With no options, the script regenerates the entries in both rows. `--row` may be repeated.
  Add `--include-classifications` to also generate or check model dispatch, row proofs, and
  coverage certificates. The complete check re-enumerates once and needs no saved JSON files.
  `--output-root` selects a different repository root, and `--cxx` or the `CXX` environment
  variable selects the compiler. Compilation and intermediate files use a temporary directory.
  `--check` reports missing, changed, or unexpected entry files and never rewrites sources.
  It cannot be combined with data output options. The generator does not modify `Cslib.lean`;
  run `lake exe mk_all` after adding modules and perform the usual project validation.

  [Jipsen's table](https://www1.chapman.edu/~jipsen/gap/ramaddux.html) publishes the class counts
  but does not list the individual algebras in these two rows. Their numbering here is therefore
  independent: choose the lexicographically least representative of each Peircean cycle orbit,
  order those triples by `Atom.code`, and use their indices as mask bits. For each algebra,
  choose the least mask under all identity- and converse-preserving atom permutations. Increasing
  canonical masks receive the names `Ra0001`, `Ra0002`, and so on. This is not Maddux numbering.

  Exported files `cslib-i1s2n1-data.json` and `cslib-i1s4n0-data.json` include the orbit basis,
  canonical masks, packed multiplication tables, atom renamings, successful renaming witnesses,
  and associativity counterexamples. Atom code 0 denotes identity; the other codes follow
  `Atom.code`. Each `[mask, model, rename]` witness maps the source mask to the canonical model,
  with zero-based model and rename indices. Large table codes are decimal strings. These data
  files are reproducible intermediates and need not be committed. The scripts are certificate
  generators, not trusted proof procedures: generated Lean proofs still require kernel checking.

- `RelationAlgebra/rows.py` renders the cycle basis, atom renamings, certified model dispatch,
  and the two unique-index classification statements. `RelationAlgebra/coverage.py` renders
  coverage certificates in blocks of 64 models, then combines them with the associativity
  truth table. Both use the shared comparison logic in `generate.py`. To check these files
  separately against previously exported data, run:

  ```bash
  python3 scripts/RelationAlgebra/rows.py --data-dir /tmp/cslib-ra-data --check
  python3 scripts/RelationAlgebra/coverage.py --data-dir /tmp/cslib-ra-data --check
  ```

  Both accept the same `--row` and `--output-root` options as the entry generator. Omit `--check`
  to regenerate their files. Their inputs are untrusted certificate data; neither script runs
  Lean or changes the public mathematical statements based on an unchecked proof claim.
