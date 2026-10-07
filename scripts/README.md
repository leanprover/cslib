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

**Relation algebra counting certificates**

- `RelationAlgebra/count.py` runs the C++20 search in `RelationAlgebra/count.cpp` and writes
  reproducible JSON certificates. It supports all integral signatures through six atoms.
  Requirements are Python 3.10 or newer and a C++20 compiler; no third-party Python packages
  or network access are needed. `--cxx` or the `CXX` environment variable selects the compiler.
  Compilation and intermediate files use a temporary directory.

- `RelationAlgebra/count_lean.py` renders those certificates as Lean count theorems in
  `Cslib/Foundations/RelationAlgebra/Catalogue/Counts/`. The committed count rows cover the
  five-atom signatures `I1S0N2`, `I1S2N1`, `I1S4N0` and the six-atom signatures `I1S1N2`,
  `I1S3N1`, `I1S5N0`. The explicit models and representability proofs through four atoms
  remain in their original catalogue modules.

- `RelationAlgebra/test_count.py` runs regression tests for certificate validation, including
  invalid reason records, incorrect uses of valid reasons, and malformed search trees.
  Run `python3 scripts/RelationAlgebra/test_count.py` from the repository root.

- `RelationAlgebra/benchmark.py` selects representative independent certificate fragments,
  prepares standalone Lean profiling inputs, and summarizes their timing reports. It keeps
  metadata verification in the measured input. Run the script with `--help` for its commands.
  Fragment measurements help identify costs; acceptance requires rebuilding the complete row.

  Run from the repository root, for example:

  ```bash
  # Generate a certificate and independently verify every search step in Python.
  python3 scripts/RelationAlgebra/count.py --row I1S1N2 --data-dir /tmp/cslib-ra-counts --verify

  # Render its kernel-checked Lean count theorem.
  python3 scripts/RelationAlgebra/count_lean.py --row I1S1N2 --data-dir /tmp/cslib-ra-counts

  # Check reproducibility without rewriting either the JSON or Lean source.
  python3 scripts/RelationAlgebra/count.py --row I1S1N2 --data-dir /tmp/cslib-ra-counts --check --verify
  python3 scripts/RelationAlgebra/count_lean.py --row I1S1N2 --data-dir /tmp/cslib-ra-counts --check
  ```

  Both scripts accept repeated `--row` arguments. Omitting `--row` makes `count.py` process all
  twelve supported signatures, while `count_lean.py` renders the six committed count modules.
  `count.py` prints the count and search statistics, and saves JSON only when
  `--data-dir` is supplied. `count_lean.py` requires that directory; `--output-root` selects a
  different destination repository, and `--metadata-only` isolates the problem-encoding proofs
  for development. `--chunk-size` bounds each independently checked fragment; the default is
  8,000 search nodes. Neither script updates `Cslib.lean`. Run `lake exe mk_all` after adding modules,
  then perform the normal build, test and lint validation. JSON files are reproducible intermediates
  and need not be committed.

  The search follows the partial-assignment methods in Jipsen's
  [findra3.p](https://math.chapman.edu/~jipsen/relalg/ra1/findra3.p) and
  [findra4.p](https://math.chapman.edu/~jipsen/relalg/ra1/findra4.p).
  It chooses one Boolean variable for each Peircean cycle orbit, expresses atomic associativity
  as equations between positive Boolean expressions, and propagates forced values. Partial
  lexicographic comparisons eliminate noncanonical atom labellings. Constraints proved true for
  every completion are retired, allowing an entire remaining family to be counted at once.
  Masks store cycle variables and active constraints; their width does not grow as one bit per
  complete assignment.

  Certificate format 3 records splits, forced assignments, cached contradiction reasons, and
  bundles of constraint retirements. Each reason identifies a constraint, its required truth
  value, and sufficient positive and negative assignment masks. Lean validates every reason once
  with the original constraint checker, in independent blocks of 256 entries. Subsequent uses
  check the reason's polarity, active constraint, and two mask inclusions. Consecutive retirements
  share one bundle containing the unions of their constraint and requirement masks. In blocks of
  256 entries, Lean checks each constituent reason's positivity and requirement inclusions, and
  verifies that their constraint masks cover exactly the bundle. Composition witnesses use packed
  index sequences that are decoded only during this validation. Blocks of 32 sequences carry
  their own field widths, keeping both short and long witnesses compact. Each subsequent bundle use
  checks three mask inclusions and retires the whole constraint mask at once. This removes more than
  half a million search steps from `I1S5N0`. Formats 1 and 2 are obsolete; regenerate old JSON with
  `count.py` before rendering it. Unknown versions are also rejected.

  Generated proofs are divided into bounded checks with exact boundary-state references,
  so that the kernel need not retain the reduction of the whole search at once. Identical certificate
  subtrees share syntax declarations. Numeric reference records contain only states and counts;
  separate opaque proofs establish their validity before the final count can be concluded.
  A generic equality-transport lemma assembles these proofs without reducing the finite-set
  definition of model counts at concrete states. A 35-variable regression guards this boundary.
  Permutations use packed natural-number fields. Reason and bundle records are packed in blocks
  of 32, with balanced lookup between blocks; equation lookups also use balanced dispatch.
  The `nat_lit%` elaborator turns decimal strings into ordinary natural-number literals, allowing
  large data constants to span source lines without adding parsing or arithmetic to kernel reduction.
  The `certificate_lit%` elaborator similarly turns compact instruction strings into ordinary
  certificate constructor trees, preserving shared helper declarations. This avoids repeatedly
  parsing and elaborating verbose constructor syntax; the kernel checker traverses the resulting
  trees directly. Both elaborators produce data only and do not establish any proof. A proved byte
  population table accelerates the count of free variables. Associativity coverage is also checked
  in small blocks.
  Generated data definitions explicitly use `noncomputable def` to avoid emitting runtime code;
  the kernel still reduces and checks every certificate. The generated rows disable asynchronous
  elaboration: thousands of dependent proof tasks otherwise create excessive worker threads and
  scheduling overhead. Independent rows can still be built concurrently by Lake.
  Lean verifies the cycle basis, the complete
  associativity equation cover, the atom-renaming group and its action, and every search step. The general
  counting theorem identifies the resulting canonical masks with relation-algebra isomorphism
  classes. Each row exports `count : isomorphismClassCount symmetric pairs = N`.

  The C++ search, Python validation, JSON counts and rendering are untrusted. `--verify` is an
  independent development check; only the generated kernel-checked Lean proofs establish the
  count theorems. Their statements concern isomorphism classes and do not assert representability.

  Measurements on 2026-10-07 used Lean 4.35.0-rc3 on an AMD Ryzen AI 5 PRO 340
  (6 cores, 12 threads), with 86 GiB usable RAM. The acceptance command was:

  ```bash
  lake build --wfail --iofail Cslib.Foundations.RelationAlgebra.Catalogue.Counts.I1S5N0
  ```

  Dependencies were cached, but every `I1S5N0.*` artifact under both `.lake/build/lib/lean/`
  and `.lake/build/ir/` was removed before each run. These are complete isolated row builds,
  including elaboration, kernel checking and output generation. No other Lean build or benchmark
  ran concurrently. Source hashes were recorded to verify that repeated runs used identical code.

  | Fresh build | Wall time | User CPU | System CPU | Peak child RSS |
  | --- | ---: | ---: | ---: | ---: |
  | 1 | 536.66 s (8 min 56.66 s) | 533.63 s | 3.41 s | 5,593,892 KiB (5.33 GiB) |
  | 2 | 547.13 s (9 min 7.13 s) | 543.89 s | 3.65 s | 5,597,516 KiB (5.34 GiB) |

  Both fresh builds passed the 600-second target, with every count checked by the Lean kernel.

  GNU `time -v` reports peak memory for the largest child process, rather than aggregate memory
  across Lake and other processes. These measurements apply to the hardware and cache conditions
  above; they are not timing guarantees for other machines.

  The generated public theorems establish the following counts:

  | Row | Signature | Isomorphism classes |
  | --- | --- | ---: |
  | `I1S0N2` | ⟨1, 0, 2⟩ | 83 |
  | `I1S2N1` | ⟨1, 2, 1⟩ | 1,316 |
  | `I1S4N0` | ⟨1, 4, 0⟩ | 3,013 |
  | `I1S1N2` | ⟨1, 1, 2⟩ | 47,965 |
  | `I1S3N1` | ⟨1, 3, 1⟩ | 988,464 |
  | `I1S5N0` | ⟨1, 5, 0⟩ | 3,849,920 |
