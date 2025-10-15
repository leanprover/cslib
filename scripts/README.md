# Scripts for working on cslib

This directory contains miscellaneous scripts that are useful for working on or with cslib.
When adding a new script, please make sure to document it here, so other readers have a chance
to learn about it as well!

## Current scripts and their purpose

**Documentation generation**
- `gendocs.sh`
  Generates the documentation for cslib using `lake`.

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
