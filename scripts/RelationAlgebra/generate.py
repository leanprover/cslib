#!/usr/bin/env python3
# Copyright (c) 2026 Chris Henson. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Chris Henson

"""Reproduce the five-atom catalogues I1S2N1 and I1S4N0.

The C++ enumerator provides candidates and witnesses. Independent Python checks
validate every rejected mask, every renaming witness, and every canonical model.
The emitted Lean definitions still require kernel-checked proofs; these scripts
are not part of Lean's trusted computing base. See scripts/README.md for usage.
"""

import argparse
import array
from collections import Counter
import itertools
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile


ROWS = {"I1S2N1": (2, 1, 1316, 3720), "I1S4N0": (4, 0, 3013, 63673)}
CATALOGUE = Path("Cslib/Foundations/RelationAlgebra/Catalogue")
SOURCE_URL = "https://www1.chapman.edu/~jipsen/gap/ramaddux.html"
PROGRAM_URL = "https://math.chapman.edu/~jipsen/relalg/ra/findra.p"


def require(condition, message):
    """Keep certificate validation enabled even when Python runs with -O."""
    if not condition:
        raise ValueError(message)


def cycle_orbit(triple, converse):
    a, b, c = triple
    return {
        (a, b, c),
        (converse[a], c, b),
        (c, converse[b], a),
        (converse[b], converse[a], converse[c]),
        (b, converse[c], converse[a]),
        (converse[c], a, converse[b]),
    }


def table_index(a, b, c):
    return (a * 5 + b) * 5 + c


def row_specification(j, k):
    converse = list(range(5))
    for i in range(k):
        a, b = j + 2 * i + 1, j + 2 * i + 2
        converse[a], converse[b] = b, a
    triples = itertools.product(range(1, 5), repeat=3)
    representatives = sorted({min(cycle_orbit(t, converse)) for t in triples})
    permutations = [
        (0,) + p
        for p in itertools.permutations(range(1, 5))
        if all(p[converse[a] - 1] == converse[p[a - 1]] for a in range(1, 5))
    ]
    require(len(representatives) == (16 if k else 20), "unexpected cycle count")
    require(len(permutations) == (4 if k else 24), "unexpected permutation count")
    require(permutations[0] == tuple(range(5)), "identity must be the first permutation")
    return converse, representatives, permutations


def write_specification(path, j, k, representatives, permutations):
    lines = [f"{j} {k} {len(representatives)}"]
    lines.extend(" ".join(map(str, triple)) for triple in representatives)
    lines.append(str(len(permutations)))
    lines.extend(" ".join(map(str, p)) for p in permutations)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def enumerate_row(executable, temporary, row):
    j, k, expected_models, expected_associative = ROWS[row]
    converse, representatives, permutations = row_specification(j, k)
    specification = temporary / f"{row}.txt"
    result_path = temporary / f"{row}.bin"
    write_specification(specification, j, k, representatives, permutations)
    subprocess.run([str(executable), str(specification), str(result_path)], check=True)
    results = array.array("I")
    require(results.itemsize == 4, "this platform does not have 32-bit unsigned int")
    results.frombytes(result_path.read_bytes())
    if sys.byteorder != "little":
        results.byteswap()

    cycle_count = len(representatives)
    permutation_count = len(permutations)
    require(len(results) == 1 << cycle_count, "incomplete enumeration output")
    orbits = [cycle_orbit(t, converse) for t in representatives]
    lookup = {t: i for i, orbit in enumerate(orbits) for t in orbit}
    require(len(lookup) == sum(map(len, orbits)) == 64, "cycle orbits do not partition")
    orbit_codes = [sum(1 << table_index(*t) for t in orbit) for orbit in orbits]
    identity_code = sum(
        1 << table_index(a, b, c)
        for a, b, c in itertools.product(range(5), repeat=3)
        if (a == 0 and b == c) or (b == 0 and a == c) or (c == 0 and b == converse[a])
    )
    rename_orbits = [
        [lookup[tuple(p[x] for x in t)] for t in representatives] for p in permutations
    ]
    valid = [mask for mask, result in enumerate(results) if not result >> 31]
    canonical = sorted({results[mask] & ((1 << 20) - 1) for mask in valid})
    require(len(canonical) == expected_models, f"{row}: unexpected isomorphism count")
    require(len(valid) == expected_associative, f"{row}: unexpected labelled count")
    model_indices = {mask: i for i, mask in enumerate(canonical)}

    tables = [identity_code] * len(results)
    for mask in range(1, len(results)):
        low = mask & -mask
        tables[mask] = tables[mask ^ low] | orbit_codes[low.bit_length() - 1]

    witnesses, invalid = [], []
    for mask, result in enumerate(results):
        if result >> 31:
            quadruple = result & 0x7FFFFFFF
            require(quadruple < 625, f"{row}: invalid counterexample encoding")
            a, b, c, d = quadruple // 125, quadruple // 25 % 5, quadruple // 5 % 5, quadruple % 5
            invalid.append([mask, a, b, c, d])
            # Check the existential associativity conditions directly, independently
            # of the C++ enumerator's unions of product bitsets.
            code = tables[mask]
            left = any(
                (code >> table_index(a, b, u)) & 1 and (code >> table_index(u, c, d)) & 1
                for u in range(5)
            )
            right = any(
                (code >> table_index(b, c, u)) & 1 and (code >> table_index(a, u, d)) & 1
                for u in range(5)
            )
            require(left != right, f"{row}: false counterexample for mask {mask}")
        else:
            target, permutation = result & ((1 << 20) - 1), result >> 20
            require(permutation < permutation_count, f"{row}: invalid permutation index")
            image = sum(
                1 << rename_orbits[permutation][i]
                for i in range(cycle_count) if mask >> i & 1
            )
            require(image == target, f"{row}: incorrect renaming for mask {mask}")
            witnesses.append([mask, model_indices[target], permutation])

    for mask in canonical:
        code = tables[mask]
        product = [[code >> table_index(a, b, 0) & 31 for b in range(5)] for a in range(5)]
        for a, b, c in itertools.product(range(5), repeat=3):
            left = right = 0
            for u in range(5):
                if product[a][b] >> u & 1:
                    left |= product[u][c]
                if product[b][c] >> u & 1:
                    right |= product[a][u]
            require(left == right, f"{row}: nonassociative canonical model {mask}")
        minimum = min(
            sum(1 << p[i] for i in range(cycle_count) if mask >> i & 1)
            for p in rename_orbits
        )
        require(mask == minimum, f"{row}: nonminimal canonical mask {mask}")

    orbit_sizes = Counter(w[1] for w in witnesses)
    return {
        "schema_version": 1,
        "j": j, "k": k, "atoms": 5,
        "model_count": len(canonical), "cycle_count": cycle_count,
        "mask_count": len(results), "associative_count": len(valid),
        "permutation_count": permutation_count,
        "reps": representatives, "converse": converse,
        "orbit_sizes": list(map(len, orbits)), "orbit_codes": list(map(str, orbit_codes)),
        "identity_code": str(identity_code), "canonical_masks": canonical,
        "table_codes": [str(tables[mask]) for mask in canonical],
        "renames": permutations, "rename_orbits": rename_orbits,
        "associative_masks": valid, "witnesses": witnesses, "invalid_witnesses": invalid,
        "distributions": {
            "models_by_cycle_count": dict(sorted(Counter(m.bit_count() for m in canonical).items())),
            "labeled_by_cycle_count": dict(sorted(Counter(m.bit_count() for m in valid).items())),
            "models_by_orbit_size": dict(sorted(Counter(orbit_sizes.values()).items())),
            "models_by_automorphism_size": dict(sorted(Counter(
                permutation_count // size for size in orbit_sizes.values()).items())),
            "distinct_invalid_quads": len({tuple(w[1:]) for w in invalid}),
        },
        "numbering": (
            "One-based ascending canonical cycle mask; each canonical mask is the least image "
            "under all identity- and converse-preserving atom permutations. Basis is sorted "
            "lexicographically least Peircean-orbit representatives. This is not Maddux numbering."
        ),
        "source_url": SOURCE_URL, "program_url": PROGRAM_URL,
        "witness_convention": (
            "Each [mask,model,rename] maps source mask to canonical model using renames[rename]; "
            "model and rename indices are zero-based. Invalid [mask,a,b,c,d] witnesses "
            "((a*b)*c) membership d differing from (a*(b*c)) membership d."
        ),
    }


def render_entries(data):
    """Yield relative paths and deterministic source text, without writing files."""
    j, k = data["j"], data["k"]
    row = f"I1S{j}N{k}"
    names, atoms = {}, {}
    for i in range(j):
        names[i + 1], atoms[i + 1] = chr(97 + i), f".inl {i}"
    for i in range(k):
        for converse in range(2):
            code = j + 2 * i + converse + 1
            names[code] = chr(97 + j + i) + ("'" if converse else "")
            atoms[code] = f".inr ({i}, {str(bool(converse)).lower()})"
    for ordinal, (mask, table_code) in enumerate(
        zip(data["canonical_masks"], data["table_codes"]), start=1
    ):
        module = f"Ra{ordinal:04d}"
        triples = [rep for i, rep in enumerate(data["reps"]) if mask >> i & 1]
        used = sorted({a for triple in triples for a in triple})
        lets = "\n".join(f"  let {names[a]} : DiversityAtom {j} {k} := {atoms[a]}" for a in used)
        terms = ["(" + ", ".join(names[a] for a in triple) + ")" for triple in triples]
        lines, line = [], "  {"
        for i, term in enumerate(terms):
            token = term + ("," if i + 1 < len(terms) else "}")
            if len(line) + len(token) > 96:
                lines.append(line.rstrip())
                line = "    "
            line += token + (" " if i + 1 < len(terms) else "")
        lines.append(line if terms else line + "}")
        cycle_set = "\n".join(lines)
        source = f'''/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles

/-!
# Catalogue algebra ⟨1, {j}, {k}⟩, number {ordinal}

The ⟨1, {j}, {k}⟩ count appears in
[Jipsen's catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
This entry uses canonical cycle mask `{mask}`. Our numbering orders the least masks under
atom renaming increasingly; it is independent of the source's numbering for smaller rows.
The cycle basis consists of the lexicographically least triple in each Peircean orbit,
ordered by `Atom.code`. Identity cycles are supplied by `cycleClosure`.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.{row}.{module}

/-- The diversity cycles of this canonical representative. -/
def cycles : Finset (Cycle {j} {k}) :=
{lets}
{cycle_set}

/-- The numeric encoding used by the catalogue's classification certificate. -/
theorem tableCode_eq : tableCode cycles = {table_code} := by
  decide +kernel

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable {j} {k} where
  cycles := cycles
  associative := atomCompositionAssociative_of_assocCheck (by
    rw [tableCode_eq]
    decide +kernel)

/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table

/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 {j} {k} :=
  Complex.hasSignature table

/-- Atomic multiplication is characterized by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom {j} {k}) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z :=
  Complex.atom_le_mul_iff table x y z

end Cslib.RelationAlgebra.Catalogue.{row}.{module}
'''
        yield CATALOGUE / row / f"{module}.lean", source


def renamed_profiles(data):
    """The profile of each canonical model under each listed atom renaming."""
    return [
        [sum(((mask >> q) & 1) << i for i, q in enumerate(permutation))
         for permutation in data["rename_orbits"]]
        for mask in data["canonical_masks"]
    ]


def process_sources(sources, output_root, check, patterns):
    """Write or compare rendered sources and reject stale files in owned patterns."""
    rendered = list(sources)
    expected = {path for path, _ in rendered}
    actual = {path.relative_to(output_root)
              for pattern in patterns for path in output_root.glob(str(pattern))}
    failures = [f"unexpected file: {output_root / path}" for path in sorted(actual - expected)]
    for relative, source in rendered:
        path = output_root / relative
        if check:
            if not path.is_file():
                failures.append(f"missing file: {path}")
            elif path.read_text(encoding="utf-8") != source:
                failures.append(f"different contents: {path}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source, encoding="utf-8")
    if failures:
        raise ValueError("\n".join(failures))
    return len(rendered)


def process_entries(data, output_root, check):
    row = f'I1S{data["j"]}N{data["k"]}'
    count = process_sources(render_entries(data), output_root, check,
                            [CATALOGUE / row / "Ra*.lean"])
    print(f'{row}: {"checked" if check else "generated"} {count} entries', flush=True)


def process_classifications(data, output_root, check):
    # The renderers also import the shared helpers above, so load them only when
    # requested, after this module's definitions are available.
    from coverage import render_coverage
    from rows import render_row

    row = f'I1S{data["j"]}N{data["k"]}'
    sources = list(render_row(row, data).items()) + list(render_coverage(data))
    patterns = [CATALOGUE / f"{row}.lean", CATALOGUE / row / "Data.lean",
                CATALOGUE / row / "Models*.lean", CATALOGUE / row / "Coverage*.lean"]
    count = process_sources(sources, output_root, check, patterns)
    print(f'{row}: {"checked" if check else "generated"} {count} classification modules', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--row", choices=ROWS, action="append", help="row to process; default: both")
    parser.add_argument("--check", action="store_true", help="compare sources without rewriting them")
    parser.add_argument("--include-classifications", action="store_true",
                        help="also process model dispatch, row proofs, and coverage certificates")
    parser.add_argument("--output-root", type=Path, default=Path(__file__).resolve().parents[2],
                        help="repository root receiving generated Lean entries")
    parser.add_argument("--data-dir", type=Path, help="also save reproducible JSON certificate data")
    parser.add_argument("--data-only", action="store_true", help="save data without rendering Lean")
    parser.add_argument("--cxx", default=os.environ.get("CXX", "c++"), help="C++ compiler command")
    args = parser.parse_args()
    if args.check and (args.data_dir or args.data_only):
        parser.error("--check cannot be combined with data output options")
    if args.data_only and not args.data_dir:
        parser.error("--data-only requires --data-dir")
    if args.data_only and args.include_classifications:
        parser.error("--data-only cannot be combined with --include-classifications")
    try:
        with tempfile.TemporaryDirectory(prefix="cslib-ra-enumeration-") as directory:
            temporary = Path(directory)
            executable = temporary / "enumerate"
            subprocess.run(shlex.split(args.cxx) + [
                "-std=c++20", "-O3", "-Wall", "-Wextra",
                str(Path(__file__).with_name("enumerate.cpp")), "-o", str(executable),
            ], check=True)
            for row in dict.fromkeys(args.row or ROWS):
                data = enumerate_row(executable, temporary, row)
                print(f'{row}: verified {data["associative_count"]} associative masks '
                      f'and {data["model_count"]} isomorphism classes', flush=True)
                if args.data_dir:
                    args.data_dir.mkdir(parents=True, exist_ok=True)
                    path = args.data_dir / f"cslib-{row.lower()}-data.json"
                    path.write_text(json.dumps(data, separators=(",", ":")) + "\n", encoding="utf-8")
                    print(f"Data: {path}", flush=True)
                if not args.data_only:
                    process_entries(data, args.output_root, args.check)
                    if args.include_classifications:
                        process_classifications(data, args.output_root, args.check)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
