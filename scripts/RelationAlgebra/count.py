#!/usr/bin/env python3
# Copyright (c) 2026 Chris Henson. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Chris Henson

"""Generate compact, untrusted counting certificates for integral relation algebras.

Run from the repository root. Python 3.10 and a C++20 compiler are required;
there are no third-party Python or network dependencies. The C++ search uses
partial cycle assignments, propagation, symmetry pruning, and bulk counting.
Each output tree consists of accept, reject, split, forced-assignment, and
simplification nodes.
Only an independent Lean proof checking the output establishes a theorem.

Examples:
  python3 scripts/RelationAlgebra/count.py --row I1S1N2
  python3 scripts/RelationAlgebra/count.py --data-dir /tmp/ra-counts
  python3 scripts/RelationAlgebra/count.py --row I1S1N2 --verify

JSON format 3 uses Pascal's cycle order, with the lexicographically least triple
as each orbit representative. A DNF is a list of natural-number monomial masks;
mask zero denotes true, and an empty list denotes false. Equation entries are
[leftDNF, rightDNF, sourceQuadruple]. All atom quadruples, including identity,
are covered by equation_cover in lexicographic order; -1 means a tautology.
Each cycle permutation lists preimages, so bit i of the renamed assignment is
bit permutation[i] of the original assignment. Permutations include identity.

Nodes are stored in postorder as [tag, variable, value, witness, left, right,
count]. Tags are accept=0, reject=1, split=2, force=3, simplify=4. Split children
mean false and true; force and simplify store their sole child in left. Witnesses
in reject and force nodes index cached reasons [constraint, positive, onReq, offReq]. Constraints index
equations first, followed by permutations; positive reasons settle a constraint,
while negative reasons refute it. A force witness rejects the
opposite assignment under its parent's partial assignment. A simplification
witness indexes a bundle [reasonIDs, constraintsMask, onReq, offReq], which combines
consecutive positive reasons and removes all its constraints at once. Acceptance
requires no active constraints.
Counts are redundant
metadata for checking and rendering; they are never additional assumptions.
"""

from __future__ import annotations

import argparse
import itertools
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import time


ROWS = {
    "I1S0N0": (0, 0, 1),
    "I1S1N0": (1, 0, 2),
    "I1S0N1": (0, 1, 3),
    "I1S2N0": (2, 0, 7),
    "I1S1N1": (1, 1, 37),
    "I1S3N0": (3, 0, 65),
    "I1S0N2": (0, 2, 83),
    "I1S2N1": (2, 1, 1316),
    "I1S4N0": (4, 0, 3013),
    "I1S1N2": (1, 2, 47965),
    "I1S3N1": (3, 1, 988464),
    "I1S5N0": (5, 0, 3849920),
}


def validate_problem(data: dict) -> None:
    """Reconstruct the entire problem independently of the C++ preprocessing."""
    s, k, n = data["symmetric"], data["pairs"], data["atoms"]
    if data.get("format") != 3:
        raise ValueError("unsupported certificate format; regenerate with count.py")
    if n != 1 + s + 2 * k or not 1 <= n <= 6:
        raise ValueError("invalid signature")
    converse = list(range(n))
    for pair in range(k):
        a, b = 1 + s + 2 * pair, 2 + s + 2 * pair
        converse[a], converse[b] = b, a

    def orbit(a: int, b: int, c: int) -> set[tuple[int, int, int]]:
        return {
            (a, b, c), (converse[a], c, b), (c, converse[b], a),
            (converse[b], converse[a], converse[c]),
            (b, converse[c], converse[a]), (converse[c], a, converse[b]),
        }

    slots = {}
    for i, representative in enumerate(data["basis"]):
        if any(a not in range(1, n) for a in representative):
            raise ValueError("basis contains an identity or out-of-range atom")
        triples = orbit(*representative)
        if tuple(representative) != min(triples) or any(t in slots for t in triples):
            raise ValueError("invalid or repeated Peircean orbit")
        slots.update((triple, 1 << i) for triple in triples)
    if len(slots) != (n - 1) ** 3:
        raise ValueError("the basis does not cover all diversity triples")

    def cycle(a: int, b: int, c: int) -> int | None:
        if a and b and c:
            return slots[a, b, c]
        if ((a == 0 and b == c) or (b == 0 and a == c)
                or (c == 0 and b == converse[a])):
            return 0
        return None

    def side(quad: tuple[int, int, int, int], left: bool) -> list[int]:
        a, b, c, d = quad
        terms = set()
        for t in range(n):
            x, y = ((cycle(a, b, t), cycle(t, c, d)) if left else
                    (cycle(b, c, t), cycle(a, t, d)))
            if x is not None and y is not None:
                terms.add(x | y)
        return [0] if 0 in terms else sorted(terms)

    all_quads = list(itertools.product(range(n), repeat=4))
    if len(data["equation_cover"]) != len(all_quads):
        raise ValueError("equation cover has the wrong length")
    for quad, index in zip(all_quads, data["equation_cover"]):
        expected = sorted((side(quad, True), side(quad, False)))
        if index == -1:
            if expected[0] != expected[1]:
                raise ValueError("a nontrivial associativity equation was omitted")
        elif not 0 <= index < len(data["equations"]):
            raise ValueError("invalid equation-cover index")
        elif data["equations"][index][:2] != expected:
            raise ValueError("incorrect associativity equation")
    for left, right, source in data["equations"]:
        if [left, right] != sorted((side(tuple(source), True), side(tuple(source), False))):
            raise ValueError("incorrect source quadruple")

    expected_permutations = [
        (0,) + p for p in itertools.permutations(range(1, n))
        if all(((0,) + p)[converse[a]] == converse[((0,) + p)[a]] for a in range(n))
    ]
    if data["atom_permutations"] != [list(p) for p in expected_permutations]:
        raise ValueError("atom permutations do not cover exactly the required group")
    if len(data["permutations"]) != len(expected_permutations):
        raise ValueError("cycle permutations have the wrong length")
    for atom_perm, cycle_perm in zip(expected_permutations, data["permutations"]):
        expected = [0] * len(data["basis"])
        for i, (a, b, c) in enumerate(data["basis"]):
            image_bit = slots[atom_perm[a], atom_perm[b], atom_perm[c]]
            expected[image_bit.bit_length() - 1] = i
        if cycle_perm != expected:
            raise ValueError("incorrect induced cycle permutation")


def constraint_status(data: dict, witness: int, on: int, off: int) -> int:
    """Independently evaluate the partial constraint: false=-1, unknown=0, true=1."""
    equations, permutations = data["equations"], data["permutations"]
    if not 0 <= witness < len(equations) + len(permutations):
        raise ValueError("invalid constraint index")
    if witness < len(equations):
        left, right, _ = equations[witness]
        def bounds(terms: list[int]) -> tuple[bool, bool]:
            return (any(term & on == term for term in terms),
                    any(term & off == 0 for term in terms))
        lo_l, hi_l = bounds(left)
        lo_r, hi_r = bounds(right)
        if (lo_l and not hi_r) or (lo_r and not hi_l):
            return -1
        if (lo_l and lo_r) or (not hi_l and not hi_r):
            return 1
        return 0
    p = permutations[witness - len(equations)]
    possible = {0}
    for i in reversed(range(len(data["basis"]))):
        if i == p[i] or 0 not in possible:
            continue
        possible.remove(0)
        left = [1] if on >> i & 1 else [0] if off >> i & 1 else [0, 1]
        right = [1] if on >> p[i] & 1 else [0] if off >> p[i] & 1 else [0, 1]
        possible.update(a - b for a in left for b in right)
    return 1 if 1 not in possible else -1 if possible == {1} else 0


def cache_reasons(data: dict) -> None:
    """Replace raw C++ witnesses by canonical, reusable sufficient subcubes.

    This extraction is untrusted. verify_tree separately checks every cached
    reason using constraint_status and checks its inclusion at every use.
    """
    if data["format"] != 1:
        raise ValueError("reason extraction requires the raw search format")
    q, r = len(data["equations"]), len(data["basis"])

    def reason(witness: int, positive: bool, on: int, off: int) -> tuple:
        if witness >= q:
            on_req = off_req = 0
            for i in reversed(range(r)):
                j = data["permutations"][witness - q][i]
                if i == j:
                    continue
                first = (off if positive else on) >> i & 1
                second = (on if positive else off) >> j & 1
                if not (first or second):
                    raise ValueError("raw symmetry witness is not decisive")
                if first:
                    if positive:
                        off_req |= 1 << i
                    else:
                        on_req |= 1 << i
                if second:
                    if positive:
                        on_req |= 1 << j
                    else:
                        off_req |= 1 << j
                if first and second:
                    break
            return witness, positive, on_req, off_req
        left, right, _ = data["equations"][witness]
        left_true = [term for term in left if term & on == term]
        right_true = [term for term in right if term & on == term]
        order = lambda mask: (mask.bit_count(), mask)
        if left_true and right_true:
            on_req = min((a | b for a in left_true for b in right_true), key=order)
            return witness, positive, on_req, 0
        false_terms = right if left_true else left if right_true else left + right
        on_req = min(left_true or right_true, key=order) if left_true or right_true else 0
        pending = [term & off for term in false_terms]
        if not all(pending):
            raise ValueError("raw equation witness has an undecided side")
        off_req = 0
        while pending:
            coverage = {}
            for term in pending:
                while term:
                    bit = term & -term
                    term -= bit
                    coverage[bit] = coverage.get(bit, 0) + 1
            bit = max(coverage, key=lambda bit: (coverage[bit], -bit))
            off_req |= bit
            pending = [term for term in pending if not term & bit]
        return witness, positive, on_req, off_req

    nodes = data["nodes"]
    node_reasons = [None] * len(nodes)
    unique = set()
    pending = [(data["root"], 0, 0)]
    while pending:
        index, on, off = pending.pop()
        tag, variable, value, witness, left, right, _ = nodes[index]
        bit = 1 << variable
        if tag in (1, 3, 4):
            rejected_on, rejected_off = on, off
            if tag == 3:
                if value:
                    rejected_off |= bit
                else:
                    rejected_on |= bit
            entry = reason(witness, tag == 4, rejected_on, rejected_off)
            node_reasons[index] = entry
            unique.add(entry)
        if tag == 2:
            pending.extend([(left, on, off | bit), (right, on | bit, off)])
        elif tag == 3:
            pending.append((left, on | bit if value else on, off if value else off | bit))
        elif tag == 4:
            pending.append((left, on, off))
    entries = sorted(unique)
    indices = {entry: i for i, entry in enumerate(entries)}
    for node, entry in zip(nodes, node_reasons):
        if entry is not None:
            node[3] = indices[entry]
    data["reasons"] = [list(entry) for entry in entries]
    data["format"] = 2


def cache_bundles(data: dict) -> None:
    """Collapse maximal retirement chains into checked unions of cached reasons."""
    if data["format"] != 2:
        raise ValueError("bundle extraction requires cached reasons")
    original, reasons = data["nodes"], data["reasons"]
    nodes, sequences = [], set()

    def visit(index: int) -> int:
        node = list(original[index])
        if node[0] == 4:
            sequence = []
            cursor = index
            while original[cursor][0] == 4:
                sequence.append(original[cursor][3])
                cursor = original[cursor][4]
            node[3] = tuple(sorted(sequence))
            sequences.add(node[3])
            node[4] = visit(cursor)
        elif node[0] in (2, 3):
            node[4] = visit(node[4])
            if node[0] == 2:
                node[5] = visit(node[5])
        nodes.append(node)
        return len(nodes) - 1

    root = visit(data["root"])
    sequences = sorted(sequences)
    indices = {sequence: i for i, sequence in enumerate(sequences)}
    bundles = []
    for sequence in sequences:
        constraints = on_req = off_req = 0
        for index in sequence:
            constraint, positive, on, off = reasons[index]
            if not positive:
                raise ValueError("retirement chain contains a negative reason")
            constraints |= 1 << constraint
            on_req |= on
            off_req |= off
        bundles.append([list(sequence), constraints, on_req, off_req])
    for node in nodes:
        if node[0] == 4:
            node[3] = indices[node[3]]
    data.update(nodes=nodes, root=root, bundles=bundles, format=3)


def verify_tree(data: dict) -> int:
    """Check every reason, use and family with an independent Python evaluator."""
    if data.get("format") != 3:
        raise ValueError("unsupported certificate format; regenerate with count.py")
    equations, permutations, nodes = data["equations"], data["permutations"], data["nodes"]
    variables = len(data["basis"])
    full = (1 << variables) - 1
    reasons = data["reasons"]
    for entry in reasons:
        if len(entry) != 4:
            raise ValueError("malformed cached reason")
        witness, positive, on_req, off_req = entry
        if type(positive) is not bool or not (0 <= on_req <= full and 0 <= off_req <= full):
            raise ValueError("invalid reason flag or requirements")
        if on_req & off_req:
            raise ValueError("inconsistent cached reason")
        if constraint_status(data, witness, on_req, off_req) != (1 if positive else -1):
            raise ValueError("incorrect cached reason")
    if "bundles" not in data:
        raise ValueError("missing retirement bundles; regenerate with count.py")
    bundles = data["bundles"]
    for entry in bundles:
        if len(entry) != 4 or not isinstance(entry[0], list) or not entry[0]:
            raise ValueError("malformed retirement bundle")
        sequence, constraints, on_req, off_req = entry
        expected_constraints = expected_on = expected_off = 0
        for index in sequence:
            if type(index) is not int or not 0 <= index < len(reasons):
                raise ValueError("invalid bundled-reason index")
            constraint, positive, on, off = reasons[index]
            if not positive:
                raise ValueError("bundle contains a negative reason")
            if expected_constraints >> constraint & 1:
                raise ValueError("bundle repeats a constraint")
            expected_constraints |= 1 << constraint
            expected_on |= on
            expected_off |= off
        if (constraints, on_req, off_req) != (expected_constraints, expected_on, expected_off):
            raise ValueError("incorrect retirement-bundle composition")
        if on_req & off_req:
            raise ValueError("inconsistent retirement bundle")

    def use_reason(index: int, positive: bool, on: int, off: int, active: int) -> int:
        if not 0 <= index < len(reasons):
            raise ValueError("invalid cached-reason index")
        witness, actual, on_req, off_req = reasons[index]
        if actual != positive or not active >> witness & 1:
            raise ValueError("incorrect reason polarity or inactive constraint")
        if on_req & on != on_req or off_req & off != off_req:
            raise ValueError("cached reason does not apply to this assignment")
        return witness

    seen = set()

    def visit(index: int, on: int, off: int, active: int) -> int:
        if not 0 <= index < len(nodes) or index in seen:
            raise ValueError("invalid, repeated, or cyclic certificate node")
        seen.add(index)
        node = nodes[index]
        if len(node) != 7:
            raise ValueError("malformed certificate node")
        tag, variable, value, witness, left, right, count = node
        if tag == 0:
            if active:
                raise ValueError("a bulk family has an unresolved constraint")
            result = 1 << (full & ~(on | off)).bit_count()
        elif tag == 1:
            use_reason(witness, False, on, off, active)
            result = 0
        elif tag in (2, 3):
            if not 0 <= variable < variables or (on | off) >> variable & 1:
                raise ValueError("assignment chooses an invalid or already assigned variable")
            if not left < index or (tag == 2 and not right < index):
                raise ValueError("children must precede their parent")
            bit = 1 << variable
            if tag == 2:
                result = visit(left, on, off | bit, active)
                result += visit(right, on | bit, off, active)
            else:
                if value not in (0, 1):
                    raise ValueError("invalid forced Boolean value")
                rejected = (on, off | bit) if value else (on | bit, off)
                use_reason(witness, False, *rejected, active)
                child = (on | bit, off) if value else (on, off | bit)
                result = visit(left, *child, active)
        elif tag == 4:
            if not left < index:
                raise ValueError("children must precede their parent")
            if not 0 <= witness < len(bundles):
                raise ValueError("invalid retirement-bundle index")
            _, constraints, on_req, off_req = bundles[witness]
            if constraints & active != constraints:
                raise ValueError("bundle retires an inactive constraint")
            if on_req & on != on_req or off_req & off != off_req:
                raise ValueError("retirement bundle does not apply to this assignment")
            result = visit(left, on, off, active ^ constraints)
        else:
            raise ValueError("unknown node tag")
        if count != result:
            raise ValueError("incorrect redundant node count")
        return result

    answer = visit(data["root"], 0, 0, (1 << (len(equations) + len(permutations))) - 1)
    if len(seen) != len(nodes) or answer != data["count"]:
        raise ValueError("unreachable certificate nodes or incorrect root count")
    return answer


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--row", action="append", choices=ROWS, help="signature to count (repeatable)")
    parser.add_argument("--data-dir", type=Path, help="save reproducible certificate JSON in this directory")
    parser.add_argument("--check", action="store_true", help="compare regenerated JSON with --data-dir")
    parser.add_argument("--verify", action="store_true", help="independently check every tree node in Python")
    parser.add_argument("--cxx", default=os.environ.get("CXX", "c++"), help="C++20 compiler command")
    args = parser.parse_args()
    if args.check and args.data_dir is None:
        parser.error("--check requires --data-dir")
    source = Path(__file__).resolve().with_suffix(".cpp")
    with tempfile.TemporaryDirectory(prefix="cslib-ra-count-") as temporary:
        directory = Path(temporary)
        executable = directory / "count"
        subprocess.run([*shlex.split(args.cxx), "-std=c++20", "-O3", "-Wall", "-Wextra",
                        str(source), "-o", str(executable)], check=True)
        for row in args.row or ROWS:
            symmetric, pairs, expected = ROWS[row]
            output = directory / f"{row}.json"
            start = time.perf_counter()
            subprocess.run([str(executable), str(symmetric), str(pairs), str(output)], check=True)
            data = json.loads(output.read_bytes())
            cache_reasons(data)
            cache_bundles(data)
            validate_problem(data)
            raw = (json.dumps(data, separators=(",", ":")) + "\n").encode()
            if data["count"] != expected:
                raise ValueError(f"{row}: computed {data['count']}, expected {expected}")
            if args.verify:
                verify_tree(data)
            if args.data_dir is not None:
                target = args.data_dir / f"{row}.json"
                if args.check:
                    if not target.is_file() or target.read_bytes() != raw:
                        raise ValueError(f"{target}: missing or differs from regenerated certificate")
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(raw)
            print(f"{row}: {data['count']:,} classes; {len(data['nodes']):,} certificate nodes; "
                  f"{len(data['reasons']):,} cached reasons; {len(raw):,} bytes; "
                  f"{time.perf_counter() - start:.3f}s", flush=True)


if __name__ == "__main__":
    main()
