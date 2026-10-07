#!/usr/bin/env python3
# Copyright (c) 2026 Chris Henson. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Chris Henson

"""Render kernel-checked relation-algebra counts from count.py certificates.

The JSON and this renderer are untrusted: generated proofs must elaborate in
Lean. Run from the repository root, for example:

  python3 scripts/RelationAlgebra/count_lean.py --data-dir /tmp/ra-counts --row I1S0N2

Certificate expressions share identical subtrees and use independently checked
fragments. The default selection is the six committed five- and six-atom rows.
--metadata-only emits the orbit basis and equation-coverage proofs for debugging
the problem encoding independently of the counting certificate.
"""

from __future__ import annotations

import argparse
from collections import Counter
import itertools
import json
from pathlib import Path

from count import ROWS, validate_problem


HEADER = """/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

"""
CATALOGUE = Path("Cslib/Foundations/RelationAlgebra/Catalogue/Counts")
DEFAULT_ROWS = [row for row, (symmetric, pairs, _) in ROWS.items()
                if symmetric + 2 * pairs >= 4]


def diversity_atom(symmetric: int, code: int) -> str:
    if code <= 0:
        raise ValueError("identity is not a diversity atom")
    if code <= symmetric:
        return f".inl {code - 1}"
    pair, converse = divmod(code - symmetric - 1, 2)
    return f".inr ({pair}, {str(bool(converse)).lower()})"


def triple(symmetric: int, atoms: list[int]) -> str:
    return "(" + ", ".join(diversity_atom(symmetric, atom) for atom in atoms) + ")"


def sequence(items: list[str], opening: str = "#[", closing: str = "]",
             indent: int = 2, width: int = 94) -> str:
    """Wrap a Lean sequence without splitting individual entries."""
    prefix = " " * indent
    lines = []
    line = prefix + opening
    for index, item in enumerate(items):
        token = item + ("," if index + 1 < len(items) else closing)
        if len(line) + len(token) + 1 > width and line != prefix + opening:
            lines.append(line.rstrip())
            line = prefix + "  "
        line += token + " "
    if not items:
        line += closing
    lines.append(line.rstrip())
    return "\n".join(lines)


def invert(permutation: list[int]) -> list[int]:
    inverse = [0] * len(permutation)
    for source, target in enumerate(permutation):
        inverse[target] = source
    return inverse


def nat_literal(value: int) -> str:
    """Keep large packed integers within the generated source's line-width limit."""
    if value.bit_length() <= 256:
        return str(value)
    # Small conversions also avoid Python's default large-decimal-string limit.
    chunks = []
    while value:
        value, remainder = divmod(value, 10 ** 72)
        chunks.append(str(remainder).zfill(72) if value else str(remainder))
    return '(nat_lit% "' + '\\\n    '.join(reversed(chunks)) + '")'


def balanced_lookup(name: str, result_type: str, entries: list[str], default: str,
                    private: bool = False) -> str:
    """Closed balanced data; index substitution never traverses the whole table."""
    definitions = []
    modifier = "private " if private else ""

    def save(expression: str) -> str:
        child_name = f"{name}TreePart{len(definitions):04d}"
        definitions.append((child_name, expression))
        return child_name

    def body(low: int, high: int) -> tuple[str, int]:
        if high == low:
            return ".empty", 1
        if high - low == 1:
            return f"(.leaf ({entries[low]}))", 1
        middle = (low + high) // 2
        left, left_size = body(low, middle)
        right, right_size = body(middle, high)
        while 1 + left_size + right_size > 255:
            if left_size >= right_size:
                left, left_size = save(left), 1
            else:
                right, right_size = save(right), 1
        return f"(.branch {middle} {left} {right})", 1 + left_size + right_size

    tree, _ = body(0, len(entries))
    definitions.append((name + "Tree", tree))
    source = ""
    for index, (child_name, expression) in enumerate(definitions):
        if index:
            source += "/-- A closed block of balanced numeric lookup data. -/\n"
        source += (f"{modifier}def {child_name} : Search.LookupTree ({result_type}) :=\n"
                   f"  {expression}\n\n")
    source += "/-- Bounded lookup through closed balanced data. -/\n"
    source += f"{modifier}def {name} (i : ℕ) : {result_type} :=\n"
    source += f"  if Nat.blt i {len(entries)} then\n"
    source += f"    Search.LookupTree.get ({default}) {name}Tree i\n"
    source += f"  else {default}\n\n"
    return source


def packed_lookup(name: str, values: list[int], default: int = 0) -> str:
    """Store groups of 32 small fields in literal Nats and dispatch by block."""
    width = max(1, max(values, default=0).bit_length())
    blocks = [sum(value << (width * j) for j, value in enumerate(values[i:i + 32]))
              for i in range(0, len(values), 32)]
    source = "/-- Packed blocks for bounded numeric lookup. -/\n"
    source += balanced_lookup(name + "Blocks", "ℕ", list(map(nat_literal, blocks)), "0")
    source += "/-- A bounded numeric table decoded from packed blocks. -/\n"
    source += f"def {name} (i : ℕ) : ℕ :=\n"
    source += f"  if Nat.blt i {len(values)} then\n"
    source += (f"    Code.field ({name}Blocks (Nat.shiftRight i 5)) "
               f"(Nat.land i 31 * {width}) {width}\n")
    source += f"  else {default}\n\n"
    return source


def adaptive_packed_lookup(name: str, values: list[int], default: int = 0) -> str:
    """Pack variable-length words with a separate field width in each block."""
    maximum_width = max(1, max((value.bit_length() for value in values), default=0))
    header = maximum_width.bit_length()
    blocks = []
    for first in range(0, len(values), 32):
        chunk = values[first:first + 32]
        width = max(1, max(value.bit_length() for value in chunk))
        blocks.append(width | sum(value << (header + offset * width)
                                  for offset, value in enumerate(chunk)))
    source = "/-- Packed blocks with an independent field width stored in each header. -/\n"
    source += balanced_lookup(name + "Blocks", "ℕ", list(map(nat_literal, blocks)), "0")
    source += "/-- Bounded lookup through the adaptive-width packed blocks. -/\n"
    source += f"def {name} (i : ℕ) : ℕ :=\n"
    source += f"  if Nat.blt i {len(values)} then\n"
    source += f"    let block := {name}Blocks (Nat.shiftRight i 5)\n"
    source += f"    let width := Code.field block 0 {header}\n"
    source += f"    Code.field block ({header} + Nat.land i 31 * width) width\n"
    source += f"  else {default}\n\n"
    return source


def wrap_lean(source: str) -> str:
    """Wrap long vectors and constructor expressions without changing tokens."""
    lines = []
    for line in source.splitlines():
        while len(line) > 100:
            split = line.rfind(" ", 0, 96)
            if split <= len(line) - len(line.lstrip()):
                split = line.rfind(")", 0, 96) + 1
            if split <= len(line) - len(line.lstrip()):
                break
            lines.append(line[:split].rstrip())
            line = "    " + line[split:].lstrip()
        lines.append(line)
    return "\n".join(lines) + "\n"


def metadata(data: dict) -> str:
    s, k, n = data["symmetric"], data["pairs"], data["atoms"]
    r, p, q = len(data["basis"]), len(data["permutations"]), len(data["equations"])
    out = "/-- Closed lookup data for representatives of the Peircean orbits. -/\n"
    if r:
        reps = [triple(s, t) for t in data["basis"]]
        out += balanced_lookup("cycleRepValues", f"Cycle {s} {k}", reps, reps[0])
        out += f"""/-- Representatives of the Peircean orbits, in the search's branching order. -/
def cycleReps (i : Fin {r}) : Cycle {s} {k} := cycleRepValues i

"""
    else:
        out += f"def cycleReps : Fin 0 → Cycle {s} {k} := fun i => Fin.elim0 i\n\n"
    out += f"""/-- The basis meets every diversity-cycle orbit. -/
theorem cycleReps_cover : ∀ c : Cycle {s} {k},
    ∃ i, (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (cycleReps i) := by
  decide +kernel

/-- Different basis indices describe disjoint Peircean orbits. -/
theorem cycleReps_distinct : ∀ i l,
    (some (cycleReps i).1, some (cycleReps i).2.1, some (cycleReps i).2.2) ∈
      cycleOrbit (cycleReps l) ↔ i = l := by
  decide +kernel

"""
    # The search stores the preimage action on bits. Inverting the actual atom
    # maps aligns it with Code.permuteProfile's pullback convention.
    renamings = [invert(permutation) for permutation in data["atom_permutations"]]
    for atom in range(1, n):
        out += "/-- Images of one diversity atom under the enumerated renamings. -/\n"
        out += balanced_lookup(f"renameAtom{atom}", f"DiversityAtom {s} {k}",
                               [diversity_atom(s, perm[atom]) for perm in renamings],
                               diversity_atom(s, atom))
    out += f"""/-- All converse-preserving diversity-atom permutations. -/
def renameDiversity (p : Fin {p}) : DiversityAtom {s} {k} → DiversityAtom {s} {k}
"""
    if n == 1:
        out += "  := fun x => Sum.elim Fin.elim0 (fun y => Fin.elim0 y.1) x\n"
    else:
        for atom in range(1, n):
            out += f"  | {diversity_atom(s, atom)} => renameAtom{atom} p\n"
    out += f"""
/-- Extend the diversity permutation by fixing the identity. -/
def rename (p : Fin {p}) : Atom {s} {k} → Atom {s} {k} :=
  Option.map (renameDiversity p)

/-- The atom maps are injective and preserve identity and converse. -/
theorem rename_laws : ∀ p, Function.Injective (rename p) ∧ rename p none = none ∧
    ∀ x, rename p x.converse = (rename p x).converse := by
  decide +kernel

/-- Every possible atom renaming occurs in the finite list. -/
theorem renamings_exhaustive : ∀ f : Atom {s} {k} → Atom {s} {k},
    Function.Injective f → f none = none →
      (∀ x, f x.converse = (f x).converse) → ∃ p : Fin {p}, f = rename p := by
  exact renamings_exhaustive_of_atomPermutations rename (by decide +kernel)

"""
    if r:
        out += "/-- Closed typed lookup data for the induced cycle permutations. -/\n"
        out += balanced_lookup("orbitActionValues", f"Fin {r}",
                               [str(value) for perm in data["permutations"] for value in perm], "0")
        out += f"""/-- The action of an atom renaming on the cycle basis. -/
def orbitAction (p : Fin {p}) (i : Fin {r}) : Fin {r} :=
  orbitActionValues (p.val * {r} + i.val)

"""
    else:
        out += f"""/-- The action of an atom renaming on the empty cycle basis. -/
def orbitAction : Fin {p} → Fin 0 → Fin 0 := fun _ i => Fin.elim0 i

"""
    out += """/-- The stored cycle action agrees with the actual atom maps. -/
theorem orbitAction_spec : ∀ p i,
    (some (renameDiversity p (cycleReps i).1),
      some (renameDiversity p (cycleReps i).2.1),
      some (renameDiversity p (cycleReps i).2.2)) ∈
        cycleOrbit (cycleReps (orbitAction p i)) := by
  decide +kernel

"""

    converse = list(range(n))
    for pair in range(k):
        a, b = 1 + s + 2 * pair, 2 + s + 2 * pair
        converse[a], converse[b] = b, a
    slots = {}
    for i, (a, b, c) in enumerate(data["basis"]):
        for t in [(a, b, c), (converse[a], c, b), (c, converse[b], a),
                  (converse[b], converse[a], converse[c]),
                  (b, converse[c], converse[a]), (converse[c], a, converse[b])]:
            slots[t] = i + 2
    slot_values = []
    for a, b, c in itertools.product(range(n), repeat=3):
        unit = ((a == 0 and b == c) or (b == 0 and a == c)
                or (c == 0 and b == converse[a]))
        slot_values.append(1 if unit else slots.get((a, b, c), 0))
    out += packed_lookup("slotValues", slot_values)
    out += f"""/-- Numeric slots for every atom triple, including forced identity cycles. -/
def slots (a b c : ℕ) : ℕ :=
  slotValues (Code.index {n} a b c)

/-- The slot representation agrees with cycle closure. -/
theorem slots_spec : CycleSlots cycleReps slots := by
  decide +kernel

/-- The distinct atomic associativity equations used by the search. -/
"""
    equation_entries = ["⟨[" + ", ".join(map(str, left)) + "], [" +
                        ", ".join(map(str, right)) + "]⟩"
                        for left, right, _ in data["equations"]]
    out += balanced_lookup("equations", "Search.Equation", equation_entries, "⟨[], []⟩")
    out += "/-- A source quadruple for each retained associativity equation. -/\n"
    out += balanced_lookup("sourceQuads", "Code.Quadruple",
                           ["(" + ", ".join(map(str, quad)) + ")"
                            for _, _, quad in data["equations"]], "(0, 0, 0, 0)")
    out += packed_lookup("equationCoverValues",
                         [q if index == -1 else index for index in data["equation_cover"]], q)
    out += f"""/-- Map every atom quadruple to its retained equation, with a tautology sentinel. -/
def equationCover (a b c d : ℕ) : ℕ :=
  equationCoverValues (((a * {n} + b) * {n} + c) * {n} + d)

"""
    out += f"""/-- Every retained equation comes from atomic associativity. -/
theorem sources_checked :
    Search.sourcesCheck {n} {q} slots equations sourceQuads = true := by
  decide +kernel

private def equationPairCover (a b : ℕ) : Bool :=
  Code.allBelow (fun c => Code.allBelow (fun d =>
    let eqn := Search.compileEquation {n} slots (a, b, c, d)
    eqn.left.beq eqn.right ||
      (Nat.blt (equationCover a b c d) {q} &&
        (equations (equationCover a b c d)).same eqn)) {n}) {n}

"""
    for a, b in itertools.product(range(n), repeat=2):
        out += f"""private theorem equationPairCover_{a}_{b} : equationPairCover {a} {b} = true := by
  decide +kernel

"""
    out += f"""private theorem equationPairCover_all : ∀ a b : Fin {n}, equationPairCover a b = true := by
  intro a b
  fin_cases a <;> fin_cases b
"""
    for a, b in itertools.product(range(n), repeat=2):
        out += f"  · exact equationPairCover_{a}_{b}\n"
    out += f"""
/-- The retained equations cover all associativity conditions, including identity cases. -/
theorem equations_cover_checked :
    Search.equationsCoverCheck {n} {q} slots equations equationCover = true := by
  apply Code.allBelow_eq_true.mpr
  intro a ha
  apply Code.allBelow_eq_true.mpr
  intro b hb
  exact equationPairCover_all ⟨a, ha⟩ ⟨b, hb⟩

"""
    permutation_width = max(1, (r - 1).bit_length())
    permutation_code = sum(value << (permutation_width * (pi * r + i))
                           for pi, perm in enumerate(data["permutations"])
                           for i, value in enumerate(perm))
    out += "/-- All numeric cycle-variable permutations in one literal. -/\n"
    out += f"def permutationCodes : ℕ :=\n  {nat_literal(permutation_code)}\n\n"
    out += f"""/-- Numeric cycle permutations stored as packed, fixed-width fields. -/
def permutations (p i : ℕ) : ℕ :=
  if Nat.blt p {p} && Nat.blt i {r} then
    Code.field permutationCodes ((p * {r} + i) * {permutation_width}) {permutation_width}
  else 0

"""
    out += f"""/-- Numeric permutations implement the certified orbit action. -/
theorem permutations_eq : ∀ p : Fin {p}, ∀ i : Fin {r},
    permutations p i = (orbitAction p i).val := by
  decide +kernel

"""
    return out


def reason_definitions(data: dict, block_size: int = 256) -> str:
    """Validate shared reasons once, in bounded kernel computations."""
    variables = len(data["basis"])
    constraint_width = max(1, (len(data["equations"]) + len(data["permutations"]) - 1).bit_length())
    on_offset = constraint_width + 1
    off_offset = on_offset + variables
    codes = [constraint | (int(positive) << constraint_width) |
             (on << on_offset) | (off << off_offset)
             for constraint, positive, on, off in data["reasons"]]
    out = packed_lookup("reasonCodes", codes)
    out += f"""/-- Decode one cached reason without referring to its validity proof. -/
def reasonData (i : ℕ) : Search.ReasonData :=
  let code := reasonCodes i
  ⟨Code.field code 0 {constraint_width}, Code.bitAt code {constraint_width},
    Code.field code {on_offset} {variables}, Code.field code {off_offset} {variables}⟩

/-- Shared sufficient subcubes for all contradiction and retirement steps. -/
def reasons : Search.ReasonTable where
  size := {len(codes)}
  lookup := reasonData

"""
    blocks = len(codes) // block_size + 1
    for block in range(blocks):
        out += f"""private theorem reasonBlock{block:03d}_checked :
    reasons.checkBlock problem {block_size} {block} = true := by
  decide +kernel

"""
    out += f"""/-- Each reason is checked by the original partial-constraint evaluator. -/
theorem reasons_valid : reasons.Valid problem := by
  apply reasons.valid_of_blocks problem {block_size} (by decide)
  intro block hblock
  have h : ∀ i : Fin {blocks}, reasons.checkBlock problem {block_size} i = true := by
    intro i
    fin_cases i
"""
    for block in range(blocks):
        out += f"    · exact reasonBlock{block:03d}_checked\n"
    out += "  exact h ⟨block, hblock⟩\n\n"
    return out


def bundle_definitions(data: dict, block_size: int = 256) -> str:
    """Check cached unions once, then retire each whole chain with mask operations."""
    variables = len(data["basis"])
    constraints = len(data["equations"]) + len(data["permutations"])
    bundles = data["bundles"]
    codes = [mask | (on << constraints) | (off << (constraints + variables))
             for _, mask, on, off in bundles]
    out = packed_lookup("bundleCodes", codes)
    reason_width = max(1, (len(data["reasons"]) - 1).bit_length())
    length_width = max(1, max((len(sequence) for sequence, *_ in bundles), default=0).bit_length())
    sequence_codes = [len(sequence) | sum(index << (length_width + i * reason_width)
                                        for i, index in enumerate(sequence))
                      for sequence, *_ in bundles]
    out += adaptive_packed_lookup("bundleReasonCodes", sequence_codes)
    out += f"""/-- The positive reasons used to validate one cached retirement bundle. -/
def bundleReasons (i : ℕ) : List ℕ :=
  let code := bundleReasonCodes i
  Search.decodeBundleIndices {reason_width} (Code.field code 0 {length_width})
    (Nat.shiftRight code {length_width})

"""
    out += f"""/-- Decode the masks used by one retirement step. -/
def bundleData (i : ℕ) : Search.BundleData :=
  let code := bundleCodes i
  ⟨Code.field code 0 {constraints}, Code.field code {constraints} {variables},
    Code.field code {constraints + variables} {variables}⟩

/-- Consecutive retirements certified by unions of independently checked reasons. -/
def bundles : Search.BundleTable where
  size := {len(bundles)}
  lookup := bundleData
  reasons := bundleReasons

"""
    blocks = len(bundles) // block_size + 1
    for block in range(blocks):
        out += f"""private theorem bundleBlock{block:03d}_checked :
    bundles.checkBlock reasons {block_size} {block} = true := by
  decide +kernel

"""
    out += f"""/-- Every cached union is checked against its constituent positive reasons. -/
theorem bundles_valid : bundles.Valid reasons := by
  apply bundles.valid_of_blocks reasons {block_size} (by decide)
  intro block hblock
  have h : ∀ i : Fin {blocks}, bundles.checkBlock reasons {block_size} i = true := by
    intro i
    fin_cases i
"""
    for block in range(blocks):
        out += f"    · exact bundleBlock{block:03d}_checked\n"
    out += "  exact h ⟨block, hblock⟩\n\n"
    return out


def certificate_definitions(data: dict, chunk_size: int = 8000) -> tuple[str, dict]:
    """Partition the proof, preserving exact states at every fragment boundary.

    A reference names an independently certified state/count pair. Its checker
    compares all three state masks before reusing the count. The constructor
    expressions themselves can consequently share syntax across different
    fragments without sharing, or assuming, their mathematical conclusions.
    """
    nodes = data["nodes"]

    def original_children(index: int) -> tuple[int, ...]:
        node = nodes[index]
        return (node[4], node[5]) if node[0] == 2 else (node[4],) if node[0] in (3, 4) else ()

    boundaries, costs = set(), []
    for index in range(len(nodes)):
        descendants = original_children(index)

        def body_size() -> int:
            return 1 + sum(1 if child in boundaries else costs[child] for child in descendants)

        while body_size() > chunk_size:
            candidates = [child for child in descendants if child not in boundaries]
            boundaries.add(max(candidates, key=lambda child: costs[child]))
        costs.append(body_size())
    boundaries.add(data["root"])
    order = sorted(boundaries)
    ordinals = {index: ordinal for ordinal, index in enumerate(order)}

    # Recover each boundary's cube and active constraints from the untrusted
    # tree. These values are subsequently checked against every reference use.
    active = (1 << (len(data["equations"]) + len(data["permutations"]))) - 1
    pending = [(data["root"], 0, 0, active)]
    states = {}
    while pending:
        index, on, off, active = pending.pop()
        if index in boundaries:
            states[index] = (on, off, active)
        tag, variable, value, witness, left, right, _ = nodes[index]
        bit = 1 << variable
        if tag == 2:
            pending.append((left, on, off | bit, active))
            pending.append((right, on | bit, off, active))
        elif tag == 3:
            pending.append((left, on | bit if value else on,
                            off if value else off | bit, active))
        elif tag == 4:
            pending.append((left, on, off, active ^ data["bundles"][witness][1]))

    intern, keys = {}, []

    def intern_key(key: tuple) -> int:
        if key not in intern:
            intern[key] = len(keys)
            keys.append(key)
        return intern[key]

    fragment_roots, references = [], []
    for root in order:
        local_refs, ref_indices = [], {}

        def fragment(index: int) -> int:
            if index != root and index in boundaries:
                if index not in ref_indices:
                    ref_indices[index] = len(local_refs)
                    local_refs.append(index)
                return intern_key((5, ref_indices[index]))
            tag, variable, value, witness, left, right, _ = nodes[index]
            if tag == 0:
                return intern_key((0,))
            if tag == 1:
                return intern_key((1, witness))
            if tag == 2:
                return intern_key((2, variable, fragment(left), fragment(right)))
            if tag == 3:
                return intern_key((3, variable, value, witness, fragment(left)))
            if tag == 4:
                return intern_key((4, witness, fragment(left)))
            raise ValueError(f"unknown certificate tag {tag}")

        fragment_roots.append(fragment(root))
        references.append(local_refs)

    def children(index: int) -> tuple[int, ...]:
        key = keys[index]
        return key[2:] if key[0] == 2 else key[-1:] if key[0] in (3, 4) else ()

    uses = Counter(child for i in range(len(keys)) for child in children(i))
    syntax_boundaries = set(fragment_roots)
    syntax_cost = []
    for index in range(len(keys)):
        size = 1 + sum(1 if child in syntax_boundaries else syntax_cost[child]
                       for child in children(index))
        if uses[index] > 1 and size >= 24:
            syntax_boundaries.add(index)
        syntax_cost.append(size)
    syntax_names = {index: f"certificateTree{ordinal:05d}"
                    for ordinal, index in enumerate(sorted(syntax_boundaries))}

    def expression(index: int, defining: int) -> str:
        tokens, helpers, slots = [], [], {}

        def visit(current: int) -> None:
            if current in syntax_boundaries and current != defining:
                if current not in slots:
                    slots[current] = len(helpers)
                    helpers.append(syntax_names[current])
                tokens.extend(("h", str(slots[current])))
                return
            key = keys[current]
            if key[0] == 0:
                tokens.append("a")
            elif key[0] == 1:
                tokens.extend(("r", str(key[1])))
            elif key[0] == 2:
                tokens.extend(("b", str(key[1])))
                visit(key[2])
                visit(key[3])
            elif key[0] == 3:
                tokens.extend(("f", str(key[1]), str(int(bool(key[2]))), str(key[3])))
                visit(key[4])
            elif key[0] == 4:
                tokens.extend(("s", str(key[1])))
                visit(key[2])
            else:
                tokens.extend(("c", str(key[1])))

        visit(index)
        lines, line = [], ""
        for token in tokens:
            if len(line) + len(token) + 1 > 72:
                lines.append(line)
                line = ""
            line += (" " if line else "") + token
        lines.append(line)
        # A space before each string gap keeps adjacent tokens separate.
        payload = " \\\n    ".join(lines)
        return ('certificate_lit% "' + payload + '"\n' +
                sequence(helpers, opening="[", closing="]", indent=4))

    definitions = []
    for index in sorted(syntax_boundaries):
        definitions.append(f"private def {syntax_names[index]} : Counting.Certificate :=\n  " +
                           expression(index, index) + "\n")
    # Pure reference data must not mention the proofs certifying their counts.
    # The expensive chunk checks are independent of all semantic count proofs.
    for ordinal, (root, refs) in enumerate(zip(order, references)):
        name = f"chunk{ordinal:05d}"
        on, off, active = states[root]
        definitions.append(f"private def {name}State : Counting.ActiveSearch.State :=\n"
                           f"  ⟨⟨{on}, {off}⟩, {active}⟩\n")
        definitions.append(f"private def {name}Data :\n"
                           "    Counting.CountData Counting.ActiveSearch.State :=\n"
                           f"  ⟨{name}State, {nodes[root][6]}⟩\n")
        if refs:
            cases = "\n".join(f"  | {i} => some chunk{ordinals[reference]:05d}Data"
                              for i, reference in enumerate(refs))
            definitions.append(f"private def {name}References :\n"
                               "    ℕ → Option (Counting.CountData Counting.ActiveSearch.State)\n"
                               + cases + "\n  | _ => none\n")
        else:
            definitions.append(f"private def {name}References :\n"
                               "    ℕ → Option (Counting.CountData Counting.ActiveSearch.State) :=\n"
                               "  fun _ => none\n")
    for ordinal, (root, syntax) in enumerate(zip(order, fragment_roots)):
        name = f"chunk{ordinal:05d}"
        definitions.append(f"private theorem {name}_checked :\n"
                           f"    problem.checkBundleDataChunk reasons bundles\n"
                           f"      {name}References {name}State\n"
                           f"      {syntax_names[syntax]} = some {nodes[root][6]} := by\n"
                           "  decide +kernel\n")
    for ordinal, (root, syntax, refs) in enumerate(zip(order, fragment_roots, references)):
        name = f"chunk{ordinal:05d}"
        validity = (f"private theorem {name}References_valid :\n"
                    "    Counting.ReferencesValid\n"
                    "      (Counting.ActiveSearch.modelCount problem.variables problem.constraints)\n"
                    f"      {name}References := by\n"
                    "  intro index data h\n"
                    f"  unfold {name}References at h\n")
        if refs:
            validity += "  split at h\n"
            for reference in refs:
                previous = f"chunk{ordinals[reference]:05d}"
                # Opaque transport avoids injection/subst reducing the concrete
                # finite model count; the 35-variable regression protects this.
                validity += ("  · exact Counting.CountData.count_eq_of_some_eq\n"
                             f"      {previous}State {nodes[reference][6]} {previous}_count h\n")
            validity += "  · exact False.elim (Option.some_ne_none data h.symm)\n"
        else:
            validity += "  exact False.elim (Option.some_ne_none data h.symm)\n"
        definitions.append(validity)
        definitions.append(f"private theorem {name}_count :\n"
                           "    Counting.ActiveSearch.modelCount problem.variables problem.constraints\n"
                           f"      {name}State = {nodes[root][6]} :=\n"
                           "  problem.checkBundleDataChunk_sound permutations_bounded reasons reasons_valid\n"
                           "    bundles bundles_valid\n"
                           f"    {name}References {name}References_valid {name}State\n"
                           f"    {syntax_names[syntax]} {nodes[root][6]}\n"
                           f"    {name}_checked\n")
    final_name = f"chunk{ordinals[data['root']]:05d}"
    definitions.append("/-- Independent fragment checks prove the complete initial model count. -/\n"
                       "theorem certified_count :\n"
                       "    Counting.ActiveSearch.modelCount problem.variables problem.constraints\n"
                       "      (Counting.ActiveSearch.initial problem.constraints) = "
                       f"{data['count']} :=\n  {final_name}_count\n")
    stats = {"tree_nodes": len(nodes), "distinct_subtrees": len(keys),
             "certificate_declarations": len(syntax_names), "checked_fragments": len(order),
             "max_fragment_constructors": max(costs, default=0)}
    return "\n".join(definitions) + "\n", stats


def render(row: str, data: dict, metadata_only: bool = False,
           chunk_size: int = 8000) -> tuple[str, dict]:
    s, k, answer = ROWS[row]
    if (data["symmetric"], data["pairs"], data["count"]) != (s, k, answer):
        raise ValueError(f"{row}: unexpected signature or count")
    validate_problem(data)
    imported = "SearchConstraints" if metadata_only else "SearchCounting"
    out = HEADER + f"public import Cslib.Foundations.RelationAlgebra.{imported}\n"
    out += "public import Cslib.Foundations.RelationAlgebra.AtomRenaming\n"
    out += "public import Cslib.Foundations.RelationAlgebra.SearchBundles\n"
    out += "public import Cslib.Foundations.RelationAlgebra.SearchData\n"
    out += "public import Mathlib.Tactic.FinCases\n\n"
    out += f"""/-!
# Counting integral relation algebras of signature ⟨1, {s}, {k}⟩

Generated by `scripts/RelationAlgebra/count_lean.py`. The cycle basis and all atom
renamings are checked independently of the untrusted search. Normalized atomic
associativity equations cover every quadruple, including the identity cases.
"""
    if not metadata_only:
        out += "The certificate propagates forced choices and counts settled families at once.\n"
    # Fail promptly on a malformed certificate or proof instead of elaborating
    # hundreds of downstream declarations after an earlier error.
    out += f"""-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.Counts.{row}

set_option maxRecDepth 8192
set_option Elab.async false
set_option maxErrors 1

"""
    out += metadata(data)
    stats = {}
    if not metadata_only:
        out += f"""/-- The finite constraint problem certified by this row. -/
def problem : Search.Problem where
  «variables» := {len(data['basis'])}
  equationCount := {len(data['equations'])}
  equations := equations
  permutationCount := {len(data['permutations'])}
  permutations := permutations

"""
        out += f"""/-- Numeric permutations preserve the bounds on the cycle indices. -/
theorem permutations_bounded : problem.PermutationsBounded := by
  have h : ∀ p : Fin {len(data['permutations'])}, ∀ i : Fin {len(data['basis'])},
      permutations p i < {len(data['basis'])} := by decide +kernel
  exact fun p hp i hi => h ⟨p, hp⟩ ⟨i, hi⟩

/-- The numeric search problem presents precisely this relation-algebra signature. -/
def presentation : problem.Presentation {s} {k} where
  reps := cycleReps
  cover := cycleReps_cover
  distinct := cycleReps_distinct
  slots := slots
  slots_spec := slots_spec
  renames := renameDiversity
  rename_laws := rename_laws
  renames_exhaustive := renamings_exhaustive
  permutations_bounded := permutations_bounded
  action_spec p i := by
    have h : (⟨permutations p i, permutations_bounded p p.isLt i i.isLt⟩ :
        Fin {len(data['basis'])}) = orbitAction p i := Fin.ext (permutations_eq p i)
    change _ ∈ cycleOrbit (cycleReps
      (⟨permutations p i, permutations_bounded p p.isLt i i.isLt⟩ :
        Fin {len(data['basis'])}))
    rw [h]
    exact orbitAction_spec p i
  sources := sourceQuads
  sources_spec := sources_checked
  equationCover := equationCover
  equationCover_spec := equations_cover_checked

"""
        out += reason_definitions(data)
        out += bundle_definitions(data)
        definitions, stats = certificate_definitions(data, chunk_size)
        out += definitions
        out += f"""/-- The exact number of isomorphism classes with this atom signature. -/
theorem count : isomorphismClassCount {s} {k} = {answer} :=
  presentation.count_eq_of_initial {answer} certified_count

"""
    out += f"end Cslib.RelationAlgebra.Catalogue.Counts.{row}\n"
    # These definitions are proof data: explicit modifiers suppress native code
    # generation while leaving every definition reducible by the kernel.
    out = "\n".join("noncomputable " + line if line.startswith("def ") else
                    line.replace("private def ", "private noncomputable def ", 1)
                    if line.startswith("private def ") else line
                    for line in out.splitlines()) + "\n"
    return wrap_lean(out), stats


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--row", action="append", choices=ROWS, help="signature to render (repeatable)")
    parser.add_argument("--data-dir", type=Path, required=True, help="directory written by count.py")
    parser.add_argument("--output-root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--check", action="store_true", help="compare generated files without rewriting them")
    parser.add_argument("--metadata-only", action="store_true", help="emit only the certified problem encoding")
    parser.add_argument("--chunk-size", type=int, default=8000,
                        help="maximum constructors per independently checked fragment")
    args = parser.parse_args()
    if args.chunk_size < 4:
        parser.error("--chunk-size must be at least four")
    for row in args.row or DEFAULT_ROWS:
        data = json.loads((args.data_dir / f"{row}.json").read_text())
        source, stats = render(row, data, args.metadata_only, args.chunk_size)
        path = args.output_root / CATALOGUE / f"{row}.lean"
        if args.check:
            if not path.is_file() or path.read_text() != source:
                raise ValueError(f"{path}: missing or differs from regenerated source")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
        print(f"{row}: {len(source):,} bytes" + (f"; {stats}" if stats else ""))


if __name__ == "__main__":
    main()
