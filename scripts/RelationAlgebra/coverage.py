#!/usr/bin/env python3
# Copyright (c) 2026 Chris Henson. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Chris Henson

"""Render kernel-checked coverage words in 64-model blocks from catalogue JSON.

Run generate.py --data-only first. This script does not invoke Lean; check the
resulting kernel certificates through the usual project build.
"""

import argparse
import json
from pathlib import Path

from generate import CATALOGUE, ROWS, process_sources, renamed_profiles, require

HEADER = '''/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

'''


def render_word(word, width, indent=2):
    """Use balanced relative shifts and literals of at most 128 bits."""
    lead = ' ' * indent
    if word == 0 or width <= 128:
        return lead + str(word)
    half = width // 2
    low, high = word & ((1 << half) - 1), word >> half
    if high == 0:
        return render_word(low, half, indent)
    if low == 0:
        return (lead + '(Nat.shiftLeft\n' + render_word(high, half, indent + 2)
                + '\n' + lead + '  ' + str(half) + ')')
    return (lead + '(Code.joinWords ' + str(half) + '\n'
            + render_word(low, half, indent + 2) + '\n'
            + render_word(high, half, indent + 2) + ')')


def render_coverage(data):
    j, k, r = data['j'], data['k'], data['cycle_count']
    m, p = data['model_count'], data['permutation_count']
    row = f'I1S{j}N{k}'
    base = f'Cslib.Foundations.RelationAlgebra.Catalogue.{row}'
    out = CATALOGUE / row
    profiles = renamed_profiles(data)
    count = (m + 63) // 64
    for b in range(count):
        n, word = min(64, m - 64 * b), 0
        for profile_row in profiles[64 * b:64 * b + n]:
            for profile in profile_row:
                word |= 1 << profile
        s = HEADER + f'''public import {base}.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models {64*b+1}–{64*b+n} of the ⟨1, {j}, {k}⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.{row}.Coverage{b:03}

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
''' + render_word(word, 2 ** r) + f'''

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord {n} {p} (fun i q => Data.profiles ({64*b} + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.{row}.Coverage{b:03}
'''
        yield out / f'Coverage{b:03}.lean', s
    qs = sorted({tuple(w[1:]) for w in data['invalid_witnesses']})
    q = len(qs)
    s = HEADER + '\n'.join(f'public import {base}.Coverage{b:03}' for b in range(count)) + f'''

/-!
# Complete profile coverage for the ⟨1, {j}, {k}⟩ row

Independent block certificates bound kernel memory. Their union equals the simultaneous
associativity truth table, computed from a sufficient collection of necessary equations.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.{row}.Coverage

/-- The independently certified coverage words. -/
def blockWords : ℕ → ℕ
'''
    s += '\n'.join(f'  | {b} => Coverage{b:03}.word' for b in range(count)) + '\n  | _ => 0\n\n'
    s += f'''private theorem blockWords_eq : ∀ b, b < {count} →
    Code.profileWord (min 64 ({m} - b * 64)) {p}
      (fun i q => Data.profiles (b * 64 + i) q) = blockWords b
'''
    s += '\n'.join(f'  | {b}, _ => Coverage{b:03}.word_eq' for b in range(count))
    s += f'''\n  | n + {count}, h => False.elim (by omega)

/-- The union of the block words is the complete profile word. -/
theorem profileWord_eq : Code.profileWord {m} {p} Data.profiles =
    Code.orBelow blockWords {count} :=
  Code.profileWord_eq_of_chunks Data.profiles (by decide) (by decide) blockWords blockWords_eq

/-- The truth word for a cycle on the specified atom codes. -/
def words (a b c : ℕ) : ℕ := Code.cycleWord {r} (Data.slots a b c)

/-- A sufficient list of necessary associativity equations. -/
def quads : ℕ → Code.Quadruple
'''
    s += '\n'.join(f'  | {i} => ({", ".join(map(str, t))})' for i, t in enumerate(qs))
    s += '\n  | _ => (0, 0, 0, 0)\n\n'
    s += f'''/-- Every equation uses valid atom codes. -/
theorem quads_lt : ∀ i < {q}, (quads i).1 < 5 ∧ (quads i).2.1 < 5 ∧
    (quads i).2.2.1 < 5 ∧ (quads i).2.2.2 < 5 := by
  have h : ∀ i : Fin {q}, (quads i).1 < 5 ∧ (quads i).2.1 < 5 ∧
      (quads i).2.2.1 < 5 ∧ (quads i).2.2.2 < 5 := by decide +kernel
  intro i hi
  exact h ⟨i, hi⟩

/-- Every assignment satisfying these necessary equations is a listed cycle profile. -/
theorem check : Code.associativityWordFor 5 (Code.truthOnes (2 ^ {r})) words quads {q} =
    Code.profileWord {m} {p} Data.profiles := by
  rw [profileWord_eq]
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.{row}.Coverage
'''
    yield out / 'Coverage.lean', s


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path, required=True,
                        help="directory containing JSON files exported by generate.py")
    parser.add_argument("--row", choices=ROWS, action="append", help="row to process; default: both")
    parser.add_argument("--output-root", type=Path, default=Path(__file__).resolve().parents[2],
                        help="repository root receiving generated Lean certificates")
    parser.add_argument("--check", action="store_true", help="compare sources without rewriting them")
    args = parser.parse_args()
    try:
        for row in dict.fromkeys(args.row or ROWS):
            data = json.loads((args.data_dir / f"cslib-{row.lower()}-data.json")
                              .read_text(encoding="utf-8"))
            require((data["j"], data["k"], data["model_count"]) == ROWS[row][:3],
                    f"{row}: unexpected row signature or model count")
            count = process_sources(render_coverage(data), args.output_root, args.check,
                                    [CATALOGUE / row / "Coverage*.lean"])
            print(f'{row}: {"checked" if args.check else "generated"} {count} coverage modules',
                  flush=True)
    except (ValueError, OSError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
