// Copyright (c) 2026 Chris Henson. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Authors: Chris Henson

// Exhaustive five-atom table enumeration used by generate.py. This program is
// an untrusted certificate generator: the resulting Lean proofs are checked by
// Lean's kernel. Input and output formats are private to generate.py.

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>

using Table = unsigned __int128;
using Triple = std::array<int, 3>;
using Permutation = std::array<int, 5>;

constexpr int index(int a, int b, int c) { return (a * 5 + b) * 5 + c; }

int main(int argc, char **argv) {
  if (argc != 3) {
    std::cerr << "usage: enumerate SPEC OUTPUT\n";
    return 1;
  }
  std::ifstream input(argv[1]);
  int j, k, cycleCount;
  if (!(input >> j >> k >> cycleCount) ||
      !((j == 2 && k == 1 && cycleCount == 16) ||
        (j == 4 && k == 0 && cycleCount == 20))) {
    std::cerr << "invalid row specification\n";
    return 1;
  }
  std::vector<Triple> representatives(cycleCount);
  for (auto &triple : representatives)
    for (auto &atom : triple)
      if (!(input >> atom) || atom < 1 || atom > 4) return 1;
  int permutationCount;
  if (!(input >> permutationCount) || permutationCount != (k == 1 ? 4 : 24))
    return 1;
  std::vector<Permutation> permutations(permutationCount);
  for (auto &permutation : permutations)
    for (auto &atom : permutation)
      if (!(input >> atom) || atom < 0 || atom > 4) return 1;

  Permutation converse = {0, 1, 2, 3, 4};
  for (int i = 0; i < k; ++i)
    std::swap(converse[j + 2 * i + 1], converse[j + 2 * i + 2]);
  std::array<int, 125> orbitIndex;
  orbitIndex.fill(-1);
  std::vector<Table> orbitCodes(cycleCount);
  for (int i = 0; i < cycleCount; ++i) {
    auto [a, b, c] = representatives[i];
    std::array<Triple, 6> orbit = {{{a, b, c},
        {converse[a], c, b}, {c, converse[b], a},
        {converse[b], converse[a], converse[c]},
        {b, converse[c], converse[a]}, {converse[c], a, converse[b]}}};
    for (auto [x, y, z] : orbit) {
      orbitCodes[i] |= Table(1) << index(x, y, z);
      orbitIndex[index(x, y, z)] = i;
    }
  }
  Table identityCode = 0;
  for (int a = 0; a < 5; ++a)
    for (int b = 0; b < 5; ++b)
      for (int c = 0; c < 5; ++c)
        if ((a == 0 && b == c) || (b == 0 && a == c) ||
            (c == 0 && b == converse[a]))
          identityCode |= Table(1) << index(a, b, c);

  std::vector<std::vector<int>> orbitPermutations(
      permutationCount, std::vector<int>(cycleCount));
  for (int p = 0; p < permutationCount; ++p)
    for (int i = 0; i < cycleCount; ++i) {
      auto [a, b, c] = representatives[i];
      auto &permutation = permutations[p];
      int target = orbitIndex[index(permutation[a], permutation[b], permutation[c])];
      if (target < 0) return 1;
      orbitPermutations[p][i] = target;
    }

  uint32_t maskCount = uint32_t(1) << cycleCount;
  std::vector<uint32_t> answers(maskCount);
  std::vector<Table> tables(maskCount);
  tables[0] = identityCode;
  for (uint32_t mask = 0; mask < maskCount; ++mask) {
    if (mask)
      tables[mask] = tables[mask & (mask - 1)] | orbitCodes[std::countr_zero(mask)];
    unsigned product[5][5];
    for (int a = 0; a < 5; ++a)
      for (int b = 0; b < 5; ++b)
        product[a][b] = unsigned(tables[mask] >> index(a, b, 0)) & 31u;

    // Find the first atomic associativity counterexample, when one exists.
    bool associative = true;
    for (int a = 0; a < 5 && associative; ++a)
      for (int b = 0; b < 5 && associative; ++b)
        for (int c = 0; c < 5 && associative; ++c) {
          unsigned left = 0, right = 0;
          for (unsigned bits = product[a][b]; bits; bits &= bits - 1)
            left |= product[std::countr_zero(bits)][c];
          for (unsigned bits = product[b][c]; bits; bits &= bits - 1)
            right |= product[a][std::countr_zero(bits)];
          if (left != right) {
            associative = false;
            int d = std::countr_zero(left ^ right);
            answers[mask] = 0x80000000u | (((a * 5 + b) * 5 + c) * 5 + d);
          }
        }
    if (!associative) continue;

    uint32_t canonicalMask = mask;
    int bestPermutation = 0;
    for (int p = 1; p < permutationCount; ++p) {
      uint32_t image = 0;
      for (uint32_t bits = mask; bits; bits &= bits - 1)
        image |= 1u << orbitPermutations[p][std::countr_zero(bits)];
      if (image < canonicalMask) {
        canonicalMask = image;
        bestPermutation = p;
      }
    }
    // Bits 0..19 contain the target mask, bits 20..24 the permutation index.
    // Bit 31 distinguishes an invalid mask and its base-five quadruple.
    answers[mask] = canonicalMask | (uint32_t(bestPermutation) << 20);
  }

  // Explicit little-endian output avoids depending on the host byte order.
  std::ofstream output(argv[2], std::ios::binary);
  for (uint32_t answer : answers)
    for (int shift = 0; shift < 32; shift += 8)
      output.put(static_cast<char>((answer >> shift) & 255));
  if (!output) {
    std::cerr << "could not write enumeration output\n";
    return 1;
  }
}
