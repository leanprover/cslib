// Copyright (c) 2026 Chris Henson. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Authors: Chris Henson

// Untrusted partial-cycle search for count.py. The output describes a counting
// proof tree; it is not a proof until the independent Lean checker accepts it.
// The search follows Jipsen's findra3/findra4 approach: propagation, partial
// isomorphism rejection, and counting an entirely decided family at once.
// https://math.chapman.edu/~jipsen/relalg/ra1/findra4.p

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Mask = std::uint64_t;
using Triple = std::array<int, 3>;
using Quadruple = std::array<int, 4>;
using Dnf = std::vector<Mask>;

struct Equation {
  Dnf left, right;
  Quadruple source;
};

struct Assignment {
  Mask on = 0, off = 0;
  void set(int variable, bool value) {
    (value ? on : off) |= Mask(1) << variable;
  }
};

// Node tags: 0 accept, 1 reject, 2 split, 3 force, 4 simplify.
// A rejection witness indexes the equations, followed by the permutations.
struct Node {
  int tag = 0, variable = 0, value = 0, witness = 0;
  std::size_t left = 0, right = 0;
  Mask count = 0;
};

class Search {
  int symmetric, pairs, atoms;
  std::vector<int> converse, cycleIndex;
  std::vector<Triple> basis;
  std::vector<Equation> equations;
  std::vector<int> equationCover;
  std::vector<std::vector<int>> atomPermutations, permutations;
  std::vector<Node> nodes;
  std::uint64_t searchCalls = 0, bulkCalls = 0;
  int maxFree = 0;

  int index(int a, int b, int c) const { return (a * atoms + b) * atoms + c; }

  std::array<Triple, 6> orbit(int a, int b, int c) const {
    return {{{a, b, c}, {converse[a], c, b}, {c, converse[b], a},
             {converse[b], converse[a], converse[c]},
             {b, converse[c], converse[a]}, {converse[c], a, converse[b]}}};
  }

  void addCycle(int a, int b, int c) {
    if (cycleIndex[index(a, b, c)] >= 0) return;
    auto triples = orbit(a, b, c);
    int slot = static_cast<int>(basis.size());
    for (auto [x, y, z] : triples) cycleIndex[index(x, y, z)] = slot;
    basis.push_back(*std::min_element(triples.begin(), triples.end()));
  }

  void makeCycles() {
    // Place the least constraining monochromatic cycles last in the search.
    // Slots increase in Pascal's order; the search branches from high to low.
    for (int a = 1; a < atoms; ++a) addCycle(a, a, converse[a]);
    for (int a = 1; a < atoms; ++a)
      for (int b = 1; b < atoms; ++b)
        if (converse[b] == b) addCycle(converse[a], a, b);
    for (int a = 1; a < atoms; ++a)
      for (int b = a; b < atoms; ++b)
        for (int c = a; c < atoms; ++c) addCycle(a, b, c);
    if (basis.size() >= 63) throw std::runtime_error("at most 62 cycles supported");
  }

  // A cycle is either a variable, the constant true (0), or false (~0).
  Mask term(int a, int b, int c) const {
    if (a == 0 || b == 0 || c == 0) {
      bool unit = (a == 0 && b == c) || (b == 0 && a == c) ||
                  (c == 0 && b == converse[a]);
      return unit ? 0 : ~Mask(0);
    }
    return Mask(1) << cycleIndex[index(a, b, c)];
  }

  static void normalize(Dnf &terms) {
    std::sort(terms.begin(), terms.end());
    terms.erase(std::unique(terms.begin(), terms.end()), terms.end());
    // A zero mask is the empty conjunction, hence makes the whole DNF true.
    if (!terms.empty() && terms.front() == 0) terms.erase(terms.begin() + 1, terms.end());
  }

  void makeEquations() {
    std::map<std::pair<Dnf, Dnf>, int> known;
    for (int a = 0; a < atoms; ++a)
      for (int b = 0; b < atoms; ++b)
        for (int c = 0; c < atoms; ++c)
          for (int d = 0; d < atoms; ++d) {
            Dnf left, right;
            for (int t = 0; t < atoms; ++t) {
              Mask l = term(a, b, t) | term(t, c, d);
              Mask r = term(b, c, t) | term(a, t, d);
              if (l != ~Mask(0)) left.push_back(l);
              if (r != ~Mask(0)) right.push_back(r);
            }
            normalize(left);
            normalize(right);
            if (left == right) {
              equationCover.push_back(-1);
              continue;
            }
            if (right < left) std::swap(left, right);
            auto key = std::make_pair(left, right);
            auto [it, fresh] = known.emplace(key, static_cast<int>(equations.size()));
            if (fresh) equations.push_back({left, right, {a, b, c, d}});
            equationCover.push_back(it->second);
          }
  }

  void makePermutations() {
    std::vector<int> p(atoms);
    std::iota(p.begin(), p.end(), 0);
    do {
      bool preserves = true;
      for (int a = 0; a < atoms; ++a)
        if (p[converse[a]] != converse[p[a]]) preserves = false;
      if (!preserves) continue;
      atomPermutations.push_back(p);
      std::vector<int> image(basis.size()), preimage(basis.size());
      for (std::size_t i = 0; i < basis.size(); ++i) {
        auto [a, b, c] = basis[i];
        image[i] = cycleIndex[index(p[a], p[b], p[c])];
        preimage[image[i]] = static_cast<int>(i);
      }
      permutations.push_back(std::move(preimage));
    } while (std::next_permutation(p.begin() + 1, p.end()));
  }

  // The three results mean definitely false, undecided, definitely true.
  static int evaluate(const Dnf &terms, Assignment state) {
    bool possible = false;
    for (Mask term : terms) {
      if ((term & state.on) == term) return 1;
      if ((term & state.off) == 0) possible = true;
    }
    return possible ? 0 : -1;
  }

  int equationStatus(int equation, Assignment state) const {
    const auto &e = equations[equation];
    int left = evaluate(e.left, state), right = evaluate(e.right, state);
    if (left == 0 || right == 0) return 0;
    return left == right ? 1 : -1;
  }

  int permutationStatus(int permutation, Assignment state) const {
    // Overapproximate the possible lexicographic comparison results. Sharing
    // a variable at the same position always means equality; other unknown
    // positions may be treated independently, which only weakens pruning.
    bool less = false, equal = true, greater = false;
    const auto &p = permutations[permutation];
    for (int i = static_cast<int>(basis.size()) - 1; i >= 0 && equal; --i) {
      if (p[i] == i) continue;
      Mask l = Mask(1) << i, r = Mask(1) << p[i];
      bool l0 = !(state.on & l), l1 = !(state.off & l);
      bool r0 = !(state.on & r), r1 = !(state.off & r);
      less = less || (l0 && r1);
      greater = greater || (l1 && r0);
      equal = (l0 && r0) || (l1 && r1);
    }
    if (!greater) return 1;
    if (!less && !equal) return -1;
    return 0;
  }

  // Find one unit consequence. Testing the opposite branch makes the emitted
  // witness independent of the particular propagation heuristic used here.
  std::pair<int, bool> consequence(int equation, Assignment state) const {
    const auto &e = equations[equation];
    int left = evaluate(e.left, state), right = evaluate(e.right, state);
    if (left == 0 && right == 0) return {-1, false};
    const Dnf &unknown = left == 0 ? e.left : e.right;
    int required = left == 0 ? right : left;
    if (required == 1) {
      Mask common = ~Mask(0);
      for (Mask term : unknown)
        if ((term & state.off) == 0) common &= term;
      common &= ~(state.on | state.off);
      if (common) return {std::countr_zero(common), true};
    } else if (required == -1) {
      for (Mask term : unknown) {
        if (term & state.off) continue;
        Mask undecided = term & ~state.on;
        if (std::has_single_bit(undecided))
          return {std::countr_zero(undecided), false};
      }
    }
    return {-1, false};
  }

  std::size_t append(Node node) {
    nodes.push_back(node);
    return nodes.size() - 1;
  }

  std::size_t search(Assignment state, std::vector<int> activeEquations,
                     std::vector<int> activePermutations) {
    ++searchCalls;
    std::vector<Node> forces;
    auto finish = [&](std::size_t root) {
      for (auto it = forces.rbegin(); it != forces.rend(); ++it) {
        it->left = root;
        it->count = nodes[root].count;
        root = append(*it);
      }
      return root;
    };
    bool changed = true;
    while (changed) {
      changed = false;
      std::size_t keep = 0;
      for (int equation : activeEquations) {
        int status = equationStatus(equation, state);
        if (status < 0) return finish(append({1, 0, 0, equation}));
        if (status > 0) {
          forces.push_back({4, 0, 0, equation});
          continue;
        }
        activeEquations[keep++] = equation;
        auto [variable, value] = consequence(equation, state);
        if (variable < 0) continue;
        Assignment opposite = state;
        opposite.set(variable, !value);
        if (equationStatus(equation, opposite) != -1)
          throw std::runtime_error("invalid propagation witness");
        forces.push_back({3, variable, value, equation});
        state.set(variable, value);
        changed = true;
      }
      activeEquations.resize(keep);
    }
    std::size_t keep = 0;
    for (int permutation : activePermutations) {
      int status = permutationStatus(permutation, state);
      if (status < 0)
        return finish(append({1, 0, 0,
                              static_cast<int>(equations.size()) + permutation}));
      if (status == 0) activePermutations[keep++] = permutation;
      else forces.push_back({4, 0, 0,
                             static_cast<int>(equations.size()) + permutation});
    }
    activePermutations.resize(keep);
    Mask undecided = ((Mask(1) << basis.size()) - 1) & ~(state.on | state.off);
    if (activeEquations.empty() && activePermutations.empty()) {
      int free = std::popcount(undecided);
      maxFree = std::max(maxFree, free);
      if (free) ++bulkCalls;
      return finish(append({0, 0, 0, 0, 0, 0, Mask(1) << free}));
    }
    if (!undecided) throw std::runtime_error("undecided predicate on total assignment");
    int variable = 63 - std::countl_zero(undecided);
    Assignment excluded = state, included = state;
    excluded.set(variable, false);
    included.set(variable, true);
    std::size_t left = search(excluded, activeEquations, activePermutations);
    std::size_t right = search(included, activeEquations, activePermutations);
    return finish(append({2, variable, 0, 0, left, right,
                          nodes[left].count + nodes[right].count}));
  }

  template <class T> static void writeArray(std::ostream &out, const T &values) {
    out << '[';
    bool first = true;
    for (auto value : values) {
      if (!first) out << ',';
      first = false;
      out << value;
    }
    out << ']';
  }

 public:
  Search(int symmetric, int pairs)
      : symmetric(symmetric), pairs(pairs), atoms(1 + symmetric + 2 * pairs),
        converse(atoms), cycleIndex(atoms * atoms * atoms, -1) {
    if (symmetric < 0 || pairs < 0 || atoms > 6)
      throw std::runtime_error("supported signatures have at most six atoms");
    std::iota(converse.begin(), converse.end(), 0);
    for (int i = 0; i < pairs; ++i)
      std::swap(converse[1 + symmetric + 2 * i], converse[2 + symmetric + 2 * i]);
    makeCycles();
    makeEquations();
    makePermutations();
  }

  void run(const std::string &path) {
    std::vector<int> activeEquations(equations.size()), activePermutations(permutations.size());
    std::iota(activeEquations.begin(), activeEquations.end(), 0);
    std::iota(activePermutations.begin(), activePermutations.end(), 0);
    std::size_t root = search({}, activeEquations, activePermutations);
    std::ofstream out(path);
    if (!out) throw std::runtime_error("cannot open output file");
    out << "{\"format\":1,\"symmetric\":" << symmetric << ",\"pairs\":" << pairs
        << ",\"atoms\":" << atoms << ",\"count\":" << nodes[root].count
        << ",\"root\":" << root << ",\"search_calls\":" << searchCalls
        << ",\"bulk_calls\":" << bulkCalls << ",\"max_free\":" << maxFree
        << ",\"basis\":[";
    for (std::size_t i = 0; i < basis.size(); ++i) {
      if (i) out << ',';
      writeArray(out, basis[i]);
    }
    out << "],\"equations\":[";
    for (std::size_t i = 0; i < equations.size(); ++i) {
      if (i) out << ',';
      out << '[';
      writeArray(out, equations[i].left);
      out << ',';
      writeArray(out, equations[i].right);
      out << ',';
      writeArray(out, equations[i].source);
      out << ']';
    }
    out << "],\"equation_cover\":";
    writeArray(out, equationCover);
    out << ",\"atom_permutations\":[";
    for (std::size_t i = 0; i < atomPermutations.size(); ++i) {
      if (i) out << ',';
      writeArray(out, atomPermutations[i]);
    }
    out << "],\"permutations\":[";
    for (std::size_t i = 0; i < permutations.size(); ++i) {
      if (i) out << ',';
      writeArray(out, permutations[i]);
    }
    out << "],\"nodes\":[\n";
    for (std::size_t i = 0; i < nodes.size(); ++i) {
      if (i) out << ",\n";
      const auto &n = nodes[i];
      out << '[' << n.tag << ',' << n.variable << ',' << n.value << ',' << n.witness
          << ',' << n.left << ',' << n.right << ',' << n.count << ']';
    }
    out << "\n]}\n";
    if (!out) throw std::runtime_error("failed to write output");
    std::cerr << "I1S" << symmetric << 'N' << pairs << ": count=" << nodes[root].count
              << " cycles=" << basis.size() << " equations=" << equations.size()
              << " permutations=" << permutations.size() << " nodes=" << nodes.size()
              << " search_calls=" << searchCalls << " bulk_calls=" << bulkCalls
              << " max_free=" << maxFree << '\n';
  }
};

int main(int argc, char **argv) {
  try {
    if (argc != 4) throw std::runtime_error("usage: count SYMMETRIC PAIRS OUTPUT.json");
    Search(std::stoi(argv[1]), std::stoi(argv[2])).run(argv[3]);
  } catch (const std::exception &error) {
    std::cerr << error.what() << '\n';
    return 1;
  }
}
