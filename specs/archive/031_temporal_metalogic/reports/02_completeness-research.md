# Research Report: Canonical Model Construction for Temporal Logic Completeness

## 1. Literature Analysis (BimodalLogic)

### BimodalLogic Lake Dependency Status

The BimodalLogic package is **not present** as a lake dependency in the current project. The `lakefile.lean` contains no reference to BimodalLogic, and `.lake/packages/` does not contain a BimodalLogic directory. The available lake packages are: importGraph, mathlib, LeanSearchClient, proofwidgets, Cli, Qq, plausible, aesop, batteries.

There is **no `literature/` directory** to examine. The BimodalLogic project appears to have been decoupled from cslib at some point.

### Bimodal Completeness Status in Cslib

The bimodal metalogic in `Cslib/Logics/Bimodal/Metalogic/` contains:
- **Soundness**: Fully implemented across 6 files (Core, DenseSoundness, DenseValidity, DiscreteSoundness, FrameClassVariants, Soundness)
- **No Completeness**: There is no bimodal completeness proof in cslib. The bimodal metalogic has only soundness and conservative extension results.

The bimodal soundness (`Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean`) validates all BX temporal axioms plus modal axioms (T, 4, B, 5, K-distribution) against a richer semantic framework involving `TaskFrame`, `TaskModel`, `WorldHistory`, and `ShiftClosed` sets. This is substantially more complex than the standalone temporal semantics, which just uses a `TemporalModel D Atom` with a linear order on `D`.

**Conclusion**: The bimodal system provides no completeness template to follow. The standalone temporal completeness must be developed from first principles using the modal completeness as the closest structural template.

## 2. Modal Completeness as Template

### Modal Canonical Model Construction (`Cslib/Logics/Modal/Metalogic/Completeness.lean`)

The modal completeness proof for S5 follows this structure (547 lines total):

1. **CanonicalWorld**: `{ S : Set (Proposition Atom) // Modal.SetMaximalConsistent S }`
2. **CanonicalModel**: Accessibility `R S T := forall phi, box phi in S.val -> phi in T.val`; Valuation `v S p := atom p in S.val`
3. **Frame properties**:
   - `canonical_refl`: From axiom T (`mcs_box_closure`)
   - `canonical_trans`: From axiom 4 (`mcs_box_box`)
   - `canonical_eucl`: From axiom B (`mcs_box_diamond`) -- this is the most complex proof, ~180 lines of commented reasoning
4. **Truth lemma** by structural induction on formula (4 cases: atom, bot, imp, box):
   - `atom`: trivial by definition
   - `bot`: by `mcs_bot_not_mem`
   - `imp`: forward uses Peirce's law derivation for contrapositive; reverse uses `implication_property`
   - `box`: forward uses `mcs_box_witness` (if box phi not in S, exists T with R S T and phi not in T); reverse is direct from accessibility definition
5. **Completeness**: Contrapositive -- not derivable implies {neg phi} consistent, Lindenbaum to MCS, truth lemma gives contradiction

### Key Structural Differences for Temporal

| Aspect | Modal (S5) | Temporal (BX) |
|--------|-----------|---------------|
| Worlds | MCS | MCS |
| Relation | Binary accessibility R | Linear order < |
| Frame properties | Reflexive + Transitive + Euclidean | Irreflexive + Transitive + Total + Serial |
| Truth lemma cases | 4 (atom, bot, imp, box) | 5 (atom, bot, imp, untl, snce) |
| Operator semantics | box = forall accessible | G = forall future; U = existential with guard |
| Witness lemma | `mcs_box_witness` | `mcs_g_witness`, `mcs_h_witness`, plus Until/Since witnesses |
| Duality | None needed | `swap_temporal` / OrderDual duality |

The modal proof is ~547 lines. The temporal proof will need substantially more due to:
- Building a LinearOrder instance (vs. just showing reflexive/transitive/Euclidean)
- Two additional truth lemma cases (Until, Since) which are the hardest
- The Until/Since cases require axioms BX5, BX6, BX7, BX10, BX11, BX12, BX13

## 3. Current Completeness.lean State

### What Exists (418 lines)

The current file has significant infrastructure already proven:

**MCS Helper Lemmas** (lines 53-215):
- `mcs_mp_axiom`: Apply axiom instance in MCS
- `mcs_top_mem`, `mcs_f_top_mem`, `mcs_p_top_mem`: Seriality members
- `mcs_g_bot_not_mem`, `mcs_h_bot_not_mem`: G(bot)/H(bot) not in MCS
- `derive_and_top_intro`: Derives `phi -> top /\ phi`
- `derive_dne`: Derives double negation elimination
- `derive_h_nec`: H-necessitation via duality
- `mcs_dne`: Double negation elimination in MCS
- `mcs_neg_g_iff_f_neg`: neg(G psi) iff F(neg psi) in MCS
- `mcs_ff_imp_f`: F(F(psi)) -> F(psi) (F-idempotency via BX6 + BX3)
- `mcs_pp_imp_p`: P(P(psi)) -> P(psi) (P-idempotency via BX6' + BX3')
- `mcs_g_trans`: G(psi) -> G(G(psi)) (G-transitivity)
- `mcs_h_trans`: H(psi) -> H(H(psi)) (H-transitivity)
- `past_of_future_subset`: If futureSet(S) subset T, then pastSet(T) subset S (via BX4)
- `future_of_past_subset`: Dual (via BX4')

**Canonical Model Definitions** (lines 306-325):
- `CanonicalWorld`: MCS as worlds
- `canonical_lt`: Two-condition relation (futureSet + pastSet)
- `canonical_le`: Extension with equality
- `canonical_lt_trans`: Transitivity of canonical_lt (proven, uses mcs_g_trans + mcs_h_trans)

**Additional Definitions** (lines 280-305):
- `CanonicalModel`: Valuation as atom membership
- `canonical_acc`: Preorder version (just futureSet inclusion)
- `truth_lemma_g_forward` and `truth_lemma_g_reverse`: G-case truth lemma (both proven)

**Consistency and Completeness Setup** (lines 308-418):
- `neg_consistent_of_not_derivable`: Proven
- `completeness` theorem: Started but has the main sorry

### Sorry Locations

1. **Line 278**: In the transitivity proof for `canonical_lt` with the strict-inequality `W1.val != W2.val` condition. The author discovered that this condition breaks transitivity because `W1 < W2 < W3 = W1` can't be ruled out without showing `W1 = W2` when futureSet goes both ways -- and futureSet inclusion alone doesn't determine MCS equality.

2. **Line 416**: The main completeness sorry. Requires the full LinearOrder instance on CanonicalWorld, the Nontrivial/NoMaxOrder/NoMinOrder instances, and the full truth lemma.

### Analysis of Where the Proof Stalls

The implementation encountered a fundamental design choice about the canonical order:

**Problem**: The file defines `canonical_lt` as:
```
canonical_lt W1 W2 := (forall psi, G(psi) in W1 -> psi in W2) /\ (forall psi, H(psi) in W2 -> psi in W1)
```

But `canonical_lt` as defined is NOT irreflexive (it's reflexive! `canonical_lt W W` holds trivially since G(psi) in W implies psi in W by the standard K axiom / distribution). The author then tried adding `W1.val != W2.val` but this breaks transitivity.

**Root cause**: The relation `canonical_lt` as defined (both conditions) is actually a **preorder** (reflexive and transitive), NOT a strict order. The past condition follows from the future condition via BX4, so the two-condition definition collapses to just futureSet inclusion.

## 4. MCS Infrastructure Inventory

### Available in `Cslib/Logics/Temporal/Metalogic/MCS.lean` (704 lines)

**Generic Framework Instantiations**:
- `Temporal.SetConsistent`, `Temporal.SetMaximalConsistent`: Abbreviations
- `temporal_lindenbaum`: Consistent set extends to MCS
- `temporal_closed_under_derivation`: MCS closed under derivability
- `temporal_implication_property`: phi -> psi in S and phi in S implies psi in S
- `temporal_negation_complete`: phi in S or neg phi in S

**Basic MCS Properties**:
- `mcs_bot_not_mem`: bot not in MCS
- `mcs_neg_of_not_mem`: phi not in S implies neg phi in S
- `mcs_not_mem_of_neg`: neg phi in S implies phi not in S
- `mcs_mem_iff_neg_not_mem`: phi in S iff neg phi not in S

**G-Distribution / H-Distribution**:
- `mcs_g_mp`: G(phi -> psi) in S and G(phi) in S implies G(psi) in S
  - Proven via BX3 (right_mono_until) and derive_contrapositive, ~215 lines
- `mcs_h_mp`: Symmetric for H
  - Proven via BX3' (right_mono_since) and temporal duality, ~85 lines

**Witness Lemmas** (the key completeness ingredients):
- `derive_g_contradiction`: If all G(li) in S and L derives phi, then G(phi) in S
  - Induction on L, using mcs_g_mp
- `mcs_g_witness`: If G(phi) not in S, exists MCS T with futureSet(S) subset T and phi not in T
  - Shows `futureSet(S) union {neg phi}` is consistent, then extends via Lindenbaum
- `derive_h_contradiction`: Symmetric for H
- `mcs_h_witness`: Symmetric -- if H(phi) not in S, exists MCS T with pastSet(S) subset T and phi not in T

**Helper Functions**:
- `futureSet(S) = { phi | G(phi) in S }`
- `pastSet(S) = { phi | H(phi) in S }`

### Available in Completeness.lean (already proven)

- `mcs_g_trans`: G(psi) -> G(G(psi)) in MCS
- `mcs_h_trans`: H(psi) -> H(H(psi)) in MCS
- `mcs_ff_imp_f`: F(F(psi)) -> F(psi) in MCS
- `mcs_pp_imp_p`: P(P(psi)) -> P(psi) in MCS
- `past_of_future_subset`: futureSet(S) subset T implies pastSet(T) subset S
- `future_of_past_subset`: pastSet(S) subset T implies futureSet(T) subset S
- `canonical_lt_trans`: Transitivity of canonical_lt (assuming both conditions)
- `truth_lemma_g_forward` and `truth_lemma_g_reverse`: G-case of truth lemma

### What's Missing

1. **Irreflexivity / strict order**: No proof that any canonical relation is a strict linear order
2. **Totality**: No proof using BX11/BX11' (temp_linearity axioms)
3. **Seriality**: No NoMaxOrder/NoMinOrder instances
4. **Truth lemma for Until**: Completely absent
5. **Truth lemma for Since**: Completely absent
6. **LinearOrder instance**: Not constructed
7. **Nontrivial instance**: Not shown

## 5. Standard Tense Logic Completeness Construction

### The Standard Approach (Burgess 1982, Xu 1988)

For Kt (basic tense logic) extended with Until/Since over serial linear orders:

#### Step 1: Define the Canonical Preorder

Define `W1 <= W2` iff `futureSet(W1) subset W2` (equivalently: for all psi, G(psi) in W1 implies psi in W2).

This is a **preorder** (reflexive and transitive):
- **Reflexive**: G(psi) in W implies psi in W, because G(psi) = neg F(neg psi) and the seriality axiom BX1 gives F(top) in W. If G(psi) in W, then by mcs_g_mp applied to G(psi -> psi) (which is in W by necessitation of identity), we get psi in W. Actually simpler: define W <= W' by checking that G-formulas transfer. For reflexivity, if G(psi) in W, then by the axiom phi -> G(P(phi)) (BX4) and its consequences, plus the standard K-like distribution, we can show psi in W. But actually this depends on whether Kt has the T axiom (G(phi) -> phi). In BX, the seriality axioms give us F(top) and P(top), and the absorption axiom gives us G(phi) -> phi via: G(phi) is the negation of F(neg phi), and F(neg phi) = (neg phi) U top. If phi is false at the current point, then... actually BX does NOT have G(phi) -> phi as an axiom. G(phi) says phi holds at all STRICTLY future points. So G(psi) in W does NOT imply psi in W.

**CORRECTION**: In BX temporal logic, G and H are strict operators (they only speak about strictly future/past points, not the current point). So `futureSet(W) subset W` does NOT hold in general. The relation `W1 <= W2` defined by futureSet(W1) subset W2 is NOT reflexive.

This is actually critical for the construction. The canonical relation should be:

**W1 < W2** iff futureSet(W1) subset W2 (and pastSet(W2) subset W1, but this follows from BX4).

This gives a **strict partial order** that is transitive (proven in the code as `canonical_lt_trans` using `mcs_g_trans`).

The question is whether it's also:
- **Irreflexive**: Does futureSet(W) subset W fail? Not necessarily -- it could hold for some W.
- **Total**: Given W1 != W2, is W1 < W2 or W2 < W1?

#### Step 2: Totality via BX11

The key axiom for totality is **BX11** (temp_linearity):
```
F(phi) /\ F(psi) -> F(phi /\ psi) \/ F(phi /\ F(psi)) \/ F(F(phi) /\ psi)
```

This says: if two things happen in the future, either they happen at the same time, or one happens first with the other still in the future.

**How BX11 gives totality**: Suppose W1 and W2 are MCS that are not related by <=. Then there exist phi with G(phi) in W1 but phi not in W2, and psi with G(psi) in W2 but psi not in W1.

This means: neg phi in W2 (since phi not in W2 and W2 is MCS). And neg psi in W1.
By BX4 (connect_future): neg psi -> G(P(neg psi)). So G(P(neg psi)) in W1.
By BX4' (connect_past): neg phi -> H(F(neg phi)). So H(F(neg phi)) in W2.

Now BX11 applied in W1: F(neg phi) and F(neg psi) being in some related world... Actually the linearity argument is more subtle. The standard approach uses BX11 not directly on W1 and W2 but through a chain of reasoning involving the G-witness lemma.

**Alternative totality proof via BX11**: For any two MCS W1, W2, either:
- For all phi, G(phi) in W1 implies phi in W2 (i.e., W1 <= W2), or
- For all phi, G(phi) in W2 implies phi in W1 (i.e., W2 <= W1)

Suppose neither. Then there exist alpha, beta with G(alpha) in W1 and alpha not in W2, and G(beta) in W2 and beta not in W1. By negation completeness: neg alpha in W2 and neg beta in W1.

Consider the MCS W1: neg beta in W1. By BX4: G(P(neg beta)) in W1. Since G(alpha) in W1, by G-distribution: G(alpha /\ P(neg beta)) should be derivable if alpha /\ P(neg beta) were in some future-set... 

This is getting complex. The standard proof typically proceeds differently.

#### Step 3: The "Defect" or "Chain" Approach

Many textbook proofs (following Gabbay, Hodkinson, and Reynolds) avoid building a LinearOrder on ALL MCS. Instead, they build a **countable chain of MCS indexed by the integers** that witnesses enough structure for the specific formula being falsified.

**Construction**:
1. Start with M0 (the MCS containing neg phi, from Lindenbaum)
2. For n >= 0: Choose M(n+1) by extending futureSet(M(n)) to an MCS (using Lindenbaum), ensuring that any "defects" (G(psi) not in M(n)) are witnessed (psi not in M(n+1))
3. For n <= 0: Symmetrically extend pastSet(M(n)) to get M(n-1)
4. The truth lemma holds on this chain by construction

**Advantage**: No need to prove totality of the canonical order on ALL MCS. The chain is automatically linearly ordered since it's indexed by Z.

**Disadvantage**: The truth lemma for Until/Since requires careful construction of the chain to ensure all Until/Since defects are witnessed. This typically requires either:
- Atom to be countable (so defects can be enumerated)
- Only finitely many subformulas of the target formula (always true)
- An omega-step construction at limit ordinals

For the BX system, since we only need to falsify one specific formula phi, we only need to witness subformulas of phi, which is finite. So a finite-defect construction suffices.

#### Step 4: Truth Lemma for G/H

The G case is the simplest temporal case:

**Forward (G(psi) in M(n) implies psi holds at all M(m) for m > n)**:
By the chain construction, futureSet(M(n)) subset M(n+1). So G(psi) in M(n) implies psi in M(n+1). Also G(G(psi)) in M(n) (by mcs_g_trans), so G(psi) in M(n+1), so psi in M(n+2). By induction, psi in M(m) for all m > n.

**Reverse (psi in M(m) for all m > n implies G(psi) in M(n))**:
Contrapositive: G(psi) not in M(n). By mcs_g_witness, exists MCS T with futureSet(M(n)) subset T and psi not in T. By the defect construction, we can ensure M(n+1) = T (or at least that psi not in M(n+1)). Then by truth lemma IH, psi does not hold at M(n+1) in the chain model.

The key: the chain must be constructed to witness ALL G-defects, not just one.

#### Step 5: Truth Lemma for Until/Since

The Until case is the hardest. `(phi U psi)` at time n means: there exists m > n with psi at m, and phi at all k with n < k < m.

**Forward (phi U psi in M(n) implies the semantic condition)**:
Need to find m > n with psi in M(m) and phi in M(k) for n < k < m.

Key axioms used:
- **BX10** (until_F): phi U psi implies F(psi). So F(psi) in M(n), which means by the chain construction, psi in M(m) for some m > n.
- **BX5** (self_accum_until): phi U psi implies phi U (psi /\ (phi U psi)). This strengthens the Until witness.
- **BX13** (enrichment_until): p /\ (phi U psi) implies (phi /\ S(p, psi)) U psi. This enriches the guard.
- **BX6** (absorb_until): (psi /\ (phi U psi)) U psi implies phi U psi. This collapses nested untils.

The standard proof uses BX5 + BX13 + BX6 together to show that if phi U psi is in M(n), then we can find a witness m where psi in M(m) and the guard phi holds at all intermediate chain points.

The argument: phi U psi in M(n). By BX10: F(psi) in M(n). By BX12: F(psi) implies psi U top, so psi U top in M(n). 

Actually, the standard proof for the forward direction of the Until truth lemma on the chain goes:

1. phi U psi in M(n).
2. By BX5: phi U (psi /\ (phi U psi)) in M(n).
3. By BX10 on the strengthened until: F(psi /\ (phi U psi)) in M(n).
4. So there exists m > n with (psi /\ (phi U psi)) in M(m).
5. psi in M(m), and phi U psi in M(m).
6. Repeat from step 2 with M(m). This gives m' > m with psi in M(m') and phi U psi in M(m').
7. This process must terminate for the CHAIN approach because the chain is omega-indexed and we can't go to infinity.

Hmm, this doesn't terminate directly. The standard approach uses **BX7** (linearity of Until) to establish that the Until witnesses are ordered linearly and the absorption axiom to collapse.

Actually, the cleaner approach for the forward direction:

For the chain model indexed by Z, the truth lemma is proven by induction on formula complexity. For phi U psi at M(n):
- phi U psi in M(n) implies F(psi) in M(n) by BX10.
- The chain witnesses F(psi): there exists some m > n in the chain where psi holds (by IH for psi, since psi has lower complexity than phi U psi).
- Take the LEAST such m. For all k with n < k < m, psi does not hold at M(k).
- phi U psi in M(n). We need phi at all k with n < k < m.
- At each such k: psi not in M(k). phi U psi might or might not be in M(k).
- Actually, by BX5 (self-accumulation): phi U psi implies phi U (psi /\ (phi U psi)). The guard is strengthened to psi /\ (phi U psi). At k < m, the guard psi /\ (phi U psi) must hold.

Wait, this uses Until semantics on the chain, not MCS membership. The semantic Until at M(n) says: exists m > n with phi at m and psi at all k between. The MCS membership phi U psi in M(n) needs to be connected to this semantic condition.

The standard Henkin/canonical model approach:

**For the chain indexed by Z with truth lemma by induction on formula complexity**:

Assume IH holds for all proper subformulas.

**Forward**: phi U psi in M(n). Want: exists m > n with Sat(m, phi) and forall k in (n,m), Sat(k, psi).

By IH, Sat(k, alpha) iff alpha in M(k) for all subformulas alpha of phi U psi (i.e., for phi and psi, which have lower complexity).

phi U psi in M(n). By BX10: F(phi) in M(n). By IH for phi: exists m0 > n with phi in M(m0).

Take m = min { j > n | phi in M(j) } (this exists by the above, and is well-defined since the chain is discrete / omega-indexed in each direction). Wait, the chain is indexed by Z, which is dense? No, Z is discrete. So there IS a minimal m > n with phi in M(m).

For the guard: need psi in M(k) for all n < k < m. Since m is minimal with phi in M(m), phi not in M(k) for n < k < m.

phi U psi in M(n). Does this persist along the chain? We need: psi in M(k) for n < k < m.

The key insight is that from phi U psi in M(n) and the chain construction:
- futureSet(M(n)) subset M(n+1). So every G-formula from M(n) transfers.
- But phi U psi is NOT a G-formula. It's an Until formula.

**This is where the construction gets subtle.** The chain must be built so that the truth lemma for Until holds. This typically requires ensuring:
- If phi U psi in M(n) and phi not in M(n+1), then psi in M(n+1).
- If phi U psi in M(n) and phi in M(n+1), then phi U psi in M(n+1) (by some chain of reasoning).

The BX axioms that enable this:
- **BX13** (enrichment): p /\ (phi U psi) -> ((phi /\ S(p, psi)) U psi). Starting with phi U psi at n and TRUE (= p) at n, we get (phi /\ S(TRUE, psi)) U psi at n. The strengthened guard carries a Since witness.
- **BX5** (self-accumulation): phi U psi -> phi U (psi /\ (phi U psi)). The event gets strengthened.
- **BX6** (absorption): (psi /\ (phi U psi)) U psi -> phi U psi. Collapses double untils.

### Recommended Construction Strategy

**Approach A: Full Canonical Model on All MCS (Hard)**

Define the canonical preorder by futureSet inclusion, quotient by the equivalence relation (W1 ~ W2 iff W1 <= W2 and W2 <= W1), show the quotient is a linear order using BX11, and lift the truth lemma to the quotient.

Pros: Conceptually clean, follows the standard textbook approach.
Cons: ~400+ additional lines. The quotient construction is complex in Lean. Proving totality via BX11 requires intricate reasoning. Proving Until/Since truth lemma on the quotient requires careful lifting.

**Approach B: Integer Chain Construction (Medium)**

Build a chain M : Z -> MCS indexed by Z with:
- M(0) = the initial MCS containing neg phi
- M(n+1) extends futureSet(M(n)) union defect-witnessing formulas
- M(n-1) extends pastSet(M(n)) union defect-witnessing formulas

Pros: No need for totality proof. Z is automatically a linear order. Truth lemma only needs to work on the chain.
Cons: The defect enumeration requires either Atom to be countable or a finite subformula argument. The construction is more ad hoc. In Lean, building a function Z -> MCS with the right properties requires careful use of Classical.choice and well-founded recursion.

**Approach C: Abstract the LinearOrder (Pragmatic)**

Prove a weaker but sufficient result:

```lean
theorem completeness_core (phi : Formula Atom)
    (h_valid : forall (D : Type _) [LinearOrder D] [Nontrivial D]
      [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D), Satisfies M t phi) :
    Temporal.ThDerivable phi
```

Instead of building a LinearOrder on CanonicalWorld, observe that the proof only needs ONE countermodel. Build the countermodel on Z using the chain construction.

The chain construction for Z:
1. Start with M0 (MCS from Lindenbaum containing neg phi).
2. For each n >= 0: M(n+1) is any MCS extending futureSet(M(n)) (exists by mcs_g_witness applied with phi = bot -- wait, that gives futureSet(M(n)) is consistent, which follows from M(n) being consistent plus seriality).
3. For each n <= 0: M(n-1) is any MCS extending pastSet(M(n)).

Actually, the seriality already gives us the successor:
- mcs_g_witness with any phi: if G(phi) not in S, get T with futureSet(S) subset T. But we need T to exist unconditionally, not just when G(phi) not in S.
- Seriality (BX1): F(top) in S. So G(bot) not in S (since G(bot) = neg F(top)). Apply mcs_g_witness with phi = bot: get T with futureSet(S) subset T and bot not in T. Since bot not in any MCS, this T always exists. So: for any MCS S, exists MCS T with futureSet(S) subset T. QED.

This gives us the chain existence. The truth lemma for G/H follows. The truth lemma for Until/Since is harder but can be handled by building the chain more carefully.

**Recommended: Approach C (Integer Chain)**

This is the most feasible approach given the existing infrastructure. Here's the detailed plan:

### Detailed Construction Plan

#### Part 1: Chain Existence

```lean
-- For any MCS S, there exists an MCS T with futureSet(S) subset T
theorem mcs_future_successor (S : Set (Formula Atom))
    (h_mcs : Temporal.SetMaximalConsistent S) :
    exists T, Temporal.SetMaximalConsistent T /\ (forall psi, G(psi) in S -> psi in T) := by
  -- G(bot) not in S (from seriality)
  -- mcs_g_witness gives T with futureSet(S) subset T and bot not in T
  -- T is automatically MCS (from Lindenbaum)
```

Similarly for past successors.

#### Part 2: Chain Construction

```lean
noncomputable def chain (M0 : Set (Formula Atom)) (h_mcs : ...) : Int -> Set (Formula Atom) :=
  -- Use Int.rec or a well-founded construction
  -- Positive: iterate future successor from M0
  -- Negative: iterate past successor from M0
```

This requires Classical.choice at each step.

#### Part 3: Chain Properties

```lean
-- chain n is always an MCS
-- futureSet(chain n) subset chain(n+1)
-- pastSet(chain n) subset chain(n-1)
```

#### Part 4: Truth Lemma on Chain

The truth lemma on the chain model `(Z, val(n,p) := atom p in chain(n))`:

For G/H: Follows from chain properties + mcs_g_trans/mcs_h_trans.

For Until: This is the hard part. The truth lemma forward direction for phi U psi at chain(n) requires showing there exists m > n in Z with phi at chain(m) and psi at all chain(k) for n < k < m.

The approach: From phi U psi in chain(n):
1. By BX10: F(phi) in chain(n). By truth lemma for F (which reduces to G case): there exists m > n with phi in chain(m).
2. Take m = minimal such. Need psi in chain(k) for n < k < m.
3. By BX5 (self-accumulation): phi U psi implies phi U (psi /\ (phi U psi)). So the event carries phi U psi.
4. At the witness m: psi /\ (phi U psi) in chain(m). So phi U psi in chain(m).
5. For the guard: at each k in (n,m), we need to show psi in chain(k).

Step 5 is the crux. The argument uses induction on m - n:
- If m = n + 1: vacuously true (no k between n and n+1 in Z).
- If m > n + 1: phi U psi in chain(n). futureSet(chain(n)) subset chain(n+1). We need phi U psi to transfer to chain(n+1). But phi U psi is NOT in futureSet -- it's not a G-formula.

**Key insight**: phi U psi is NOT preserved by the futureSet transfer. We need a different argument.

The standard argument for the forward direction on Z-chains uses BX13 (enrichment) and BX6 (absorption):

From phi U psi in chain(n), define:
- alpha := phi U psi (the Until formula at n)
- At n: alpha in chain(n). top in chain(n).
- By BX13: top /\ alpha -> ((phi /\ S(top, psi)) U psi). So (phi /\ S(top, psi)) U psi in chain(n).
- S(top, psi) at k means: exists j < k with top at j and psi at all between j and k. I.e., psi held continuously from some past point to k.
- This enriched Until transfers along the chain because the guard now carries enough information.

Actually, this is still complex. Let me think about the reverse direction instead, which might be simpler.

**Reverse (semantic Until implies phi U psi in chain(n))**: Suppose there exists m > n with phi in chain(m) and psi in chain(k) for all n < k < m. Want: phi U psi in chain(n).

This is actually the easier direction. By induction on m - n:
- Base (m = n + 1): phi in chain(n+1), no guard needed (vacuous). Need phi U psi in chain(n). We have F(phi) in chain(n) (by truth lemma reverse for F). By BX12: F(phi) -> phi U top. So phi U top in chain(n). But we need phi U psi, not phi U top. The guard is psi, not top. Since m = n+1 and the guard is vacuous, phi U top suffices... no, phi U psi requires psi as guard, not top.

Hmm. phi U psi: event = phi at some future point, guard = psi at all intermediate. phi U top: event = phi at some future point, guard = top at all intermediate. These are different formulas with different membership in chain(n).

The reverse direction requires: from phi in chain(m) and psi in chain(k) for n < k < m, derive phi U psi in chain(n).

For m = n + 1: phi in chain(n+1), guard is vacuous. phi U psi in chain(n) means: semantically, exists s > n with event phi at s and guard psi between. Taking s = n+1, guard is vacuous. So semantically it holds. But we need MEMBERSHIP in chain(n), not semantic truth.

The truth lemma is circular here! We're trying to prove the truth lemma (semantic truth iff membership) and using semantic truth to argue membership. The reverse direction needs a purely syntactic/membership argument.

**Correct reverse direction (canonical model approach)**: Suppose G(psi) not in M(n). By mcs_g_witness: exists T with futureSet(M(n)) subset T and psi not in T. So the truth lemma reverse for G works. But for Until, the reverse direction on the CHAIN is:

If for all m > n with phi in chain(m), there exists k in (n,m) with psi not in chain(k), then phi U psi not in chain(n).

Contrapositive: phi U psi in chain(n) implies exists m > n with phi in chain(m) and psi in chain(k) for all k in (n,m).

This IS the forward direction. So the reverse direction is the contrapositive of the forward. The truth lemma reduces to showing:
- Forward: phi U psi in chain(n) -> semantically holds
- Reverse: semantically holds -> phi U psi in chain(n)

**For the reverse**: Suppose the semantic Until holds: exists m > n, phi in chain(m) and psi in chain(k) for n < k < m. Want phi U psi in chain(n).

Induction on m - n (over naturals):
- m - n = 1: phi in chain(n+1). Guard is vacuous. Need phi U psi in chain(n).
  - We have F(phi) in chain(n) (reverse G truth lemma: phi in chain(n+1) implies... hmm, this uses the truth lemma for phi which has lower complexity).
  - F(phi) in chain(n). By BX12: F(phi) -> phi U top. So phi U top in chain(n).
  - But we need phi U psi. From phi U top, can we get phi U psi?
  - BX2G: G(top -> psi) -> (phi U top -> phi U psi). So if G(top -> psi) in chain(n)...
  - G(top -> psi) = G(psi) essentially (since top -> psi is equivalent to psi modulo derivability).
  - Actually G(top -> psi) is not the same as G(psi). But top -> psi and psi are inter-derivable.
  - By necessitation of (top -> psi) <-> psi, and BX3: G(top -> psi) iff G(psi) in MCS.
  - So we need G(psi) in chain(n). But we DON'T have this in general.
  - In the m - n = 1 case, the guard is vacuous, so we don't need G(psi).
  - But syntactically, phi U psi requires the guard psi. Even when the guard is semantically vacuous (no intermediate points), the FORMULA phi U psi is different from phi U top.
  
  This is the core difficulty. The reverse Until truth lemma requires showing phi U psi membership from semantic conditions, and this requires reasoning about psi at intermediate points of the chain, not just the witness.

  **Resolution for m - n = 1**: We need a different argument. Since phi in chain(n+1) and the guard is vacuous, we need to show phi U psi in chain(n) purely from phi in chain(n+1).
  
  Claim: F(phi) in chain(n) -> phi U top in chain(n) (by BX12). Also psi U top in chain(n) is irrelevant. We need phi U psi.
  
  From phi U top in chain(n): event phi at some future, guard top between. The semantic model shows this holds for m = n+1 with phi at n+1 and top everywhere between.
  
  But we need phi U PSI, not phi U top. The key: when m = n+1, the guard psi between n and n+1 is vacuous SEMANTICALLY (no integer strictly between n and n+1). But SYNTACTICALLY, phi U psi and phi U top are different formulas with potentially different MCS membership.
  
  **On an integer-indexed chain, the semantic Until reduces to**: exists m > n with phi at m and psi at k for all n < k < m. On Z, if m = n+1, there ARE no integers strictly between n and n+1. So the guard is vacuously satisfied. But phi U psi in chain(n) as an MCS membership is about the FORMULA phi U psi being in the set chain(n), not about Z-semantic truth.
  
  This means: the truth lemma on a Z-indexed chain says phi U psi in chain(n) iff (exists m > n in Z with phi in chain(m) and psi in chain(k) for all n < k < m in Z). The reverse direction is NOT straightforward because MCS membership of phi U psi at chain(n) is a set-membership statement, not a semantic statement about the Z model.

### Critical Insight: Integer Chain is Insufficient

The integer chain approach has a fundamental problem: **Z is not dense**, so the semantic Until/Since on Z is weaker than the syntactic Until/Since in the BX axioms, which are sound for ALL linear orders including dense ones.

Specifically, on Z, "phi U psi at n" (semantically) means: exists m > n with phi at m and psi at k for all n < k < m. If m = n+1, the guard is vacuous. But the BX axioms were designed for dense linear orders where there are always points between any two. On Z, the guard is trivially satisfied in many cases.

This means: on Z, more formulas are satisfied than on dense orders. So a formula valid on all serial linear orders (including dense ones) might NOT be derivable from what the Z-chain shows.

Actually wait -- the completeness theorem says: valid on ALL serial linear orders implies derivable. The contrapositive is: not derivable implies exists a serial linear order model where it fails. We're building a SPECIFIC model (the chain on Z) where neg phi holds. The issue is whether our chain model is a SERIAL LINEAR ORDER that falsifies phi.

Z IS a serial linear order (with NoMaxOrder and NoMinOrder). And we build a valuation on Z that makes neg phi true at 0. The question is whether the truth lemma holds: does phi in chain(n) iff Satisfies (Z-model) n phi?

For Until, the forward direction (phi U psi in chain(n) implies semantic truth on Z) requires:
- phi in chain(n) implies exists m > n with phi in chain(m) and psi in chain(k) for n < k < m.
- On Z, there might not be any k between n and m if m = n+1.
- So the guard might be vacuously true even if psi is not in chain(n+1).
- But we only need phi at m. So if phi in chain(m) holds (by IH), we're fine.

Actually, this IS fine. The forward direction just needs to find the right m. phi U psi in chain(n) guarantees (by BX10) that F(phi) in chain(n), so there exists m > n with phi in chain(m). Taking m as the first such, the guard psi at intermediate chain points follows from... the BX axioms?

No, the issue is precisely that phi U psi in chain(n) is a membership statement, not a semantic statement on Z. We can't directly extract "psi in chain(k)" from "phi U psi in chain(n)" without the truth lemma, which we're trying to prove.

### Recommended Strategy: Rational Chain (Q or R instead of Z)

Use Q (rationals) or R (reals) instead of Z. On a dense linear order, the guard is never vacuously satisfied, which aligns better with the BX axiom design.

On Q: "phi U psi at q" means exists r > q with phi at r and psi at all s in (q,r). Since Q is dense, there are always points between q and r.

The chain construction on Q:
- Choose M(q) for each q in Q such that the truth lemma holds.
- This requires a more complex construction (not just successor iteration).

**Alternative: Use the completeness theorem's hypothesis directly.**

The validity hypothesis quantifies over ALL serial linear orders, including the canonical model itself. If we can show the canonical model (on all MCS) is a linear order, we're done. The truth lemma on the canonical model is MUCH cleaner because the canonical order is derived from MCS membership.

### Final Recommendation: Canonical Model Approach with Corrected Order

**Step 1: Fix the canonical order definition.**

The current `canonical_lt` is actually a preorder (reflexive). The correct definition for a strict order is:

```lean
def canonical_lt (W1 W2 : CanonicalWorld Atom) : Prop :=
  (forall psi, G(psi) in W1.val -> psi in W2.val) /\
  exists chi, chi in W2.val /\ chi not in W1.val
```

Or equivalently, define:
```lean
def canonical_le (W1 W2 : CanonicalWorld Atom) : Prop :=
  forall psi, G(psi) in W1.val -> psi in W2.val

def canonical_lt (W1 W2 : CanonicalWorld Atom) : Prop :=
  canonical_le W1 W2 /\ not (canonical_le W2 W1)
```

This is automatically irreflexive and transitive.

**Step 2: Prove totality using BX11.**

The totality proof: For any W1, W2, either canonical_le W1 W2 or canonical_le W2 W1.

Suppose neither. Then exists alpha with G(alpha) in W1 and alpha not in W2, AND exists beta with G(beta) in W2 and beta not in W1.

neg alpha in W2. By BX4: neg alpha -> G(P(neg alpha)). So G(P(neg alpha)) in W2. Combined with G(beta): by G-distribution, can derive G(P(neg alpha) /\ beta)... but this isn't quite right.

The argument needs BX11: F(neg alpha) /\ F(neg beta) -> ... This uses the negations of the G-formulas.

G(alpha) in W1 means neg F(neg alpha) in W1. Equivalently: F(neg alpha) not in W1.
But we want to work in a SINGLE MCS. The totality argument typically proceeds by contradiction in a single world.

Actually, let me reconsider. Totality of canonical_le means: for all W1 W2, either forall psi (G(psi) in W1 -> psi in W2) or forall psi (G(psi) in W2 -> psi in W1).

Suppose the first fails: exists alpha, G(alpha) in W1 and alpha not in W2. neg alpha in W2.
Suppose the second fails: exists beta, G(beta) in W2 and beta not in W1. neg beta in W1.

We need a contradiction. Consider the MCS W1: neg beta in W1 and G(alpha) in W1. Consider W2: neg alpha in W2 and G(beta) in W2.

The key is to use BX11 in W1 or W2 to derive a contradiction. But BX11 speaks about F(phi) /\ F(psi) -> ..., which requires diamond-like formulas. Since G(alpha) in W1, neg alpha not in W1. But F(neg alpha) might or might not be in W1.

Hmm. The BX11 totality argument is typically applied not to W1 and W2 directly but to a THIRD world that can see both. Since the canonical order is not yet built, we don't have a third world.

**Alternative totality argument**: Build a "connecting" MCS.

Given W1, W2 not comparable: exists alpha with G(alpha) in W1, alpha not in W2; exists beta with G(beta) in W2, beta not in W1.

Consider futureSet(W1) union futureSet(W2). If this is consistent, extend to MCS T. Then futureSet(W1) subset T and futureSet(W2) subset T, meaning W1 <= T and W2 <= T.

Is futureSet(W1) union futureSet(W2) consistent? If not, there exist L1 from futureSet(W1) and L2 from futureSet(W2) with L1 ++ L2 derives bot. By derive_g_contradiction twice: G(bot) in W1 (or W2), contradiction with seriality.

So futureSet(W1) union futureSet(W2) IS consistent (assuming W1 and W2 are both MCS). Extend to T. Now W1 <= T and W2 <= T.

But this doesn't give us W1 <= W2 or W2 <= W1. We just know both are below T.

**The correct totality argument uses BX11 inside T.**

alpha not in W2 means alpha not in T ... no, alpha might be in T.

Actually, alpha in T because G(alpha) in W1 and futureSet(W1) subset T, so alpha in T. Similarly beta in T.

This doesn't give a contradiction. We need a more refined argument.

**Standard totality proof (sketch from Burgess)**:

Totality of canonical_le: suppose not. Then W1 and W2 are incomparable. There exist:
- alpha with G(alpha) in W1, alpha not in W2
- beta with G(beta) in W2, beta not in W1

From W2: alpha not in W2, so neg alpha in W2. neg alpha in W2. Also G(beta) in W2.
From W1: beta not in W1, so neg beta in W1. Also G(alpha) in W1.

Now in W1: neg beta in W1. By BX4 (connect_future): neg beta -> G(P(neg beta)). So G(P(neg beta)) in W1.
In W2: neg alpha in W2. By BX4: neg alpha -> G(P(neg alpha)). So G(P(neg alpha)) in W2.

Now construct a common future world T from futureSet(W1) union futureSet(W2) (consistent as shown above). In T:
- alpha in T (from G(alpha) in W1)
- beta in T (from G(beta) in W2)
- P(neg beta) in T (from G(P(neg beta)) in W1)
- P(neg alpha) in T (from G(P(neg alpha)) in W2)

P(neg beta) in T: exists s < T with neg beta at s. But this refers to the canonical order, which we haven't finished building. Circular.

**Resolution**: The totality proof might need to be done differently. One approach is to show that the canonical preorder (canonical_le) can be extended to a linear order using Zorn's lemma or a similar principle, and that the truth lemma still holds on the extended order.

Actually, in the standard presentation (e.g., Goldblatt "Logics of Time and Computation"), the canonical model for tense logic uses:
- Worlds = MCS
- t < t' iff {alpha | G(alpha) in t} subset t' (strict subset, meaning futureSet(t) properly included in t')

But "properly included" doesn't make the relation total either.

**The standard trick**: Define t R t' iff for all alpha, G(alpha) in t implies alpha in t'. Then show R is a partial order (reflexive, transitive, antisymmetric when restricted to the equivalence classes). Then use BX11 to show totality.

Wait -- I was wrong earlier. G(alpha) in W does NOT imply alpha in W when G is the strict-future operator. G(alpha) says alpha at all STRICTLY future times. At the current time, alpha may or may not hold.

So canonical_le (futureSet inclusion) is NOT reflexive! Let me verify:

canonical_le W W means: for all psi, G(psi) in W implies psi in W.
G(psi) = neg F(neg psi). If G(psi) in W, does psi have to be in W?

In the BX axiom system, there is no axiom G(psi) -> psi (the T axiom for the temporal case). G is the strict-future operator.

So G(psi) in W does NOT imply psi in W in general. canonical_le is NOT reflexive.

**This changes the picture significantly.** The current code's `canonical_lt` (with both conditions futureSet and pastSet) is not reflexive, and it IS transitive. It might be a strict partial order already.

Let me verify irreflexivity: canonical_lt W W means futureSet(W) subset W and pastSet(W) subset W. Is this possible?

If G(psi) in W implies psi in W for all psi, and H(psi) in W implies psi in W for all psi, this is a very strong condition. It would mean W is "reflexive" in the canonical sense.

Actually, it IS possible for specific MCS. Consider an MCS W that contains alpha but not G(alpha) for any alpha. Then futureSet(W) = {} subset W trivially. So canonical_lt W W would hold (vacuously).

Wait, futureSet(W) = { psi | G(psi) in W }. If no G-formulas are in W, then futureSet(W) = {} and canonical_lt W W holds vacuously.

But can an MCS have no G-formulas? Recall G(psi) = neg F(neg psi). F(neg psi) = (neg psi) U top. So G(psi) not in W means F(neg psi) in W. If this holds for ALL psi, then F(neg psi) in W for all psi. In particular F(neg top) = F(bot) in W. But F(bot) = bot U top. Is bot U top always false? Semantically, bot U top at t means exists s > t with bot at s (impossible). So bot U top is always false. So F(bot) not in any MCS. Contradiction.

So it's NOT the case that no G-formulas are in W. There exists at least one psi with G(psi) in W. For instance, G(top) is in every MCS: G(top) = neg F(neg top) = neg F(bot). Since F(bot) not in any MCS (as argued above), neg F(bot) is in every MCS. So G(top) in W, meaning top in futureSet(W).

So top in futureSet(W), and top in W (since top is derivable and hence in every MCS). So canonical_lt W W holds at least for psi = top.

In fact, canonical_lt W W (the relation with both conditions) may well hold for many or all W, making it reflexive -- not the strict order we want.

**The correct definition**: Use the following strict order:

```
W1 < W2 iff:
  (forall psi, G(psi) in W1 -> psi in W2) AND
  NOT (forall psi, G(psi) in W2 -> psi in W1)
```

i.e., canonical_le W1 W2 and not canonical_le W2 W1. This is automatically irreflexive and transitive.

For totality: canonical_le W1 W2 or canonical_le W2 W1. This is what BX11 needs to establish.

## 6. BX Axiom Role Summary

| Axiom | Name | Role in Completeness |
|-------|------|---------------------|
| BX1 | serial_future | Seriality (NoMaxOrder): F(top) in every MCS ensures future successors exist |
| BX1' | serial_past | Seriality (NoMinOrder): P(top) in every MCS ensures past predecessors exist |
| BX2G | left_mono_until_G | Guard monotonicity -- used in Until truth lemma |
| BX2H | left_mono_since_H | Guard monotonicity -- used in Since truth lemma |
| BX3 | right_mono_until | Event monotonicity -- used in G-distribution (mcs_g_mp) |
| BX3' | right_mono_since | Event monotonicity -- used in H-distribution (mcs_h_mp) |
| BX4 | connect_future | Connectivity: phi -> G(P(phi)) -- links past and future sets; proves past_of_future_subset |
| BX4' | connect_past | Connectivity: phi -> H(F(phi)) -- dual; proves future_of_past_subset |
| BX5 | self_accum_until | Self-accumulation of Until -- used in Until truth lemma forward direction |
| BX5' | self_accum_since | Self-accumulation of Since -- dual |
| BX6 | absorb_until | Absorption of Until -- used for F-idempotency (mcs_ff_imp_f), which gives G-transitivity |
| BX6' | absorb_since | Absorption of Since -- used for P-idempotency (mcs_pp_imp_p), which gives H-transitivity |
| BX7 | linear_until | Linearity of Until -- used in Until truth lemma |
| BX7' | linear_since | Linearity of Since -- used in Since truth lemma |
| BX10 | until_F | Until implies eventuality -- connects Until to F for witness extraction |
| BX10' | since_P | Since implies past eventuality -- dual |
| BX11 | temp_linearity | Temporal linearity: F(phi)/\F(psi) trichotomy -- used for TOTALITY of canonical order |
| BX11' | temp_linearity_past | Past temporal linearity -- dual totality |
| BX12 | F_until_equiv | F(phi) -> phi U top -- connects F to Until |
| BX12' | P_since_equiv | P(phi) -> phi S top -- connects P to Since |
| BX13 | enrichment_until | Until-Since enrichment -- used in Until truth lemma |
| BX13' | enrichment_since | Since-Until enrichment -- dual |

### Critical Axiom Groups

1. **Seriality** (BX1, BX1'): Ensure NoMaxOrder/NoMinOrder of canonical model
2. **Transitivity** (BX6, BX6' via mcs_ff_imp_f/mcs_pp_imp_p -> mcs_g_trans/mcs_h_trans): Ensure transitivity of canonical order
3. **Totality** (BX11, BX11'): Ensure canonical order is total (linear)
4. **Connectivity** (BX4, BX4'): Link futureSet and pastSet; ensure antisymmetry-like properties
5. **Until/Since truth lemma** (BX5, BX6, BX7, BX10, BX12, BX13 and primes): Enable the hardest cases

## 7. Concrete Implementation Recommendations

### Priority 1: Fix the Canonical Order

Replace the current broken `canonical_lt` with:

```lean
def canonical_le (W1 W2 : CanonicalWorld Atom) : Prop :=
  forall psi, Formula.all_future psi in W1.val -> psi in W2.val

def canonical_lt (W1 W2 : CanonicalWorld Atom) : Prop :=
  canonical_le W1 W2 /\ not (canonical_le W2 W1)
```

Prove:
- Transitivity of canonical_le (from mcs_g_trans, already essentially proven)
- Totality of canonical_le (requires BX11 argument -- see below)
- Irreflexivity and transitivity of canonical_lt (automatic from above)

### Priority 2: Prove Totality via BX11

The totality proof for canonical_le is the key missing piece. The argument:

Suppose canonical_le W1 W2 fails: exists alpha, G(alpha) in W1 and alpha not in W2.
Suppose canonical_le W2 W1 fails: exists beta, G(beta) in W2 and beta not in W1.

neg alpha in W2, neg beta in W1.

In W1: neg beta and G(alpha) are both in W1.
By BX4: neg beta -> G(P(neg beta)). So G(P(neg beta)) in W1.
By mcs_g_mp: G(alpha) and G(alpha -> alpha) in W1. So alpha propagates.

The BX11 argument applied in a future-successor T of W1:
- G(alpha) in W1, alpha in T (futureSet transfer)
- G(P(neg beta)) in W1, P(neg beta) in T

Similarly from W2 through a future-successor S of W2:
- G(beta) in W2, beta in S
- G(P(neg alpha)) in W2, P(neg alpha) in S

Now use BX11 in T (or construct a world that sees both): F(neg alpha) and F(neg beta) in some common world...

This requires further analysis. The standard proof constructs the contradiction within a single MCS using the linearity axiom. The exact MCS-level argument should be worked out separately.

### Priority 3: Build LinearOrder Instance

Once totality is proven, construct:
```lean
instance : LinearOrder (CanonicalWorld Atom) where
  le := canonical_le
  lt := canonical_lt
  le_refl := ... -- NOT trivially true! Need to show G(psi) in W -> psi in W is possible
```

Wait -- canonical_le is NOT reflexive (as analyzed above). G(psi) in W does not imply psi in W since G is the strict-future operator.

So canonical_le is NOT a preorder. It's a relation that is transitive but not reflexive.

This means we should directly build a **StrictOrder** (irreflexive + transitive) and then derive a LinearOrder using `linearOrderOfSTO` or similar Mathlib machinery.

But LinearOrder requires le (which is reflexive). The standard approach:
- Define `W1 <= W2` iff `W1 < W2 or W1 = W2`
- This requires deciding equality on CanonicalWorld, which needs extensionality.

Actually for the completeness theorem, what we need is:
1. A type with LinearOrder, Nontrivial, NoMaxOrder, NoMinOrder
2. A TemporalModel on that type
3. A world in that type where the truth lemma holds

We can potentially avoid building a full LinearOrder on CanonicalWorld. Instead:

**Option**: Use a QUOTIENT of the canonical preorder, or use the Subtype of a linearly ordered subset, or use a well-order argument.

**Simpler option**: Just build the LinearOrder using Lean 4's `LinearOrder.mk'` or manually define all fields using canonical_le with totality.

### Priority 4: Truth Lemma for Until/Since

The Until truth lemma forward direction is the hardest remaining piece. The approach:

**Forward**: phi U psi in W. Want: exists T > W with Sat(T, phi) and forall S in (W,T), Sat(S, psi).

By IH, Sat(S, alpha) iff alpha in S.val for subformulas alpha.

phi U psi in W. By BX10: F(phi) in W. By truth lemma for F (reduces to G case): exists T > W with phi in T.val. (This uses canonical_le W T and phi in T.val.)

Take T to be any such world with phi in T.val. Need psi in S.val for all S with W < S < T.

From phi U psi in W: we need to show the guard psi holds at intermediate worlds. The argument uses BX7 (linear_until), BX5 (self_accum_until), and BX13 (enrichment_until) to establish that the syntactic Until membership propagates correctly along the canonical order with the guard being satisfied at each step.

The key lemma: if phi U psi in W and canonical_le W S and S < T (where T is the witness for phi), then psi in S.val.

This follows from: phi U psi in W -> the guard psi should hold at all intermediate canonical worlds between W and the Until-witness T.

The proof uses BX7 (linearity of Until): if phi U psi in W and theta U chi in W, the two Untils have compatible witness points. This ensures the canonical order respects Until semantics.

### Summary of Remaining Work

1. **Fix canonical order** (~50 lines): Redefine using canonical_le (futureSet inclusion) as the base relation
2. **Prove totality** (~100 lines): Use BX11 (temp_linearity) -- the most novel and difficult piece
3. **Build LinearOrder instance** (~50 lines): Combine irreflexivity, transitivity, totality
4. **Prove seriality** (~30 lines): NoMaxOrder from mcs_g_witness, NoMinOrder from mcs_h_witness, Nontrivial from having two distinct MCS
5. **Truth lemma for Until** (~100 lines): Forward direction using BX5/BX10/BX7/BX13; reverse using mcs_g_witness-style argument
6. **Truth lemma for Since** (~80 lines): Symmetric to Until
7. **Close the completeness sorry** (~20 lines): Apply h_valid to canonical model, use truth lemma

**Estimated total additional code**: ~430 lines
**Current file**: 418 lines with 2 sorries
**Estimated final**: ~850 lines

The hardest components are (2) totality and (5) Until truth lemma. Both require novel MCS-level reasoning with the BX axioms that has no direct template in the modal completeness proof.
