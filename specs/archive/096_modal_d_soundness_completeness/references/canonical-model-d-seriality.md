# Canonical Model Completeness for Modal Logic D (Serial Frames)

Extracted from: Open Logic Project, "Normal Modal Logics" (rev 9f12419, 2026-05-25), Chapter 4.
Source PDF: `openlogicproject-normal-modal-logic.pdf` in this directory.

## Key Definitions

### Complete Sigma-Consistent Set (= MCS)

**Definition 4.1** (p.46): A set Gamma is *complete Sigma-consistent* iff it is Sigma-consistent
and for every phi, either phi in Gamma or neg phi in Gamma.

### Canonical Model

**Definition 4.11** (p.51): The canonical model for Sigma is M^Sigma = <W^Sigma, R^Sigma, V^Sigma> where:
1. W^Sigma = {Delta : Delta is complete Sigma-consistent}
2. R^Sigma Delta Delta' holds iff box^{-1} Delta subseteq Delta'
   (equivalently: for all psi, box psi in Delta implies psi in Delta')
3. V^Sigma(p) = {Delta : p in Delta}

### Box-Inverse Notation

**Definition 4.5** (p.49):
- box Gamma = {box psi : psi in Gamma}
- diamond Gamma = {diamond psi : psi in Gamma}
- box^{-1} Gamma = {psi : box psi in Gamma}
- diamond^{-1} Gamma = {psi : diamond psi in Gamma}

## Truth Lemma

**Proposition 4.12** (p.51): For every formula phi, M^Sigma, Delta |= phi iff phi in Delta.

Proof by induction on phi. The box case uses:
- Left-to-right (box): If box phi in Delta then for all Delta' with R^Sigma Delta Delta',
  phi in Delta' (by definition of R^Sigma).
- Right-to-left (box): If box phi not in Delta, by Proposition 4.8 there exists a complete
  Sigma-consistent Delta' with box^{-1} Delta subseteq Delta' and phi not in Delta'.
  Then R^Sigma Delta Delta' and M^Sigma, Delta' |/= phi.

## Seriality of the Canonical Model for D

**Theorem 4.16** (p.53): If a normal modal logic Sigma contains D (box phi -> diamond phi),
then the canonical model for Sigma is serial.

**Proof** (p.53, first paragraph):
Suppose Sigma contains D, and let Delta in W^Sigma; we need to show that there is a Delta'
such that R^Sigma Delta Delta'. It suffices to show that box^{-1} Delta is Sigma-consistent,
for then by Lindenbaum's Lemma, there is a complete Sigma-consistent set
Delta' supseteq box^{-1} Delta, and by definition of R^Sigma we have R^Sigma Delta Delta'.

So, suppose for contradiction that box^{-1} Delta is *not* Sigma-consistent, i.e.,
box^{-1} Delta |-_Sigma bot. By Lemma 4.7, Delta |-_Sigma box bot, and since Sigma
contains D, also Delta |-_Sigma diamond bot (Proposition 3.7). But Sigma is normal,
so Sigma |- neg diamond bot (Proposition 3.7), whence also Delta |-_Sigma neg diamond bot,
against the consistency of Delta.

### Key supporting lemmas:
- **Lemma 4.7** (p.50): If box^{-1} Gamma |-_Sigma phi then Gamma |-_Sigma box phi.
- **Proposition 3.7** (p.31): Every normal modal logic Sigma contains neg diamond bot.
  (Proof: By NEC on tautology neg bot, get box(neg bot). By K, box(neg bot) -> (box bot -> box(neg bot)). So box(neg bot) in Sigma. Since neg diamond bot = box neg bot iff neg(neg box neg bot) = neg diamond bot... Actually the key fact is: Sigma |- box T (by NEC on tautology T), and box T -> neg box bot by tautological reasoning + K.)

### Reformulation for our Lean codebase:

The argument in the Lean codebase's terms:
1. Given MCS S (for DAxiom), we need to find MCS T with R S T (i.e., for all psi, box psi in S -> psi in T).
2. It suffices to show {psi | box psi in S} is consistent.
3. Suppose not: {psi | box psi in S} |- bot.
4. By the iterated deduction / box-from-box-context mechanism: S contains box bot.
5. Since DAxiom includes modalD, S contains box bot -> diamond bot (i.e., box bot -> neg box neg bot).
6. So diamond bot in S.
7. But every normal modal logic proves neg diamond bot (i.e., box neg bot, since diamond bot = neg box neg bot = (box(phi -> bot)) -> bot with phi = anything... Actually diamond bot = neg box neg bot. And neg diamond bot = box neg bot. Wait: diamond phi = neg box neg phi, so diamond bot = neg box neg bot = neg box T. But neg diamond bot = box T = box(bot -> bot). By NEC on bot -> bot, we get box(bot -> bot) in S. That means neg diamond bot in S.
8. Contradiction with diamond bot in S.

Actually more precisely in the Lean encoding: diamond phi = (box(phi -> bot)) -> bot.
So diamond bot = (box(bot -> bot)) -> bot. And neg(diamond bot) = (diamond bot) -> bot.

The key insight: bot -> bot is a tautology, so box(bot -> bot) is derivable by NEC.
So box(bot -> bot) in S. Then diamond bot = (box(bot -> bot)) -> bot would mean
bot in S (by MP with box(bot -> bot) in S). But bot not in MCS. Contradiction.

Wait, let me re-examine. diamond bot = neg(box(neg bot)) = (box(neg bot)) -> bot.
neg bot = bot -> bot. So diamond bot = (box(bot -> bot)) -> bot.

If box bot in S, then by axiom D: box bot -> diamond bot, so diamond bot in S.
diamond bot = (box(bot -> bot)) -> bot.
But bot -> bot is derivable (tautology), so box(bot -> bot) is derivable (by NEC), so box(bot -> bot) in S.
Then by MP: (box(bot -> bot)) -> bot and box(bot -> bot) gives bot in S.
But bot not in MCS. Contradiction.

So the full chain is:
1. Assume {psi | box psi in S} is inconsistent.
2. Then box bot in S (by Lemma 4.7 / derive_box_from_box_context).
3. By axiom D: diamond bot in S.
4. By NEC on tautology (bot -> bot): box(bot -> bot) in S.
5. diamond bot = (box(bot -> bot)) -> bot, so bot in S.
6. Contradiction with MCS.

## Completeness Theorem

**Theorem 4.17** (p.54): For any schemas phi_1, ..., phi_n among D, T, B, 4, and 5,
the system K phi_1 ... phi_n is determined by the class of models
C = C_{phi_1} intersect ... intersect C_{phi_n}.

This gives completeness for KD (= system D) with respect to the class of serial models.

## Soundness of Axiom D

**Theorem 2.1/3.31** (pp.18,40): Axiom D (box phi -> diamond phi) is valid in all serial models.

Proof: Let M = <W,R,V> be serial and w in W. Suppose M,w |= box phi.
Since R is serial, there exists w' with Rww'. Then M,w' |= phi.
So there exists w' with Rww' and M,w' |= phi, hence M,w |= diamond phi.
