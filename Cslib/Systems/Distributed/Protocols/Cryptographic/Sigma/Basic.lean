/-
Copyright (c) 2026 Christiano Braga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christiano Braga
-/

module

public import Mathlib.Tactic

@[expose] public section

/-!
A Sigma Protocol for R is a pair (P, V).

- P is an interactive protocol algorithm called the prover, which takes as input a witness-statement
  pair (x, y) ∈ R.
- V is an interactive protocol algorithm called the verifier, which takes as input a statement
  y ∈ Y, and which outputs accept or reject.
- P and V are structured so that an interaction between them always works as follows:

1. To start the protocol, P computes a message t, called the commitment, and sends t to V.
2. Upon receiving P's commitment t, V chooses a challenge c at random from a finite challenge space
   C, and sends c to P.
3. Upon receiving V's challenge c, P computes a response z, and sends z to V.
4. Upon receiving P's response z, V outputs either accept or reject, which must be computed strictly
   as a function of the statement y and the conversation (t, c, z). In particular, V does not make
   any random choices other than the selection of the challenge — all other computations are
   completely deterministic.

Reference:

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup],
  Section 19.4.

Note: The notion of an _effective relation_ is implicit in the definition of a Sigma protocol.
      The relation R must be decidable, and the prover must be able to efficiently compute the
      commitment and response functions, while the verifier must be able to efficiently compute
      the verification function. In practice, these efficiency requirements are crucial for
      the security and usability of the protocol, but they are not explicitly formalized in this
      definition.
-/

universe u v w x y

class SigmaProtocol
    (Statement : Type u) (Witness : Type v)
    (Commitment : Type w) (Challenge : Type x)
    (Response : Type y) where
  rel : Statement → Witness → Prop
  commit : Statement → Witness → Commitment
  respond : Statement → Witness → Commitment → Challenge → Response
  verify : Statement → Commitment → Challenge → Response → Prop
  extract : Statement → Commitment →
            Challenge → Response →
            Challenge → Response → Witness
  simulate : Statement → Challenge → Commitment × Response
  -- Non-degeneracy: the relation is inhabited for some statement-witness pair,
  -- ensuring that completeness is not vacuously true.
  nonDegenerate : ∃ (s : Statement) (w : Witness), rel s w
  -- Properties that every instance must satisfy
  complete : ∀ (s : Statement) (w : Witness) (e : Challenge),
               rel s w →
               verify s (commit s w) e (respond s w (commit s w) e)
  sound    : ∀ (s : Statement) (a : Commitment) (e e' : Challenge) (z z' : Response),
               e ≠ e' →
               verify s a e z →
               verify s a e' z' →
               rel s (extract s a e z e' z')
  shvzk    : ∀ (s : Statement) (e : Challenge),
               let (a, z) := simulate s e
               verify s a e z
