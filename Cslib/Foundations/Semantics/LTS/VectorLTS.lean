/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Vectors Labelled Transition System (LTS)

Defined vectors of labelled transition systems, an abstraction that frequently
pops up in the semantics of cryptography, distributed computing, game theory,and concurrency theory.

In particular, there are two "views" of a vector LTSes,
1. As a vector of many `Entity → LTS State Label` representing multiple
labelled transition systems, each of which corresponds to the local view
of a node/entity `e : Entity`.

2. As a single LTS with a state vector `LTS (Fin n → State) (Fin n → Label)`.
This is the global view of the system in operation

We prove theorems to transition between these two views. This is a common
theme that occurs in all the aforementioned areas where such labelled transition
systems are used. Further we provide notions of fair executions, step
transitions of individual nodes, scheduling, and fairness.

-/

@[expose] public section

namespace Cslib

/--
An indexed collection of LTSes. Each component LTS represents
the local view of an entity.
-/
abbrev LTSVec (Entity : Type u) (State Label : Entity → Type*) :=
  (e : Entity) → LTS (State e) (Label e)

/--
An LTS of vector states and vector labels. A labelled transition system
which represents the global view of a collection of LTSes, collectively
transition for each input vector label to their next states. This
matches how synchronous distributed systems behave
-/
abbrev SynchronousVecLTS (Entity : Type u) (State Label : Entity → Type*) :=
  LTS ((e : Entity) → State e) ((e : Entity) → Label e)

def LTSVec.toSynchronousVecLTS {Entity} {State Label : Entity → Type*}
    (l : LTSVec Entity State Label) : SynchronousVecLTS Entity State Label  where
  Tr s μ s' := ∀ e, (l e).Tr (s e) (μ e) (s' e)

def AsynchronousVecLTS (Entity : Type u) (State Label : Entity → Type*) :=
  LTS ((e : Entity) → State e) (Σ (e : Entity), Label e)
/--
A model of an asynchronously advancing collection of LTSes. This abstracts
the behaviour of asynchronous distributed systems.
-/
abbrev LTSVec.toAsynchronousVecLTS (Entity : Type u)
    (State Label : Entity → Type*)
    (l : LTSVec Entity State Label) :
    AsynchronousVecLTS Entity State Label where
  Tr := fun s ⟨e, μe⟩ s' =>
    (l e).Tr (s e) μe (s' e) ∧ ∀ e' ≠ e, s e = s' e

end Cslib
