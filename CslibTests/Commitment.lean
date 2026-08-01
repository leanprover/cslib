/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Crypto.Protocols.Commitment.Basic

namespace CslibTests.Commitment

open Cslib.Crypto.Protocols.Commitment
open Cslib.Probability.PMF
open scoped NNReal

example {α β : Type*} [Fintype α] [Fintype β] {p q : PMF α} {ε : ℝ≥0}
    (h : StatisticallyClose p q ε) (kernel : α → PMF β) :
    StatisticallyClose (p.bind kernel) (q.bind kernel) ε :=
  h.bind kernel

/-- A toy scheme that reveals nothing and accepts every opening. -/
noncomputable def opaqueScheme (Message : Type*) : Scheme Message Unit Unit :=
  Scheme.ofPure (fun _ => ((), ())) (fun _ _ _ => true) (by simp)

theorem opaqueScheme_perfectlyHiding (Message : Type*) :
    (opaqueScheme Message).PerfectlyHiding := by
  simp [Scheme.PerfectlyHiding, opaqueScheme, Scheme.commitmentDist, Scheme.ofPure]

example (Message : Type*) : (opaqueScheme Message).StatisticallyHiding 0 :=
  ((opaqueScheme Message).perfectlyHiding_iff_statisticallyHiding_zero).mp
    (opaqueScheme_perfectlyHiding Message)

/-- A toy scheme whose commitment is the message itself. -/
noncomputable def revealingScheme (Message : Type*) [DecidableEq Message] :
    Scheme Message Message Unit :=
  Scheme.ofPure (fun message => (message, ()))
    (fun message commitment _ => decide (commitment = message)) (by simp)

theorem revealingScheme_perfectlyBinding (Message : Type*) [DecidableEq Message] :
    (revealingScheme Message).PerfectlyBinding := by
  simp [Scheme.PerfectlyBinding, Scheme.Accepts, revealingScheme, Scheme.ofPure]

end CslibTests.Commitment
