/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

import Cslib.Languages.InteractionNets.Combinators

/-! Examples of reduction steps of the interaction combinators. -/

namespace CslibTests

open FirstOrder Language Cslib.InteractionNets

/-- The term `con(t, u)`. -/
abbrev con (t u : combinators.Term String) : combinators.Term String :=
  func Combinator.con ![t, u]

/-- The term `dup(t, u)`. -/
abbrev dup (t u : combinators.Term String) : combinators.Term String :=
  func Combinator.dup ![t, u]

/-- The term `era`. -/
abbrev era : combinators.Term String := func Combinator.era ![]

/-- An Interaction without internal names: `⟨ | era = era⟩ ⭢ ⟨ | ⟩`. -/
example : (⟨[], s(era, era) ::ₘ 0⟩ : Configuration combinators String)
    ⭢[interactionCombinators] ⟨[], 0⟩ := by
  refine Step.interaction (R := interactionCombinators) [] 0 Combinator.era Combinator.era
    ![] ![] eraEra var rfl
    ⟨fun i => i.elim0, fun j => j.elim0, id, ?_, ?_⟩
  · intro x hx
    exact absurd hx.1 (Multiset.notMem_zero x)
  · intro x _ hx
    exact absurd hx.1 (Multiset.notMem_zero x)

/-- A Collect: `⟨x | x = era⟩ ⭢ ⟨era | ⟩`. -/
example : (⟨[var "x"], s(var "x", era) ::ₘ 0⟩ : Configuration combinators String)
    ⭢[interactionCombinators] ⟨[era], 0⟩ :=
  Step.collect [var "x"] 0 "x" era (by decide)

/-- The substitution used to instantiate `conDup` on the active pair `con(p, q) = dup(r, s)`:
the internal names `a`, `b`, `c`, `d` are kept, since they do not occur in the configuration. -/
def σ : String → combinators.Term String := fun x =>
  if x = "x1" then var "p" else if x = "x2" then var "q"
  else if x = "y1" then var "r" else if x = "y2" then var "s" else var x

/-- The internal names of `conDup`. -/
theorem conDup_isInternal (x : String) (h : conDup.IsInternal x) : x ∈ ["a", "b", "c", "d"] := by
  have key : ∀ x ∈ conDup.Δ.bind Equation.names,
      (∀ i, x ≠ conDup.xNames i) → (∀ j, x ≠ conDup.yNames j) → x ∈ ["a", "b", "c", "d"] := by
    decide
  exact key x h.1 h.2.1 h.2.2

/-- The instance of `conDup` given by `σ`. -/
theorem conDup_subst : conDup.Δ.map (fun e => e.subst σ) + 0 =
    ({s(var "p", dup (var "a") (var "b")), s(var "q", dup (var "c") (var "d")),
      s(var "r", con (var "a") (var "c")), s(var "s", con (var "b") (var "d"))} :
      Multiset (Equation combinators String)) := by
  decide

/-- An Interaction with internal names:
`⟨ | con(p, q) = dup(r, s)⟩ ⭢ ⟨ | p = dup(a, b), q = dup(c, d), r = con(a, c), s = con(b, d)⟩`. -/
example :
    (⟨[], s(con (var "p") (var "q"), dup (var "r") (var "s")) ::ₘ 0⟩ :
      Configuration combinators String)
    ⭢[interactionCombinators]
    ⟨[], {s(var "p", dup (var "a") (var "b")), s(var "q", dup (var "c") (var "d")),
      s(var "r", con (var "a") (var "c")), s(var "s", con (var "b") (var "d"))}⟩ := by
  rw [← conDup_subst]
  refine Step.interaction (R := interactionCombinators) [] 0 Combinator.con Combinator.dup
    _ _ conDup σ rfl
    ⟨?_, ?_, id, ?_, fun _ _ _ _ h => h⟩
  · exact Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  · exact Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  · intro x hx
    have hmem := conDup_isInternal x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by decide⟩

end CslibTests
