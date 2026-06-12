/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Semantics.Satisfies
public import Cslib.Logics.Temporal.Syntax.Context
public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Order.SuccPred.Archimedean

/-! # Temporal Validity and Semantic Consequence

This module defines semantic validity and consequence for temporal logic formulas
evaluated on linear orders.

## Validity Hierarchy

The validity definitions form a hierarchy based on the frame conditions imposed
on the time domain:

```
Valid (LinearOrder + Nontrivial)
  |
ValidSerial (+ NoMaxOrder + NoMinOrder)
  /     \
ValidDense          ValidDiscrete
(+ DenselyOrdered)  (+ SuccOrder + PredOrder + IsSuccArchimedean)
```

- `Valid`: formula holds in all nontrivial linear orders.
- `ValidSerial`: formula holds in all serial (no endpoints) linear orders.
- `ValidDense`: formula holds in all dense serial linear orders.
- `ValidDiscrete`: formula holds in all discrete serial linear orders.

Validity at a higher level implies validity at all lower levels. Dense and
discrete are incomparable (neither implies the other).

## Main Definitions

- `Temporal.Valid`, `Temporal.ValidSerial`, `Temporal.ValidDense`,
  `Temporal.ValidDiscrete`: Validity quantified over appropriate linear orders.
- `Temporal.SemanticConsequence`: Semantic consequence from a context.
- `Temporal.Satisfiable`, `Temporal.FormulaSatisfiable`: Satisfiability.

## Main Results

- `valid_implies_valid_serial`, `valid_implies_valid_dense`,
  `valid_implies_valid_discrete`: Reduction lemmas for the validity hierarchy.
- `valid_serial_implies_valid_dense`, `valid_serial_implies_valid_discrete`.
- `valid_iff_empty_consequence`: Validity is consequence from the empty context.
- `consequence_monotone`: Semantic consequence is monotone in the context.
- `valid_modus_ponens`: Modus ponens preserves validity.
- `satisfiable_not_valid_neg`: A satisfiable formula's negation is not valid.

## Note on Universe Levels

All validity definitions quantify over `(D : Type)` (not `Type*`) to avoid
universe polymorphism issues, matching the bimodal `valid` pattern.
-/

@[expose] public section

namespace Cslib.Logic.Temporal

variable {Atom : Type*}

/-- A formula is valid if it is true in all nontrivial linear orders,
all models, and at all time points.

Uses `Type` (not `Type*`) to avoid universe level issues. -/
def Valid (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [LinearOrder D] [Nontrivial D]
    (M : TemporalModel D Atom) (t : D),
    Satisfies M t φ

/-- A formula is valid over serial linear orders (no maximum or minimum). -/
def ValidSerial (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [LinearOrder D] [Nontrivial D]
    [NoMaxOrder D] [NoMinOrder D]
    (M : TemporalModel D Atom) (t : D),
    Satisfies M t φ

/-- A formula is valid over dense serial linear orders. -/
def ValidDense (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [LinearOrder D] [Nontrivial D]
    [NoMaxOrder D] [NoMinOrder D] [DenselyOrdered D]
    (M : TemporalModel D Atom) (t : D),
    Satisfies M t φ

/-- A formula is valid over discrete serial linear orders. -/
def ValidDiscrete (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [LinearOrder D] [Nontrivial D]
    [NoMaxOrder D] [NoMinOrder D]
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D]
    (M : TemporalModel D Atom) (t : D),
    Satisfies M t φ

/-- Semantic consequence: φ follows from context Γ in all nontrivial
linear orders. -/
def SemanticConsequence (Γ : Context Atom) (φ : Formula Atom) : Prop :=
  ∀ (D : Type) [LinearOrder D] [Nontrivial D]
    (M : TemporalModel D Atom) (t : D),
    (∀ ψ ∈ Γ, Satisfies M t ψ) →
    Satisfies M t φ

/-- A formula is satisfiable if there exists some nontrivial model and time
where it holds. The `Nontrivial` requirement matches the `Valid` quantifier,
ensuring satisfiability and validity are properly dual. -/
def Satisfiable (φ : Formula Atom) : Prop :=
  ∃ (D : Type) (_ : LinearOrder D) (_ : Nontrivial D)
    (M : TemporalModel D Atom) (t : D),
    Satisfies M t φ

/-- A formula is satisfiable (alternative name). -/
abbrev FormulaSatisfiable (φ : Formula Atom) : Prop := Satisfiable φ

namespace Validity

/-! ## Validity Reduction Lemmas -/

/-- Validity implies validity over serial orders. -/
theorem valid_implies_valid_serial {φ : Formula Atom}
    (h : Valid φ) : ValidSerial φ :=
  fun D _ _ _ _ M t => h D M t

/-- Validity implies validity over dense orders. -/
theorem valid_implies_valid_dense {φ : Formula Atom}
    (h : Valid φ) : ValidDense φ :=
  fun D _ _ _ _ _ M t => h D M t

/-- Validity implies validity over discrete orders. -/
theorem valid_implies_valid_discrete {φ : Formula Atom}
    (h : Valid φ) : ValidDiscrete φ :=
  fun D _ _ _ _ _ _ _ M t => h D M t

/-- Serial validity implies dense validity. -/
theorem valid_serial_implies_valid_dense {φ : Formula Atom}
    (h : ValidSerial φ) : ValidDense φ :=
  fun D _ _ _ _ _ M t => h D M t

/-- Serial validity implies discrete validity. -/
theorem valid_serial_implies_valid_discrete {φ : Formula Atom}
    (h : ValidSerial φ) : ValidDiscrete φ :=
  fun D _ _ _ _ _ _ _ M t => h D M t

/-! ## Validity and Consequence Relationship -/

/-- Valid formulas are consequences of the empty context. -/
theorem valid_iff_empty_consequence (φ : Formula Atom) :
    Valid φ ↔ SemanticConsequence [] φ := by
  constructor
  · intro h D _ _ M t _
    exact h D M t
  · intro h D _ _ M t
    apply h D M t
    intro ψ hψ
    exact absurd hψ (List.not_mem_nil)

/-- Semantic consequence is monotonic: more premises, same conclusion. -/
theorem consequence_monotone {Γ Δ : Context Atom} {φ : Formula Atom}
    (h_sub : Γ ⊆ Δ) (h_cons : SemanticConsequence Γ φ) :
    SemanticConsequence Δ φ := by
  intro D _ _ M t h_delta
  exact h_cons D M t (fun ψ hψ => h_delta ψ (h_sub hψ))

/-- If a formula is valid, it is a consequence of any context. -/
theorem valid_consequence (φ : Formula Atom) (Γ : Context Atom)
    (h : Valid φ) : SemanticConsequence Γ φ :=
  fun D _ _ M t _ => h D M t

/-- Membership in context implies semantic consequence. -/
theorem consequence_of_member {Γ : Context Atom} {φ : Formula Atom}
    (h : φ ∈ Γ) : SemanticConsequence Γ φ := by
  intro _ _ _ _ _ h_all
  exact h_all φ h

/-! ## Modus Ponens and Satisfiability -/

/-- Modus ponens preserves validity. -/
theorem valid_modus_ponens {φ ψ : Formula Atom}
    (h_imp : Valid (φ.imp ψ)) (h_phi : Valid φ) :
    Valid ψ :=
  fun D _ _ M t => h_imp D M t (h_phi D M t)

/-- A satisfiable formula's negation is not valid. -/
theorem satisfiable_not_valid_neg {φ : Formula Atom}
    (h : Satisfiable φ) : ¬ Valid (¬φ) := by
  intro h_valid
  obtain ⟨D, hord, hnt, M, t, h_sat⟩ := h
  have h_neg := @h_valid D hord hnt M t
  exact h_neg h_sat

end Validity

end Cslib.Logic.Temporal
