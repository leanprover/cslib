/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.MapHom

/-! # Lifting the labels of an LTS to `Option`

`lts.liftOption` reads every label `μ` of `lts` as `some μ` and has no transitions on `none`. This
is how an `NA` becomes an `εNA` without ε-transitions.

## Main definitions

* `LTS.liftOption lts`: the transitions of `lts` on `some μ`, and none on `none`.

## Main statements

* `LTS.isBisimulation_liftOption_mapLabel_some`: reading `lts.liftOption` back through `some`
  gives `lts`, so equality is a bisimulation between the two.
* `LTS.liftOption_mTr_iff`: the runs of `lts.liftOption` are the runs of `lts`, read through
  `some`.
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*}

/-- The LTS with the transitions of `lts` on `some μ` for each label `μ`, and none on `none`. -/
def liftOption (lts : LTS State Label) : LTS State (Option Label) where
  Tr s μ s' := match μ with
    | some μ => lts.Tr s μ s'
    | none => False

/-- The transitions of `lts.liftOption` on `some μ` are those of `lts` on `μ`. -/
@[simp]
theorem liftOption_tr_some {lts : LTS State Label} {s s' : State} {μ : Label} :
    lts.liftOption.Tr s (some μ) s' ↔ lts.Tr s μ s' := Iff.rfl

/-- `lts.liftOption` has no transitions on `none`. -/
@[simp]
theorem liftOption_not_tr_none {lts : LTS State Label} {s s' : State} :
    ¬lts.liftOption.Tr s none s' := id

/-- Reading the transitions of `lts.liftOption` back through `some` gives those of `lts`, so
equality is a bisimulation between the two. -/
theorem isBisimulation_liftOption_mapLabel_some {lts : LTS State Label} :
    IsBisimulation (lts.liftOption.mapLabel some) lts Eq := by
  rintro s _ rfl μ
  simp

/-- The runs of `lts.liftOption` are the runs of `lts`, read through `some`. -/
theorem liftOption_mTr_iff {lts : LTS State Label} {s t : State} {μs : List (Option Label)} :
    lts.liftOption.MTr s μs t ↔ ∃ μs' : List Label, μs = μs'.map some ∧ lts.MTr s μs' t := by
  have hb : IsBisimulation (lts.liftOption.mapLabel some) lts Eq :=
    isBisimulation_liftOption_mapLabel_some
  constructor
  · intro h
    -- A run of `lts.liftOption` never reads `none`; the bisimulation does the rest.
    obtain ⟨μs', rfl⟩ : ∃ μs' : List Label, μs = μs'.map some := by
      induction h with
      | refl => exact ⟨[], rfl⟩
      | @stepL _ μ _ _ _ htr _ ih =>
        obtain ⟨μs', rfl⟩ := ih
        cases μ with
        | none => exact absurd htr liftOption_not_tr_none
        | some μ => exact ⟨μ :: μs', rfl⟩
    obtain ⟨_, hrun, rfl⟩ := hb.bisim_trace rfl μs' t (mapLabel_mTr.mpr h)
    exact ⟨μs', rfl, hrun⟩
  · rintro ⟨μs', rfl, h⟩
    obtain ⟨t', hrun, (rfl : t' = t)⟩ := hb.inv.bisim_trace rfl μs' t h
    exact mapLabel_mTr.mp hrun

end Cslib.LTS
