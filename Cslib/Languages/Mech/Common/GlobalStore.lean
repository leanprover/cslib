/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Languages.Mech.Common.LocalStore

/-! # Global stores -/

@[expose] public section

namespace Cslib.Mech

namespace Sig

/-- A global store represents the memory state of an entire network, mapping each process to a
local store of its own local signature. -/
abbrev Store {Pid} (S : Sig Pid) := (p : Pid) → (S p).Store

/-- Write the local variable `x` of process `p`. Results are stated with the notation
`gs[⟨p, x⟩ := v]`. -/
def Store.write {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (v : α) : S.Store :=
  Function.update gs p ((gs p)[x := v])

/-! ### Notation for global stores

We define notation for read and write operations on global stores. For any global store `gs`:
- `(gs p)[x]` reads the value of variable `x` at process `p`;
- `gs[⟨p, x⟩ := v]` writes the value `v` in variable `x` at process `p`.
-/

/-- Instance for the write notation `gs[⟨p, x⟩ := v]`. -/
@[default_instance]
instance Store.instHasSubstitution {Pid} [DecidableEq Pid] {S : Sig Pid} {α} :
    HasSubstitution S.Store ((p : Pid) × S.Var p α) α where
  subst gs px v := gs.write px.1 px.2 v

@[simp, grind =]
theorem Store.write_def {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (v : α) : gs.write p x v = gs[⟨p, x⟩ := v] := rfl

theorem Store.subst_eq_update {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (v : α) :
    gs[⟨p, x⟩ := v] = Function.update gs p ((gs p)[x := v]) := rfl

/-- The local store of a process after a write operation at that process. -/
@[simp, grind =]
theorem Store.subst_apply_self {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (v : α) : gs[⟨p, x⟩ := v] p = (gs p)[x := v] := by
  simp [subst_eq_update]

/-- Stores writes are local: writing at one process does not affect the store of another process. -/
@[simp, grind =]
theorem Store.subst_apply_of_ne {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p q : Pid) (x : S.Var p α) (v : α) (h : q ≠ p) :
    gs[⟨p, x⟩ := v] q = gs q := by
  simp [subst_eq_update, h]

/-- Reading a variable just written returns the written value. -/
@[grind =]
theorem Store.getElem_subst_self {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (v : α) : (gs[⟨p, x⟩ := v] p)[x] = v := by
  simp

/-- Writing one variable preserves the value of another variable of the same process. -/
@[grind =]
theorem Store.getElem_subst_of_name_ne {Pid} [DecidableEq Pid] {S : Sig Pid} {α β}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (a : α) (y : S.Var p β) (h : y.name ≠ x.name) :
    (gs[⟨p, x⟩ := a] p)[y] = (gs p)[y] := by
  simp [h]

/-- A later write to the same process and variable overrides an earlier write. -/
@[simp, grind =]
theorem Store.subst_subst_self {Pid} [DecidableEq Pid] {S : Sig Pid} {α}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (a b : α) :
    gs[⟨p, x⟩ := a][⟨p, x⟩ := b] = gs[⟨p, x⟩ := b] := by
  simp [subst_eq_update]

/-- Writes to distinct processes commute. -/
theorem Store.subst_comm_of_ne {Pid} [DecidableEq Pid] {S : Sig Pid} {α β}
    (gs : S.Store) (p q : Pid) (x : S.Var p α) (y : S.Var q β) (a : α) (b : β) (h : p ≠ q) :
    gs[⟨p, x⟩ := a][⟨q, y⟩ := b] = gs[⟨q, y⟩ := b][⟨p, x⟩ := a] := by
  simp only [subst_eq_update, Function.update_of_ne h, Function.update_of_ne (Ne.symm h)]
  exact Function.update_comm h _ _ _

/-- Writes to different variables of the same process commute. -/
theorem Store.subst_comm_of_name_ne {Pid} [DecidableEq Pid] {S : Sig Pid} {α β}
    (gs : S.Store) (p : Pid) (x : S.Var p α) (y : S.Var p β) (a : α) (b : β)
    (h : x.name ≠ y.name) : gs[⟨p, x⟩ := a][⟨p, y⟩ := b] = gs[⟨p, y⟩ := b][⟨p, x⟩ := a] := by
  simp [subst_eq_update, LocalSig.Store.subst_comm _ _ _ _ _ h]

end Sig

end Cslib.Mech
