/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Synthesis

/-!
# Synthesis over the full basis

The full basis contains constants and all operations of a fixed arity. A constant can be
synthesized with one gate. In the binary full basis, applying any binary operation to
functions synthesized with budgets `a` and `b` takes at most `a + b + 1` gates.
Both constructions preserve all previously available functions.
-/

@[expose] public section

namespace Cslib.Circuits.Synthesis

universe u

variable {U : Type u} {k n a b : ℕ} {s : Set ((Fin n → U) → U)}

/-- A constant can be synthesized with one gate of the full basis. -/
theorem full_const (value : U) :
    Synthesis (fullInterpretation (k := k)) s {fun _ => value} 1 :=
  nullary (I := fullInterpretation (k := k)) (.con value) rfl

/-- Apply any binary operation to synthesized functions in the binary full basis. -/
theorem full_binary {f g : (Fin n → U) → U}
    (hf : Synthesis (fullInterpretation (k := 2)) s {f} a)
    (hg : Synthesis (fullInterpretation (k := 2)) s {g} b) (op : U → U → U) :
    Synthesis (fullInterpretation (k := 2)) s {fun x => op (f x) (g x)} (a + b + 1) :=
  hf.binary hg (.fn fun x => op (x 0) (x 1))

end Cslib.Circuits.Synthesis
