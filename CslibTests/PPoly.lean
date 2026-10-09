/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.PPoly

/-!
# P/poly automation tests

Boolean and word-valued expressions compose without manual conversions between the classes.
-/

namespace CslibTests.PPoly

open Cslib Cslib.Circuits.Boolean

example {f g : BitString → Bool} (hf : PPoly f) (hg : PPoly g) :
    PPoly (fun x => !(f x && g x) || ((f x ^^ g x) == f x)) := by fun_prop

example {f g : BitString → Bool} (hf : PPoly f) (hg : PPoly g) :
    PPoly (fun x => if f x then g x else true) := by fun_prop

example (i : ℕ) : PPoly (fun x => x[i]?.getD false) := by fun_prop

example {f : BitString → Bool} {g : BitString → BitString} (hf : PPoly f) (hg : FPPoly g) :
    PPoly (fun x => f (g (x ++ x))) := by fun_prop

-- Composed lookup needs a rule that can find f inside Option.getD.
example {f : BitString → BitString} (hf : FPPoly f) (i : ℕ) (fallback : Bool) :
    PPoly (fun x => (f x)[i]?.getD fallback) := by fun_prop

example {f : BitString → BitString} (hf : FPPoly f) :
    PPoly (fun x => (f x).all id && (f x).any not) := by fun_prop

example {f g : BitString → Bool} (hf : PPoly f) (hg : PPoly g) :
    FPPoly (fun x => [f x, !g x, f x && g x] ++ x.reverse) := by fun_prop

example {c : BitString → Bool} {f g : BitString → BitString} (hc : PPoly c) (hf : FPPoly f)
    (hg : FPPoly g) : FPPoly (fun x => if c x then f x else g x ++ f x) := by fun_prop

example {f g : BitString → BitString} (hf : FPPoly f) (hg : FPPoly g) :
    PPoly (fun x => (f x == g x.reverse) && decide ((f x).length ≤ 5)) := by fun_prop

end CslibTests.PPoly
