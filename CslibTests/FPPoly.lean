/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.FPPoly

/-!
# FP/poly automation tests

Closure proofs use ordinary bit-string functions without explicit circuit or size witnesses.
-/

namespace CslibTests.FPPoly

open Cslib Cslib.Circuits.Boolean

example {f g h : BitString → BitString} (hf : FPPoly f) (hg : FPPoly g) (hh : FPPoly h) :
    FPPoly (fun x => h (f x ++ g (f x))) := by fun_prop

example {f g : BitString → BitString} (hf : FPPoly f) (hg : FPPoly g) :
    FPPoly (f ∘ g) := by fun_prop

def transform (x : BitString) : BitString :=
  let y := x.reverse
  y ++ y.map not ++ [true, false]

example : FPPoly transform := by fun_prop [transform]

example {f g : BitString → BitString} (hf : FPPoly f) (hg : FPPoly g) :
    FPPoly (fun x => (f x).take 3 ++ (g x).drop 1) := by fun_prop

example {f g : BitString → BitString} (hf : FPPoly f) (hg : FPPoly g) :
    FPPoly (fun x => List.zipWith xor (f x) (g (x.reverse))) := by fun_prop

-- Independent layout and decoding checks for the new codec, including unused data and
-- an oversized header. Capacity four has three length bits followed by four data bits.
open BitString.Encoding in
example : List.ofFn (encode 4 [true, false, true]) =
    [true, true, false, true, false, true, false] := by decide

open BitString.Encoding in
example : decode (n := 4) ![true, false, false, true, false, true, true] = [true] := by decide

open BitString.Encoding in
example : decode (n := 4) ![true, true, true, true, false, true, false] =
    [true, false, true, false] := by decide

end CslibTests.FPPoly
