/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Cslib.Computability.FunctionAlgebras.Cobham.Defs
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-!
# Cobham's theorem

Cobham's theorem [Cobham1965] states that the functions of Cobham's algebra
(`Cslib.CobhamFP`) are exactly the functions computable in polynomial time by a Turing
machine (`Cslib.Turing.SingleTapeTM.PolyTimeComputable`).

## References

* [A. Cobham, *The intrinsic computational difficulty of functions*][Cobham1965]
-/

-- A `proof_wanted` adds no declaration to the module, so this file has nothing public.
set_option linter.privateModule false

@[expose] public section

namespace Cslib

open Turing.SingleTapeTM

/-- **Cobham's theorem**: a string function is in Cobham's algebra if and only if it is
computable in polynomial time by a single-tape Turing machine. -/
proof_wanted CobhamFP_iff_polyTimeComputable {Symbol : Type} [Inhabited Symbol]
    [Fintype Symbol] (f : List Symbol → List Symbol) :
    f ∈ CobhamFP Symbol ↔ Nonempty (PolyTimeComputable f)

end Cslib
