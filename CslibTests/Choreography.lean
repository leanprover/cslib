/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Languages.Mech.Choreography.Basic

namespace CslibTests

open Cslib.Mech Cslib.Languages.Mech

-- Notation
-- The notation of a local assignment.
example {S : Sig Pid} (p : Pid) (x : S.Var p α) (e : S.Expr p α) :
    (`(Mech|p . x ≔ e; 0) : Choreography Pid S SelLabel ProcName) =
    Choreography.pre (Prefix.assign p x e) 0 := rfl

example {S : Sig Pid} (p q : Pid) (e : S.Expr p α) (x : S.Var q α) :
    (`(Mech|p . e ⮕ q . x; 0) : Choreography Pid S SelLabel ProcName) =
    Choreography.pre (Prefix.com p e q x) 0 := rfl

end CslibTests
