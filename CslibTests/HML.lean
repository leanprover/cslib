/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.HML.Basic
import Cslib.Languages.CCS.Semantics

namespace CslibTests

open Cslib
open CCS Logic.HML LTS

example [∀ p μ, Finite ((CCS.lts (defs := defs)).image p μ)] :
    TheoryEq (CCS.lts (defs := defs)) = HomBisimilarity (CCS.lts (defs := defs)) :=
  theoryEq_eq_bisimilarity ..

end CslibTests
