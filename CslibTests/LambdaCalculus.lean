/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Haoxuan Yin
-/

import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic
import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties

namespace CslibTests

open Cslib Cslib.LambdaCalculus.Named.Untyped.Term

def x := 0
def y := 1
def z := 2
def w := 3

def lambdaId := abs x (var x)

example : (abs x (var x)) =α (abs y (var y)) := by
  have h : (abs y (var y)) = (abs y ((var x).rename x y)) := by grind [rename]
  rw [h]
  apply AlphaEquiv.abs_rename
  simp only [vars]
  decide

example : (abs y (var x)).subst x (app (var y) (var z)) = (abs w (app (var y) (var z))) := by
  simp only [rename, subst, fv, vars]
  decide

-- section 5.3.4 of TAPL
example : (abs y (app (var x) (var y))).subst x (app (var y) (var z)) =
    (abs w (app (app (var y) (var z)) (var w))) := by
  simp only [subst, vars, rename]
  decide

example : (abs x (abs y (app (var x) (var y)))) =α (abs y (abs x (app (var y) (var x)))) := by
  apply AlphaEquiv.abs (y := z)
  · simp only [vars]
    decide
  simp only [rename]
  apply AlphaEquiv.abs (y := w)
  · simp only [vars]
    decide
  simp only [rename]
  apply AlphaEquiv.refl

end CslibTests
