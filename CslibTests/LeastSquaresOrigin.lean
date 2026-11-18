import Cslib.Algorithms.Lean.LeastSquares.Origin

namespace CslibTests

open Cslib.Algorithms.Lean.LeastSquares.Origin

variable {n : ℕ} (x y : Fin n → ℝ)

example (h : Sxx (n := n) x ≠ 0) (a : ℝ) :
    loss (n := n) x y (aStar (n := n) x y) ≤ loss (n := n) x y a := by
  simpa using aStar_minimizes (n := n) (x := x) (y := y) h a

end CslibTests
