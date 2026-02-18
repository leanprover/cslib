import Mathlib.Tactic

def Q_to_Float (q : ℚ) : Float :=
  (q.num.toInt64.toFloat)/(q.den.toInt64.toFloat)

-- Simple gradient descent with iteration limit
def gradient_descent_iter
  (f : ℚ → ℚ) (f' : ℚ → ℚ)
  (x₀ : ℚ) (α : ℚ) (ε : ℚ) (iter : ℕ)
  (h₀ : 0 < α ∧ α < 1) -- learning rate constraints
  (h₁ : 0 < ε) -- tolerance constraint
  : ℚ :=
  let grad := f' x₀
  if iter = 0 then x₀
  else if h_grad_small: abs grad < ε then x₀  -- converged
  else
    let x₁ := x₀ - α * grad
    gradient_descent_iter f f' x₁ α ε (iter - 1) h₀ h₁

-- Gradient descent without iteration limit (terminates when gradient is small)
def gradient_descent
  (f : ℚ → ℚ) (f' : ℚ → ℚ) (x₀ : ℚ) (α : ℚ) (ε : ℚ)
  (h₀ : 0 < α ∧ α < 1) -- learning rate constraints
  (h₁ : 0 < ε) -- tolerance constraint
  : ℚ :=
  let grad := f' x₀
  if h_grad_small: abs grad < ε then x₀  -- converged
  else
    let x₁ := x₀ - α * grad
    gradient_descent f f' x₁ α ε h₀ h₁
termination_by abs (f' x₀)
decreasing_by
  sorry -- requires convexity and proper learning rate assumptions


def find_poly_minima (f f' : ℚ → ℚ) : ℚ :=
  let x := gradient_descent_iter f f' 1 0.1 0.0001 50 (by norm_num) (by norm_num)
  f x

-- Example: minimize f(x) = x² - 4x + 3, f'(x) = 2x - 4
-- Minimum should be at x = 2
def f (x : ℚ) : ℚ := x^2 - 4*x + 3
def f' (x : ℚ) : ℚ := 2*x - 4

#eval! Q_to_Float (find_poly_minima f f')
-- ^ Returns  -1.0, the minimum value of f(x)

-- Example: minimize f(x) = (x - 3)^2 + 4, f'(x) = 2(x - 3)
-- Minimum should be at x = 3
def g (x : ℚ) : ℚ := (x - 3)^2 + 4
def g' (x : ℚ) : ℚ := 2*(x - 3)

#eval! Q_to_Float (find_poly_minima g g')
-- ^ Returns 4.0, the minimum value of g(x)
