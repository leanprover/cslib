import Mathlib.Tactic

def Q_to_Float (q : ℚ) : Float :=
  (q.num.toInt64.toFloat)/(q.den.toInt64.toFloat)


-- Pseudo code from
-- "Numerical Analysis" by Richard L. Burden and J. Douglas Faires.
noncomputable def bisectR
  (f : ℝ → ℝ) (a b : ℝ) (ε : ℝ) (iter : ℕ)
  (h₁ : f a * f b < 0)
  (h₂ : 0 < ε ∧ ε ≤ (b - a)) : ℝ :=
  -- we use Intermediate Value Theorem (IVT) to
  -- show there exists a root in [a, b]
  let p := (a + b) / 2
  let fp := f p
  if iter = 0 then p
  else if h_fp_eq_0: fp = 0 then p
  else if h_a_b_le_eps: (b - a) / 2 < ε then p
  else if h₁': f a * fp < 0 then
    have h₂' : 0 < ε ∧ ε ≤ (p - a) := by
      simp [h₂]
      simp [p]
      simp at h_a_b_le_eps
      have h₂_temp : (a + b)/2 - a = (b - a)/2 := by linarith
      simp [h₂_temp]
      linarith
    bisectR f a p ε (iter - 1) h₁' h₂'
  else
    have h₁'' : f p * f b < 0 := by
      rw [mul_comm]
      sorry -- use f a * f b < 0 and f a * fp ≥ 0 to show f b * fp < 0
    have h₂'' : 0 < ε ∧ ε ≤ (b - p) := by
      simp [h₂]
      simp [p]
      simp at h_a_b_le_eps
      have h₂_temp : b - (a + b)/2 = (b - a)/2 := by linarith
      simp [h₂_temp]
      linarith
    bisectR f p b ε (iter - 1) h₁'' h₂''

def bisect_iter
  (f : ℚ → ℚ) (a b : ℚ) (ε : ℚ) (iter : ℕ)
  (h₀ : a < b)
  (h₁ : f a * f b < 0)
  (h₂ : 0 < ε ∧ ε ≤ (b - a)) : ℚ :=
  let p := (a + b) / 2
  have h₀' : a < p := by
    simp [p]
    linarith
  have h₀'' : p < b := by
    simp [p]
    linarith
  let fp := f p
  if iter = 0 then p
  else if h_fp_eq_0: fp = 0 then p
  else if h_a_b_le_eps: (b - a) / 2 < ε then p
  else if h₁': f a * fp < 0 then
    have h₂' : 0 < ε ∧ ε ≤ (p - a) := by
      simp [h₂]
      simp [p]
      simp at h_a_b_le_eps
      have h₂_temp : (a + b)/2 - a = (b - a)/2 := by linarith
      simp [h₂_temp]
      linarith
    bisect_iter f a p ε (iter - 1) h₀' h₁' h₂'
  else
    have h₁'' : f p * f b < 0 := by
      rw [mul_comm]
      sorry -- use f a * f b < 0 and f a * fp ≥ 0 to show f b * fp < 0
    have h₂'' : 0 < ε ∧ ε ≤ (b - p) := by
      simp [h₂]
      simp [p]
      simp at h_a_b_le_eps
      have h₂_temp : b - (a + b)/2 = (b - a)/2 := by linarith
      simp [h₂_temp]
      linarith
    bisect_iter f p b ε (iter - 1) h₀'' h₁'' h₂''

def bisect
  (f : ℚ → ℚ) (a b : ℚ) (ε : ℚ)
  (h₀ : a < b)
  (h₁ : f a * f b < 0)
  (h₂ : 0 < ε ∧ ε ≤ (b - a)) : ℚ :=
  let p := (a + b) / 2
  have h₀' : a < p := by
    simp [p]
    linarith
  have h₀'' : p < b := by
    simp [p]
    linarith
  let fp := f p
  if h_fp_eq_0: fp = 0 then p
  else if h_a_b_le_eps: (b - a)/2 < ε then p
  else if h₁': f a * fp < 0 then
    have h₂' : 0 < ε ∧ ε ≤ (p - a) := by
      simp [h₂]
      simp [p]
      simp at h_a_b_le_eps
      have h₂_temp : (a + b)/2 - a = (b - a)/2 := by linarith
      simp [h₂_temp]
      linarith
    bisect f a p ε h₀' h₁' h₂'
  else
    have h₁'' : f p * f b < 0 := by
      rw [mul_comm]
      sorry -- use f a * f b < 0 and f a * fp ≥ 0 to show f b * fp < 0
    have h₂'' : 0 < ε ∧ ε ≤ (b - p) := by
      simp [h₂]
      simp [p]
      simp at h_a_b_le_eps
      have h₂_temp : b - (a + b)/2 = (b - a)/2 := by linarith
      simp [h₂_temp]
      linarith
    bisect f p b ε h₀'' h₁'' h₂''
termination_by (b.num * a.den - a.num * b.den).toNat
decreasing_by
  all_goals sorry


def sqrt (c : ℚ) (ε : ℚ) (h₀ : 0 < ε ∧ ε ≤ c ∧ 1 < c) : ℚ :=
  bisect (fun x => x^2 - c) 0 c ε (by linarith)
  (
    by
    simp
    have h₂ : c^2 - c = c*(c - 1) := by linarith
    rw [h₂]
    simp [←mul_assoc]
    apply mul_pos
    apply mul_pos
    all_goals linarith
  )
  (
    by
    simp [h₀]
  )

def sqrtN (c : ℕ) (h : 1 < c) : ℚ :=
  sqrt c 0.000001
  (
    by
    repeat apply And.intro
    linarith
    apply And.intro
    transitivity 1
    linarith
    simp
    linarith
    simp
    linarith
  )

#eval! Q_to_Float (bisect (fun x => x^3 - x - 2) 0.0 2.0 0.01 (by norm_num) (by norm_num) (by norm_num))

#eval! Q_to_Float (sqrt 2.0 0.000001 (by norm_num))

#eval! Q_to_Float (sqrtN 2 (by norm_num))
