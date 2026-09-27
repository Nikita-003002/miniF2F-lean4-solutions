import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2003_p25 (a b : ℝ) (f : ℝ → ℝ) (h₀ : 0 < b)
  (h₁ : ∀ x, f x = Real.sqrt (a * x ^ 2 + b * x)) (h₂ : { x | 0 ≤ f x } = f '' { x | 0 ≤ f x }) :
  a = 0 ∨ a = -4 := by
  have hx: ∀ x, 0 ≤ f x := fun x ↦ h₁ x ▸ Real.sqrt_nonneg _
  rcases (by rw[← h₂]; exact hx (-1): -1 ∈ f ''{ x | 0 ≤ f x }) with ⟨y, _, _⟩
  linarith [hx y]
