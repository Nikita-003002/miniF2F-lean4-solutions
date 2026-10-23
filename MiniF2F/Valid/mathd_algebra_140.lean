import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_140 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : ∀ x, 24 * x ^ 2 - 19 * x - 35 = (a * x - 5) * (2 * (b * x) + c)) : a * b - 3 * c = -9 := by
  have h0 := h₁ 0
  have h1 := h₁ 1
  have h_neg1 := h₁ (-1)
  norm_num at h0 h1 h_neg1
  linear_combination (- 1 / 4)* h1 - (1 / 4) * h_neg1 + (1 / 10) * h0

-- Completion time : 19.41 mins
