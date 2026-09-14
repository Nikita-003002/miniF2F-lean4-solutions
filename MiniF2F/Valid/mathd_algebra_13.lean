import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_13 (a b : ℝ)
  (h₀ : ∀ x, x - 3 ≠ 0 ∧ x - 5 ≠ 0 → 4 * x / (x ^ 2 - 8 * x + 15) = a / (x - 3) + b / (x - 5)) :
  a = -6 ∧ b = 10 := by
  have h₁: 4 * 4 / (4 ^ 2 - 8 * 4 + 15) = a / (4 - 3) + b / (4 - 5) := by
    apply h₀
    norm_num
  have h₂: 4 * 6 / (6 ^ 2 - 8 * 6 + 15) = a / (6 - 3) + b / (6 - 5) := by
    apply h₀
    norm_num
  norm_num at h₁ h₂
  constructor <;>
  linarith
