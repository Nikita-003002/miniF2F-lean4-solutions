import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12_2001_p9 (f : ℝ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x / y) (h₁ : f 500 = 3) :
    f 600 = 5 / 2 := by
    have h_eq: (600 : ℝ) = 500 * (6 / 5) := by norm_num
    rw [h_eq, h₀ 500 (by positivity) (6 / 5) (by positivity), h₁]
    norm_num
