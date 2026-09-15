import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_28 (c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x ^ 2 + 5 * x + c)
  (h₁ : ∃ x, f x ≤ 0) : c ≤ 25 / 8 := by
  rcases h₁ with ⟨x, hx⟩
  rw[h₀] at hx
  have h_sq: 0 ≤ (x + 5 / 4) ^ 2 := by positivity
  nlinarith
