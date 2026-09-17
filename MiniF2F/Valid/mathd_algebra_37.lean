import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_37 (x y : ℝ) (h₀ : x + y = 7) (h₁ : 3 * x + y = 45) : x ^ 2 - y ^ 2 = 217 := by
  have hx: x = 19 := by linarith
  have hy: y = -12 := by linarith
  rw[hx, hy]
  norm_num
