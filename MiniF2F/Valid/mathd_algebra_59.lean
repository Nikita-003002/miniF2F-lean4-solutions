import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_59 (b : ℝ) (h₀ : (4 : ℝ) ^ b + 2 ^ 3 = 12) : b = 1 := by
  have hx: (4 : ℝ) ^ b = (4 : ℝ) ^ (1 : ℝ):= by
    rw[show (4 : ℝ) ^ (1 : ℝ) = 4 by norm_num]
    linarith
  exact (strictMono_rpow_of_base_gt_one (by norm_num)).injective hx
