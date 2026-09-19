import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_89 (b : ℝ) (h₀ : b ≠ 0) :
  (7 * b ^ 3) ^ 2 * (4 * b ^ 2) ^ (-(3 : ℤ)) = 49 / 64 := by
  rw[zpow_neg, zpow_ofNat]
  have hd: (4 * b ^ 2) ^ 3 ≠ 0 := by positivity
  field_simp
  ring
