import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_22 : Real.logb (5 ^ 2) (5 ^ 4) = 2 := by
  unfold Real.logb
  rw[Real.log_pow, Real.log_pow]
  field_simp
  ring
