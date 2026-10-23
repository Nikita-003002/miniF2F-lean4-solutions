import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem induction_12dvd4expnp1p20
  (n : ℕ) :
  12 ∣ 4^(n+1) + 20 := by
  induction n with
    | zero => decide
    | succ i ih =>
      rw [pow_succ]
      omega

-- Completion time : 20.14 mins
