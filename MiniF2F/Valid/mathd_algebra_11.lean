import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_11 (a b : ℝ) (h₀ : a ≠ b) (h₁ : a ≠ 2 * b)
    (h₂ : (4 * a + 3 * b) / (a - 2 * b) = 5) : (a + 11 * b) / (a - b) = 2 := by
    have h_deno1: a - 2 * b ≠ 0 := sub_ne_zero.mpr h₁
    have h_deno2: a - b ≠ 0 := sub_ne_zero.mpr h₀
    have h₃: (4 * a + 3 * b) = 5 * (a - 2 * b) := (div_eq_iff h_deno1).mp h₂
    rw[div_eq_iff h_deno2]
    linarith
