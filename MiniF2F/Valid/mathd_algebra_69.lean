import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_69 (rows seats : ℕ) (h₀ : rows * seats = 450)
  (h₁ : (rows + 5) * (seats - 3) = 450) : rows = 25 := by
  have hs: 3 ≤ seats := by
    by_contra! h
    have h_zero: seats - 3 = 0 := by omega
    rw[h_zero, mul_zero] at h₁
    omega
  zify [hs] at h₀ h₁ ⊢
  have h₂: 3 * ((rows : ℤ) - 25) * ((rows : ℤ) + 30) = 0 := by
    linear_combination (rows + 5) * h₀ - rows * h₁
  nlinarith
