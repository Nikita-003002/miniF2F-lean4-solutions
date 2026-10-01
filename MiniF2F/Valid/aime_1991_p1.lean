import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1991_p1 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : x * y + (x + y) = 71)
  (h₂ : x ^ 2 * y + x * y ^ 2 = 880) : x ^ 2 + y ^ 2 = 146 := by
  have h₃ : (x + y) * (x * y + (x + y)) = (x ^ 2 * y + x * y ^ 2) + (x + y) ^ 2 := by ring
  rw [h₁, h₂] at h₃
  have h₄ : (x ^ 2 + y ^ 2) + 2 * (x * y + (x + y)) = (x + y) ^ 2 + 2 * (x + y) := by ring
  rw [h₁] at h₄
  have h₅ : 0 ≤ ((x : ℤ) - 1) * ((y : ℤ) - 1) := mul_nonneg (by omega) (by omega)
  zify at h₁ h₃
  have h₇ : ((x : ℤ) + y - 16) * ((x : ℤ) + y - 55) = 0 := by linarith
  have h₈ : (x : ℤ) + y = 16 := by
    rcases mul_eq_zero.mp h₇ with h | h <;> linarith
  rw [show x + y = 16 by omega] at h₄
  omega
