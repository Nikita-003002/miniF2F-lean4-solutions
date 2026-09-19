import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_77 (a b : ℝ) (f : ℝ → ℝ) (h₀ : a ≠ 0 ∧ b ≠ 0) (h₁ : a ≠ b)
  (h₂ : ∀ x, f x = x ^ 2 + a * x + b) (h₃ : f a = 0) (h₄ : f b = 0) : a = 1 ∧ b = -2 := by
  rw[h₂] at h₃ h₄
  have hb: b * (b + a + 1) = 0 := by linear_combination h₄
  have hb1: b + a + 1 = 0 := by
    apply (mul_eq_zero.mp hb).resolve_left h₀.2
  have ha: (2 * a + 1) * (a - 1) = 0 := by linear_combination h₃ - hb1
  cases mul_eq_zero.mp ha with
  | inl hz => exact (h₁ (by linarith)).elim
  | inr hz => exact ⟨by linarith, by linarith⟩
