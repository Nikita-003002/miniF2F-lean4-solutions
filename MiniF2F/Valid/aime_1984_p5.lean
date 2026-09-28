import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1984_p5 (a b : ℝ) (ha: 0 < a) (hb: 0 < b) (h₀ : Real.logb 8 a + Real.logb 4 (b ^ 2) = 5)
  (h₁ : Real.logb 8 b + Real.logb 4 (a ^ 2) = 7) : a * b = 512 := by
  have h8: Real.log 8 = 3 * Real.log 2 := by rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; exact rfl
  have h4: Real.log 4 = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2  by norm_num, Real.log_pow]; exact rfl
  have eq1: (1 / 3 : ℝ) * Real.logb 2 a + Real.logb 2 b = 5 := by
    rw [← h₀]; unfold Real.logb; rw[h4, h8, Real.log_pow]; ring_nf
  have eq2: (1 / 3 : ℝ) * Real.logb 2 b + Real.logb 2 a = 7 := by
    rw [← h₁]; unfold Real.logb; rw[h4, h8, Real.log_pow]; ring_nf
  have h_eq: Real.logb 2 a + Real.logb 2 b = 9 := by linarith
  rw [← Real.rpow_logb (b := 2) (by norm_num) (by norm_num) (mul_pos ha hb), Real.logb_mul (ne_of_gt ha) (ne_of_gt hb), h_eq]
  ring_nf
