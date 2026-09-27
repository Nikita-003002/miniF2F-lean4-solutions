import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2003_p24 :
  IsGreatest { y : ℝ | ∃ a b : ℝ, 1 < b ∧ b ≤ a ∧ y = Real.logb a (a / b) + Real.logb b (b / a) }
    0 := by
    constructor
    · simp
      use 2, 2
      simp
    · rintro y ⟨a, b, hb_gt, b_le_a, rfl⟩
      rw [← Real.log_div_log, ← Real.log_div_log, Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) (by linarith)]
      set u := Real.log a
      set v := Real.log b
      have hv_pos: 0 < v := Real.log_pos hb_gt
      have ha_gt: v ≤ u := Real.log_le_log (by linarith) b_le_a
      have hu_pos: 0 < u := by linarith
      have: (u - v) / u + (v - u) / v = (- (u - v) ^ 2) / (u * v) := by field_simp; linarith
      rw[this]
      have h_eq: 0 ≤ (u - v) ^ 2 / (u * v) := by positivity
      rw[neg_div]
      exact neg_nonpos.mpr h_eq
