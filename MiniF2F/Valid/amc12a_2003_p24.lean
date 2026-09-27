import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2003_p24 :
  IsGreatest { y : ℝ | ∃ a b : ℝ, 1 < b ∧ b ≤ a ∧ y = Real.logb a (a / b) + Real.logb b (b / a) }
    0 := by
    refine ⟨⟨2, 2, (by norm_num)⟩, ?_⟩
    · rintro y ⟨a, b, hb_gt, b_le_a, rfl⟩
      rw [← Real.log_div_log, ← Real.log_div_log, Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) (by linarith)]
      have hv_pos: 0 < Real.log b := Real.log_pos hb_gt
      have hu_pos: 0 < Real.log a := Real.log_pos (by linarith)
      have h_pos: 0 ≤ ((Real.log a - Real.log b) ^ 2 / (Real.log a * Real.log b)) := by positivity
      calc
        _ = -(((Real.log a - Real.log b) ^ 2) / (Real.log a * Real.log b)) := by field_simp; linarith
        _ ≤ 0 := neg_nonpos.mpr (by positivity)
