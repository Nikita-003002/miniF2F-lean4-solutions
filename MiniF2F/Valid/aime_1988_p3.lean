import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1988_p3 (x : ℝ) (h₀ : 0 < x) (hx: x ≠ 1)
  (h₁ : Real.logb 2 (Real.logb 8 x) = Real.logb 8 (Real.logb 2 x)) : Real.logb 2 x ^ 2 = 27 := by
  unfold Real.logb at h₁ ⊢
  set y := Real.log x / Real.log 2
  have hy: y ≠ 0 := fun h => hx <| (Real.log_eq_zero.mp <| (div_eq_zero_iff.mp h).resolve_right (by norm_num)).resolve_left h₀.ne' |>.resolve_right (by linarith)
  have h₂ : 2 * Real.log y = 3 * Real.log 3 := by
    have h8 : Real.log 8 = 3 * Real.log 2 := by rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; rfl
    rw [h8, show Real.log x / (3 * Real.log 2) = y / 3 by ring] at h₁
    field_simp at h₁
    rw [Real.log_div hy (by norm_num), show 3 * (Real.log y - Real.log 3) = 3 * Real.log y - 3 * Real.log 3 by ring] at h₁
    linarith
  have h_log : Real.log (y ^ 2) = Real.log 27 := by
    calc
      Real.log (y ^ 2) = 2 * Real.log y := by exact_mod_cast Real.log_pow y 2
      _                = 3 * Real.log 3 := h₂
      _                = Real.log 27    := by norm_num [← Real.log_rpow]

  exact Real.log_injOn_pos (sq_pos_of_ne_zero hy) (by norm_num) h_log
