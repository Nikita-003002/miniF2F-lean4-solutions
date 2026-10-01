import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1990_p2 :
  (52 + 6 * Real.sqrt 43) ^ ((3 : ℝ) / 2) - (52 - 6 * Real.sqrt 43) ^ ((3 : ℝ) / 2) = 828 := by
  have hsq : Real.sqrt 43 ^ 2 = 43 := Real.sq_sqrt (by positivity)
  have hs1 : 52 + 6 * Real.sqrt 43 = (Real.sqrt 43 + 3) ^ (2 : ℝ) := by
    norm_num; linarith
  have hs2 : 52 - 6 * Real.sqrt 43 = (Real.sqrt 43 - 3) ^ (2 : ℝ) := by
    norm_num; linarith
  have ha : 0 ≤ Real.sqrt 43 + 3 := by positivity
  have hb : 0 ≤ Real.sqrt 43 - 3 := sub_nonneg.mpr <|
    (show (3 : ℝ) = Real.sqrt 9 by norm_num) ▸ Real.sqrt_le_sqrt (by norm_num)
  rw [hs1, hs2,← Real.rpow_mul ha, ← Real.rpow_mul hb]
  rw [show (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  linarith
